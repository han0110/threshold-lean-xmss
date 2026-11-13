import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Run
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Setup
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Local
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Round1
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SyncHandlers
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Verify
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1ChainRelease
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Finish
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1TreeStep
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Round2

/-! # The coupling of the two complete runs of the O1 coupling

- `FinalRel` is the relation of the two complete runs. The final facts hold at reveal maps before
  the last reveals of the honest signature.
- `finishO1X` is the finish of the compiler game. `sourceGameO1X_eq` writes the compiler game as the
  setup, the forger phase and the finish in sequence.
- `realOracles_stop` states that the stop of the real side persists over the forger phase.
- `run_coupled` couples the raw real run and the O1 program on the eager backend, for fixed tables.
  It joins the setup (`setup_sync`), the forger phase (`forger_sync`) and the finish
  (`finish_sync`). After a stop each later phase keeps the stop.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Coupled
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame SigningCompilerO1Verify SigningCompilerO1Tail
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

section Finish
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The relation of the two complete runs. The final facts hold at reveal maps before the last
reveals of the honest signature. -/
def FinalRel (z : RealFinal C) (c : CompFinal C) : Prop :=
  RealStop q (realEnd z) ∨ Stop c.2 ∨ ∃ source wrapper : HiddenKey → Option Digest,
    FinalFacts prims x s pads u rest noise z
      ((c.1.1, (withReveal (c.1.2, c.2) source wrapper).1), (withReveal (c.1.2, c.2) source wrapper).2)

/-- The finish of the compiler game, the verification and the freshness check after the forger. -/
def finishO1X (top : TopTree) (forgery : Forgery) : SourceMXO1 C Bool := do
  let st := (← get).base
  let _ ← liftM (markQ (C := C) st.hiddenFlag)
  let verified ← simulateQ (verifyImplO1 x st)
    (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)
  let fresh ← if (signersAt st.signing forgery.signature.leafIndex forgery.message).card < C.t
    then pure true else do
      let honest ← liftBaseX (sourceHonestSignatureX prims x top
        forgery.signature.leafIndex forgery.message)
      pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh)

/-- The compiler game is the setup, the forger phase and the finish in sequence. -/
theorem sourceGameO1X_eq (A : TsigAdversary C) :
    sourceGameO1X prims A x =
      (do let _ ← liftM (markQ (C := C) (← get).base.hiddenFlag)
          liftBaseX (sourceTopTreeX x.1 x.2.1)) >>= fun top =>
        simulateQ (sourceOraclesO1X prims x top) (A ⟨top.root, x.1⟩ top) >>= fun forgery =>
          finishO1X prims x top forgery >>= fun verdict => pure (verdict, top, forgery) := by
  have hite : ∀ {α β : Type} (c : Prop) [Decidable c] (a b : SourceMXO1 C α)
      (f : α → SourceMXO1 C β), (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
    intros; split <;> rfl
  simp only [sourceGameO1X, finishO1X, bind_assoc, pure_bind, hite]
  rfl

/-- A coupling of a run with a map on the left. -/
theorem relTriple_map_left {α β γ : Type} {oa : ProbComp α} {ob : ProbComp β} (f : α → γ)
    {R : γ → β → Prop} (h : RelTriple oa ob (fun a b => R (f a) b)) :
    RelTriple (f <$> oa) ob R := by
  have hm := relTriple_map (f := f) (g := id) (R := R) h
  rwa [id_map] at hm

/-- The stop of the real side persists over the forger phase. -/
theorem realOracles_stop (top : TopTree) {α : Type} (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (a : RealState C) (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realOracles prims x s pads u rest top) oa).run a)) :
    RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_adv prims x _ (gOf s pads u) rest q
    t st hst r hr) _ a h r hr

/-- The coupling of the two complete runs, for fixed tables. -/
theorem run_coupled (A : TsigAdversary C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    RelTriple (realRunRaw prims A x s pads (gOf s pads u) rest noise)
      ((simulateQ (compBackend x q s pads u rest noise) (sourceProgramO1X prims A x)).run
        SigningCompilerShareTables.initial)
      (FinalRel prims x q s pads u rest noise) := by
  have hstep : ∀ top t, StepO1' prims x q s pads u rest noise top t := by
    intro top t
    rcases t with t | (i | bi | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩)
    · exact SigningCompilerO1Local.step_local prims x q s pads u rest noise hkeys top t
    · exact step_pads prims x q s pads u rest noise top _
        (SigningCompilerO1SyncHandlers.step_corrupt prims x q s pads u rest noise hkeys top i)
    · exact SigningCompilerO1TreeStep.step_tree prims x q s pads u rest noise hkeys top bi
    · exact SigningCompilerO1Round1.step_round1 prims x q s pads u rest noise hkeys top i J e
        message
    · exact SigningCompilerO1Round2.step_round2 prims x q s pads u rest noise hkeys top i J e
        message parts
  rw [SigningCompilerO1Run.realRunRaw_fused]
  change RelTriple _ (runXO1 (compBackend x q s pads u rest noise) (sourceGameO1X prims A x)
    (compInit (C := C)).1 (compInit (C := C)).2) _
  unfold SigningJointEagerProof.jointGameWith
  simp only [StateT.run_bind]
  rw [sourceGameO1X_eq, SigningCompilerO1ChainRelease.runXO1_bind]
  refine relTriple_map_left _ (relTriple_bind
    (SigningCompilerO1Setup.setup_sync prims x q s pads u rest noise hkeys) ?_)
  rintro ⟨r, st⟩ ⟨⟨top, b1⟩, b2⟩ hpost
  rcases hpost with hra | hrb | ⟨hres, hsync, hpads, -⟩
  · refine relTriple_of_support_left fun z hz c => Or.inl ?_
    change RealStop q z.2
    rcases r with _ | (top' | tree) <;>
      simp only [StateT.run_bind, StateT.run_pure, StateT.run_mk, pure_bind, support_bind,
        support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz <;>
      try (subst hz; exact hra)
    obtain ⟨i, hi, w, hw, rfl⟩ := hz
    exact SigningCompilerO1Tail.realWorld_stop prims x q s pads u rest _ i.2
      (realOracles_stop prims x q s pads u rest top' _ st hra i hi) w hw
  · refine relTriple_of_support_right fun c hc z => Or.inr (Or.inl ?_)
    exact SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ hrb c hc
  · dsimp only at hres hsync hpads
    subst hres
    dsimp only
    simp only [StateT.run_bind, StateT.run_mk, pure_bind]
    rw [SigningCompilerO1ChainRelease.runXO1_bind]
    rw [show runXO1 (compBackend x q s pads u rest noise)
        (simulateQ (sourceOraclesO1X prims x top) (A ⟨top.root, x.1⟩ top)) b1 b2 = _ from
      SigningCompilerO1Run.simulateQ_run_fuse _ _ _ _ _, bind_map_left]
    refine relTriple_bind (SigningCompilerO1Run.forger_sync prims x q s pads u rest noise top
      (hstep top) _ st (b1, b2) (Or.inr (Or.inr ⟨hsync, hpads⟩))) ?_
    rintro ⟨forgery, a⟩ ⟨forgery', b1', b2'⟩ hu
    dsimp only at hu ⊢
    have hrealStop : RealStop q a → RelTriple
        ((simulateQ (realWorld prims x s pads u rest)
          (SigningGuessLinkProof.tsigFinishLogged (SigningJointEagerProof.dealtOf x top)
            (realExposed a) (forgery, realSigning a))).run a >>= fun p =>
          (pure (((p.1.1.1, a.1.2.1.2), some (top, p.1.1.2)), a.1.2.2.2 ++ p.1.2) :
            StateT (RealState C) ProbComp _).run p.2)
        (runXO1 (compBackend x q s pads u rest noise)
          (finishO1X prims x top forgery' >>= fun verdict => pure (verdict, top, forgery')) b1' b2')
        (fun a b => FinalRel prims x q s pads u rest noise ((a.1, a.2.1), a.2.2) b) := by
      intro ha
      refine relTriple_of_support_left fun z hz c => Or.inl ?_
      change RealStop q z.2
      simp only [StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff, exists_prop] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact SigningCompilerO1Tail.realWorld_stop prims x q s pads u rest _ a ha w hw
    have hcompStop : Stop b2' → RelTriple
        ((simulateQ (realWorld prims x s pads u rest)
          (SigningGuessLinkProof.tsigFinishLogged (SigningJointEagerProof.dealtOf x top)
            (realExposed a) (forgery, realSigning a))).run a >>= fun p =>
          (pure (((p.1.1.1, a.1.2.1.2), some (top, p.1.1.2)), a.1.2.2.2 ++ p.1.2) :
            StateT (RealState C) ProbComp _).run p.2)
        (runXO1 (compBackend x q s pads u rest noise)
          (finishO1X prims x top forgery' >>= fun verdict => pure (verdict, top, forgery')) b1' b2')
        (fun a b => FinalRel prims x q s pads u rest noise ((a.1, a.2.1), a.2.2) b) := by
      intro hb
      refine relTriple_of_support_right fun c hc z => Or.inr (Or.inl ?_)
      exact SigningCompilerO1ChainRelease.runXO1_stop x q s pads u rest noise _ _ _ hb c hc
    rcases hu with ha | hb | ⟨rfl, hsync', hpads'⟩
    · exact hrealStop ha
    · exact hcompStop hb
    by_cases ha : RealStop q a
    · exact hrealStop ha
    by_cases hb : Stop b2'
    · exact hcompStop hb
    rw [SigningCompilerO1ChainRelease.runXO1_bind]
    refine relTriple_bind (SigningCompilerO1Finish.finish_sync prims x q s pads u rest noise hkeys
      top forgery a (b1', b2') ⟨hsync', hpads'⟩ ha hb) ?_
    rintro ⟨⟨⟨win, sig⟩, vlog⟩, w⟩ ⟨⟨verdict, b1''⟩, b2''⟩ hpost
    dsimp only at hpost ⊢
    have hpure : runXO1 (compBackend x q s pads u rest noise) (pure (verdict, top, forgery))
        b1'' b2'' = pure (((verdict, top, forgery), b1''), b2'') := by
      simp [runXO1]
    rw [StateT.run_pure, hpure]
    refine relTriple_pure_pure ?_
    rcases hpost with h | h | ⟨-, rfl, hcar, source, wrapper, hfin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨source, wrapper, vlog, win, ?_, hfin⟩)
      change _ = (((win, w.1.2.1.2), some (top, w.1.2.1.1, forgery)), w.1.2.2.2 ++ vlog)
      rw [hcar]

end Finish

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupled.sourceGameO1X_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceGameO1X_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupled.relTriple_map_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_map_left

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupled.realOracles_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realOracles_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Coupled.run_coupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_coupled

end ThresholdLeanXmssSecurity.SigningCompilerO1Coupled
