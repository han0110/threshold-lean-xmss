import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Programs
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pending
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealBuild
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1HashProgram

/-! # The commitment step of the bottom tree build

- `commitment_sync` couples one commitment of a build. Both sides give the same commitment. Each
  term of the key is virtual, and the opening of a bound key is revealed.
- `realCommitment_run` and `runX_sourceCommitmentX` split each side into the PRF reads and the
  commitment call.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Programs SigningCompilerO1RealBuild
open SigningCompilerSyncBackend SigningCompilerSyncLocalRead
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The truncation of an answer is the reading of its low half. -/
theorem truncateHash_interpret (s : HiddenKey → Digest) (v : DeferredOutput) :
    truncateHash (v.interpret s) = v.low.interpret s :=
  congrArg Prod.snd (XmssSecurity.Rom.hashOutputEquivDigestPair.apply_symm_apply _)

section Build
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real commitment reads the PRF value, then makes one honest call at the commitment input. -/
theorem realCommitment_run (e : KeyIndex) (a : RealState C) :
    (simulateQ (realWorld prims x s pads u rest) (realCommitment x.1 x.2.1 e)).run a =
      (realHonest prims x s pads u rest (prfValue x.2.1 (.randomizer bottomLayer e))).run a >>=
        fun r1 => (fun r => (truncateHash r.1, r.2)) <$>
          (realWorld prims x s pads u rest (.inr (.inr (.inl (.hash (commitmentInput x.1 e r1.1)))))).run
            r1.2 := by
  unfold realCommitment
  rw [simulateQ_bind, StateT.run_bind]
  refine congrArg _ (funext fun r1 => ?_)
  rw [simulateQ_map, StateT.run_map]
  refine congrArg _ ?_
  have h := SigningCompilerO1HashProgram.realHonest_tweakable prims x s pads u rest
    (Concrete.oracleHash (commitmentInput x.1 e r1.1))
  change (realHonest prims x s pads u rest _).run r1.2 = _
  rw [h]
  simp [Concrete.oracleHash, SigningCompilerO1Pending.readCall_false]

/-- The compiler commitment makes the virtual reads, then one pending call. -/
theorem runX_sourceCommitmentX (e : KeyIndex) (src : SourceState C) (st : CompState C) :
    runX (compBackend x q s pads u rest noise) (sourceCommitmentX x.1 x.2.1 e) src st =
      runX (compBackend x q s pads u rest noise)
        (C.terms.mapM fun T => sourceVirtualX x.1 x.2.1 T (.randomizer bottomLayer e)) src st >>=
        fun rb1 => (fun r => ((match r.1.1.low with | .known d => d | .secret _ => 0, r.1.2), r.2)) <$>
          runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 (.commitment e)) rb1.1.2 rb1.2 := by
  unfold sourceCommitmentX
  rw [runX_bind]
  refine congrArg _ (funext fun rb1 => ?_)
  rw [runX_bind]
  simp only [runX_pure, map_eq_bind_pure_comp, Function.comp_def]
  rfl

/-- One commitment of a build. Both sides give the same commitment. Each term of the key is
virtual, and the opening of a bound key is revealed. -/
theorem commitment_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (e : KeyIndex) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest) (realCommitment x.1 x.2.1 e)).run a)
      (runX (compBackend x q s pads u rest noise) (sourceCommitmentX x.1 x.2.1 e) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed)
        (fun va vb => va = vb ∧
          (∀ T, (T, Point.randomizer bottomLayer e) ∈ (dataOf x rb.2).virtual) ∧
          (∀ k, b.1.base.revealed k ≠ none → rb.1.2.revealed k ≠ none) ∧
          (b.1.base.signing.bound e ≠ none →
            rb.1.2.revealed (.opening bottomLayer e) ≠ none)) ra rb) := by
  have hbound : b.1.base.signing.bound = cCore.1.1.bound := hs.1.1.1.bound
  let pt : CPoint := ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩
  rw [realCommitment_run, runX_sourceCommitmentX]
  refine relTriple_bind (relTriple_supported (relTriple_true _ _)) ?_
  rintro r1 rb1 ⟨-, h1, hb1⟩
  have hP := prfVirtual_sync prims x q s pads u rest noise hkeys cCore pt a b.1.base b.2 hs.1 ha hb
    hmark r1 (by with_reducible exact h1) rb1 hb1
  by_cases ha1 : RealStop q r1.2
  · refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
    rintro ra2 rb2 ⟨-, hra2, -⟩
    rw [support_map] at hra2
    obtain ⟨r, hr, rfl⟩ := hra2
    exact Or.inl (realStop_world prims x (gOf s pads u) rest q
      (.inr (.inr (.inl (.hash (commitmentInput x.1 e r1.1))))) r1.2 ha1 r (by with_reducible exact hr))
  by_cases hb1' : Stop rb1.2
  · refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
    rintro ra2 rb2 ⟨-, -, hrb2⟩
    rw [support_map] at hrb2
    obtain ⟨r, hr, rfl⟩ := hrb2
    exact Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 hb1' r hr))
  rcases hP with h | h | ⟨⟨hv, hvirt, hrev⟩, hcore, hf1, hm1⟩
  · exact (ha1 h).elim
  · exact (hb1' h).elim
  have hrevealed1 : ∀ k, rb1.1.2.revealed k = none → b.1.base.revealed k = none := by
    intro k hk
    by_contra hne
    exact hne ((hf1.revealed k hne).symm.trans hk)
  have hfree : rb1.1.2.revealed (PendingInput.commitment e).key = none →
      (dataOf x rb1.2).pending (.commitment e) = none →
      visibleOf r1.2 (.hash ((PendingInput.commitment e).input x.1
        (s (PendingInput.commitment e).key))) = none := by
    intro hk hp
    have h0 := hs.2.1.rest.guessFree (.commitment e) (hrevealed1 _ hk)
      (by_contra fun hne => hf1.pending _ hne hp)
    by_contra hne
    rcases hf1.fresh _ hne with h | ⟨T, hT⟩
    · exact h h0
    · cases hT
  have hO := SigningCompilerO1Pending.openingPending_sync prims x q s pads u rest noise hkeys cCore
    (.commitment e) (Or.inl ⟨e, rfl⟩) r1.2 rb1.1.2 rb1.2 hcore hfree ha1 hb1' hm1
  have hpads1 : PadsFixed x pads rb1.2 :=
    backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb1 hb1
  obtain ⟨v1, a1⟩ := r1
  change v1 = tauOf s pads pt at hv
  subst hv
  refine relTriple_map (relTriple_post_mono (relTriple_supported hO) ?_)
  rintro ra2 rb2 ⟨hC, -, hrb2⟩
  rcases hC with h | h | ⟨⟨hval, ⟨d, hd⟩, hpend⟩, hcore2, hf2, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hf := CallFrame.trans x _ _ a a1 ra2.2 _ _ _ hf1 hf2
  have hpads2 : PadsFixed x pads rb2.2 :=
    backend_padsFixed x q s pads u rest noise _ rb1.2 hpads1 rb2 hrb2
  have hx := ExtraOpen.frame prims x top s _ (fun _ _ => False) (fun _ _ => False)
    b.1.base.revealed rb2.1.2.revealed cTime a ra2.2 b (⟨rb2.1.2, b.1.starts⟩, rb2.2) hs.2.1 hf rfl
    (fun k hk => by rw [hf.revealed k hk]; exact hk)
    (fun k hk => by
      by_cases h0 : b.1.base.revealed k = none
      · obtain ⟨e', he', hb'⟩ := hf.opened k h0 hk
        exact Or.inr ⟨e', he', by rw [htime, ← hbound]; exact hb'⟩
      · exact Or.inl h0)
    (fun e' ρ message hseen => by
      rcases hseen with ⟨T, hT⟩ | hT
      · cases hT
      · injection hT with hT
        exact SigningGuessProof.commitmentInput_ne_randomizerInput _ _ _ _ _ _ _ hT.symm)
    (fun p _ hp hseen => by
      rcases hseen with ⟨T, hT⟩ | hT
      · cases hT
      · injection hT with hT
        have he := pendingInput_injective x.1 p (.commitment e) _ _ hT
        subst he
        rw [hpend] at hp
        cases hp)
    (fun T p hseen => by
      rcases hseen with ⟨T', hT⟩ | hT
      · injection hT with _ hT
        subst hT
        exact Or.inr pt.2
      · cases hT)
    (fun T e' l d hseen => by
      rcases hseen with ⟨T', hT⟩ | hT
      · injection hT with _ hT
        cases hT
      · cases hT)
    (fun _ _ h => h)
  refine Or.inr (Or.inr ⟨⟨?_, fun T => hf2.virtual _ _ (hvirt T),
    fun k hk => by rw [hf.revealed k hk]; exact hk, fun hbd => ?_⟩,
    ⟨hcore2, hx, TopO1.frame prims x top _ a ra2.2 b (⟨rb2.1.2, b.1.starts⟩, rb2.2) hs.2.2.1 hf,
      hpads2⟩, hf.signing, hf.trees, hf.exposed, hf.candidates, hm2, hf.carried, hf.log⟩)
  · change truncateHash ra2.1 = match rb2.1.1.low with | .known d => d | .secret _ => 0
    rw [hval, truncateHash_interpret, hd]
    rfl
  · have h0 := hrev e rfl hbd
    rw [hf2.revealed _ h0]
    exact h0

end Build

end ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.truncateHash_interpret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.truncateHash_interpret

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.realCommitment_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.realCommitment_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.runX_sourceCommitmentX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.runX_sourceCommitmentX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.commitment_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildCommit.commitment_sync
