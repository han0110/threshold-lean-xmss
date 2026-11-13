import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1HashProgram
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1BaseRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Queries

/-! # The codeword search inside a handler

- `sourceRoProgramX_tweakable` writes the compiler run of a tweakable program as a hash program.
- `realHonest_bind` and `sourceHashProgramX_bind` split both runs of a hash program at a bind.
- `realHonest_oracleHash` and `sourceHashProgramX_oracleHash` write one hash call as one read.
- `realHonest_stop` and `compHash_stop` state that the stop of each side persists over a run.
- `codeword_core` couples `signCodeword` call by call. `hashProgram_sync` couples the commitment call
  and the search, and `baseRead_sync` couples the base call.
- `codeword_sync` adds the resolution of the search on the log cache of the real side.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Codeword
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Reads SigningCompilerO1RealLog
open SigningCompilerO1HashProgram SigningCompilerO1BaseRead SigningCompilerO1Queries
open SigningCompilerSyncLocalRead
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind Queries

/-- The compiler run of a tweakable program is the run of the hash program. -/
theorem sourceRoProgramX_tweakable (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) {α : Type} (oa : OracleComp HashSpec α) :
    sourceRoProgramX prims P seeds (tweakable oa) = sourceHashProgramX P seeds oa := by
  induction oa using OracleComp.inductionOn with
  | pure v => rfl
  | query_bind input next ih =>
    simp only [sourceRoProgramX, tweakable, sourceHashProgramX, deferredHash, simulateQ_bind,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map] at ih ⊢
    exact congrArg (_ >>= ·) (funext ih)

/-- The compiler run of a hash program splits at a bind. -/
theorem sourceHashProgramX_bind (P : PublicParameter) (seeds : C.Term → HashOutput) {α β : Type}
    (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    sourceHashProgramX (C := C) P seeds (oa >>= f) =
      sourceHashProgramX P seeds oa >>= fun v => sourceHashProgramX P seeds (f v) := by
  simp only [sourceHashProgramX, deferredHash, simulateQ_bind]

/-- One hash call of the compiler is one hash read. -/
theorem sourceHashProgramX_oracleHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : HashInput) :
    sourceHashProgramX (C := C) P seeds (Concrete.oracleHash input) = sourceHashX P seeds (.hash input) :=
  rfl

section Calls
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real run of a hash program splits at a bind. -/
theorem realHonest_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (a : RealState C) :
    (realHonest prims x s pads u rest (tweakable (oa >>= f))).run a =
      (realHonest prims x s pads u rest (tweakable oa)).run a >>= fun r =>
        (realHonest prims x s pads u rest (tweakable (f r.1))).run r.2 := by
  rw [realHonest_tweakable, realHonest_tweakable, simulateQ_bind, StateT.run_bind]
  exact congrArg (_ >>= ·) (funext fun r => by rw [realHonest_tweakable])

/-- One real hash call is one read. -/
theorem realHonest_oracleHash (input : HashInput) :
    realHonest prims x s pads u rest (tweakable (Concrete.oracleHash input)) =
      readCall prims x s pads u rest false (.inl (.hash input)) := by
  rw [realHonest_tweakable]
  exact (simulateQ_query _ _).trans (id_map _)

/-- The stop of the real side persists over a hash program. -/
theorem realHonest_stop {α : Type} (oa : OracleComp HashSpec α) (st : RealState C)
    (h : RealStop q st) :
    ∀ r ∈ support ((realHonest prims x s pads u rest (tweakable oa)).run st), RealStop q r.2 := by
  rw [realHonest_tweakable]
  exact simulateQ_sticky _ (RealStop q)
    (fun t st' h' => readCall_stop prims x q s pads u rest (.inl (.hash t)) st' h') oa st h

set_option maxHeartbeats 800000 in
/-- The stop of the compiler side persists over a hash program. -/
theorem compHash_stop {α : Type} (oa : OracleComp HashSpec α) (src : SourceState C)
    (st : CompState C) (h : Stop st) :
    ∀ r ∈ support (runX (compBackend x q s pads u rest noise) (sourceHashProgramX x.1 x.2.1 oa)
      src st), Stop r.2 := by
  intro r hr
  rw [runX_sourceHashProgramX, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  have hsticky : ∀ (t : HashInput) (st' : SourceState C × CompState C), Stop st'.2 →
      ∀ r' ∈ support ((SigningCompilerUntil.fuse (spec := HashSpec)
        (fun input => sourceHashX x.1 x.2.1 (.hash input))
        (compBackend x q s pads u rest noise) t).run st'), Stop r'.2.2 :=
    fun t st' h' r' hr' => fuse_stop (spec := HashSpec)
      (fun input => sourceHashX x.1 x.2.1 (.hash input)) (compBackend x q s pads u rest noise)
      (fun t'' st'' h'' r'' hr'' => backendT_stop _ _ _ q s pads _ _ noise rest t'' st'' h'' r'' hr'')
      t st' h' r' hr'
  exact simulateQ_sticky _ (fun z : SourceState C × CompState C => Stop z.2) hsticky oa (src, st) h z hz

/-- The codeword search on both sides, call by call. Both sides give the same result, and the
source state does not move. -/
theorem codeword_core (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) (commitment : Digest)
    (e : KeyIndex) (message : Message) (ρ : Digest) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a b)
    (hsig : a.1.2.1.1.bound = cCore.1.1.bound) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((realHonest prims x s pads u rest (signCodeword x.1 commitment e message ρ)).run a)
      (runX (compBackend x q s pads u rest noise)
        (sourceRoProgramX prims x.1 x.2.1 (signCodeword x.1 commitment e message ρ)) b.1.base b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧ rb.1.2 = b.1.base ∧
          SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime ra.2
            (⟨rb.1.2, b.1.starts⟩, rb.2) ∧ rb.2.1.2 = false)) := by
  have hq1 : Queries (fun input => ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
      (Concrete.oracleHash (commitmentInput x.1 e ρ) : OracleComp HashSpec HashOutput) :=
    Queries.query _ fun f τ m =>
      SigningGuessProof.commitmentInput_ne_randomizerInput _ _ _ _ _ _ _
  unfold signCodeword
  rw [sourceRoProgramX_tweakable, realHonest_bind, sourceHashProgramX_bind, runX_bind]
  refine relTriple_bind (hashProgram_sync prims x q s pads u rest noise hkeys top rev cCore cTime _
    hq1 a b hs ha hb hmark) fun r1a r1b h1 => ?_
  rcases h1 with h1 | h1 | ⟨⟨hv1, hsrc1, -⟩, hs1, -, -, -, -, hm1, hc1, -⟩
  · exact relTriple_of_support_left fun c hc _ =>
      Or.inl (realHonest_stop prims x q s pads u rest _ _ h1 c hc)
  · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ =>
      Or.inr (Or.inl (compHash_stop x q s pads u rest noise _ _ _ h1 c hc))
  by_cases ha1 : RealStop q r1a.2
  · exact relTriple_of_support_left fun c hc _ =>
      Or.inl (realHonest_stop prims x q s pads u rest _ _ ha1 c hc)
  by_cases hb1 : Stop r1b.2
  · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ =>
      Or.inr (Or.inl (compHash_stop x q s pads u rest noise _ _ _ hb1 c hc))
  rw [hv1]
  by_cases hc : truncateHash r1b.1.1 ≠ commitment
  · rw [if_pos hc, realHonest_tweakable, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hsrc1, hs1, hm1⟩))
  · simp only [hc, if_false]
    rw [realHonest_bind, sourceHashProgramX_bind, runX_bind, realHonest_oracleHash,
      sourceHashProgramX_oracleHash]
    refine relTriple_bind (baseRead_sync prims x q s pads u rest noise hkeys false top rev cCore cTime
      e ρ (bytesLE 32 message) r1a.2 (⟨r1b.1.2, b.1.starts⟩, r1b.2) hs1 (by rw [hc1]; exact hsig)
      htime ha1 hb1 hm1) fun r2a r2b h2 => ?_
    rcases h2 with h2 | h2 | ⟨hv2, hs2, hsrc2, hm2, -, -, -⟩
    · exact relTriple_of_support_left fun c hc _ =>
        Or.inl (realHonest_stop prims x q s pads u rest _ _ h2 c hc)
    · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ =>
        Or.inr (Or.inl (compHash_stop x q s pads u rest noise _ _ _ h2 c hc))
    by_cases ha2 : RealStop q r2a.2
    · exact relTriple_of_support_left fun c hc _ =>
        Or.inl (realHonest_stop prims x q s pads u rest _ _ ha2 c hc)
    by_cases hb2 : Stop r2b.2
    · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ =>
        Or.inr (Or.inl (compHash_stop x q s pads u rest noise _ _ _ hb2 c hc))
    rw [hv2]
    refine relTriple_post_mono (hashProgram_sync prims x q s pads u rest noise hkeys top rev cCore
      cTime _ (queries_noBase x.1 _ (queries_grind _ _ _ _ _ _ _)) r2a.2 (⟨r2b.1.2, b.1.starts⟩, r2b.2)
      hs2 ha2 hb2 hm2) ?_
    rintro ra rb (h | h | ⟨⟨hv, hsrc, -⟩, hs3, -, -, -, -, hm3, -, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hv, hsrc.trans (hsrc2.trans hsrc1), hs3, hm3⟩)

/-- The codeword search of a signer or of the honest signature on both sides, at a revealed opening.
Both sides give the same result, and the log cache of the real side resolves the search. It is the
form of `codeword_mid` for each view and each reveal map. -/
theorem codeword_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) (commitment : Digest)
    (e : KeyIndex) (message : Message) (ρ : Digest) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a b)
    (hsig : a.1.2.1.1.bound = cCore.1.1.bound) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (hbound : cCore.1.1.bound e = some message)
    (hopen : b.1.base.revealed (.opening bottomLayer e) ≠ none)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((realHonest prims x s pads u rest (signCodeword x.1 commitment e message ρ)).run a)
      (runX (compBackend x q s pads u rest noise)
        (sourceRoProgramX prims x.1 x.2.1 (signCodeword x.1 commitment e message ρ)) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b (fun _ => rev)
        (fun va vb => va = vb ∧ rb.1.2 = b.1.base ∧
          DeterministicSigning.Resolves (realLog ra.2)
            (SigningCompilerO1RealLog.codewordForest x.1 commitment e message ρ) va) ra rb) := by
  have hlog : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 := hs.2.1.rest.logAgreement
  have hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a) :=
    hs.1.1.1.realPrivate
  refine relTriple_post_mono (relTriple_supported (codeword_core prims x q s pads u rest noise hkeys
    top rev cCore cTime commitment e message ρ a b hs hsig htime ha hb hmark)) ?_
  rintro ra rb ⟨h | h | ⟨hv, hsrc, hsync, hm⟩, hra, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  rw [← hashEmbed_codewordForest] at hra
  generalize codewordForest x.1 commitment e message ρ = cf at hra ⊢
  obtain ⟨hres, -, -, hle, hcarried⟩ :=
    honest_resolves prims x s pads u rest noise cf a hlog hpriv ra (no_implicit_lambda% hra)
  refine Or.inr (Or.inr ⟨⟨hv, hsrc, hres⟩, hsync, ?_, ?_, ?_, ?_, hm, hcarried, hle⟩)
  · rw [hsrc]
  · rw [hsrc]
  · rw [hsrc]
  · rw [hsrc]

end Calls

end ThresholdLeanXmssSecurity.SigningCompilerO1Codeword

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.sourceRoProgramX_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.sourceRoProgramX_tweakable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.sourceHashProgramX_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.sourceHashProgramX_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.sourceHashProgramX_oracleHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.sourceHashProgramX_oracleHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.realHonest_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.realHonest_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.realHonest_oracleHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.realHonest_oracleHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.realHonest_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.realHonest_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.compHash_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.compHash_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.codeword_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.codeword_core

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.codeword_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Codeword.codeword_sync
