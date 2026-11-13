import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Reads
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealLog
import ThresholdLeanXmssSecurity.Proof.SigningCompilerCouplingUntil

/-! # The coupling of a hash program inside a handler

- `relTriple_simulateQ_until_queries` is `relTriple_simulateQ_until` for a program with a query
  alphabet. The step holds only at the allowed queries.
- `realHonest_tweakable` and `runX_sourceHashProgramX` write both runs of a hash program as
  `simulateQ` of one handler for each side.
- `readCall_stop` states that the stop of the real side persists over a read. `hash_step` couples
  one hash call with `ordinaryRead_sync` and carries the clauses with `ExtraOpen.frame`.
- `hashProgram_core` couples a hash program with no bottom base input for the relation without the
  top clauses. Both sides return the same value, the source state does not move, the log cache of
  the real side resolves the program, and each pending answer stays.
- `hashProgram_sync` is the same coupling for the relation inside a handler.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram
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
open SigningCompilerSyncRealRead SigningCompilerSyncLocalRead SigningCompilerSyncHonestRead
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

/-- `relTriple_simulateQ_until` for a program with a query alphabet. The step holds at the allowed
queries. -/
theorem relTriple_simulateQ_until_queries {ι σ₁ σ₂ α : Type} {spec : OracleSpec ι}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (Bad₁ : σ₁ → Prop) (Bad₂ : σ₂ → Prop) (Sync : σ₁ → σ₂ → Prop) (allowed : ι → Prop)
    (hsticky₁ : ∀ t s, Bad₁ s → ∀ a ∈ support ((impl₁ t).run s), Bad₁ a.2)
    (hsticky₂ : ∀ t s, Bad₂ s → ∀ b ∈ support ((impl₂ t).run s), Bad₂ b.2)
    (hstep : ∀ t, allowed t → ∀ s₁ s₂, Sync s₁ s₂ → ¬ Bad₁ s₁ → ¬ Bad₂ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂) (Until Bad₁ Bad₂ Sync))
    (oa : OracleComp spec α) (hq : Queries allowed oa) :
    ∀ s₁ s₂, Bad₁ s₁ ∨ Bad₂ s₂ ∨ Sync s₁ s₂ →
      RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
        (Until Bad₁ Bad₂ Sync) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s₁ s₂ hs
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rcases hs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  | query_bind t k ih =>
    intro s₁ s₂ hs
    have hb := (isQueryBound_query_bind_iff ..).mp hq
    by_cases hb₁ : Bad₁ s₁
    · exact relTriple_of_support_left fun a ha _ => Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₁ Bad₁ hsticky₁ _ s₁ hb₁ a ha)
    by_cases hb₂ : Bad₂ s₂
    · exact SigningOpeningProof.relTriple_of_support_right fun b hb _ => Or.inr (Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₂ Bad₂ hsticky₂ _ s₂ hb₂ b hb))
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    refine relTriple_bind (hstep t hb.1 s₁ s₂ ((hs.resolve_left hb₁).resolve_left hb₂) hb₁ hb₂)
      fun a b hab => ?_
    rcases hab with h | h | ⟨heq, h⟩
    · exact relTriple_of_support_left fun c hc _ => Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₁ Bad₁ hsticky₁ _ a.2 h c hc)
    · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ => Or.inr (Or.inl
        (SigningOpeningProof.simulateQ_sticky impl₂ Bad₂ hsticky₂ _ b.2 h c hc))
    · rw [heq]
      exact ih b.1 (hb.2 b.1) a.2 b.2 (Or.inr (Or.inr h))

section Programs
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real run of a hash program is the run of one honest call for each query. -/
theorem realHonest_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    realHonest prims x s pads u rest (tweakable oa) =
      simulateQ (fun input => readCall prims x s pads u rest false (.inl (.hash input))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure v =>
    rfl
  | query_bind input next ih =>
    have he : (tweakable (liftM (HashSpec.query input) >>= next) : OracleComp (RoSpec C) α) =
        hashQuery (.hash input) >>= fun answer => tweakable (next answer) := by
      simp [tweakable, simulateQ_bind]
    rw [he, realHonest, SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind,
      simulateQ_bind]
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have h1 : simulateQ (realWorld prims x s pads u rest)
        (free ((hashQuery (C := C) (.hash input)).liftComp (LocalSpec C))) =
        readCall prims x s pads u rest false (.inl (.hash input)) := by
      rw [hashQuery, free]
      erw [liftComp_query, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query]
      exact id_map _
    rw [h1]
    exact congrArg (readCall prims x s pads u rest false (.inl (.hash input)) >>= ·) (funext ih)

/-- The compiler run of a hash program is the fused run of one hash read for each query. -/
theorem runX_sourceHashProgramX {α : Type} (oa : OracleComp HashSpec α) (src : SourceState C)
    (st : CompState C) :
    runX (compBackend x q s pads u rest noise) (sourceHashProgramX x.1 x.2.1 oa) src st =
      (fun z => ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (SigningCompilerUntil.fuse (fun input => sourceHashX x.1 x.2.1 (.hash input))
          (compBackend x q s pads u rest noise)) oa).run (src, st) := by
  have hinner : sourceHashProgramX x.1 x.2.1 oa =
      simulateQ (fun input => sourceHashX x.1 x.2.1 (.hash input)) oa := by
    induction oa using OracleComp.inductionOn with
    | pure v => rfl
    | query_bind input next ih =>
      simp only [sourceHashProgramX, deferredHash, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map] at ih ⊢
      simp only [ih]
      rfl
  rw [← simulateQ_fuse, Functor.map_map, runX, hinner]
  exact (id_map _).symm

/-- The stop of the real side persists over a read. -/
theorem readCall_stop (rq : (RoSpec C).Domain) (st : RealState C) (h : RealStop q st) :
    ∀ r ∈ support ((readCall prims x s pads u rest false rq).run st), RealStop q r.2 := by
  intro r hr
  obtain ⟨hcarried, hcount⟩ :=
    realWorld_read_fields_route prims x (gOf s pads u) rest rq _ (Or.inr rfl) st r hr
  unfold RealStop at h ⊢
  rw [hcarried, hcount]
  rcases h with hflag | hq
  · exact Or.inl hflag
  · exact Or.inr (Nat.lt_succ_of_lt hq)

/-- One hash call with no bottom base input keeps the relation without the top clauses at the
source state `src`, the mark, and each pending answer of `st₀`. Both sides return the same answer. -/
theorem hash_step (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) (src : SourceState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (st₀ : CompState C) (input : HashInput)
    (hbase : ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (a : RealState C) (b : SourceState C × CompState C)
    (hs : b.1 = src ∧
      SyncPre prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a
        (⟨b.1, starts⟩, b.2) ∧ b.2.1.2 = false ∧
      ∀ p, (dataOf x st₀).pending p ≠ none → (dataOf x b.2).pending p ≠ none)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) :
    RelTriple ((readCall prims x s pads u rest false (.inl (.hash input))).run a)
      ((SigningCompilerUntil.fuse (spec := HashSpec) (fun input => sourceHashX x.1 x.2.1 (.hash input))
        (compBackend x q s pads u rest noise) input).run b)
      (Until (RealStop q) (fun z : SourceState C × CompState C => Stop z.2)
        (fun (a' : RealState C) (b' : SourceState C × CompState C) => b'.1 = src ∧
        SyncPre prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a'
          (⟨b'.1, starts⟩, b'.2) ∧ b'.2.1.2 = false ∧
        ∀ p, (dataOf x st₀).pending p ≠ none → (dataOf x b'.2).pending p ≠ none)) := by
  obtain ⟨hsrc, ⟨hcore, hextra, hpads⟩, hmark, hpend⟩ := hs
  have hread := relTriple_supported (ordinaryRead_sync prims x q s pads u rest noise hkeys false
    cCore (.inl (.hash input)) (not_isSlot_hash x input)
    (fun i hi => by cases hi; exact hbase) a b.1 b.2 hcore ha hb hmark)
  have hfuse : (SigningCompilerUntil.fuse (spec := HashSpec)
      (fun input => sourceHashX x.1 x.2.1 (.hash input))
      (compBackend x q s pads u rest noise) input).run b = (fun z => (z.1.1, (z.1.2, z.2))) <$>
        runX (compBackend x q s pads u rest noise) (sourceHashX x.1 x.2.1 (.hash input)) b.1 b.2 :=
    rfl
  have hro : runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 (.inl (.hash input)))
      b.1 b.2 = runX (compBackend x q s pads u rest noise) (sourceHashX x.1 x.2.1 (.hash input))
        b.1 b.2 := rfl
  rw [hro] at hread
  rw [hfuse]
  apply relTriple_map_right
  refine relTriple_post_mono hread ?_
  rintro ra rb ⟨h | h | ⟨⟨hval, hrest⟩, hcore', hframe, hmark'⟩, -, hrb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  obtain ⟨hrb1, hrev⟩ := hrest input rfl
  have hextra' : ExtraOpen prims x top s rev (fun _ _ => False) (withCarried ra.2 cTime)
      (⟨rb.1.2, starts⟩, rb.2) := by
    refine ExtraOpen.frame prims x top s _ _ _ rev rev cTime a ra.2 _ _ hextra hframe rfl
      (fun _ h => h) (fun _ h => Or.inl h) ?_ ?_ ?_ ?_ (fun _ _ h => h)
    · intro e ρ message h
      cases h
      exact hbase e ρ message rfl
    · intro p hk _ h
      cases h
      rw [hrb1] at hk
      exact hrev p.key (PendingInput.hiddenCandidate x.1 p (s p.key)) hk
    · intro T p h
      cases h
    · intro T e l d h
      cases h
  exact Or.inr (Or.inr ⟨hval, hrb1.trans hsrc, ⟨hcore', hextra',
    backend_padsFixed x q s pads u rest noise _ b.2 hpads rb hrb⟩, hmark',
    fun p hp => hframe.pending p (hpend p hp)⟩)

set_option maxHeartbeats 800000 in
/-- A hash program with no bottom base input, for the relation without the top clauses. Both sides
return the same value, the source state does not move, the log cache of the real side resolves the
program, and each pending answer stays. -/
theorem hashProgram_core (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) {α : Type}
    (oa : OracleComp HashSpec α)
    (hbase : Queries (fun input => ∀ e ρ message,
      input ≠ randomizerInput x.1 bottomLayer e ρ message) oa)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncPre prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((realHonest prims x s pads u rest (tweakable oa)).run a)
      (runX (compBackend x q s pads u rest noise) (sourceHashProgramX x.1 x.2.1 oa) b.1.base b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧ rb.1.2 = b.1.base ∧
          DeterministicSigning.Resolves (realLog ra.2) (SigningHitProof.forestHash oa) ra.1 ∧
          SyncPre prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime ra.2
            (⟨rb.1.2, b.1.starts⟩, rb.2) ∧
          rb.2.1.2 = false ∧ ra.2.1.2 = a.1.2 ∧ realLog a ≤ realLog ra.2 ∧
          ∀ p, (dataOf x b.2).pending p ≠ none → (dataOf x rb.2).pending p ≠ none)) := by
  have hrun := relTriple_simulateQ_until_queries (spec := HashSpec)
    (fun input => readCall prims x s pads u rest false (.inl (.hash input)))
    (SigningCompilerUntil.fuse (spec := HashSpec) (fun input => sourceHashX x.1 x.2.1 (.hash input))
      (compBackend x q s pads u rest noise))
    (RealStop q) (fun z : SourceState C × CompState C => Stop z.2) _ _
    (fun t st h => readCall_stop prims x q s pads u rest (.inl (.hash t)) st h)
    (fun t st h r hr => fuse_stop (spec := HashSpec)
      (fun input => sourceHashX x.1 x.2.1 (.hash input)) (compBackend x q s pads u rest noise)
      (fun t' st' h' r' hr' => backendT_stop _ _ _ q s pads _ _ noise rest t' st' h' r' hr')
      t st h r hr)
    (fun input hin a' b' hs' ha' hb' => hash_step prims x q s pads u rest noise hkeys top rev cCore
      cTime b.1.base b.1.starts b.2 input hin a' b' hs' ha' hb') oa hbase a (b.1.base, b.2)
    (Or.inr (Or.inr ⟨rfl, hs, hmark, fun _ h => h⟩))
  have hlog : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 := hs.2.1.rest.logAgreement
  have hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a) :=
    hs.1.1.1.realPrivate
  rw [realHonest_tweakable, runX_sourceHashProgramX]
  apply relTriple_map_right
  refine relTriple_post_mono (relTriple_supported hrun) ?_
  rintro ra rb ⟨h | h | ⟨hval, hsrc, hpre, hm, hpend⟩, hra, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  rw [← realHonest_tweakable, ← SigningHitProof.hashEmbed_forestHash] at hra
  obtain ⟨hres, -, -, hle, hcarried⟩ :=
    honest_resolves prims x s pads u rest noise (SigningHitProof.forestHash oa) a hlog hpriv ra hra
  exact Or.inr (Or.inr ⟨hval, hsrc, hres, hpre, hm, hcarried, hle, hpend⟩)

/-- The hash-program coupling inside a handler, from the coupling without the top clauses. -/
theorem hashProgram_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (cCore cTime : Carried C) {α : Type}
    (oa : OracleComp HashSpec α)
    (hbase : Queries (fun input => ∀ e ρ message,
      input ≠ randomizerInput x.1 bottomLayer e ρ message) oa)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncAt prims x s pads u rest noise top rev (fun _ _ => False) cCore cTime a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((realHonest prims x s pads u rest (tweakable oa)).run a)
      (runX (compBackend x q s pads u rest noise) (sourceHashProgramX x.1 x.2.1 oa) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b (fun _ => rev)
        (fun va vb => va = vb ∧ rb.1.2 = b.1.base ∧
          DeterministicSigning.Resolves (realLog ra.2) (SigningHitProof.forestHash oa) va) ra rb) := by
  obtain ⟨hpre, htop⟩ := (syncAt_iff_pre prims x s pads u rest noise top rev _ cCore cTime a b).1 hs
  refine relTriple_post_mono
    (hashProgram_core prims x q s pads u rest noise hkeys top rev cCore cTime oa hbase a b hpre
      ha hb hmark) ?_
  rintro ra rb (h | h | ⟨hv, hsrc, hres, hpre', hm, hc, hlog, hpend⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨⟨hv, hsrc, hres⟩, ?_, ?_, ?_, ?_, ?_, hm, hc, hlog⟩)
    · refine (syncAt_iff_pre prims x s pads u rest noise top rev _ cCore cTime _ _).2 ⟨hpre', ?_⟩
      obtain ⟨start, result, hrun, hout, hle⟩ := htop.topRun
      exact ⟨fun bi l d => hpend _ (htop.topRows bi l d), start, result, hrun, hout, hle.trans hlog⟩
    · rw [hsrc]
    · rw [hsrc]
    · rw [hsrc]
    · rw [hsrc]

end Programs

end ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.relTriple_simulateQ_until_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.relTriple_simulateQ_until_queries

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.realHonest_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.realHonest_tweakable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.runX_sourceHashProgramX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.runX_sourceHashProgramX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.readCall_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.readCall_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.hash_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.hash_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.hashProgram_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.hashProgram_core

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.hashProgram_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1HashProgram.hashProgram_sync
