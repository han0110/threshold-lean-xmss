import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Verify
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Calls
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1BaseRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SyncHandlers

/-! # A local query of the forger in the O1 coupling

`step_local` states that a local query of the forger keeps `SyncO1` with the fixed pads, or stops
one side.

- `realLocal_run` and `compLocal_run` unfold the two handlers. Both write the flag and the
  candidates of the state before the call.
- A query with a hidden hit raises the real flag, so the real side stops.
- `local_uniform` couples a uniform query. Both sides sample the same value. The real side adds
  only a log entry and a monitor step, which `CallFrame` allows.
- `local_slot` couples a slot read. With no hidden hit the term of the slot is revealed.
- `local_base` couples a hash call at a bottom base input.
- `local_ordinary` couples each other read.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Local
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open SigningCompilerSyncBackend SigningCompilerSyncRealRead SigningCompilerSyncTrigger
open SigningCompilerSyncLocalRead SigningCompilerSyncHonestRead
open SigningCompilerO1Calls SigningCompilerO1Reads SigningCompilerO1BaseRead SigningCompilerO1Verify
open SigningCompilerO1SyncHandlers
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  SigningLaneUnionProof.traceStepAt

section Local
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real state after a uniform query with the answer `v`. The query adds a log entry and a
monitor step. -/
def uniformAfter (n : ℕ) (a : RealState C) (v : Fin (n + 1)) : RealState C :=
  ((((((a.1.1.1.1.1.1, a.1.1.1.1.1.2.logQuery (.inl (.inl (.inl n))) v),
    SigningFlatEagerProof.queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1) a.1.1.1.1.2
      (SigningPartnerBoundProof.hashEntry (C := C) ⟨.inl (.inl (.inl n)), v⟩)), a.1.1.1.2), a.1.1.2),
    a.1.2), a.2)

/-- The real uniform query samples a value and keeps each part of the state that the relation
reads. -/
theorem realWorld_uniform (n : ℕ) (a : RealState C) :
    (realWorld prims x s pads u rest (.inl (.inl (.inl n)))).run a =
      (fun v => (v, uniformAfter x n a v)) <$> query (spec := unifSpec) n := by
  change (_root_.ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x) (realImpl x (gOf s pads u) rest)
    (.inl (.inl (.inl n)))).run a = _
  simp only [_root_.ThresholdLeanXmssSecurity.fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
      rawCarriedLogged, HasQuery.instOfMonadLift_query,
      SigningGuessProof.signingRawWorld, SigningGuessProof.signingRawLocal,
      simulateQ_map, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_map,
      StateT.run_bind, SigningGuessProof.privateRoObserve,
      Functor.map_map, bind_map_left, map_bind]
  have hnh : ∀ i, ¬SigningFlatProof.HashCallAt i (.inl (.inl (.inl n)) : (WorldSpec C).Domain) := by
    rintro i (h | h) <;> cases h
  rw [realImpl_uniform]
  simp only [SigningOneRunProof.jointCachedExtra, nonhash_cachedExtra _ _ _ _ _ hnh,
    nonhash_traceStepAt _ _ _ _ _ _ _ hnh, simulateQ_pure, StateT.run_pure, map_pure,
    bind_map_left]
  rw [map_eq_bind_pure_comp]
  rfl

/-- A real call keeps the carried state. -/
theorem realWorld_carried (t : (WorldSpec C).Domain) (a : RealState C) (r : (WorldSpec C).Range t × RealState C)
    (hr : r ∈ support ((realWorld prims x s pads u rest t).run a)) : r.2.1.2 = a.1.2 := by
  change r ∈ support ((_root_.ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) t).run a) at hr
  simp only [_root_.ThresholdLeanXmssSecurity.fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
      rawCarriedLogged, simulateQ_map, simulateQ_bind, StateT.run_map, StateT.run_bind,
      support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hr
  obtain ⟨_, ⟨_, ⟨_, ⟨_, -, rfl⟩, ⟨_, -, rfl⟩⟩, rfl⟩, rfl⟩ := hr
  rfl

/-- The real handler of a local query runs the call and writes the flag and the candidates of the
carried state before the call. -/
theorem realLocal_run (top : TopTree) (t : (LocalSpec C).Domain) (a : RealState C) :
    (realOracles prims x s pads u rest top (.inl t)).run a =
      (fun r => (r.1, ((r.2.1.1, ((a.1.2.1.1, a.1.2.1.2 ||
        SigningCoreProof.hiddenHit x a.1.2.1.1.corrupt t), a.1.2.2.1,
          a.1.2.2.2 ++ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t)), r.2.2))) <$>
        (realWorld prims x s pads u rest (.inl (.inl t))).run a :=
  realAdv_local_run prims x top (gOf s pads u) rest t a

/-- The compiler handler of a local query sets the mark, runs the call and writes the flag and the
candidates of the source state before the call. -/
theorem compLocal_run (top : TopTree) (t : (LocalSpec C).Domain)
    (b : SourceStateO1 C × CompState C) :
    (compOracles prims x q s pads u rest noise top (.inl t)).run b =
      (fun r => (r.1.1, (⟨{ r.1.2 with
        hiddenFlag := b.1.base.hiddenFlag || SigningCoreProof.hiddenHit x b.1.base.signing.corrupt t
        candidates := b.1.base.candidates ++
          unreleasedCandidates x.1 b.1.base.signing b.1.base.exposed t }, b.1.starts⟩, r.2))) <$>
        runX (compBackend x q s pads u rest noise) (sourceLocalX prims x t) b.1.base
          ((b.2.1.1, b.1.base.hiddenFlag ||
            SigningCoreProof.hiddenHit x b.1.base.signing.corrupt t), b.2.2) := by
  have h : (compOracles prims x q s pads u rest noise top (.inl t)).run b =
      (fun w => (w.1, (⟨w.2.1, b.1.starts⟩, w.2.2))) <$>
        (SigningCompilerUntil.fuse (sourceOraclesX prims x top) (compBackend x q s pads u rest noise)
          (.inl t)).run (b.1.base, b.2) := by
    change (fun z => (z.1.1, (z.1.2, z.2))) <$> runXO1 (compBackend x q s pads u rest noise)
        (liftBaseX (sourceOraclesX prims x top (.inl t))) b.1 b.2 =
      (fun w => (w.1, (⟨w.2.1, b.1.starts⟩, w.2.2))) <$> ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        runX (compBackend x q s pads u rest noise) (sourceOraclesX prims x top (.inl t)) b.1.base b.2)
    rw [runXO1_liftBaseX, Functor.map_map, Functor.map_map]
  rw [h, compAdv_local_run, Functor.map_map]

/-- Maps on both sides of a coupling. -/
theorem relTriple_map_both {α β γ δ : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} {S : γ → δ → Prop} (f : α → γ) (g : β → δ) (h : RelTriple oa ob R)
    (hS : ∀ a b, R a b → S (f a) (g b)) : RelTriple (f <$> oa) (g <$> ob) S := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact relTriple_bind h fun a b hab => relTriple_pure_pure (hS a b hab)

/-- The post of the call inside a local query. Both sides return the same answer, and the relation
holds after the candidates of the query. -/
def LocalPost (top : TopTree) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (new : List (HiddenKey × Digest)) {α : Type} (ra : α × RealState C)
    (rb : (α × SourceState C) × CompState C) : Prop :=
  RealStop q ra.2 ∨ Stop rb.2 ∨
    (ra.1 = rb.1.1 ∧ rb.1.2.hiddenFlag = b.1.base.hiddenFlag ∧
      SyncO1 prims x top s pads noise (gOf s pads u) rest (withCandidates ra.2 (a.1.2.2.2 ++ new))
        (⟨{ rb.1.2 with candidates := b.1.base.candidates ++ new }, b.1.starts⟩, rb.2) ∧
      PadsFixed x pads rb.2)

/-- A released candidate is not in the candidate list. The parser stays abstract, so that the
kernel does not unfold it. -/
theorem not_mem_candidateList (parse : HashInput → Option (HiddenKey × Digest))
    (released : HiddenKey → Prop) (input : HashInput) (c : HiddenKey × Digest)
    (hh : parse input = some c) (hr : released c.1) :
    c ∉ candidateList parse released (.inr (.inl (.hash input)) : (LocalSpec C).Domain) := by
  intro hc
  simp only [candidateList, hh, if_pos hr] at hc
  exact List.not_mem_nil hc

/-- A candidate of a local query is the hidden candidate of its hash input, and it is not
released. -/
theorem mem_unreleased (P : PublicParameter) (sig : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (t : (LocalSpec C).Domain) (c : HiddenKey × Digest)
    (hc : c ∈ unreleasedCandidates P sig trees t) :
    ∃ input, t = .inr (.inl (.hash input)) ∧ hiddenCandidate P input = some c ∧
      ¬Released sig trees c.1 := by
  rw [unreleasedCandidates_eq_candidateList] at hc
  obtain ⟨input, ht, hh⟩ := candidateList_mem (hiddenCandidate P) (Released sig trees) _ c hc
  subst ht
  exact ⟨input, rfl, hh, fun hr => not_mem_candidateList _ _ input c hh hr hc⟩

/-- The relation inside the handler after the call gives the boundary relation after the
candidates of the query. A new candidate that carries its secret has a revealed key. -/
theorem local_candidates (top : TopTree) (t : (LocalSpec C).Domain) (a : RealState C)
    (b : SourceStateO1 C × CompState C) (ra : RealState C) (rb : SourceState C × CompState C)
    (hcar : ra.1.2 = a.1.2) (hcand : rb.1.candidates = b.1.base.candidates)
    (hs : SyncAt prims x s pads u rest noise top rb.1.revealed (fun _ _ => False) a.1.2 a.1.2 ra
      (⟨rb.1, b.1.starts⟩, rb.2))
    (hpaid : ∀ c ∈ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t, c.2 = s c.1 →
      rb.1.revealed c.1 ≠ none) :
    SyncO1 prims x top s pads noise (gOf s pads u) rest
        (withCandidates ra (a.1.2.2.2 ++ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t))
        (⟨{ rb.1 with candidates := b.1.base.candidates ++
          unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t }, b.1.starts⟩, rb.2) ∧
      PadsFixed x pads rb.2 := by
  obtain ⟨hc, hx, ht, hp⟩ := hs
  have heq : withCarried ra a.1.2 = ra := by
    rw [← hcar]
    exact withCarried_self ra
  rw [heq] at hc hx
  have hfresh : ∀ c ∈ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t,
      ∀ lay e, c.1 = .opening lay e → c.2 ≠ s c.1 := by
    intro c hc' lay e hk he
    obtain ⟨-, -, -, hrel⟩ := mem_unreleased x.1 _ _ t c hc'
    have hr := hpaid c hc' he
    rw [hk] at hr
    have hrr : Released ra.1.2.1.1 ra.1.2.2.1 (.opening lay e) := hx.rest.revealedReleased lay e hr
    rw [hcar, ← hk] at hrr
    exact hrel hrr
  have hx' := ExtraOpen.candidates prims x top s (fun _ _ => False) rb.1.revealed ra
    (⟨rb.1, b.1.starts⟩, rb.2) _ hx hpaid hfresh
  have hc' := syncCore_candidates x s pads rest noise (gOf s pads u) ra rb.1 rb.2 _ hc hpaid
  rw [hcar, hcand] at hx' hc'
  exact (syncO1_iff_syncIn prims x s pads u rest noise top _ _).2
    ⟨hc', hx', ⟨ht.topRows, ht.topRun⟩, hp⟩

/-- With no hidden hit, the term of a PRF read of the forger is revealed. -/
theorem revealed_of_noHit (D : Finset C.Party) (T : C.Term) (p : Point)
    (h : SigningCoreProof.hiddenHit x D (.inr (.inl (.prf (x.2.1 T) p))) = false) :
    TprfSecurityProof.Revealed D (.inl T) := by
  simp only [SigningCoreProof.hiddenHit, decide_eq_false_iff_not, not_exists, not_and,
    not_not] at h
  exact h T rfl

/-- A uniform query. Both sides sample the same value. -/
theorem local_uniform (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (n : ℕ) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2) :
    RelTriple ((realWorld prims x s pads u rest (.inl (.inl (.inl n)))).run a)
      (runX (compBackend x q s pads u rest noise) (sourceLocalX prims x (.inl n)) b.1.base b.2)
      (LocalPost prims x q s pads u rest noise top a b
        (unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 (.inl n))) := by
  obtain ⟨hcore, hx, htop, hp⟩ := (syncO1_iff_syncIn prims x s pads u rest noise top a b).1 hs
  have hcomp : runX (compBackend x q s pads u rest noise) (sourceLocalX prims x (.inl n)) b.1.base b.2 =
      (fun v => ((v, b.1.base), b.2)) <$> query (spec := unifSpec) n := by
    change runX (compBackend x q s pads u rest noise) (liftM (deferredQueryX (C := C) (.uniform n)))
      b.1.base b.2 = _
    rw [runX_deferred, backendT_uniform capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest n
      b.2 hcore.1.1.restFree, Functor.map_map]
  rw [realWorld_uniform, hcomp]
  refine relTriple_map_both _ _ (relTriple_refl (query (spec := unifSpec) n)) ?_
  rintro v v' (rfl : v = v')
  have hlog : SigningCacheLogProof.logCache (a.1.1.1.1.1.2.logQuery (.inl (.inl (.inl n))) v) =
      SigningCacheLogProof.logCache a.1.1.1.1.1.2 := by
    funext query
    rw [SigningCacheLogProof.logCache_logQuery]
    exact Option.or_none
  have hf : CallFrame x (fun _ => False) a (uniformAfter x n a v) (b.1.base, b.2) (b.1.base, b.2) :=
    { carried := rfl
      visible := le_refl _
      fresh := fun _ h => Or.inl h
      log := fun query w h => (congrFun hlog query).trans h
      logAgreement := fun hl => by
        change SigningPartnerCompareProof.LogAgreement x.1
          ((a.1.1.1.1.1.1, a.1.1.1.1.1.2.logQuery (.inl (.inl (.inl n))) v))
        unfold SigningPartnerCompareProof.LogAgreement at hl ⊢
        rw [hlog]
        exact hl
      trace := rfl
      signing := rfl
      trees := rfl
      exposed := rfl
      candidates := rfl
      revealed := fun _ _ => rfl
      opened := fun _ h h' => (h' h).elim
      pending := fun _ h => h
      virtual := fun _ _ h => h }
  have hx' := ExtraOpen.frame prims x top s (fun _ => False) (fun _ _ => False) (fun _ _ => False)
    b.1.base.revealed b.1.base.revealed a.1.2 a (uniformAfter x n a v) b b hx hf rfl
    (fun _ h => h) (fun _ h => Or.inl h) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h.elim)
    (fun _ _ _ _ h => h.elim) (fun _ _ h => h)
  have ht := TopO1.frame prims x top _ a (uniformAfter x n a v) b b ⟨htop.topRows, htop.topRun⟩ hf
  have hcore' : SyncCore x s pads noise (gOf s pads u) rest (uniformAfter x n a v) (b.1.base, b.2) :=
    ⟨⟨syncFields_observe x hkeys s pads u rest noise a (uniformAfter x n a v) (b.1.base, b.2)
      hcore.1.1 hcore.1.1.realPrivate (le_refl _) rfl rfl, hcore.1.2⟩, hcore.2⟩
  have hsync := (syncO1_iff_syncIn prims x s pads u rest noise top (uniformAfter x n a v) b).2
    ⟨hcore', hx', ⟨ht.topRows, ht.topRun⟩, hp⟩
  have hnil : unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 (.inl n : (LocalSpec C).Domain) = [] := rfl
  refine Or.inr (Or.inr ⟨rfl, rfl, ?_, hsync.2⟩)
  rw [hnil, List.append_nil, List.append_nil]
  exact hsync.1

/-- A slot read with no hidden hit. The term of the slot is revealed. -/
theorem local_slot (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (z : TprfSecurityProof.Slot C) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hhit : SigningCoreProof.hiddenHit x a.1.2.1.1.corrupt
      (.inr (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))) = false)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((readCall prims x s pads u rest true
        (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))).run a)
      (runX (compBackend x q s pads u rest noise)
        (sourceRoX prims x.1 x.2.1 (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))) b.1.base b.2)
      (LocalPost prims x q s pads u rest noise top a b (unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1
        (.inr (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))))) := by
  obtain ⟨hcore, hx, htop, hp⟩ := (syncO1_iff_syncIn prims x s pads u rest noise top a b).1 hs
  have hfields := hcore.1.1
  apply TreeCheckKernelCoupling.relTriple_of_support
  intro ra hra rb hrb
  rcases slotRead_sync prims x q s pads u rest noise hkeys true a.1.2 z a b.1.base b.2 hcore ha hb
    hmark ra (no_implicit_lambda% hra) rb hrb with h | h | ⟨⟨hv, -⟩, hsync, hf, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hx' := ExtraOpen.frame prims x top s
    (fun query => query = TprfSecurityProof.slotInput x.2.1 x.2.2 z) (fun _ _ => False)
    (fun _ _ => False) b.1.base.revealed rb.1.2.revealed a.1.2 a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2)
    hx hf rfl
    (fun k hk => by rw [hf.revealed k hk]; exact hk)
    (fun k hk => by
      by_cases h0 : b.1.base.revealed k = none
      · obtain ⟨e, he, hbd⟩ := hf.opened k h0 hk
        exact Or.inr ⟨e, he, hfields.bound ▸ hbd⟩
      · exact Or.inl h0)
    (fun e ρ message h => by rcases z with ⟨T, p⟩ | w <;> cases h)
    (fun p _ _ h => by rcases z with ⟨T, p'⟩ | w <;> cases h)
    (fun T p h => by
      rw [← h] at hhit
      exact Or.inl (revealed_of_noHit x _ T p hhit))
    (fun T e l d h => by
      rw [← h] at hhit
      exact Or.inl (revealed_of_noHit x _ T _ hhit))
    (fun _ _ h => h)
  have ht := TopO1.frame prims x top _ a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2)
    ⟨htop.topRows, htop.topRun⟩ hf
  have hpads := backend_padsFixed x q s pads u rest noise _ b.2 hp _ hrb
  have hpaid : ∀ c ∈ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1
      (.inr (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 z))), c.2 = s c.1 →
      rb.1.2.revealed c.1 ≠ none := by
    intro c hc _
    obtain ⟨input, hrq, -⟩ := mem_unreleased x.1 _ _ _ c hc
    rcases z with ⟨T, p⟩ | w <;> cases hrq
  refine Or.inr (Or.inr ⟨hv, hsync.1.1.flag.trans hfields.flag.symm, ?_⟩)
  exact local_candidates prims x s pads u rest noise top _ a b ra.2 (rb.1.2, rb.2) hf.carried
    hf.candidates ⟨hsync, hx', ⟨ht.topRows, ht.topRun⟩, hpads⟩ hpaid

/-- A hash call at a bottom base input. -/
theorem local_base (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (e : KeyIndex) (ρ : Digest) (message : HashInput)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((readCall prims x s pads u rest true
        (.inl (.hash (randomizerInput x.1 bottomLayer e ρ message)))).run a)
      (runX (compBackend x q s pads u rest noise)
        (sourceRoX prims x.1 x.2.1 (.inl (.hash (randomizerInput x.1 bottomLayer e ρ message))))
        b.1.base b.2)
      (LocalPost prims x q s pads u rest noise top a b (unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1
        (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e ρ message)))))) := by
  have h := baseRead_sync prims x q s pads u rest noise hkeys true top b.1.base.revealed a.1.2 a.1.2
    e ρ message a b ((syncO1_iff_syncIn prims x s pads u rest noise top a b).1 hs) rfl rfl ha hb hmark
  refine relTriple_post_mono h ?_
  rintro ra rb (h1 | h1 | ⟨hv, hsync, hsrc, -, hcar, -, hrev⟩)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  have hpaid : ∀ c ∈ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1
      (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e ρ message)))), c.2 = s c.1 →
      rb.1.2.revealed c.1 ≠ none := by
    intro c hc he
    obtain ⟨input, hrq, hcand, -⟩ := mem_unreleased x.1 _ _ _ c hc
    cases hrq
    rw [hiddenCandidate_randomizerInput] at hcand
    cases hcand
    rw [hsrc]
    exact hrev he
  rw [← hsrc] at hsync
  refine Or.inr (Or.inr ⟨hv, by rw [hsrc], ?_⟩)
  exact local_candidates prims x s pads u rest noise top _ a b ra.2 (rb.1.2, rb.2) hcar
    (by rw [hsrc]) hsync hpaid

/-- A read that is no slot and no bottom base input. -/
theorem local_ordinary (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rq : (RoSpec C).Domain) (hslot : ¬IsSlot x (readInput rq))
    (hbase : ∀ input, readInput rq = .hash input →
      ∀ e ρ message, input ≠ randomizerInput x.1 bottomLayer e ρ message)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((readCall prims x s pads u rest true rq).run a)
      (runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 rq) b.1.base b.2)
      (LocalPost prims x q s pads u rest noise top a b
        (unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 (.inr rq))) := by
  obtain ⟨hcore, hx, htop, hp⟩ := (syncO1_iff_syncIn prims x s pads u rest noise top a b).1 hs
  have hread := ordinaryRead_sync prims x q s pads u rest noise hkeys true a.1.2 rq hslot hbase a
    b.1.base b.2 hcore ha hb hmark
  refine relTriple_post_mono (relTriple_supported hread) ?_
  rintro ra rb ⟨hpost, -, hrb⟩
  rcases hpost with h | h | ⟨⟨hv, hval⟩, hsync, hf, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hfields := hcore.1.1
  have hx' := ExtraOpen.frame prims x top s (fun query => query = readInput rq) (fun _ _ => False)
    (fun _ _ => False) b.1.base.revealed rb.1.2.revealed a.1.2 a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2)
    hx hf rfl
    (fun k hk => by rw [hf.revealed k hk]; exact hk)
    (fun k hk => by
      by_cases h0 : b.1.base.revealed k = none
      · obtain ⟨e, he, hbd⟩ := hf.opened k h0 hk
        exact Or.inr ⟨e, he, hfields.bound ▸ hbd⟩
      · exact Or.inl h0)
    (fun e ρ message h => hbase _ h.symm e ρ message rfl)
    (fun p hr _ h => by
      obtain ⟨hsrc, hrev⟩ := hval _ h.symm
      rw [hsrc] at hr
      exact hrev p.key (PendingInput.hiddenCandidate x.1 p (s p.key)) hr)
    (fun T p h => (hslot ⟨.inl (T, p), h⟩).elim)
    (fun T e l d h => (hslot ⟨.inl (T, _), h⟩).elim)
    (fun _ _ h => h)
  have ht := TopO1.frame prims x top _ a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2)
    ⟨htop.topRows, htop.topRun⟩ hf
  have hpads := backend_padsFixed x q s pads u rest noise _ b.2 hp _ hrb
  have hpaid : ∀ c ∈ unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 (.inr rq), c.2 = s c.1 →
      rb.1.2.revealed c.1 ≠ none := by
    intro c hc he
    obtain ⟨input, hrq, hcand, -⟩ := mem_unreleased x.1 _ _ _ c hc
    cases hrq
    obtain ⟨hsrc, hrev⟩ := hval input rfl
    rw [hsrc]
    refine hrev c.1 ?_
    rw [← he]
    exact hcand
  refine Or.inr (Or.inr ⟨hv, hsync.1.1.flag.trans hfields.flag.symm, ?_⟩)
  exact local_candidates prims x s pads u rest noise top (.inr rq) a b ra.2 (rb.1.2, rb.2) hf.carried
    hf.candidates ⟨hsync, hx', ⟨ht.topRows, ht.topRun⟩, hpads⟩ hpaid

/-- A local query of the forger. -/
theorem step_local (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (t : (LocalSpec C).Domain) : StepO1' prims x q s pads u rest noise top (.inl t) := by
  intro a b hs ha hb
  have hflagA : a.1.2.1.2 = false := by simpa [RealStop] using (not_or.mp ha).1
  have hf := hs.1.1.1.1.1
  have hflagB : b.1.base.hiddenFlag = false := hf.flag.trans hflagA
  have hcorr : b.1.base.signing.corrupt = a.1.2.1.1.corrupt := hf.corrupt
  rw [realLocal_run, compLocal_run]
  cases hh : SigningCoreProof.hiddenHit x a.1.2.1.1.corrupt t with
  | true =>
    apply TreeCheckKernelCoupling.relTriple_of_support
    intro ra hra rb _
    rw [support_map] at hra
    obtain ⟨r, -, rfl⟩ := hra
    exact Or.inl (Or.inl (Bool.or_true _))
  | false =>
    obtain ⟨-, hcand⟩ := control_sync x s pads noise (gOf s pads u) rest a (b.1.base, b.2) hf t
    have hnew : unreleasedCandidates x.1 b.1.base.signing b.1.base.exposed t =
        unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t := by
      have h2 : b.1.base.candidates = a.1.2.2.2 := hf.candidates
      rw [h2] at hcand
      exact List.append_cancel_left hcand
    rw [hcorr, hh, hflagB, hnew, Bool.or_false]
    have hcore : RelTriple ((realWorld prims x s pads u rest (.inl (.inl t))).run a)
        (runX (compBackend x q s pads u rest noise) (sourceLocalX prims x t) b.1.base
          ((b.2.1.1, false), b.2.2))
        (LocalPost prims x q s pads u rest noise top a (b.1, ((b.2.1.1, false), b.2.2))
          (unreleasedCandidates x.1 a.1.2.1.1 a.1.2.2.1 t)) := by
      have hs' : SyncO1 prims x top s pads noise (gOf s pads u) rest a (b.1, ((b.2.1.1, false), b.2.2)) ∧
          PadsFixed x pads ((b.2.1.1, false), b.2.2) :=
        ⟨syncO1_mark prims x s pads u rest noise top a b hs.1 false, hs.2⟩
      rcases t with n | rq
      · exact (local_uniform prims x q s pads u rest noise hkeys top n a
          (b.1, ((b.2.1.1, false), b.2.2)) hs' :)
      · change RelTriple ((readCall prims x s pads u rest true rq).run a)
          (runX (compBackend x q s pads u rest noise) (sourceRoX prims x.1 x.2.1 rq) b.1.base
            ((b.2.1.1, false), b.2.2)) _
        rcases rq with query | input
        · by_cases hsl : IsSlot x query
          · obtain ⟨z, rfl⟩ := hsl
            exact (local_slot prims x q s pads u rest noise hkeys top z a
              (b.1, ((b.2.1.1, false), b.2.2)) hh hs' ha hb rfl :)
          by_cases hbs : ∃ e ρ message, query = .hash (randomizerInput x.1 bottomLayer e ρ message)
          · obtain ⟨e, ρ, message, rfl⟩ := hbs
            exact (local_base prims x q s pads u rest noise hkeys top e ρ message a
              (b.1, ((b.2.1.1, false), b.2.2)) hs' ha hb rfl :)
          · have hno : ∀ i, readInput (.inl query : (RoSpec C).Domain) = .hash i →
                ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message := by
              rintro i hi e ρ message rfl
              exact hbs ⟨e, ρ, message, hi⟩
            exact (local_ordinary prims x q s pads u rest noise hkeys top (.inl query) hsl hno a
              (b.1, ((b.2.1.1, false), b.2.2)) hs' ha hb rfl :)
        · have hsl : ¬IsSlot x (readInput (.inr input : (RoSpec C).Domain)) := by
            rintro ⟨⟨T, p⟩ | z, h⟩ <;> cases h
          have hno : ∀ i, readInput (.inr input : (RoSpec C).Domain) = .hash i →
              ∀ e ρ message, i ≠ randomizerInput x.1 bottomLayer e ρ message := by
            intro i hi
            cases hi
          exact (local_ordinary prims x q s pads u rest noise hkeys top (.inr input) hsl hno a
            (b.1, ((b.2.1.1, false), b.2.2)) hs' ha hb rfl :)
    refine relTriple_map_both _ _ (relTriple_supported hcore) ?_
    rintro ra rb ⟨hp, hra, -⟩
    have hcar := realWorld_carried prims x s pads u rest _ a ra hra
    rcases hp with h | h | ⟨hv, hfl, hsync, hpads⟩
    · refine Or.inl ?_
      rcases h with h | h
      · rw [hcar, hflagA] at h
        cases h
      · exact Or.inr h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨hv, ?_, hpads⟩)
      convert hsync using 2 <;> simp [withCandidates, hcar, hfl, hflagB]

end Local

end ThresholdLeanXmssSecurity.SigningCompilerO1Local

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.realWorld_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.realWorld_uniform

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.realWorld_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.realWorld_carried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.realLocal_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.realLocal_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.compLocal_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.compLocal_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.relTriple_map_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.relTriple_map_both

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.not_mem_candidateList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.not_mem_candidateList

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.mem_unreleased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.mem_unreleased

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_candidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_candidates

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.revealed_of_noHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.revealed_of_noHit

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_uniform

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_slot

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.local_ordinary

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Local.step_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Local.step_local
