import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Programs
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1ChainPending
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealBuild
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1HashProgram
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Queries
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SyncHandlers

/-! # The setup of the O1 coupling, the top tree build of both sides

- `padsFixed_init` states that the initial compiler state has no stored pad.
- `topEnd_sync` couples one chain end of the top tree. The real side reads the PRF value at the
  chain start and walks three steps. The compiler side reads the virtual terms and makes the three
  pending calls of the chain.
- `setup_sync` couples the complete top tree build. The real tree is the tree of the compiler, and
  the boundary relation holds at that tree with the fixed pads.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Setup
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
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local irreducible] Queries

/-! ## The programs of one chain end -/

/-- The truncation of an answer is the reading of its low half. -/
theorem truncateHash_interpret (s : HiddenKey → Digest) (v : DeferredOutput) :
    truncateHash (v.interpret s) = v.low.interpret s :=
  congrArg Prod.snd (XmssSecurity.Rom.hashOutputEquivDigestPair.apply_symm_apply _)

/-- A walk of `n + 1` steps is the walk of `n` steps and one more step. -/
theorem chainWalk_step {m : Type → Type} [Monad m] [HasQuery HashSpec m] (P : PublicParameter)
    (lay : Layer) (key : KeyIndex) (l : ChainIndex) (start n : ℕ) (v : Digest)
    (h : start + n < chainLength - 1) :
    Concrete.chainWalk (m := m) P lay key l start (n + 1) v =
      Concrete.chainWalk P lay key l start n v >>= fun previous =>
        Concrete.tweakableHash P (.chain lay key ⟨start + n, h⟩) (Concrete.chainPayload l previous) := by
  simp only [Concrete.chainWalk, dif_pos h]

/-- One step of `Th` on the domain of `H` is the truncated answer of one query. -/
theorem tweakable_tweakableHash (P : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    tweakable (C := C) (Concrete.tweakableHash P domain payload : OracleComp HashSpec Digest) =
      truncateHash <$> hashQuery (.hash (tweakableHashInput P domain payload)) := by
  simp [Concrete.tweakableHash, tweakable_bind, tweakable_oracleHash, tweakable_pure,
    map_eq_bind_pure_comp]

/-- A walk of three steps from position 0 is three reads of truncated hashes. -/
theorem tweakable_walkThree (P : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex)
    (v : Digest) :
    tweakable (C := C) (Concrete.chainWalk P lay key l 0 3 v : OracleComp HashSpec Digest) = (do
      let v₁ ← truncateHash <$> hashQuery (.hash (tweakableHashInput P (.chain lay key ⟨0, by decide⟩)
        (Concrete.chainPayload l v)))
      let v₂ ← truncateHash <$> hashQuery (.hash (tweakableHashInput P (.chain lay key ⟨1, by decide⟩)
        (Concrete.chainPayload l v₁)))
      truncateHash <$> hashQuery (.hash (tweakableHashInput P (.chain lay key ⟨2, by decide⟩)
        (Concrete.chainPayload l v₂)))) := by
  rw [chainWalk_step _ _ _ _ _ _ _ (by decide : 0 + 2 < chainLength - 1),
    chainWalk_step _ _ _ _ _ _ _ (by decide : 0 + 1 < chainLength - 1),
    chainWalk_step _ _ _ _ _ _ _ (by decide : 0 + 0 < chainLength - 1),
    show (Concrete.chainWalk P lay key l 0 0 v : OracleComp HashSpec Digest) = pure v from rfl]
  simp only [tweakable_bind, tweakable_tweakableHash, pure_bind]
  rfl

/-- The input of a top chain edge is the input of its pending call. -/
theorem topChain_input (P : PublicParameter) (bi : XmssSecurity.TopIndex) (l : ChainIndex)
    (k : XmssSecurity.ChainStep) (w : Digest) :
    tweakableHashInput P (.chain topLayer (topKey bi) k) (Concrete.chainPayload l w) =
      (PendingInput.top bi l k).input P w := rfl

/-- The compiler program of one chain end reads the virtual terms of the chain start and makes the
three pending calls of the chain. -/
theorem sourceTopEnd_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (bi : XmssSecurity.TopIndex) (l : ChainIndex) :
    simulateQ (sourceBackendX P seeds) (deferredTopEnd bi l) = (do
      let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.chain topLayer (topKey bi) l (digit 0))
      let _ ← sourcePendingX P (.top bi l ⟨0, by decide⟩)
      let _ ← sourcePendingX P (.top bi l ⟨1, by decide⟩)
      let last ← sourcePendingX P (.top bi l ⟨2, by decide⟩)
      pure (match last.low with | .known value => value | .secret _ => 0)) := by
  simp only [deferredTopEnd, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, backendQuery,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceBackendX]
  rfl

/-- A virtual call at a chain point keeps the reveal map of the source. -/
theorem keepsRevealed_virtual (P : PublicParameter) (seeds : C.Term → HashOutput) (T : C.Term)
    (lay : Layer) (e : KeyIndex) (l : ChainIndex) (d : Digit) :
    SourceKeepsX (fun src : SourceState C => src.revealed)
      (sourceVirtualX P seeds T (.chain lay e l d)) := by
  unfold sourceVirtualX
  exact (SourceKeepsX.lift _).bind _ fun _ => SourceKeepsX.pure ()

/-- A pending call keeps the reveal map of the source. -/
theorem keepsRevealed_pending (P : PublicParameter) (p : PendingInput) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourcePendingX P p) := by
  have tail (prior : Option DeferredOutput) : SourceKeepsX (fun src : SourceState C => src.revealed)
      (do
        let value ← liftM (deferredQueryX (C := C) (.pending p))
        if prior.isNone then
          modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
        pure value : SourceMX C DeferredOutput) := by
    refine (SourceKeepsX.lift (deferredQueryX (.pending p))).bind _ fun value => ?_
    split
    · exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] })
        (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure value)
    · exact SourceKeepsX.pure value
  unfold sourcePendingX
  refine (SourceKeepsX.lift (deferredQueryX (.inspect p))).bind _ fun prior => ?_
  refine SourceKeepsX.get.bind _ fun source => ?_
  dsimp only
  split
  · refine (SourceKeepsX.lift (deferredQueryX (.hash (.hash _)))).bind _ fun value => ?_
    refine (SourceKeepsX.lift (deferredQueryX (.record p value))).bind _ fun _ => ?_
    exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] })
      (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (SourceKeepsX.modify (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
        (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-- The compiler program of one chain end keeps the reveal map of the source. -/
theorem keepsRevealed_topEnd (P : PublicParameter) (seeds : C.Term → HashOutput)
    (bi : XmssSecurity.TopIndex) (l : ChainIndex) :
    SourceKeepsX (fun src : SourceState C => src.revealed)
      (simulateQ (sourceBackendX P seeds) (deferredTopEnd bi l)) := by
  rw [sourceTopEnd_eq]
  refine (SourceKeepsX.mapM _ _ fun T _ => keepsRevealed_virtual P seeds T _ _ _ _).bind _ fun _ => ?_
  refine (keepsRevealed_pending P _).bind _ fun _ => ?_
  refine (keepsRevealed_pending P _).bind _ fun _ => ?_
  exact (keepsRevealed_pending P _).bind _ fun _ => SourceKeepsX.pure _

/-- An inner top chain edge has the secret of the next position as the low half of its answer. -/
theorem top_low_secret (st : DeferredState C) (h : PendingValid st) (bi : XmssSecurity.TopIndex)
    (l : ChainIndex) (k : XmssSecurity.ChainStep) (hk : k.val + 1 < 3) (vb : DeferredOutput)
    (hp : st.pending (.top bi l k) = some vb) :
    vb.low = .secret (.topChain bi l ⟨k.val + 1, hk⟩) := by
  rcases h _ _ hp with ⟨k', hk', hlow⟩ | ⟨hk', -⟩
  · simp only [PendingInput.next, dif_pos hk, Option.some.injEq] at hk'
    rw [hlow, hk']
  · simp [PendingInput.next, dif_pos hk] at hk'

/-- The last top chain edge has a known low half. -/
theorem top_low_known (st : DeferredState C) (h : PendingValid st) (bi : XmssSecurity.TopIndex)
    (l : ChainIndex) (vb : DeferredOutput)
    (hp : st.pending (.top bi l ⟨2, by decide⟩) = some vb) :
    ∃ d, vb.low = .known d := by
  rcases h _ _ hp with ⟨k', hk', -⟩ | ⟨-, hd⟩
  · simp [PendingInput.next] at hk'
  · exact hd

section Setup
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The fixed pads hold at the initial compiler state. -/
theorem padsFixed_init : PadsFixed x pads (compInit (C := C)).2 := by
  intro p v h
  have hdata : dataOf x (compInit (C := C)).2 = deferredInit := by
    change (withCache ((compilerInit, 0), fun _ => none, false)
      (merge x.2.1 ∅ (fun _ => none))).1.1.data = _
    rw [merge_empty]
    rfl
  rw [hdata] at h
  cases h

/-- The real run of one chain end is the PRF value of the chain start and a walk of three steps. -/
theorem realTopEnd_eq (bi : XmssSecurity.TopIndex) (l : ChainIndex) :
    simulateQ (realWorld prims x s pads u rest) (realTopEnd x.1 x.2.1 bi l) =
      realHonest prims x s pads u rest (prfValue x.2.1 (.chain topLayer (topKey bi) l (digit 0)))
        >>= fun v₀ => realHonest prims x s pads u rest
          (tweakable (Concrete.chainWalk x.1 topLayer (topKey bi) l 0 3 v₀)) := by
  simp only [realTopEnd, simulateQ_bind]

/-- The posts of two parts of a run compose. The second part may use the value of the first part.
The pending answers after the first part stay. -/
theorem callPost_seq {α β α' β' : Type} (cCore : Carried C) (seen1 seen2 : Query C → Prop)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (value1 : α → β → Prop) (value2 : α' → β' → Prop)
    (r1 : α × RealState C) (rb1 : (β × SourceState C) × CompState C)
    (r2 : α' × RealState C) (rb2 : (β' × SourceState C) × CompState C)
    (h1 : CallPost x q s pads u rest noise cCore seen1 a src st value1 r1 rb1)
    (hstopa : RealStop q r1.2 → RealStop q r2.2) (hstopb : Stop rb1.2 → Stop rb2.2)
    (h2 : value1 r1.1 rb1.1.1 →
      SyncCore x s pads noise (gOf s pads u) rest (withCarried r1.2 cCore) (rb1.1.2, rb1.2) →
      ¬RealStop q r1.2 → ¬Stop rb1.2 → rb1.2.1.2 = false →
      CallPost x q s pads u rest noise cCore seen2 r1.2 rb1.1.2 rb1.2 value2 r2 rb2) :
    CallPost x q s pads u rest noise cCore (fun query => seen1 query ∨ seen2 query) a src st
      (fun va vb => value1 r1.1 rb1.1.1 ∧
        (∀ p, (dataOf x rb1.2).pending p ≠ none → (dataOf x rb2.2).pending p ≠ none) ∧
        value2 va vb) r2 rb2 := by
  by_cases ha : RealStop q r1.2
  · exact Or.inl (hstopa ha)
  by_cases hb : Stop rb1.2
  · exact Or.inr (Or.inl (hstopb hb))
  rcases h1 with h | h | ⟨hv1, hs1, hf1, hm1⟩
  · exact (ha h).elim
  · exact (hb h).elim
  rcases h2 hv1 hs1 ha hb hm1 with h | h | ⟨hv2, hs2, hf2, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  exact Or.inr (Or.inr ⟨⟨hv1, hf2.pending, hv2⟩, hs2,
    CallFrame.trans x seen1 seen2 a r1.2 r2.2 _ _ _ hf1 hf2, hm2⟩)

/-- One top chain edge at its secret. The real side reads the truncated hash, and the compiler side
returns the pending answer of the edge. -/
theorem topStep_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (bi : XmssSecurity.TopIndex) (l : ChainIndex) (k : XmssSecurity.ChainStep) (a : RealState C)
    (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest (truncateHash <$> hashQuery
      (.hash (tweakableHashInput x.1 (.chain topLayer (topKey bi) k)
        (Concrete.chainPayload l (s (.topChain bi l k))))))).run a))
    (rb : (DeferredOutput × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourcePendingX x.1 (.top bi l k)) src st)) :
    CallPost x q s pads u rest noise cCore
      (fun query => query = .hash ((PendingInput.top bi l k).input x.1 (s (.topChain bi l k))))
      a src st (fun va vb => va = vb.low.interpret s ∧
        (dataOf x rb.2).pending (.top bi l k) = some vb) ra rb := by
  obtain ⟨r1, h1, rfl⟩ := realHonest_read_support prims x s pads u rest _ a ra
    (by with_reducible exact hra)
  have h := SigningCompilerO1ChainPending.chainPending_sync prims x q s pads u rest noise hkeys cCore
    (l, .inr bi, k) a src st hs ha hb hmark r1 (by
      simp only [chainPending, PendingInput.key, ← topChain_input]
      with_reducible exact h1) rb hrb
  refine callPost_map x q s pads u rest noise cCore _ a src st _ _ r1 rb _ rb h rfl rfl rfl ?_
  rintro ⟨hv, hp⟩
  exact ⟨by rw [hv]; exact truncateHash_interpret s _, hp⟩

/-- One chain end of the setup. Both sides give the same end, and the chain has its pending
answers. -/
theorem topEnd_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (bi : Fin (2 ^ layerHeight)) (l : ChainIndex) (a : RealState C) (src : SourceState C)
    (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
      (realTopEnd x.1 x.2.1 bi l)).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (simulateQ (sourceBackendX x.1 x.2.1) (deferredTopEnd bi l)) src st)) :
    CallPost x q s pads u rest noise cCore
      (fun query => (∃ T, query = .prf (x.2.1 T) (.chain topLayer (topKey bi) l (digit 0))) ∨
        ∃ d : XmssSecurity.ChainStep,
          query = .hash ((PendingInput.top bi l d).input x.1 (s (.topChain bi l d))))
      a src st (fun va vb => va = vb ∧ rb.1.2.revealed = src.revealed ∧
        ∀ d : XmssSecurity.ChainStep, (dataOf x rb.2).pending (.top bi l d) ≠ none) ra rb := by
  have hrev : rb.1.2.revealed = src.revealed :=
    SourceKeepsX.run (keepsRevealed_topEnd x.1 x.2.1 bi l) _ src st rb hrb
  rw [realTopEnd_eq, StateT.run_bind, mem_support_bind_iff] at hra
  obtain ⟨r0, h0, hra⟩ := hra
  rw [tweakable_walkThree, realHonest_bind, StateT.run_bind, mem_support_bind_iff] at hra
  obtain ⟨r1, h1, hra⟩ := hra
  rw [realHonest_bind, StateT.run_bind, mem_support_bind_iff] at hra
  obtain ⟨r2, h2, h3⟩ := hra
  rw [sourceTopEnd_eq] at hrb
  obtain ⟨rb0, hb0, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ src st rb hrb
  obtain ⟨rb1, hb1, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb
  obtain ⟨rb2, hb2, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb
  obtain ⟨rb3, hb3, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb
  rw [runX_pure, mem_support_pure_iff] at hrb
  subst hrb
  have P0 := prfVirtual_sync prims x q s pads u rest noise hkeys cCore
    ⟨.chain topLayer (topKey bi) l (digit 0), constrained_top_chain bi l⟩ a src st hs ha hb hmark r0
    (by with_reducible exact h0) rb0 hb0
  have P1 := callPost_seq x q s pads u rest noise cCore _ _ a src st _ _ r0 rb0 r1 rb1 P0
    (fun h => realHonest_stop prims x q s pads u rest _ r0.2 h r1 (by with_reducible exact h1))
    (fun h => runX_compStop x q s pads u rest noise _ _ _ h rb1 (by with_reducible exact hb1))
    (fun hv hs' ha' hb' hm' => topStep_sync prims x q s pads u rest noise hkeys cCore bi l
      ⟨0, by decide⟩ r0.2 rb0.1.2 rb0.2 hs' ha' hb' hm' r1
      (by rw [← hv.1.trans (NoFalse.tau_top_start s pads bi l)]; with_reducible exact h1) rb1
      (by with_reducible exact hb1))
  have P2 := callPost_seq x q s pads u rest noise cCore _ _ a src st _ _ r1 rb1 r2 rb2 P1
    (fun h => realHonest_stop prims x q s pads u rest _ r1.2 h r2 (by with_reducible exact h2))
    (fun h => runX_compStop x q s pads u rest noise _ _ _ h rb2 (by with_reducible exact hb2))
    (fun hv hs' ha' hb' hm' => topStep_sync prims x q s pads u rest noise hkeys cCore bi l
      ⟨1, by decide⟩ r1.2 rb1.1.2 rb1.2 hs' ha' hb' hm' r2
      (by
        rw [show s (.topChain bi l ⟨1, by decide⟩) = r1.1 by
          rw [hv.2.2.1, top_low_secret _ hs'.1.1.pendingValid bi l ⟨0, by decide⟩ (by decide) _
            hv.2.2.2]
          rfl]
        with_reducible exact h2) rb2 (by with_reducible exact hb2))
  have P3 := callPost_seq x q s pads u rest noise cCore _ _ a src st _ _ r2 rb2 _ rb3 P2
    (fun h => realHonest_stop prims x q s pads u rest _ r2.2 h _ (by with_reducible exact h3))
    (fun h => runX_compStop x q s pads u rest noise _ _ _ h rb3 (by with_reducible exact hb3))
    (fun hv hs' ha' hb' hm' => topStep_sync prims x q s pads u rest noise hkeys cCore bi l
      ⟨2, by decide⟩ r2.2 rb2.1.2 rb2.2 hs' ha' hb' hm' _
      (by
        rw [show s (.topChain bi l ⟨2, by decide⟩) = r2.1 by
          rw [hv.2.2.1, top_low_secret _ hs'.1.1.pendingValid bi l ⟨1, by decide⟩ (by decide) _
            hv.2.2.2]
          rfl]
        with_reducible exact h3) rb3 (by with_reducible exact hb3))
  rcases P3 with h | h | ⟨⟨⟨⟨-, hm01, hv0⟩, hm12, hv1⟩, hm23, hv2⟩, hs3, hf3, hm3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨⟨?_, hrev, ?_⟩, hs3, CallFrame.weaken x _ _ a _ _ _ hf3 ?_, hm3⟩)
  · obtain ⟨w, hw⟩ := top_low_known _ hs3.1.1.pendingValid bi l _ hv2.2
    rw [hv2.1, hw]
    rfl
  · rintro ⟨_ | _ | _ | n, hd⟩
    · exact hm23 _ (hm12 _ (by rw [hv0.2]; exact Option.some_ne_none _))
    · exact hm23 _ (by rw [hv1.2]; exact Option.some_ne_none _)
    · rw [hv2.2]; exact Option.some_ne_none _
    · change n + 3 < 3 at hd
      omega
  · rintro query (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩

/-- The stop of the real side persists over a run in the real world. -/
theorem realWorld_stop {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) : RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r hr) _ a h r hr

/-- The queries of one chain end keep the clauses of `ExtraOpen`. -/
theorem topEnd_extraOpen (top : TopTree) (rev : HiddenKey → Option Digest) (cTime : Carried C)
    (bi : XmssSecurity.TopIndex) (l : ChainIndex) (a a' : RealState C)
    (b b' : SourceStateO1 C × CompState C)
    (hx : ExtraOpen prims x top s rev (fun _ _ => False) (withCarried a cTime) b)
    (hf : CallFrame x (fun query => (∃ T, query = .prf (x.2.1 T) (.chain topLayer (topKey bi) l (digit 0))) ∨
        ∃ d : XmssSecurity.ChainStep,
          query = .hash ((PendingInput.top bi l d).input x.1 (s (.topChain bi l d))))
      a a' (b.1.base, b.2) (b'.1.base, b'.2))
    (hstarts : b'.1.starts = b.1.starts)
    (hrows : ∀ d : XmssSecurity.ChainStep, (dataOf x b'.2).pending (.top bi l d) ≠ none) :
    ExtraOpen prims x top s rev (fun _ _ => False) (withCarried a' cTime) b' := by
  refine ExtraOpen.frame prims x top s _ _ _ rev rev cTime a a' b b' hx hf hstarts (fun _ h => h)
    (fun _ h => Or.inl h) ?_ ?_ ?_ ?_ (fun _ _ h => h)
  · rintro e ρ message (⟨T, h⟩ | ⟨d, h⟩)
    · cases h
    · have h' := Query.hash.inj h
      have hp := pendingInput_injective x.1 (.base bottomLayer e message) (.top bi l d) ρ _ h'
      cases hp
  · rintro p - hp (⟨T, h⟩ | ⟨d, h⟩)
    · cases h
    · have hp' := pendingInput_injective x.1 p (.top bi l d) _ _ (Query.hash.inj h)
      subst hp'
      exact hrows d hp
  · rintro T p (⟨T', h⟩ | ⟨d, h⟩)
    · obtain ⟨-, rfl⟩ := Query.prf.inj h
      exact Or.inr (constrained_top_chain bi l)
    · cases h
  · rintro T e l' d (⟨T', h⟩ | ⟨d', h⟩)
    · obtain ⟨-, h⟩ := Query.prf.inj h
      exact absurd (Point.chain.inj h).1 (by decide)
    · cases h

/-- The chain ends of a list of top chains. Both sides give the same ends. The relation without the
top clauses stays at a fixed top tree, and each chain of the list has its pending answers. -/
theorem topEnds_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (c : Carried C) :
    ∀ (L : List (Fin (2 ^ layerHeight) × ChainIndex)) (a : RealState C)
      (b : SourceStateO1 C × CompState C),
      SyncPre prims x s pads u rest noise top rev (fun _ _ => False) c c a b →
      ¬RealStop q a → ¬Stop b.2 → b.2.1.2 = false →
      ∀ ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
        (L.mapM fun bl => realTopEnd x.1 x.2.1 bl.1 bl.2)).run a),
      ∀ rb ∈ support (runX (compBackend x q s pads u rest noise)
        (L.mapM fun bl => simulateQ (sourceBackendX x.1 x.2.1) (deferredTopEnd bl.1 bl.2))
          b.1.base b.2),
      RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧
          SyncPre prims x s pads u rest noise top rev (fun _ _ => False) c c ra.2
            (⟨rb.1.2, b.1.starts⟩, rb.2) ∧
          CallFrame x (fun _ => True) a ra.2 (b.1.base, b.2) (rb.1.2, rb.2) ∧
          rb.1.2.revealed = b.1.base.revealed ∧
          (∀ bl ∈ L, ∀ d : XmssSecurity.ChainStep, (dataOf x rb.2).pending (.top bl.1 bl.2 d) ≠ none) ∧
          rb.2.1.2 = false) := by
  intro L
  induction L with
  | nil =>
    intro a b hs ha hb hm ra hra rb hrb
    rw [List.mapM_nil, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra
    rw [List.mapM_nil, runX_pure, mem_support_pure_iff] at hrb
    subst hra hrb
    exact Or.inr (Or.inr ⟨rfl, hs, CallFrame.weaken x _ _ a a _ _ (CallFrame.refl x a _)
      (fun _ h => h.elim), rfl, (fun _ h => (List.not_mem_nil h).elim), hm⟩)
  | cons bl L ih =>
    intro a b hs ha hb hm ra hra rb hrb
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hra
    obtain ⟨r1, h1, hra⟩ := hra
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hra
    obtain ⟨r2, h2, hra⟩ := hra
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra
    subst hra
    obtain ⟨rb1, hb1, rb2, hb2, rfl⟩ := runX_cons_support x q s pads u rest noise bl L _ b.1.base b.2
      rb hrb
    have E := topEnd_sync prims x q s pads u rest noise hkeys c bl.1 bl.2 a b.1.base b.2 hs.1 ha hb hm
      r1 h1 rb1 hb1
    rcases E with h | h | ⟨⟨hv, hrev1, hrows1⟩, hcore1, hf1, hm1⟩
    · exact Or.inl (realWorld_stop prims x q s pads u rest _ r1.2 h r2 h2)
    · exact Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ _ _ h rb2 hb2))
    have hpads1 : PadsFixed x pads rb1.2 :=
      backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2 rb1 hb1
    have hs1 : SyncPre prims x s pads u rest noise top rev (fun _ _ => False) c c r1.2
        (⟨rb1.1.2, b.1.starts⟩, rb1.2) :=
      ⟨hcore1, topEnd_extraOpen prims x s top rev c bl.1 bl.2 a r1.2 b (⟨rb1.1.2, b.1.starts⟩, rb1.2)
        hs.2.1 hf1 rfl hrows1, hpads1⟩
    by_cases ha1 : RealStop q r1.2
    · exact Or.inl (realWorld_stop prims x q s pads u rest _ r1.2 ha1 r2 h2)
    by_cases hb1' : Stop rb1.2
    · exact Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ _ _ hb1' rb2 hb2))
    rcases ih r1.2 (⟨rb1.1.2, b.1.starts⟩, rb1.2) hs1 ha1 hb1' hm1 r2 h2 rb2 hb2 with
      h | h | ⟨hv2, hs2, hf2, hrev2, hrows2, hm2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨?_, hs2, CallFrame.weaken x _ _ a _ _ _
      (CallFrame.trans x _ _ a r1.2 r2.2 _ _ _ hf1 hf2) (fun _ _ => trivial),
      hrev2.trans hrev1, ?_, hm2⟩)
    · change r1.1 :: r2.1 = rb1.1.1 :: rb2.1.1
      rw [hv, hv2]
    · intro bl' hbl' d
      rcases List.mem_cons.mp hbl' with rfl | hbl'
      · exact hf2.pending _ (hrows1 d)
      · exact hrows2 bl' hbl' d

/-- The compiler build of the top tree is the chain ends and then the root. -/
theorem sourceTopTreeX_eq (P : PublicParameter) (seeds : C.Term → HashOutput) :
    sourceTopTreeX P seeds = (do
      let indices := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
        (List.finRange numChains).map fun l => (b, l)
      let ends ← indices.mapM fun bl => simulateQ (sourceBackendX P seeds) (deferredTopEnd bl.1 bl.2)
      let keys := indices.map fun bl => (topKey bl.1, bl.2)
      let chainEnd := fun e l => ends.getD (keys.idxOf (e, l)) 0
      let root ← sourceHashProgramX P seeds (merkleNode P topLayer chainEnd layerHeight 0)
      pure (⟨chainEnd, root⟩ : TopTree)) := by
  simp only [sourceTopTreeX, deferredTopTree, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  rfl

/-- The setup at the fixed top tree `emptyTop`. Both sides give the same tree. The relation without
the top clauses holds, the source keeps its reveal map and its stored trees, and each top chain has
its pending answers. -/
theorem setup_core (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest) (realTopBuild x.1 x.2.1)).run
        (realInit x s pads noise))
      (runX (compBackend x q s pads u rest noise) (sourceTopTreeX x.1 x.2.1) compInit.1.base
        compInit.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧
          SyncPre prims x s pads u rest noise emptyTop (compInit (C := C)).1.base.revealed
            (fun _ _ => False) (realInit x s pads noise).1.2 (realInit x s pads noise).1.2 ra.2
            (⟨rb.1.2, (compInit (C := C)).1.starts⟩, rb.2) ∧
          ra.2.1.2 = (realInit x s pads noise).1.2 ∧
          rb.1.2.revealed = (compInit (C := C)).1.base.revealed ∧
          rb.1.2.trees = (compInit (C := C)).1.base.trees ∧
          (∀ bi l d, (dataOf x rb.2).pending (.top bi l d) ≠ none) ∧ rb.2.1.2 = false)) := by
  have h0 : SyncPre prims x s pads u rest noise emptyTop (compInit (C := C)).1.base.revealed
      (fun _ _ => False) (realInit x s pads noise).1.2 (realInit x s pads noise).1.2
      (realInit x s pads noise) compInit := by
    obtain ⟨hcore, hx⟩ := syncBase_init prims x s pads u rest noise hkeys emptyTop
    unfold SyncPre
    rw [withCarried_self]
    exact ⟨hcore, extraOpen_of_extra prims x emptyTop s _ _ _ hx, padsFixed_init x pads⟩
  have ha0 : ¬RealStop q (realInit x s pads noise) := by
    rintro (h | h) <;> [cases h; exact Nat.not_lt_zero _ h]
  have hb0 : ¬Stop (compInit (C := C)).2 := by
    rintro (⟨c, k, l, h⟩ | ⟨h, -⟩) <;> cases h
  rw [sourceTopTreeX_eq]
  simp only [realTopBuild, simulateQ_bind, StateT.run_bind, runX_bind]
  refine relTriple_bind (relTriple_post_mono
    (SigningCompilerSyncLocalRead.relTriple_supported (relTriple_true _ _))
    fun ra rb h => topEnds_sync prims x q s pads u rest noise hkeys emptyTop _ _ _ _ compInit h0 ha0
      hb0 rfl ra h.2.1 rb h.2.2) fun r1a r1b h1 => ?_
  rcases h1 with h1 | h1 | ⟨hv, hs1, hf1, hrev1, hrows1, hm1⟩
  · refine relTriple_of_support_left fun c hc _ => Or.inl ?_
    rw [mem_support_bind_iff] at hc
    obtain ⟨c1, hc1, hc2⟩ := hc
    exact realWorld_stop prims x q s pads u rest _ _
      (realWorld_stop prims x q s pads u rest _ _ h1 c1 (by with_reducible exact hc1)) c
        (by with_reducible exact hc2)
  · refine SigningOpeningProof.relTriple_of_support_right fun c hc _ => Or.inr (Or.inl ?_)
    rw [mem_support_bind_iff] at hc
    obtain ⟨c1, hc1, hc2⟩ := hc
    exact runX_compStop x q s pads u rest noise _ _ _
      (runX_compStop x q s pads u rest noise _ _ _ h1 c1 (by with_reducible exact hc1)) c
        (by with_reducible exact hc2)
  by_cases ha1 : RealStop q r1a.2
  · refine relTriple_of_support_left fun c hc _ => Or.inl ?_
    rw [mem_support_bind_iff] at hc
    obtain ⟨c1, hc1, hc2⟩ := hc
    exact realWorld_stop prims x q s pads u rest _ _
      (realWorld_stop prims x q s pads u rest _ _ ha1 c1 (by with_reducible exact hc1)) c
        (by with_reducible exact hc2)
  by_cases hb1 : Stop r1b.2
  · refine SigningOpeningProof.relTriple_of_support_right fun c hc _ => Or.inr (Or.inl ?_)
    rw [mem_support_bind_iff] at hc
    obtain ⟨c1, hc1, hc2⟩ := hc
    exact runX_compStop x q s pads u rest noise _ _ _
      (runX_compStop x q s pads u rest noise _ _ _ hb1 c1 (by with_reducible exact hc1)) c
        (by with_reducible exact hc2)
  rw [hv]
  refine relTriple_bind (SigningCompilerO1HashProgram.hashProgram_core prims x q s pads u rest noise
    hkeys emptyTop _ _ _ _ (SigningCompilerO1Queries.queries_noBase x.1 _
      (SigningCompilerO1Queries.queries_merkleNode _ _ _ _ _))
    r1a.2 (⟨r1b.1.2, (compInit (C := C)).1.starts⟩, r1b.2) hs1 ha1 hb1 hm1) fun r2a r2b h2 => ?_
  simp only [simulateQ_pure, StateT.run_pure, runX_pure]
  refine relTriple_pure_pure ?_
  rcases h2 with h2 | h2 | ⟨hv2, hsrc2, -, hs2, hm2, hc2, -, hpend2⟩
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ⟨by rw [hv2], hs2, hc2.trans hf1.carried, by rw [hsrc2]; exact hrev1,
    by rw [hsrc2]; exact hf1.trees, fun bi l d => hpend2 _ (hrows1 (bi, l) ?_ d), hm2⟩)
  exact List.mem_flatMap.2 ⟨bi, List.mem_finRange _, List.mem_map.2 ⟨l, List.mem_finRange _, rfl⟩⟩

/-- The post of the setup. The real run gives the top tree of the compiler, and the boundary
relation holds. -/
def SetupPost (ra : Option TreeOutput × RealState C)
    (rb : (TopTree × SourceStateO1 C) × CompState C) : Prop :=
  RealStop q ra.2 ∨ Stop rb.2 ∨
    (ra.1 = some (.top rb.1.1) ∧
      SyncO1 prims x rb.1.1 s pads noise (gOf s pads u) rest ra.2 (rb.1.2, rb.2) ∧
        PadsFixed x pads rb.2 ∧ rb.2.1.2 = false)

/-- The setup, the top tree build of both sides. -/
theorem setup_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
          (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top)).run
        (realInit x s pads noise))
      (runXO1 (compBackend x q s pads u rest noise)
        (do let _ ← liftM (markQ (C := C) (← get).base.hiddenFlag)
            liftBaseX (sourceTopTreeX x.1 x.2.1)) compInit.1 compInit.2)
      (SetupPost prims x q s pads u rest noise) := by
  have hrhs : runXO1 (compBackend x q s pads u rest noise)
      (do let _ ← liftM (markQ (C := C) (← get).base.hiddenFlag)
          liftBaseX (sourceTopTreeX x.1 x.2.1)) compInit.1 compInit.2 =
      (fun r => ((r.1.1, { (compInit (C := C)).1 with base := r.1.2 }), r.2)) <$>
        runX (compBackend x q s pads u rest noise) (sourceTopTreeX x.1 x.2.1) compInit.1.base
          compInit.2 := by
    rw [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_get, pure_bind]
    dsimp only
    rw [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1SyncHandlers.runXO1_mark,
      pure_bind, runXO1_liftBaseX]
    rfl
  have hreal := realTop_eq x
  rw [hrhs, hreal, simulateQ_map, StateT.run_map]
  apply relTriple_map
  refine relTriple_post_mono (SigningCompilerSyncLocalRead.relTriple_supported
    (setup_core prims x q s pads u rest noise hkeys)) ?_
  rintro ra rb ⟨h | h | ⟨hv, hs, hc, hrev, htrees, hrows, hm⟩, hra, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hbase := syncBase_init prims x s pads u rest noise hkeys emptyTop
  have hfull : (some (TreeOutput.top ra.1), ra.2) ∈ support ((realHonest prims x s pads u rest
      (SigningHitProof.hashEmbed (referenceTree SigningHitProof.forestHash
        (SigningHitProof.forestValue x.2.1) x.1 emptyTop .top))).run (realInit x s pads noise)) := by
    rw [SigningHitProof.hashEmbed_referenceTree]
    change _ ∈ support ((simulateQ (realWorld prims x s pads u rest)
      (φ (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top))).run _)
    rw [← referenceTree_φ, hreal, simulateQ_map, StateT.run_map, support_map]
    exact ⟨ra, hra, rfl⟩
  obtain ⟨hres, -⟩ := SigningCompilerO1RealLog.honest_resolves prims x s pads u rest noise _ _
    hbase.2.logAgreement hbase.1.1.1.realPrivate _ hfull
  obtain ⟨m, hcount⟩ := SigningCompilerO1RealLog.resolves_countRun prims _ _ _ hres 0
  rw [SigningHitProof.hashEmbed_referenceTree] at hcount
  have htopRun : TopRun prims x rb.1.1 (realLog ra.2) :=
    ⟨(realLog ra.2, 0), (some (.top ra.1), realLog ra.2, m), hcount, by rw [hv], le_rfl⟩
  obtain ⟨hcore, hx, hpads⟩ := hs
  have hw : withCarried ra.2 (realInit x s pads noise).1.2 = ra.2 := by
    rw [← hc]
    exact withCarried_self _
  rw [hw] at hcore hx
  have hx' := ExtraOpen.retop prims x s _ emptyTop rb.1.1 _ ra.2 _ hx (fun bi => by rw [htrees]; rfl)
  have hextra := extra_of_extraOpen prims x rb.1.1 s _ _ ra.2 _ hx' (fun _ _ h => h.elim)
  rw [← hrev] at hextra
  exact Or.inr (Or.inr ⟨by rw [hv], ⟨⟨hcore, hextra⟩, ⟨hrows, htopRun⟩⟩, hpads, hm⟩)

end Setup

end ThresholdLeanXmssSecurity.SigningCompilerO1Setup

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.truncateHash_interpret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.truncateHash_interpret

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.chainWalk_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.chainWalk_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.tweakable_tweakableHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.tweakable_tweakableHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.tweakable_walkThree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.tweakable_walkThree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topChain_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topChain_input

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.sourceTopEnd_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.sourceTopEnd_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.keepsRevealed_virtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.keepsRevealed_virtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.keepsRevealed_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.keepsRevealed_pending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.keepsRevealed_topEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.keepsRevealed_topEnd

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.top_low_secret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.top_low_secret

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.top_low_known' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.top_low_known

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.padsFixed_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.padsFixed_init

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.realTopEnd_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.realTopEnd_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.callPost_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.callPost_seq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topStep_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topStep_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topEnd_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topEnd_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.realWorld_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.realWorld_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topEnd_extraOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topEnd_extraOpen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topEnds_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.topEnds_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.sourceTopTreeX_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.sourceTopTreeX_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.setup_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.setup_core

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Setup.setup_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Setup.setup_sync
