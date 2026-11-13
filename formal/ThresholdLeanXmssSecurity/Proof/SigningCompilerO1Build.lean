import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1BuildSteps
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1BuildCommit
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Queries

/-! # The bottom tree build of the O1 coupling

`BuildFacts` holds the facts of a complete build that the store and the later releases read.
`bottomTree_sync` couples the bottom tree build of both sides. The real build is the bottom tree of
the dealer, and the compiler build is `sourceBottomTreeX`.

- `inPost_bind` and `inPost_pure` compose the posts of the parts of a build.
- `rows_sync`, `commitments_sync`, `topPrf_sync`, `hashStage_sync`, `base_sync`, `values_sync` and
  `recover_sync` couple the parts of a build in the order of `sourceBottomTreeX`.
- `core_sync` joins the parts on `realBottomBuild`. After a successful search, the digest resolves on
  the same log cache, so it decodes to the codeword of the search (`decode_of_resolves`). The
  compiler branch for a different codeword does not occur.
- `bottomTree_sync` adds the rows of the compiler run and the counted run of the real run.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Build
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame SigningCompilerO1Pre
open SigningCompilerO1Programs SigningCompilerO1BuildSteps SigningCompilerO1RealBuild
open SigningCompilerO1Queries SigningCompilerSyncBackend SigningCompilerSyncLocalRead
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

/-- The facts of a complete build that the store and the later releases read. -/
structure BuildFacts (prims : Primitives) (x : Keys3 C) (s : HiddenKey → Digest) (top : TopTree)
    (bi : Fin (2 ^ layerHeight)) (b : SourceStateO1 C × CompState C)
    (real : Option BottomTree) (symbolic : Option DeferredBottomTree) (a' : RealState C)
    (src' : SourceState C) (st' : CompState C) : Prop where
  /-- The real tree is the symbolic tree read at the secrets, with the real `cpk` default. -/
  value : real = symbolic.map (interpretTree s bi)
  /-- Each row of the tree has its virtual terms and its pending answers. -/
  rows : BottomRows x bi st'
  /-- Each commitment and the top randomizer have their virtual terms. -/
  terms : (∀ k T, (T, Point.randomizer bottomLayer (bottomKey bi k)) ∈ (dataOf x st').virtual) ∧
    ∀ T, (T, Point.randomizer topLayer (topKey bi)) ∈ (dataOf x st').virtual
  /-- A successful build has the virtual terms of each top chain start. -/
  starts : symbolic ≠ none →
    ∀ T l, (T, Point.chain topLayer (topKey bi) l (digit 0)) ∈ (dataOf x st').virtual
  /-- A chain value of the top signature is the secret at its digit, or a known chain end. -/
  shape : ∀ tree, symbolic = some tree → ∀ l,
    (∀ h : (tree.topSignature.encoding l).val < 3, tree.topSignature.chainValue l =
      .secret (.topChain bi l ⟨(tree.topSignature.encoding l).val, h⟩)) ∧
    ((tree.topSignature.encoding l).val = 3 → ∃ w, tree.topSignature.chainValue l = .known w)
  /-- The reveal map grows, and each bound key of the tree has a revealed opening. -/
  revealed : (∀ k, b.1.base.revealed k ≠ none → src'.revealed k ≠ none) ∧
    ∀ k, b.1.base.signing.bound (bottomKey bi k) ≠ none →
      src'.revealed (.opening bottomLayer (bottomKey bi k)) ≠ none
  /-- A successful real build has a counted run below the log cache. -/
  run : ∀ tree, real = some tree →
    ∃ (start : HashCache C × ℕ) (result : Option TreeOutput × HashCache C × ℕ),
      result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
          top (.bottom bi)))).run start) ∧
      result.1 = some (.bottom tree) ∧ result.2.1 ≤ realLog a'
  /-- The log cache holds the top digest input of a successful build, and it decodes to the top
  codeword. -/
  digit : ∀ tree, symbolic = some tree →
    (SigningDescentProof.thView (realLog a') (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 bi
      (tree.root, tree.topSignature.randomness))).isSome ∧
    XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.topEncodingHash
      (SigningDescentProof.thView (realLog a')) x.1 bi (tree.root, tree.topSignature.randomness)) =
        some tree.topSignature.encoding

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind Queries

/-- The facts of a complete build apart from the rows and the counted run. -/
structure CoreFacts (x : Keys3 C) (s : HiddenKey → Digest) (bi : Fin (2 ^ layerHeight))
    (b : SourceStateO1 C × CompState C)
    (real : Option BottomTree) (symbolic : Option DeferredBottomTree) (a' : RealState C)
    (src' : SourceState C) (st' : CompState C) : Prop where
  value : real = symbolic.map (interpretTree s bi)
  terms : (∀ k T, (T, Point.randomizer bottomLayer (bottomKey bi k)) ∈ (dataOf x st').virtual) ∧
    ∀ T, (T, Point.randomizer topLayer (topKey bi)) ∈ (dataOf x st').virtual
  starts : symbolic ≠ none →
    ∀ T l, (T, Point.chain topLayer (topKey bi) l (digit 0)) ∈ (dataOf x st').virtual
  shape : ∀ tree, symbolic = some tree → ∀ l,
    (∀ h : (tree.topSignature.encoding l).val < 3, tree.topSignature.chainValue l =
      .secret (.topChain bi l ⟨(tree.topSignature.encoding l).val, h⟩)) ∧
    ((tree.topSignature.encoding l).val = 3 → ∃ w, tree.topSignature.chainValue l = .known w)
  revealed : (∀ k, b.1.base.revealed k ≠ none → src'.revealed k ≠ none) ∧
    ∀ k, b.1.base.signing.bound (bottomKey bi k) ≠ none →
      src'.revealed (.opening bottomLayer (bottomKey bi k)) ≠ none
  digit : ∀ tree, symbolic = some tree →
    (SigningDescentProof.thView (realLog a') (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 bi
      (tree.root, tree.topSignature.randomness))).isSome ∧
    XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.topEncodingHash
      (SigningDescentProof.thView (realLog a')) x.1 bi (tree.root, tree.topSignature.randomness)) =
        some tree.topSignature.encoding

section Values

/-- The third `cpk` value of a row list does not depend on a default with third value 0. -/
theorem getD_third (rows : List (Digest × Digest × Digest)) (i : ℕ) (c : Digest) :
    (rows.getD i (c, 0, 0)).2.2 = (rows.getD i (0, 0, 0)).2.2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases rows[i]? <;> rfl

/-- The real `cpk` values of a build are the compiler values patched outside the tree. -/
theorem patchCpk_rows (bi : Fin (2 ^ layerHeight)) (rows : List (Digest × Digest × Digest))
    (commitments : List Digest)
    (hrows : rows.length = ((List.finRange (2 ^ layerHeight)).flatMap fun k =>
      (List.finRange numChains).map fun l => (bottomKey bi k, l)).length) :
    patchCpk bi (fun e => commitments.getD (e.val % 2 ^ layerHeight) 0)
      (fun e l => rows.getD (((List.finRange (2 ^ layerHeight)).flatMap fun k =>
        (List.finRange numChains).map fun l => (bottomKey bi k, l)).idxOf (e, l)) (0, 0, 0)) =
    fun e l => rows.getD (((List.finRange (2 ^ layerHeight)).flatMap fun k =>
      (List.finRange numChains).map fun l => (bottomKey bi k, l)).idxOf (e, l))
        (commitments.getD 0 0, 0, 0) := by
  funext e l
  have hmem : (e, l) ∈ ((List.finRange (2 ^ layerHeight)).flatMap fun k =>
      (List.finRange numChains).map fun l => (bottomKey bi k, l)) ↔ treeOf e = bi := by
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨k, l', hk, -⟩
      subst hk
      apply Fin.ext
      simp only [treeOf, bottomKey]
      have := k.isLt
      rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt this, Nat.add_zero]
    · intro h
      exact ⟨⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩, l, by
        rw [← h]; exact bottomKey_treeOf e, rfl⟩
  unfold patchCpk
  split_ifs with h
  · have hlt := List.idxOf_lt_length_of_mem (hmem.2 h)
    rw [← hrows] at hlt
    dsimp only
    rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt]
  · have hnot := fun hm => h (hmem.1 hm)
    rw [List.idxOf_of_notMem hnot, ← hrows, List.getD_eq_default _ _ le_rfl]
    simp [bottomKey]

/-- The top digest of a cache is the cache reading of the top digest computation. -/
theorem eval_topEncodingHash (cache : QueryCache XmssSecurity.HashSpec)
    (P : XmssSecurity.PublicParameter) (key : XmssSecurity.TopIndex) (root : XmssSecurity.Digest)
    (randomness : XmssSecurity.Randomness) :
    evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn cache)
      (XmssSecurity.Concrete.topEncodingHash P key root randomness :
        OracleComp XmssSecurity.HashSpec XmssSecurity.Digest) =
      XmssSecurity.Concrete.CacheView.topEncodingHash cache P key (root, randomness) := by
  simp [XmssSecurity.Concrete.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingHash,
    XmssSecurity.Concrete.CacheView.topEncodingInput, XmssSecurity.Concrete.CacheView.tweakableHash]

/-- A search and a digest that resolve on one cache give the codeword of the search. -/
theorem decode_of_resolves (prims : Primitives) (cache : HashCache C) (P : PublicParameter)
    (lay : Layer) (key : KeyIndex) (message : HashInput) (base randomness : Randomness)
    (encoding : Encoding) (digest : Digest)
    (hsearch : DeterministicSigning.Resolves cache (SigningHitProof.forestHash
      (grind P lay key message base randomizerAttemptLimit 0)) (some (randomness, encoding)))
    (hdigest : DeterministicSigning.Resolves cache (SigningHitProof.forestHash
      (Concrete.messageDigest P lay key message randomness)) digest) :
    Codeword.decode digest = some encoding := by
  have hs' := SigningHitProof.resolves_forestHash cache _ _ hsearch
  have hd' := SigningHitProof.resolves_forestHash cache _ _ hdigest
  have hagree : ∀ input answer, SigningDescentProof.thView cache input = some answer →
      (fun input => (cache (.hash input)).getD 0 : QueryImpl HashSpec Id) input = answer := by
    intro input answer hc
    change (cache (.hash input)).getD 0 = answer
    change cache (.hash input) = some answer at hc
    rw [hc]
    rfl
  have hg : E prims (fun query => (cache query).getD 0)
      (grind P lay key message base randomizerAttemptLimit 0) = some (randomness, encoding) := by
    rw [SigningCacheProof.E_eval]
    exact hs'.eval _ hagree
  have hspec := E_grind_spec P lay key message base randomizerAttemptLimit 0 randomness encoding hg
  rw [SigningCacheProof.E_eval] at hspec
  rw [← hd'.eval _ hagree]
  exact hspec

/-- A top digest that resolves on the log cache gives the top digit fact. -/
theorem topDigit_of_resolves (cache : HashCache C) (P : PublicParameter)
    (bi : Fin (2 ^ layerHeight)) (root : Digest) (randomness : Randomness) (digest : Digest)
    (encoding : Encoding)
    (hdigest : DeterministicSigning.Resolves cache (SigningHitProof.forestHash
      (Concrete.messageDigest P topLayer (topKey bi) (bytesLE 16 root) randomness)) digest)
    (hdecode : Codeword.decode digest = some encoding) :
    (SigningDescentProof.thView cache (XmssSecurity.Concrete.CacheView.topEncodingInput P bi
      (root, randomness))).isSome ∧
    XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.topEncodingHash
      (SigningDescentProof.thView cache) P bi (root, randomness)) = some encoding := by
  have hd' : DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (XmssSecurity.Concrete.topEncodingHash P bi root randomness :
        OracleComp XmssSecurity.HashSpec XmssSecurity.Digest) digest := by
    rw [← XmssSecurity.Bridge.messageDigest_top P bi root randomness]
    exact SigningHitProof.resolves_forestHash cache _ _ hdigest
  have hval := hd'.eval (XmssSecurity.Concrete.CacheReplay.answerFn (SigningDescentProof.thView cache))
    (fun input answer h => by
      simp [XmssSecurity.Concrete.CacheReplay.answerFn, XmssSecurity.Concrete.CacheReplay.answer, h])
  rw [eval_topEncodingHash] at hval
  refine ⟨?_, ?_⟩
  · unfold XmssSecurity.Concrete.topEncodingHash XmssSecurity.Concrete.tweakableHash at hd'
    obtain ⟨answer, hanswer, -⟩ := hd'.query_inv
    exact Option.isSome_iff_exists.2 ⟨answer, hanswer⟩
  · rw [hval, ← XmssSecurity.Bridge.decode_eq]
    exact hdecode

end Values

section Build
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The stop of the real side persists over a run of the real world. -/
theorem realWorld_stop {α : Type} (m : OracleComp (WorldSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) m).run a)) : RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r (by with_reducible exact hr)) m a h r hr

/-- A post inside a handler holds for a weaker value relation. -/
theorem inPost_mono (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C) {α β : Type} (value value' : α → β → Prop)
    (ra : α × RealState C) (rb : (β × SourceState C) × CompState C)
    (h : InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      value ra rb)
    (hv : value ra.1 rb.1.1 → value' ra.1 rb.1.1) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      value' ra rb := by
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hv h1, h2⟩)

/-- The posts of two parts of a build compose. The second part starts from the states after the
first part. -/
theorem inPost_bind (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C) {α β α' β' : Type}
    (ma : OracleComp (WorldSpec C) α) (mb : SourceMX C β)
    (fa : α → OracleComp (WorldSpec C) α') (fb : β → SourceMX C β')
    (V1 : α × RealState C → (β × SourceState C) × CompState C → Prop)
    (V : α' × RealState C → (β' × SourceState C) × CompState C → Prop)
    (h1 : RelTriple ((simulateQ (realWorld prims x s pads u rest) ma).run a)
      (runX (compBackend x q s pads u rest noise) mb b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed) (fun _ _ => V1 ra rb) ra rb))
    (h2 : ∀ r1 rb1, rb1 ∈ support (runX (compBackend x q s pads u rest noise) mb b.1.base b.2) →
      InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
        (fun _ _ => V1 r1 rb1) r1 rb1 →
      ¬RealStop q r1.2 → ¬Stop rb1.2 →
      RelTriple ((simulateQ (realWorld prims x s pads u rest) (fa r1.1)).run r1.2)
        (runX (compBackend x q s pads u rest noise) (fb rb1.1.1) rb1.1.2 rb1.2)
        (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime r1.2
          (⟨rb1.1.2, b.1.starts⟩, rb1.2) (fun rb => rb.1.2.revealed) (fun _ _ => V ra rb) ra rb)) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest) (ma >>= fa)).run a)
      (runX (compBackend x q s pads u rest noise) (mb >>= fb) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed) (fun _ _ => V ra rb) ra rb) := by
  rw [simulateQ_bind, StateT.run_bind, runX_bind]
  refine relTriple_bind (relTriple_supported h1) ?_
  rintro r1 rb1 ⟨hp, -, hrb1⟩
  by_cases ha1 : RealStop q r1.2
  · exact relTriple_of_support_left fun c hc _ =>
      Or.inl (realWorld_stop prims x q s pads u rest _ _ ha1 c hc)
  by_cases hb1 : Stop rb1.2
  · exact SigningOpeningProof.relTriple_of_support_right fun c hc _ =>
      Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ _ _ hb1 c hc))
  refine relTriple_post_mono (h2 r1 rb1 hrb1 hp ha1 hb1) ?_
  rintro ra rb h
  rcases hp with h0 | h0 | ⟨-, -, hsig1, htr1, hex1, hca1, -, hc1, hl1⟩
  · exact (ha1 h0).elim
  · exact (hb1 h0).elim
  rcases h with h | h | ⟨hv, hsy, hsig, htr, hex, hca, hm, hc, hl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hv, hsy, hsig.trans hsig1, htr.trans htr1, hex.trans hex1,
      hca.trans hca1, hm, hc.trans hc1, hl1.trans hl⟩)

/-- Two pure values that satisfy the value relation give the post at the start states. -/
theorem inPost_pure (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C) {α β : Type} (va : α) (vb : β)
    (V : α × RealState C → (β × SourceState C) × CompState C → Prop)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b) (hmark : b.2.1.2 = false)
    (hv : V (va, a) ((vb, b.1.base), b.2)) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest) (pure va : OracleComp (WorldSpec C) α)).run a)
      (runX (compBackend x q s pads u rest noise) (pure vb) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed) (fun _ _ => V ra rb) ra rb) := by
  rw [simulateQ_pure, StateT.run_pure, runX_pure]
  exact relTriple_pure_pure (Or.inr (Or.inr ⟨hv, hs, rfl, rfl, rfl, rfl, hmark, rfl, le_rfl⟩))

/-- A virtual call at the top randomizer keeps the reveal map of the source. -/
theorem keepsRevealed_topVirtual (P : PublicParameter) (seeds : C.Term → HashOutput) (T : C.Term)
    (e : KeyIndex) :
    SourceKeepsX (fun src : SourceState C => src.revealed)
      (sourceVirtualX P seeds T (.randomizer topLayer e)) := by
  unfold sourceVirtualX
  exact (SourceKeepsX.lift _).bind _ fun _ => by
    simp only [show (topLayer = bottomLayer) = False by decide, if_false]
    exact SourceKeepsX.pure ()

/-- The rows of a build. Both sides give the same rows, and no key is revealed. -/
theorem rows_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (htime : cTime.1.1.bound = cCore.1.1.bound) :
    ∀ (L : List (KeyIndex × ChainIndex)) (a : RealState C) (b : SourceStateO1 C × CompState C),
      SyncIn prims x s pads u rest noise top cCore cTime a b →
      ¬RealStop q a → ¬Stop b.2 → b.2.1.2 = false →
      RelTriple ((simulateQ (realWorld prims x s pads u rest)
          (L.mapM fun el => realRow x.1 x.2.1 el.1 el.2)).run a)
        (runX (compBackend x q s pads u rest noise)
          (L.mapM fun el => sourceBottomRowX x.1 x.2.1 el.1 el.2) b.1.base b.2)
        (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
          (fun rb => rb.1.2.revealed)
          (fun _ _ => ra.1 = rb.1.1 ∧ rb.1.2.revealed = b.1.base.revealed ∧ ra.1.length = L.length)
          ra rb) := by
  intro L
  induction L with
  | nil =>
    intro a b hs ha hb hmark
    rw [List.mapM_nil, List.mapM_nil]
    exact inPost_pure prims x q s pads u rest noise top cCore cTime a b [] [] _ hs hmark ⟨rfl, rfl, rfl⟩
  | cons el L ih =>
    intro a b hs ha hb hmark
    rw [List.mapM_cons, List.mapM_cons]
    refine inPost_bind prims x q s pads u rest noise top cCore cTime a b _ _ _ _
      (fun ra rb => ra.1 = rb.1.1 ∧ rb.1.2.revealed = b.1.base.revealed) _ ?_ ?_
    · refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
      rintro ra rb ⟨-, hra, hrb⟩
      exact inPost_mono prims x q s pads u rest noise top cCore cTime a b _ _ ra rb
        (row_sync prims x q s pads u rest noise hkeys top cCore cTime el.1 el.2 a b hs htime ha hb
          hmark ra hra rb hrb) (fun h => ⟨h.1, h.2.1⟩)
    rintro r1 rb1 - hp ha1 hb1
    rcases hp with h | h | ⟨⟨hv1, hrev1⟩, hs1, -, -, -, -, hm1, -, -⟩
    · exact (ha1 h).elim
    · exact (hb1 h).elim
    refine inPost_bind prims x q s pads u rest noise top cCore cTime r1.2 (⟨rb1.1.2, b.1.starts⟩, rb1.2)
      _ _ _ _ (fun ra rb => ra.1 = rb.1.1 ∧ rb.1.2.revealed = rb1.1.2.revealed ∧ ra.1.length = L.length) _
      (ih r1.2 _ hs1 ha1 hb1 hm1) ?_
    rintro r2 rb2 - hp2 ha2 hb2
    rcases hp2 with h | h | ⟨⟨hv2, hrev2, hlen2⟩, hs2, -, -, -, -, hm2, -, -⟩
    · exact (ha2 h).elim
    · exact (hb2 h).elim
    exact inPost_pure prims x q s pads u rest noise top cCore cTime r2.2 (⟨rb2.1.2, b.1.starts⟩, rb2.2)
      _ _ _ hs2 hm2 ⟨by rw [hv1, hv2], hrev2.trans hrev1, by simp [hlen2]⟩

/-- The commitments of a build. Both sides give the same commitments. Each term of each key is
virtual, the reveal map grows, and each bound key has a revealed opening. -/
theorem commitments_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (bi : Fin (2 ^ layerHeight)) :
    ∀ (L : List (Fin (2 ^ layerHeight))) (a : RealState C) (b : SourceStateO1 C × CompState C),
      SyncIn prims x s pads u rest noise top cCore cTime a b →
      ¬RealStop q a → ¬Stop b.2 → b.2.1.2 = false →
      RelTriple ((simulateQ (realWorld prims x s pads u rest)
          (L.mapM fun k => realCommitment x.1 x.2.1 (bottomKey bi k))).run a)
        (runX (compBackend x q s pads u rest noise)
          (L.mapM fun k => sourceCommitmentX x.1 x.2.1 (bottomKey bi k)) b.1.base b.2)
        (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
          (fun rb => rb.1.2.revealed)
          (fun _ _ => ra.1 = rb.1.1 ∧
            (∀ k ∈ L, ∀ T, (T, Point.randomizer bottomLayer (bottomKey bi k)) ∈
              (dataOf x rb.2).virtual) ∧
            (∀ k, b.1.base.revealed k ≠ none → rb.1.2.revealed k ≠ none) ∧
            ∀ k ∈ L, b.1.base.signing.bound (bottomKey bi k) ≠ none →
              rb.1.2.revealed (.opening bottomLayer (bottomKey bi k)) ≠ none) ra rb) := by
  intro L
  induction L with
  | nil =>
    intro a b hs ha hb hmark
    rw [List.mapM_nil, List.mapM_nil]
    exact inPost_pure prims x q s pads u rest noise top cCore cTime a b [] [] _ hs hmark
      ⟨rfl, fun k hk => (by cases hk), fun k hk => hk, fun k hk => (by cases hk)⟩
  | cons k0 L ih =>
    intro a b hs ha hb hmark
    rw [List.mapM_cons, List.mapM_cons]
    refine inPost_bind prims x q s pads u rest noise top cCore cTime a b _ _ _ _
      (fun ra rb => ra.1 = rb.1.1 ∧
        (∀ T, (T, Point.randomizer bottomLayer (bottomKey bi k0)) ∈ (dataOf x rb.2).virtual) ∧
        (∀ k, b.1.base.revealed k ≠ none → rb.1.2.revealed k ≠ none) ∧
        (b.1.base.signing.bound (bottomKey bi k0) ≠ none →
          rb.1.2.revealed (.opening bottomLayer (bottomKey bi k0)) ≠ none)) _
      (SigningCompilerO1BuildCommit.commitment_sync prims x q s pads u rest noise hkeys top cCore
        cTime (bottomKey bi k0) a b hs htime ha hb hmark) ?_
    rintro r1 rb1 - hp ha1 hb1
    rcases hp with h | h | ⟨⟨hv1, hvirt1, hrev1, hbound1⟩, hs1, hsig1, -, -, -, hm1, -, -⟩
    · exact (ha1 h).elim
    · exact (hb1 h).elim
    refine inPost_bind prims x q s pads u rest noise top cCore cTime r1.2 (⟨rb1.1.2, b.1.starts⟩, rb1.2)
      _ _ _ _ _ _ (ih r1.2 _ hs1 ha1 hb1 hm1) ?_
    rintro r2 rb2 hrb2 hp2 ha2 hb2
    rcases hp2 with h | h | ⟨⟨hv2, hvirt2, hrev2, hbound2⟩, hs2, -, -, -, -, hm2, -, -⟩
    · exact (ha2 h).elim
    · exact (hb2 h).elim
    have hsub := (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ rb2 hrb2).1
    refine inPost_pure prims x q s pads u rest noise top cCore cTime r2.2 (⟨rb2.1.2, b.1.starts⟩, rb2.2)
      _ _ _ hs2 hm2 ⟨by rw [hv1, hv2], fun k hk T => ?_, fun k hk => hrev2 k (hrev1 k hk),
        fun k hk hbd => ?_⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hsub (hvirt1 T)
      · exact hvirt2 k hk T
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hrev2 _ (hbound1 hbd)
      · exact hbound2 k hk (by rw [hsig1]; exact hbd)

/-- The PRF value at the top randomizer of a build. The real value is the top opening, each term
is virtual, and no key is revealed. -/
theorem topPrf_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest)
        (liftFree (prfValue x.2.1 (.randomizer topLayer (topKey bi))))).run a)
      (runX (compBackend x q s pads u rest noise)
        (C.terms.mapM fun T => sourceVirtualX x.1 x.2.1 T (.randomizer topLayer (topKey bi)))
        b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed)
        (fun _ _ => ra.1 = s (.opening topLayer (topKey bi)) ∧
          (∀ T, (T, Point.randomizer topLayer (topKey bi)) ∈ (dataOf x rb.2).virtual) ∧
          rb.1.2.revealed = b.1.base.revealed) ra rb) := by
  refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
  rintro ra rb ⟨-, hra, hrb⟩
  let pt : CPoint := ⟨.randomizer topLayer (topKey bi), constrained_top_randomizer bi⟩
  have hP := prfVirtual_sync prims x q s pads u rest noise hkeys cCore pt a b.1.base b.2 hs.1 ha hb
    hmark ra (by with_reducible exact hra) rb hrb
  have hrev := SourceKeepsX.run (SourceKeepsX.mapM C.terms _ fun T _ =>
    keepsRevealed_topVirtual x.1 x.2.1 T (topKey bi)) (compBackend x q s pads u rest noise)
    b.1.base b.2 rb hrb
  have hpads := backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb hrb
  refine inPost_mono prims x q s pads u rest noise top cCore cTime a b _ _ ra rb
    (inPost_of_callPost prims x q s pads u rest noise top cCore cTime a b hs _ _ ra rb hP hpads hrev
      (fun e ρ message ⟨T, hT⟩ => by cases hT) (fun p _ ⟨T, hT⟩ => by cases hT)
      (fun T p ⟨T', hT⟩ => by injection hT with _ hp; subst hp; exact pt.2)
      (fun T e l d ⟨T', hT⟩ => by injection hT with _ hp; cases hp)) ?_
  rintro ⟨hv, hvirt, -⟩
  exact ⟨hv, hvirt, hrev⟩

/-- A hash program of a build. Both sides give the same value, the source state stays, and the log
cache resolves the program. -/
theorem hashStage_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) {α : Type} (oa' oa : OracleComp HashSpec α) (heq : oa' = oa)
    (hbase : Queries (fun input => ∀ e ρ message,
      input ≠ randomizerInput x.1 bottomLayer e ρ message) oa)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest) (liftFree (tweakable oa'))).run a)
      (runX (compBackend x q s pads u rest noise) (sourceHashProgramX x.1 x.2.1 oa) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed)
        (fun _ _ => ra.1 = rb.1.1 ∧ rb.1.2 = b.1.base ∧
          DeterministicSigning.Resolves (realLog ra.2) (SigningHitProof.forestHash oa) ra.1) ra rb) := by
  subst oa
  refine relTriple_post_mono (SigningCompilerO1HashProgram.hashProgram_sync prims x q s pads u rest
    noise hkeys top b.1.base.revealed cCore cTime oa' hbase a b hs ha hb hmark) ?_
  rintro ra rb (h | h | ⟨hv, hsy, hrest⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨hv, ?_, hrest⟩)
    dsimp only at hsy ⊢
    rw [show rb.1.2.revealed = b.1.base.revealed from congrArg _ hv.2.1]
    exact hsy

/-- The base call of the top signature of a build. The real value is the low half of the compiler
answer, and the reveal map grows. -/
theorem base_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (message : HashInput) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest) (liftFree (tweakable
        (truncateHash <$> Concrete.oracleHash (randomizerInput x.1 topLayer (topKey bi)
          (s (.opening topLayer (topKey bi))) message))))).run a)
      (runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 (.base topLayer (topKey bi) message))
        b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed)
        (fun _ _ => (ra.1 = match rb.1.1.low with | .known value => value | .secret _ => 0) ∧
          ∀ k, b.1.base.revealed k ≠ none → rb.1.2.revealed k ≠ none) ra rb) := by
  let p : PendingInput := .base topLayer (topKey bi) message
  have hreal : (simulateQ (realWorld prims x s pads u rest) (liftFree (tweakable
      (truncateHash <$> Concrete.oracleHash (randomizerInput x.1 topLayer (topKey bi)
        (s (.opening topLayer (topKey bi))) message))))).run a =
      (fun r => (truncateHash r.1, r.2)) <$>
        (realWorld prims x s pads u rest (.inr (.inr (.inl (.hash (p.input x.1 (s p.key))))))).run a := by
    have h := SigningCompilerO1HashProgram.realHonest_tweakable prims x s pads u rest
      (truncateHash <$> Concrete.oracleHash (randomizerInput x.1 topLayer (topKey bi)
        (s (.opening topLayer (topKey bi))) message))
    change (realHonest prims x s pads u rest _).run a = _
    rw [h]
    simp [Concrete.oracleHash, SigningCompilerO1Pending.readCall_false]
    rfl
  rw [hreal]
  have hfree : b.1.base.revealed p.key = none → (dataOf x b.2).pending p = none →
      visibleOf a (.hash (p.input x.1 (s p.key))) = none :=
    fun hk hp => hs.2.1.rest.guessFree p hk hp
  have hO := SigningCompilerO1Pending.openingPending_sync prims x q s pads u rest noise hkeys cCore p
    (Or.inr ⟨_, _, rfl⟩) a b.1.base b.2 hs.1 hfree ha hb hmark
  rw [← id_map (runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) b.1.base b.2)]
  refine relTriple_map (relTriple_post_mono (relTriple_supported hO) ?_)
  rintro ra rb ⟨hC, -, hrb⟩
  have hpads := backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb hrb
  have hrev := SourceKeepsX.run (keepsRevealed_pending x.1 p) (compBackend x q s pads u rest noise)
    b.1.base b.2 rb hrb
  rcases hC with h | h | ⟨⟨hval, ⟨d, hd⟩, hp⟩, hrest⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hI := inPost_of_callPost prims x q s pads u rest noise top cCore cTime a b hs _
    (fun va vb => va = vb.interpret s ∧ (∃ d, vb.low = .known d) ∧
      (dataOf x rb.2).pending p = some vb) ra rb (Or.inr (Or.inr ⟨⟨hval, ⟨d, hd⟩, hp⟩, hrest⟩))
    hpads hrev
    (fun e ρ m hseen => by
      injection hseen with hseen
      exact absurd (SigningGuessProof.randomizerInput_layer_eq x.1 hseen) (by decide))
    (fun p' hp' hseen => by
      injection hseen with hseen
      have he := pendingInput_injective x.1 p' p _ _ hseen
      subst he
      rw [hp] at hp'
      cases hp')
    (fun T p' hseen => by cases hseen)
    (fun T e l d' hseen => by cases hseen)
  rcases hI with h | h | ⟨-, hrest'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨⟨?_, fun k hk => by change rb.1.2.revealed k ≠ none; rw [hrev]; exact hk⟩,
    hrest'⟩)
  change truncateHash ra.1 = match rb.1.1.low with | .known value => value | .secret _ => 0
  rw [hval, truncateHash_interpret, hd]
  rfl

/-- The chain values of the top signature of a build. Each real value is the reading of the
symbolic value, and no key is revealed. -/
theorem values_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (bi : Fin (2 ^ layerHeight)) :
    ∀ (n : ℕ) (σ : Fin n → ChainIndex) (p : Fin n → Digit) (a : RealState C)
      (b : SourceStateO1 C × CompState C),
      SyncIn prims x s pads u rest noise top cCore cTime a b →
      ¬RealStop q a → ¬Stop b.2 → b.2.1.2 = false →
      RelTriple ((simulateQ (realWorld prims x s pads u rest)
          (Concrete.sequenceFin fun i => realTopValue x.1 x.2.1 bi (σ i) (p i))).run a)
        (runX (compBackend x q s pads u rest noise)
          (Concrete.sequenceFin fun i => sourceTopValueX x.1 x.2.1 bi (σ i) (p i)) b.1.base b.2)
        (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
          (fun rb => rb.1.2.revealed)
          (fun _ _ => rb.1.2.revealed = b.1.base.revealed ∧ ∀ i,
            ra.1 i = (rb.1.1 i).interpret s ∧
            (∀ h : (p i).val < 3, rb.1.1 i = .secret (.topChain bi (σ i) ⟨(p i).val, h⟩)) ∧
            ((p i).val = 3 → ∃ w, rb.1.1 i = .known w) ∧
            ∀ T, (T, Point.chain topLayer (topKey bi) (σ i) (digit 0)) ∈ (dataOf x rb.2).virtual)
          ra rb) := by
  intro n
  induction n with
  | zero =>
    intro σ p a b hs ha hb hmark
    rw [Concrete.sequenceFin.eq_1, Concrete.sequenceFin.eq_1]
    exact inPost_pure prims x q s pads u rest noise top cCore cTime a b _ _ _ hs hmark
      ⟨rfl, fun i => i.elim0⟩
  | succ n ih =>
    intro σ p a b hs ha hb hmark
    rw [Concrete.sequenceFin.eq_2, Concrete.sequenceFin.eq_2]
    refine inPost_bind prims x q s pads u rest noise top cCore cTime a b _ _ _ _
      (fun ra rb => ra.1 = rb.1.1.interpret s ∧ rb.1.2.revealed = b.1.base.revealed ∧
        (∀ h : (p 0).val < 3, rb.1.1 = .secret (.topChain bi (σ 0) ⟨(p 0).val, h⟩)) ∧
        ((p 0).val = 3 → ∃ w, rb.1.1 = .known w) ∧
        ∀ T, (T, Point.chain topLayer (topKey bi) (σ 0) (digit 0)) ∈ (dataOf x rb.2).virtual) _
      ?_ ?_
    · refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
      rintro ra rb ⟨-, hra, hrb⟩
      exact inPost_mono prims x q s pads u rest noise top cCore cTime a b _ _ ra rb
        (topValue_sync prims x q s pads u rest noise hkeys top cCore cTime bi (σ 0) (p 0) a b hs htime
          ha hb hmark ra hra rb hrb) id
    rintro r1 rb1 - hp ha1 hb1
    rcases hp with h | h | ⟨⟨hv1, hrev1, hlow1, hend1, hvirt1⟩, hs1, -, -, -, -, hm1, -, -⟩
    · exact (ha1 h).elim
    · exact (hb1 h).elim
    refine inPost_bind prims x q s pads u rest noise top cCore cTime r1.2 (⟨rb1.1.2, b.1.starts⟩, rb1.2)
      _ _ _ _ _ _ (ih (fun i => σ i.succ) (fun i => p i.succ) r1.2 _ hs1 ha1 hb1 hm1) ?_
    rintro r2 rb2 hrb2 hp2 ha2 hb2
    rcases hp2 with h | h | ⟨⟨hrev2, htail⟩, hs2, -, -, -, -, hm2, -, -⟩
    · exact (ha2 h).elim
    · exact (hb2 h).elim
    have hsub := (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ rb2 hrb2).1
    refine inPost_pure prims x q s pads u rest noise top cCore cTime r2.2 (⟨rb2.1.2, b.1.starts⟩, rb2.2)
      _ _ _ hs2 hm2 ⟨hrev2.trans hrev1, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hv1, hlow1, hend1, fun T => hsub (hvirt1 T)⟩
    · exact htail j

/-- The verification walks of the top signature of a build. Both sides give the same chain ends,
and no key is revealed. -/
theorem recover_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (htime : cTime.1.1.bound = cCore.1.1.bound)
    (bi : Fin (2 ^ layerHeight)) :
    ∀ (n : ℕ) (σ : Fin n → ChainIndex) (p : Fin n → Digit) (v : Fin n → Digest)
      (dv : Fin n → DeferredDigest), (∀ i, v i = (dv i).interpret s) →
      (∀ i, ∀ h : (p i).val < 3, dv i = .secret (.topChain bi (σ i) ⟨(p i).val, h⟩)) →
      (∀ i, (p i).val = 3 → ∃ w, dv i = .known w) →
      ∀ (a : RealState C) (b : SourceStateO1 C × CompState C),
      SyncIn prims x s pads u rest noise top cCore cTime a b →
      ¬RealStop q a → ¬Stop b.2 → b.2.1.2 = false →
      RelTriple ((simulateQ (realWorld prims x s pads u rest)
          (Concrete.sequenceFin fun i => liftFree (tweakable
            (Concrete.recoverChain x.1 topLayer (topKey bi) (σ i) (p i) (v i))))).run a)
        (runX (compBackend x q s pads u rest noise)
          (Concrete.sequenceFin fun i => sourceTopRecoverX x.1 bi (σ i) (p i) (dv i)) b.1.base b.2)
        (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
          (fun rb => rb.1.2.revealed)
          (fun _ _ => ra.1 = rb.1.1 ∧ rb.1.2.revealed = b.1.base.revealed) ra rb) := by
  intro n
  induction n with
  | zero =>
    intro σ p v dv hv hlow hend a b hs ha hb hmark
    rw [Concrete.sequenceFin.eq_1, Concrete.sequenceFin.eq_1]
    exact inPost_pure prims x q s pads u rest noise top cCore cTime a b _ _ _ hs hmark
      ⟨funext fun i => i.elim0, rfl⟩
  | succ n ih =>
    intro σ p v dv hv hlow hend a b hs ha hb hmark
    rw [Concrete.sequenceFin.eq_2, Concrete.sequenceFin.eq_2]
    refine inPost_bind prims x q s pads u rest noise top cCore cTime a b _ _ _ _
      (fun ra rb => ra.1 = rb.1.1 ∧ rb.1.2.revealed = b.1.base.revealed) _ ?_ ?_
    · refine relTriple_post_mono (relTriple_supported (relTriple_true _ _)) ?_
      rintro ra rb ⟨-, hra, hrb⟩
      exact topRecover_sync prims x q s pads u rest noise hkeys top cCore cTime bi (σ 0) (p 0) (v 0)
        (dv 0) (hv 0) (hlow 0) (hend 0) a b hs htime ha hb hmark ra (by with_reducible exact hra) rb hrb
    rintro r1 rb1 - hp ha1 hb1
    rcases hp with h | h | ⟨⟨hv1, hrev1⟩, hs1, -, -, -, -, hm1, -, -⟩
    · exact (ha1 h).elim
    · exact (hb1 h).elim
    refine inPost_bind prims x q s pads u rest noise top cCore cTime r1.2 (⟨rb1.1.2, b.1.starts⟩, rb1.2)
      _ _ _ _ _ _ (ih (fun i => σ i.succ) (fun i => p i.succ) (fun i => v i.succ) (fun i => dv i.succ)
        (fun i => hv i.succ) (fun i => hlow i.succ) (fun i => hend i.succ) r1.2 _ hs1 ha1 hb1 hm1) ?_
    rintro r2 rb2 - hp2 ha2 hb2
    rcases hp2 with h | h | ⟨⟨hv2, hrev2⟩, hs2, -, -, -, -, hm2, -, -⟩
    · exact (ha2 h).elim
    · exact (hb2 h).elim
    refine inPost_pure prims x q s pads u rest noise top cCore cTime r2.2 (⟨rb2.1.2, b.1.starts⟩, rb2.2)
      _ _ _ hs2 hm2 ⟨?_, hrev2.trans hrev1⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hv1
    · exact congrFun hv2 j

/-- The bottom tree build of both sides in the order of the compiler build, with the facts apart
from the rows and the counted run. -/
theorem core_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest) (realBottomBuild x.1 x.2.1 top bi)).run a)
      (runX (compBackend x q s pads u rest noise) (sourceBottomTreeX x.1 x.2.1 top bi) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed)
        (fun _ _ => CoreFacts x s bi b ra.1 rb.1.1 ra.2 rb.1.2 rb.2) ra rb) := by
  unfold realBottomBuild sourceBottomTreeX
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a b _ _ _ _
    (fun ra rb => ra.1 = rb.1.1 ∧ rb.1.2.revealed = b.1.base.revealed ∧
      ra.1.length = ((List.finRange (2 ^ layerHeight)).flatMap fun k =>
        (List.finRange numChains).map fun l => (bottomKey bi k, l)).length) _
    (rows_sync prims x q s pads u rest noise hkeys top cCore cTime htime _ a b hs ha hb hmark) ?_
  rintro r1 rb1 hrb1 hp1 ha1 hb1
  rcases hp1 with h | h | ⟨⟨hv1, hrev1, hlen1⟩, hs1, hsig1, -, -, -, hm1, -, hl1⟩
  · exact (ha1 h).elim
  · exact (hb1 h).elim
  refine inPost_bind prims x q s pads u rest noise top cCore cTime r1.2 (⟨rb1.1.2, b.1.starts⟩, rb1.2)
    _ _ _ _ _ _ (commitments_sync prims x q s pads u rest noise hkeys top cCore cTime htime bi
      (List.finRange _) r1.2 _ hs1 ha1 hb1 hm1) ?_
  rintro r2 rb2 hrb2 hp2 ha2 hb2
  rcases hp2 with h | h | ⟨⟨hv2, hvirt2, hrev2, hbound2⟩, hs2, hsig2, -, -, -, hm2, -, hl2⟩
  · exact (ha2 h).elim
  · exact (hb2 h).elim
  refine inPost_bind prims x q s pads u rest noise top cCore cTime r2.2 (⟨rb2.1.2, b.1.starts⟩, rb2.2)
    _ _ _ _ _ _ (topPrf_sync prims x q s pads u rest noise hkeys top cCore cTime bi r2.2 _ hs2 ha2 hb2
      hm2) ?_
  rintro ⟨ρ, a3⟩ rb3 hrb3 hp3 ha3 hb3
  rcases hp3 with h | h | ⟨⟨hv3, hvirt3, hrev3⟩, hs3, hsig3, -, -, -, hm3, -, hl3⟩
  · exact (ha3 h).elim
  · exact (hb3 h).elim
  dsimp only at hv3
  subst hv3
  have hsub3 := (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ rb3 hrb3).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a3 (⟨rb3.1.2, b.1.starts⟩, rb3.2)
    _ _ _ _ _ _ (hashStage_sync prims x q s pads u rest noise hkeys top cCore cTime _ _
      (by
        congr 1
        funext e l
        rw [hv1, hv2]
        exact getD_third _ _ _)
      (queries_noBase x.1 _ (queries_merkleNode _ _ _ _ _)) a3 _ hs3 ha3 hb3 hm3) ?_
  rintro ⟨root, a4⟩ rb4 hrb4 hp4 ha4 hb4
  rcases hp4 with h | h | ⟨⟨hv4, hsrc4, hres4⟩, hs4, -, -, -, -, hm4, -, hl4⟩
  · exact (ha4 h).elim
  · exact (hb4 h).elim
  dsimp only at hv4 hsrc4 hres4
  subst hv4
  have hsub4 : (dataOf x rb3.2).virtual ⊆ (dataOf x rb4.2).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ rb4
      (by with_reducible exact hrb4)).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a4 (⟨rb4.1.2, b.1.starts⟩, rb4.2)
    _ _ _ _ _ _ (base_sync prims x q s pads u rest noise hkeys top cCore cTime bi _ a4 _ hs4 ha4 hb4
      hm4) ?_
  rintro ⟨base, a5⟩ rb5 hrb5 hp5 ha5 hb5
  rcases hp5 with h | h | ⟨⟨hv5, hrev5⟩, hs5, -, -, -, -, hm5, -, hl5⟩
  · exact (ha5 h).elim
  · exact (hb5 h).elim
  dsimp only at hv5
  subst hv5
  have hsub5 : (dataOf x rb4.2).virtual ⊆ (dataOf x rb5.2).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ rb5
      (by with_reducible exact hrb5)).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a5 (⟨rb5.1.2, b.1.starts⟩, rb5.2)
    _ _ _ _ _ _ (hashStage_sync prims x q s pads u rest noise hkeys top cCore cTime _ _ rfl
      (queries_noBase x.1 _ (queries_grind _ _ _ _ _ _ _)) a5 _ hs5 ha5 hb5 hm5) ?_
  rintro ⟨res, a6⟩ ⟨⟨res', src6⟩, st6⟩ hrb6 hp6 ha6 hb6
  rcases hp6 with h | h | ⟨⟨hv6, hsrc6, hres6⟩, hs6, -, -, -, -, hm6, -, hl6⟩
  · exact (ha6 h).elim
  · exact (hb6 h).elim
  dsimp only at hv6 hsrc6 hres6 hs6 hm6 ha6 hb6
  subst hv6
  have hsub6 : (dataOf x rb5.2).virtual ⊆ (dataOf x st6).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((res, src6), st6)
      (by with_reducible exact hrb6)).1
  have hterms : ∀ st : CompState C, (dataOf x st6).virtual ⊆ (dataOf x st).virtual →
      (∀ k T, (T, Point.randomizer bottomLayer (bottomKey bi k)) ∈ (dataOf x st).virtual) ∧
        ∀ T, (T, Point.randomizer topLayer (topKey bi)) ∈ (dataOf x st).virtual :=
    fun st hst => ⟨fun k T => hst (hsub6 (hsub5 (hsub4 (hsub3 (hvirt2 k (List.mem_finRange k) T))))),
      fun T => hst (hsub6 (hsub5 (hsub4 (hvirt3 T))))⟩
  have hrevealed : ∀ src : SourceState C, (∀ k, src6.revealed k ≠ none → src.revealed k ≠ none) →
      (∀ k, b.1.base.revealed k ≠ none → src.revealed k ≠ none) ∧
        ∀ k, b.1.base.signing.bound (bottomKey bi k) ≠ none →
          src.revealed (.opening bottomLayer (bottomKey bi k)) ≠ none := by
    intro src hsrc
    have hchain : ∀ k, rb2.1.2.revealed k ≠ none → src.revealed k ≠ none := by
      intro k hk
      apply hsrc
      rw [hsrc6]
      apply hrev5
      rw [hsrc4, hrev3]
      exact hk
    refine ⟨fun k hk => hchain k (hrev2 k (by rw [hrev1]; exact hk)), fun k hbd => ?_⟩
    exact hchain _ (hbound2 k (List.mem_finRange k) (by rw [hsig1]; exact hbd))
  rcases res with _ | ⟨randomness, encoding⟩
  · exact inPost_pure prims x q s pads u rest noise top cCore cTime a6 (⟨src6, b.1.starts⟩, st6)
      none none _ hs6 hm6 ⟨rfl, hterms st6 fun _ h => h, fun h => (h rfl).elim, fun _ h => (by cases h),
        hrevealed src6 fun _ h => h, fun _ h => (by cases h)⟩
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a6 (⟨src6, b.1.starts⟩, st6)
    _ _ _ _ _ _ (values_sync prims x q s pads u rest noise hkeys top cCore cTime htime bi _
      (fun l => l) encoding a6 _ hs6 ha6 hb6 hm6) ?_
  rintro ⟨values, a7⟩ ⟨⟨dvalues, src7⟩, st7⟩ hrb7 hp7 ha7 hb7
  rcases hp7 with h | h | ⟨⟨hrev7, hval7⟩, hs7, -, -, -, -, hm7, -, hl7⟩
  · exact (ha7 h).elim
  · exact (hb7 h).elim
  dsimp only at hrev7 hval7 hs7 hm7 ha7 hb7 hl7
  have hsub7 : (dataOf x st6).virtual ⊆ (dataOf x st7).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((dvalues, src7), st7)
      (by with_reducible exact hrb7)).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a7 (⟨src7, b.1.starts⟩, st7)
    _ _ _ _ _ _ (hashStage_sync prims x q s pads u rest noise hkeys top cCore cTime _ _ rfl
      (queries_noBase x.1 _ (queries_merklePath _ _ _ _)) a7 _ hs7 ha7 hb7 hm7) ?_
  rintro ⟨path, a8⟩ ⟨⟨path', src8⟩, st8⟩ hrb8 hp8 ha8 hb8
  rcases hp8 with h | h | ⟨⟨hv8, hsrc8, -⟩, hs8, -, -, -, -, hm8, -, hl8⟩
  · exact (ha8 h).elim
  · exact (hb8 h).elim
  dsimp only at hv8 hsrc8 hs8 hm8 ha8 hb8 hl8
  subst hv8
  have hsub8 : (dataOf x st7).virtual ⊆ (dataOf x st8).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((path, src8), st8)
      (by with_reducible exact hrb8)).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a8 (⟨src8, b.1.starts⟩, st8)
    _ _ _ _ _ _ (hashStage_sync prims x q s pads u rest noise hkeys top cCore cTime _ _ rfl
      (queries_noBase x.1 _ (queries_messageDigest _ _ _ _ _)) a8 _ hs8 ha8 hb8 hm8) ?_
  rintro ⟨digest, a9⟩ ⟨⟨digest', src9⟩, st9⟩ hrb9 hp9 ha9 hb9
  rcases hp9 with h | h | ⟨⟨hv9, hsrc9, hres9⟩, hs9, -, -, -, -, hm9, -, hl9⟩
  · exact (ha9 h).elim
  · exact (hb9 h).elim
  dsimp only at hv9 hsrc9 hres9 hs9 hm9 ha9 hb9 hl9
  subst hv9
  have hsub9 : (dataOf x st8).virtual ⊆ (dataOf x st9).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((digest, src9), st9)
      (by with_reducible exact hrb9)).1
  have hdec : Codeword.decode digest = some encoding :=
    decode_of_resolves prims (realLog a9) x.1 topLayer (topKey bi) _ _ randomness encoding digest
      (hres6.mono (hl7.trans (hl8.trans hl9))) hres9
  simp only [hdec, ne_eq, not_true_eq_false, if_false]
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a9 (⟨src9, b.1.starts⟩, st9)
    _ _ _ _ _ _ (recover_sync prims x q s pads u rest noise hkeys top cCore cTime htime bi _
      (fun l => l) encoding values dvalues (fun l => (hval7 l).1) (fun l => (hval7 l).2.1)
      (fun l => (hval7 l).2.2.1) a9 _ hs9 ha9 hb9 hm9) ?_
  rintro ⟨ends, a10⟩ ⟨⟨ends', src10⟩, st10⟩ hrb10 hp10 ha10 hb10
  rcases hp10 with h | h | ⟨⟨hv10, hrev10⟩, hs10, -, -, -, -, hm10, -, hl10⟩
  · exact (ha10 h).elim
  · exact (hb10 h).elim
  dsimp only at hv10 hrev10 hs10 hm10 ha10 hb10 hl10
  subst hv10
  have hsub10 : (dataOf x st9).virtual ⊆ (dataOf x st10).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((ends, src10), st10)
      (by with_reducible exact hrb10)).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a10 (⟨src10, b.1.starts⟩, st10)
    _ _ _ _ _ _ (hashStage_sync prims x q s pads u rest noise hkeys top cCore cTime _ _ rfl
      (queries_noBase x.1 _ (queries_leafHash _ _ _ _)) a10 _ hs10 ha10 hb10 hm10) ?_
  rintro ⟨leaf, a11⟩ ⟨⟨leaf', src11⟩, st11⟩ hrb11 hp11 ha11 hb11
  rcases hp11 with h | h | ⟨⟨hv11, hsrc11, -⟩, hs11, -, -, -, -, hm11, -, hl11⟩
  · exact (ha11 h).elim
  · exact (hb11 h).elim
  dsimp only at hv11 hsrc11 hs11 hm11 ha11 hb11 hl11
  subst hv11
  have hsub11 : (dataOf x st10).virtual ⊆ (dataOf x st11).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((leaf, src11), st11)
      (by with_reducible exact hrb11)).1
  refine inPost_bind prims x q s pads u rest noise top cCore cTime a11 (⟨src11, b.1.starts⟩, st11)
    _ _ _ _ _ _ (hashStage_sync prims x q s pads u rest noise hkeys top cCore cTime _ _ rfl
      (queries_noBase x.1 _ (queries_treeFold _ _ _ _ _ _)) a11 _ hs11 ha11 hb11 hm11) ?_
  rintro ⟨topRoot, a12⟩ ⟨⟨topRoot', src12⟩, st12⟩ hrb12 hp12 ha12 hb12
  rcases hp12 with h | h | ⟨⟨hv12, hsrc12, -⟩, hs12, -, -, -, -, hm12, -, hl12⟩
  · exact (ha12 h).elim
  · exact (hb12 h).elim
  dsimp only at hv12 hsrc12 hs12 hm12 ha12 hb12 hl12
  subst hv12
  have hsub12 : (dataOf x st11).virtual ⊆ (dataOf x st12).virtual :=
    (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ ((topRoot, src12), st12)
      (by with_reducible exact hrb12)).1
  have hsub : (dataOf x st6).virtual ⊆ (dataOf x st12).virtual :=
    fun _ h => hsub12 (hsub11 (hsub10 (hsub9 (hsub8 (hsub7 h)))))
  have hsrc : ∀ k, src6.revealed k ≠ none → src12.revealed k ≠ none := by
    intro k hk
    rw [hsrc12, hsrc11, hrev10, hsrc9, hsrc8, hrev7]
    exact hk
  by_cases hroot : topRoot = top.root
  · simp only [hroot, not_true_eq_false, if_false]
    refine inPost_pure prims x q s pads u rest noise top cCore cTime a12 (⟨src12, b.1.starts⟩, st12)
      _ _ _ hs12 hm12 ⟨?_, hterms st12 hsub, fun _ T l => hsub12 (hsub11 (hsub10 (hsub9 (hsub8
        ((hval7 l).2.2.2 T))))), fun tree htree l => ?_, hrevealed src12 hsrc, fun tree htree => ?_⟩
    · change some _ = some (interpretTree s bi _)
      unfold interpretTree
      dsimp only
      rw [patchCpk_rows bi rb1.1.1 rb2.1.1 (by rw [← hv1]; exact hlen1), hv1, hv2,
        show values = fun l => (dvalues l).interpret s from funext fun l => (hval7 l).1]
    · cases htree
      exact ⟨(hval7 l).2.1, (hval7 l).2.2.1⟩
    · cases htree
      exact topDigit_of_resolves (realLog a12) x.1 bi rb4.1.1 randomness digest encoding
        (hres9.mono (hl10.trans (hl11.trans hl12))) hdec
  · simp only [hroot, not_false_eq_true, if_true]
    exact inPost_pure prims x q s pads u rest noise top cCore cTime a12 (⟨src12, b.1.starts⟩, st12)
      none none _ hs12 hm12 ⟨rfl, hterms st12 hsub, fun h => (h rfl).elim, fun _ h => (by cases h),
        hrevealed src12 hsrc, fun _ h => (by cases h)⟩

/-- The bottom tree build of both sides. The real build is the bottom tree of the dealer, and the
compiler build is `sourceBottomTreeX`. No tree is stored. -/
theorem bottomTree_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        ((SigningJointEagerProof.dealtOf x top).bottom bi)).run a)
      (runX (compBackend x q s pads u rest noise) (sourceBottomTreeX x.1 x.2.1 top bi) b.1.base b.2)
      (fun ra rb => InPost prims x q s pads u rest noise top cCore cTime a b
        (fun rb => rb.1.2.revealed)
        (fun va vb => BuildFacts prims x s top bi b va vb ra.2 rb.1.2 rb.2) ra rb) := by
  have hcore := core_sync prims x q s pads u rest noise hkeys top cCore cTime bi a b hs htime ha hb
    hmark
  rw [← realBottom_eq] at hcore
  refine relTriple_post_mono (relTriple_supported hcore) ?_
  rintro ra rb ⟨h | h | ⟨hF, hrest⟩, hra, hrb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨⟨hF.value, sourceBottomTreeX_rows capTag x q s pads (tauOf s pads)
    (gOf s pads u) noise rest top bi b.1.base b.2 rb hrb, hF.terms, hF.starts, hF.shape, hF.revealed,
    fun tree htree => ?_, hF.digit⟩, hrest⟩)
  have hlog : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 := hs.2.1.rest.logAgreement
  have hpriv : RealPrivate x s pads noise (gOf s pads u) rest a.2 (visibleOf a) :=
    hs.1.1.1.realPrivate
  unfold SigningJointEagerProof.dealtOf dealtWith at hra
  rw [simulateQ_map, StateT.run_map, support_map] at hra
  obtain ⟨⟨out, z⟩, hz, rfl⟩ := hra
  have hfull : (out, z) ∈ support ((realHonest prims x s pads u rest (SigningHitProof.hashEmbed
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top
        (.bottom bi)))).run a) := by
    rw [SigningHitProof.hashEmbed_referenceTree]
    change _ ∈ support ((simulateQ (realWorld prims x s pads u rest)
      (φ (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom bi)))).run _)
    rw [← referenceTree_φ]
    exact hz
  generalize hrt : referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1
    top (.bottom bi) = rt at hfull
  obtain ⟨hres, -⟩ := SigningCompilerO1RealLog.honest_resolves prims x s pads u rest noise rt a hlog
    hpriv _ hfull
  obtain ⟨m, hcount⟩ := SigningCompilerO1RealLog.resolves_countRun prims rt _ _ hres 0
  subst hrt
  rw [SigningHitProof.hashEmbed_referenceTree] at hcount
  refine ⟨(realLog z, 0), (out, realLog z, m), hcount, ?_, le_rfl⟩
  rcases out with _ | ⟨t | t⟩
  · cases htree
  · cases htree
  · cases htree
    rfl

end Build

end ThresholdLeanXmssSecurity.SigningCompilerO1Build

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.getD_third' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.getD_third

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.patchCpk_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.patchCpk_rows

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.eval_topEncodingHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.eval_topEncodingHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.decode_of_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.decode_of_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.topDigit_of_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.topDigit_of_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.realWorld_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.realWorld_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.inPost_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.inPost_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.inPost_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.inPost_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.inPost_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.inPost_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.keepsRevealed_topVirtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.keepsRevealed_topVirtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.rows_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.rows_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.commitments_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.commitments_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.topPrf_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.topPrf_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.hashStage_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.hashStage_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.base_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.base_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.values_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.values_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.recover_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.recover_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.core_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.core_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Build.bottomTree_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Build.bottomTree_sync
