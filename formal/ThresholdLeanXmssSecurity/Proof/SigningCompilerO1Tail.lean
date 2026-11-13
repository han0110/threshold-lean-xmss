import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Build
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1TailChain
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Codeword
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRows
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling

/-! # The honest signature tail

- `withReveal` is the compiler state with other reveal maps. `SyncFinal'` is the relation after the
  tail, at reveal maps before the last reveals.
- `compGood_withReveal` states that the good event of the compiler outcome does not read the reveal
  maps.
- `merklePath_congr` states that a Merkle path of the bottom layer reads only the chain ends of the
  tree of its key.
- `sequenceFin_support` couples two sequences step by step. `runX_sequenceFin_support` is its form
  for one side.
- `revealDigests_run` states that the last reveals of the top chain values change only the reveal
  maps.
- `TailInv` is the relation inside the tail after the tree build. The timing clauses read the reveal
  map after the build. `opening_sync`, `chainStep_sync` and `chains_sync` keep it over the opening
  read and the chains, and `tailInv_of_inPost` keeps it over a step with a post `InPost`.
- `syncFinal'_of_syncAt` and `tailInv_final` give `SyncFinal'` from the relation inside the tail.
- `tail_sync` couples the honest signature at a key with `t` signers on both sides. The tree build
  is `bottomTree_sync`, the opening release is void because the key is bound, the codeword search is
  `codeword_sync`, and the path is `hashProgram_sync`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Tail
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Programs SigningCompilerO1Build
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
attribute [local irreducible] Queries

/-! ## The Merkle path of a bottom key -/

/-- A Merkle node of the bottom tree `T` reads only the chain ends of the keys of `T`. -/
theorem merkleNode_congr (P : PublicParameter) (lay : Layer) (f g : KeyIndex → ChainIndex → Digest)
    (T : ℕ) (hT : T < 2 ^ layerHeight)
    (hfg : ∀ key : KeyIndex, key.val / 2 ^ layerHeight = T → f key = g key) :
    ∀ level idx, level ≤ layerHeight → idx / 2 ^ (layerHeight - level) = T →
      merkleNode P lay f level idx = merkleNode P lay g level idx := by
  intro level
  induction level with
  | zero =>
    intro idx _ hidx
    simp only [merkleNode]
    rw [hfg]
    simp only [lifetime, numLayers, layerHeight, Nat.sub_zero] at hidx hT ⊢
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hidx
  | succ level ih =>
    intro idx hl hidx
    have hpow : 2 ^ (layerHeight - level) = 2 * 2 ^ (layerHeight - (level + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    have h0 : (2 * idx) / 2 ^ (layerHeight - level) = T := by
      rw [hpow, Nat.mul_div_mul_left _ _ (by decide)]
      exact hidx
    have h1 : (2 * idx + 1) / 2 ^ (layerHeight - level) = T := by
      rw [hpow, ← Nat.div_div_eq_div_mul]
      have : (2 * idx + 1) / 2 = idx := by omega
      rw [this]
      exact hidx
    simp only [merkleNode]
    rw [ih (2 * idx) (by omega) h0, ih (2 * idx + 1) (by omega) h1]

/-- A Merkle path of the bottom layer reads only the chain ends of the tree of its key. -/
theorem merklePath_congr (P : PublicParameter) (f g : KeyIndex → ChainIndex → Digest)
    (key : KeyIndex)
    (hfg : ∀ key' : KeyIndex, treeOf key' = treeOf key → f key' = g key') :
    merklePath P bottomLayer f key = merklePath P bottomLayer g key := by
  unfold merklePath
  congr 1
  funext level
  refine merkleNode_congr P bottomLayer f g (treeOf key).val (treeOf key).isLt
    (fun key' h => hfg key' (Fin.ext h)) level.val _ level.isLt.le ?_
  have hl := level.isLt
  have hpow : 2 ^ (layerHeight - level.val) = 2 * 2 ^ (layerHeight - (level.val + 1)) := by
    rw [← pow_succ']
    congr 1
    simp only [layerHeight] at hl ⊢
    omega
  have hx : Nat.xor (key.val / 2 ^ level.val) 1 / 2 = key.val / 2 ^ level.val / 2 := by
    generalize key.val / 2 ^ level.val = n
    have h1 : Nat.xor n 1 >>> 1 = n >>> 1 := by
      change (n ^^^ 1) >>> 1 = n >>> 1
      rw [Nat.shiftRight_xor_distrib]
      simp
    simpa only [Nat.shiftRight_eq_div_pow, pow_one] using h1
  rw [hpow, ← Nat.div_div_eq_div_mul, hx, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    ← pow_succ', ← pow_add]
  simp only [treeOf, layerHeight] at hl ⊢
  congr 2
  omega

/-! ## Sequences -/

/-- Two sequences couple step by step. Each stop persists, and `Inv` passes from step to step. -/
theorem sequenceFin_support {σ α β : Type}
    (backend : QueryImpl (SpecX C) (StateT (CompState C) ProbComp))
    (Stop1 : σ → Prop) (Stop2 : CompState C → Prop) (Inv : σ → SourceState C → CompState C → Prop) :
    ∀ {n : ℕ} (f : Fin n → StateT σ ProbComp α) (g : Fin n → SourceMX C β)
      (R : Fin n → α → β → Prop),
      (∀ i a, Stop1 a → ∀ ra ∈ support ((f i).run a), Stop1 ra.2) →
      (∀ i src st, Stop2 st → ∀ rb ∈ support (runX backend (g i) src st), Stop2 rb.2) →
      (∀ i a src st, Inv a src st → ¬Stop1 a → ¬Stop2 st →
        ∀ ra ∈ support ((f i).run a), ∀ rb ∈ support (runX backend (g i) src st),
          Stop1 ra.2 ∨ Stop2 rb.2 ∨ (R i ra.1 rb.1.1 ∧ Inv ra.2 rb.1.2 rb.2)) →
      ∀ a src st, ∀ ra ∈ support ((Concrete.sequenceFin f).run a),
        ∀ rb ∈ support (runX backend (Concrete.sequenceFin g) src st),
          (Stop1 a → Stop1 ra.2) ∧ (Stop2 st → Stop2 rb.2) ∧
          (Inv a src st → ¬Stop1 a → ¬Stop2 st → Stop1 ra.2 ∨ Stop2 rb.2 ∨
            ((∀ i, R i (ra.1 i) (rb.1.1 i)) ∧ Inv ra.2 rb.1.2 rb.2))
  | 0, f, g, R, _, _, _, a, src, st, ra, hra, rb, hrb => by
    simp only [Concrete.sequenceFin, StateT.run_pure, mem_support_pure_iff] at hra
    simp only [Concrete.sequenceFin, runX_pure, mem_support_pure_iff] at hrb
    subst hra hrb
    exact ⟨id, id, fun hi _ _ => Or.inr (Or.inr ⟨fun i => i.elim0, hi⟩)⟩
  | n + 1, f, g, R, h1, h2, hstep, a, src, st, ra, hra, rb, hrb => by
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hra
    simp only [Concrete.sequenceFin, runX_bind, runX_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hrb
    obtain ⟨ra1, hra1, ra2, hra2, rfl⟩ := hra
    obtain ⟨rb1, hrb1, rb2, hrb2, rfl⟩ := hrb
    have ih := sequenceFin_support backend Stop1 Stop2 Inv (fun i => f i.succ) (fun i => g i.succ)
      (fun i => R i.succ) (fun i => h1 i.succ) (fun i => h2 i.succ) (fun i => hstep i.succ)
      ra1.2 rb1.1.2 rb1.2 ra2 hra2 rb2 hrb2
    refine ⟨fun hs => ih.1 (h1 0 a hs ra1 hra1), fun hs => ih.2.1 (h2 0 src st hs rb1 hrb1),
      fun hi ha hb => ?_⟩
    rcases hstep 0 a src st hi ha hb ra1 hra1 rb1 hrb1 with hs | hs | ⟨hr, hi1⟩
    · exact Or.inl (ih.1 hs)
    · exact Or.inr (Or.inl (ih.2.1 hs))
    by_cases ha1 : Stop1 ra1.2
    · exact Or.inl (ih.1 ha1)
    by_cases hb1 : Stop2 rb1.2
    · exact Or.inr (Or.inl (ih.2.1 hb1))
    rcases ih.2.2 hi1 ha1 hb1 with hs | hs | ⟨hr', hi2⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    refine Or.inr (Or.inr ⟨fun i => ?_, hi2⟩)
    cases i using Fin.cases with
    | zero => exact hr
    | succ i => exact hr' i

/-- A sequence on the compiler side keeps `Inv` step by step. -/
theorem runX_sequenceFin_support {β : Type}
    (backend : QueryImpl (SpecX C) (StateT (CompState C) ProbComp))
    (Inv : SourceState C → CompState C → Prop) :
    ∀ {n : ℕ} (g : Fin n → SourceMX C β) (R : Fin n → β → Prop),
      (∀ i src st, Inv src st → ∀ rb ∈ support (runX backend (g i) src st),
        R i rb.1.1 ∧ Inv rb.1.2 rb.2) →
      ∀ src st, Inv src st → ∀ rb ∈ support (runX backend (Concrete.sequenceFin g) src st),
        (∀ i, R i (rb.1.1 i)) ∧ Inv rb.1.2 rb.2
  | 0, g, R, _, src, st, hi, rb, hrb => by
    simp only [Concrete.sequenceFin, runX_pure, mem_support_pure_iff] at hrb
    subst hrb
    exact ⟨fun i => i.elim0, hi⟩
  | n + 1, g, R, hstep, src, st, hi, rb, hrb => by
    simp only [Concrete.sequenceFin, runX_bind, runX_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hrb
    obtain ⟨rb1, hrb1, rb2, hrb2, rfl⟩ := hrb
    obtain ⟨hr, hi1⟩ := hstep 0 src st hi rb1 hrb1
    obtain ⟨hr', hi2⟩ := runX_sequenceFin_support backend Inv (fun i => g i.succ)
      (fun i => R i.succ) (fun i => hstep i.succ) rb1.1.2 rb1.2 hi1 rb2 hrb2
    refine ⟨fun i => ?_, hi2⟩
    cases i using Fin.cases with
    | zero => exact hr
    | succ i => exact hr' i

section Finish
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The compiler state with other reveal maps. The last step of the honest signature reveals top
chain values and plants no answer, so the relation after the tail holds at the reveal maps before
that step. -/
def withReveal (b : SourceStateO1 C × CompState C) (source wrapper : HiddenKey → Option Digest) :
    SourceStateO1 C × CompState C :=
  (⟨{ b.1.base with revealed := source }, b.1.starts⟩,
    (((b.2.1.1.1, (wrapper, b.2.1.1.2.2)), b.2.1.2), b.2.2))

/-- The relation after the tail, at reveal maps before the last reveals. -/
def SyncFinal' (top : TopTree) (vlog : List (HiddenKey × Digest)) (a : RealState C)
    (b : SourceStateO1 C × CompState C) : Prop :=
  ∃ source wrapper : HiddenKey → Option Digest,
    SyncFinal prims x top s pads noise (gOf s pads u) rest vlog a (withReveal b source wrapper)

/-- The good event of the compiler outcome does not read the reveal maps. -/
theorem compGood_withReveal (c : CompFinal C) (source wrapper : HiddenKey → Option Digest) :
    CompGood x q (SigningCompilerShareTables.finish x.2.1
      ((c.1.1, (withReveal (c.1.2, c.2) source wrapper).1),
        (withReveal (c.1.2, c.2) source wrapper).2)).1 ↔
      CompGood x q (SigningCompilerShareTables.finish x.2.1 c).1 :=
  Iff.rfl

/-- The last reveals of the top chain values give the values at the secrets. They change only the
reveal maps of both states. -/
theorem revealDigests_run (values : ChainIndex → DeferredDigest) (src : SourceState C)
    (st : CompState C) (hrel : RevealRelation s src st.1.1)
    (hfree : RestFree x.2.1 st.1.1.1.1.data.cache)
    (rb : ((ChainIndex → Digest) × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (Concrete.sequenceFin fun l => sourceRevealDigestX (values l)) src st)) :
    (∀ l, rb.1.1 l = (values l).interpret s) ∧ rb.1.2 = { src with revealed := rb.1.2.revealed } ∧
      rb.2 = (((st.1.1.1, (rb.2.1.1.2.1, st.1.1.2.2)), st.1.2), st.2) := by
  have h := runX_sequenceFin_support (compBackend x q s pads u rest noise)
    (fun src' st' => RevealRelation s src' st'.1.1 ∧ src' = { src with revealed := src'.revealed } ∧
      st' = (((st.1.1.1, (st'.1.1.2.1, st.1.1.2.2)), st.1.2), st.2))
    (fun l => sourceRevealDigestX (values l)) (fun l v => v = (values l).interpret s) ?_ src st
    ⟨hrel, rfl, rfl⟩ rb hrb
  · exact ⟨h.1, h.2.2⟩
  rintro l src' st' ⟨hrel', hsrc', hst'⟩ r hr
  cases hv : values l with
  | known w =>
    rw [hv] at hr
    simp only [sourceRevealDigestX, runX_pure, mem_support_pure_iff] at hr
    subst hr
    exact ⟨rfl, hrel', hsrc', hst'⟩
  | secret k =>
    rw [hv] at hr
    have hfree' : RestFree x.2.1 st'.1.1.1.1.data.cache := by rw [hst']; exact hfree
    obtain ⟨h1, h2, h3, h4⟩ := sourceRevealX_sync capTag x q s pads (tauOf s pads) (gOf s pads u)
      noise rest k src' st' hrel' hfree' r hr
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [h3, hsrc']
    · rw [h4, hst']

/-- The stop of the real side persists over a run in the real world. -/
theorem realWorld_stop {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) : RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r hr) _ a h r hr

/-- A coupling from a stopped real state holds each post that a real stop gives. -/
theorem relTriple_realStop {α β : Type} (oa : OracleComp (WorldSpec C) α) (ob : ProbComp β)
    (a : RealState C) (h : RealStop q a) {R : α × RealState C → β → Prop}
    (hR : ∀ r : α × RealState C, RealStop q r.2 → ∀ c, R r c) :
    RelTriple ((simulateQ (realWorld prims x s pads u rest) oa).run a) ob R :=
  relTriple_of_support_left fun r hr c =>
    hR r (realWorld_stop prims x q s pads u rest oa a h r hr) c

/-- A coupling from a stopped compiler state holds each post that a compiler stop gives. -/
theorem relTriple_compStop {α β : Type} (oa : ProbComp α) (ob : SourceMX C β)
    (src : SourceState C) (st : CompState C) (h : Stop st)
    {R : α → (β × SourceState C) × CompState C → Prop}
    (hR : ∀ r : (β × SourceState C) × CompState C, Stop r.2 → ∀ c, R c r) :
    RelTriple oa (runX (compBackend x q s pads u rest noise) ob src st) R :=
  SigningOpeningProof.relTriple_of_support_right fun r hr c =>
    hR r (runX_compStop x q s pads u rest noise ob src st h r hr) c

/-- The relation inside the tail after the tree build. `rev` is the reveal map after the build, and
`a` is the real state at the start of the tail. The rows of key `e` have their virtual terms and their
pending answers. -/
def TailInv (top : TopTree) (rev : HiddenKey → Option Digest) (c : Carried C) (a : RealState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex) (a' : RealState C)
    (src : SourceState C) (st : CompState C) : Prop :=
  SyncAt prims x s pads u rest noise top rev (fun _ _ => False) c c a' (⟨src, starts⟩, st) ∧
    (∀ l (d : XmssSecurity.ChainStep),
      (∀ T, (T, Point.chain bottomLayer e l (chainStepDigit d)) ∈ (dataOf x st).virtual) ∧
        (dataOf x st).pending (.bottom e l d) ≠ none) ∧
    st.1.2 = false ∧ a'.1.2 = a.1.2 ∧ ∀ k, rev k ≠ none → src.revealed k ≠ none

/-- The post of a step inside the tail keeps `TailInv` when the step keeps each revealed key. -/
theorem tailInv_of_inPost (top : TopTree) (rev : HiddenKey → Option Digest) (c : Carried C)
    (a : RealState C) (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex)
    (a' : RealState C) (src : SourceState C) (st : CompState C)
    (hi : TailInv prims x s pads u rest noise top rev c a starts e a' src st)
    {α β : Type} (value : α → β → Prop) (oa : SourceMX C β)
    (ra : α × RealState C) (rb : (β × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise) oa src st))
    (h : InPost prims x q s pads u rest noise top c c a' (⟨src, starts⟩, st) (fun _ => rev) value
      ra rb)
    (hmono : value ra.1 rb.1.1 → ∀ k, src.revealed k ≠ none → rb.1.2.revealed k ≠ none) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (value ra.1 rb.1.1 ∧ TailInv prims x s pads u rest noise top rev c a starts e ra.2 rb.1.2 rb.2) := by
  rcases h with h | h | ⟨hv, hsync, -, -, -, -, hm, hc, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hrows := SigningCompilerSyncRows.simulate_rows capTag x q s pads (tauOf s pads) (gOf s pads u)
    noise rest (oa.run src) st rb hrb
  refine Or.inr (Or.inr ⟨hv, hsync, fun l d => ⟨fun T => hrows.1 ((hi.2.1 l d).1 T),
    hrows.2 _ (hi.2.1 l d).2⟩, hm, hc.trans hi.2.2.2.1, fun k hk => hmono hv k (hi.2.2.2.2 k hk)⟩)

/-- The opening read of the tail. Both sides read the PRF value, and no revealed key changes. -/
theorem opening_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (c : Carried C) (a : RealState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex)
    (a' : RealState C) (src : SourceState C) (st : CompState C)
    (hi : TailInv prims x s pads u rest noise top rev c a starts e a' src st)
    (ha : ¬RealStop q a') (hb : ¬Stop st) (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (prfValue x.2.1 (.randomizer bottomLayer e))).run a'))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.randomizer bottomLayer e))) src st)) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (ra.1 = rb.1.1 ∧ TailInv prims x s pads u rest noise top rev c a starts e ra.2 rb.1.2 rb.2 ∧
        (∀ k, src.revealed k ≠ none → rb.1.2.revealed k = src.revealed k) ∧
        rb.1.2.signing = src.signing) := by
  obtain ⟨⟨hcore, hx, htop, hpads⟩, hrows, hm, hc, hrev⟩ := hi
  have hP := prfValue_sync prims x q s pads u rest noise hkeys c
    ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩ a' src st hcore ha hb hm ra
    (by with_reducible exact hra) rb hrb
  rcases hP with h | h | ⟨⟨hv, -⟩, hcore2, hf, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hx2 := ExtraOpen.frame prims x top s _ (fun _ _ => False) (fun _ _ => False) rev rev c a' ra.2
    (⟨src, starts⟩, st) (⟨rb.1.2, starts⟩, rb.2) hx hf rfl (fun _ h => h) (fun _ h => Or.inl h)
    (fun _ _ _ hseen => by obtain ⟨T, hT⟩ := hseen; cases hT)
    (fun _ _ _ hseen => by obtain ⟨T, hT⟩ := hseen; cases hT)
    (fun T p hseen => by
      obtain ⟨T', hT⟩ := hseen
      injection hT with _ hT
      subst hT
      exact Or.inr (constrained_bottom_randomizer e))
    (fun T e' l' d' hseen => by
      obtain ⟨T', hT⟩ := hseen
      injection hT with _ hT
      cases hT)
    (fun _ _ h => h)
  have hpads2 : PadsFixed x pads rb.2 := backend_padsFixed x q s pads u rest noise _ st hpads rb hrb
  refine Or.inr (Or.inr ⟨hv, ⟨⟨hcore2, hx2, TopO1.frame prims x top _ a' ra.2 _ (⟨rb.1.2, starts⟩, rb.2)
    htop hf, hpads2⟩, fun l d => ⟨fun T => hf.virtual _ _ ((hrows l d).1 T), hf.pending _ (hrows l d).2⟩,
    hm2, hf.carried.trans hc, fun k hk => ?_⟩, hf.revealed, hf.signing⟩)
  rw [hf.revealed k (hrev k hk)]
  exact hrev k hk

/-- One chain of the tail below digit 3. Both sides give the same value. -/
theorem chainStep_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (c : Carried C) (a : RealState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex) (l : ChainIndex) (d : Digit)
    (hd : d.val < 3) (H : Digest → Digest)
    (a' : RealState C) (src : SourceState C) (st : CompState C)
    (hi : TailInv prims x s pads u rest noise top rev c a starts e a' src st)
    (ha : ¬RealStop q a') (hb : ¬Stop st) (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (prfValue x.2.1 (.chain bottomLayer e l d)) >>= fun f => pure (H f)).run a'))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      ((do
        sourceReleaseBottomSuffixX x.1 x.2.1 e l d
        sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.chain bottomLayer e l d))) >>= fun v =>
          pure (H v)) src st)) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (ra.1 = rb.1.1 ∧ TailInv prims x s pads u rest noise top rev c a starts e ra.2 rb.1.2 rb.2) := by
  rw [StateT.run_bind, mem_support_bind_iff] at hra
  obtain ⟨r1, h1, h2⟩ := hra
  rw [StateT.run_pure, mem_support_pure_iff] at h2
  rw [runX_bind, mem_support_bind_iff] at hrb
  obtain ⟨rb1, hb1, hb2⟩ := hrb
  rw [runX_pure, mem_support_pure_iff] at hb2
  subst h2 hb2
  have hT := SigningCompilerO1TailChain.tailChain_sync prims x q s pads u rest noise hkeys top rev c
    e l d hd a' (⟨src, starts⟩, st) hi.1 (hi.2.1 l) ha hb hi.2.2.1 r1 (by with_reducible exact h1)
    rb1 hb1
  rcases tailInv_of_inPost prims x q s pads u rest noise top rev c a starts e a' src st hi _ _ r1 rb1
    hb1 hT (fun hv => hv.2) with h | h | ⟨⟨hv, -⟩, hi2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨congrArg H hv, hi2⟩)

/-- The chains of the tail. A chain at digit 3 gives the same known value on both sides, and a chain
below digit 3 is `chainStep_sync`. -/
theorem chains_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (c : Carried C) (a : RealState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex) (encoding : Encoding)
    (f : ChainIndex → StateT (RealState C) ProbComp Digest) (g : ChainIndex → SourceMX C Digest)
    (hshape : ∀ l, (∃ w, f l = pure w ∧ g l = pure w) ∨ ∃ H : Digest → Digest,
      (encoding l).val < 3 ∧
      f l = (realHonest prims x s pads u rest
        (prfValue x.2.1 (.chain bottomLayer e l (encoding l))) >>= fun v => pure (H v)) ∧
      g l = ((do
        sourceReleaseBottomSuffixX x.1 x.2.1 e l (encoding l)
        sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.chain bottomLayer e l (encoding l)))) >>=
          fun v => pure (H v)))
    (a' : RealState C) (src : SourceState C) (st : CompState C)
    (hi : TailInv prims x s pads u rest noise top rev c a starts e a' src st)
    (ha : ¬RealStop q a') (hb : ¬Stop st) (ra : (ChainIndex → Digest) × RealState C)
    (hra : ra ∈ support ((Concrete.sequenceFin f).run a'))
    (rb : ((ChainIndex → Digest) × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise) (Concrete.sequenceFin g) src st)) :
    RealStop q ra.2 ∨ Stop rb.2 ∨
      (ra.1 = rb.1.1 ∧ TailInv prims x s pads u rest noise top rev c a starts e ra.2 rb.1.2 rb.2) := by
  have h := sequenceFin_support (compBackend x q s pads u rest noise) (RealStop q) Stop
    (TailInv prims x s pads u rest noise top rev c a starts e) f g (fun _ va vb => va = vb) ?_ ?_ ?_
    a' src st ra hra rb hrb
  · rcases h.2.2 hi ha hb with h | h | ⟨hv, hi2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨funext hv, hi2⟩)
  · intro l a1 hs r hr
    rcases hshape l with ⟨w, hf, -⟩ | ⟨H, -, hf, -⟩ <;> rw [hf] at hr
    · rw [StateT.run_pure, mem_support_pure_iff] at hr
      subst hr
      exact hs
    · rw [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨r1, h1, h2⟩ := hr
      rw [StateT.run_pure, mem_support_pure_iff] at h2
      subst h2
      exact realHonest_stop prims x q s pads u rest _ a1 hs r1 h1
  · intro l src1 st1 hs r hr
    exact runX_compStop x q s pads u rest noise _ src1 st1 hs r hr
  · intro l a1 src1 st1 hi1 ha1 hb1 r1 hr1 r2 hr2
    rcases hshape l with ⟨w, hf, hg⟩ | ⟨H, hd, hf, hg⟩
    · rw [hf, StateT.run_pure, mem_support_pure_iff] at hr1
      rw [hg, runX_pure, mem_support_pure_iff] at hr2
      subst hr1 hr2
      exact Or.inr (Or.inr ⟨rfl, hi1⟩)
    · rw [hf] at hr1
      rw [hg] at hr2
      exact chainStep_sync prims x q s pads u rest noise hkeys top rev c a starts e l (encoding l) hd
        H a1 src1 st1 hi1 ha1 hb1 r1 hr1 r2 hr2

/-- The relation inside the tail at the carried state of the verification gives the relation after
the tail. `b0` is the state before the last reveals, and `b1` is the state after them. -/
theorem syncFinal'_of_syncAt (top : TopTree) (vlog : List (HiddenKey × Digest)) (a : RealState C)
    (rev : HiddenKey → Option Digest) (ra : RealState C) (b0 b1 : SourceStateO1 C × CompState C)
    (hsync : SyncAt prims x s pads u rest noise top rev (fun _ _ => False)
      (withCandidates a (a.1.2.2.2 ++ vlog)).1.2 (withCandidates a (a.1.2.2.2 ++ vlog)).1.2 ra b0)
    (hrev : ∀ k, rev k ≠ none → b0.1.base.revealed k ≠ none) (hc : ra.1.2 = a.1.2)
    (hw : withReveal b1 b0.1.base.revealed b0.2.1.1.2.1 = b0) :
    SyncFinal' prims x s pads u rest noise top vlog ra b1 := by
  refine ⟨b0.1.base.revealed, b0.2.1.1.2.1, ?_⟩
  rw [hw]
  obtain ⟨⟨ra1, rc⟩, ra2⟩ := ra
  change rc = a.1.2 at hc
  subst hc
  obtain ⟨hcore, hx, htop, -⟩ := hsync
  exact ⟨hcore, htop, rev, hrev,
    extra_of_extraOpen prims x top s rev (fun _ _ => False) _ b0 hx (fun _ _ h => h.elim)⟩

/-- The relation inside the tail gives the relation after the tail at the same state. A failed step
of the tail returns there. -/
theorem tailInv_final (top : TopTree) (vlog : List (HiddenKey × Digest)) (a : RealState C)
    (rev : HiddenKey → Option Digest) (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex)
    (a' : RealState C) (src : SourceState C) (st : CompState C)
    (hi : TailInv prims x s pads u rest noise top rev (withCandidates a (a.1.2.2.2 ++ vlog)).1.2 a
      starts e a' src st) :
    a'.1.2 = a.1.2 ∧ SyncFinal' prims x s pads u rest noise top vlog a' (⟨src, starts⟩, st) :=
  ⟨hi.2.2.2.1, syncFinal'_of_syncAt prims x s pads u rest noise top vlog a rev a' (⟨src, starts⟩, st)
    (⟨src, starts⟩, st) hi.1 hi.2.2.2.2 hi.2.2.2.1 rfl⟩

/-- The honest signature at a key with `t` signers on both sides. Both sides give the same
signature. The relation after the tail holds at reveal maps before the last reveals. -/
theorem tail_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (e : KeyIndex) (message : Message) (vlog : List (HiddenKey × Digest))
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest
      (withCandidates a (a.1.2.2.2 ++ vlog)) b ∧ PadsFixed x pads b.2)
    (ht : C.t ≤ (signersAt (realSigning a) e message).card)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        (honestSignature (fun oa => SigningCoreProof.honestLift oa)
          (SigningJointEagerProof.dealtOf x top) e message)).run a)
      (runXO1 (compBackend x q s pads u rest noise)
        (liftBaseX (sourceHonestSignatureX prims x top e message)) b.1 b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1 = rb.1.1 ∧ ra.2.1.2 = a.1.2 ∧
          SyncFinal' prims x s pads u rest noise top vlog ra.2 (rb.1.2, rb.2))) := by
  obtain ⟨hsync, hpads⟩ := hs
  have hin : SyncIn prims x s pads u rest noise top (withCandidates a (a.1.2.2.2 ++ vlog)).1.2
      (withCandidates a (a.1.2.2.2 ++ vlog)).1.2 a b := by
    have h := (syncO1_iff_syncIn prims x s pads u rest noise top _ b).1 ⟨hsync, hpads⟩
    exact ⟨h.1, h.2.1, ⟨h.2.2.1.topRows, h.2.2.1.topRun⟩, h.2.2.2⟩
  rw [runXO1_liftBaseX]
  refine SigningCompilerO1Reads.relTriple_map_right _ ?_
  unfold honestSignature sourceHonestSignatureX
  rw [simulateQ_bind, StateT.run_bind, runX_bind]
  refine relTriple_bind (SigningCompilerSyncLocalRead.relTriple_supported
    (bottomTree_sync prims x q s pads u rest noise hkeys top
    _ _ (treeOf e) a b hin rfl ha hb hmark)) fun r1a r1b h1 => ?_
  obtain ⟨h1, -, hr1b⟩ := h1
  rcases h1 with h1 | h1 | ⟨hF, hsync1, -, -, -, -, hm1, hc1, -⟩
  · exact relTriple_realStop prims x q s pads u rest _ _ _ h1 fun _ hr _ => Or.inl hr
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ h1 fun _ hr _ => Or.inr (Or.inl hr)
  by_cases ha1 : RealStop q r1a.2
  · exact relTriple_realStop prims x q s pads u rest _ _ _ ha1 fun _ hr _ => Or.inl hr
  by_cases hb1 : Stop r1b.2
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ hb1 fun _ hr _ => Or.inr (Or.inl hr)
  obtain ⟨real, a1⟩ := r1a
  obtain ⟨⟨sym, src1⟩, st1⟩ := r1b
  have hval : real = sym.map (interpretTree s (treeOf e)) := hF.value
  have hi1 : TailInv prims x s pads u rest noise top src1.revealed
      (withCandidates a (a.1.2.2.2 ++ vlog)).1.2 a b.1.starts e a1 src1 st1 := by
    refine ⟨hsync1, fun l d => ?_, hm1, hc1, fun _ h => h⟩
    have hrow := hF.rows ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ l d
    rwa [bottomKey_treeOf] at hrow
  cases sym with
  | none =>
    subst hval
    obtain ⟨hc, hfin⟩ := tailInv_final prims x s pads u rest noise top vlog a _ _ e a1 src1 st1 hi1
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hc, hfin⟩))
  | some tree =>
  subst hval
  have hbound : (realSigning a).bound e = some message := by
    have hcor : (realSigning a).corrupt.card ≤ C.t - 1 := hin.2.1.rest.corruptBound
    have hle := Finset.card_union_le (realSigning a).corrupt
      (((realSigning a).released.filter fun r => r.1 = e ∧ r.2.1 = message).map (·.2.2)).toFinset
    have hpos : 0 < (((realSigning a).released.filter fun r => r.1 = e ∧ r.2.1 = message).map
        (·.2.2)).toFinset.card := by
      have := C.one_le_t
      unfold signersAt at ht
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
    rw [List.mem_toFinset, List.mem_map] at hi
    obtain ⟨r, hr, -⟩ := hi
    rw [List.mem_filter] at hr
    obtain ⟨hr, hre⟩ := hr
    simp only [decide_eq_true_eq] at hre
    have hb' := hin.2.1.rest.releasedBound r.1 r.2.1 r.2.2 hr
    rw [hre.1, hre.2] at hb'
    exact hb'
  have hopen : src1.revealed (.opening bottomLayer e) ≠ none := by
    have hk := hF.revealed.2 ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ (by
      rw [bottomKey_treeOf, hin.1.1.1.bound]
      change (realSigning a).bound e ≠ none
      rw [hbound]
      exact Option.some_ne_none _)
    rwa [bottomKey_treeOf] at hk
  rw [Option.map_some]
  dsimp only
  rw [simulateQ_bind, StateT.run_bind, runX_bind,
    SigningCompilerSyncBackend.runX_releaseOpening_revealed _ _ _ _ _ _ hopen, pure_bind, runX_bind]
  refine relTriple_bind (TreeCheckKernelCoupling.relTriple_of_support fun r2a hr2a r2b hr2b =>
    opening_sync prims x q s pads u rest noise hkeys top _ _ a b.1.starts e a1 src1 st1 hi1 ha1 hb1
      r2a (by exact hr2a) r2b hr2b) fun r2a r2b h2 => ?_
  rcases h2 with h2 | h2 | ⟨hv2, hi2, hrev2, -⟩
  · exact relTriple_realStop prims x q s pads u rest _ _ _ h2 fun _ hr _ => Or.inl hr
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ h2 fun _ hr _ => Or.inr (Or.inl hr)
  by_cases ha2 : RealStop q r2a.2
  · exact relTriple_realStop prims x q s pads u rest _ _ _ ha2 fun _ hr _ => Or.inl hr
  by_cases hb2 : Stop r2b.2
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ hb2 fun _ hr _ => Or.inr (Or.inl hr)
  have hopen2 : r2b.1.2.revealed (.opening bottomLayer e) ≠ none := by
    rw [hrev2 _ hopen]
    exact hopen
  rw [simulateQ_bind, StateT.run_bind, runX_bind, hv2]
  refine relTriple_bind (SigningCompilerSyncLocalRead.relTriple_supported
    (SigningCompilerO1Codeword.codeword_sync prims x q s pads u rest noise hkeys top src1.revealed
      _ _ (tree.commitment e) e message r2b.1.1 r2a.2 (⟨r2b.1.2, b.1.starts⟩, r2b.2) hi2.1
      (by rw [hi2.2.2.2.1]; rfl) rfl hbound hopen2 ha2 hb2 hi2.2.2.1)) fun r3a r3b h3 => ?_
  obtain ⟨h3, -, hr3b⟩ := h3
  rcases tailInv_of_inPost prims x q s pads u rest noise top _ _ a b.1.starts e r2a.2 r2b.1.2 r2b.2
      hi2 _ _ r3a r3b hr3b h3 (fun hv k hk => by rw [hv.2.1]; exact hk) with
    h3 | h3 | ⟨⟨hv3, -, -⟩, hi3⟩
  · exact relTriple_realStop prims x q s pads u rest _ _ _ h3 fun _ hr _ => Or.inl hr
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ h3 fun _ hr _ => Or.inr (Or.inl hr)
  by_cases ha3 : RealStop q r3a.2
  · exact relTriple_realStop prims x q s pads u rest _ _ _ ha3 fun _ hr _ => Or.inl hr
  by_cases hb3 : Stop r3b.2
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ hb3 fun _ hr _ => Or.inr (Or.inl hr)
  obtain ⟨res, a3⟩ := r3a
  obtain ⟨⟨res', src3⟩, st3⟩ := r3b
  change res = res' at hv3
  subst hv3
  rcases res with _ | ⟨randomness, encoding⟩
  · obtain ⟨hc, hfin⟩ := tailInv_final prims x s pads u rest noise top vlog a _ _ e a3 src3 st3 hi3
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hc, hfin⟩))
  dsimp only
  rw [simulateQ_bind, StateT.run_bind, runX_bind, simulateQ_sequenceFin]
  refine relTriple_bind (TreeCheckKernelCoupling.relTriple_of_support fun r4a hr4a r4b hr4b =>
    chains_sync prims x q s pads u rest noise hkeys top _ _ a b.1.starts e encoding _ _ ?_ a3 src3 st3
      hi3 ha3 hb3 r4a hr4a r4b hr4b) fun r4a r4b h4 => ?_
  · intro l
    have hpatch : (interpretTree s (treeOf e) tree).cpk e l = tree.cpk e l := by
      simp only [interpretTree, patchCpk, if_true]
    simp only [hpatch]
    generalize encoding l = d
    obtain ⟨n, hn⟩ := d
    rcases n with _ | _ | _ | _ | n
    · exact Or.inr ⟨fun v => v, (by decide : (0 : ℕ) < 3), by simp; rfl, by simp⟩
    · exact Or.inr ⟨fun v => (tree.cpk e l).1 ^^^ v, (by decide : (1 : ℕ) < 3), by simp; rfl,
        by simp⟩
    · exact Or.inr ⟨fun v => (tree.cpk e l).2.1 ^^^ v, (by decide : (2 : ℕ) < 3), by simp; rfl,
        by simp⟩
    · exact Or.inl ⟨(tree.cpk e l).2.2, by simp, by simp⟩
    · exact absurd hn (by change ¬ _ < 4; omega)
  rcases h4 with h4 | h4 | ⟨hv4, hi4⟩
  · exact relTriple_realStop prims x q s pads u rest _ _ _ h4 fun _ hr _ => Or.inl hr
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ h4 fun _ hr _ => Or.inr (Or.inl hr)
  by_cases ha4 : RealStop q r4a.2
  · exact relTriple_realStop prims x q s pads u rest _ _ _ ha4 fun _ hr _ => Or.inl hr
  by_cases hb4 : Stop r4b.2
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ hb4 fun _ hr _ => Or.inr (Or.inl hr)
  obtain ⟨values, a4⟩ := r4a
  obtain ⟨⟨values', src4⟩, st4⟩ := r4b
  change values = values' at hv4
  subst hv4
  have hpath : merklePath (SigningJointEagerProof.dealtOf x top).parameter bottomLayer
      (fun e' l => ((interpretTree s (treeOf e) tree).cpk e' l).2.2) e =
      merklePath x.1 bottomLayer (fun key l => (tree.cpk key l).2.2) e :=
    merklePath_congr x.1 _ _ e fun key hk => by simp only [interpretTree, patchCpk, hk, if_true]
  rw [simulateQ_bind, StateT.run_bind, runX_bind, hpath]
  have hbase := SigningCompilerO1Queries.queries_noBase x.1 _
    (SigningCompilerO1Queries.queries_merklePath x.1 bottomLayer (fun key l => (tree.cpk key l).2.2) e)
  refine relTriple_bind (SigningCompilerSyncLocalRead.relTriple_supported
    (SigningCompilerO1HashProgram.hashProgram_sync prims x q s pads u rest noise hkeys top
      src1.revealed _ _ (merklePath x.1 bottomLayer (fun key l => (tree.cpk key l).2.2) e) hbase a4
      (⟨src4, b.1.starts⟩, st4) hi4.1 ha4 hb4 hi4.2.2.1)) fun r5a r5b h5 => ?_
  obtain ⟨h5, -, hr5b⟩ := h5
  generalize merklePath x.1 bottomLayer (fun key l => (tree.cpk key l).2.2) e = P at h5 hr5b
  rcases tailInv_of_inPost prims x q s pads u rest noise top _ _ a b.1.starts e a4 src4 st4
      hi4 _ (sourceHashProgramX x.1 x.2.1 P) r5a r5b hr5b h5
      (fun hv k hk => by rw [hv.2.1]; exact hk) with
    h5 | h5 | ⟨⟨hv5, -, -⟩, hi5⟩
  · exact relTriple_realStop prims x q s pads u rest _ _ _ h5 fun _ hr _ => Or.inl hr
  · exact relTriple_compStop x q s pads u rest noise _ _ _ _ h5 fun _ hr _ => Or.inr (Or.inl hr)
  obtain ⟨path, a5⟩ := r5a
  obtain ⟨⟨path', src5⟩, st5⟩ := r5b
  change path = path' at hv5
  subst hv5
  rw [runX_bind]
  refine TreeCheckKernelCoupling.relTriple_of_support fun r6a hr6a r6b hr6b => ?_
  rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr6a
  rw [mem_support_bind_iff] at hr6b
  obtain ⟨rv, hrv, hr6b⟩ := hr6b
  rw [runX_pure, mem_support_pure_iff] at hr6b
  subst hr6a hr6b
  obtain ⟨hvals, hsrc, hst⟩ := revealDigests_run x q s pads u rest noise
    (fun l => tree.topSignature.chainValue l) src5 st5 hi5.1.1.1.1.reveal hi5.1.1.1.1.restFree rv hrv
  refine Or.inr (Or.inr ⟨?_, hi5.2.2.2.1, syncFinal'_of_syncAt prims x s pads u rest noise top vlog a
    _ a5 (⟨src5, b.1.starts⟩, st5) (⟨rv.1.2, b.1.starts⟩, rv.2) hi5.1 hi5.2.2.2.2 hi5.2.2.2.1 ?_⟩)
  · change some _ = some _
    rw [funext hvals]
    rfl
  · unfold withReveal
    rw [hst, hsrc]

end Finish

end ThresholdLeanXmssSecurity.SigningCompilerO1Tail

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.merkleNode_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.merkleNode_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.merklePath_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.merklePath_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.sequenceFin_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.sequenceFin_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.runX_sequenceFin_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.runX_sequenceFin_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.compGood_withReveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.compGood_withReveal

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.revealDigests_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.revealDigests_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.realWorld_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.realWorld_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.relTriple_realStop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.relTriple_realStop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.relTriple_compStop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.relTriple_compStop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.tailInv_of_inPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.tailInv_of_inPost

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.opening_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.opening_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.chainStep_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.chainStep_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.chains_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.chains_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.syncFinal'_of_syncAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.syncFinal'_of_syncAt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.tailInv_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.tailInv_final

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Tail.tail_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Tail.tail_sync
