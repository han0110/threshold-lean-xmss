import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Programs

/-! # One chain of the honest signature tail

- `tailChain_sync` couples one chain of the honest signature below digit 3. The compiler releases
  the suffix of the chain, and both sides read the PRF value. The reveal map of the timing clauses
  stays.
- `extraOpen_suffix` states that a suffix release keeps `ExtraOpen` at a fixed reveal map of the
  timing clauses.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1TailChain
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerSyncSuffix
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Programs
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

section Finish
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A suffix release keeps `ExtraOpen` at a fixed reveal map of the timing clauses. -/
theorem extraOpen_suffix (top : TopTree) (rev : HiddenKey → Option Digest)
    (openRow : KeyIndex → ChainIndex → Prop) (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (a : RealState C) (b : SourceStateO1 C × CompState C) (src' : SourceState C) (st' : CompState C)
    (hx : ExtraOpen prims x top s rev openRow a b)
    (hfr : SuffixFrame x s e l start (b.1.base, b.2) (src', st')) :
    ExtraOpen prims x top s rev openRow a (⟨src', b.1.starts⟩, st') := by
  have hx0 := hx.rest
  have hsigning : src'.signing = b.1.base.signing := hfr.signing
  have htrees : src'.trees = b.1.base.trees := hfr.trees
  have hcand : src'.candidates = b.1.base.candidates := hfr.candidates
  have hpend : (dataOf x st').pending = (dataOf x b.2).pending := hfr.pending
  have hvirt : (dataOf x st').virtual = (dataOf x b.2).virtual := hfr.virtual
  have hrev : ∀ k, (∀ d : XmssSecurity.ChainStep, start.val ≤ d.val → k ≠ .bottomChain e l d) →
      src'.revealed k = b.1.base.revealed k := hfr.revealed
  refine ⟨
    { treeRows := fun bi hbi k l' d => by
        change src'.trees bi ≠ none at hbi
        rw [htrees] at hbi
        obtain ⟨h1, h2⟩ := hx0.treeRows bi hbi k l' d
        refine ⟨fun T => ?_, ?_⟩
        · show _ ∈ (dataOf x st').virtual
          rw [hvirt]; exact h1 T
        · show (dataOf x st').pending _ ≠ none
          rw [hpend]; exact h2
      storedTrees := fun bi => by
        show _ = (src'.trees bi).map _
        rw [htrees]; exact hx0.storedTrees bi
      storedTopDigit := fun bi tree h => by
        change src'.trees bi = _ at h
        rw [htrees] at h; exact hx0.storedTopDigit bi tree h
      startsTreed := fun e' l' h => by
        show ∃ tree, src'.trees (treeOf e') = some (some tree)
        rw [htrees]; exact hx0.startsTreed e' l' h
      boundTreeRevealed := fun e' h1 h2 => by
        change src'.signing.bound e' ≠ none at h1
        change src'.trees (treeOf e') ≠ none at h2
        rw [hsigning] at h1
        rw [htrees] at h2
        show src'.revealed _ ≠ none
        rw [hrev _ (fun d _ h => by cases h)]
        exact hx0.boundTreeRevealed e' h1 h2
      revealedReleased := hx0.revealedReleased
      revealedCovered := hx0.revealedCovered
      revealedTop := fun bi l' p h => by
        obtain ⟨hbi, tree, ht, hle⟩ := hx0.revealedTop bi l' p h
        refine ⟨hbi, tree, ?_, hle⟩
        show src'.trees bi = _
        rw [htrees]; exact ht
      candidatesPaid := fun c hc => by
        change c ∈ src'.candidates at hc
        rw [hcand] at hc
        exact hx0.candidatesPaid c hc
      openingFresh := fun c hc => by
        change c ∈ src'.candidates at hc
        rw [hcand] at hc
        exact hx0.openingFresh c hc
      staleFree := hx0.staleFree
      noEarlyGuess := fun e' message h => by
        change src'.revealed _ = none at h
        rw [hrev _ (fun d _ h => by cases h)] at h
        exact hx0.noEarlyGuess e' message h
      guessFree := fun p h1 h2 => by
        change src'.revealed p.key = none at h1
        change (dataOf x st').pending p = none at h2
        rw [hpend] at h2
        have hkey : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
            p.key ≠ .bottomChain e l d := by
          intro d hd hk
          have hsuf : src'.revealed (.bottomChain e l d) = some (s (.bottomChain e l d)) :=
            hfr.suffix d hd
          rw [hk, hsuf] at h1
          cases h1
        rw [hrev _ hkey] at h1
        exact hx0.guessFree p h1 h2
      treeTerms := fun bi h => by
        change src'.trees bi ≠ none at h
        rw [htrees] at h
        show (∀ k T, _ ∈ (dataOf x st').virtual) ∧ ∀ T, _ ∈ (dataOf x st').virtual
        rw [hvirt]
        exact hx0.treeTerms bi h
      treeStarts := fun bi tree h T l' => by
        change src'.trees bi = _ at h
        rw [htrees] at h
        show _ ∈ (dataOf x st').virtual
        rw [hvirt]
        exact hx0.treeStarts bi tree h T l'
      treeValues := fun bi tree h => by
        change src'.trees bi = _ at h
        rw [htrees] at h
        exact hx0.treeValues bi tree h
      baseTraced := hx0.baseTraced
      logAgreement := hx0.logAgreement
      storedRuns := hx0.storedRuns
      startsTraced := hx0.startsTraced
      corruptBound := hx0.corruptBound
      releasedBound := hx0.releasedBound
      prfSeen := hx0.prfSeen
      bottomSeen := fun hfl T e' l' d hv => (hx0.bottomSeen hfl T e' l' d hv).imp_right
        fun h d' => by show (dataOf x st').pending _ ≠ none; rw [hpend]; exact h d' },
    hx.prfSeen, fun hfl T e' l' d hno hv => (hx.bottomSeen hfl T e' l' d hno hv).imp_right
      fun h d' => by show (dataOf x st').pending _ ≠ none; rw [hpend]; exact h d'⟩

/-- One chain of the honest signature below digit 3. The compiler releases the suffix of the chain
and both sides read the PRF value. The reveal map of the timing clauses stays. -/
theorem tailChain_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (rev : HiddenKey → Option Digest) (c : Carried C) (e : KeyIndex) (l : ChainIndex) (d : Digit)
    (hd : d.val < 3) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncAt prims x s pads u rest noise top rev (fun _ _ => False) c c a b)
    (hrows : ∀ d' : XmssSecurity.ChainStep,
      (∀ T, (T, Point.chain bottomLayer e l (chainStepDigit d')) ∈ (dataOf x b.2).virtual) ∧
        (dataOf x b.2).pending (.bottom e l d') ≠ none)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (prfValue x.2.1 (.chain bottomLayer e l d))).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise) (do
      sourceReleaseBottomSuffixX x.1 x.2.1 e l d
      sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.chain bottomLayer e l d))) b.1.base b.2)) :
    InPost prims x q s pads u rest noise top c c a b (fun _ => rev)
      (fun va vb => va = vb ∧ ∀ k, b.1.base.revealed k ≠ none → rb.1.2.revealed k ≠ none) ra rb := by
  obtain ⟨hcore, hx, htop, hpads⟩ := hs
  obtain ⟨rb1, hb1, hrb2⟩ := runX_bind_support x q s pads u rest noise _ _ b.1.base b.2 rb hrb
  rcases releaseSuffix_sync x hkeys q s pads (tauOf s pads) (gOf s pads u) noise rest e l d
      (withCarried a c) b.1.base b.2 hcore hmark (fun d' _ => hrows d') rb1 hb1 with
    hstop | ⟨hcore1, hfr⟩
  · exact Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 hstop rb hrb2))
  have hm1 : rb1.2.1.2 = false := hfr.mark.trans hmark
  by_cases hb1' : Stop rb1.2
  · exact Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 hb1' rb hrb2))
  have hP := prfValue_sync prims x q s pads u rest noise hkeys c
    ⟨.chain bottomLayer e l d, Or.inl ⟨rfl, hd⟩⟩ a rb1.1.2 rb1.2 hcore1 ha hb1' hm1 ra
    (by with_reducible exact hra) rb hrb2
  rcases hP with h | h | ⟨⟨hv, -⟩, hcore2, hf, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hx1 := extraOpen_suffix prims x s top rev (fun _ _ => False) e l d (withCarried a c) b
    rb1.1.2 rb1.2 hx hfr
  have hpads1 : PadsFixed x pads rb1.2 :=
    backend_padsFixed x q s pads u rest noise _ b.2 hpads rb1 hb1
  have hpads2 : PadsFixed x pads rb.2 :=
    backend_padsFixed x q s pads u rest noise _ rb1.2 hpads1 rb hrb2
  have hpend1 : (dataOf x rb1.2).pending = (dataOf x b.2).pending := hfr.pending
  have htop1 : TopO1 prims x top a (⟨rb1.1.2, b.1.starts⟩, rb1.2) :=
    ⟨fun bi l' d' => by
      show (dataOf x rb1.2).pending _ ≠ none
      rw [hpend1]; exact htop.topRows bi l' d', htop.topRun⟩
  have hx2 := ExtraOpen.frame prims x top s _ (fun _ _ => False) (fun _ _ => False) rev rev c a ra.2
    (⟨rb1.1.2, b.1.starts⟩, rb1.2) (⟨rb.1.2, b.1.starts⟩, rb.2) hx1 hf rfl (fun _ h => h)
    (fun _ h => Or.inl h)
    (fun _ _ _ hseen => by obtain ⟨T, hT⟩ := hseen; cases hT)
    (fun _ _ _ hseen => by obtain ⟨T, hT⟩ := hseen; cases hT)
    (fun T p hseen => by
      obtain ⟨T', hT⟩ := hseen
      injection hT with _ hT
      subst hT
      exact Or.inr (Or.inl ⟨rfl, hd⟩))
    (fun T e' l' d' hseen => by
      obtain ⟨T', hT⟩ := hseen
      injection hT with _ hT
      injection hT with _ he hl _
      subst he hl
      refine Or.inr (Or.inr fun d'' => hf.pending _ ?_)
      show (dataOf x rb1.2).pending _ ≠ none
      rw [hpend1]; exact (hrows d'').2)
    (fun _ _ h => h)
  refine Or.inr (Or.inr ⟨⟨hv, fun k hk => ?_⟩,
    ⟨hcore2, hx2, TopO1.frame prims x top _ a ra.2 _ (⟨rb.1.2, b.1.starts⟩, rb.2) htop1 hf, hpads2⟩,
    hf.signing.trans hfr.signing, hf.trees.trans hfr.trees, hf.exposed.trans hfr.exposed,
    hf.candidates.trans hfr.candidates, hm2, hf.carried, hf.log⟩)
  have h1 : rb1.1.2.revealed k ≠ none := by
    by_cases hkey : ∃ d' : XmssSecurity.ChainStep, d.val ≤ d'.val ∧ k = .bottomChain e l d'
    · obtain ⟨d', hd', rfl⟩ := hkey
      rw [hfr.suffix d' hd']
      exact Option.some_ne_none _
    · rw [hfr.revealed k (fun d' hd' hk' => hkey ⟨d', hd', hk'⟩)]
      exact hk
  rw [hf.revealed k h1]
  exact h1

end Finish

end ThresholdLeanXmssSecurity.SigningCompilerO1TailChain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TailChain.extraOpen_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TailChain.extraOpen_suffix

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TailChain.tailChain_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TailChain.tailChain_sync
