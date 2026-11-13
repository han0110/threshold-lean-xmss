import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Sync

/-! # The chain release inside a signing handler

`syncMid_widen` states that the timing state of `SyncMid` can grow. `recordStart_mid` states that a
recorded digit keeps `SyncMid`. `releaseCovered_mid` and `releaseKey_mid` state that the release of
a covered chain, and of every chain of a key, keeps `SyncMid` or stops the compiler side.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerSyncSuffix SigningCompilerO1Sync
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Inner
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The timing state of the relation inside a handler can grow. The bound map, the corrupt set and
the stored trees stay, and each signer set grows. -/
theorem syncMid_widen (top : TopTree) (sigCore sigTime sigTime' : TsigState C)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b)
    (hbound : sigTime'.bound = sigTime.bound) (hcorrupt : sigTime'.corrupt = sigTime.corrupt)
    (htrees : sigTime'.trees = sigTime.trees)
    (hsigners : ∀ e m, signersAt sigTime e m ⊆ signersAt sigTime' e m)
    (hrel : SigningGuessProof.ReleasedBound sigTime') :
    SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime' a b := by
  obtain ⟨hcore, hx, htop⟩ := hs
  refine ⟨hcore, ?_, htop⟩
  obtain ⟨c1, b1, r1, t1⟩ := sigTime
  obtain ⟨c2, b2, r2, t2⟩ := sigTime'
  cases hbound
  cases hcorrupt
  cases htrees
  exact
    { treeRows := hx.treeRows
      storedTrees := hx.storedTrees
      storedTopDigit := hx.storedTopDigit
      startsTreed := hx.startsTreed
      boundTreeRevealed := hx.boundTreeRevealed
      revealedReleased := hx.revealedReleased
      revealedCovered := fun e l p h => by
        obtain ⟨m, hm, hc, hd⟩ := hx.revealedCovered e l p h
        exact ⟨m, hm, hc.trans (Finset.card_le_card (hsigners e m)), hd⟩
      revealedTop := hx.revealedTop
      candidatesPaid := hx.candidatesPaid
      openingFresh := hx.openingFresh
      staleFree := hx.staleFree
      noEarlyGuess := hx.noEarlyGuess
      guessFree := hx.guessFree
      treeTerms := hx.treeTerms
      treeStarts := hx.treeStarts
      treeValues := hx.treeValues
      baseTraced := hx.baseTraced
      logAgreement := hx.logAgreement
      storedRuns := hx.storedRuns
      startsTraced := hx.startsTraced
      corruptBound := hx.corruptBound
      releasedBound := hrel
      prfSeen := hx.prfSeen
      bottomSeen := hx.bottomSeen }

/-- A digit set after `recordStartX` holds a digit when the digit is the new one or was there. -/
theorem mem_recordStart (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex)
    (l : ChainIndex) (d : Digit) (e' : KeyIndex) (l' : ChainIndex) (d' : Digit) :
    d' ∈ Function.update starts e (Function.update (starts e) l (insert d (starts e l))) e' l' ↔
      (e' = e ∧ l' = l ∧ d' = d) ∨ d' ∈ starts e' l' := by
  by_cases he : e' = e
  · subst he
    by_cases hl : l' = l
    · subst hl
      simp
    · simp [hl]
  · simp [he]

/-- A recorded digit keeps the relation inside the handler. It needs the stored tree and the
codeword search of the digit. -/
theorem recordStart_mid (top : TopTree) (sigCore sigTime : TsigState C) (e : KeyIndex)
    (l : ChainIndex) (d : Digit) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b)
    (htree : ∃ tree, b.1.base.trees (treeOf e) = some (some tree))
    (hrec : ∃ receipt : SigningGuessProof.Round2Receipt C, receipt.key = e ∧
      sigTime.bound e = some receipt.message ∧ receipt.encoding l = d ∧
      SigningGuessProof.ReceiptRuns prims x top (realLog a) receipt) :
    SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a
      (⟨b.1.base, Function.update b.1.starts e
          (Function.update (b.1.starts e) l (insert d (b.1.starts e l)))⟩, b.2) := by
  obtain ⟨hcore, hx, htop⟩ := hs
  refine ⟨hcore, ?_, ⟨htop.topRows, htop.topRun⟩⟩
  exact
    { treeRows := hx.treeRows
      storedTrees := hx.storedTrees
      storedTopDigit := hx.storedTopDigit
      startsTreed := fun e' l' hne => by
        obtain ⟨d', hd'⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        rcases (mem_recordStart b.1.starts e l d e' l' d').mp hd' with ⟨rfl, rfl, rfl⟩ | hold
        · exact htree
        · exact hx.startsTreed e' l' (Finset.ne_empty_of_mem hold)
      boundTreeRevealed := hx.boundTreeRevealed
      revealedReleased := hx.revealedReleased
      revealedCovered := fun e' l' p h => by
        obtain ⟨m, hm, hc, d', hd', hle⟩ := hx.revealedCovered e' l' p h
        exact ⟨m, hm, hc, d', (mem_recordStart b.1.starts e l d e' l' d').mpr (Or.inr hd'), hle⟩
      revealedTop := hx.revealedTop
      candidatesPaid := hx.candidatesPaid
      openingFresh := hx.openingFresh
      staleFree := hx.staleFree
      noEarlyGuess := hx.noEarlyGuess
      guessFree := hx.guessFree
      treeTerms := hx.treeTerms
      treeStarts := hx.treeStarts
      treeValues := hx.treeValues
      baseTraced := hx.baseTraced
      logAgreement := hx.logAgreement
      storedRuns := hx.storedRuns
      startsTraced := fun e' l' d' hd' => by
        rcases (mem_recordStart b.1.starts e l d e' l' d').mp hd' with ⟨rfl, rfl, rfl⟩ | hold
        · exact hrec
        · exact hx.startsTraced e' l' d' hold
      corruptBound := hx.corruptBound
      releasedBound := hx.releasedBound
      prfSeen := hx.prfSeen
      bottomSeen := hx.bottomSeen }

/-- A stop of the compiler side stays through an O1 source run. -/
theorem runXO1_stop {α : Type} (oa : SourceMXO1 C α) (src : SourceStateO1 C) (st : CompState C)
    (h : Stop st) (r : (α × SourceStateO1 C) × CompState C)
    (hr : r ∈ support (runXO1 (compBackend x q s pads u rest noise) oa src st)) : Stop r.2 :=
  simulateQ_sticky _ Stop (backendT_stop x.1 x.2.1 x.2.2 q s pads (tauOf s pads) (gOf s pads u) noise rest)
    (oa.run src) st h r hr

/-- An O1 source run of a bind is the run of the first step and then the run of the rest. -/
theorem runXO1_bind {Tag α β : Type}
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (oa : SourceMXO1 C α) (next : α → SourceMXO1 C β) (src : SourceStateO1 C) (st : FullState C Tag) :
    runXO1 backend (oa >>= next) src st = runXO1 backend oa src st >>= fun r =>
      runXO1 backend (next r.1.1) r.1.2 r.2 := by
  simp only [runXO1, StateT.run_bind, simulateQ_bind]

/-- An O1 source run of `pure` returns its value and keeps both states. -/
theorem runXO1_pure {Tag α : Type}
    (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (v : α) (src : SourceStateO1 C) (st : FullState C Tag) :
    runXO1 backend (pure v) src st = pure ((v, src), st) := by
  simp [runXO1, StateT.run_pure]

/-- An O1 source run of `get` returns the source state. -/
theorem runXO1_get {Tag : Type} (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (src : SourceStateO1 C) (st : FullState C Tag) :
    runXO1 backend get src st = pure ((src, src), st) := by
  simp [runXO1, StateT.run_get]

/-- An O1 source run of `modify` changes only the source state. -/
theorem runXO1_modify {Tag : Type} (backend : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (f : SourceStateO1 C → SourceStateO1 C) (src : SourceStateO1 C) (st : FullState C Tag) :
    runXO1 backend (modify f) src st = pure (((), f src), st) := by
  simp [runXO1, StateT.run_modify]

/-- The release of a covered chain at a key with `t` signers at the return state. The real state
does not move. -/
theorem releaseCovered_mid (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sigCore sigTime : TsigState C) (e : KeyIndex) (l : ChainIndex)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b)
    (hmark : b.2.1.2 = false)
    (hcov : ∃ m, sigTime.bound e = some m ∧ C.t ≤ (signersAt sigTime e m).card)
    (r : (Unit × SourceStateO1 C) × CompState C)
    (hr : r ∈ support (runXO1 (compBackend x q s pads u rest noise)
      (sourceReleaseCoveredX x.1 x.2.1 e l) b.1 b.2)) :
    Stop r.2 ∨ (SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a (r.1.2, r.2) ∧
      r.1.2.starts = b.1.starts ∧ r.1.2.base.signing = b.1.base.signing ∧
      r.1.2.base.trees = b.1.base.trees ∧ r.2.1.2 = false) := by
  obtain ⟨hcore, hx, htop⟩ := hs
  cases hf : firstStart (b.1.starts e l) with
  | none =>
    have hrun : runXO1 (compBackend x q s pads u rest noise) (sourceReleaseCoveredX x.1 x.2.1 e l)
        b.1 b.2 = pure (((), b.1), b.2) := by
      simp [runXO1, sourceReleaseCoveredX, hf, StateT.run_bind]
    rw [hrun, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Or.inr ⟨⟨hcore, hx, htop⟩, rfl, rfl, rfl, hmark⟩
  | some start =>
    have hrun : runXO1 (compBackend x q s pads u rest noise) (sourceReleaseCoveredX x.1 x.2.1 e l)
        b.1 b.2 = runXO1 (compBackend x q s pads u rest noise)
          (liftBaseX (sourceReleaseBottomSuffixX x.1 x.2.1 e l start)) b.1 b.2 := by
      simp [runXO1, sourceReleaseCoveredX, hf, StateT.run_bind]
    rw [hrun, runXO1_liftBaseX, support_map] at hr
    obtain ⟨⟨⟨_, src'⟩, st'⟩, hr0, rfl⟩ := hr
    obtain ⟨hstart, -⟩ := firstStart_spec _ _ hf
    obtain ⟨tree, htree⟩ := hx.startsTreed e l (Finset.ne_empty_of_mem hstart)
    have hrowsTree := hx.treeRows (treeOf e) (by rw [htree]; exact Option.some_ne_none _)
    have hrows : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val →
        (∀ T, (T, .chain bottomLayer e l (chainStepDigit d)) ∈ (dataOf x b.2).virtual) ∧
        (dataOf x b.2).pending (.bottom e l d) ≠ none := by
      intro d _
      have h := hrowsTree ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ l d
      rwa [bottomKey_treeOf] at h
    rcases releaseSuffix_sync x hkeys q s pads (tauOf s pads) (gOf s pads u) noise rest e l start
        (withSigning a sigCore) b.1.base b.2 hcore hmark hrows _ hr0 with hstop | ⟨hcore', hfr⟩
    · exact Or.inl hstop
    have hsigning : src'.signing = b.1.base.signing := hfr.signing
    have htrees : src'.trees = b.1.base.trees := hfr.trees
    have hcand : src'.candidates = b.1.base.candidates := hfr.candidates
    have hpend : (dataOf x st').pending = (dataOf x b.2).pending := hfr.pending
    have hvirt : (dataOf x st').virtual = (dataOf x b.2).virtual := hfr.virtual
    have hrev : ∀ k, (∀ d : XmssSecurity.ChainStep, start.val ≤ d.val → k ≠ .bottomChain e l d) →
        src'.revealed k = b.1.base.revealed k := hfr.revealed
    have hextra : ExtraO1 prims x top s src'.revealed (withSigning a sigTime)
        (⟨src', b.1.starts⟩, st') :=
      { treeRows := fun bi hbi k l' d => by
          rw [htrees] at hbi
          obtain ⟨h1, h2⟩ := hx.treeRows bi hbi k l' d
          refine ⟨fun T => ?_, ?_⟩
          · rw [hvirt]; exact h1 T
          · rw [hpend]; exact h2
        storedTrees := fun bi => by
          show _ = (src'.trees bi).map _
          rw [htrees]; exact hx.storedTrees bi
        storedTopDigit := fun bi tree h => by
          rw [htrees] at h; exact hx.storedTopDigit bi tree h
        startsTreed := fun e' l' h => by
          show ∃ tree, src'.trees (treeOf e') = some (some tree)
          rw [htrees]; exact hx.startsTreed e' l' h
        boundTreeRevealed := fun e' h1 h2 => by
          change src'.signing.bound e' ≠ none at h1
          change src'.trees (treeOf e') ≠ none at h2
          rw [hsigning] at h1
          rw [htrees] at h2
          show src'.revealed _ ≠ none
          rw [hrev _ (fun d _ h => by cases h)]
          exact hx.boundTreeRevealed e' h1 h2
        revealedReleased := fun lay e' h => by
          rw [hrev _ (fun d _ h => by cases h)] at h
          exact hx.revealedReleased lay e' h
        revealedCovered := fun e' l' p h => by
          by_cases hk : e' = e ∧ l' = l ∧ start.val ≤ p.val
          · obtain ⟨rfl, rfl, hp⟩ := hk
            obtain ⟨m, hm, hc⟩ := hcov
            exact ⟨m, hm, hc, start, hstart, hp⟩
          · rw [hrev _ (fun d hd h => by cases h; exact hk ⟨rfl, rfl, hd⟩)] at h
            exact hx.revealedCovered e' l' p h
        revealedTop := fun bi l' p h => by
          rw [hrev _ (fun d _ h => by cases h)] at h
          obtain ⟨hbi, tree, ht, hle⟩ := hx.revealedTop bi l' p h
          refine ⟨hbi, tree, ?_, hle⟩
          show src'.trees bi = _
          rw [htrees]; exact ht
        candidatesPaid := hcore'.1.1.candidatesPaid
        openingFresh := fun c hc => by
          change c ∈ src'.candidates at hc
          rw [hcand] at hc
          exact hx.openingFresh c hc
        staleFree := hx.staleFree
        noEarlyGuess := fun e' message h => by
          change src'.revealed _ = none at h
          rw [hrev _ (fun d _ h => by cases h)] at h
          exact hx.noEarlyGuess e' message h
        guessFree := fun p h1 h2 => by
          change src'.revealed p.key = none at h1
          change (dataOf x st').pending p = none at h2
          rw [hpend] at h2
          have hkey : ∀ d : XmssSecurity.ChainStep, start.val ≤ d.val → p.key ≠ .bottomChain e l d := by
            intro d hd hk
            have hsuf : src'.revealed (.bottomChain e l d) = some (s (.bottomChain e l d)) :=
              hfr.suffix d hd
            rw [hk, hsuf] at h1
            cases h1
          rw [hrev _ hkey] at h1
          exact hx.guessFree p h1 h2
        treeTerms := fun bi h => by
          change src'.trees bi ≠ none at h
          rw [htrees] at h
          rw [hvirt]
          exact hx.treeTerms bi h
        treeStarts := fun bi tree h T l' => by
          change src'.trees bi = _ at h
          rw [htrees] at h
          rw [hvirt]
          exact hx.treeStarts bi tree h T l'
        treeValues := fun bi tree h => by
          change src'.trees bi = _ at h
          rw [htrees] at h
          exact hx.treeValues bi tree h
        baseTraced := hx.baseTraced
        logAgreement := hx.logAgreement
        storedRuns := hx.storedRuns
        startsTraced := hx.startsTraced
        corruptBound := hx.corruptBound
        releasedBound := hx.releasedBound
        prfSeen := hx.prfSeen
        bottomSeen := fun hfl T e' l' d hv => (hx.bottomSeen hfl T e' l' d hv).imp_right
          fun h d' => by rw [hpend]; exact h d' }
    refine Or.inr ⟨⟨hcore', hextra, fun bi l' d => ?_, htop.topRun⟩, rfl, hsigning, htrees,
      hfr.mark.trans hmark⟩
    show (dataOf x st').pending _ ≠ none
    rw [hpend]; exact htop.topRows bi l' d

/-- The release of the chains of a list at one key. -/
theorem releaseChains_mid (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sigCore sigTime : TsigState C) (e : KeyIndex) (a : RealState C)
    (hcov : ∃ m, sigTime.bound e = some m ∧ C.t ≤ (signersAt sigTime e m).card) :
    ∀ (chains : List ChainIndex) (b : SourceStateO1 C × CompState C),
      SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b → b.2.1.2 = false →
      ∀ r ∈ support (runXO1 (compBackend x q s pads u rest noise)
        (chains.mapM fun l => sourceReleaseCoveredX x.1 x.2.1 e l) b.1 b.2),
      Stop r.2 ∨ (SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a (r.1.2, r.2) ∧
        r.1.2.starts = b.1.starts ∧ r.1.2.base.signing = b.1.base.signing ∧
        r.1.2.base.trees = b.1.base.trees ∧ r.2.1.2 = false) := by
  intro chains
  induction chains with
  | nil =>
    intro b hs hmark r hr
    rw [List.mapM_nil, runXO1_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Or.inr ⟨hs, rfl, rfl, rfl, hmark⟩
  | cons l chains ih =>
    intro b hs hmark r hr
    rw [List.mapM_cons, runXO1_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    rw [runXO1_bind, mem_support_bind_iff] at hr
    obtain ⟨next, hnext, hr⟩ := hr
    rw [runXO1_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rcases releaseCovered_mid prims x q s pads u rest noise hkeys top sigCore sigTime e l a b hs hmark
        hcov mid hmid with hstop | ⟨hs', hst, hsg, htr, hm⟩
    · exact Or.inl (runXO1_stop x q s pads u rest noise _ mid.1.2 mid.2 hstop next hnext)
    rcases ih (mid.1.2, mid.2) hs' hm next hnext with hstop | ⟨hs'', hst', hsg', htr', hm'⟩
    · exact Or.inl hstop
    · exact Or.inr ⟨hs'', hst'.trans hst, hsg'.trans hsg, htr'.trans htr, hm'⟩

/-- The release of every chain of a key. -/
theorem releaseKey_mid (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sigCore sigTime : TsigState C) (e : KeyIndex)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b)
    (hmark : b.2.1.2 = false)
    (hcov : ∃ m, sigTime.bound e = some m ∧ C.t ≤ (signersAt sigTime e m).card)
    (r : (Unit × SourceStateO1 C) × CompState C)
    (hr : r ∈ support (runXO1 (compBackend x q s pads u rest noise)
      (sourceReleaseKeyX x.1 x.2.1 e) b.1 b.2)) :
    Stop r.2 ∨ (SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a (r.1.2, r.2) ∧
      r.1.2.starts = b.1.starts ∧ r.1.2.base.signing = b.1.base.signing ∧
      r.1.2.base.trees = b.1.base.trees ∧ r.2.1.2 = false) := by
  rw [sourceReleaseKeyX, runXO1_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hmid, hr⟩ := hr
  rw [runXO1_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact releaseChains_mid prims x q s pads u rest noise hkeys top sigCore sigTime e a hcov
    (List.finRange numChains) b hs hmark mid hmid

end Inner

end ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.syncMid_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.syncMid_widen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.mem_recordStart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.mem_recordStart

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.recordStart_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.recordStart_mid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_modify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.runXO1_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.releaseCovered_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.releaseCovered_mid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.releaseChains_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.releaseChains_mid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.releaseKey_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1ChainRelease.releaseKey_mid
