import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame

/-! # Round 1 of the O1 coupling

- `bindX` is the bind of round 1 on the compiler side, with the opening release after it.
- `round1X_eq` states that round 1 of the compiler is the guard, `bindX` and the part of the
  signer.
- `backendT_bindKey` states that the backend bind writes the bound map and nothing else.
- `bind_core` states that the bind on both sides keeps the core relation at the carried state with
  the new bound message. `bind_post` gives the other clauses after the bind and the release.
- `bind_sync` states that the bind keeps the relation inside the handler at the carried state with
  the new bound message, unless the compiler stops. A key with no bound message has no revealed
  opening, so the base inputs at the new message are not visible. A stored tree has each of its
  commitment terms virtual, so the release runs at a key of a stored tree.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Round1
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerSyncBackend
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

/-- The bind of round 1 on the compiler side, with the opening release after it. -/
def bindX (x : Keys3 C) (st : TsigState C) (e : KeyIndex) (message : Message) : SourceMX C Unit := do
  modify fun (s : SourceState C) => { s with signing :=
    { st with bound := Function.update st.bound e (some message) } }
  let _ ← liftM (deferredQueryX (C := C) (.bindKey e message))
  let backend ← liftM (deferredQueryX (C := C) .snapshot)
  if OpeningReady x.2.1 backend (← get).signing e then sourceReleaseOpeningX x.1 x.2.1 e

section Round1
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- Round 1 of the compiler is the guard, the bind and the part of the signer. -/
theorem round1X_eq (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex)
    (message : Message) :
    sourceTsigX prims x top (.round1 i J e message) = (do
      let st := (← get).signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ breaksOneMessagePerKey st e message then pure none else do
        bindX x st e message
        some <$> sourcePartX prims x i J (.randomizer bottomLayer e) message) := by
  simp only [sourceTsigX, bindX, bind_assoc]
  refine bind_congr fun src => ?_
  split
  · rfl
  · refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => bind_congr fun src' => ?_
    split <;> simp

/-- The compiler state after the backend bind. The bind is write-once. -/
def boundState (st : CompState C) (e : KeyIndex) (message : Message) : CompState C :=
  (((({ st.1.1.1.1 with bound := (if st.1.1.1.1.bound e = none then
      Function.update st.1.1.1.1.bound e (some message) else st.1.1.1.1.bound) },
    st.1.1.1.2), st.1.1.2), st.1.2), st.2)

/-- The backend bind writes the bound map and nothing else. -/
theorem backendT_bindKey (st : CompState C) (e : KeyIndex) (message : Message)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache) :
    (compBackend x q s pads u rest noise (.inl (.inl (.inl (.bindKey e message))))).run st =
      pure ((), boundState st e message) := by
  simp only [shareBackendTagT, backendRaw, ordinaryFullRaw, ordinaryRaw, StateT.run]
  rw [ordinary_uncounted x.1 x.2.1 q s pads (.bindKey e message)
    (by exact not_false) (by intro p; simp)]
  simp [compilerImpl, StateT.run, splitRest, merged, withCache, boundState,
    erase_merge_of_restFree _ _ _ hf]
  rfl

/-- The carried state of the real run with the new bound message. -/
abbrev bindView (a : RealState C) (e : KeyIndex) (message : Message) : Carried C :=
  (({ realSigning a with bound := Function.update (realSigning a).bound e (some message) },
    a.1.2.1.2), a.1.2.2)

/-- The clauses after the bind. The new source state has the new bound message and the old trees,
candidates, pending points and virtual terms. Its only new revealed key is the opening of `e`, and
that key is revealed when the tree of `e` is stored. -/
theorem bind_post (top : TopTree) (e : KeyIndex) (message : Message) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hx : ExtraO1 prims x top s b.1.base.revealed a b) (htop : TopO1 prims x top a b)
    (hbound : b.1.base.signing.bound = (realSigning a).bound)
    (hfree : breaksOneMessagePerKey (realSigning a) e message = false)
    (src : SourceState C) (st : CompState C)
    (hcore : SyncCore x s pads noise (gOf s pads u) rest (withCarried a (bindView a e message))
      (src, st))
    (hsig : src.signing.bound = Function.update (realSigning a).bound e (some message))
    (htrees : src.trees = b.1.base.trees) (hcand : src.candidates = b.1.base.candidates)
    (hrevOld : ∀ k, b.1.base.revealed k ≠ none → src.revealed k = b.1.base.revealed k)
    (hrevNew : ∀ k, b.1.base.revealed k = none → src.revealed k ≠ none →
      k = .opening bottomLayer e)
    (hpend : (dataOf x st).pending = (dataOf x b.2).pending)
    (hvirt : (dataOf x st).virtual = (dataOf x b.2).virtual)
    (htree : b.1.base.trees (treeOf e) ≠ none → src.revealed (.opening bottomLayer e) ≠ none)
    (hpads : PadsFixed x pads st) :
    SyncIn prims x s pads u rest noise top (bindView a e message) (bindView a e message) a
      (⟨src, b.1.starts⟩, st) := by
  have hsame : ∀ m, (realSigning a).bound e = some m → m = message := by
    intro m hm
    simpa [breaksOneMessagePerKey, hm] using hfree
  have hkeep : ∀ e', (realSigning a).bound e' ≠ none →
      Function.update (realSigning a).bound e (some message) e' = (realSigning a).bound e' := by
    intro e' he'
    by_cases hee : e' = e
    · subst hee
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp he'
      rw [Function.update_self, hm, hsame m hm]
    · exact Function.update_of_ne hee _ _
  have hnone : ∀ k, src.revealed k = none → b.1.base.revealed k = none := by
    intro k hk
    by_contra hne
    exact hne (by rw [← hrevOld k hne]; exact hk)
  have hunbound : (realSigning a).bound e = none →
      b.1.base.revealed (.opening bottomLayer e) = none := by
    intro hb
    by_contra hne
    rcases hx.revealedReleased bottomLayer e hne with ⟨_, h⟩ | ⟨h, _⟩
    · exact h hb
    · exact absurd h (by decide)
  have hgrow : ∀ k, b.1.base.revealed k ≠ none → src.revealed k ≠ none := by
    intro k hk
    rw [hrevOld k hk]
    exact hk
  refine ⟨hcore, ⟨?_, ?_, ?_⟩, ?_, hpads⟩
  · exact
      { treeRows := fun bi hbi k l d => by
          have hrows := hx.treeRows bi (htrees ▸ hbi) k l d
          exact ⟨fun T => hvirt ▸ hrows.1 T, hpend ▸ hrows.2⟩
        storedTrees := fun bi => by
          change (realSigning a).trees bi = _
          rw [htrees]
          exact hx.storedTrees bi
        storedTopDigit := fun bi tree ht => hx.storedTopDigit bi tree (htrees ▸ ht)
        startsTreed := fun e l h => by
          rw [htrees]
          exact hx.startsTreed e l h
        boundTreeRevealed := fun e' hb ht => by
          by_cases hee : e' = e
          · subst hee
            exact htree (htrees ▸ ht)
          · have hb' : b.1.base.signing.bound e' ≠ none := by
              change src.signing.bound e' ≠ none at hb
              rw [hsig, Function.update_of_ne hee] at hb
              rw [hbound]
              exact hb
            exact hgrow _ (hx.boundTreeRevealed e' hb' (htrees ▸ ht))
        revealedReleased := fun lay e' h => by
          by_cases hk : b.1.base.revealed (.opening lay e') = none
          · have he := hrevNew _ hk h
            injection he with hl he
            subst hl he
            refine Or.inl ⟨rfl, ?_⟩
            change Function.update (realSigning a).bound e' (some message) e' ≠ none
            rw [Function.update_self]
            exact Option.some_ne_none _
          · rcases hx.revealedReleased lay e' hk with ⟨hl, hb⟩ | h0
            · exact Or.inl ⟨hl, by
              change Function.update (realSigning a).bound e (some message) e' ≠ none
              rw [hkeep e' hb]; exact hb⟩
            · exact Or.inr h0
        revealedCovered := fun e' l p h => by
          by_cases hk : b.1.base.revealed (.bottomChain e' l p) = none
          · exact absurd (hrevNew _ hk h) (by simp)
          · obtain ⟨m, hm, ht, hd⟩ := hx.revealedCovered e' l p hk
            refine ⟨m, ?_, ht, hd⟩
            change Function.update (realSigning a).bound e (some message) e' = some m
            rw [hkeep e' (by rw [hm]; exact Option.some_ne_none _), hm]
        revealedTop := fun bi l p h => by
          by_cases hk : b.1.base.revealed (.topChain bi l p) = none
          · exact absurd (hrevNew _ hk h) (by simp)
          · rw [htrees]
            exact hx.revealedTop bi l p hk
        candidatesPaid := fun c hc hs => hgrow _ (hx.candidatesPaid c (hcand ▸ hc) hs)
        openingFresh := fun c hc => hx.openingFresh c (hcand ▸ hc)
        staleFree := hx.staleFree
        noEarlyGuess := fun e' message' hk => hx.noEarlyGuess e' message' (hnone _ hk)
        guessFree := fun p hk hp => hx.guessFree p (hnone _ hk) (hpend ▸ hp)
        treeTerms := fun bi hbi => by
          obtain ⟨h1, h2⟩ := hx.treeTerms bi (htrees ▸ hbi)
          exact ⟨fun k T => hvirt ▸ h1 k T, fun T => hvirt ▸ h2 T⟩
        treeStarts := fun bi tree ht T l => hvirt ▸ hx.treeStarts bi tree (htrees ▸ ht) T l
        treeValues := fun bi tree ht => hx.treeValues bi tree (htrees ▸ ht)
        baseTraced := fun e' m hb hv => by
          change Function.update (realSigning a).bound e (some message) e' = some m at hb
          by_cases hold : (realSigning a).bound e' = none
          · by_cases hee : e' = e
            · subst hee
              exact absurd (hx.noEarlyGuess e' _ (hunbound hold)) hv
            · rw [Function.update_of_ne hee] at hb
              rw [hold] at hb
              cases hb
          · rw [hkeep e' hold] at hb
            exact hx.baseTraced e' m hb hv
        logAgreement := hx.logAgreement
        storedRuns := hx.storedRuns
        startsTraced := fun e' l d hd => by
          obtain ⟨receipt, h1, h2, h3, h4⟩ := hx.startsTraced e' l d hd
          refine ⟨receipt, h1, ?_, h3, h4⟩
          change Function.update (realSigning a).bound e (some message) e' = _
          rw [hkeep e' (by rw [h2]; exact Option.some_ne_none _), h2]
        corruptBound := hx.corruptBound
        releasedBound := fun e' m i hm => by
          have h0 := hx.releasedBound e' m i hm
          change Function.update (realSigning a).bound e (some message) e' = _
          rw [hkeep e' (by rw [h0]; exact Option.some_ne_none _), h0]
        prfSeen := fun hfl => by cases hfl
        bottomSeen := fun hfl => by cases hfl }
  · exact hx.prfSeen
  · intro hfl T e' l d _ hv
    rcases hx.bottomSeen hfl T e' l d hv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr fun d' => hpend ▸ h1 d'
  · exact ⟨fun bi l d => hpend ▸ htop.topRows bi l d, htop.topRun⟩

/-- The source state after the bind. -/
abbrev boundSource (src : SourceState C) (e : KeyIndex) (message : Message) : SourceState C :=
  { src with signing := { src.signing with bound := Function.update src.signing.bound e (some message) } }

set_option backward.isDefEq.respectTransparency false in
/-- The bind on both sides keeps the core relation at the carried state with the new bound
message. -/
theorem bind_core (e : KeyIndex) (message : Message) (a : RealState C)
    (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest a (src, st))
    (hfree : breaksOneMessagePerKey (realSigning a) e message = false) :
    SyncCore x s pads noise (gOf s pads u) rest (withCarried a (bindView a e message))
      (boundSource src e message, boundState st e message) := by
  obtain ⟨⟨hsf, hc⟩, hcount⟩ := hs
  have hcb : (boundState st e message).1.1.1.1.bound = (boundSource src e message).signing.bound := by
    change (if st.1.1.1.1.bound e = none then Function.update st.1.1.1.1.bound e (some message)
      else st.1.1.1.1.bound) = Function.update src.signing.bound e (some message)
    rw [hsf.compilerBound]
    split
    · rfl
    · rename_i hne
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
      have hm' : (realSigning a).bound e = some m := hsf.bound ▸ hm
      have : m = message := by simpa [breaksOneMessagePerKey, hm'] using hfree
      subst this
      exact (Function.update_eq_self_iff.mpr hm.symm).symm
  have hbound : (boundSource src e message).signing.bound =
      (bindView a e message).1.1.bound := by
    change Function.update src.signing.bound e (some message) =
      Function.update (realSigning a).bound e (some message)
    rw [hsf.bound]
  exact ⟨⟨⟨hsf.corrupt, hbound, hsf.released, hsf.exposed, hsf.candidates, hsf.flag, hsf.reveal,
    hsf.releasedPending, ⟨hsf.opening.actualValue, hsf.opening.released⟩, hsf.pendingValid, hsf.allocated, hsf.virtualSeen, hcb,
    hsf.trace, hsf.bad, hsf.share, hsf.restAgree, hsf.restFree, hsf.realPrivate, hsf.frontier,
    hsf.candidatesPaid, hsf.doneCached⟩, hc⟩, hcount⟩

set_option backward.isDefEq.respectTransparency false in
/-- The bind of round 1. The real state does not move. The relation inside the handler holds at the
carried state with the new bound message. A bound key of a stored tree gets a revealed opening. -/
theorem bind_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (e : KeyIndex) (message : Message) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2)
    (hfree : breaksOneMessagePerKey (realSigning a) e message = false)
    (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (r : (Unit × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (bindX x b.1.base.signing e message) b.1.base b.2)) :
    Stop r.2 ∨
      (SyncIn prims x s pads u rest noise top
          (({ realSigning a with bound := Function.update (realSigning a).bound e (some message) },
            a.1.2.1.2), a.1.2.2)
          (({ realSigning a with bound := Function.update (realSigning a).bound e (some message) },
            a.1.2.1.2), a.1.2.2) a (⟨r.1.2, b.1.starts⟩, r.2) ∧
        r.2.1.2 = false) := by
  obtain ⟨⟨⟨hcore, hx⟩, htop⟩, hpads⟩ := hs
  have hsf := hcore.1.1
  have hcore1 := bind_core x s pads u rest noise e message a b.1.base b.2 hcore hfree
  simp only [bindX, runX_bind, runX_modify, pure_bind, runX_deferred, runX_get,
    backendT_bindKey x q s pads u rest noise b.2 e message hsf.restFree, map_pure,
    backendT_snapshot capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest
      (boundState b.2 e message) hsf.restFree] at hr
  have hpost := bind_post prims x s pads u rest noise top e message a b hx htop hsf.bound hfree
  have hsig : (boundSource b.1.base e message).signing.bound =
      Function.update (realSigning a).bound e (some message) := by
    change Function.update b.1.base.signing.bound e (some message) = _
    rw [hsf.bound]
  have htreeReady : b.1.base.trees (treeOf e) ≠ none →
      OpeningReady x.2.1 (dataOf x (boundState b.2 e message))
        (boundSource b.1.base e message).signing e := by
    intro ht
    refine ⟨by rw [hsig, Function.update_self]; exact Option.some_ne_none _, fun T => Or.inl ?_⟩
    have h0 := (hx.treeTerms (treeOf e) ht).1 ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩ T
    rw [bottomKey_treeOf] at h0
    exact h0
  by_cases hready : OpeningReady x.2.1 (dataOf x (boundState b.2 e message))
      (boundSource b.1.base e message).signing e
  · rw [if_pos hready] at hr
    by_cases hrev : b.1.base.revealed (.opening bottomLayer e) = none
    · have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
      have hready' : ReadyAfter x.2.1 (dataOf x (boundState b.2 e message))
          (boundSource b.1.base e message).signing e
          (.prf (x.2.1 (someTerm C)) (.randomizer bottomLayer e)) :=
        ⟨hready.1, fun T => (hready.2 T).elim Or.inl (fun h => Or.inr (Or.inl h))⟩
      have hvis : visibleOf a (.prf (x.2.1 (someTerm C)) (.randomizer bottomLayer e)) ≠ none := by
        rcases hready.2 (someTerm C) with h | h
        · exact hsf.virtualSeen _ _ h
        · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
          rw [hcore.1.2.cache_le hv]
          exact Option.some_ne_none _
      have hafter : VisibleAfter x (gOf s pads u) e
          (.prf (x.2.1 (someTerm C)) (.randomizer bottomLayer e)) (visibleOf a) (visibleOf a) :=
        Or.inr (Or.inl ⟨hvis, rfl⟩)
      have hrelease := releaseOpening_sync x hkeys q s pads (tauOf s pads) (gOf s pads u) noise
        rest e (x.2.1 (someTerm C)) (withCarried a (bindView a e message))
        (boundSource b.1.base e message) (boundState b.2 e message) (visibleOf a) hcore1.1.1
        hcore1.1.2 hmark hrev hready' hafter r hr
      rcases hrelease with hstop | ⟨hnext, hlocal, _, hcount, _⟩
      · exact Or.inl hstop
      have hrow := readyAfter_covers_visible x hkeys s pads noise (gOf s pads u) rest a.2
        (visibleOf a) (visibleOf a) (dataOf x (boundState b.2 e message))
        (boundSource b.1.base e message).signing e _ hcore1.1.1.realPrivate hcore1.1.2
        hcore1.1.1.virtualSeen hready' hafter
      have hrp := releaseOpening_post x hinj q s pads (tauOf s pads) (gOf s pads u) noise rest
        e _ (boundSource b.1.base e message) (boundState b.2 e message) (visibleOf a) (visibleOf a)
        hmark hrev hcore1.1.1.reveal hcore1.1.2 hcore1.1.1.releasedPending
        hcore1.1.1.pendingValid hcore1.1.1.allocated hcore1.1.1.restFree hcore1.1.1.share
        hcore1.1.1.doneCached hcore1.1.1.bad hafter hrow r hr
      have hrevEq : r.1.2.revealed = Function.update b.1.base.revealed (.opening bottomLayer e)
          (some (s (.opening bottomLayer e))) := congrArg SourceState.revealed hrp.source
      refine Or.inr ⟨hpost r.1.2 r.2 ⟨hnext, hcore1.2.trans hcount.symm⟩
        (by rw [hlocal.signing]; exact hsig) hlocal.trees
        (by have h := congrArg SourceState.candidates hrp.source; exact h) ?_ ?_ hlocal.pending hlocal.virtual ?_
        (backend_padsFixed x q s pads u rest noise
          ((sourceReleaseOpeningX x.1 x.2.1 e).run (boundSource b.1.base e message))
          (boundState b.2 e message) hpads r hr), ?_⟩
      · intro k hk
        rw [hrevEq]
        apply Function.update_of_ne
        rintro rfl
        exact hk hrev
      · intro k hk h
        by_contra hne
        rw [hrevEq, Function.update_of_ne hne] at h
        exact h hk
      · intro _
        rw [hrevEq, Function.update_self]
        exact Option.some_ne_none _
      · rw [hrp.backend]
        exact hmark
    · rw [runX_releaseOpening_revealed _ x.1 x.2.1 e (boundSource b.1.base e message)
        (boundState b.2 e message) hrev, mem_support_pure_iff] at hr
      subst r
      exact Or.inr ⟨hpost _ _ hcore1 hsig rfl rfl (fun _ _ => rfl) (fun _ hk h => absurd hk h)
        rfl rfl (fun _ => hrev) hpads, hmark⟩
  · rw [if_neg hready, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact Or.inr ⟨hpost _ _ hcore1 hsig rfl rfl (fun _ _ => rfl) (fun _ hk h => absurd hk h)
      rfl rfl (fun ht => absurd (htreeReady ht) hready) hpads, hmark⟩

end Round1

end ThresholdLeanXmssSecurity.SigningCompilerO1Round1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round1.round1X_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round1.round1X_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round1.backendT_bindKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round1.backendT_bindKey

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round1.bind_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round1.bind_post

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round1.bind_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round1.bind_core

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Round1.bind_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Round1.bind_sync
