import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Build

/-! # The tree step of a signing handler of the O1 coupling

- `bottomOnce_run_some` and `bottomOnce_run_none` write the real tree step as a stored result or as
  the build and the store.
- `sourceBottomOnceX_some` and `sourceBottomOnceX_none` do the same for the compiler tree step.
- `update_top_ne` and `update_top_self` read the compiler store of trees at a tree index.
- `syncIn_store` states that the store of a built tree keeps the relation inside a handler. The
  clauses of the new tree come from `BuildFacts`.
- `bottomOnce_sync` couples the tree step of both sides. A stored result returns, and a first
  request builds the tree with `bottomTree_sync` and stores the result.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Build
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

section Build
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A stored real tree returns with no call. -/
theorem bottomOnce_run_some (top : TopTree) (sig : TsigState C) (bi : Fin (2 ^ layerHeight))
    (a : RealState C) (tree : Option BottomTree) (h : sig.trees bi = some tree) :
    (simulateQ (realWorld prims x s pads u rest)
      ((bottomOnce (SigningJointEagerProof.dealtOf x top) bi).run sig)).run a =
        pure ((tree, sig), a) := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind, h, StateT.run_pure, simulateQ_pure]

/-- A first real request builds the tree and stores the result. -/
theorem bottomOnce_run_none (top : TopTree) (sig : TsigState C) (bi : Fin (2 ^ layerHeight))
    (a : RealState C) (h : sig.trees bi = none) :
    (simulateQ (realWorld prims x s pads u rest)
      ((bottomOnce (SigningJointEagerProof.dealtOf x top) bi).run sig)).run a =
        (fun r => ((r.1, { sig with trees := Function.update sig.trees bi (some r.1) }), r.2)) <$>
          (simulateQ (realWorld prims x s pads u rest)
            ((SigningJointEagerProof.dealtOf x top).bottom bi)).run a := by
  simp [bottomOnce, h, map_eq_bind_pure_comp]

/-- A stored compiler tree returns with no call. -/
theorem sourceBottomOnceX_some (top : TopTree) (bi : Fin (2 ^ layerHeight)) (src : SourceState C)
    (st : CompState C) (tree : Option DeferredBottomTree) (h : src.trees bi = some tree) :
    runX (compBackend x q s pads u rest noise) (sourceBottomOnceX x.1 x.2.1 top bi) src st =
      pure ((tree, src), st) := by
  simp only [sourceBottomOnceX, runX_bind, runX_get, pure_bind, h, runX_pure]

/-- A first compiler request builds the tree and stores the result. -/
theorem sourceBottomOnceX_none (top : TopTree) (bi : Fin (2 ^ layerHeight)) (src : SourceState C)
    (st : CompState C) (h : src.trees bi = none) :
    runX (compBackend x q s pads u rest noise) (sourceBottomOnceX x.1 x.2.1 top bi) src st =
      (fun r => ((r.1.1, { r.1.2 with trees := Function.update r.1.2.trees bi (some r.1.1) }), r.2)) <$>
        runX (compBackend x q s pads u rest noise) (sourceBottomTreeX x.1 x.2.1 top bi) src st := by
  simp only [sourceBottomOnceX, runX_bind, runX_get, pure_bind, h, runX_pure, runX_modify,
    map_eq_bind_pure_comp, Function.comp_def]

/-- A store at another tree of the compiler keeps the stored result. -/
theorem update_top_ne {β : Type} (f : XmssSecurity.TopIndex → β) (bi bj : Fin (2 ^ layerHeight))
    (v : β) (h : bj ≠ bi) : Function.update f bi v bj = f bj :=
  Function.update_of_ne h v f

/-- A store at a tree of the compiler gives the stored result. -/
theorem update_top_self {β : Type} (f : XmssSecurity.TopIndex → β) (bi : Fin (2 ^ layerHeight))
    (v : β) : Function.update f bi v bi = v :=
  Function.update_self bi v f

/-- The store of a built tree on both sides keeps the relation inside a handler. The clauses of the
new stored tree come from `BuildFacts`, and the other stored trees keep their clauses. -/
theorem syncIn_store (top : TopTree) (sig : TsigState C) (bi : Fin (2 ^ layerHeight))
    (a : RealState C) (b : SourceStateO1 C × CompState C) (hsrc : b.1.base.trees bi = none)
    (real : Option BottomTree) (symbolic : Option DeferredBottomTree) (a' : RealState C)
    (src' : SourceState C) (st' : CompState C)
    (hs : SyncAt prims x s pads u rest noise top src'.revealed (fun _ _ => False)
      ((sig, a.1.2.1.2), a.1.2.2) ((sig, a.1.2.1.2), a.1.2.2) a' (⟨src', b.1.starts⟩, st'))
    (hsig : src'.signing = b.1.base.signing) (htrees : src'.trees = b.1.base.trees)
    (hF : BuildFacts prims x s top bi b real symbolic a' src' st') :
    SyncIn prims x s pads u rest noise top
      (({ sig with trees := Function.update sig.trees bi (some real) }, a.1.2.1.2), a.1.2.2)
      (({ sig with trees := Function.update sig.trees bi (some real) }, a.1.2.1.2), a.1.2.2) a'
      (⟨{ src' with trees := Function.update src'.trees bi (some symbolic) }, b.1.starts⟩, st') := by
  obtain ⟨hcore, hx, htop, hpads⟩ := hs
  have hr := hx.rest
  have hnone : src'.trees bi = none := htrees ▸ hsrc
  have hne : ∀ bj : Fin (2 ^ layerHeight), bj ≠ bi →
      Function.update src'.trees bi (some symbolic) bj = src'.trees bj :=
    fun bj hj => update_top_ne _ _ _ _ hj
  have hself : Function.update src'.trees bi (some symbolic) bi = some symbolic :=
    update_top_self _ _ _
  refine ⟨⟨⟨{ hcore.1.1 with
    opening := ⟨hcore.1.1.opening.actualValue, hcore.1.1.opening.released⟩ }, hcore.1.2⟩, hcore.2⟩,
    ⟨?_, hx.prfSeen, hx.bottomSeen⟩, ⟨htop.topRows, htop.topRun⟩, hpads⟩
  exact
    { hr with
      treeRows := fun bj hbj => by
        by_cases hj : bj = bi
        · subst hj
          exact hF.rows
        · exact hr.treeRows bj fun h => hbj ((hne bj hj).trans h)
      storedTrees := fun bj => by
        simp only [realSigning, flagUp, withCarried]
        by_cases hj : bj = bi
        · subst hj
          refine (Function.update_self _ _ _).trans (Eq.trans ?_ (congrArg _ hself.symm))
          rw [hF.value]
          rfl
        · exact (Function.update_of_ne hj _ _).trans
            ((hr.storedTrees bj).trans (congrArg _ (hne bj hj).symm))
      storedTopDigit := fun bj t ht => by
        by_cases hj : bj = bi
        · subst hj
          exact hF.digit t (Option.some.inj (hself.symm.trans ht))
        · exact hr.storedTopDigit bj t ((hne bj hj).symm.trans ht)
      startsTreed := fun e l hl => by
        obtain ⟨t, ht⟩ := hr.startsTreed e l hl
        have hj : treeOf e ≠ bi := by
          rintro rfl
          rw [hnone] at ht
          cases ht
        exact ⟨t, (hne _ hj).trans ht⟩
      boundTreeRevealed := fun e hb ht => by
        by_cases hj : treeOf e = bi
        · subst hj
          have hk := hF.revealed.2 ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
            (by rw [bottomKey_treeOf, ← hsig]; exact hb)
          rwa [bottomKey_treeOf] at hk
        · exact hr.boundTreeRevealed e hb fun h => ht ((hne _ hj).trans h)
      revealedTop := fun bj l p hk => by
        obtain ⟨hex, t, ht, hle⟩ := hr.revealedTop bj l p hk
        have hj : bj ≠ bi := by
          rintro rfl
          rw [hnone] at ht
          cases ht
        exact ⟨hex, t, (hne bj hj).trans ht, hle⟩
      treeTerms := fun bj hbj => by
        by_cases hj : bj = bi
        · subst hj
          exact hF.terms
        · exact hr.treeTerms bj fun h => hbj ((hne bj hj).trans h)
      treeStarts := fun bj t ht => by
        by_cases hj : bj = bi
        · subst hj
          have hsym := Option.some.inj (hself.symm.trans ht)
          exact hF.starts (by rw [hsym]; exact Option.some_ne_none _)
        · exact hr.treeStarts bj t ((hne bj hj).symm.trans ht)
      treeValues := fun bj t ht => by
        by_cases hj : bj = bi
        · subst hj
          exact hF.shape t (Option.some.inj (hself.symm.trans ht))
        · exact hr.treeValues bj t ((hne bj hj).symm.trans ht)
      storedRuns := fun bj t ht => by
        simp only [realSigning, flagUp, withCarried] at ht
        by_cases hj : bj = bi
        · subst hj
          rw [Function.update_self, Option.some.injEq] at ht
          exact hF.run t ht
        · rw [Function.update_of_ne hj] at ht
          exact hr.storedRuns bj t ht }

/-- The tree step of a signing handler on both sides. A stored result returns. A first request
builds the tree and stores the result. `sig` is the signing state that the real handler holds. -/
theorem bottomOnce_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (sig : TsigState C) (bi : Fin (2 ^ layerHeight)) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top ((sig, a.1.2.1.2), a.1.2.2)
      ((sig, a.1.2.1.2), a.1.2.2) a b)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false) :
    RelTriple
      ((simulateQ (realWorld prims x s pads u rest)
        ((bottomOnce (SigningJointEagerProof.dealtOf x top) bi).run sig)).run a)
      (runX (compBackend x q s pads u rest noise) (sourceBottomOnceX x.1 x.2.1 top bi) b.1.base b.2)
      (fun ra rb => RealStop q ra.2 ∨ Stop rb.2 ∨
        (ra.1.1 = rb.1.1.map (interpretTree s bi) ∧
          SyncIn prims x s pads u rest noise top ((ra.1.2, a.1.2.1.2), a.1.2.2)
            ((ra.1.2, a.1.2.1.2), a.1.2.2) ra.2 (⟨rb.1.2, b.1.starts⟩, rb.2) ∧
          rb.2.1.2 = false ∧ rb.1.2.signing = b.1.base.signing ∧
          rb.1.2.exposed = b.1.base.exposed ∧ rb.1.2.candidates = b.1.base.candidates ∧
          rb.1.2.trees bi = some rb.1.1 ∧ ra.2.1.2 = a.1.2 ∧
          ra.1.2.bound = sig.bound ∧ ra.1.2.corrupt = sig.corrupt ∧
          ra.1.2.released = sig.released ∧ ra.1.2.trees bi = some ra.1.1 ∧
          ∀ bj, bj ≠ bi → ra.1.2.trees bj = sig.trees bj)) := by
  have hstored : sig.trees bi = (b.1.base.trees bi).map (Option.map (interpretTree s bi)) :=
    hs.2.1.rest.storedTrees bi
  cases hsrc : b.1.base.trees bi with
  | some tree =>
    rw [hsrc, Option.map_some] at hstored
    rw [bottomOnce_run_some prims x s pads u rest top sig bi a _ hstored,
      sourceBottomOnceX_some x q s pads u rest noise top bi _ _ tree hsrc]
    exact relTriple_pure_pure (Or.inr (Or.inr ⟨rfl, hs, hmark, rfl, rfl, rfl, hsrc, rfl, rfl, rfl,
      rfl, hstored, fun _ _ => rfl⟩))
  | none =>
    rw [hsrc, Option.map_none] at hstored
    rw [bottomOnce_run_none prims x s pads u rest top sig bi a hstored,
      sourceBottomOnceX_none x q s pads u rest noise top bi _ _ hsrc]
    refine relTriple_map (relTriple_post_mono (bottomTree_sync prims x q s pads u rest noise hkeys top
      _ _ bi a b hs rfl ha hb hmark) ?_)
    rintro ra rb (h | h | ⟨hF, hsync, hsig, htrees, hexp, hcand, hm, hcar, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨hF.value, ?_, hm, hsig, hexp, hcand, update_top_self _ _ _, hcar, rfl, rfl,
      rfl, Function.update_self _ _ _, fun bj hj => Function.update_of_ne hj _ _⟩)
    exact syncIn_store prims x s pads u rest noise top sig bi a b hsrc ra.1 rb.1.1 ra.2 rb.1.2 rb.2
      hsync hsig htrees hF

end Build

end ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.update_top_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.update_top_ne

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.update_top_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.update_top_self

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.bottomOnce_run_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.bottomOnce_run_some

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.bottomOnce_run_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.bottomOnce_run_none

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.sourceBottomOnceX_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.sourceBottomOnceX_some

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.sourceBottomOnceX_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.sourceBottomOnceX_none

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.syncIn_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.syncIn_store

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.bottomOnce_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildOnce.bottomOnce_sync
