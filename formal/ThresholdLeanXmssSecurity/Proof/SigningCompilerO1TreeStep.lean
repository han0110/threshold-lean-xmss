import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1TreeRequest
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Round1
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1BuildOnce

/-! # The tree request of the O1 coupling

- `real_tree` and `comp_tree` write both handlers of a tree request as the tree step and the rest.
- `syncIn_expose` states that the insert of the tree into the exposed set of both sides keeps the
  relation inside a handler.
- `step_tree` states that a tree request keeps the boundary relation with the fixed pads or stops
  one side. Both sides return the real stored tree and the opening value of its top key.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame SigningCompilerO1TreeRequest
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
section TreeRequest
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A world run keeps the carried state. -/
theorem realWorld_run_carried {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) :
    r.2.1.2 = a.1.2 := by
  refine SeedHitProof.support_simulateQ_inv (realWorld prims x s pads u rest)
    (fun st : RealState C => st.1.2 = a.1.2) (fun t st hst z hz => ?_) _ a rfl r hr
  rw [← hst]
  change z ∈ support ((_root_.ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) t).run st) at hz
  simp only [_root_.ThresholdLeanXmssSecurity.fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
      rawCarriedLogged, simulateQ_map, simulateQ_bind, StateT.run_map, StateT.run_bind,
      support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hz
  obtain ⟨_, ⟨_, ⟨_, ⟨_, -, rfl⟩, ⟨_, -, rfl⟩⟩, rfl⟩, rfl⟩ := hz
  rfl

/-- The real handler of a tree request runs the signing oracle on the world and then names the
tree. -/
theorem real_tree (top : TopTree) (bi : Fin (2 ^ layerHeight)) (a : RealState C) :
    (realOracles prims x s pads u rest top (.inr (.tree bi))).run a =
      (fun z => (z.1.1, withCarried z.2 ((z.1.2, a.1.2.1.2), insert bi a.1.2.2.1, a.1.2.2.2))) <$>
        (simulateQ (realWorld prims x s pads u rest)
          ((tsigOracles (m := OracleComp (WorldSpec C)) (fun oa => SigningCoreProof.honestLift oa)
            (SigningJointEagerProof.dealtOf x top) (.tree bi)).run (realSigning a))).run a := by
  have hfuse : ∀ {ι κ : Type} {spec : OracleSpec ι} {mid : OracleSpec κ} {σ₁ σ₂ α : Type}
      (inner : QueryImpl spec (StateT σ₁ (OracleComp mid))) (outer : QueryImpl mid (StateT σ₂ ProbComp))
      (oa : OracleComp spec α) (s : σ₁) (c : σ₂),
      (simulateQ outer ((simulateQ inner oa).run s)).run c =
        (fun w => ((w.1, w.2.1), w.2.2)) <$>
          (simulateQ (SigningCompilerUntil.fuse inner outer) oa).run (s, c) := by
    intro ι κ spec mid σ₁ σ₂ α inner outer oa s c
    rw [← SigningCompilerUntil.simulateQ_fuse, Functor.map_map]
    exact (id_map _).symm
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (realImpl x (gOf s pads u) rest)
    ((rawTraceFlatWith prims x (openingOracles x (SigningJointEagerProof.dealtOf x top))
      (.inr (.tree bi))).run a.1)).run a.2 = _
  simp only [rawTraceFlatWith, openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk,
    Functor.map_map, simulateQ_map, StateT.run_map]
  rw [hfuse]
  simp only [Functor.map_map]
  rfl

/-- A run of a mapped program is the mapped run. -/
theorem runXO1_map {α β : Type} (f : α → β) (oa : SourceMXO1 C α) (src : SourceStateO1 C)
    (st : CompState C) :
    runXO1 (compBackend x q s pads u rest noise) (f <$> oa) src st =
      (fun r => ((f r.1.1, r.1.2), r.2)) <$> runXO1 (compBackend x q s pads u rest noise) oa src st := by
  simp [runXO1, StateT.run_map, simulateQ_map]

set_option backward.isDefEq.respectTransparency false in
/-- The compiler handler of a tree request sets the mark, runs the request on the base source state,
patches the tree and names it. -/
theorem comp_tree (top : TopTree) (bi : Fin (2 ^ layerHeight)) (b : SourceStateO1 C × CompState C) :
    (compOracles prims x q s pads u rest noise top (.inr (.tree bi))).run b =
      (fun r => (r.1.1.map (fun v => (patchTree bi v.1, v.2)),
          (⟨{ r.1.2 with exposed := insert bi r.1.2.exposed }, b.1.starts⟩, r.2))) <$>
        runX (compBackend x q s pads u rest noise) (sourceTsigX prims x top (.tree bi))
          b.1.base ((b.2.1.1, b.1.base.hiddenFlag), b.2.2) := by
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> runXO1 (compBackend x q s pads u rest noise)
      (sourceOraclesO1X prims x top (.inr (.tree bi))) b.1 b.2 = _
  simp only [sourceOraclesO1X, sourceTsigO1X]
  rw [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_get, pure_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1SyncHandlers.runXO1_mark, pure_bind,
    SigningCompilerO1ChainRelease.runXO1_bind, runXO1_map, runXO1_liftBaseX, Functor.map_map,
    bind_map_left]
  simp only [SigningCompilerO1ChainRelease.runXO1_bind, SigningCompilerO1ChainRelease.runXO1_modify,
    SigningCompilerO1ChainRelease.runXO1_pure, pure_bind, map_bind, map_pure]
  rw [← bind_pure_comp]
  rfl

/-- The real signing oracle at a tree request is the tree step and then the opening value. -/
theorem realTree_eq (top : TopTree) (bi : Fin (2 ^ layerHeight)) (sig : TsigState C) (a : RealState C) :
    (simulateQ (realWorld prims x s pads u rest)
        ((tsigOracles (m := OracleComp (WorldSpec C)) (fun oa => SigningCoreProof.honestLift oa)
          (SigningJointEagerProof.dealtOf x top) (.tree bi)).run sig)).run a =
      (simulateQ (realWorld prims x s pads u rest)
          ((bottomOnce (SigningJointEagerProof.dealtOf x top) bi).run sig)).run a >>= fun r =>
        match r.1.1 with
        | none => pure ((none, r.1.2), r.2)
        | some tree => (fun z => ((some (tree, z.1), r.1.2), z.2)) <$>
            (realHonest prims x s pads u rest
              (prfValue x.2.1 (.randomizer topLayer (topKey bi)))).run r.2 := by
  simp only [tsigOracles, StateT.run_bind, simulateQ_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨_ | tree, sig'⟩, a'⟩
  · simp
    rfl
  · simp [realHonest, liftM, monadLift, MonadLift.monadLift, StateT.run_lift, map_eq_bind_pure_comp]
    rfl

/-- The compiler signing oracle at a tree request is the tree step, the release and then the opening
value. -/
theorem sourceTree_eq (top : TopTree) (bi : Fin (2 ^ layerHeight)) (src : SourceState C)
    (st : CompState C) :
    runX (compBackend x q s pads u rest noise) (sourceTsigX prims x top (.tree bi)) src st =
      runX (compBackend x q s pads u rest noise) (sourceBottomOnceX x.1 x.2.1 top bi) src st >>= fun r =>
        match r.1.1 with
        | none => pure ((none, r.1.2), r.2)
        | some tree =>
            runX (compBackend x q s pads u rest noise) (sourceReturnTreeX x.1 x.2.1 bi tree) r.1.2 r.2 >>=
              fun r2 => (fun r3 => ((some (r2.1.1.1, r3.1.1), r3.1.2), r3.2)) <$>
                runX (compBackend x q s pads u rest noise)
                  (sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.randomizer topLayer (topKey bi))))
                  r2.1.2 r2.2 := by
  simp only [sourceTsigX, runX_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨_ | tree, src'⟩, st'⟩
  · simp [runX_pure]
    rfl
  · simp [runX_bind, runX_pure, map_eq_bind_pure_comp]
    rfl

/-- A result of a mapped run is the image of a result of the run. -/
theorem exists_of_mem_support_map {α β : Type} {f : α → β} {oa : ProbComp α} {z : β}
    (h : z ∈ support (f <$> oa)) : ∃ y ∈ support oa, f y = z := by
  rwa [support_map, Set.mem_image] at h

/-- A real stop with the flag down is a stop of the count, so another carried state keeps it. -/
theorem realStop_withCarried (z : RealState C) (c : Carried C) (hz : RealStop q z)
    (hflag : z.1.2.1.2 = false) : RealStop q (withCarried z c) := by
  unfold RealStop at hz ⊢
  rcases hz with h | h
  · rw [hflag] at h
    cases h
  · exact Or.inr h

/-- A coupling of the first runs and of each mapped rest couples the mapped binds. -/
theorem relTriple_map_bind {α β γ δ ε ζ : Type} {oa : ProbComp α} {ob : ProbComp β}
    {fa : α → ProbComp γ} {fb : β → ProbComp δ} {ga : γ → ε} {gb : δ → ζ}
    {R : α → β → Prop} {S : ε → ζ → Prop} (h : RelTriple oa ob R)
    (hk : ∀ a b, R a b → RelTriple (ga <$> fa a) (gb <$> fb b) S) :
    RelTriple (ga <$> (oa >>= fa)) (gb <$> (ob >>= fb)) S := by
  rw [map_bind, map_bind]
  exact relTriple_bind h hk

/-- The insert of the tree into the exposed set of both sides gives the boundary relation, when the
timing view already names the tree. -/
theorem syncIn_expose (top : TopTree) (bi : Fin (2 ^ layerHeight)) (c : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top c (c.1, insert bi c.2.1, c.2.2) a b) :
    SyncO1 prims x top s pads noise (gOf s pads u) rest (withCarried a (c.1, insert bi c.2.1, c.2.2))
        (⟨{ b.1.base with exposed := insert bi b.1.base.exposed }, b.1.starts⟩, b.2) ∧
      PadsFixed x pads b.2 := by
  refine (syncO1_iff_syncIn prims x s pads u rest noise top _ _).2 ?_
  obtain ⟨⟨⟨hf, hc⟩, hcount⟩, hx, htop, hpads⟩ := hs
  refine ⟨⟨⟨{ hf with
    exposed := ?_, opening := ⟨hf.opening.actualValue, hf.opening.released⟩ }, hc⟩, hcount⟩,
    ⟨{ hx.rest with treeRows := hx.rest.treeRows }, hx.prfSeen, hx.bottomSeen⟩,
    ⟨htop.topRows, htop.topRun⟩, hpads⟩
  change insert bi b.1.base.exposed = insert bi c.2.1
  rw [hf.exposed]
  rfl

/-- A tree request, with the tree step, the release and the opening value. -/
theorem step_tree (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (bi : Fin (2 ^ layerHeight)) :
    StepO1' prims x q s pads u rest noise top (.inr (.tree bi)) := by
  intro a b hs ha hb
  have hflagA : a.1.2.1.2 = false := by
    unfold RealStop at ha
    simpa using (not_or.mp ha).1
  have hflag : b.1.base.hiddenFlag = false := hs.1.1.1.1.1.flag.trans hflagA
  have hmarked := SigningCompilerO1SyncHandlers.syncO1_mark prims x s pads u rest noise top a b hs.1 false
  have hin : SyncIn prims x s pads u rest noise top a.1.2 a.1.2 a (b.1, (b.2.1.1, false), b.2.2) :=
    (syncO1_iff_syncIn prims x s pads u rest noise top a _).1 ⟨hmarked, hs.2⟩
  rw [real_tree, comp_tree, hflag, realTree_eq, sourceTree_eq]
  refine relTriple_map_bind (SigningCompilerSyncLocalRead.relTriple_supported
    (SigningCompilerO1BuildOnce.bottomOnce_sync prims x q s pads u rest noise hkeys top (realSigning a) bi a
      (b.1, (b.2.1.1, false), b.2.2) hin ha hb rfl)) ?_
  rintro ra rb ⟨hpost, hra, hrb⟩
  have hcarA : ra.2.1.2 = a.1.2 := realWorld_run_carried prims x s pads u rest _ a ra hra
  apply TreeCheckKernelCoupling.relTriple_of_support
  intro za hza zb hzb
  obtain ⟨⟨oa, sig1⟩, a1⟩ := ra
  obtain ⟨⟨ob, src1⟩, st1⟩ := rb
  have hflag1 : a1.1.2.1.2 = false := by
    rw [show a1.1.2 = a.1.2 from hcarA]
    exact hflagA
  by_cases hA : RealStop q a1
  · left
    cases oa with
    | none =>
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_support_map hza
      obtain rfl := (mem_support_pure_iff _ _).1 hz
      exact realStop_withCarried q a1 _ hA hflag1
    | some tree =>
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_support_map hza
      obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map hz
      have hcar := realWorld_run_carried prims x s pads u rest _ a1 y (by with_reducible exact hy)
      exact realStop_withCarried q y.2 _
        (SigningCompilerO1Programs.realHonest_stop prims x q s pads u rest _ a1 hA y
          (by with_reducible exact hy))
        (by rw [hcar]; exact hflag1)
  by_cases hB : Stop st1
  · right; left
    cases ob with
    | none =>
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_support_map hzb
      obtain rfl := (mem_support_pure_iff _ _).1 hz
      exact hB
    | some tree =>
      obtain ⟨z, hz, rfl⟩ := exists_of_mem_support_map hzb
      obtain ⟨r2, hr2, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨r3, hr3, rfl⟩ := exists_of_mem_support_map hz
      exact SigningCompilerO1Programs.runX_compStop x q s pads u rest noise _ _ _
        (SigningCompilerO1Programs.runX_compStop x q s pads u rest noise _ _ _ hB r2 hr2) r3 hr3
  rcases hpost with hstop | hstop | ⟨hval, hsync, hmark1, -, -, -, htree1, -⟩
  · exact absurd hstop hA
  · exact absurd hstop hB
  have hwide : SyncIn prims x s pads u rest noise top ((sig1, a.1.2.1.2), a.1.2.2)
      ((sig1, a.1.2.1.2), insert bi a.1.2.2.1, a.1.2.2.2) a1 (⟨src1, b.1.starts⟩, st1) :=
    ⟨hsync.1, ExtraOpen.expose prims x top s _ _ _ _ a1 _ hsync.2.1 (Finset.subset_insert _ _),
      hsync.2.2.1, hsync.2.2.2⟩
  cases ob with
  | none =>
    obtain rfl : oa = none := hval
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_support_map hza
    obtain rfl := (mem_support_pure_iff _ _).1 hz
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map hzb
    obtain rfl := (mem_support_pure_iff _ _).1 hy
    exact Or.inr (Or.inr ⟨rfl, syncIn_expose prims x s pads u rest noise top bi _ a1 _ hwide⟩)
  | some tree =>
    obtain rfl : oa = some (interpretTree s bi tree) := hval
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_support_map hza
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map hz
    obtain ⟨w, hw, rfl⟩ := exists_of_mem_support_map hzb
    obtain ⟨r2, hr2, hw⟩ := (mem_support_bind_iff _ _ _).1 hw
    obtain ⟨r3, hr3, rfl⟩ := exists_of_mem_support_map hw
    have hcarY : y.2.1.2 = a1.1.2 :=
      realWorld_run_carried prims x s pads u rest _ a1 y (by with_reducible exact hy)
    rcases returnTree_sync prims x q s pads u rest noise hkeys top _ _ bi tree a1
        (⟨src1, b.1.starts⟩, st1) hwide htree1 (Finset.mem_insert_self _ _) hmark1 r2 hr2
      with hstop | ⟨hv, hs2, -, -, -, -, hmark2⟩
    · exact Or.inr (Or.inl
        (SigningCompilerO1Programs.runX_compStop x q s pads u rest noise _ _ _ hstop r3 hr3))
    by_cases hB2 : Stop r2.2
    · exact Or.inr (Or.inl
        (SigningCompilerO1Programs.runX_compStop x q s pads u rest noise _ _ _ hB2 r3 hr3))
    rcases SigningCompilerO1Programs.prfValue_sync prims x q s pads u rest noise hkeys
        ((sig1, a.1.2.1.2), a.1.2.2) ⟨_, constrained_top_randomizer bi⟩ a1 r2.1.2 r2.2 hs2.1 hA hB2
        hmark2 y (by with_reducible exact hy) r3 hr3
      with hstop | hstop | ⟨hv3, hcore3, hf, -⟩
    · exact Or.inl (realStop_withCarried q y.2 _ hstop (by rw [hcarY]; exact hflag1))
    · exact Or.inr (Or.inl hstop)
    have hx3 := ExtraOpen.frame prims x top s _ (fun _ _ => False) (fun _ _ => False)
      r2.1.2.revealed r3.1.2.revealed ((sig1, a.1.2.1.2), insert bi a.1.2.2.1, a.1.2.2.2) a1 y.2
      (⟨r2.1.2, b.1.starts⟩, r2.2) (⟨r3.1.2, b.1.starts⟩, r3.2) hs2.2.1 hf rfl
      (fun k hk => by rw [hf.revealed k hk]; exact hk)
      (fun k hk => by
        by_cases h0 : r2.1.2.revealed k = none
        · obtain ⟨e, rfl, he⟩ := hf.opened k h0 hk
          exact Or.inr ⟨e, rfl, fun h => he ((congrFun hs2.1.1.1.bound e).trans h)⟩
        · exact Or.inl h0)
      (fun _ _ _ ⟨_, h⟩ => by cases h)
      (fun _ _ _ ⟨_, h⟩ => by cases h)
      (fun _ _ ⟨_, h⟩ => by
        rw [(Query.prf.inj h).2]
        exact Or.inr (constrained_top_randomizer bi))
      (fun _ _ _ _ ⟨_, h⟩ => by cases (Query.prf.inj h).2)
      (fun _ _ h => h)
    have hsync3 : SyncIn prims x s pads u rest noise top ((sig1, a.1.2.1.2), a.1.2.2)
        ((sig1, a.1.2.1.2), insert bi a.1.2.2.1, a.1.2.2.2) y.2 (⟨r3.1.2, b.1.starts⟩, r3.2) :=
      ⟨hcore3, hx3, TopO1.frame prims x top _ a1 y.2 _ _ hs2.2.2.1 hf,
        backend_padsFixed x q s pads u rest noise _ r2.2 hs2.2.2.2 r3 hr3⟩
    refine Or.inr (Or.inr ⟨?_, syncIn_expose prims x s pads u rest noise top bi _ y.2 _ hsync3⟩)
    change some (interpretTree s bi tree, y.1) = some (patchTree bi r2.1.1.1, r3.1.1)
    rw [hv.1, hv3.1]

end TreeRequest

end ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.realWorld_run_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.realWorld_run_carried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.real_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.real_tree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.runXO1_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.runXO1_map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.comp_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.comp_tree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.realTree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.realTree_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.sourceTree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.sourceTree_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.exists_of_mem_support_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.exists_of_mem_support_map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.realStop_withCarried' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.realStop_withCarried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.relTriple_map_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.relTriple_map_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.syncIn_expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.syncIn_expose

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.step_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1TreeStep.step_tree
