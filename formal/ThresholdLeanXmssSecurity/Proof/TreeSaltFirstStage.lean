import ThresholdLeanXmssSecurity.Proof.TreeSaltCrossCoupling

/-!
# The first-stage law of the cross pairs

`TreeSaltCrossCoupling.CrossFirstStage` bounds the expected `stageWeight` over the actual first
stage by `2^-256`, for a hidden stage-1 entry `a` and the stage-2 entry `j`. This module derives it
from `LiteralTransport`, a support statement on one fixed compiled program.

## Truth audit

`CrossFirstStage` is true; the argument below has no slack. The view `m` holds `s₁`, so the
proof never conditions on `m`. It fixes the run `I` instead.

## Steps

1. The first-stage law (`first_law`). `firstProgram` is the first stage with the honest step
   states as output. The boundary compiler of `TreeRawSaltCompile` turns it into `firstCompiled`
   over the opaque salt table, from the state `p.2` with every salt point open (`setup_open`).
   `first_law` equates the law of `TreeSaltPairsFinal.first` with the decoded law of
   `firstCompiled`, including the step states, both caches and the retained log. The compiled
   program reads salts only through private digest calls.
2. The run `I` (`iAnswer`). The digests of the block `a` come from fresh rows keyed by the history
   hash (`treeSimHashSaltAnswer`). `I` never reads the block `a`. All other queries, the other
   blocks and the step states are as in the real run. `fill s₁` plants the rows at the salt `s₁`
   and stores `s₁` at `a` if `a` was called.
3. The coupling (`before`, `after`). `HitA` holds when the block `a` holds `v` and `v` is a
   public digest salt, initial or later, or the salt of another block. For every weight `g` of the
   output, hash cache and block cache, the real expectation of `g` off `HitA` is at most the
   `I`-expectation of the `s₁`-average of `g ∘ fill s₁`. Before `a` is read the runs are equal.
   At the first read the real run draws `s₁`; if `s₁` is not already a covered salt, the runs
   agree until a public digest at `s₁` or another block at `s₁`.
4. The average (`avg_cross`, `avg_part`). The stage-2 table depends only on the step states, so
   it is fixed in `I`. Each position of `a` matches its partner with average `1/2`. A hidden
   partner `b ≠ a` keeps its block, and a known partner keeps its key weights, because the
   planted rows change only digest points. Both branches give exactly `2^-256` in one sum.
5. `crossFirstStage_of_transport` bounds `stageWeight` by the weight off `HitA` with
   `FirstTransport`, applies the coupling and the average, and sums. The initial salt list is
   `logSalts p.2.2`, which covers the setup cache (`DigestLogged`). `FirstTransport` states that
   a log with `FirstClean` excludes `HitA` on the support of `firstCompiled`.
6. `firstTransport_of_literal` derives `FirstTransport` from `LiteralTransport`. By `first_law`
   the decoded outcome is a real stage view, where `HiddenCoherent` and `HiddenOnly` hold. So a
   read block is a hidden read of its salt at a stage-1 address in the log. Another block at the
   salt of `a` is then a reuse of two stage-1 entries (`clean_no_reuse`). Every public salt is
   the salt of a literal log piece (`PublicLogged`). A counted literal digest at that salt is a
   `TreeSimSaltGuess`.

`LiteralTransport` states that, on the support of `firstCompiled` with `FirstClean`, every
literal digest piece at the salt of `a` is a counted query. On paper it holds for these reasons.
The prefix log has no free entry, and the setup queries only `.commit` and `.sharedKeys`. The
boundary program drops programming. `compareDigests` is the only honest digest, so a free
literal digest comes from an honest known row, and its known read is a reuse of a stage-1 pair.
`crossHiddenBound_of_literal` and `pairBoundsGuardedFrom_of_literal` carry the reduction to the
original A118 and A116 targets.

The pinned and current leanVM simulations were searched; the coupling is specific to the
threshold salt table and reuses `treeSimHashSaltAnswer_run` and `treeSimHashRowCache_local`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeSaltFirstStage

open TreeSaltGuardedPairBound TreeSaltCrossCoupling
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
open TreeRawSaltCompileProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The hidden cache holds only hidden names -/

/-- The hidden cache has entries only at hidden names. -/
def HiddenOnly (D : C.Coalition) (s : TreeSimState C) : Prop :=
  ∀ y, s.1.2 y ≠ none → Hidden D y.1.1

theorem hiddenOnly_step (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : TreeSimState C) (hs : HiddenOnly D s) (z : (WorldSpec C).Range t × TreeSimState C)
    (hz : z ∈ support ((treeSimLoggedWorld prims D t).run s)) : HiddenOnly D z.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with t | (t | t | x)
  · exact fun y hy => hs y (by rwa [← onHash_hidden _ s.1 r hr])
  · exact fun y hy => hs y (by rwa [← onHash_hidden _ s.1 r hr])
  · exact fun y hy => hs y (by rwa [← onHash_hidden _ s.1 r hr])
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨o, ho, rfl⟩ := hr
      have law : o.2 = s.1.2.cacheQuery ((x.1, x.2.1), x.2.2) o.1 := by
        cases hc : s.1.2 ((x.1, x.2.1), x.2.2) with
        | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map, Set.mem_image] at ho
          obtain ⟨v, _, rfl⟩ := ho
          rfl
        | some c =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ho
          subst ho
          funext d
          by_cases hd : d = ((x.1, x.2.1), x.2.2)
          · subst hd
            rw [QueryCache.cacheQuery_self, hc]
          · rw [QueryCache.cacheQuery_of_ne _ _ hd]
      intro y hy
      change o.2 y ≠ none at hy
      rw [law] at hy
      by_cases hyx : y = ((x.1, x.2.1), x.2.2)
      · subst hyx
        exact hx
      · rw [QueryCache.cacheQuery_of_ne _ _ hyx] at hy
        exact hs y hy
    · simp only [streamWorld, if_neg hx] at hr
      exact fun y hy => hs y (by rwa [← onHash_hidden _ s.1 r hr])

theorem hiddenOnly_run (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) (hs : HiddenOnly D s) :
    ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) oa).run s), HiddenOnly D z.2 :=
  simulateQ_run_preserves_inv_of_query _ _ (fun t s hs z hz => hiddenOnly_step prims D t s hs z hz)
    oa s hs

/-! ## The first stage as a compiled boundary program -/

section FirstLaw

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The adversary state and the honest step states at the stage point. -/
abbrev FirstView (A : Adversary C E (Keys C) PEmpty PEmpty) :=
  A.State × (C.Party → Step C E RealSpec TreeOutput)

/-- The first stage of `TreeSaltPairsFinal.first` as one world program. -/
def firstProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    OracleComp (WorldSpec C) (FirstView A) :=
  treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2 >>= fun next =>
    executeSteps worldRoles D A noFunctionality
      (TreeSaltPairsFinal.firstRounds circuits settings tree (TreeSaltPairsFinal.parameter x)) p.1.1 next

theorem first_eq (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    TreeSaltPairsFinal.first prims K circuits settings top tree D A x p =
      (simulateQ (treeSimLoggedWorld prims D) (firstProgram K circuits settings top tree D A x p)).run p.2 := by
  unfold TreeSaltPairsFinal.first firstProgram
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_executeSteps, treeSimRealRoles]

theorem partyCode_after (D : C.Coalition) (i : C.Party) (keys : Keys C) (prss : PrssKeys C)
    (top : TopTree) (tree : Tree) :
    PartyCode (E := E) D
      (ceremonyAfterSetup K circuits settings ⟨i, keys, prss⟩ top tree : PartyM C E RealSpec TreeOutput).run := by
  unfold ceremonyAfterSetup
  refine PartyCode.bind D ?_ fun out => ?_
  · rw [StateT.run'_eq]
    exact (partyCode_ceremonyOutput D K circuits settings ⟨i, keys, prss⟩ top tree (0, 0)).map D _
  · cases out <;> exact .pure _

theorem compiled_continue (D : C.Coalition) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (keys : C.Party → Option (PrssKeys C)) :
    Compiled (E := E) D (treeSimContinue (treeSimRealCont K circuits settings top tree x) keys)
      (fun steps => ∀ i, StepCode D (steps i)) := by
  unfold treeSimContinue
  rw [free_sequenceFin]
  refine Compiled.sequenceFin D _ (fun _ => StepCode D) fun i => ?_
  cases hk : keys i with
  | none => exact Compiled.pure D _ _ trivial
  | some prss =>
    simp only [continueStep]
    exact PartyCode.advance D K (partyCode_after K circuits settings D i (x i) prss top tree)

include K in
theorem compiled_executeSteps (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec TreeOutput),
      (∀ i, StepCode D (steps i)) →
      Compiled (E := E) D (executeSteps worldRoles D A noFunctionality fuel state steps)
        (fun r => ∀ i, StepCode D (r.2 i))
  | 0, state, steps, hs => Compiled.pure D _ _ hs
  | fuel + 1, state, steps, hs => by
    rw [executeSteps]
    split_ifs
    · exact Compiled.pure D _ _ hs
    · refine (compiled_stepRound D K A state steps hs).bind D fun r hr => ?_
      obtain ⟨st, sts, o⟩ := r
      exact compiled_executeSteps D A fuel st sts hr

theorem compiled_first (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    Compiled (E := E) D (firstProgram K circuits settings top tree D A x p)
      (fun r => ∀ i, StepCode D (r.2 i)) :=
  (compiled_continue K circuits settings D top tree x p.1.2).bind D fun next hn =>
    compiled_executeSteps K D A _ p.1.1 next hn

omit [Fintype E] [DecidableEq E] in
-- Copy of `aimed_noProgram_rounds` (`TreeKeyAimed.lean`) for the runner that keeps pending programs.
theorem steps_noProgram {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      IsQueryBoundP (executeSteps worldRoles D A noFunctionality fuel state steps)
        AimedProgramCall 0
  | 0, state, steps => by simp [executeSteps]
  | fuel + 1, state, steps => by
    rw [executeSteps]
    split_ifs
    · simp
    · refine qb0_bind ?_ fun r => ?_
      · unfold stepRound
        split_ifs
        · refine qb0_bind ?_ fun _ => qb0_bind (isQueryBoundP_sequenceFin _ fun i => ?_) fun _ => by simp
          · simp [runFunctionality, noFunctionality]
          · rcases steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
            · simp
            · simp
            · dsimp only; split_ifs <;> first | exact aimed_noProgram_free _ | simp
        · refine qb0_bind (aimed_noProgram_adversary _) fun _ =>
            qb0_bind (isQueryBoundP_sequenceFin _ fun i => ?_) fun _ => by simp
          rcases steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
          · simp
          · dsimp only; split_ifs <;> first | exact aimed_noProgram_free _ | simp
          · simp
      · obtain ⟨st, sts, o⟩ := r
        exact steps_noProgram D A fuel st sts

theorem first_noProgram (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    IsQueryBoundP (firstProgram K circuits settings top tree D A x p) AimedProgramCall 0 :=
  qb0_bind (aimed_noProgram_free _) fun next => steps_noProgram D A _ p.1.1 next

/-- The fixed boundary program of the first stage. -/
def firstBoundary (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    OracleComp (BoundarySpec D) (FirstView A) :=
  simulateQ (boundaryDropPrograms D)
    (Subtype.val <$> Classical.choose (compiled_first K circuits settings top tree D A x p))

theorem firstBoundary_source (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    simulateQ (boundarySource (E := E) D) (firstBoundary K circuits settings top tree D A x p) =
      firstProgram K circuits settings top tree D A x p := by
  unfold firstBoundary
  rw [boundaryDropPrograms_program, simulateQ_map,
    Classical.choose_spec (compiled_first K circuits settings top tree D A x p)]
  exact dropPrograms_eq _ (first_noProgram K circuits settings top tree D A x p)

/-- The compiled first stage over the opaque salt table, from the state `p.2`. -/
def firstCompiled (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (FirstView A × CompilerState C) :=
  (simulateQ (boundaryCompiler D) (firstBoundary K circuits settings top tree D A x p)).run
    (p.2.1.2, p.2.2.map .literal)

omit [Fintype E] [DecidableEq E] in
theorem decode_start (cache : HashCache C) (other : HiddenCache C) (log : TreeSimLog C)
    (hopen : ∀ x, (saltAt x).isSome → other x = none) :
    decodeCompiler cache ∅ ((other, log.map .literal) : CompilerState C) = ((cache, other), log) := by
  have hl : (log.map LogPiece.literal).flatMap (LogPiece.decode cache (∅ : BlockCache C)) = log := by
    induction log with
    | nil => rfl
    | cons e l ih => simpa [LogPiece.decode] using ih
  simp only [decodeCompiler, hl]
  congr 2
  funext y
  cases h : saltAt y with
  | none => simp [restore, h]
  | some bg => simp [restore, h, hopen y (by simp [h])]

/-- The first stage has the law of its compiled program, with the complete stage view. -/
theorem first_law (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hopen : ∀ y, (saltAt y).isSome → p.2.1.2 y = none) (used : SaltLists) :
    𝒟[TreeSaltPairsFinal.first prims K circuits settings top tree D A x p] =
      𝒟[decodeResult <$> tableRun prims (firstCompiled K circuits settings top tree D A x p)
        used p.2.1.1 ∅] := by
  have ready : Ready p.2.1.1 ∅ ((p.2.1.2, p.2.2.map .literal) : CompilerState C) := by
    intro piece hp
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hp
    trivial
  have h := compiler_program_law (E := E) prims D (TreeRawSaltStepsProof.boundaryCompilerSteps prims D)
    (firstBoundary K circuits settings top tree D A x p) (boundaryDropPrograms_safe D _)
    used p.2.1.1 ∅ _ ready
  rw [firstBoundary_source, decode_start _ _ _ hopen] at h
  rw [first_eq]
  exact h

end FirstLaw

/-! ## The independent-row run `I` -/

section Coupling

variable (prims : Primitives) (a : TreeSimHashSaltBlock C)

abbrev TableSpec (C : Committee) := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C

/-- The hash cache and the rows of the target block, the block cache, and whether the target
block was called. -/
abbrev IState (C : Committee) :=
  (HashCache C × List (HashOutput × HashOutput)) × BlockCache C × Bool

/-- A lazy read of one block. -/
def blockRead (b : TreeSimHashSaltBlock C) (blocks : BlockCache C) :
    ProbComp ((Fin 256 → Bit) × BlockCache C) :=
  ((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run blocks

/-- The run `I`: the digests of the target block `a` come from fresh rows, so `I` never reads
the block `a`. Every other query is answered as in `tableRun`. -/
def iAnswer : QueryImpl (TableSpec C) (StateT (IState C) ProbComp)
  | .inl (b, history) => StateT.mk fun s =>
    if b = a then (fun r => (r.1, r.2, s.2.1, true)) <$> (treeSimHashSaltAnswer prims history).run s.1
    else do
      let salt ← blockRead b s.2.1
      (fun r => (r.1, (r.2, s.1.2), salt.2, s.2.2)) <$>
        (saltedDigestAnswer prims (List.ofFn salt.1) history).run s.1.1
  | .inr t => StateT.mk fun s => (fun r => (r.1, (r.2, s.1.2), s.2)) <$> (localAnswer prims t).run s.1.1

/-- An outcome of `I` with the target salt `s₁` put back: the planted rows in the hash cache and
the block `a`, if it was called. -/
def fill (s₁ : Fin 256 → Bit) {α : Type} (r : α × IState C) : α × HashCache C × BlockCache C :=
  (r.1, treeSimHashRowCache r.2.1.1 (List.ofFn s₁) r.2.1.2,
    if r.2.2.2 then r.2.2.1.cacheQuery a s₁ else r.2.2.1)

/-- The block `a` is read, and its salt is a public digest salt or the salt of another block. -/
def HitState (used : SaltLists) (blocks : BlockCache C) : Prop :=
  ∃ v, blocks a = some v ∧ (List.ofFn v ∈ used.2 ∨ ∃ b, b ≠ a ∧ blocks b = some v)

/-- `HitState` on the final state of a table run. -/
def HitA {α : Type} (r : TableOutcome (C := C) (TreeSimHashSaltBlock C) α) : Prop :=
  HitState a r.1.2 r.2.2

/-- The cache of the digests is covered by the used salts, and each private used salt is a block. -/
def Cov (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C) : Prop :=
  DigestSaltsCovered cache (used.1 ++ used.2).toFinset ∧
    ∀ v ∈ used.1, ∃ b w, blocks b = some w ∧ List.ofFn w = v

theorem blockRead_grow (b : TreeSimHashSaltBlock C) (blocks : BlockCache C)
    (r : (Fin 256 → Bit) × BlockCache C) (hr : r ∈ support (blockRead b blocks)) :
    r.2 = blocks.cacheQuery b r.1 ∧ (∀ b' v, blocks b' = some v → r.2 b' = some v) := by
  have hu := block_read_update b blocks r hr
  refine ⟨hu, fun b' v hv => ?_⟩
  rw [hu]
  by_cases hb : b' = b
  · subst hb
    unfold blockRead at hr
    rw [QueryImpl.withCaching_run_some _ hv, mem_support_pure_iff] at hr
    subst hr
    exact QueryCache.cacheQuery_self _ _ _
  · rw [QueryCache.cacheQuery_of_ne _ _ hb]
    exact hv

theorem cacheQuery_comm (blocks : BlockCache C) {a b : TreeSimHashSaltBlock C} (hab : b ≠ a)
    (u v : Fin 256 → Bit) :
    (blocks.cacheQuery a u).cacheQuery b v = (blocks.cacheQuery b v).cacheQuery a u := by
  funext c
  by_cases hc : c = a
  · subst hc
    rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hab), QueryCache.cacheQuery_self,
      QueryCache.cacheQuery_self]
  · by_cases hcb : c = b
    · subst hcb
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne _ _ hc, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hcb, QueryCache.cacheQuery_of_ne _ _ hc,
        QueryCache.cacheQuery_of_ne _ _ hc, QueryCache.cacheQuery_of_ne _ _ hcb]

/-- A read of another block commutes with the stored target block. -/
theorem blockRead_other (b : TreeSimHashSaltBlock C) (hab : b ≠ a) (blocks : BlockCache C)
    (s₁ : Fin 256 → Bit) :
    blockRead b (blocks.cacheQuery a s₁) =
      (fun r => (r.1, r.2.cacheQuery a s₁)) <$> blockRead b blocks := by
  unfold blockRead
  cases hb : blocks b with
  | none =>
    have hb' : (blocks.cacheQuery a s₁) b = none := by
      rw [QueryCache.cacheQuery_of_ne _ _ hab, hb]
    rw [QueryImpl.withCaching_run_none _ hb', QueryImpl.withCaching_run_none _ hb, Functor.map_map]
    congr 1
    funext v
    rw [cacheQuery_comm blocks hab]
  | some v =>
    have hb' : (blocks.cacheQuery a s₁) b = some v := by
      rw [QueryCache.cacheQuery_of_ne _ _ hab, hb]
    rw [QueryImpl.withCaching_run_some _ hb', QueryImpl.withCaching_run_some _ hb, map_pure]

theorem blockRead_none (blocks : BlockCache C) (ha : blocks a = none) :
    blockRead a blocks = (fun v => (v, blocks.cacheQuery a v)) <$> ($ᵗ (Fin 256 → Bit)) := by
  unfold blockRead
  rw [QueryImpl.withCaching_run_none _ ha]
  rfl

theorem blockRead_some (blocks : BlockCache C) (v : Fin 256 → Bit) (ha : blocks a = some v) :
    blockRead a blocks = pure (v, blocks) := by
  unfold blockRead
  rw [QueryImpl.withCaching_run_some _ ha]

theorem tableRun_pure_eq {α : Type} (x : α) (used : SaltLists) (cache : HashCache C)
    (blocks : BlockCache C) :
    tableRun prims (pure x : OracleComp (TableSpec C) α) used cache blocks =
      pure ((x, used), cache, blocks) := by
  simp [tableRun]

set_option backward.isDefEq.respectTransparency false in
/-- Every table run keeps the earlier blocks and public salts. -/
theorem tableRun_grow {α : Type} (P : OracleComp (TableSpec C) α)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (r) (hr : r ∈ support (tableRun prims P used cache blocks)) :
    used.2 ⊆ r.1.2.2 ∧ ∀ b v, blocks b = some v → r.2.2 b = some v := by
  refine ⟨TreeRawSaltCertificatesProof.tableRun_public_mono prims P used cache blocks r hr, ?_⟩
  induction P using OracleComp.inductionOn generalizing used cache blocks with
  | pure value =>
    rw [tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    exact fun b v h => h
  | query_bind t k ih =>
    rw [tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    intro b v hv
    apply ih mid.1.1 mid.1.2 mid.2.1 mid.2.2 hr
    cases t with
    | inl row =>
      rcases row with ⟨b', history⟩
      rw [tableRun_private, mem_support_bind_iff] at hm
      obtain ⟨salt, hs, hm⟩ := hm
      simp only [support_map, Set.mem_image] at hm
      obtain ⟨out, _, rfl⟩ := hm
      exact (blockRead_grow b' blocks salt hs).2 b v hv
    | inr t =>
      rw [tableRun_public] at hm
      simp only [support_map, Set.mem_image] at hm
      obtain ⟨out, _, rfl⟩ := hm
      exact hv

theorem hit_persist {α : Type} (P : OracleComp (TableSpec C) α)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (hit : HitState a used blocks) :
    ∀ r ∈ support (tableRun prims P used cache blocks), HitA a r := by
  intro r hr
  obtain ⟨hu, hb⟩ := tableRun_grow prims P used cache blocks r hr
  obtain ⟨v, hv, h⟩ := hit
  refine ⟨v, hb a v hv, ?_⟩
  rcases h with h | ⟨b, hba, hbv⟩
  · exact Or.inl (hu h)
  · exact Or.inr ⟨b, hba, hb b v hbv⟩

theorem tsum_hit_zero {α : Type} (P : OracleComp (TableSpec C) α)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (hit : HitState a used blocks) (g : TableOutcome (C := C) (TreeSimHashSaltBlock C) α → ℝ≥0∞) :
    ∑' r, Pr[= r | tableRun prims P used cache blocks] * (if HitA a r then 0 else g r) = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun r => ?_
  by_cases hr : r ∈ support (tableRun prims P used cache blocks)
  · rw [if_pos (hit_persist prims a P used cache blocks hit r hr), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

/-- A digest under another salt commutes with the planted rows. -/
theorem saltedDigest_rowCache (salt history : List Bit) (s₁ : List Bit) (hne : salt ≠ s₁)
    (cache : HashCache C) (rows : List (HashOutput × HashOutput)) :
    (saltedDigestAnswer prims salt history).run (treeSimHashRowCache cache s₁ rows) =
      (fun r => (r.1, treeSimHashRowCache r.2 s₁ rows)) <$>
        (saltedDigestAnswer prims salt history).run cache := by
  unfold saltedDigestAnswer
  rw [StateT.run_bind, StateT.run_bind, treeSimHashRowCache_history, bind_map_left, map_bind]
  apply bind_congr
  intro r
  have h := treeSimHashRowCache_local prims r.2 s₁ rows (.inr (.inl (.digest salt r.1)))
    (by simp [digestSaltHit, hne])
  exact h

theorem saltedDigest_covered (salt history : List Bit) (cache : HashCache C)
    (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen)
    (r : HashOutput × HashCache C)
    (hr : r ∈ support ((saltedDigestAnswer prims salt history).run cache)) :
    DigestSaltsCovered r.2 (insert salt seen) := by
  unfold saltedDigestAnswer at hr
  rw [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hmid, hr⟩ := hr
  have h1 := history_preserves_digestSalts prims cache seen hc history mid hmid
  have h2 := localAnswer_digest_covered prims mid.2 seen.toList
    (fun s h hh => Finset.mem_toList.mpr (h1 s h hh)) (.inr (.inl (.digest salt mid.1))) r hr
  intro s h hh
  have := h2 s h hh
  simp only [digestSaltProjection, Option.toList_some, List.cons_append, List.mem_cons,
    List.nil_append, Finset.mem_toList] at this
  rcases this with rfl | h
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem h

theorem tableRun_private_read (b : TreeSimHashSaltBlock C) (history : List Bit) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) :
    tableRun prims (OracleComp.lift (OracleSpec.query (spec := TableSpec C) (.inl (b, history))))
      used cache blocks = (do
      let salt ← blockRead b blocks
      (fun r => ((r.1, used.1 ++ [List.ofFn salt.1], used.2), r.2, salt.2)) <$>
        (saltedDigestAnswer prims (List.ofFn salt.1) history).run cache) :=
  tableRun_private prims b history used cache blocks

theorem iAnswer_target (history : List Bit) (s : IState C) :
    (iAnswer prims a (.inl (a, history))).run s =
      (fun r => (r.1, r.2, s.2.1, true)) <$> (treeSimHashSaltAnswer prims history).run s.1 := by
  simp only [iAnswer, StateT.run_mk, if_true]
  rfl

theorem iAnswer_other (b : TreeSimHashSaltBlock C) (hb : b ≠ a) (history : List Bit) (s : IState C) :
    (iAnswer prims a (.inl (b, history))).run s = (do
      let salt ← blockRead b s.2.1
      (fun r => (r.1, (r.2, s.1.2), salt.2, s.2.2)) <$>
        (saltedDigestAnswer prims (List.ofFn salt.1) history).run s.1.1) := by
  simp only [iAnswer, StateT.run_mk, if_neg hb]

theorem iAnswer_public (t : (LocalSpec C).Domain) (s : IState C) :
    (iAnswer prims a (.inr t)).run s =
      (fun r => (r.1, (r.2, s.1.2), s.2)) <$> (localAnswer prims t).run s.1.1 := rfl

theorem ofFn_ne {v w : Fin 256 → Bit} (h : v ≠ w) : List.ofFn v ≠ List.ofFn w :=
  fun he => h (List.ofFn_injective he)

set_option backward.isDefEq.respectTransparency false in
/-- After the target block holds `s₁`, the real table run and `I` agree until a hit. -/
theorem after {α : Type} (g : α × HashCache C × BlockCache C → ℝ≥0∞) (s₁ : Fin 256 → Bit)
    (P : OracleComp (TableSpec C) α) :
    ∀ (used : SaltLists) (cacheI : HashCache C) (rows : List (HashOutput × HashOutput))
      (blocksI : BlockCache C) (seen : Finset (List Bit)),
    blocksI a = none → DigestSaltsCovered cacheI seen → List.ofFn s₁ ∉ seen →
    ∑' r, Pr[= r | tableRun prims P used (treeSimHashRowCache cacheI (List.ofFn s₁) rows)
        (blocksI.cacheQuery a s₁)] * (if HitA a r then 0 else g (r.1.1, r.2.1, r.2.2)) ≤
      ∑' r, Pr[= r | (simulateQ (iAnswer prims a) P).run ((cacheI, rows), blocksI, true)] *
        g (fill a s₁ r) := by
  induction P using OracleComp.inductionOn with
  | pure x =>
    intro used cacheI rows blocksI seen _ _ _
    rw [tableRun_pure_eq, tsum_probOutput_pure_mul]
    simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, fill, if_true]
    split_ifs
    · exact zero_le
    · exact le_rfl
  | query_bind t k ih =>
    intro used cacheI rows blocksI seen ha hc hs
    rw [tableRun_bind, tsum_probOutput_bind_mul]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [tsum_probOutput_bind_mul]
    cases t with
    | inr u =>
      by_cases hu : digestSaltHit (List.ofFn s₁) u = true
      · refine le_of_eq_of_le ?_ zero_le
        refine ENNReal.tsum_eq_zero.mpr fun z => ?_
        by_cases hz : z ∈ support (tableRun prims
            (OracleComp.lift (OracleSpec.query (spec := TableSpec C) (.inr u))) used
            (treeSimHashRowCache cacheI (List.ofFn s₁) rows) (blocksI.cacheQuery a s₁))
        · refine mul_eq_zero_of_right _ (tsum_hit_zero prims a (k z.1.1) _ _ _ ?_ _)
          rw [tableRun_public] at hz
          simp only [support_map, Set.mem_image] at hz
          obtain ⟨out, _, rfl⟩ := hz
          refine ⟨s₁, QueryCache.cacheQuery_self _ _ _, Or.inl ?_⟩
          rw [digestSaltHit_projection, decide_eq_true_eq] at hu
          show List.ofFn s₁ ∈ (digestSaltProjection u).toList ++ used.2
          rw [hu]
          exact List.mem_append_left _ (List.mem_singleton_self _)
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul]
      · have hu' : digestSaltHit (List.ofFn s₁) u = false := Bool.eq_false_iff.mpr hu
        rw [tableRun_public, treeSimHashRowCache_local prims cacheI _ rows u hu', Functor.map_map,
          tsum_probOutput_map_mul, iAnswer_public, tsum_probOutput_map_mul]
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((localAnswer prims u).run cacheI)
        · refine mul_le_mul_right ?_ _
          obtain ⟨seen', hc', hs'⟩ :=
            treeSimHash_local_covered_off_hit prims cacheI seen hc _ hs u hu' z hz
          exact ih z.1 _ z.2 rows blocksI seen' ha hc' hs'
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
    | inl row =>
      rcases row with ⟨b, history⟩
      by_cases hb : b = a
      · subst hb
        rw [tableRun_private_read, blockRead_some b _ s₁ (QueryCache.cacheQuery_self _ _ _),
          pure_bind, treeSimHashSaltAnswer_run prims _ history cacheI seen hc hs rows,
          Functor.map_map, tsum_probOutput_map_mul, iAnswer_target, tsum_probOutput_map_mul]
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((treeSimHashSaltAnswer prims history).run (cacheI, rows))
        · refine mul_le_mul_right ?_ _
          exact ih z.1 _ z.2.1 z.2.2 blocksI seen ha
            (treeSimHashSaltAnswer_covered prims history cacheI rows seen hc z hz) hs
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      · rw [tableRun_private_read, blockRead_other a b hb, bind_map_left, tsum_probOutput_bind_mul,
          iAnswer_other prims a b hb, tsum_probOutput_bind_mul]
        refine ENNReal.tsum_le_tsum fun w => ?_
        by_cases hw : w ∈ support (blockRead b blocksI)
        · refine mul_le_mul_right ?_ _
          obtain ⟨hw2, -⟩ := blockRead_grow b blocksI w hw
          by_cases hv : w.1 = s₁
          · refine le_of_eq_of_le ?_ zero_le
            rw [tsum_probOutput_map_mul]
            refine ENNReal.tsum_eq_zero.mpr fun z => ?_
            refine mul_eq_zero_of_right _ (tsum_hit_zero prims a (k z.1) _ _ _ ?_ _)
            refine ⟨s₁, QueryCache.cacheQuery_self _ _ _, Or.inr ⟨b, hb, ?_⟩⟩
            show (w.2.cacheQuery a s₁) b = some s₁
            rw [QueryCache.cacheQuery_of_ne _ _ hb, hw2, QueryCache.cacheQuery_self, hv]
          · have hne : List.ofFn w.1 ≠ List.ofFn s₁ := ofFn_ne hv
            rw [saltedDigest_rowCache prims _ history _ hne, Functor.map_map,
              tsum_probOutput_map_mul, tsum_probOutput_map_mul]
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hz : z ∈ support ((saltedDigestAnswer prims (List.ofFn w.1) history).run cacheI)
            · refine mul_le_mul_right ?_ _
              have hwa : w.2 a = none := by
                rw [hw2, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hb), ha]
              refine ih z.1 _ z.2 rows w.2 (insert (List.ofFn w.1) seen) hwa
                (saltedDigest_covered prims _ history cacheI seen hc z hz) ?_
              rw [Finset.mem_insert, not_or]
              exact ⟨Ne.symm hne, hs⟩
            · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
        · rw [probOutput_eq_zero_of_not_mem_support hw, zero_mul, zero_mul]

theorem uniform_mass : ∑' v, Pr[= v | ($ᵗ (Fin 256 → Bit) : ProbComp (Fin 256 → Bit))] = 1 :=
  tsum_probOutput_eq_one' (by simp)

theorem cov_public (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (hcov : Cov used cache blocks) (u : (LocalSpec C).Domain) (z : (LocalSpec C).Range u × HashCache C)
    (hz : z ∈ support ((localAnswer prims u).run cache)) :
    Cov (used.1, (digestSaltProjection u).toList ++ used.2) z.2 blocks := by
  refine ⟨fun salt h hh => ?_, hcov.2⟩
  have := localAnswer_digest_covered prims cache (used.1 ++ used.2)
    (fun s h hh => List.mem_toFinset.mp (hcov.1 s h hh)) u z hz salt h hh
  simp only [List.mem_append] at this
  simp only [List.mem_toFinset, List.mem_append]
  tauto

theorem cov_private (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (hcov : Cov used cache blocks) (b : TreeSimHashSaltBlock C) (history : List Bit)
    (w : (Fin 256 → Bit) × BlockCache C) (hw : w ∈ support (blockRead b blocks))
    (z : HashOutput × HashCache C)
    (hz : z ∈ support ((saltedDigestAnswer prims (List.ofFn w.1) history).run cache)) :
    Cov (used.1 ++ [List.ofFn w.1], used.2) z.2 w.2 := by
  obtain ⟨hw2, grow⟩ := blockRead_grow b blocks w hw
  refine ⟨fun salt h hh => ?_, fun v hv => ?_⟩
  · have := saltedDigest_covered prims _ history cache _ hcov.1 z hz salt h hh
    simp only [Finset.mem_insert, List.mem_toFinset, List.mem_append] at this
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
    tauto
  · rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨b', w', hb', hw'⟩ := hcov.2 v hv
      exact ⟨b', w', grow b' w' hb', hw'⟩
    · rw [List.mem_singleton] at hv
      refine ⟨b, w.1, ?_, hv.symm⟩
      rw [hw2]
      exact QueryCache.cacheQuery_self _ _ _

/-- The three sums of the target read commute. -/
theorem tsum_swap3 {β γ δ : Type} (p : β → ℝ≥0∞) (q : γ → ℝ≥0∞) (r : γ → δ → ℝ≥0∞)
    (f : β → δ → ℝ≥0∞) :
    ∑' v, p v * ∑' z, q z * ∑' x, r z x * f v x =
      ∑' z, q z * ∑' x, r z x * ∑' v, p v * f v x := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => tsum_congr fun v => ?_
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Before the target block is read, the real table run and `I` are equal. At the first read the
real run draws `s₁`, and `I` answers from fresh rows; the sum over `s₁` moves to the end. -/
theorem before {α : Type} (g : α × HashCache C × BlockCache C → ℝ≥0∞)
    (P : OracleComp (TableSpec C) α) :
    ∀ (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C),
    blocks a = none → Cov used cache blocks →
    ∑' r, Pr[= r | tableRun prims P used cache blocks] *
        (if HitA a r then 0 else g (r.1.1, r.2.1, r.2.2)) ≤
      ∑' r, Pr[= r | (simulateQ (iAnswer prims a) P).run ((cache, []), blocks, false)] *
        ∑' s₁, Pr[= s₁ | ($ᵗ (Fin 256 → Bit) : ProbComp (Fin 256 → Bit))] * g (fill a s₁ r) := by
  induction P using OracleComp.inductionOn with
  | pure x =>
    intro used cache blocks _ _
    rw [tableRun_pure_eq, tsum_probOutput_pure_mul]
    simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
    have hfill : ∀ s₁ : Fin 256 → Bit,
        fill a s₁ ((x, ((cache, []), blocks, false)) : α × IState C) = (x, cache, blocks) :=
      fun _ => rfl
    simp only [hfill]
    rw [ENNReal.tsum_mul_right, uniform_mass, one_mul]
    split_ifs
    · exact zero_le
    · exact le_rfl
  | query_bind t k ih =>
    intro used cache blocks ha hcov
    rw [tableRun_bind, tsum_probOutput_bind_mul]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [tsum_probOutput_bind_mul]
    cases t with
    | inr u =>
      rw [tableRun_public, tsum_probOutput_map_mul, iAnswer_public, tsum_probOutput_map_mul]
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : z ∈ support ((localAnswer prims u).run cache)
      · refine mul_le_mul_right ?_ _
        exact ih z.1 _ z.2 blocks ha (cov_public prims used cache blocks hcov u z hz)
      · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
    | inl row =>
      rcases row with ⟨b, history⟩
      by_cases hb : b = a
      · subst hb
        rw [tableRun_private_read, blockRead_none b blocks ha, bind_map_left, tsum_probOutput_bind_mul,
          iAnswer_target, tsum_probOutput_map_mul]
        refine le_trans (ENNReal.tsum_le_tsum fun v => mul_le_mul_right (?_ : _ ≤
          ∑' z, Pr[= z | (treeSimHashSaltAnswer prims history).run (cache, [])] *
            ∑' r, Pr[= r | (simulateQ (iAnswer prims b) (k z.1)).run ((z.2.1, z.2.2), blocks, true)] *
              g (fill b v r)) _) (le_of_eq (tsum_swap3 _ _ _ _))
        by_cases hv : List.ofFn v ∈ (used.1 ++ used.2).toFinset
        · refine le_of_eq_of_le ?_ zero_le
          rw [tsum_probOutput_map_mul]
          refine ENNReal.tsum_eq_zero.mpr fun z => mul_eq_zero_of_right _
            (tsum_hit_zero prims b (k z.1) _ _ _ ?_ _)
          refine ⟨v, QueryCache.cacheQuery_self _ _ _, ?_⟩
          rw [List.mem_toFinset, List.mem_append] at hv
          rcases hv with hv | hv
          · obtain ⟨b', w', hb', hw'⟩ := hcov.2 _ hv
            have hwv : w' = v := List.ofFn_injective hw'
            subst hwv
            have hne : b' ≠ b := by
              rintro rfl
              rw [ha] at hb'
              cases hb'
            refine Or.inr ⟨b', hne, ?_⟩
            show (blocks.cacheQuery b w') b' = some w'
            rw [QueryCache.cacheQuery_of_ne _ _ hne, hb']
          · exact Or.inl hv
        · have hrun := treeSimHashSaltAnswer_run prims (List.ofFn v) history cache _ hcov.1 hv []
          rw [show (saltedDigestAnswer prims (List.ofFn v) history).run cache = _ from hrun,
            Functor.map_map, tsum_probOutput_map_mul]
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support ((treeSimHashSaltAnswer prims history).run (cache, []))
          · refine mul_le_mul_right ?_ _
            exact after prims b g v (k z.1) _ z.2.1 z.2.2 blocks _ ha
              (treeSimHashSaltAnswer_covered prims history cache [] _ hcov.1 z hz) hv
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      · rw [tableRun_private_read, tsum_probOutput_bind_mul, iAnswer_other prims a b hb,
          tsum_probOutput_bind_mul]
        refine ENNReal.tsum_le_tsum fun w => ?_
        by_cases hw : w ∈ support (blockRead b blocks)
        · refine mul_le_mul_right ?_ _
          rw [tsum_probOutput_map_mul, tsum_probOutput_map_mul]
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : z ∈ support ((saltedDigestAnswer prims (List.ofFn w.1) history).run cache)
          · refine mul_le_mul_right ?_ _
            have hwa : w.2 a = none := by
              rw [(blockRead_grow b blocks w hw).1, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hb), ha]
            exact ih z.1 _ z.2 w.2 hwa (cov_private prims used cache blocks hcov b history w hw z hz)
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
        · rw [probOutput_eq_zero_of_not_mem_support hw, zero_mul, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The run `I` never reads the target block. -/
theorem iRun_target {α : Type} (P : OracleComp (TableSpec C) α) (s : IState C) (hs : s.2.1 a = none) :
    ∀ r ∈ support ((simulateQ (iAnswer prims a) P).run s), r.2.2.1 a = none := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure x =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst hr
    exact hs
  | query_bind t k ih =>
    intro r hr
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    apply ih mid.1 mid.2 _ r hr
    cases t with
    | inr u =>
      rw [iAnswer_public] at hm
      simp only [support_map, Set.mem_image] at hm
      obtain ⟨z, _, rfl⟩ := hm
      exact hs
    | inl row =>
      rcases row with ⟨b, history⟩
      by_cases hb : b = a
      · subst hb
        rw [iAnswer_target] at hm
        simp only [support_map, Set.mem_image] at hm
        obtain ⟨z, _, rfl⟩ := hm
        exact hs
      · rw [iAnswer_other prims a b hb] at hm
        simp only [mem_support_bind_iff, support_map, Set.mem_image] at hm
        obtain ⟨w, hw, z, _, rfl⟩ := hm
        show w.2 a = none
        rw [(blockRead_grow b s.2.1 w hw).1, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hb), hs]

end Coupling

/-! ## The average over the target salt -/

section Average

theorem rowCache_streamKey (cache : HashCache C) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) (key : HashOutput) :
    treeSimHashRowCache cache salt rows (.streamKey key) = cache (.streamKey key) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [treeSimHashRowCache, List.foldr_cons] at ih ⊢
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp), ih]

theorem keyWeight_rowCache (b : C.Term × HashOutput × ℕ) (cache : HashCache C) (salt : List Bit)
    (rows : List (HashOutput × HashOutput)) (k : HashOutput) :
    keyWeight b (treeSimHashRowCache cache salt rows) k = keyWeight b cache k := by
  simp only [keyWeight, rowCache_streamKey]

theorem pr_uniform (s₁ : Fin 256 → Bit) :
    Pr[= s₁ | ($ᵗ (Fin 256 → Bit) : ProbComp (Fin 256 → Bit))] = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]

/-- The average of the pair weight of the target salt against fixed sides. -/
theorem avg_side (called : Bool) (B : Fin 256 → Option Bit) :
    ∑ s₁ : Fin 256 → Bit, (2 ^ 256 : ℝ≥0∞)⁻¹ *
      ∏ g, saltPositionWeight (if called then some (s₁ g) else none) (B g) = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  cases called with
  | false =>
    simp only [Bool.false_eq_true, if_false, (saltPositionWeight_open _).1, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.inv_pow]
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  | true =>
    simp only [if_true]
    rw [← Finset.mul_sum, ← Fintype.prod_sum (fun g (bit : Bit) => saltPositionWeight (some bit) (B g))]
    have h : ∀ g, ∑ bit : Bit, saltPositionWeight (some bit) (B g) = 1 := fun g => by
      change ∑ bit : Fin 2, saltPositionWeight (some bit) (B g) = 1
      rw [Fin.sum_univ_two]
      exact (saltPositionWeight_draw (B g)).1
    simp only [h, Finset.prod_const_one, mul_one]

variable (prims : Primitives)

/-- The hidden point of the target salt in a restored cache. -/
theorem side_target (blocks : BlockCache C) (other : HiddenCache C) (a : C.Term × HashOutput × ℕ)
    (g : Fin 256) :
    saltSideValue (restore blocks other) (.inl (saltPoint a g)) = (blocks a).map (fun v => v g) :=
  restore_address blocks other a g

set_option backward.isDefEq.respectTransparency false in
/-- The average of `crossWeight` at a filled outcome of `I` is `2^-256`, in both branches. -/
theorem avg_cross (D : C.Coalition) (a b : C.Term × HashOutput × ℕ) (hab : b ≠ a)
    (cache : HashCache C) (rows : List (HashOutput × HashOutput)) (blocks : BlockCache C)
    (ha : blocks a = none) (called : Bool) (other : HiddenCache C) :
    ∑' s₁, Pr[= s₁ | ($ᵗ (Fin 256 → Bit) : ProbComp (Fin 256 → Bit))] *
      crossWeight prims D a b (treeSimHashRowCache cache (List.ofFn s₁) rows,
        restore (if called then blocks.cacheQuery a s₁ else blocks) other) = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hA : ∀ (s₁ : Fin 256 → Bit) g,
      saltSideValue (restore (if called then blocks.cacheQuery a s₁ else blocks) other)
        (.inl (saltPoint a g)) = if called then some (s₁ g) else none := by
    intro s₁ g
    rw [side_target]
    cases called
    · simp [ha]
    · simp
  have hB : ∀ (s₁ : Fin 256 → Bit) g,
      saltSideValue (restore (if called then blocks.cacheQuery a s₁ else blocks) other)
        (.inl (saltPoint b g)) = (blocks b).map (fun v => v g) := by
    intro s₁ g
    rw [side_target]
    cases called
    · simp
    · simp [QueryCache.cacheQuery_of_ne _ _ hab]
  rw [tsum_fintype]
  simp only [pr_uniform]
  by_cases kb : KnownTo D.1 b.1
  · have e : ∀ s₁ : Fin 256 → Bit, crossWeight prims D a b (treeSimHashRowCache cache (List.ofFn s₁) rows,
        restore (if called then blocks.cacheQuery a s₁ else blocks) other) =
        ∑ k, keyWeight b cache k * ∏ g, saltPositionWeight (if called then some (s₁ g) else none)
          (some (keyBit prims b k g)) := by
      intro s₁
      rw [crossWeight, if_pos kb, knownPotential]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [keyWeight_rowCache, saltPairWeight]
      congr 1
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [hA]
      rfl
    simp only [e]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm _ (keyWeight b cache _)]
    rw [Finset.sum_congr rfl fun k _ => by rw [← Finset.mul_sum, avg_side], ← Finset.sum_mul,
      keyWeight_sum, one_mul]
  · have e : ∀ s₁ : Fin 256 → Bit, crossWeight prims D a b (treeSimHashRowCache cache (List.ofFn s₁) rows,
        restore (if called then blocks.cacheQuery a s₁ else blocks) other) =
        ∏ g, saltPositionWeight (if called then some (s₁ g) else none) ((blocks b).map (fun v => v g)) := by
      intro s₁
      rw [crossWeight, if_neg kb, saltPairWeight]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [hA, hB]
    simp only [e]
    exact avg_side called _

end Average

/-! ## The state at the end of the setup -/

section SetupState

/-- The salt of a logged digest query, counted, free or programmed. -/
def entrySalt (e : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) : Option (List Bit) :=
  match e.1 with
  | .inl (.inl u) => digestSaltProjection u
  | .inl (.inr x) => match x.1 with
    | .digest salt _ => some salt
    | _ => none
  | .inr u => digestSaltProjection u

/-- The salts of all logged digest queries. -/
def logSalts (log : TreeSimLog C) : List (List Bit) := log.filterMap entrySalt

/-- Every cached digest has a logged salt. -/
def DigestLogged (s : TreeSimState C) : Prop := DigestSaltsCovered s.1.1 (logSalts s.2).toFinset

theorem logSalts_append (log : TreeSimLog C) (e : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) :
    logSalts (log ++ [e]) = logSalts log ++ (entrySalt e).toList := by
  simp only [logSalts, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases entrySalt e <;> rfl

theorem digestLogged_local (prims : Primitives) (s : TreeSimState C) (hs : DigestLogged s)
    (u : (LocalSpec C).Domain) (o : (LocalSpec C).Range u × HashCache C)
    (ho : o ∈ support ((localAnswer prims u).run s.1.1)) (e : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t)
    (he : entrySalt e = digestSaltProjection u) :
    DigestSaltsCovered o.2 (logSalts (s.2 ++ [e])).toFinset := by
  intro salt h hh
  have := localAnswer_digest_covered prims s.1.1 (logSalts s.2)
    (fun s' h' hh' => List.mem_toFinset.mp (hs s' h' hh')) u o ho salt h hh
  rw [logSalts_append, he, List.mem_toFinset, List.mem_append]
  rw [List.mem_append] at this
  tauto

theorem digestLogged_step (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : TreeSimState C) (hs : DigestLogged s) (z : (WorldSpec C).Range t × TreeSimState C)
    (hz : z ∈ support ((treeSimLoggedWorld prims D t).run s)) : DigestLogged z.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with (u | x) | u
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨o, ho, rfl⟩ := hr
    exact digestLogged_local prims s hs u o ho _ rfl
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨o, ho, rfl⟩ := hr
    change o ∈ support ((programAnswer x).run s.1.1) at ho
    intro salt h hh
    rw [logSalts_append, List.mem_toFinset, List.mem_append]
    simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at ho
    split_ifs at ho
    · simp only [StateT.run_pure] at ho
      subst ho
      exact Or.inl (List.mem_toFinset.mp (hs salt h hh))
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure] at ho
      subst ho
      change (s.1.1.cacheQuery x.1 x.2) (.digest salt h) ≠ none at hh
      by_cases hx : x.1 = .digest salt h
      · right
        simp [entrySalt, hx]
      · rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hx)] at hh
        exact Or.inl (List.mem_toFinset.mp (hs salt h hh))
  · rcases u with n | q | y
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨o, ho, rfl⟩ := hr
      exact digestLogged_local prims s hs (.inl n) o ho _ rfl
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨o, ho, rfl⟩ := hr
      exact digestLogged_local prims s hs (.inr (.inl q)) o ho _ rfl
    · by_cases hy : Hidden D y.1
      · simp only [streamWorld, if_pos hy, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨o, ho, rfl⟩ := hr
        intro salt h hh
        rw [logSalts_append, List.mem_toFinset, List.mem_append]
        exact Or.inl (List.mem_toFinset.mp (hs salt h hh))
      · simp only [streamWorld, if_neg hy, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨o, ho, rfl⟩ := hr
        exact digestLogged_local prims s hs (.inr (.inr y)) o ho _ rfl

theorem digestLogged_run (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) (hs : DigestLogged s) :
    ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) oa).run s), DigestLogged z.2 :=
  simulateQ_run_preserves_inv_of_query _ _ (fun t s hs z hz => digestLogged_step prims D t s hs z hz)
    oa s hs

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives)

/-- An invariant of every logged step holds after a counted prefix and the setup. -/
theorem setup_inv (D : C.Coalition) (Inv : TreeSimState C → Prop)
    (h0 : Inv (((∅, ∅), []) : TreeSimState C))
    (step : ∀ {β : Type} (oa : OracleComp (WorldSpec C) β) (s : TreeSimState C), Inv s →
      ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) oa).run s), Inv z.2)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) : Inv p.2 := by
  have h1 := step _ _ h0 s hs
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  have h2 := step _ _ h1 start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  exact step _ _ h2 p hp

end SetupState

/-! ## Public salts come from literal log pieces -/

section PublicSalts

open TreeRawSaltCertificatesProof

variable (prims : Primitives)

/-- Every public salt of the table run is the salt of a literal log piece. -/
def PublicLogged (state : CompilerState C) (used : SaltLists) : Prop :=
  ∀ v ∈ used.2, ∃ e, LogPiece.literal e ∈ state.2 ∧ entrySalt e = some v

set_option backward.isDefEq.respectTransparency false in
/-- A lifted probabilistic computation adds no public salt. -/
theorem tableRun_prob_used {α : Type} (p : ProbComp α) (used : SaltLists) (cache : HashCache C)
    (blocks : BlockCache C) :
    ∀ r ∈ support (tableRun prims (liftComp p (TableSpec C)) used cache blocks), r.1.2 = used := by
  induction p using OracleComp.inductionOn generalizing used cache blocks with
  | pure a =>
    intro r hr
    rw [liftComp_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    rfl
  | query_bind t k ih =>
    intro r hr
    rw [liftComp_bind, liftComp_query] at hr
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map] at hr
    change r ∈ support (tableRun prims (OracleComp.lift (OracleSpec.query (spec := TableSpec C)
      (.inr (.inl t))) >>= fun u => liftComp (k u) (TableSpec C)) used cache blocks) at hr
    rw [tableRun_bind, mem_support_bind_iff, tableRun_public] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    simp only [support_map, Set.mem_image] at hm
    obtain ⟨out, _, rfl⟩ := hm
    exact ih _ _ _ _ r hr

set_option backward.isDefEq.respectTransparency false in
theorem publicAnswer_used (D : C.Coalition) (t : (WorldSpec C).Domain) (state : CompilerState C)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C) r
    (hr : r ∈ support (tableRun prims ((publicAnswer D t).run state) used cache blocks)) :
    ∀ v ∈ r.1.2.2, v ∈ used.2 ∨ entrySalt ⟨t, r.1.1.1⟩ = some v := by
  have loc : ∀ (u : (LocalSpec C).Domain) r,
      r ∈ support (tableRun prims ((localQuery u).run state) used cache blocks) →
      ∀ v ∈ r.1.2.2, v ∈ used.2 ∨ digestSaltProjection u = some v := by
    intro u r hr v hv
    simp only [localQuery, StateT.run_lift, bind_pure_comp, tableRun_map, support_map,
      Set.mem_image] at hr
    obtain ⟨mid, hm, rfl⟩ := hr
    erw [tableRun_public, support_map] at hm
    obtain ⟨out, _, rfl⟩ := hm
    rcases List.mem_append.mp hv with hv | hv
    · exact Or.inr (Option.mem_toList.mp hv)
    · exact Or.inl hv
  rcases t with (u | prog) | (u | (q | x))
  · exact loc u r hr
  · simp only [publicAnswer, StateT.run_pure, tableRun, simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    exact fun v hv => Or.inl hv
  · exact loc (.inl u) r hr
  · exact loc (.inr (.inl q)) r hr
  · simp only [publicAnswer] at hr
    split_ifs at hr
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
        StateT.run_set, StateT.run_map, map_pure, bind_pure_comp,
        tableRun_map, support_map, Set.mem_image] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      obtain ⟨y, hy, rfl⟩ := hout
      intro v hv
      left
      rw [← tableRun_prob_used prims _ used cache blocks y hy]
      exact hv
    · exact loc (.inr (.inr x)) r hr

theorem pl_emit (piece : LogPiece C) : Preserves prims PublicLogged (emit piece) := by
  intro state used cache blocks h r hr
  simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hr
  subst r
  intro v hv
  obtain ⟨e, he, hs⟩ := h v hv
  exact ⟨e, List.mem_append_left _ he, hs⟩

theorem pl_publicQuery (D : C.Coalition) (t : (WorldSpec C).Domain) :
    Preserves prims PublicLogged (publicQuery D t) := by
  intro state used cache blocks h r hr
  simp only [publicQuery, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hm, hr⟩ := hr
  simp only [emit, StateT.run_modify, StateT.run_pure,
    tableRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
  obtain ⟨_, rfl, rfl⟩ := hr
  intro v hv
  rcases publicAnswer_used prims D t state used cache blocks mid hm v hv with old | new
  · obtain ⟨e, he, hs⟩ := h v old
    refine ⟨e, ?_, hs⟩
    rw [publicAnswer_log prims D t state used cache blocks mid hm]
    exact List.mem_append_left _ he
  · exact ⟨⟨t, mid.1.1.1⟩, List.mem_append_right _ (List.mem_singleton_self _), new⟩

set_option backward.isDefEq.respectTransparency false in
theorem pl_private (b : TreeSimHashSaltBlock C) (history : List Bit) :
    Preserves prims PublicLogged (StateT.lift (rowProgram (.inl b, history)) : CompilerM C HashOutput) := by
  intro state used cache blocks h r hr
  simp only [StateT.run_lift, bind_pure_comp, tableRun_map, support_map, Set.mem_image] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  simp only [rowProgram] at hout
  rw [tableRun_private, mem_support_bind_iff] at hout
  obtain ⟨salt, _, hout⟩ := hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨o, _, rfl⟩ := hout
  exact h

theorem pl_publicDraw (D : C.Coalition) (name : KeyName C) (key : HashOutput) (label : ℕ) :
    Preserves prims PublicLogged (publicDraw D name key label) :=
  Preserves.simulateQ prims _ _ (pl_publicQuery prims D)

theorem pl_prepareTerm (D : C.Coalition) (ctx : Context C) (label : ℕ) (T : C.Term) :
    Preserves prims PublicLogged (prepareTerm D ctx label T) := by
  unfold prepareTerm
  split_ifs
  · exact (pl_publicDraw prims D _ _ _).map prims _ _
  · exact (pl_emit prims _).bind prims _ _ (fun _ => Preserves.pure prims _)
  · exact Preserves.pure prims _

theorem pl_preparePairs (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    Preserves prims PublicLogged (preparePairs D ctx label) := by
  unfold preparePairs
  refine Preserves.bind prims (I := PublicLogged) _ _ ?_ ?_
  · apply Preserves.mapM prims (I := PublicLogged)
    intro j
    split_ifs
    · exact Preserves.pure prims _
    · exact pl_publicDraw prims D _ _ _
  · intro _
    exact Preserves.pure prims _

theorem pl_compileDigest (D : C.Coalition) (row : Row C) :
    Preserves prims PublicLogged (compileDigest D row) := by
  rcases row with ⟨b | salt, history⟩
  · exact (pl_private prims b history).bind prims _ _ (fun output =>
      (pl_emit prims _).bind prims _ _ (fun _ => Preserves.pure prims _))
  · exact Preserves.simulateQ prims _ _ (pl_publicQuery prims D)

theorem pl_boundaryCompiler (D : C.Coalition) (t : (BoundarySpec D).Domain) :
    Preserves prims PublicLogged (boundaryCompiler D t) := by
  cases t with
  | inl row =>
    unfold boundaryCompiler compileBoundaryDigest
    refine Preserves.bind prims (I := PublicLogged) _ _ ?_ ?_
    · exact Preserves.mapM prims _ _ (pl_prepareTerm prims D row.1 row.2.label)
    · intro terms
      apply (pl_preparePairs prims D row.1 row.2.label).bind prims
      intro _
      apply Preserves.mapM prims (I := PublicLogged)
      intro T
      split_ifs
      · exact pl_compileDigest prims D _
      · exact Preserves.pure prims _
  | inr t => exact pl_publicQuery prims D t.1

end PublicSalts

/-! ## The first-stage bound from the event transport -/

section Assembly

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Every salt point is open at the end of the setup. -/
theorem setup_open (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    ∀ y, (saltAt y).isSome → p.2.1.2 y = none := by
  have only := setup_inv prims D (HiddenOnly D) (fun y hy => (hy rfl).elim)
    (fun oa s hs => hiddenOnly_run prims D oa s hs) A x z pre s hs p hp
  intro y hy
  obtain ⟨⟨b, g⟩, hbg⟩ := Option.isSome_iff_exists.mp hy
  have hyb := saltAt_sound hbg
  subst hyb
  by_cases hk : KnownTo D.1 b.1
  · by_contra hne
    exact (only _ hne) hk
  · exact open_setup prims D A x z pre s hs p hp b hk g

/-- The stage-2 table selected by a stage view. It reads only the honest step states. -/
def secondOf (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (view : FirstView A) :=
  TreeSaltPairsFinal.secondSet circuits settings tree D x setup A
    (view, (((∅ : HashCache C), (∅ : HiddenCache C)), ([] : TreeSimLog C)))

/-- `crossWeight` of the entry `j` of the stage-2 table of a view, without the guards. -/
def crossPart (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (i j : ℕ)
    (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card)
    (view : FirstView A) (c : HashCache C × HiddenCache C) : ℝ≥0∞ :=
  if h : j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card <
      (secondOf circuits settings tree D A x setup view).card then
    crossWeight prims D
      (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩)
      (TreeSaltPairsFinal.enumerate (secondOf circuits settings tree D A x setup view)
        ⟨j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card, h⟩) c
  else 0

theorem stageWeight_eq (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (i j : ℕ)
    (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card)
    (m : TreeSimConfig A (TreeSimState C)) :
    stageWeight prims circuits settings tree D A x setup i j hi m =
      if FirstClean D (TreeSaltPairsFinal.enumerate
          (TreeSaltPairsFinal.firstSet circuits settings tree x setup)) m.2.2 then
        crossPart prims circuits settings tree D A x setup i j hi m.1 m.2.1
      else 0 := rfl

theorem secondOf_not_first (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (view : FirstView A)
    (y : C.Term × HashOutput × ℕ) (h : y ∈ secondOf circuits settings tree D A x setup view) :
    y ∉ TreeSaltPairsFinal.firstSet circuits settings tree x setup := by
  unfold secondOf TreeSaltPairsFinal.secondSet at h
  exact (Finset.mem_sdiff.mp h).2

/-- The `I`-average of `crossPart` is at most `2^-256` at every outcome of `I`. -/
theorem avg_part (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (i j : ℕ)
    (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card)
    (view : FirstView A) (cache : HashCache C) (rows : List (HashOutput × HashOutput))
    (blocks : BlockCache C)
    (ha : blocks (TreeSaltPairsFinal.enumerate
      (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩) = none)
    (called : Bool) (other : HiddenCache C) :
    ∑' s₁, Pr[= s₁ | ($ᵗ (Fin 256 → Bit) : ProbComp (Fin 256 → Bit))] *
      crossPart prims circuits settings tree D A x setup i j hi view
        (treeSimHashRowCache cache (List.ofFn s₁) rows,
          restore (if called then blocks.cacheQuery (TreeSaltPairsFinal.enumerate
            (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩) s₁ else blocks) other) ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  by_cases hc : j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card <
      (secondOf circuits settings tree D A x setup view).card
  · have e : ∀ c, crossPart prims circuits settings tree D A x setup i j hi view c =
        crossWeight prims D
          (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩)
          (TreeSaltPairsFinal.enumerate (secondOf circuits settings tree D A x setup view)
            ⟨j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card, hc⟩) c :=
      fun c => dif_pos hc
    simp only [e]
    have hmemS := TreeSaltPairsFinal.enumerate_mem (secondOf circuits settings tree D A x setup view)
      ⟨j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card, hc⟩
    have hmemF := TreeSaltPairsFinal.enumerate_mem
      (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩
    have hab : TreeSaltPairsFinal.enumerate (secondOf circuits settings tree D A x setup view)
        ⟨j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card, hc⟩ ≠
        TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩ := by
      intro h
      rw [h] at hmemS
      exact secondOf_not_first circuits settings tree D A x setup view _ hmemS hmemF
    exact le_of_eq (avg_cross prims D _ _ hab cache rows blocks ha called other)
  · have e : ∀ c, crossPart prims circuits settings tree D A x setup i j hi view c = 0 :=
      fun c => dif_neg hc
    simp only [e, mul_zero, tsum_zero]
    exact zero_le

/-- Event transport on the compiled first stage. On the compiled first stage from the setup state
`p`, a stage log with `FirstClean` excludes `HitA` of the hidden stage-1 entry `i`: its salt is not
a public digest salt, initial or later, and not the salt of another block. -/
def FirstTransport : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ i : ℕ, (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card) →
      ¬ KnownTo D.1
        (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)
          ⟨i, hi⟩).1 →
    ∀ r ∈ support (tableRun prims (firstCompiled K circuits settings top tree D A x p)
        ([], logSalts p.2.2) p.2.1.1 ∅),
      FirstClean D (TreeSaltPairsFinal.enumerate
          (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)) (decodeResult r).2.2 →
      ¬ HitA (TreeSaltPairsFinal.enumerate
          (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) r

/-- `CrossFirstStage` follows from the event transport `FirstTransport`. -/
theorem crossFirstStage_of_transport (transport : FirstTransport prims K circuits settings) :
    CrossFirstStage prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i j hi hj ka
  set F := TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2 with hF
  set a := TreeSaltPairsFinal.enumerate F ⟨i, hi⟩ with ha
  have hopen := setup_open prims D A x z pre s hs p hp
  have hcov0 : DigestLogged p.2 :=
    setup_inv prims D DigestLogged (fun salt h hh => (hh rfl).elim)
      (fun oa s hs => digestLogged_run prims D oa s hs) A x z pre s hs p hp
  have hlaw := first_law prims K circuits settings top tree D A x p hopen ([], logSalts p.2.2)
  let g : (FirstView A × CompilerState C) × HashCache C × BlockCache C → ℝ≥0∞ := fun o =>
    crossPart prims circuits settings tree D A x p.1.2 i j hi o.1.1 (o.2.1, restore o.2.2 o.1.2.1)
  let P := firstCompiled K circuits settings top tree D A x p
  calc ∑' m, Pr[= m | TreeSaltPairsFinal.first prims K circuits settings top tree D A x p] *
        stageWeight prims circuits settings tree D A x p.1.2 i j hi m
      = ∑' m, Pr[= m | decodeResult <$> tableRun prims P ([], logSalts p.2.2) p.2.1.1 ∅] *
          stageWeight prims circuits settings tree D A x p.1.2 i j hi m :=
        tsum_congr fun m => by rw [probOutput_congr rfl hlaw]
    _ = ∑' r, Pr[= r | tableRun prims P ([], logSalts p.2.2) p.2.1.1 ∅] *
          stageWeight prims circuits settings tree D A x p.1.2 i j hi (decodeResult r) :=
        tsum_probOutput_map_mul _ _ _
    _ ≤ ∑' r, Pr[= r | tableRun prims P ([], logSalts p.2.2) p.2.1.1 ∅] *
          (if HitA a r then 0 else g (r.1.1, r.2.1, r.2.2)) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (tableRun prims P ([], logSalts p.2.2) p.2.1.1 ∅)
        · refine mul_le_mul_right ?_ _
          rw [stageWeight_eq]
          split_ifs with clean hit
          · exact (transport hb top tree D A x z Z q hx hq hsmall pre s hs p hp i hi ka r hr
              clean hit).elim
          · exact le_rfl
          · exact zero_le
          · exact zero_le
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ ∑' r, Pr[= r | (simulateQ (iAnswer prims a) P).run ((p.2.1.1, []), ∅, false)] *
          ∑' s₁, Pr[= s₁ | ($ᵗ (Fin 256 → Bit) : ProbComp (Fin 256 → Bit))] * g (fill a s₁ r) :=
        before prims a g P ([], logSalts p.2.2) p.2.1.1 ∅ rfl
          ⟨hcov0, fun v hv => absurd hv List.not_mem_nil⟩
    _ ≤ ∑' r, Pr[= r | (simulateQ (iAnswer prims a) P).run ((p.2.1.1, []), ∅, false)] *
          (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support ((simulateQ (iAnswer prims a) P).run ((p.2.1.1, []), ∅, false))
        · refine mul_le_mul_right ?_ _
          exact avg_part prims circuits settings tree D A x p.1.2 i j hi r.1.1 r.2.1.1 r.2.1.2
            r.2.2.1 (iRun_target prims a P _ rfl r hr) r.2.2.2 r.1.2.1
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

/-- The original cross-pair bound `CrossHiddenBound` (A118) follows from `FirstTransport`. -/
theorem crossHiddenBound_of_transport (transport : FirstTransport prims K circuits settings) :
    CrossHiddenBound prims K circuits settings :=
  crossHiddenBound_of_firstStage prims K circuits settings
    (crossFirstStage_of_transport prims K circuits settings transport)

/-- The guarded pair bounds `PairBoundsGuardedFrom` follow from `FirstTransport`. -/
theorem pairBoundsGuardedFrom_of_transport (transport : FirstTransport prims K circuits settings) :
    LifetimeSaltGuarded.PairBoundsGuardedFrom prims K circuits settings :=
  pairBoundsGuardedFrom_of_cross prims K circuits settings
    (crossHiddenBound_of_transport prims K circuits settings transport)

/-! ### The transport off the literal digests -/

theorem ofFn_getD (w : Fin 256 → Bit) (g : Fin 256) : (List.ofFn w).getD g.val 0 = w g := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact g.isLt), List.getElem_ofFn]

theorem projection_some (u : (LocalSpec C).Domain) (salt : List Bit)
    (h : digestSaltProjection u = some salt) : ∃ hist, u = .inr (.inl (.digest salt hist)) := by
  rcases u with n | q | y
  · simp [digestSaltProjection] at h
  · cases q <;> simp_all [digestSaltProjection]
  · simp [digestSaltProjection] at h

/-- The public salts of the compiled first stage are salts of literal log pieces. -/
theorem firstCompiled_publicLogged (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    ∀ r ∈ support (tableRun prims (firstCompiled K circuits settings top tree D A x p)
      ([], logSalts p.2.2) p.2.1.1 ∅), PublicLogged r.1.1.2 r.1.2 := by
  intro r hr
  refine TreeRawSaltCertificatesProof.Preserves.simulateQ prims (boundaryCompiler D)
    (firstBoundary K circuits settings top tree D A x p) (pl_boundaryCompiler prims D)
    (p.2.1.2, p.2.2.map .literal) ([], logSalts p.2.2) p.2.1.1 ∅ ?_ r hr
  intro v hv
  obtain ⟨e, he, hs⟩ := List.mem_filterMap.mp hv
  exact ⟨e, List.mem_map.mpr ⟨e, he, rfl⟩, hs⟩

/-- On a clean first stage, two different stage-1 entries with a hidden one read different salts. -/
theorem clean_no_reuse (D : C.Coalition) (F : Finset (C.Term × HashOutput × ℕ)) (log : TreeSimLog C)
    (clean : FirstClean D (TreeSaltPairsFinal.enumerate F) log) (k₁ k₂ : Fin F.card) (hne : k₁ ≠ k₂)
    (hidden : ¬ KnownTo D.1 (TreeSaltPairsFinal.enumerate F k₁).1) (salt : List Bit)
    (hlen : salt.length = 256) (h₁ : TreeSaltAt log (TreeSaltPairsFinal.enumerate F k₁) salt)
    (h₂ : TreeSaltAt log (TreeSaltPairsFinal.enumerate F k₂) salt) : False := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact clean.2.2 k₁.val k₂.val hlt ⟨k₁.isLt, k₂.isLt, salt, hlen, Or.inl hidden, h₁, h₂⟩
  · exact clean.2.2 k₂.val k₁.val hlt ⟨k₂.isLt, k₁.isLt, salt, hlen, Or.inr hidden, h₂, h₁⟩

/-- Every literal digest piece at the target salt is a counted query, on the clean compiled first
stage from a setup state. -/
def LiteralTransport : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ i : ℕ, (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card) →
      ¬ KnownTo D.1
        (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)
          ⟨i, hi⟩).1 →
    ∀ r ∈ support (tableRun prims (firstCompiled K circuits settings top tree D A x p)
        ([], logSalts p.2.2) p.2.1.1 ∅),
      FirstClean D (TreeSaltPairsFinal.enumerate
          (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)) (decodeResult r).2.2 →
      ∀ v, r.2.2 (TreeSaltPairsFinal.enumerate
          (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) = some v →
      ∀ e, LogPiece.literal e ∈ r.1.1.2.2 → entrySalt e = some (List.ofFn v) →
        ∃ u, e.1 = .inl (.inl u)

set_option backward.isDefEq.respectTransparency false in
/-- `FirstTransport` follows from `LiteralTransport`. A read block is a hidden read in the
decoded log, so a block hit is a reuse of two stage-1 entries, and a counted digest hit is a
salt guess. -/
theorem firstTransport_of_literal (literal : LiteralTransport prims K circuits settings) :
    FirstTransport prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i hi ka r hr clean ⟨v, hav, hit⟩
  set F := TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2 with hF
  have hopen := setup_open prims D A x z pre s hs p hp
  have hlaw := first_law prims K circuits settings top tree D A x p hopen ([], logSalts p.2.2)
  have hm : decodeResult r ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p) := by
    rw [mem_support_iff, probOutput_congr rfl hlaw, ← mem_support_iff, support_map]
    exact ⟨r, hr, rfl⟩
  have hcoh := hiddenCoherent_first prims K circuits settings top tree D A x p
    (hiddenCoherent_setup prims D A x z pre s hs p hp) _ hm
  have honly : HiddenOnly D (decodeResult r).2 := by
    have h0 := setup_inv prims D (HiddenOnly D) (fun y hy => (hy rfl).elim)
      (fun oa s hs => hiddenOnly_run prims D oa s hs) A x z pre s hs p hp
    rw [first_eq] at hm
    exact hiddenOnly_run prims D _ p.2 h0 _ hm
  have agree := TreeSaltPairsFinal.first_agreement_from prims K circuits settings top tree D A x z hx
    pre s hs p hp _ hm clean.1
  -- A read block is a hidden read of its salt in the decoded log, at a stage-1 address.
  have read : ∀ b w, r.2.2 b = some w → ¬ KnownTo D.1 b.1 ∧
      TreeSaltAt (decodeResult r).2.2 b (List.ofFn w) ∧ b ∈ F := by
    intro b w hbw
    have cached : ∀ g : Fin 256, (decodeResult r).2.1.2 (saltPoint b g) = some (w g) := by
      intro g
      change restore r.2.2 r.1.1.2.1 (treeSimHashSaltAddress b g) = some (w g)
      rw [restore_address, hbw]
      rfl
    have hid : ¬ KnownTo D.1 b.1 := honly (saltPoint b ⟨0, by decide⟩) (by rw [cached]; simp)
    have at_b : TreeSaltAt (decodeResult r).2.2 b (List.ofFn w) := by
      intro g
      rw [ofFn_getD]
      exact (hcoh (.term b.1, b.2.1, b.2.2, 2, g.val) (w g) hid).mpr (cached g)
    refine ⟨hid, at_b, ?_⟩
    exact TreeSaltPairsFinal.agreement_mem _ _ _ agree b.1 b.2.1 b.2.2 0 _ (at_b ⟨0, by decide⟩)
  obtain ⟨-, at_a, -⟩ := read _ v hav
  have hlen : (List.ofFn v).length = 256 := List.length_ofFn
  rcases hit with pub | ⟨b, hba, hbv⟩
  · obtain ⟨e, he, hes⟩ := firstCompiled_publicLogged prims K circuits settings top tree D A x p r hr _ pub
    obtain ⟨u, hu⟩ := literal hb top tree D A x z Z q hx hq hsmall pre s hs p hp i hi ka r hr clean v
      hav e he hes
    obtain ⟨t, out⟩ := e
    simp only at hu
    subst hu
    obtain ⟨hist, rfl⟩ := projection_some u _ hes
    have hmem : (⟨.inl (.inl (.inr (.inl (.digest (List.ofFn v) hist)))), out⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ (decodeResult r).2.2 :=
      List.mem_flatMap.mpr ⟨_, he, List.mem_singleton_self _⟩
    exact clean.2.1 ⟨List.ofFn v, hist, out, ⟨hlen, _, _, _, ka, at_a⟩, hmem⟩
  · obtain ⟨-, at_b, hbF⟩ := read b v hbv
    obtain ⟨k, hk⟩ := TreeSaltPairsFinal.mem_enumerate F b hbF
    have hne : (⟨i, hi⟩ : Fin F.card) ≠ k := by
      rintro rfl
      exact hba hk.symm
    refine clean_no_reuse D F _ clean ⟨i, hi⟩ k hne ka _ hlen at_a ?_
    rw [hk]
    exact at_b

/-- `CrossFirstStage` follows from `LiteralTransport`. -/
theorem crossFirstStage_of_literal (literal : LiteralTransport prims K circuits settings) :
    CrossFirstStage prims K circuits settings :=
  crossFirstStage_of_transport prims K circuits settings
    (firstTransport_of_literal prims K circuits settings literal)

/-- The cross-pair bound `CrossHiddenBound` (A118) follows from `LiteralTransport`. -/
theorem crossHiddenBound_of_literal (literal : LiteralTransport prims K circuits settings) :
    CrossHiddenBound prims K circuits settings :=
  crossHiddenBound_of_transport prims K circuits settings
    (firstTransport_of_literal prims K circuits settings literal)

/-- The guarded pair bounds `PairBoundsGuardedFrom` follow from `LiteralTransport`. -/
theorem pairBoundsGuardedFrom_of_literal (literal : LiteralTransport prims K circuits settings) :
    LifetimeSaltGuarded.PairBoundsGuardedFrom prims K circuits settings :=
  pairBoundsGuardedFrom_of_transport prims K circuits settings
    (firstTransport_of_literal prims K circuits settings literal)

end Assembly

end ThresholdLeanXmssSecurity.TreeSaltFirstStage


/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.first_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.first_law

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.after

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.before

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.avg_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.avg_cross

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossFirstStage_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossFirstStage_of_transport

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossHiddenBound_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossHiddenBound_of_transport

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.pairBoundsGuardedFrom_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.pairBoundsGuardedFrom_of_transport

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.firstTransport_of_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.firstTransport_of_literal

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossFirstStage_of_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossFirstStage_of_literal

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossHiddenBound_of_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.crossHiddenBound_of_literal

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltFirstStage.pairBoundsGuardedFrom_of_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltFirstStage.pairBoundsGuardedFrom_of_literal
