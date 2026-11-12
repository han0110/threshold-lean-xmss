import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkRecipe

/-!
# Draw shapes, query bounds and finished states of the fixed walk

This module works on the fixed family `TreeCheckWalkRecipe.family` and its GS20
check adapter `TreeCheckWalkRecipe.checkAdversary`.

## Draw shapes

* `check_shapedGadgets` says that the real `check` calls its gadgets only with
  one coin, two products, two field elements and 256 bits.
* `realCheckGadgets_shapes` says that at these shapes the real gadgets draw
  `Rand(ρ, 1)` for the coin and the field elements, `Rand(ρ, 0)` for the
  products and `Rand(ρ, 2)` for the bits.
* `bitRow_replay` and `fieldRow_replay` say that a visible block under a cached
  stream key replays as the adapter rows `bitRow` and `fieldRow`.
* `streamKey_pair` says that a pair with a corrupt endpoint uses the key of its
  honest endpoint. `streamKey_term` says that the `refHolder` term key is the
  key of each honest holder when the honest holders agree on it.

## Hybrid clauses

* `walkQueries` proves `Queries` of the family. The coin and peer simulators run
  one round of the original adversary. All other adapter steps are pure rows
  or private samples.
* `dummyHybrid_event` says that the hybrid check of a finished cut state accepts
  with probability one.
* `WalkCheckpointCache` and `WalkCheckpointTransport` are the `Cache` and
  `Transport` clauses of `WalkHybrid` at the batch checkpoints of the family.
* `walkHybrid_of_checkpoints` proves `WalkHybrid` from these two clauses.

The pinned leanVM proofs were searched for the query-bound helpers.
`liftComp_counted` restates `isQueryBoundP_liftComp_counted` of `KeygenHalves`,
which is outside the import closure of this module.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkTransport

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Shapes

variable {ι : Type} {G : OracleSpec ι}

/-- The gadgets `g` restricted to one coin, two products, two field elements
and 256 bits. Every other argument fails. -/
def shapedGadgets (g : CheckGadgets C E G) : CheckGadgets C E G where
  coin count := if count = 1 then g.coin count else StateT.lift failure
  extendMult products := if products.length = 2 then g.extendMult products else StateT.lift failure
  randElements count := if count = 2 then g.randElements count else StateT.lift failure
  randBits count := if count = 256 then g.randBits count else StateT.lift failure

/-- The check calls its gadgets only with these shapes. -/
theorem check_shapedGadgets (K : Constants C E) (ctx : Context C) (g : CheckGadgets C E G)
    (tuples : List (Tuple C)) :
    check K ctx (shapedGadgets g) tuples = check K ctx g tuples := rfl

/-- At these shapes the real gadgets draw `Rand(ρ, 1)` for the coin and the
field elements, `Rand(ρ, 0)` for two products and `Rand(ρ, 2)` for 256 bits. -/
theorem realCheckGadgets_shapes (K : Constants C E) (ctx : Context C) :
    (realCheckGadgets (G := G) K ctx).coin 1 =
        (prssRandomness ctx (elementCodec K) 1 1 >>= fun randomness => coinWith K ctx randomness 1) ∧
      (∀ products : List (Product C E), products.length = 2 →
        (realCheckGadgets (G := G) K ctx).extendMult products =
          (prssRandomness ctx (elementCodec K) 0 2 >>= fun randomness =>
            reshare K ctx (elementCodec K) randomness
              (fun g => match products[g]? with | some p => productShare K ctx p | none => 0) 2)) ∧
      (realCheckGadgets (G := G) K ctx).randElements 2 = prssRandomness ctx (elementCodec K) 1 2 ∧
      (realCheckGadgets (G := G) K ctx).randBits 256 = prssRandomness ctx bitCodec 2 256 := by
  refine ⟨rfl, fun products length => ?_, rfl, rfl⟩
  simp only [realCheckGadgets, length]
  rfl

end Shapes

section Rows

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

/-- `knownRows` reads a term only when a corrupt operator holds it. Such a term
is visible. -/
theorem term_visible (T : C.Term) (known : KnownTo D.1 T) : ¬ Hidden D (.term T) :=
  fun hidden => hidden known

/-- `knownRows` reads a pair only when one endpoint is corrupt. Such a pair is
visible. -/
theorem pair_visible (i j : C.Party) (ne : i ≠ j) (corrupt : j ∈ D.1) :
    ¬ Hidden D (.pair (C.pairOf i j ne)) := by
  unfold Hidden Committee.pairOf
  by_cases order : i < j
  · simp only [dif_pos order]
    exact fun hidden => hidden.2 corrupt
  · simp only [dif_neg order]
    exact fun hidden => hidden.1 corrupt

/-- A pair with a corrupt endpoint is read with the key of its honest endpoint. -/
theorem streamKey_pair (prss : C.Party → PrssKeys C) (i j : C.Party) (ne : i ≠ j)
    (honest : i ∉ D.1) (corrupt : j ∈ D.1) :
    TreeCheckWalkRecipe.streamKey D prss (.pair (C.pairOf i j ne)) = (prss i).pair j := by
  unfold TreeCheckWalkRecipe.streamKey Committee.pairOf
  by_cases order : i < j
  · simp only [dif_pos order, if_pos honest]
  · simp only [dif_neg order, if_neg (fun h : j ∉ D.1 => h corrupt)]

/-- A term is read with the key of `refHolder`. It is the key of every honest
holder when the honest holders agree on the term key. -/
theorem streamKey_term (prss : C.Party → PrssKeys C) (T : C.Term) (i : C.Party)
    (honest : i ∉ D.1) (held : i ∈ C.holders T)
    (agree : ∀ a b, a ∉ D.1 → b ∉ D.1 → a ∈ C.holders T → b ∈ C.holders T →
      (prss a).term T = (prss b).term T) :
    TreeCheckWalkRecipe.streamKey D prss (.term T) = (prss i).term T := by
  obtain ⟨refHeld, refHonest⟩ := refHolder_spec D T
  exact agree _ _ refHonest honest refHeld held

/-- A visible bit block (`bitCodec.draw` is `prgBits`) under a cached stream key
replays as `bitRow`. -/
theorem bitRow_replay (prss : C.Party → PrssKeys C) (h : HashCache C) (cache : HiddenCache C)
    (name : KeyName C) (visible : ¬ Hidden D name) (derived : HashOutput)
    (cached : h (.streamKey (TreeCheckWalkRecipe.streamKey D prss name)) = some derived)
    (label idx count : ℕ) :
    (simulateQ (streamWorld prims D) (free (liftComp
      (prgBits name (TreeCheckWalkRecipe.streamKey D prss name) label idx count)
        (LocalSpec C)))).run (h, cache) =
      pure (TreeCheckWalkRecipe.bitRow prims D prss h label idx count name, (h, cache)) := by
  have ready : TreeSimStreamReady prims D name (TreeCheckWalkRecipe.streamKey D prss name)
      label idx count (fun g => prims.aes.eval (truncateHash derived) (label, idx, g)) h cache := by
    unfold TreeSimStreamReady
    rw [if_neg visible]
    exact ⟨derived, cached, fun _ _ => rfl⟩
  rw [treeSim_prgBits_ready prims D _ _ _ _ _ _ h cache ready]
  unfold TreeCheckWalkRecipe.bitRow
  rw [cached, Option.getD_some]

/-- A visible field block under a cached stream key replays as `fieldRow`. -/
theorem fieldRow_replay (prss : C.Party → PrssKeys C) (h : HashCache C) (cache : HiddenCache C)
    (name : KeyName C) (visible : ¬ Hidden D name) (derived : HashOutput)
    (cached : h (.streamKey (TreeCheckWalkRecipe.streamKey D prss name)) = some derived)
    (label idx count : ℕ) :
    (simulateQ (streamWorld prims D) (free (liftComp
      ((elementCodec K).draw name (TreeCheckWalkRecipe.streamKey D prss name) label idx count)
        (LocalSpec C)))).run (h, cache) =
      pure (TreeCheckWalkRecipe.fieldRow prims K D prss h label idx count name, (h, cache)) := by
  have ready : TreeSimStreamReady prims D name (TreeCheckWalkRecipe.streamKey D prss name)
      label idx (elementBits * count) (fun g => prims.aes.eval (truncateHash derived) (label, idx, g))
      h cache := by
    unfold TreeSimStreamReady
    rw [if_neg visible]
    exact ⟨derived, cached, fun _ _ => rfl⟩
  rw [treeSim_elementDraw_ready prims K D _ _ _ _ _ _ h cache ready]
  unfold TreeCheckWalkRecipe.fieldRow
  rw [cached, Option.getD_some]

end Rows

section Queries

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- A private sample makes no counted call. -/
theorem liftComp_counted {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) Counted 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [Counted]), fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

theorem bind_counted {α β : Type} {oa : OracleComp (LocalSpec C) α}
    {ob : α → OracleComp (LocalSpec C) β} {n : ℕ} (first : IsQueryBoundP oa Counted 0)
    (rest : ∀ a, IsQueryBoundP (ob a) Counted n) : IsQueryBoundP (oa >>= ob) Counted n := by
  simpa only [Nat.zero_add] using isQueryBoundP_bind first fun a _ => rest a

theorem bind_pure_counted {α β : Type} {oa : OracleComp (LocalSpec C) α} (f : α → β) {n : ℕ}
    (first : IsQueryBoundP oa Counted n) :
    IsQueryBoundP (oa >>= fun a => pure (f a)) Counted n := by
  simpa only [Nat.add_zero] using isQueryBoundP_bind first fun a _ => isQueryBoundP_pure _ (f a) 0

-- The adapter samples with the local instance of `TreeCheckWalkRecipe`.
attribute [local instance] TreeCheckWalkRecipe.instSampleableType_thresholdLeanXmssSecurity
-- A bound on a concrete simulator answer otherwise unfolds the uniform samplers.
attribute [local irreducible] IsQueryBoundP

/-- The coin simulator on the adapter's rows makes the counted calls of one
round of the original adversary. -/
theorem coinAnswer_counted (x : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (cache : HashCache C) (label step : ℕ) (values : List E)
    (state : A.State) (rounds : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (coinSimAnswer K D
      (TreeCheckWalkRecipe.randomAdversary prims K D A x prss cache label 1 values.length)
      values.length values state) Counted step := by
  unfold coinSimAnswer
  generalize ($ᵗ (C.Term → Fin values.length → E) : ProbComp _) = terms
  generalize ($ᵗ (C.Pair → Fin values.length → E) : ProbComp _) = pairs
  refine bind_counted (isQueryBoundP_pure _ _ 0) fun _ => ?_
  refine bind_counted (liftComp_counted terms) fun _ => ?_
  refine bind_counted (liftComp_counted pairs) fun _ => ?_
  exact bind_pure_counted _ (rounds _ _)

/-- The peer-reshare simulator on the adapter's rows makes the counted calls of
one round of the original adversary. -/
theorem peerAnswer_counted (x : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (cache : HashCache C) (label step : ℕ) (state : A.State)
    (rounds : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    IsQueryBoundP (peerSimAnswer K D
      (TreeCheckWalkRecipe.randomAdversary prims K D A x prss cache label 0 2)
      (elementCodec K) 2 state) Counted step := by
  unfold peerSimAnswer
  generalize ($ᵗ (C.Term → Fin 2 → E) : ProbComp _) = terms
  generalize ($ᵗ (C.Pair → Fin 2 → E) : ProbComp _) = pairs
  refine bind_counted (isQueryBoundP_pure _ _ 0) fun _ => ?_
  refine bind_counted (liftComp_counted terms) fun _ => ?_
  refine bind_counted (liftComp_counted pairs) fun _ => ?_
  exact bind_pure_counted _ (rounds _ _)

/-- Each round and each answer of the check adapter makes at most one round of
counted calls of the original adversary. The simulator answers use only pure
cached-key rows and private samples. -/
theorem checkAdversary_queries (x : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (cache : HashCache C) (initialLabel step : ℕ)
    (rounds : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    (∀ state sent, IsQueryBoundP
      ((TreeCheckWalkRecipe.checkAdversary prims K D A x prss cache initialLabel).round state sent)
        Counted step) ∧
    (∀ state l, IsQueryBoundP
      ((TreeCheckWalkRecipe.checkAdversary prims K D A x prss cache initialLabel).answer state l)
        Counted step) := by
  refine ⟨fun state sent => (isQueryBoundP_map_iff _ _ _).2 (rounds state.1 sent), ?_⟩
  intro state l
  cases l with
  | inl l =>
    cases l with
    | inl values =>
      simp only [TreeCheckWalkRecipe.checkAdversary]
      exact bind_pure_counted _ (coinAnswer_counted prims K D A
        x prss cache state.2 step values state.1 rounds)
    | inr products =>
      simp only [TreeCheckWalkRecipe.checkAdversary]
      exact bind_pure_counted _ (peerAnswer_counted prims K D A
        x prss cache state.2 step state.1 rounds)
  | inr l =>
    cases l with
    | inl _ => exact isQueryBoundP_pure _ _ _
    | inr _ => exact isQueryBoundP_pure _ _ _

end Queries

section Finished

variable (prims : Primitives) (K : Constants C E)

/-- The check of no tuple accepts at once. -/
theorem check_nil_run {I O : Type} (ctx : Context C) (g : CheckGadgets C E (CallSpec I O))
    (state : RunState C) : (check K ctx g []).run' state = terminalProgram (some ()) := by
  unfold check
  simp [terminalProgram]

/-- The hybrid check of a finished cut state accepts with probability one. -/
theorem dummyHybrid_event (D : C.Coalition) :
    (treeCheckDummyHybrid (C := C) (E := E)).event prims K D = 1 := by
  unfold TreeCheckHybrid.event
  simp only [treeCheckDummyHybrid, check_nil_run, executePhase_terminal, simulateQ_pure,
    StateT.run_pure]
  rw [probEvent_pure, if_pos]
  obtain ⟨i, honest⟩ := exists_honest D
  refine ⟨fun ⟨_, _, _, _, _, empty, _⟩ => ?_, i, honest, if_neg honest⟩
  simp [splitRegionCache] at empty

end Finished

section Family

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `Queries` of `WalkHybrid`. At every cut state of the fixed family, each
hybrid round and answer stays within the round bound `step` of the original
query bound. -/
def WalkQueries : Prop :=
  TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    (W.cut prims K circuits settings D Z).Queries prims K circuits settings top tree D A x z j

theorem walkQueries : WalkQueries prims K circuits settings := by
  intro _ top tree D A x z Z q _ bounded _ j p _
  rintro (⟨c, o⟩ | r) _ _
  · exact checkAdversary_queries prims K D A x _ _ _ _ (TreeCheckQueryBudget.ofBound bounded).rounds
  · exact ⟨fun _ _ => isQueryBoundP_pure _ _ _, fun _ _ => isQueryBoundP_pure _ _ _⟩

/-- `Cache` of `WalkHybrid` at the batch checkpoints of the fixed family. The
cache, `seen` set, label and keys are those of the family's hybrid adapter. -/
def WalkCheckpointCache : Prop :=
  TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    ∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
      ∀ c o, s = .inl (c, o) →
        SoundCache ((W.cut prims K circuits settings D Z).hybrid s).label
          ((W.cut prims K circuits settings D Z).hybrid s).cache
          ((W.cut prims K circuits settings D Z).hybrid s).seen
          ((W.cut prims K circuits settings D Z).hybrid s).keys

/-- `Transport` of `WalkHybrid` at the batch checkpoints of the fixed family. The
real check after the checkpoint is at most the family's GS20 hybrid check. -/
def WalkCheckpointTransport : Prop :=
  TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    ∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
      ∀ c o, s = .inl (c, o) →
        Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
            ¬ TreeCheckUncounted D r.2 | (W.cut prims K circuits settings D Z).cont s] ≤
          ((W.cut prims K circuits settings D Z).hybrid s).event prims K D

set_option maxRecDepth 2000 in
set_option linter.constructorNameAsVariable false in
/-- `WalkHybrid` follows from the checkpoint cache and transport clauses, with
`walkQueries` and the finished cut states. -/
theorem walkHybrid_of_checkpoints
    (cache : WalkCheckpointCache prims K circuits settings)
    (transport : WalkCheckpointTransport prims K circuits settings) :
    TreeCheckWalkRecipe.WalkHybrid prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  refine ⟨walkQueries prims K circuits settings hb top tree D A x z Z q dealt bounded small j p hp,
    ?_, ?_⟩
  · rintro (⟨c, o⟩ | r) run live
    · have atCheckpoint := cache hb top tree D A x z Z q dealt bounded small j p hp
      with_reducible exact atCheckpoint _ run live c o rfl
    · exact ⟨fun _ _ _ _ cached => (cached rfl).elim, fun _ _ cached => (cached rfl).elim⟩
  · rintro (⟨c, o⟩ | r) run live
    · have atCheckpoint := transport hb top tree D A x z Z q dealt bounded small j p hp
      with_reducible exact atCheckpoint _ run live c o rfl
    · change _ ≤ (treeCheckDummyHybrid (C := C) (E := E)).event prims K D
      rw [dummyHybrid_event]
      exact probEvent_le_one

end Family

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.check_shapedGadgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_shapedGadgets

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.realCheckGadgets_shapes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realCheckGadgets_shapes

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.term_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms term_visible

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.pair_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_visible

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.streamKey_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms streamKey_pair

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.streamKey_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms streamKey_term

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.bitRow_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bitRow_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.fieldRow_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldRow_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.checkAdversary_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checkAdversary_queries

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.walkQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkQueries

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.dummyHybrid_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dummyHybrid_event

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTransport.walkHybrid_of_checkpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkHybrid_of_checkpoints

end TreeCheckWalkTransport
end ThresholdLeanXmssSecurity
