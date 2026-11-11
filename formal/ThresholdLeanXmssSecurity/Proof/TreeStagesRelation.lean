import ThresholdLeanXmssSecurity.Proof.TreeCompose
import ThresholdLeanXmssSecurity.Proof.TreeEvents

/-!
# The stages relation for the corrected events

`TreeSimStagesFinish.lean` reduces `TreeSimStagesGoal` to a round-indexed relation. This file
moves that reduction to the events `treeSimEvents2` of `TreeEvents.lean`, and it gives the
transfer of one round from equal public caches to swapped public caches.

* `treeSimStagesGoal2_of_relation` gives `TreeSimStagesGoal2` from `TreeSimStagesRelationGoal2`.
* `treeStages_round_twin` runs one round of the real program on a state and on its twin, the
  state with swapped public cache. The results are equal, or the log has a salt guess, or an
  honest operator queries a digest at a swapped salt.
* `treeStages_swap_transfer` composes this with an equal-cache round coupling of the twin, and
  `treeStages_round_swap` applies it to one round with `TreeSimBad2`. `treeCompose_swapRel` does
  not fit here. Its twin does not keep the real log, and its results must be equal.
* `TreeStagesTwinRelation` is the remaining equal-cache relation `Req` on the twins.
  `treeStages_relation_of_twin` builds the relation `R` of the stages from it, and
  `treeSimStagesGoal2_of_twinRelation` gives `TreeSimStagesGoal2`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The core of `treeStages_badCore` for `TreeSimBad2`. -/
def treeStages_badCore2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (bad : TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z s.2) :
    TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z dealt state s
      (fun t => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2) where
  Inv _ _ := False
  stage _ := .ceremony
  entry p hp := by
    have hpref : s.2 <+: p.2.2 := by
      apply treeSimLoggedWorld_prefix prims D
        (executePhase worldRoles D A noFunctionality 3 state
          (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))) s p
      simpa only [simulateQ_executePhase, treeSimRealRoles] using hp
    apply relTriple_of_support_left
    intro a ha b
    apply Or.inl
    exact treeSimBad2_mono prims K circuits settings top tree D A _ z
      (hpref.trans (treeSimLoggedWorld_prefix prims D _ p.2 a ha)) bad
  noSetup _ _ h := h.elim
  done _ _ h := h.elim
  outputEvidence _ _ h := h.elim
  peerBoundary _ _ _ h := h.elim
  collectorBoundary _ _ _ h := h.elim
  collectorNextBoundary _ _ _ h := h.elim
  rerandBoundary _ _ _ h := h.elim
  coinBoundary _ _ _ h := h.elim
  extendMultBoundary _ _ _ h := h.elim
  checkBoundary _ _ _ h := h.elim
  openingBoundary _ _ _ h := h.elim
  emptyOpeningBoundary _ _ _ h := h.elim
  ceremony _ _ _ h := h.elim

/-- The stages of `treeSimEvents2` from a round-indexed relation on reachable real
configurations, as `treeStages_roundStages_of_reachable_relation`. The relation may end with a digest swap in the public caches.
Replay, empty corrupt outputs, sticky events and final observation are proved
here. -/
def treeStages_roundStages_of_reachable_relation2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (R : ℕ → TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
      RelTriple
        ((simulateQ (treeSimLoggedWorld prims D)
          (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
        ((simulateQ (streamWorld prims D)
          (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
            (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
        (fun a b => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
          R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2)))
    (agree : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      a.1.1 = b.1.1 ∧ TreeStagesSwapCache D a.2 b.2 ∧
      (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
      (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome))
    (progress : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings)
    (next : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 →
      RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
        (fun u v => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
          R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))) :
    TreeSimRoundStages prims K circuits settings (treeSimEvents2 prims K circuits settings)
      top tree D A parameter seeds pairs z Z p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) where
  Bad t := TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2
  Inv a b := ∃ n, n + 3 ≤ ceremonyFuel circuits settings ∧
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a ∧ R n a b
  stage _ := .ceremony
  Q := TreeStagesSwapFinal D A p.1.1
  entry u hu := by
    apply relTriple_post_mono (treeSim_relTriple_support (entry u hu))
    intro a b hab
    rcases hab.1 with bad | rel
    · exact Or.inl bad
    · refine Or.inr ⟨0, ?_, ?_, rel⟩
      · unfold ceremonyFuel setupRounds
        omega
      · exact treeStages_reach_entry prims K circuits settings top tree D A _ _ _ u hu a hab.2.1
  noSetup _ _ _ _ := by intro h; cases h
  badPersistent _ _ hp := treeSimBad2_mono prims K circuits settings top tree D A _ z hp
  done a b hab good := by
    obtain ⟨n, _, reach, rel⟩ := hab
    exact (agree n a b rel reach good).2.2.1
  output a b hab good := by
    obtain ⟨n, bound, reach, rel⟩ := hab
    obtain ⟨state, cache, _, success⟩ := agree n a b rel reach good
    refine ⟨state, ?_, cache⟩
    exact treeStages_outputs_of_replay prims K circuits settings top tree D A parameter seeds pairs z p.1
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      (treeStages_reach_outputWitness prims K circuits settings top tree D A parameter seeds pairs z
        p hp padding r hr n bound a reach)
      (fun h => good (treeSimBad2_of_bad prims K circuits settings top tree D A _ z _ h))
      (treeStages_reach_corrupt prims K circuits settings top tree D A _ _ _ n a reach) success
  peerBoundary _ _ h := by cases h
  collectorBoundary _ _ h := by cases h
  collectorNextBoundary _ _ h := by cases h
  rerandBoundary _ _ h := by cases h
  coinBoundary _ _ h := by cases h
  extendMultBoundary _ _ h := by cases h
  checkBoundary _ _ h := by cases h
  openingBoundary _ _ h := by cases h
  emptyOpeningBoundary _ _ h := by cases h
  ceremony a b _ hab good active := by
    obtain ⟨n, bound, reach, rel⟩ := hab
    apply relTriple_post_mono (treeSim_relTriple_support (next n a b rel reach bound good active))
    intro u v huv
    rcases huv.1 with bad | rel'
    · exact Or.inl bad
    · exact Or.inr ⟨n + 1, progress n a b rel reach bound good active,
        treeStages_reach_step prims K circuits settings top tree D A _ _ _ n a reach active u huv.2.1, rel'⟩
  observeGood a b hab := by
    apply relTriple_post_mono (treeStages_observe_swapFinal prims D A Z p.1.1 a b hab)
    intro x y hx
    rcases hx with bad | eq
    · exact Or.inl (Or.inl (by simp [treeSimEvents2, TreeSimHashBad2, bad]))
    · exact Or.inr (by rw [eq])
  badRecorded t ht := (treeSimEvents2_bad prims K circuits settings top tree D A _ z Z t.2).mpr ht

/-- The remaining ceremony relation at one good prefix and one padded cache.
It drives `treeStages_roundStages_of_reachable_relation2`. -/
structure TreeStagesRelation2 (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) where
  R : ℕ → TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop
  entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))
  agree : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    a.1.1 = b.1.1 ∧ TreeStagesSwapCache D a.2 b.2 ∧
    (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome)
  progress : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings
  next : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun u v => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
    R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))

/-- The good-prefix relation that remains for the stages. Unlike
`TreeSimStagesGoodCoreGoal`, its final caches may differ by a digest swap. -/
def TreeSimStagesRelationGoal2 : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    Nonempty (TreeStagesRelation2 prims K circuits settings top tree D A parameter seeds pairs z p r)

/-- The stages from the remaining good-prefix relation. Bad prefixes use
`treeStages_badCore2`. -/
theorem treeSimStagesGoal2_of_relation (relation : TreeSimStagesRelationGoal2 prims K circuits settings) :
    TreeSimStagesGoal2 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  by_cases bad : TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2
  · refine ⟨pure (), fun r hr => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨treeSimRoundCore_stages2 prims K circuits settings top tree D A parameter seeds pairs z Z
      p.1 p.2.1 _ (treeStages_badCore2 prims K circuits settings top tree D A parameter seeds pairs z
        p.1 p.2.1 p.2.2 bad)⟩
  · obtain ⟨padding, hpadding⟩ := relation hb top tree D A parameter seeds pairs z Z q hq hsmall p hp bad
    refine ⟨padding, fun r hr => ?_⟩
    obtain ⟨rel⟩ := hpadding r hr
    exact ⟨treeStages_roundStages_of_reachable_relation2 prims K circuits settings top tree D A
      parameter seeds pairs z Z p hp padding r hr rel.R rel.entry rel.agree rel.progress rel.next⟩


/-- The state with the swapped public cache and the same private cache and log. -/
def treeStagesTwin (swaps : List (List Bit × HashOutput × HashOutput)) (s : TreeSimState C) :
    TreeSimState C :=
  ((treeStagesSwapAll swaps s.1.1, s.1.2), s.2)

/-- A world call that commutes with the swaps on the public cache also commutes in the logged
world, with the same log. -/
theorem treeStages_logged_twin (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    (t : (WorldSpec C).Domain)
    (commute : ∀ c : HashCache C × HiddenCache C,
      (streamWorld prims D t).run (treeStagesSwapAll swaps c.1, c.2) =
        (fun r => (r.1, (treeStagesSwapAll swaps r.2.1, r.2.2))) <$> (streamWorld prims D t).run c)
    (s : TreeSimState C) :
    (treeSimLoggedWorld prims D t).run (treeStagesTwin swaps s) =
      (fun r => (r.1, treeStagesTwin swaps r.2)) <$> (treeSimLoggedWorld prims D t).run s := by
  simp only [treeSimLoggedWorld, treeStagesTwin, StateT.run_mk, commute, Functor.map_map]

/-- A local call away from the swapped salts commutes with the swaps in the stream world. -/
theorem treeStages_onHash_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (t : (LocalSpec C).Domain) (safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false)
    (c : HashCache C × HiddenCache C) :
    (onHash (localAnswer prims t)).run (treeStagesSwapAll swaps c.1, c.2) =
      (fun r => (r.1, (treeStagesSwapAll swaps r.2.1, r.2.2))) <$> (onHash (localAnswer prims t)).run c := by
  simp only [onHash, StateT.run_mk, treeStages_localAnswer_swapAll prims swaps t safe, Functor.map_map]

/-- A counted call away from the swapped salts commutes with the swaps. -/
theorem treeStages_counted_swapAll (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    (t : (LocalSpec C).Domain) (safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false)
    (c : HashCache C × HiddenCache C) :
    (streamWorld prims D (.inl (.inl t))).run (treeStagesSwapAll swaps c.1, c.2) =
      (fun r => (r.1, (treeStagesSwapAll swaps r.2.1, r.2.2))) <$>
        (streamWorld prims D (.inl (.inl t))).run c :=
  treeStages_onHash_swapAll prims swaps t safe c

/-- A free call away from the swapped salts commutes with the swaps. -/
theorem treeStages_free_swapAll (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    (t : (LocalSpec C).Domain) (safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false)
    (c : HashCache C × HiddenCache C) :
    (streamWorld prims D (.inr t)).run (treeStagesSwapAll swaps c.1, c.2) =
      (fun r => (r.1, (treeStagesSwapAll swaps r.2.1, r.2.2))) <$>
        (streamWorld prims D (.inr t)).run c := by
  rcases t with n | q | x
  · exact treeStages_onHash_swapAll prims swaps (.inl n) safe c
  · exact treeStages_onHash_swapAll prims swaps (.inr (.inl q)) safe c
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, Functor.map_map]
    · simp only [streamWorld, if_neg hx]
      exact treeStages_onHash_swapAll prims swaps (.inr (.inr x)) safe c

/-- A computation and its image under `f` are coupled along `f`. -/
theorem treeStages_relTriple_map_self {α β : Type} (f : α → β) (x : ProbComp α) :
    RelTriple x (f <$> x) (fun u v => v = f u) := by
  have h := relTriple_map (f := id) (g := f) (R := fun u v => v = f u)
    (relTriple_post_mono (relTriple_refl x) (fun u v huv => by
      change u = v at huv
      subst huv
      rfl))
  simpa only [id_map] using h

/-- A free digest call at a swapped salt. -/
def TreeStagesFreeHit (swaps : List (List Bit × HashOutput × HashOutput)) (log : TreeSimLog C) : Prop :=
  ∃ x ∈ swaps, ∃ hist answer, (⟨.inr (.inr (.inl (.digest x.1 hist))), answer⟩ :
    (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log

/-- An adaptive counted computation gives the same result on a state and on its twin, until the
real log guesses a swapped salt. -/
theorem treeStages_adversary_twin {α : Type} (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (p : OracleComp (LocalSpec C) α)
    (a : TreeSimState C) (salts : ∀ x ∈ swaps, TreeSimHiddenSalt D a.2 x.1) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run a)
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run (treeStagesTwin swaps a))
      (fun u v => TreeSimSaltGuess D u.2.2 ∨ (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)) := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure x =>
    simp only [worldRoles]
    exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)
  | query_bind t k ih =>
    change RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.adversary (k x))).run a)
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.adversary (k x))).run (treeStagesTwin swaps a)) _
    simp only [simulateQ_bind, StateT.run_bind]
    by_cases hit : ∃ x ∈ swaps, digestSaltHit x.1 t = true
    · obtain ⟨x, hx, hit⟩ := hit
      apply relTriple_of_support_left
      intro w hw z
      simp only [support_bind, Set.mem_iUnion] at hw
      obtain ⟨u, hu, hw⟩ := hw
      have guess := treeStages_local_query_saltGuess prims D x.1 t hit a (salts x hx) u hu
      exact Or.inl (treeStages_saltGuess_mono D (treeSimLoggedWorld_prefix prims D _ u.2 w hw) guess)
    · have safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false := by
        intro x hx
        cases hv : digestSaltHit x.1 t
        · rfl
        · exact False.elim (hit ⟨x, hx, hv⟩)
      have step : (simulateQ (treeSimLoggedWorld prims D)
          (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run (treeStagesTwin swaps a) =
          (fun r => (r.1, treeStagesTwin swaps r.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
            (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run a := by
        rw [adversary_query]
        erw [simulateQ_spec_query]
        exact treeStages_logged_twin prims D swaps _ (treeStages_counted_swapAll prims D swaps t safe) a
      rw [step]
      apply relTriple_bind (treeSim_relTriple_support (treeStages_relTriple_map_self _ _))
      intro u v huv
      rw [huv.1]
      exact ih u.1 u.2 (fun x hx => treeStages_hiddenSalt_mono D x.1
        (treeSimLoggedWorld_prefix prims D _ a u huv.2.1) (salts x hx))

theorem treeStages_honest_query (t : (LocalSpec C).Domain) :
    worldRoles.honest (OracleComp.lift (OracleSpec.query t)) =
      (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) := by
  rcases t with t | (q | x) <;> rfl

/-- A logged call records itself at the end of the log. -/
theorem treeStages_logged_query_log (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : TreeSimState C) (r : (WorldSpec C).Range t × TreeSimState C)
    (hr : r ∈ support ((treeSimLoggedWorld prims D t).run s)) :
    r.2.2 = s.2 ++ [⟨t, r.1⟩] := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, _, rfl⟩ := hr
  rfl

/-- An honest computation gives the same result on a state and on its twin, until it queries a
digest at a swapped salt. -/
theorem treeStages_honest_twin {α : Type} (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (q : OracleComp (LocalSpec C) α)
    (a : TreeSimState C) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest q)).run a)
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest q)).run (treeStagesTwin swaps a))
      (fun u v => (∃ l, u.2.2 = a.2 ++ l ∧ TreeStagesFreeHit swaps l) ∨
        (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)) := by
  induction q using OracleComp.inductionOn generalizing a with
  | pure x =>
    simp only [worldRoles]
    exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)
  | query_bind t k ih =>
    change RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.honest (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.honest (k x))).run a)
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.honest (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.honest (k x))).run (treeStagesTwin swaps a)) _
    simp only [simulateQ_bind, StateT.run_bind]
    have logOf (u : (LocalSpec C).Range t × TreeSimState C)
        (hu : u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (worldRoles.honest (OracleComp.lift (OracleSpec.query t)))).run a)) :
        u.2.2 = a.2 ++ [⟨.inr t, u.1⟩] := by
      rw [treeStages_honest_query] at hu
      erw [simulateQ_spec_query] at hu
      exact treeStages_logged_query_log prims D (.inr t) a u hu
    by_cases hit : ∃ x ∈ swaps, digestSaltHit x.1 t = true
    · obtain ⟨x, hx, hit⟩ := hit
      apply relTriple_of_support_left
      intro w hw z
      simp only [support_bind, Set.mem_iUnion] at hw
      obtain ⟨u, hu, hw⟩ := hw
      have recorded := logOf u hu
      obtain ⟨l, hl⟩ := treeSimLoggedWorld_prefix prims D _ u.2 w hw
      refine Or.inl ⟨[⟨.inr t, u.1⟩] ++ l, by rw [← hl, recorded, List.append_assoc], ?_⟩
      rcases t with n | q | y
      · simp [digestSaltHit] at hit
      · cases q <;> simp only [digestSaltHit, Bool.false_eq_true] at hit
        case digest salt hist =>
          have eq : salt = x.1 := of_decide_eq_true hit
          subst salt
          exact ⟨x, hx, hist, u.1, by simp⟩
      · simp [digestSaltHit] at hit
    · have safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false := by
        intro x hx
        cases hv : digestSaltHit x.1 t
        · rfl
        · exact False.elim (hit ⟨x, hx, hv⟩)
      have step : (simulateQ (treeSimLoggedWorld prims D)
          (worldRoles.honest (OracleComp.lift (OracleSpec.query t)))).run (treeStagesTwin swaps a) =
          (fun r => (r.1, treeStagesTwin swaps r.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
            (worldRoles.honest (OracleComp.lift (OracleSpec.query t)))).run a := by
        rw [treeStages_honest_query]
        erw [simulateQ_spec_query]
        exact treeStages_logged_twin prims D swaps _ (treeStages_free_swapAll prims D swaps t safe) a
      rw [step]
      apply relTriple_bind (treeSim_relTriple_support (treeStages_relTriple_map_self _ _))
      intro u v huv
      rw [huv.1]
      have recorded := logOf u huv.2.1
      apply relTriple_post_mono (ih u.1 u.2)
      intro w z hwz
      rcases hwz with ⟨l, hl, hit'⟩ | good
      · refine Or.inl ⟨[⟨.inr t, u.1⟩] ++ l, by rw [hl, recorded, List.append_assoc], ?_⟩
        obtain ⟨x, hx, hist, answer, mem⟩ := hit'
        exact ⟨x, hx, hist, answer, List.mem_append_right _ mem⟩
      · exact Or.inr good

/-- A predicate that each step keeps is kept by the sequence. -/
theorem treeStages_sequenceFin_persist {σ α : Type} {n : ℕ} (f : Fin n → StateT σ ProbComp α)
    (P : σ → Prop) (persist : ∀ i s u, u ∈ support ((f i).run s) → P s → P u.2) :
    ∀ s u, u ∈ support ((Concrete.sequenceFin f).run s) → P s → P u.2 := by
  induction n with
  | zero =>
    intro s u hu hs
    simp only [Concrete.sequenceFin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    rw [hu]
    exact hs
  | succ n ih =>
    intro s u hu hs
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hu
    obtain ⟨v, hv, w, hw, rfl⟩ := hu
    exact ih (fun i => f i.succ) (fun i => persist i.succ) v.2 w hw (persist 0 s v hv hs)

/-- Sequential steps that each commute with `τ` until a persistent event commute together. -/
theorem treeStages_sequenceFin_twin {σ α : Type} {n : ℕ} (f : Fin n → StateT σ ProbComp α)
    (τ : σ → σ) (Inv Bad : σ → Prop)
    (persistInv : ∀ i s u, u ∈ support ((f i).run s) → Inv s → Inv u.2)
    (persist : ∀ i s u, u ∈ support ((f i).run s) → Bad s → Bad u.2)
    (step : ∀ i s, Inv s → RelTriple ((f i).run s) ((f i).run (τ s))
      (fun u v => Bad u.2 ∨ (u.1 = v.1 ∧ v.2 = τ u.2))) :
    ∀ s, Inv s → RelTriple ((Concrete.sequenceFin f).run s) ((Concrete.sequenceFin f).run (τ s))
      (fun u v => Bad u.2 ∨ (u.1 = v.1 ∧ v.2 = τ u.2)) := by
  induction n with
  | zero =>
    intro s _
    simp only [Concrete.sequenceFin, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)
  | succ n ih =>
    intro s hs
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (treeSim_relTriple_support (step 0 s hs))
    intro u v huv
    rcases huv.1 with bad | ⟨same, twin⟩
    · apply relTriple_of_support_left
      intro w hw z
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact Or.inl (treeStages_sequenceFin_persist (fun i => f i.succ) Bad
        (fun i => persist i.succ) u.2 x hx bad)
    · rw [twin]
      apply relTriple_bind (ih (fun i => f i.succ) (fun i => persistInv i.succ)
        (fun i => persist i.succ) (fun i => step i.succ) u.2 (persistInv 0 s u huv.2.1 hs))
      intro x y hxy
      apply relTriple_pure_pure
      rcases hxy with bad | ⟨same', twin'⟩
      · exact Or.inl bad
      · refine Or.inr ⟨?_, twin'⟩
        rw [same, same']

/-- The events that break the twin coupling of a round from the log `start`. A counted call
guesses a swapped salt, or an honest call asks a digest at a swapped salt. -/
def TreeStagesTwinBad (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    (start log : TreeSimLog C) : Prop :=
  TreeSimSaltGuess D log ∨ ∃ l, log = start ++ l ∧ TreeStagesFreeHit swaps l

theorem treeStages_twinBad_mono (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    {start a b : TreeSimLog C} (hab : a <+: b) :
    TreeStagesTwinBad D swaps start a → TreeStagesTwinBad D swaps start b := by
  obtain ⟨m, rfl⟩ := hab
  rintro (guess | ⟨l, rfl, x, hx, hist, answer, mem⟩)
  · exact Or.inl (treeStages_saltGuess_mono D ⟨m, rfl⟩ guess)
  · exact Or.inr ⟨l ++ m, by rw [List.append_assoc], x, hx, hist, answer, List.mem_append_left _ mem⟩

/-- One real round on a state and on its twin. The results are equal and the states stay twins,
until a counted call guesses a swapped salt or an honest call asks a digest at a swapped salt. -/
theorem treeStages_round_twin {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (swaps : List (List Bit × HashOutput × HashOutput)) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (a : TreeSimState C)
    (salts : ∀ x ∈ swaps, TreeSimHiddenSalt D a.2 x.1) :
    RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality state steps).run a)
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state steps).run (treeStagesTwin swaps a))
      (fun u v => TreeStagesTwinBad D swaps a.2 u.2.2 ∨ (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)) := by
  simp only [stepRound, callInput_real, Option.isSome_none, Bool.false_eq_true, and_false,
    exists_false, false_and, if_false, StateT.run_bind]
  have twinBad : ∀ s w : TreeSimState C, s.2 <+: w.2 →
      TreeStagesTwinBad D swaps a.2 s.2 → TreeStagesTwinBad D swaps a.2 w.2 :=
    fun s w h => treeStages_twinBad_mono D swaps h
  apply relTriple_bind (treeSim_relTriple_support (treeStages_adversary_twin prims D swaps _ a salts))
  intro u v huv
  rcases huv.1 with guess | ⟨same, twin⟩
  · apply relTriple_of_support_left
    intro w hw z
    simp only [support_bind, Set.mem_iUnion, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    refine Or.inl (treeStages_sequenceFin_persist _ (fun s => TreeStagesTwinBad D swaps a.2 s.2) ?_
      u.2 x hx (Or.inl guess))
    intro i s w hw hs
    apply twinBad s w.2 _ hs
    split at hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      rw [hw]
    · split_ifs at hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
      · exact treeSimLoggedWorld_prefix prims D _ s w hw
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      rw [hw]
  · rw [twin, ← same]
    apply relTriple_bind (treeStages_sequenceFin_twin _ (treeStagesTwin swaps) (fun s => a.2 <+: s.2)
      (fun s => TreeStagesTwinBad D swaps a.2 s.2) ?_ ?_ ?_ u.2
      (treeSimLoggedWorld_prefix prims D _ a u huv.2.1))
    · intro x y hxy
      apply relTriple_pure_pure
      rcases hxy with bad | ⟨same', twin'⟩
      · exact Or.inl bad
      · exact Or.inr ⟨by rw [same'], twin'⟩
    · intro i s w hw hs
      apply hs.trans
      split at hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
      · split_ifs at hw
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
          rw [hw]
        · exact treeSimLoggedWorld_prefix prims D _ s w hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
    · intro i s w hw hs
      apply twinBad s w.2 _ hs
      split at hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
      · split_ifs at hw
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
          rw [hw]
        · exact treeSimLoggedWorld_prefix prims D _ s w hw
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
    · intro i s hs
      obtain ⟨m, hm⟩ := hs
      split
      · exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)
      · split_ifs
        · exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)
        · apply relTriple_post_mono (treeStages_honest_twin prims D swaps _ s)
          rintro w z (⟨l, hl, x, hx, hist, answer, mem⟩ | good)
          · refine Or.inl (Or.inr ⟨m ++ l, by rw [hl, ← hm, List.append_assoc], x, hx, hist, answer,
              List.mem_append_right _ mem⟩)
          · exact Or.inr good
      · exact relTriple_pure_pure (Or.inr ⟨rfl, rfl⟩)

/-- The twin coupling composed with an equal-cache coupling of the twin gives a swap-related
coupling. Unlike `treeCompose_swapRel`, the twin keeps the real log, and the results may be
related by any `S`. -/
theorem treeStages_swap_transfer {X Y : Type} (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput))
    (Bad Bad' : TreeSimLog C → Prop) (S : X → Y → Prop)
    {oa ob : ProbComp (X × TreeSimState C)} {oc : ProbComp (Y × (HashCache C × HiddenCache C))}
    (salts : ∀ u ∈ support oa, ∀ x ∈ swaps, TreeSimHiddenSalt D u.2.2 x.1)
    (real : RelTriple oa ob (fun u v => Bad u.2.2 ∨ (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)))
    (equal : RelTriple ob oc (fun v w => Bad' v.2.2 ∨ ∃ δ, S v.1 w.1 ∧ TreeSimStreamRel δ v.2 w.2)) :
    RelTriple oa oc (fun u w => Bad u.2.2 ∨ Bad' u.2.2 ∨
      ∃ δ, S u.1 w.1 ∧ TreeStagesSwapRel D swaps δ u.2 w.2) := by
  apply relTriple_post_mono (treeCompose_relTriple_comp (treeSim_relTriple_support real) equal)
  rintro u w ⟨v, ⟨bad | ⟨same, twin⟩, hu, _⟩, bad' | ⟨δ, related, cache, hidden⟩⟩
  · exact Or.inl bad
  · exact Or.inl bad
  · rw [twin] at bad'
    exact Or.inr (Or.inl bad')
  · rw [twin] at cache hidden
    rw [← same] at related
    exact Or.inr (Or.inr ⟨δ, related, salts u hu, cache.symm, hidden⟩)

/-- One round with swapped public caches from the equal-cache round of the twin. The bad event
is `TreeSimBad2`. An honest digest call at a swapped salt must give `TreeSimBad2`. -/
theorem treeStages_round_swap (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (swaps : List (List Bit × HashOutput × HashOutput))
    (Rel : (A.State × (C.Party → Step C E RealSpec TreeOutput) × (C.Party → C.Party → Option (Msg E))) →
      (A.State × (C.Party → Step C E RealSpec TreeOutput) × (C.Party → C.Party → Option (Msg E))) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (salts : ∀ y ∈ swaps, TreeSimHiddenSalt D a.2.2 y.1)
    (hit : ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
      (∃ l, u.2.2 = a.2.2 ++ l ∧ TreeStagesFreeHit swaps l) →
      TreeSimBad2 prims K circuits settings top tree D A x z u.2.2)
    (equal : RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
      (fun v w => TreeSimBad2 prims K circuits settings top tree D A x z v.2.2 ∨
        ∃ δ, Rel v.1 w.1 ∧ TreeSimStreamRel δ v.2 w.2)) :
    RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
      (fun u w => TreeSimBad2 prims K circuits settings top tree D A x z u.2.2 ∨
        ∃ δ, Rel u.1 w.1 ∧ TreeStagesSwapRel D swaps δ u.2 w.2) := by
  have twin := treeSim_relTriple_support
    (treeStages_round_twin prims D A swaps a.1.1 a.1.2 a.2 salts)
  have salts' : ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
      ∀ y ∈ swaps, TreeSimHiddenSalt D u.2.2 y.1 := by
    intro u hu y hy
    have hpref : a.2.2 <+: u.2.2 := by
      apply treeSimLoggedWorld_prefix prims D (stepRound worldRoles D A noFunctionality a.1.1 a.1.2) a.2 u
      simpa only [simulateQ_stepRound, treeSimRealRoles] using hu
    exact treeStages_hiddenSalt_mono D y.1 hpref (salts y hy)
  apply relTriple_post_mono (treeStages_swap_transfer D swaps
    (TreeSimBad2 prims K circuits settings top tree D A x z)
    (TreeSimBad2 prims K circuits settings top tree D A x z) Rel salts' ?_ equal)
  · rintro u w (bad | bad | good)
    · exact Or.inl bad
    · exact Or.inl bad
    · exact Or.inr good
  · apply relTriple_post_mono twin
    rintro u v ⟨(guess | hit') | good, hu, _⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inr guess)))
    · exact Or.inl (hit u hu hit')
    · exact Or.inr good

/-- The twin coupling composed with any coupling of the twin. -/
theorem treeStages_twin_transfer {X Y : Type} (swaps : List (List Bit × HashOutput × HashOutput))
    (Bad : TreeSimLog C → Prop) (Q : X × TreeSimState C → Y → Prop)
    {oa ob : ProbComp (X × TreeSimState C)} {oc : ProbComp Y}
    (real : RelTriple oa ob (fun u v => Bad u.2.2 ∨ (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)))
    (twin : RelTriple ob oc Q) :
    RelTriple oa oc (fun u w => Bad u.2.2 ∨ Q (u.1, treeStagesTwin swaps u.2) w) := by
  apply relTriple_post_mono (treeCompose_relTriple_comp real twin)
  rintro u w ⟨v, bad | ⟨same, twin⟩, hq⟩
  · exact Or.inl bad
  · rw [same, ← twin]
    exact Or.inr hq

theorem treeStagesTwin_append (extra swaps : List (List Bit × HashOutput × HashOutput))
    (s : TreeSimState C) :
    treeStagesTwin extra (treeStagesTwin swaps s) = treeStagesTwin (extra ++ swaps) s := by
  simp only [treeStagesTwin, treeStagesSwapAll, List.foldr_append]

/-- The remaining ceremony relation in equal-cache form. `Req n δ a' b` relates the twin `a'` of a
reachable real configuration to the ideal configuration, with equal public caches. A round may
add hidden-salt swaps, which the next twin then carries. -/
structure TreeStagesTwinRelation (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C) where
  Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop
  stream : ∀ n δ a b, Req n δ a b → TreeSimStreamRel δ a.2 b.2
  entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    ∃ δ, Req 0 δ ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))
  agree : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    a.1.1 = b.1.1 ∧ (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome)
  progress : ∀ n a,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings
  freeHit : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
    (∃ l, u.2.2 = a.2.2 ++ l ∧ TreeStagesFreeHit swaps l) →
    TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2
  next : ∀ n δ swaps a b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
    ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
    Req (n + 1) δ' ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))

/-- The relation of the stages. It is `Req` on the twin of the real configuration, for some list
of hidden-salt swaps. -/
def TreeStagesTwinRelation.R {top : TopTree} {tree : Tree} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {parameter : PublicParameter}
    {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput} {z : Aux}
    {p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C)}
    {r : Unit × HashCache C}
    (twin : TreeStagesTwinRelation prims K circuits settings top tree D A parameter seeds pairs z p r)
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) :
    Prop :=
  ∃ swaps δ, (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) ∧ twin.Req n δ (a.1, treeStagesTwin swaps a.2) b

/-- The relation of the stages from the equal-cache relation of the twins. -/
def treeStages_relation_of_twin (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (r : Unit × HashCache C)
    (twin : TreeStagesTwinRelation prims K circuits settings top tree D A parameter seeds pairs z p r) :
    TreeStagesRelation2 prims K circuits settings top tree D A parameter seeds pairs z p r where
  R := twin.R
  entry u hu := by
    apply relTriple_post_mono (twin.entry u hu)
    rintro a b (bad | ⟨δ, req⟩)
    · exact Or.inl bad
    · exact Or.inr ⟨[], δ, fun x hx => by simp at hx, req⟩
  agree n a b rel reach good := by
    obtain ⟨swaps, δ, salts, req⟩ := rel
    obtain ⟨state, done, outputs⟩ := twin.agree n δ swaps a b reach good req
    obtain ⟨cache, hidden⟩ := twin.stream n δ _ b req
    exact ⟨state, Or.inr ⟨swaps, δ, salts, cache.symm, hidden⟩, done, outputs⟩
  progress n a _ _ reach bound good active := twin.progress n a reach bound good active
  next n a b rel reach bound good active := by
    obtain ⟨swaps, δ, salts, req⟩ := rel
    have real := treeSim_relTriple_support
      (treeStages_round_twin prims D A swaps a.1.1 a.1.2 a.2 salts)
    have real' := relTriple_post_mono real (R' := fun u v => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
        (u.1 = v.1 ∧ v.2 = treeStagesTwin swaps u.2)) (by
      rintro u v ⟨(guess | hit) | good, hu, _⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inr guess)))
      · exact Or.inl (twin.freeHit n δ swaps a b reach good salts req u hu hit)
      · exact Or.inr good)
    apply relTriple_post_mono (treeSim_relTriple_support (treeStages_twin_transfer swaps _ _ real'
      (twin.next n δ swaps a b reach bound good active salts req)))
    rintro u w ⟨(bad | bad | ⟨extra, δ', salts', req'⟩), hu, _⟩
    · exact Or.inl bad
    · exact Or.inl bad
    · have hpref : a.2.2 <+: u.2.2 := by
        apply treeSimLoggedWorld_prefix prims D (stepRound worldRoles D A noFunctionality a.1.1 a.1.2) a.2 u
        simpa only [simulateQ_stepRound, treeSimRealRoles] using hu
      refine Or.inr ⟨extra ++ swaps, δ', ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact salts' x hx
        · exact treeStages_hiddenSalt_mono D x.1 hpref (salts x hx)
      · rw [← treeStagesTwin_append]
        exact req'

/-- The good-prefix twin relation that remains for `TreeSimStagesGoal2`. -/
def TreeSimStagesTwinRelationGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    Nonempty (TreeStagesTwinRelation prims K circuits settings top tree D A parameter seeds pairs z p r)

theorem treeSimStagesGoal2_of_twinRelation
    (twin : TreeSimStagesTwinRelationGoal prims K circuits settings) :
    TreeSimStagesGoal2 prims K circuits settings := by
  apply treeSimStagesGoal2_of_relation
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := twin hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨rel⟩ := hpadding r hr
  exact ⟨treeStages_relation_of_twin prims K circuits settings top tree D A parameter seeds pairs z p r rel⟩

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal2_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal2_of_relation

/-- info: 'ThresholdLeanXmssSecurity.treeStages_round_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStages_round_twin

/-- info: 'ThresholdLeanXmssSecurity.treeStages_round_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStages_round_swap

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal2_of_twinRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal2_of_twinRelation

end ThresholdLeanXmssSecurity
