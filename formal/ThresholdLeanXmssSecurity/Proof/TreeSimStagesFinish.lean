import ThresholdLeanXmssSecurity.Proof.TreeSimStages

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

/-!
`TreeSimStagesGoodCoreGoal prims K circuits settings` does not hold for all
parameters. The trace below is a deduction from the frozen definitions and is
not a Lean refutation. The lemmas after it build `TreeSimStagesGoal` directly
from `TreeSimRoundStages`, with final caches that may differ by hidden-salt
digest swaps. `treeSimStagesGoal_of_relation` reduces it to
`TreeSimStagesRelationGoal`.

The obstruction is in `TreeSimRoundCore`. Its field `outputEvidence` requires
`a.2.1.1 = b.2.1` for every non-bad `Inv` pair, at every round boundary, and
`ceremony` together with `entry` forces `Inv` at every reachable non-bad
boundary. The honest holders of the hidden term `T₀` hash their histories into
the public cache, and these histories differ between the two runs.

The instance has these values.
* `C.t = 2`, so `C.n = 3`. The parties are `p`, `a` and `b`, and `D = {p}`.
  The terms are the singletons, and `T₀ = {p}` is the only term that `D` does
  not know. Its holders `a` and `b` are honest.
* `K.filled a = {p}`, `K.filled b = {a}` and `K.filled p = {b}`. Each party
  holds its filled term, and all terms are filled, so `T₀ ∈ filledTerms K`.
* `settings.mode = .peer`, `settings.batchSize > 0`, `seeds {p} ≠ 0`, and the
  first job has an AND gate on two input bits. The adversary runs the honest
  program of `p` and stores every message, so `a` and `b` reach
  `compareDigests` in the check of the first batch.

The run goes as follows.
1. Real inputs of `T₀` use `.prf (seeds {p}) x`, and ideal inputs use
   `.prf 0 x`. If the padding does not prefetch the second key, the caches
   differ already. If it does, the support of the padding contains caches where
   the first AND gate has different values `xy` in the two runs.
2. In `reshare`, `u_b` goes to `p`, so equal adversary states fix `u_b`. By
   `pairs_unique` the shares `v = mulRep` add up to `xy`, and by `pairs_held`
   the share `v_p` has no `T₀` factor. The mask `Z_{b,p}` comes from a key of
   `p`, which is an assumption on the PRSS derivation. So the hidden mask
   `Z_{a,b}` takes the full shift, and the filled value `z T₀ = u_a` differs by
   `Δ(xy) ≠ 0` in every coupling with equal adversary states.
3. `record` appends `z T₀` to the history of `T₀` at `a` and `b`. The simulator
   gadgets `treeSimGadgets` change only `output`, so the ideal run records its
   own value. The histories `h` and `h'` of `T₀` thus differ.
4. `compareDigests` queries `.history h` and then `.digest salt η` in the
   real run, and `.history h'` and `.digest salt' η'` in the ideal run. The
   `.history` keys carry no term tag, so they can agree with keys of other
   terms. The support contains caches where the `.history` table is injective
   on the short histories, so `η ≠ η'` on every non-bad run. Equal caches then
   need the real key `(salt, η)` in the ideal cache and the reverse, so the
   padding must prefetch both keys for all salts. Then the digests are fixed by
   the padded cache, and the support contains caches where `P(·, η)` and
   `P(·, η')` have different distributions over the uniform hidden salt, for
   each possible value of `h`. So the digests that `p` receives differ with
   positive probability in every coupling. The post-round state is non-bad
   with positive probability, because the cache can have no collision on the
   logged queries.

So no padding, no coupling and no `Inv` satisfy `outputEvidence` at the
boundary after the digest exchange.

This trace refutes only the internal core Prop `TreeSimStagesGoodCoreGoal`.
The target `TreeSimStagesGoal` is not refuted by this trace. In
`TreeSimRoundStages` the fields `Bad`, `Inv`, `stage` and `Q` are free. A `Q`
that admits the digest swap, closed by `treeStages_observe_digestSwap`, and a
`.ceremony` stage after the digest round avoid the fixed `TreeSimFinalRel` of
`TreeSimRoundCore`. This route does not use `treeSimStagesGoalClosed`.
-/

/-- The composition of salted digest swaps, applied to a public cache. -/
def treeStagesSwapAll (swaps : List (List Bit × HashOutput × HashOutput)) (c : HashCache C) : HashCache C :=
  swaps.foldr (fun x c => relabelHashCache (digestSwap x.1 x.2.1 x.2.2) c) c

/-- A local call that hits none of the swapped salts commutes with all swaps. -/
theorem treeStages_localAnswer_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (t : (LocalSpec C).Domain) (safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false) (c : HashCache C) :
    (localAnswer prims t).run (treeStagesSwapAll swaps c) =
      (fun r => (r.1, treeStagesSwapAll swaps r.2)) <$> (localAnswer prims t).run c := by
  induction swaps with
  | nil => simp [treeStagesSwapAll]
  | cons x swaps ih =>
    have safe' : ∀ y ∈ swaps, digestSaltHit y.1 t = false := fun y hy => safe y (by simp [hy])
    change (localAnswer prims t).run
        (relabelHashCache (digestSwap x.1 x.2.1 x.2.2) (treeStagesSwapAll swaps c)) =
      (fun r => (r.1, relabelHashCache (digestSwap x.1 x.2.1 x.2.2) (treeStagesSwapAll swaps r.2))) <$>
        (localAnswer prims t).run c
    rw [localDigestAnswer_eq_of_no_salt prims x.1 x.2.1 x.2.2 t _ (safe x (by simp)),
      localAnswer_digestSwap, ih safe', Functor.map_map]

/-- A local computation that never queries a digest at a swapped salt. -/
def TreeStagesAvoids {α : Type} (swaps : List (List Bit × HashOutput × HashOutput))
    (q : OracleComp (LocalSpec C) α) : Prop :=
  OracleComp.construct (C := fun _ => Prop) (fun _ => True)
    (fun t _ rest => (∀ x ∈ swaps, digestSaltHit x.1 t = false) ∧ ∀ u, rest u) q

/-- The generic transfer. A local computation that avoids every swapped salt
commutes with the swaps. -/
theorem treeStages_localProgram_swapAll {α : Type} (swaps : List (List Bit × HashOutput × HashOutput))
    (q : OracleComp (LocalSpec C) α) (avoids : TreeStagesAvoids swaps q) (c : HashCache C) :
    (simulateQ (localAnswer prims) q).run (treeStagesSwapAll swaps c) =
      (fun r => (r.1, treeStagesSwapAll swaps r.2)) <$> (simulateQ (localAnswer prims) q).run c := by
  induction q using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    have h : (∀ x ∈ swaps, digestSaltHit x.1 t = false) ∧ ∀ u, TreeStagesAvoids swaps (k u) := avoids
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [treeStages_localAnswer_swapAll prims swaps t h.1, bind_map_left, map_bind]
    apply bind_congr
    intro r
    exact ih r.1 (h.2 r.1) r.2

/-- Public caches related by hidden-salt digest swaps, and private caches
related by a stream shift. -/
def TreeStagesSwapRel (D : C.Coalition) (swaps : List (List Bit × HashOutput × HashOutput))
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  (∀ x ∈ swaps, TreeSimHiddenSalt D a.2 x.1) ∧ b.1 = treeStagesSwapAll swaps a.1.1 ∧
    TreeSimHiddenRel δ a.1.2 b.2

/-- One counted call keeps the swap relation, or it guesses a hidden salt. -/
theorem treeStages_local_swapAll_step (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (δ : HiddenAddress C → Bit)
    (t : (LocalSpec C).Domain) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeStagesSwapRel D swaps δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run a)
      ((simulateQ (streamWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run b)
      (fun u z => TreeSimSaltGuess D u.2.2 ∨
        (u.1 = z.1 ∧ TreeStagesSwapRel D swaps δ u.2 z.2)) := by
  by_cases hit : ∃ x ∈ swaps, digestSaltHit x.1 t = true
  · obtain ⟨x, hx, hit⟩ := hit
    apply relTriple_of_support_left
    intro u hu z
    exact Or.inl (treeStages_local_query_saltGuess prims D x.1 t hit a (related.1 x hx) u hu)
  · have safe : ∀ x ∈ swaps, digestSaltHit x.1 t = false := by
      intro x hx
      cases hv : digestSaltHit x.1 t
      · rfl
      · exact False.elim (hit ⟨x, hx, hv⟩)
    have interp := treeSim_stream_adversary prims D (OracleComp.lift (OracleSpec.query t))
    simp only [simulateQ_spec_query] at interp
    apply relTriple_post_mono (treeSim_relTriple_support
      (treeStages_onHash_transport prims D _ _ _ _ interp interp
        (treeStagesSwapAll swaps) δ a b
        (treeStages_localAnswer_swapAll prims swaps t safe a.1.1) related.2.1 related.2.2))
    intro u z hu
    refine Or.inr ⟨hu.1.1, fun x hx => treeStages_hiddenSalt_mono D x.1
      (treeSimLoggedWorld_prefix prims D _ a u hu.2.1) (related.1 x hx), hu.1.2.1, hu.1.2.2.1⟩

/-- An adaptive counted computation keeps the swap relation until the real
log guesses a hidden salt. -/
theorem treeStages_local_swapAll {α : Type} (D : C.Coalition)
    (swaps : List (List Bit × HashOutput × HashOutput)) (δ : HiddenAddress C → Bit)
    (p : OracleComp (LocalSpec C) α) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeStagesSwapRel D swaps δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.adversary p)).run b)
      (fun u z => TreeSimSaltGuess D u.2.2 ∨ (u.1 = z.1 ∧ TreeStagesSwapRel D swaps δ u.2 z.2)) := by
  induction p using OracleComp.inductionOn generalizing a b with
  | pure x =>
    simp only [worldRoles]
    exact relTriple_pure_pure (Or.inr ⟨rfl, related⟩)
  | query_bind t k ih =>
    change RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.adversary (k x))).run a)
      ((simulateQ (streamWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.adversary (k x))).run b) _
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeStages_local_swapAll_step prims D swaps δ t a b related))
    intro u z hu
    rcases hu.1 with bad | good
    · apply relTriple_of_support_left
      intro v hv w
      exact Or.inl (treeStages_saltGuess_mono D (treeSimLoggedWorld_prefix prims D _ u.2 v hv) bad)
    · rw [← good.1]
      exact ih u.1 u.2 z.2 good.2

/-- Final public caches that are equal, or related by hidden-salt digest
swaps. -/
def TreeStagesSwapCache (D : C.Coalition) (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  a.1.1 = b.1 ∨ ∃ swaps δ, TreeStagesSwapRel D swaps δ a b

/-- Swapped final caches give the same distinguisher output, unless the real
log guesses a hidden salt. -/
theorem treeStages_observe_swapAll (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput)
    (swaps : List (List Bit × HashOutput × HashOutput)) (δ : HiddenAddress C → Bit)
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (related : TreeStagesSwapRel D swaps δ a.2 b.2) (state : a.1.1 = b.1.1)
    (outputs : a.1.2 = fun i => if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none) :
    RelTriple (treeSimRealObserve prims D A Z a) (treeSimIdealObserve prims D A Z dealt b)
      (fun x y => TreeSimSaltGuess D x.2 ∨ x.1 = y) := by
  have inputs : a.1 = (b.1.1, fun i =>
      if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none) := Prod.ext state outputs
  have hr := treeStages_local_swapAll prims D swaps δ (Z a.1) a.2 b.2 related
  have mapped : RelTriple
      ((fun r => (r.1, r.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary (Z a.1))).run a.2)
      (Prod.fst <$> (simulateQ (streamWorld prims D) (worldRoles.adversary (Z a.1))).run b.2)
      (fun x y => TreeSimSaltGuess D x.2 ∨ x.1 = y) := by
    apply relTriple_map
    exact relTriple_post_mono hr (fun _ _ hp => hp.imp id (fun good => good.1))
  simpa only [treeSimRealObserve, treeSimIdealObserve, treeSim_stream_adversary,
    onHash, StateT.run_mk, Functor.map_map, StateT.run'_eq, inputs] using mapped

/-- The final relation of the stages. It weakens `TreeSimFinalRel` by the
digest swap. -/
def TreeStagesSwapFinal (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (dealt : Option TreeOutput) (a : TreeSimRoundOutput A (TreeSimState C))
    (b : TreeSimRoundOutput A (HashCache C × HiddenCache C)) : Prop :=
  a.1.1 = b.1.1 ∧ (a.1.2 = fun i => if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none) ∧
    TreeStagesSwapCache D a.2 b.2

theorem treeStages_observe_swapFinal (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput)
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (h : TreeStagesSwapFinal D A dealt a b) :
    RelTriple (treeSimRealObserve prims D A Z a) (treeSimIdealObserve prims D A Z dealt b)
      (fun x y => TreeSimHashBad D x.2 ∨ x.1 = y) := by
  obtain ⟨state, outputs, cache | ⟨swaps, δ, related⟩⟩ := h
  · exact relTriple_post_mono (treeSim_observe_good prims D A Z dealt a b ⟨state, cache, outputs⟩)
      (fun _ _ he => Or.inr he)
  · exact relTriple_post_mono
      (treeStages_observe_swapAll prims D A Z dealt swaps δ a b related state outputs)
      (fun _ _ he => he.imp (fun guess => Or.inr guess) id)

/-- Replay fixes every successful honest output, with no cache premise. -/
theorem treeStages_outputs_of_replay (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (replay : TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z dealt a.1 a.2.2)
    (good : ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2)
    (corrupt : ∀ i, i ∈ D.1 → a.1.2 i = none)
    (success : ∀ i, i ∉ D.1 → (a.1.2 i).isSome = (b.1.2 i).isSome) :
    a.1.2 = fun i => if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt.1 else none := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi]
  · by_cases hs : (a.1.2 i).isSome = true
    · have hb : (b.1.2 i).isSome = true := (success i hi).symm.trans hs
      simpa only [hi, not_false_eq_true, hb, Bool.true_eq, and_self, if_true] using
        treeSim_output_correct prims K circuits settings top tree D A parameter seeds pairs z
          dealt a.1 a.2.2 replay good i hi hs
    · have hb : (b.1.2 i).isSome ≠ true := fun h => hs ((success i hi).trans h)
      have ha : a.1.2 i = none := by
        cases he : a.1.2 i with
        | none => rfl
        | some v => exact False.elim (hs (by simp [he]))
      simp [hi, hb, ha]

/-- The stages from a round-indexed relation on reachable real
configurations. The relation may end with a digest swap in the public caches.
Replay, empty corrupt outputs, sticky events and final observation are proved
here. -/
def treeStages_roundStages_of_reachable_relation (top : TopTree) (tree : Tree) (D : C.Coalition)
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
        (fun a b => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
          R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2)))
    (agree : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      a.1.1 = b.1.1 ∧ TreeStagesSwapCache D a.2 b.2 ∧
      (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
      (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome))
    (progress : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings)
    (next : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 →
      RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
        (fun u v => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
          R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))) :
    TreeSimRoundStages prims K circuits settings (treeSimEvents prims K circuits settings)
      top tree D A parameter seeds pairs z Z p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) where
  Bad t := TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2
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
  badPersistent _ _ hp := treeSimBad_mono prims K circuits settings top tree D A _ z hp
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
        p hp padding r hr n bound a reach) good
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
    · exact Or.inl (Or.inl (by simp [treeSimEvents, bad]))
    · exact Or.inr (by rw [eq])
  badRecorded t ht := (treeSimEvents_bad prims K circuits settings top tree D A _ z Z t.2).mpr ht

/-- The remaining ceremony relation at one good prefix and one padded cache.
It drives `treeStages_roundStages_of_reachable_relation`. -/
structure TreeStagesRelation (top : TopTree) (tree : Tree) (D : C.Coalition)
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
    (fun a b => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))
  agree : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    a.1.1 = b.1.1 ∧ TreeStagesSwapCache D a.2 b.2 ∧
    (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome)
  progress : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings
  next : ∀ n a b, R n a b →
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
    p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun u v => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
    R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))

/-- The good-prefix relation that remains for the stages. Unlike
`TreeSimStagesGoodCoreGoal`, its final caches may differ by a digest swap. -/
def TreeSimStagesRelationGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    Nonempty (TreeStagesRelation prims K circuits settings top tree D A parameter seeds pairs z p r)

/-- The stages from the remaining good-prefix relation. Bad prefixes use
`treeStages_badCore`. -/
theorem treeSimStagesGoal_of_relation (relation : TreeSimStagesRelationGoal prims K circuits settings) :
    TreeSimStagesGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  by_cases bad : TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2
  · refine ⟨pure (), fun r hr => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨treeSimRoundCore_stages prims K circuits settings top tree D A parameter seeds pairs z Z
      p.1 p.2.1 _ (treeStages_badCore prims K circuits settings top tree D A parameter seeds pairs z
        p.1 p.2.1 p.2.2 bad)⟩
  · obtain ⟨padding, hpadding⟩ := relation hb top tree D A parameter seeds pairs z Z q hq hsmall p hp bad
    refine ⟨padding, fun r hr => ?_⟩
    obtain ⟨rel⟩ := hpadding r hr
    exact ⟨treeStages_roundStages_of_reachable_relation prims K circuits settings top tree D A
      parameter seeds pairs z Z p hp padding r hr rel.R rel.entry rel.agree rel.progress rel.next⟩

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimStagesGoal_of_relation

end ThresholdLeanXmssSecurity
