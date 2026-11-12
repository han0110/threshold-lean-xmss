import ThresholdLeanXmssSecurity.Proof.TreeFromCache
import ThresholdLeanXmssSecurity.Proof.TreeKeyAimed

/-!
# The hidden-key hop and the tree distance from the cache of earlier phases

`TreeKeyHopFrom` is `TreeKeyHop` (`Tree.lean:4452`) from the cache of a prefix `pre` with at most `q0`
counted calls. `TreeFromCache.lean` gives the same form for `TreeSimulationHop`. The error is the error
of `TreeKeyHop` at `q0 + q`, as decision D14 of `FIX.md` gives for the simulation hop.

* `treeKeyHopFrom_of_hop` applies `TreeKeyHop` to `withPrefix A pre` at `q0 + q`. The prefix makes only
  calls of the adversary role. `keyWorld` answers them with `localAnswer`, so the prefix does not read
  the table of AES keys. The table and the prefix are independent, so their order does not change
  the distribution (`probOutput_bind_bind_swap`).
* `treeSecurityDistanceFrom_of_hops` composes the two from-cache hops as
  `treeSecurityDistance_of_hops` (`Tree.lean:4472`) composes the two hops. The PRF reduction runs the
  prefix and then the ceremony.
* `treeSecurityDistanceFrom` takes only `TreeSimulationHop` as a hop hypothesis. The key hop follows from
  `treeKeyAimedBound` (`TreeKeyAimed.lean`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `TreeKeyHop` from the cache of a prefix with at most `q0` counted calls. The output of the
prefix is the auxiliary input. The error is the error of `TreeKeyHop` at `q0 + q`. -/
def TreeKeyHopFrom (split : ℕ → ℝ) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (pre : OracleComp (LocalSpec C) Aux) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ),
    DealtInputs D x → IsQueryBoundP pre Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |(Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeRealGame K circuits settings top tree D A x p.1 Z)).run.run'
          p.2]).toReal -
      (Pr[= true | prefixRun prims pre >>= fun p => ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) (treeRealGame K circuits settings top tree D A x p.1 Z)).run'
          p.2]).toReal| ≤
      streamKeyError C + split (q0 + q)

/-- The distance half of `TreeSecurityStatement` from the cache of a prefix with at most `q0` counted
calls. The PRF reduction runs the prefix and then the ceremony. -/
def TreeSecurityDistanceFrom : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (pre : OracleComp (LocalSpec C) Aux) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ),
    DealtInputs D x → IsQueryBoundP pre Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |(Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeRealGame K circuits settings top tree D A x p.1 Z)).run.run'
          p.2]).toReal -
      (Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeIdealGame K circuits settings top tree D A x p.1 Z)).run.run'
          p.2]).toReal| ≤
      treeCheckError (E := E) circuits settings tree (q0 + q) + treeHashError circuits settings C tree (q0 + q) +
        streamKeyError C +
        PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D
          (worldRoles.adversary pre >>= fun w => treeRealGame K circuits settings top tree D A x w Z))

/-- `keyWorld` answers each call of the adversary role with `localAnswer`. -/
theorem keyWorld_adversary {α : Type} (D : C.Coalition) (keys : KeyName C × HashOutput → Digest)
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (keyWorld prims D keys) (worldRoles.adversary p) = simulateQ (localAnswer prims) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (keyWorld prims D keys) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun x => worldRoles.adversary (k x)) = _
    rw [simulateQ_bind, adversary_query]
    simp only [simulateQ_bind, simulateQ_query, ih]
    rfl

/-- The real side of the absorbed adversary in the world is the real side from the cache of the prefix. -/
theorem world_treeRealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    (fun r => r.1) <$> (simulateQ (world prims)
        (treeRealGame K circuits settings top tree D (withPrefix A pre) x z Z)).run.run' ∅ =
      prefixRun prims pre >>= fun p => (fun r => r.1) <$>
        (simulateQ (world prims) (treeRealGame K circuits settings top tree D A x p.1 Z)).run.run' p.2 := by
  simp only [world, fst_map_run_withAddCost]
  rw [treeRealGame_withPrefix, simulateQ_bind]
  simp only [worldRoles, simulateQ_counted, TprfSecurityProof.simulateQ_liftComp_local]
  simp only [StateT.run'_eq, StateT.run_bind, map_bind, prefixRun]

theorem accepts_treeRealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    accepts prims (treeRealGame K circuits settings top tree D (withPrefix A pre) x z Z) =
      (Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeRealGame K circuits settings top tree D A x p.1 Z)).run.run'
          p.2]).toReal := by
  have hmap := congrArg (fun m => Pr[(· = true) | m])
    (world_treeRealGame_withPrefix prims K circuits settings top tree D A x pre z Z)
  simp only [← map_bind, probEvent_map] at hmap
  exact congrArg ENNReal.toReal hmap

theorem accepts_treeIdealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    accepts prims (treeIdealGame K circuits settings top tree D (withPrefix A pre) x z Z) =
      (Pr[fun r => r.1 = true | prefixRun prims pre >>= fun p =>
        (simulateQ (world prims) (treeIdealGame K circuits settings top tree D A x p.1 Z)).run.run'
          p.2]).toReal := by
  have hmap := congrArg (fun m => Pr[(· = true) | m])
    (world_treeIdealGame_withPrefix prims K circuits settings top tree D A x pre z Z)
  simp only [← map_bind, probEvent_map] at hmap
  exact congrArg ENNReal.toReal hmap

/-- The run of the absorbed adversary with a table of AES keys is the run from the cache of the
prefix. -/
theorem keyWorld_treeRealGame_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) (keys : KeyName C × HashOutput → Digest) :
    (simulateQ (keyWorld prims D keys) (treeRealGame K circuits settings top tree D (withPrefix A pre) x z Z)).run'
        ∅ =
      prefixRun prims pre >>= fun p =>
        (simulateQ (keyWorld prims D keys) (treeRealGame K circuits settings top tree D A x p.1 Z)).run' p.2 := by
  rw [treeRealGame_withPrefix, simulateQ_bind, keyWorld_adversary]
  simp only [StateT.run'_eq, StateT.run_bind, prefixRun, map_bind]

/-- The keyed side of the absorbed adversary is the keyed side from the cache of the prefix. The
table of AES keys and the prefix are independent. -/
theorem probOutput_keyWorld_withPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (pre : OracleComp (LocalSpec C) Aux)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    Pr[= true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys)
          (treeRealGame K circuits settings top tree D (withPrefix A pre) x z Z)).run' ∅] =
      Pr[= true | prefixRun prims pre >>= fun p => ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) (treeRealGame K circuits settings top tree D A x p.1 Z)).run' p.2] := by
  simp only [keyWorld_treeRealGame_withPrefix]
  exact probOutput_bind_bind_swap _ _ _ _

/-- The key hop from the cache of a prefix follows from the key hop from the empty cache at `q0 + q`.
The adversary runs the prefix first. -/
theorem treeKeyHopFrom_of_hop (split : ℕ → ℝ) (hop : TreeKeyHop prims K circuits settings split) :
    TreeKeyHopFrom prims K circuits settings split := by
  intro hb top tree D A x pre Z q0 q hx hpre hq
  have h := hop hb top tree D (withPrefix A pre) x [] Z (q0 + q) hx
    (isQueryBounded_withPrefix A Z pre _ q0 q hpre hq)
  rw [accepts_treeRealGame_withPrefix, probOutput_keyWorld_withPrefix] at h
  exact h

/-- The two from-cache hops compose as in `treeSecurityDistance_of_hops`. -/
theorem treeSecurityDistanceFrom_of_hops (split : ℕ → ℝ) (h₁ : TreeKeyHopFrom prims K circuits settings split)
    (h₂ : TreeSimulationHopFrom prims K circuits settings split) :
    TreeSecurityDistanceFrom prims K circuits settings := by
  intro hb top tree D A x pre Z q0 q hx hpre hq
  have := abs_sub_le_of_hops prims D (treeRealGame K circuits settings top tree D (withPrefix A pre) x [] Z)
    (treeIdealGame K circuits settings top tree D (withPrefix A pre) x [] Z) (streamKeyError C + split (q0 + q))
    (treeCheckError (E := E) circuits settings tree (q0 + q) +
      (treeHashError circuits settings C tree (q0 + q) - split (q0 + q)))
    (by
      unfold reductionReal
      rw [prfRealExp_prgReduction, accepts_treeRealGame_withPrefix, probOutput_keyWorld_withPrefix]
      exact h₁ hb top tree D A x pre Z q0 q hx hpre hq)
    (by
      unfold reductionIdeal
      rw [prfIdealExp_prgReduction, streamWorld_treeRealGame_withPrefix, accepts_treeIdealGame_withPrefix]
      exact h₂ hb top tree D A x pre Z q0 q hx hpre hq)
  rw [accepts_treeRealGame_withPrefix, accepts_treeIdealGame_withPrefix, treeRealGame_withPrefix] at this
  linarith

/-- The key hop from the cache of a prefix, from the unconditional aimed-call bound. -/
theorem treeKeyHopFrom : TreeKeyHopFrom prims K circuits settings (keySplit C) :=
  treeKeyHopFrom_of_hop prims K circuits settings (keySplit C)
    (treeKeyHop_of_streamKeyBound prims K circuits settings
      (treeStreamKeyBound_of_afterDerivation prims K circuits settings
        (treeStreamKeyAfterDerivationFull prims K circuits settings
          (treeKeyHitBound prims K circuits settings
            (treeKeyAfterHitBound_of_aimed prims K circuits settings
              (treeKeyAimedBound prims K circuits settings))))))

/-- The tree distance from the cache of a prefix needs only the simulation hop from the empty cache. -/
theorem treeSecurityDistanceFrom (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityDistanceFrom prims K circuits settings :=
  treeSecurityDistanceFrom_of_hops prims K circuits settings (keySplit C)
    (treeKeyHopFrom prims K circuits settings)
    (treeSimulationHopFrom_of_hop prims K circuits settings (keySplit C) hSim)

/-- info: 'ThresholdLeanXmssSecurity.treeKeyHopFrom_of_hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeyHopFrom_of_hop

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityDistanceFrom_of_hops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityDistanceFrom_of_hops

/-- info: 'ThresholdLeanXmssSecurity.treeKeyHopFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeyHopFrom

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityDistanceFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityDistanceFrom

end ThresholdLeanXmssSecurity
