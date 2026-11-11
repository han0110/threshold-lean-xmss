import ThresholdLeanXmssSecurity.Proof.TreeSimCheck

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-
Open setup branch of `TreeSimCheckIndexedBounds`. This is not a counterexample.

Trace with n = 5, t = 3 and D = {c1, c2}. Term T has the holders {c1, i, j} and the
excluded set {c2, k}, so T is visible and two honest operators hold it.
1. In the PRSS `commitRevealEcho`, c1 commits to part a for i and to part a' for j.
   The commitments name their receiver, so each reveal opens its commitment.
2. Then i derives K_T^i from [a, p_i, p_j], and j derives K_T^j from [a', p_i, p_j].
   These are different keys.
3. The echo between i and j compares H(sharedKeys L_i) with H(sharedKeys L_j), and
   L_i is not L_j. Each list holds the key of a hidden term that i and j share, so the
   adversary cannot query H(L_i) before the echo. The adversary fixes the set S of
   inconsistent pairs before the echo answers exist, even with a commit collision.
   Every pair in S must collide, so the setup passes with probability at most 2^-256.
4. `sharedKeys` is outside `TreeSimHashDomain`, so `TreeSimHashBad` does not exclude
   this branch. The key hop (`TreeKeyHop`, `KeysApart`, `KeyHit`) is a separate hop.
   `TreeSimulationHop` bounds the full `streamWorld` run with no conditioning.
5. After step 3, the streams of T are real AES under keys that the adversary knows.
   The shares of T at i and j differ by known values. `record` hashes only filled
   positions, so `compareDigests` does not see unfilled r_T. In the Coin, c1 and c2
   can choose shares on a polynomial g with deg g ≤ 2, g(k) = g(i) = 0 and
   g(j) = psi(T, j) * δ. So `openSh` does not abort. It is open whether a wrong
   output can then pass the check and `openRep`.

Accounting (route c). Per batch, the bound is
(d + 2(R + 1)) / (2^192 - 2) + (R + 2) q / 2^192.
1. If D is empty, the branch does not exist.
2. If some corrupt commitment to an honest operator was not a counted query before its
   opening, then the setup passes with probability at most 2^-256. Take the first such
   pair in a fixed order.
3. Otherwise each such commitment is a counted query that is not a coin-domain entry.
   So `treeSimCheck_contextual` applies at q' = seen.card + (2R + 5) * step ≤ q - 1.
The total is at most 2 * 2^-256 + checkErrorOf d R (q - 1), which is at most
checkErrorOf d R q because (R + 2) / 2^192 ≥ 2^-255. If q = 0, then case 3 is empty, and
2^-256 ≤ (d + 2) / 2^192.
-/

/-- The bound of each fixed indexed batch event, the hypothesis of
`treeSimCheckBound_of_indexedBounds`. -/
def TreeSimCheckIndexedBounds : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        Pr[fun r => TreeSimCheckIndexedBad prims K circuits settings top tree D A x z j r.2 r.1.2 |
          treeSimLoggedRun prims D (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)] ≤
        ENNReal.ofReal (checkErrorOf (E := E)
          (maxBatch circuits settings fun jobs => coins (tupleCount jobs))
          (maxBatch circuits settings fun jobs => halvings (tupleCount jobs)) q)

include K in
/-- The check error grows with the coins, the halving steps and the queries. -/
theorem checkErrorOf_mono {d d' R R' q q' : ℕ} (hd : d ≤ d') (hR : R ≤ R') (hq : q ≤ q') :
    checkErrorOf (E := E) d R q ≤ checkErrorOf (E := E) d' R' q' := by
  have hE : (2 : ℝ) < Fintype.card E := by rw [card_field K]; norm_num [elementBits]
  unfold checkErrorOf
  have h1 : (0 : ℝ) < Fintype.card E - 2 := by linarith
  have h2 : (0 : ℝ) < Fintype.card E := by linarith
  gcongr

theorem TreeSimCheckTimed.require_bind {α : Type} (n : ℕ) (P : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : TreeSimCheckTimed n (k ()).run) :
    TreeSimCheckTimed n (require P >>= k).run := by
  by_cases hP : P
  · simpa only [require, if_pos hP, pure_bind] using hk
  · simp only [require, if_neg hP, failure_bind]
    exact TreeSimCheckTimed.abort n

/-- The PRSS setup takes exactly its three rounds or aborts. -/
theorem treeSimCheckTimed_prssSetup (i : C.Party) :
    TreeSimCheckTimed setupRounds (prssSetup (E := E) (G := RealSpec) i).run := by
  unfold prssSetup commitRevealEcho setupRounds
  simp only [bind_assoc]
  refine TreeSimCheckTimed.local_bind 2 _ _ (fun own => ?_)
  refine TreeSimCheckTimed.oracle_bind 2 _ _ (fun commitments => ?_)
  refine TreeSimCheckTimed.exchange_bind 2 _ _ (fun committed => ?_)
  refine TreeSimCheckTimed.exchange_bind 1 _ _ (fun revealed => ?_)
  refine TreeSimCheckTimed.oracle_bind 0 _ _ (fun opens => ?_)
  refine TreeSimCheckTimed.require_bind 1 _ _ ?_
  refine TreeSimCheckTimed.oracle_bind 0 _ _ (fun keys => ?_)
  refine TreeSimCheckTimed.oracle_bind 0 _ _ (fun shared => ?_)
  refine TreeSimCheckTimed.exchange_bind 0 _ _ (fun received => ?_)
  refine TreeSimCheckTimed.require_bind 0 _ _ ?_
  simp only [pure_bind, OptionT.run_pure]
  exact TreeSimCheckTimed.done _

/-- The audited ceremony splits after the PRSS setup. -/
theorem treeSimCheck_audit_setup_split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (state : A.State) :
    executePhase worldRoles D A noFunctionality (ceremonyFuel circuits settings) state
      (fun i => treeSimCheckCeremonyAudit K circuits settings i (x i) top tree) = (do
      let out ← executePhase worldRoles D A noFunctionality setupRounds state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
      let next ← free (Concrete.sequenceFin fun i => continueStep
        (fun prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
        (.done (out.2 i)))
      executeRounds worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) out.1 next) := by
  unfold treeSimCheckCeremonyAudit ceremonyFuel
  exact treeSimCheckTimed_phase_split D A 2 _ state (fun i => prssSetup i)
    (fun i prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
    (fun i => treeSimCheckTimed_prssSetup i)

theorem treeSimCheckBoundFinal
    (indexedBounds : TreeSimCheckIndexedBounds prims K circuits settings) :
    TreeSimCheckBoundGoal prims K circuits settings :=
  treeSimCheckBound_of_indexedBounds prims K circuits settings indexedBounds

/-- info: 'ThresholdLeanXmssSecurity.treeSimCheckBoundFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCheckBoundFinal

end ThresholdLeanXmssSecurity
