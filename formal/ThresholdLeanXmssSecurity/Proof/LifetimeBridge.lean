import ThresholdLeanXmssSecurity.Proof.LifetimeLemmas

/-!
# Joint prefixes for the lifetime tree hop

`TreeSecurityDistanceFrom` fixes the keys, top tree and selected tree before the oracle prefix.
Conditioning it on metadata computed by that prefix is invalid: the conditioning also changes
the cache law. Here `jointPrefixRun` keeps the dealer keys, selection and cache in one distribution.
Its keys come from `prawnsKeyGen`, and `jointPrefixRun_dealt` proves validity on support.

The world, stream and key-table transport laws below preserve that joint distribution.
The bridge concerns an invoked ceremony; common lifetime abort branches remain outside this
interface. The adaptive hop obligations are stated with the existing fixed tree errors at `q0 + q`, averaged
over the selected tree, and one PRF reduction running the same complete prefix.

The pinned and current leanVM bridge modules were searched first. Their
`XmssSecurity.Bridge.evalDist_run_bind_of` expresses the same joint-cache principle for `HashSpec`;
the transport here uses the existing threshold world/stream lemmas for `LocalSpec`.
The interface concerns a selected ceremony, rather than the complete lifetime scheduler.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeBridge

open TprfSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The top tree and next ceremony selected from the prefix transcript. -/
abbrev Choice := TopTree × Tree × Aux

/-- The dealer output already used by `Fkeygen`. -/
abbrev Dealing (C : Committee) :=
  PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)

/-- A prefix continuation selects the top tree, ceremony and auxiliary input. -/
abbrev Selector (C : Committee) := Dealing C → OracleComp (LocalSpec C) Choice

abbrev JointInput (C : Committee) := (C.Party → Keys C) × Choice

local instance : DecidableEq (JointInput C × HashCache C) := Classical.decEq _

/-- Sample the actual dealer keys, then retain their dependence with the entire selecting prefix.
Only local calls are allowed, as in D6; local keygen programming is handled separately. -/
def jointPrefix (pre : Selector C) : OracleComp (LocalSpec C) (JointInput C) := do
  let keys ← liftComp (prawnsKeyGen (C := C)) (LocalSpec C)
  let chosen ← pre keys
  pure (keys.2.2, chosen)

def jointPrefixRun (prims : Primitives) (pre : Selector C) :
    ProbComp (JointInput C × HashCache C) :=
  (simulateQ (localAnswer prims) (jointPrefix pre)).run ∅

/-- No arbitrary input validity assumption is imposed on the sampler. -/
theorem jointPrefix_dealt (D : C.Coalition) (pre : Selector C) (r : JointInput C)
    (hr : r ∈ support (jointPrefix pre)) : DealtInputs D r.1 := by
  simp only [jointPrefix, mem_support_bind_iff, support_liftComp, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨keys, hk, chosen, _, rfl⟩ := hr
  obtain ⟨pairs, hp⟩ := prawnsKeyGen_support keys hk
  exact ⟨keys.1, keys.2.1, pairs, fun i => congrFun hp i⟩

theorem jointPrefixRun_dealt (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (r : JointInput C) (g : HashCache C)
    (hr : (r, g) ∈ support (jointPrefixRun prims pre)) : DealtInputs D r.1 := by
  apply jointPrefix_dealt D pre r
  apply support_simulateQ_run'_subset (localAnswer prims) (jointPrefix pre) ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨(r, g), hr, rfl⟩

section Games

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The ceremony selected by the same prefix in both worlds. -/
def selectedGame (ideal : Bool) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    JointInput C → OracleComp (WorldSpec C) Bool
  | (keys, top, tree, z) =>
      if ideal then treeIdealGame K circuits settings top tree D A keys z Z
      else treeRealGame K circuits settings top tree D A keys z Z

/-- The reduction runs the same keygen and selecting prefix as the game. -/
def jointGame (ideal : Bool) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (WorldSpec C) Bool :=
  worldRoles.adversary (jointPrefix pre) >>= selectedGame K circuits settings ideal D A Z

variable (prims : Primitives)

/-- Exact joint continuation law, retaining metadata/cache dependence and forgetting only cost. -/
theorem jointWorld_run (ideal : Bool) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    Prod.fst <$> runWorld prims (jointGame K circuits settings ideal D pre A Z) =
      jointPrefixRun prims pre >>= fun p =>
        (simulateQ (worldAnswer prims) (selectedGame K circuits settings ideal D A Z p.1)).run' p.2 := by
  rw [fst_map_runWorld, jointGame, simulateQ_bind, simulateQ_adversary]
  simp only [StateT.run'_eq, StateT.run_bind, jointPrefixRun, map_bind]

theorem jointStream_run (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    (simulateQ (streamWorld prims D) (jointGame K circuits settings false D pre A Z)).run'
        (∅, ∅) =
      jointPrefixRun prims pre >>= fun p =>
        (simulateQ (streamWorld prims D) (selectedGame K circuits settings false D A Z p.1)).run' (p.2, ∅) := by
  rw [jointGame, simulateQ_bind, treeSim_stream_adversary]
  simp only [StateT.run'_eq, StateT.run_bind, onHash, StateT.run_mk, jointPrefixRun,
    map_bind, bind_map_left]

theorem jointKey_run (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (table : KeyName C × HashOutput → Digest) :
    (simulateQ (keyWorld prims D table) (jointGame K circuits settings false D pre A Z)).run' ∅ =
      jointPrefixRun prims pre >>= fun p =>
        (simulateQ (keyWorld prims D table) (selectedGame K circuits settings false D A Z p.1)).run' p.2 := by
  rw [jointGame, simulateQ_bind, keyWorld_adversary]
  simp only [StateT.run'_eq, StateT.run_bind, jointPrefixRun, map_bind]

/-- The probability law of the keyed hybrid uses the same joint prefix. Only the independent AES
table is commuted past that prefix; metadata are never fixed by conditioning on its output. -/
theorem jointKey_probability (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    reductionReal prims D (jointGame K circuits settings false D pre A Z) =
      (Pr[= true | jointPrefixRun prims pre >>= fun p =>
        ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun table =>
          (simulateQ (keyWorld prims D table)
            (selectedGame K circuits settings false D A Z p.1)).run' p.2]).toReal := by
  unfold reductionReal
  rw [prfRealExp_prgReduction]
  simp only [jointKey_run]
  rw [probOutput_bind_bind_swap]

theorem jointStream_probability (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    reductionIdeal prims D (jointGame K circuits settings false D pre A Z) =
      (Pr[= true | jointPrefixRun prims pre >>= fun p =>
        (simulateQ (streamWorld prims D)
          (selectedGame K circuits settings false D A Z p.1)).run' (p.2, ∅)]).toReal := by
  unfold reductionIdeal
  rw [prfIdealExp_prgReduction, jointStream_run]

theorem jointWorld_probability (ideal : Bool) (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) :
    accepts prims (jointGame K circuits settings ideal D pre A Z) =
      (Pr[= true | jointPrefixRun prims pre >>= fun p =>
        (simulateQ (worldAnswer prims)
          (selectedGame K circuits settings ideal D A Z p.1)).run' p.2]).toReal := by
  have h := congrArg (fun m => (Pr[= true | m]).toReal)
    (jointWorld_run K circuits settings prims ideal D pre A Z)
  simpa only [probOutput_map, accepts] using h

end Games

/-! ## The exact adaptive obligations -/

def selectedError (e : Tree → ℝ) : JointInput C → ℝ
  | (_, _, tree, _) => e tree

/-- The existing per-tree expression averaged on the complete joint prefix. -/
def jointError (prims : Primitives) (pre : Selector C) (e : Tree → ℝ) : ℝ :=
  ∑ p ∈ finSupport (jointPrefixRun prims pre),
    (Pr[= p | jointPrefixRun prims pre]).toReal * selectedError e p.1

theorem jointError_add (prims : Primitives) (pre : Selector C) (e f : Tree → ℝ) :
    jointError prims pre (fun t => e t + f t) = jointError prims pre e + jointError prims pre f := by
  have hs : ∀ p : JointInput C,
      selectedError (fun t => e t + f t) p = selectedError e p + selectedError f p := by
    intro p
    rfl
  simp only [jointError, hs, mul_add, Finset.sum_add_distrib]

section Hops

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The key-table hop with jointly sampled keys, top tree, selection and cache. This is still
open; the fixed-input `TreeKeyHopFrom` cannot be conditioned to establish it. -/
def JointKeyHopFrom (split : ℕ → ℝ) : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ),
    IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |accepts prims (jointGame K circuits settings false D pre A Z) -
      reductionReal prims D (jointGame K circuits settings false D pre A Z)| ≤
      jointError prims pre (fun _ => streamKeyError C + split (q0 + q))

/-- The stream-to-ideal hop with adaptive ceremony selection. This is the precise remaining
joint form of the simulation hop, with the same D14 budgets and split expression. -/
def JointSimulationHopFrom (split : ℕ → ℝ) : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ),
    IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |reductionIdeal prims D (jointGame K circuits settings false D pre A Z) -
      accepts prims (jointGame K circuits settings true D pre A Z)| ≤
      jointError prims pre (fun tree => treeCheckError (E := E) circuits settings tree (q0 + q) +
        (treeHashError circuits settings C tree (q0 + q) - split (q0 + q)))

/-- The adaptive joint bridge keeps one PRF reduction of the complete run. Its error is fixed
by the existing tree errors and the selected-tree distribution, not chosen by a prover. -/
def JointTreeSecurityDistanceFrom : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition) (pre : Selector C)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ),
    IsQueryBoundP (jointPrefix pre) Counted q0 →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |accepts prims (jointGame K circuits settings false D pre A Z) -
      accepts prims (jointGame K circuits settings true D pre A Z)| ≤
      jointError prims pre (fun tree => treeCheckError (E := E) circuits settings tree (q0 + q) +
        treeHashError circuits settings C tree (q0 + q) + streamKeyError C) +
      PRFScheme.prfAdvantage (hiddenStreams prims.aes)
        (prgReduction prims D (jointGame K circuits settings false D pre A Z))

theorem jointTreeSecurityDistanceFrom_of_hops (split : ℕ → ℝ)
    (hkey : JointKeyHopFrom prims K circuits settings split)
    (hsim : JointSimulationHopFrom prims K circuits settings split) :
    JointTreeSecurityDistanceFrom prims K circuits settings := by
  intro hb D pre A Z q0 q hpre hq
  have h := abs_sub_le_of_hops prims D
    (jointGame K circuits settings false D pre A Z) (jointGame K circuits settings true D pre A Z)
    _ _ (hkey hb D pre A Z q0 q hpre hq) (hsim hb D pre A Z q0 q hpre hq)
  rw [← jointError_add] at h
  convert h using 1
  congr 2
  funext tree
  ring

/-- The still-open simulation step from the component hypothesis to the joint prefix. -/
def JointSimulationFromComponent : Prop :=
  TreeSimulationHop prims K circuits settings (keySplit C) →
    JointSimulationHopFrom prims K circuits settings (keySplit C)

theorem jointTreeSecurityDistanceFrom_of_component
    (hkey : JointKeyHopFrom prims K circuits settings (keySplit C))
    (hbridge : JointSimulationFromComponent prims K circuits settings)
    (hsim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    JointTreeSecurityDistanceFrom prims K circuits settings :=
  jointTreeSecurityDistanceFrom_of_hops prims K circuits settings (keySplit C) hkey (hbridge hsim)

/-! ## Independent samples, before the oracle prefix -/

/-- The part already justified by the component theorem: sample inputs independently before the
oracle prefix, then average its fixed-input bounds. The top and tree can depend on that independent
sample. This intermediate bound averages PRF advantages; the adaptive target above instead keeps
one joint reduction and remains open at its two explicitly named hops. -/
theorem sampledTreeSecurityDistanceFrom {V : Type} [Fintype V] (draw : ProbComp V)
    (top : V → TopTree) (tree : V → Tree) (inputs : V → C.Party → Keys C)
    (pre : V → OracleComp (LocalSpec C) Aux) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ)
    (hsim : TreeSimulationHop prims K circuits settings (keySplit C))
    (hb : 0 < settings.batchSize) (hx : ∀ v, DealtInputs D (inputs v))
    (hpre : ∀ v, IsQueryBoundP (pre v) Counted q0)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    |(Pr[fun r => r.1 = true | draw >>= fun v => prefixRun prims (pre v) >>= fun p =>
        (simulateQ (world prims)
          (treeRealGame K circuits settings (top v) (tree v) D A (inputs v) p.1 Z)).run.run' p.2]).toReal -
      (Pr[fun r => r.1 = true | draw >>= fun v => prefixRun prims (pre v) >>= fun p =>
        (simulateQ (world prims)
          (treeIdealGame K circuits settings (top v) (tree v) D A (inputs v) p.1 Z)).run.run' p.2]).toReal| ≤
      ∑ v, (Pr[= v | draw]).toReal *
        (treeCheckError (E := E) circuits settings (tree v) (q0 + q) +
          treeHashError circuits settings C (tree v) (q0 + q) + streamKeyError C +
          PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D
            (worldRoles.adversary (pre v) >>= fun z =>
              treeRealGame K circuits settings (top v) (tree v) D A (inputs v) z Z))) :=
  abs_probEvent_bind_sub_le_sum draw _ _ _ _ fun v =>
    treeSecurityDistanceFrom prims K circuits settings hsim hb (top v) (tree v) D A
      (inputs v) (pre v) Z q0 q (hx v) (hpre v) hq

end Hops


/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.jointPrefixRun_dealt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointPrefixRun_dealt

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.jointWorld_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointWorld_run

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.jointKey_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointKey_probability

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.jointStream_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointStream_probability

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.jointTreeSecurityDistanceFrom_of_hops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointTreeSecurityDistanceFrom_of_hops

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.jointTreeSecurityDistanceFrom_of_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointTreeSecurityDistanceFrom_of_component

/-- info: 'ThresholdLeanXmssSecurity.LifetimeBridge.sampledTreeSecurityDistanceFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sampledTreeSecurityDistanceFrom

end ThresholdLeanXmssSecurity.LifetimeBridge
