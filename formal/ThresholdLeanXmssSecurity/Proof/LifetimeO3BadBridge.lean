import ThresholdLeanXmssSecurity.Proof.LifetimeO3Bridge
import ThresholdLeanXmssSecurity.Proof.LifetimeRealBadSum
import ThresholdLeanXmssSecurity.Proof.LifetimeAllowance

/-!
# The lifetime bad-event bounds at the fixed `Th`

`RealBadBound` and `IdealBadBound` hold for each `values`. At `values := fun x => prims.Th x.1`
they give bounds at `restrictTh prims`. The handlers below read `Th` only through `hashAnswer`,
`localAnswer` or `worldAnswer`, so they are equal at `restrictTh prims` and at `prims`.

| Bridge | Object |
| --- | --- |
| `jointHash_restrict`, `jointLocal_restrict`, `jointKeyWorldCore_restrict`, `jointKeyWorld_restrict` | the monitored stream-key world |
| `probBad_streamKey_restrict` | the stream-key bad event |
| `localImpl_restrict`, `withHidden_restrict`, `leftImpl_restrict` | the ideal side of a PRF hop |
| `worldAnswer_restrict`, `evalEmulation_restrict`, `evalSlot_restrict` | the evaluated emulation |
| `rawKernel_restrict`, `markedKernel_restrict`, `keygenPrefix_restrict`, `markedGame_restrict` | the separated slot world |

At the fixed `prims` and `circuits`, with `HasLifetimeQueryBound`, these lemmas follow.

* `realBad_fixed` and `idealBad_fixed` bound the right sides of `LifetimeO3Bridge.real_transport`
  and `LifetimeO3Bridge.ideal_transport` by the real share and the ideal share, when
  `keySplit (q₀ + q) < 2`.
* `prfTransport_fixed` bounds the two transports of each PRF hop by `keySplit (q₀ + q)`.
* `prfHop_fixed` bounds each chronological hop by the PRF advantage of `lifetimeRunReduction` and
  `keySplit (q₀ + q)`.
* `prfPass_fixed` bounds the distance from `lifetimeAdvantage` to the last chronological world by
  the sum of the PRF advantages and one `keySplit (q₀ + q)` for each run.

`markedGame_restrict` moves a bound on `markedGame` at `restrictTh prims` to `prims`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeO3BadBridge

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

open LifetimeO3Bridge (restrictTh hashAnswer_restrict localAnswer_restrict)

section Bridges

variable (prims : Primitives) (D : C.Coalition)

theorem aes_restrict : (restrictTh prims).aes = prims.aes := rfl

theorem jointHash_restrict (real : Bool) (q : Query C) :
    jointHash (restrictTh prims) real q = jointHash prims real q := by
  simp only [jointHash, hashAnswer_restrict]

theorem jointLocal_restrict (real : Bool) :
    jointLocal (C := C) (restrictTh prims) real = jointLocal prims real := by
  funext q
  simp only [jointLocal, jointHash_restrict, aes_restrict]

theorem jointKeyWorldCore_restrict (real : Bool) :
    jointKeyWorldCore (restrictTh prims) D real = jointKeyWorldCore prims D real := by
  funext q
  unfold jointKeyWorldCore
  rw [jointLocal_restrict, aes_restrict]

theorem jointKeyWorld_restrict (real : Bool) :
    jointKeyWorld (restrictTh prims) D real = jointKeyWorld prims D real := by
  funext q
  unfold jointKeyWorld
  rw [jointKeyWorldCore_restrict]

theorem probBad_streamKey_restrict (game : OracleComp (WorldSpec C) Bool) :
    probBad_streamKey (restrictTh prims) D game = probBad_streamKey prims D game := by
  simp only [probBad_streamKey, jointKeyWorld_restrict]

theorem localImpl_restrict :
    LifetimePrfTransportProof.localImpl (C := C) (restrictTh prims) = LifetimePrfTransportProof.localImpl prims := by
  funext t
  unfold LifetimePrfTransportProof.localImpl
  rw [localAnswer_restrict]

theorem withHidden_restrict
    (hidden : PrgInput C → StateT (LifetimePrfTransportProof.IdealState C) ProbComp Bit) :
    LifetimePrfTransportProof.withHidden (restrictTh prims) D hidden =
      LifetimePrfTransportProof.withHidden prims D hidden := by
  funext t
  unfold LifetimePrfTransportProof.withHidden
  rw [localAnswer_restrict]

theorem leftImpl_restrict :
    LifetimePrfTransportProof.leftImpl (restrictTh prims) D = LifetimePrfTransportProof.leftImpl prims D := by
  simp only [LifetimePrfTransportProof.leftImpl, localImpl_restrict, withHidden_restrict]

theorem worldAnswer_restrict : worldAnswer (C := C) (restrictTh prims) = worldAnswer prims := by
  simp only [worldAnswer, localAnswer_restrict]

theorem evalEmulation_restrict {α : Type} (p : EmulationM C α) :
    LifetimeSlotTransport.evalEmulation (restrictTh prims) p = LifetimeSlotTransport.evalEmulation prims p := by
  simp only [LifetimeSlotTransport.evalEmulation, worldAnswer_restrict]

theorem evalSlot_restrict {α : Type} (p : StateT (LifetimeSlots.SlotState C E) (EmulationM C) α) :
    LifetimeSlotTransport.evalSlot (restrictTh prims) p = LifetimeSlotTransport.evalSlot prims p := by
  simp only [LifetimeSlotTransport.evalSlot, evalEmulation_restrict]

variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
variable (A : LifetimeAdversary C E)

theorem rawKernel_restrict (keys : C.Party → Keys C) (h : C.Party) (sep : Bool) :
    LifetimeSlotTransport.rawKernel K circuits settings attempts k D keys h (restrictTh prims) sep =
      LifetimeSlotTransport.rawKernel K circuits settings attempts k D keys h prims sep := by
  funext t
  simp only [LifetimeSlotTransport.rawKernel, evalSlot_restrict]

theorem markedKernel_restrict (keys : C.Party → Keys C) (h : C.Party) :
    LifetimeSlotTransport.markedKernel K circuits settings attempts k D keys h (restrictTh prims) =
      LifetimeSlotTransport.markedKernel K circuits settings attempts k D keys h prims := by
  funext t
  simp only [LifetimeSlotTransport.markedKernel, rawKernel_restrict]

theorem keygenPrefix_restrict :
    LifetimeSlotTransport.keygenPrefix D A (restrictTh prims) = LifetimeSlotTransport.keygenPrefix D A prims := by
  simp only [LifetimeSlotTransport.keygenPrefix, worldAnswer_restrict]

/-- The separated slot world reads `Th` only on the inputs that the MPC evaluates. -/
theorem markedGame_restrict :
    LifetimeSlotTransport.markedGame K circuits settings attempts k D A (restrictTh prims) =
      LifetimeSlotTransport.markedGame K circuits settings attempts k D A prims := by
  simp only [LifetimeSlotTransport.markedGame, keygenPrefix_restrict, markedKernel_restrict]

end Bridges

section Bounds

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The stream-key bad event of hybrid `n` at the fixed `prims` fits the real share. -/
theorem realBad_fixed (Q : ℕ) (hQ : HasLifetimeQueryBound K circuits settings attempts D A Q)
    (hsplit : keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) < 2)
    (n : Fin (lifetimeRuns attempts)) :
    probBad_streamKey prims D (LifetimeHybridOrder.emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) ≤
      (LifetimePrfTransportProof.realShare C attempts Q (ceremonyFuel circuits settings) : ℝ) / 2 ^ 256 := by
  have h := LifetimeRealBadSum.realBadBound K settings attempts prims.aes (fun _ => circuits) D A Q
    ((LifetimeO3Bridge.hasLifetimeQueryBound_const K circuits settings attempts D A Q).1 hQ) hsplit n
    (fun x => prims.Th x.1)
  rw [show (⟨thOf fun x => prims.Th x.1, prims.aes⟩ : Primitives) = restrictTh prims from rfl,
    probBad_streamKey_restrict] at h
  exact h

/-- The bad event of the ideal side of hop `n` at the fixed `prims` fits the ideal share. -/
theorem idealBad_fixed (Q : ℕ) (hQ : HasLifetimeQueryBound K circuits settings attempts D A Q)
    (hsplit : keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) < 2)
    (n : Fin (lifetimeRuns attempts)) :
    (Pr[LifetimePrfTransportProof.IdealBad ∘ Prod.snd |
      (simulateQ (LifetimePrfTransportProof.leftImpl prims D)
        (LifetimePrfTransportProof.program4 D K circuits settings attempts A n)).run
          LifetimePrfTransportProof.idealStart]).toReal ≤
      (LifetimePrfTransportProof.idealShare C attempts Q : ℝ) / 2 ^ 256 := by
  have h := LifetimeIdealEarlyCache.idealBadBound K settings attempts D A prims.aes (fun _ => circuits) Q
    ((LifetimeO3Bridge.hasLifetimeQueryBound_const K circuits settings attempts D A Q).1 hQ) hsplit n
    (fun x => prims.Th x.1)
  rw [show (⟨thOf fun x => prims.Th x.1, prims.aes⟩ : Primitives) = restrictTh prims from rfl,
    leftImpl_restrict] at h
  exact h

theorem chronologicalProbability_mem (n : ℕ) :
    0 ≤ LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n ∧
      LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, LifetimeAllowance.toReal_le_one probEvent_le_one⟩

theorem reductionProbability_mem (real : Bool) (n : ℕ) :
    0 ≤ LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A real n ∧
      LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A real n ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, LifetimeAllowance.toReal_le_one probOutput_le_one⟩

/-- The two transports of PRF hop `n` at the fixed `prims` fit in `keySplit (q₀ + q)`. -/
theorem prfTransport_fixed (Q : ℕ) (hQ : HasLifetimeQueryBound K circuits settings attempts D A Q)
    (n : Fin (lifetimeRuns attempts)) :
    |LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n -
      LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A true n| +
    |LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A false n -
      LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A (n + 1)| ≤
      keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) := by
  by_cases hsplit : keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) < 2
  · have h1 := (LifetimeO3Bridge.real_transport prims K circuits settings attempts D A n).trans
      (realBad_fixed prims K circuits settings attempts D A Q hQ hsplit n)
    have h2 := (LifetimeO3Bridge.ideal_transport prims K circuits settings attempts D A n).trans
      (idealBad_fixed prims K circuits settings attempts D A Q hQ hsplit n)
    have he := LifetimePrfTransportProof.shares_eq (C := C) attempts Q (ceremonyFuel circuits settings)
    linarith
  · have h0 := chronologicalProbability_mem prims K circuits settings attempts D A n
    have h1 := chronologicalProbability_mem prims K circuits settings attempts D A (n + 1)
    have ht := reductionProbability_mem prims K circuits settings attempts D A true n
    have hf := reductionProbability_mem prims K circuits settings attempts D A false n
    have ha : |LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n -
        LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A true n| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [h0.2, ht.1], by linarith [h0.1, ht.2]⟩
    have hb : |LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A false n -
        LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A (n + 1)| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [hf.2, h1.1], by linarith [hf.1, h1.2]⟩
    exact (add_le_add ha hb).trans (by linarith [not_lt.1 hsplit])

/-- One chronological PRF hop at the fixed `prims`, with the PRF advantage of the reduction of the
statement and `keySplit (q₀ + q)`. -/
theorem prfHop_fixed (Q : ℕ) (hQ : HasLifetimeQueryBound K circuits settings attempts D A Q)
    (n : Fin (lifetimeRuns attempts)) :
    |LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n -
      LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A (n + 1)| ≤
      PRFScheme.prfAdvantage (hiddenStreams prims.aes)
        (lifetimeRunReduction K circuits settings attempts prims D A n) +
      keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) := by
  have ht := prfTransport_fixed prims K circuits settings attempts D A Q hQ n
  have hreal := abs_sub_le
    (LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n)
    (LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A true n)
    (LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A false n)
  have hideal := abs_sub_le
    (LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A n)
    (LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A false n)
    (LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A (n + 1))
  have hgap : |LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A true n -
      LifetimeO3Bridge.reductionProbability prims K circuits settings attempts D A false n| =
      PRFScheme.prfAdvantage (hiddenStreams prims.aes)
        (lifetimeRunReduction K circuits settings attempts prims D A n) := rfl
  linarith

theorem chronologicalProbability_zero :
    LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A 0 =
      lifetimeAdvantage prims K circuits settings attempts D A := by
  simp [LifetimeO3Bridge.chronologicalProbability, LifetimeHybridOrder.chronologicalGame, lifetimeAdvantage]

/-- The PRF pass in time order at the fixed `prims`, with one `keySplit (q₀ + q)` for each run. -/
theorem prfPass_fixed (Q : ℕ) (hQ : HasLifetimeQueryBound K circuits settings attempts D A Q) :
    |lifetimeAdvantage prims K circuits settings attempts D A -
      LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A (lifetimeRuns attempts)| ≤
      (∑ n : Fin (lifetimeRuns attempts), PRFScheme.prfAdvantage (hiddenStreams prims.aes)
        (lifetimeRunReduction K circuits settings attempts prims D A n)) +
      (lifetimeRuns attempts : ℝ) *
        keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) := by
  let e : ℕ → ℝ := fun n => PRFScheme.prfAdvantage (hiddenStreams prims.aes)
    (lifetimeRunReduction K circuits settings attempts prims D A n) +
    keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q)
  have ht := abs_sub_le_sum_of_hybrid
    (LifetimeO3Bridge.chronologicalProbability prims K circuits settings attempts D A)
    (lifetimeRuns attempts) e (fun n hn => prfHop_fixed prims K circuits settings attempts D A Q hQ ⟨n, hn⟩)
  rw [chronologicalProbability_zero] at ht
  have he : (∑ n ∈ Finset.range (lifetimeRuns attempts), e n) =
      (∑ n : Fin (lifetimeRuns attempts), PRFScheme.prfAdvantage (hiddenStreams prims.aes)
        (lifetimeRunReduction K circuits settings attempts prims D A n)) +
      (lifetimeRuns attempts : ℝ) *
        keySplit C (Q + lifetimeOverhead C attempts Q + (ceremonyFuel circuits settings + 2) * Q) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rwa [he] at ht

end Bounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.jointHash_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointHash_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.jointLocal_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointLocal_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.jointKeyWorldCore_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointKeyWorldCore_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.jointKeyWorld_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointKeyWorld_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.probBad_streamKey_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probBad_streamKey_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.localImpl_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localImpl_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.withHidden_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withHidden_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.leftImpl_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leftImpl_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.worldAnswer_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worldAnswer_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.evalEmulation_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalEmulation_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.evalSlot_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalSlot_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.rawKernel_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rawKernel_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.markedKernel_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms markedKernel_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.keygenPrefix_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenPrefix_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.markedGame_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms markedGame_restrict

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.realBad_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realBad_fixed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.idealBad_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealBad_fixed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.prfTransport_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfTransport_fixed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.prfHop_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfHop_fixed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.chronologicalProbability_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chronologicalProbability_zero

/-- info: 'ThresholdLeanXmssSecurity.LifetimeO3BadBridge.prfPass_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfPass_fixed

end ThresholdLeanXmssSecurity.LifetimeO3BadBridge
