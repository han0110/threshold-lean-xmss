import ThresholdLeanXmssSecurity.Proof.LifetimeJointLink
import ThresholdLeanXmssSecurity.Proof.LifetimeTranscriptReplay
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# Chronological lifetime PRF hybrids

The chronological worlds run the real keygen. Their hidden streams share the
same `StreamCache` as `lifetimeRunReductionSampled`; the sampled `Th`, adversary and
real keygen remain inside each experiment. The subsequent dealer world changes
keygen once and retains the actual lifetime scheduler and random streams.

There are two different random-stream tables in the ideal experiment of
`lifetimeRunReductionSampled n`: the earlier runs use `EmulationM`'s table, while run
`n` uses the PRF oracle's table. Consequently its output law is not definitionally
the next chronological world. A repeated PRSS key and stream coordinate makes
the next world reuse a bit, whereas the reduction samples an independent bit.
Fresh PRSS setup does not rule out this event. Its key has 256 bits; it is not
an additional collision of 128-bit AES keys.

The transport contract below charges both sides of the PRF experiment together
against the existing `streamKeyError + keySplit` allowance. Charging each side
the full allowance would not give the lifetime statement. The conditional
assembly cancels `keySplit` once per slot and keeps the prescribed reductions.
It does not identify the shared-cache lifetime with a selected ceremony whose
hidden-stream cache starts empty.

The pinned and current leanVM bridge and replay sources were searched. The
threshold-specific chronological scheduler and shared PRSS cache require the
existing lifetime definitions; the sum uses `abs_sub_le_sum_of_hybrid` and
`sum_lifetime_slot_error`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeHybridOrder

open LifetimeJointLink

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- An earlier emulated run fixes the answer when a PRSS key and coordinate repeat. -/
theorem cached_stream (x : PrgInput C) (cache : StreamCache C) (b : Bit)
    (h : cache x = some b) :
    ((PrgInput C →ₒ Bit).randomOracle x).run cache = pure (b, cache) :=
  QueryImpl.withCaching_run_some _ h

/-- The independent table of the PRF ideal experiment resamples that coordinate. -/
theorem fresh_stream (x : PrgInput C) :
    Prod.fst <$> ((PrgInput C →ₒ Bit).randomOracle x).run ∅ = ($ᵗ Bit) := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ (by rfl)]
  simp [uniformSampleImpl, Functor.map_map]

/-- A concrete table state witnessing failure of unconditional cache reset.
This is a counterexample to exact stream-table equality, not to the lifetime bound. -/
theorem cached_stream_ne_fresh (x : PrgInput C) (b : Bit) :
    Prod.fst <$> ((PrgInput C →ₒ Bit).randomOracle x).run
        ((∅ : StreamCache C).cacheQuery x b) ≠
      Prod.fst <$> ((PrgInput C →ₒ Bit).randomOracle x).run ∅ := by
  rw [cached_stream x _ b (QueryCache.cacheQuery_self _ _ _), map_pure, fresh_stream]
  intro h
  have hp := congrArg (fun p : ProbComp Bit => Pr[= b | p]) h
  simp only [probOutput_pure_self, probOutput_uniformSample] at hp
  have hpR := congrArg ENNReal.toReal hp
  norm_num [Bit, ZMod.card] at hpR

/-- Forget only the private stream table and observation log of an emulation. -/
def emulationGame (p : EmulationM C Bool) : OracleComp (WorldSpec C) Bool :=
  (fun r => r.1.1) <$> (p.run ∅).run

/-- The real lifetime at zero, then the actual real-keygen chronological hybrids.
The explicit zero branch fixes the initial world without an extra equality premise. -/
def chronologicalGame (circuits : Circuits) (n : ℕ) : OracleComp (WorldSpec C) Bool :=
  if n = 0 then lifetimeGame K circuits settings attempts D A else
    emulationGame (lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n)
      (lifetimeHybridRoles D n n) D A)

def chronologicalProbability (n : ℕ) : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRunSampled aes fun Th =>
    chronologicalGame K settings attempts D A (circuitsOf Th) n]).toReal

theorem chronologicalProbability_zero :
    chronologicalProbability K settings attempts aes circuitsOf D A 0 =
      lifetimeAdvantageSampled K settings attempts aes circuitsOf D A := by
  simp [chronologicalProbability, chronologicalGame, lifetimeAdvantageSampled]

/-- The two probabilities use the exact reduction named by the statement. -/
def reductionProbability (real : Bool) (n : ℕ) : ℝ :=
  (Pr[= true | if real then
    (hiddenStreams aes).prfRealExp
      (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)
    else PRFScheme.prfIdealExp
      (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)]).toReal

theorem reductionProbability_gap (n : ℕ) :
    |reductionProbability K settings attempts aes circuitsOf D A true n -
      reductionProbability K settings attempts aes circuitsOf D A false n| =
      PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) := rfl

/-- The shared-table and separate-table transports must fit one allocation of
the original key-hop error. This contract does not assume a PRF security bound. -/
def LifetimePrfTransport (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  ∀ n : Fin (lifetimeRuns attempts),
    |chronologicalProbability K settings attempts aes circuitsOf D A n -
      reductionProbability K settings attempts aes circuitsOf D A true n| +
    |reductionProbability K settings attempts aes circuitsOf D A false n -
      chronologicalProbability K settings attempts aes circuitsOf D A (n + 1)| ≤
      streamKeyError C + keySplit C (q₀ + q)

/-- One chronological PRF hop, with real keygen and the prescribed reduction. -/
def LifetimePrfHop (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  ∀ n : Fin (lifetimeRuns attempts),
    |chronologicalProbability K settings attempts aes circuitsOf D A n -
      chronologicalProbability K settings attempts aes circuitsOf D A (n + 1)| ≤
      PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) +
          streamKeyError C + keySplit C (q₀ + q)

theorem lifetimePrfHop_of_transport (Q : ℕ)
    (h : LifetimePrfTransport K settings attempts aes circuitsOf D A Q) :
    LifetimePrfHop K settings attempts aes circuitsOf D A Q := by
  intro n
  have ht := h n
  have hreal := abs_sub_le
    (chronologicalProbability K settings attempts aes circuitsOf D A n)
    (reductionProbability K settings attempts aes circuitsOf D A true n)
    (reductionProbability K settings attempts aes circuitsOf D A false n)
  have hideal := abs_sub_le
    (chronologicalProbability K settings attempts aes circuitsOf D A n)
    (reductionProbability K settings attempts aes circuitsOf D A false n)
    (chronologicalProbability K settings attempts aes circuitsOf D A (n + 1))
  rw [reductionProbability_gap] at hreal
  linarith

/-- The entire PRF pass in time order. No keygen error is repeated. -/
theorem lifetimePrfPass (Q : ℕ)
    (h : LifetimePrfHop K settings attempts aes circuitsOf D A Q) :
    |lifetimeAdvantageSampled K settings attempts aes circuitsOf D A -
      chronologicalProbability K settings attempts aes circuitsOf D A (lifetimeRuns attempts)| ≤
      (∑ n : Fin (lifetimeRuns attempts), PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)) +
      (lifetimeRuns attempts : ℝ) * (streamKeyError C +
        keySplit C (Q + lifetimeOverhead C attempts Q +
          (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)) := by
  let e : ℕ → ℝ := fun n => PRFScheme.prfAdvantage (hiddenStreams aes)
    (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) + streamKeyError C +
    keySplit C (Q + lifetimeOverhead C attempts Q +
      (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)
  have ht := abs_sub_le_sum_of_hybrid
    (chronologicalProbability K settings attempts aes circuitsOf D A)
    (lifetimeRuns attempts) e (fun n hn => h ⟨n, hn⟩)
  rw [chronologicalProbability_zero] at ht
  have he : (∑ n ∈ Finset.range (lifetimeRuns attempts), e n) =
      (∑ n : Fin (lifetimeRuns attempts), PRFScheme.prfAdvantage (hiddenStreams aes)
        (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)) +
      (lifetimeRuns attempts : ℝ) * (streamKeyError C +
        keySplit C (Q + lifetimeOverhead C attempts Q +
          (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [e, add_assoc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rwa [he] at ht

/-- The actual scheduler continuation after keygen, in the same emulation monad. -/
def afterKeygen (circuits : Circuits) (state : A.keygen.State)
    (outputs : C.Party → Option (Keys C)) : EmulationM C Bool := do
  let base := lifetimeHybridRoles D 0 0
  let some h := C.parties.find? (· ∉ D.1) | pure false
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure false else do
  let keys := fun i => (outputs i).getD default
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → EmulationM C β :=
    fun oa => base.honest (liftComp oa _)
  let value := fun x => lift (prfValue (honestSeeds D keys) x)
  let forger : QueryImpl (LocalSpec C) (StateT (LifetimeState C E) (EmulationM C)) :=
    fun t => StateT.lift (base.adversary (OracleComp.lift (OracleSpec.query t)))
  let (forgery, st) ← (simulateQ
    (forger + lifetimeOraclesWith K circuits settings attempts (fun _ => emulatedRoles D)
      base D keys value h) (A.run state (keys h).parameter)).run
    ⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none,
      0, fun _ => 0, ∅, none⟩
  if ¬ ∀ i, i ∉ D.1 → (st.top i).isSome then pure false else do
  let some (_, top) := st.publicKey (keys h).parameter h | pure false
  forgeryWins lift (dealtWith lift (keys h).parameter keys top value) st.sign forgery

/-- Replace keygen once by its actual functionality and simulator. The remaining
lifetime scheduler keeps all hidden streams random in one shared table. -/
def dealerKeygenGame (circuits : Circuits) : OracleComp (WorldSpec C) Bool :=
  emulationGame (do
    let (state, outputs) ← StateT.lift (liftM
      (idealExecution (fun p => p) D Fkeygen (keygenSimulator D A.keygen)
        (fun _ => ()) []))
    afterKeygen K settings attempts D A circuits state outputs)

def dealerKeygenProbability : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRunSampled aes fun Th =>
    dealerKeygenGame K settings attempts D A (circuitsOf Th)]).toReal

/-- The single keygen hop after every chronological PRF hop. -/
def LifetimeKeygenHop (Q : ℕ) : Prop :=
  |chronologicalProbability K settings attempts aes circuitsOf D A (lifetimeRuns attempts) -
    dealerKeygenProbability K settings attempts aes circuitsOf D A| ≤
    keygenHashError C ((setupRounds + 2) * Q)

/-- The simulation and forger bound on the fixed dealer-keygen world. Its slot
errors reserve `keySplit` for the preceding chronological pass. It is a source
contract on this concrete world, not a choice of intermediate probabilities. -/
def LifetimeAfterKeygen (Q : ℕ) : Prop :=
  let circuits := circuitsOf fun _ => 0
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel circuits settings + 2) * Q
  dealerKeygenProbability K settings attempts aes circuitsOf D A ≤
    (∑ slot : Slot attempts,
      (treeCheckError (E := E) circuits settings (slotTree slot) (q₀ + q) +
        (treeHashError circuits settings C (slotTree slot) (q₀ + q) - keySplit C (q₀ + q)) +
        seedHitError C (q₀ + q))) +
      2 ^ layerHeight * searchFailure + signingHashError q₀ +
      seedHitError C q₀ + seedCollisionError C

/-- The key split occurs equally often in time order and in the fixed slot order. -/
theorem slot_split_cancel (circuits : Circuits) (q₀ q : ℕ) :
    (lifetimeRuns attempts : ℝ) * (streamKeyError C + keySplit C (q₀ + q)) +
      (∑ slot : Slot attempts,
        (treeCheckError (E := E) circuits settings (slotTree slot) (q₀ + q) +
          (treeHashError circuits settings C (slotTree slot) (q₀ + q) - keySplit C (q₀ + q)) +
          seedHitError C (q₀ + q))) =
      (let runError := fun tree => (attempts : ℝ) *
        (treeCheckError (E := E) circuits settings tree (q₀ + q) +
          treeHashError circuits settings C tree (q₀ + q) + streamKeyError C +
          seedHitError C (q₀ + q))
       runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) := by
  rw [← sum_lifetime_slot_error (C := C) (E := E) attempts circuits settings q₀ q]
  have hc : (∑ _ : Slot attempts, (streamKeyError C + keySplit C (q₀ + q))) =
      (lifetimeRuns attempts : ℝ) * (streamKeyError C + keySplit C (q₀ + q)) := by
    rw [Finset.sum_const, Finset.card_univ, slot_card, nsmul_eq_mul]
  rw [← hc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro slot _
  ring

/-- The statement's exact inequality follows from the chronological pass, one
keygen hop, and the fixed dealer-world simulation contract. -/
theorem lifetime_bound_of_hops (Q : ℕ)
    (hprf : LifetimePrfHop K settings attempts aes circuitsOf D A Q)
    (hkeygen : LifetimeKeygenHop K settings attempts aes circuitsOf D A Q)
    (hrest : LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q) :
    let circuits := circuitsOf fun _ => 0
    let q₀ := Q + lifetimeOverhead C attempts Q
    let q := (ceremonyFuel circuits settings + 2) * Q
    let runError := fun tree => (attempts : ℝ) *
      (treeCheckError (E := E) circuits settings tree (q₀ + q) +
        treeHashError circuits settings C tree (q₀ + q) + streamKeyError C +
        seedHitError C (q₀ + q))
    lifetimeAdvantageSampled K settings attempts aes circuitsOf D A ≤
      keygenHashError C ((setupRounds + 2) * Q) +
        (runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) +
        ∑ n : Fin (lifetimeRuns attempts),
          PRFScheme.prfAdvantage (hiddenStreams aes)
            (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) +
        2 ^ layerHeight * searchFailure + signingHashError q₀ +
        seedHitError C q₀ + seedCollisionError C := by
  dsimp only
  have hp := (le_abs_self _).trans (lifetimePrfPass K settings attempts aes circuitsOf D A Q hprf)
  have hk := (le_abs_self _).trans hkeygen
  have hs := slot_split_cancel (C := C) (E := E) settings attempts
    (circuitsOf fun _ => 0) (Q + lifetimeOverhead C attempts Q)
    ((ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)
  dsimp only [LifetimeAfterKeygen] at hrest
  linarith

/-- Full quantifiers of the original target, with source contracts evaluated on
one prescribed family of concrete worlds for every adversary. -/
theorem lifetimeSecurity_of_sources
    (hsource : (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf →
      0 < settings.batchSize → ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
        HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
        LifetimePrfTransport K settings attempts aes circuitsOf D A Q ∧
        LifetimeKeygenHop K settings attempts aes circuitsOf D A Q ∧
        LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q) :
    LifetimeSecurityStatementSampled K settings attempts aes circuitsOf := by
  intro hcompute hshape hbatch D A Q hQ
  obtain ⟨hp, hk, hr⟩ := hsource hcompute hshape hbatch D A Q hQ
  exact lifetime_bound_of_hops K settings attempts aes circuitsOf D A Q
    (lifetimePrfHop_of_transport K settings attempts aes circuitsOf D A Q hp) hk hr

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.cached_stream_ne_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cached_stream_ne_fresh

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.chronologicalProbability_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chronologicalProbability_zero

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.lifetimePrfHop_of_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimePrfHop_of_transport

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.lifetimePrfPass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimePrfPass

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.slot_split_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slot_split_cancel

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.lifetime_bound_of_hops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetime_bound_of_hops

/-- info: 'ThresholdLeanXmssSecurity.LifetimeHybridOrder.lifetimeSecurity_of_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeSecurity_of_sources

end ThresholdLeanXmssSecurity.LifetimeHybridOrder
