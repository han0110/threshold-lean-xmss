import ThresholdLeanXmssSecurity.Proof.SigningCacheLog
import ThresholdLeanXmssSecurity.Proof.SigningAssembly

/-!
# The eager grind with the randomizer from the cache

The honest randomizer of a run is `cachedRandomizer x.2.1 cache e`, a read of uniform PRF answers.
So the trigger of the eager grind reads it from the cache of the state. `SigningOneRun` uses this
trigger on the joint run.

## The trigger

* `cachedExtra seeds P` runs `grindExtra P (cachedRandomizer seeds cache)` at a base call of a key
  `e` whose PRF entries `.prf (seeds T) (.randomizer bottomLayer e)` are all cached
  (`RandomizerCached`). `cache` is the cache of the state before the call.
* At a base call of a key with an uncached PRF entry the trigger runs no grind. The value
  `cachedRandomizer` reads `0` at an uncached entry, so it is not yet the randomizer of the key.
  A grind on it could install a wrong target at `e` and so block the install of the honest
  selection. Once all entries are cached the value is stable (`cachedRandomizer_stable`). So each
  grind at `e` runs on one base input.
* The eager law does not read the trigger. It holds for each `extra` (`hashLaw_eagerWorld`), so the
  guard costs nothing there.

## The limit of the trigger

The trigger does not cover every bottom partner. A forger can call the base input and the trials at
a key `e` before round 1 binds the message at `e`. None of these calls is a base call, because
`bound e` is unset. Round 1 then binds the message and makes no base call. If no base call of `e`
comes after round 1, the trigger never grinds at `e`. So the argument for a released partner needs
an honest round 2 at `e`, which makes the base call. An unreleased partner needs the separate
input-side argument of `SigningLinkPaid`.

## The results

* `baseCall_key_eq` says that one call is a base call of at most one key
  (`randomizerInput_key_eq`).
* `baseGrind_signed_ne` says that a grind at `e` signs no other key. Each trial is a message digest
  input of `e`, and `encodingInputLeafIndex?` reads `e` from it.
* `randomizerCached_mono` says that a larger cache keeps the PRF entries of a key cached.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningR1FixedProof

open HashSig LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningHitLaneProof
  SigningPartnerBoundProof

variable {C : Committee} (prims : Primitives)

section Trigger

open Classical in
/-- The eager grind at a base call of a key `e` whose PRF entries are all cached, on the randomizer
that the cache of the state gives. At a base call with an uncached PRF entry it runs no grind. -/
def cachedExtra (seeds : C.Term → HashOutput) (P : PublicParameter) (p : FlatState C)
    (t : (WorldSpec C).Domain) (p' : FlatState C) : OracleComp (Query C →ₒ HashOutput) Unit :=
  if ∃ e, SigningGuessProof.RandomizerCached seeds p.1.1.1 e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds p.1.1.1 e) p.2.1 t then
    grindExtra P (SigningGuessProof.cachedRandomizer seeds p.1.1.1) p t p'
  else pure ()

/-- One call is a base call of at most one key. -/
theorem baseCall_key_eq {P : PublicParameter} {e f : KeyIndex} {ρ τ : Digest} {st : TsigState C}
    {t : (WorldSpec C).Domain} (he : BaseCall P e ρ st t) (hf : BaseCall P f τ st t) : e = f := by
  obtain ⟨input, hin, hcall⟩ := he
  obtain ⟨input', hin', hcall'⟩ := hf
  have heq : input = input' := by
    rcases hcall with rfl | rfl <;> rcases hcall' with h | h <;> simp_all
  subst heq
  simp only [baseInput, Option.map_eq_some_iff] at hin hin'
  obtain ⟨m, -, rfl⟩ := hin
  obtain ⟨m', -, h⟩ := hin'
  exact (SigningGuessProof.randomizerInput_key_eq P h).symm

end Trigger

section Witness

open SigningCacheLogProof

/-- An invariant of each trial of a grind at `e` on `message` holds after the grind. -/
theorem grind_inv (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (e : KeyIndex) (message : Message) (base : Randomizer) (Inv : HashCache C × Monitor → Prop)
    (hstep : ∀ randomness s, Inv s → ∀ w ∈ support ((monitoredOracle keyOf
      (.hash (tweakableHashInput P (.message bottomLayer e) (littleEndianBytes 32 message ++ littleEndianBytes 16 randomness)))).run s),
      Inv w.2) :
    ∀ attempts trial s, Inv s → ∀ z ∈ support ((simulateQ (monitoredOracle keyOf)
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (littleEndianBytes 32 message) base attempts trial))).run s), Inv z.2 := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s hs z hz
    simp only [grind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | succ n ih =>
    intro trial s hs z hz
    simp [grind, Verification.messageDigestWithHash, Verification.tweakableHashWithHash, Verification.thWithHash,
      Verification.oracleHashWithHash] at hz
    obtain ⟨a, a1, b, hw, hz⟩ := hz
    have hmid := hstep _ s hs _ hw
    cases hdec : Codeword.decode (truncateHash a) with
    | some encoding =>
      simp only [hdec, simulateQ_pure, StateT.run_pure] at hz
      subst hz
      exact hmid
    | none =>
      simp only [hdec] at hz
      exact ih (trial + 1) (a1, b) hmid z hz

/-- An invariant of each trial of a grind at `e` on `message` holds after `baseGrind`. -/
theorem baseGrind_inv (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (e : KeyIndex) (message : Message) (answer : HashOutput) (Inv : HashCache C × Monitor → Prop)
    (hstep : ∀ randomness s, Inv s → ∀ w ∈ support ((monitoredOracle keyOf
      (.hash (tweakableHashInput P (.message bottomLayer e) (littleEndianBytes 32 message ++ littleEndianBytes 16 randomness)))).run s),
      Inv w.2)
    (s : HashCache C × Monitor) (hs : Inv s)
    (z : Unit × (HashCache C × Monitor)) (hz : z ∈ support ((simulateQ (monitoredOracle keyOf)
      (baseGrind P e message answer)).run s)) : Inv z.2 := by
  simp only [baseGrind, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact grind_inv keyOf P e message _ Inv hstep _ _ s hs y hy

/-- A fresh call on the counted copy never signs a key and never changes a signed key. -/
theorem fresh_query_signed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) :
    (m.fresh keyOf input digest false).state.signed = m.state.signed := by
  cases hk : keyOf input with
  | none => rw [m.fresh_none keyOf input digest false hk]
  | some e =>
    cases hs : m.state.signed e with
    | none =>
      rw [m.fresh_unsigned keyOf input digest false e hk hs]
      split_ifs <;> simp_all [XmssSecurity.EncodingMonitor.State.addPending]
    | some target => rw [m.fresh_signed keyOf input digest false e hk target hs]

/-- The query step of a logged call keeps the signed keys. -/
theorem queryEntryStep_signed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (entry : Option (XmssSecurity.HashInput × XmssSecurity.Digest × Bool)) :
    (queryEntryStep keyOf m entry).state.signed = m.state.signed := by
  cases entry with
  | none => rfl
  | some entry =>
    simp only [queryEntryStep, Monitor.step]
    split_ifs
    · rfl
    · exact fresh_query_signed keyOf m _ _

/-- A trial at an input of key `e` keeps the signed state of each other key. -/
theorem trialStep_signed_ne (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (m : Monitor)
    (input : XmssSecurity.HashInput) (output : HashOutput) (e f : XmssSecurity.LeafIndex)
    (hk : keyOf input = some e) (hf : f ≠ e) :
    (trialStep (C := C) keyOf m (.hash input) output).state.signed f = m.state.signed f := by
  simp only [trialStep]
  split_ifs
  · rfl
  · unfold trialFresh
    split
    · rfl
    · exact (SigningUnchargedLoggedProof.fresh_state_at keyOf f m input _ true
        (by rw [hk]; exact fun h => hf (Option.some_injective _ h).symm)).1

/-- A grind at `e` keeps the signed state of each other key. -/
theorem baseGrind_signed_ne (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput)
    (s : HashCache C × Monitor) (z : Unit × (HashCache C × Monitor))
    (hz : z ∈ support ((simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? P))
      (baseGrind P e message answer)).run s)) (f : KeyIndex) (hf : f ≠ e) :
    z.2.2.state.signed f = s.2.state.signed f := by
  refine baseGrind_inv _ P e message answer (fun w => w.2.state.signed f = s.2.state.signed f)
    (fun randomness w hw v hv => ?_) s rfl z hz
  simp only [monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hv
  obtain ⟨u, -, rfl⟩ := hv
  rw [← hw]
  exact trialStep_signed_ne (C := C) _ w.2 _ _ e f
    (SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message _) hf

/-- `RandomizerCached` holds on a larger cache. -/
theorem randomizerCached_mono {seeds : C.Term → HashOutput} {left right : HashCache C} {e : KeyIndex}
    (hle : left ≤ right) (h : SigningGuessProof.RandomizerCached seeds left e) :
    SigningGuessProof.RandomizerCached seeds right e := fun T => by
  obtain ⟨v, hv⟩ := h T
  exact ⟨v, hle hv⟩

end Witness

end SigningR1FixedProof

end ThresholdLeanXmssSecurity
