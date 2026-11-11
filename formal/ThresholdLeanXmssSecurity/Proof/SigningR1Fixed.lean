import ThresholdLeanXmssSecurity.Proof.SigningCacheLog
import ThresholdLeanXmssSecurity.Proof.SigningAssembly

/-!
# The eager grind with the randomizer from the cache

`R1Link ρ` of `SigningFlatEager` is false for each fixed `ρ` (end of `SigningCacheLog`). The
honest randomizer of a run is `cachedRandomizer x.2.1 cache e`, a read of uniform PRF answers. So
the trigger of the eager grind reads it from the cache of the state.

## The trigger

* `cachedExtra seeds P` runs `grindExtra P (cachedRandomizer seeds cache)` at a base call of a key
  `e` whose PRF entries `.prf (seeds T) (.randomizer bottomLayer e)` are all cached
  (`RandomizerCached`). `cache` is the cache of the state before the call.
* At a base call of a key with an uncached PRF entry the trigger runs no grind. The value
  `cachedRandomizer` reads `0` at an uncached entry, so it is not yet the randomizer of the key.
  A grind on it could install a wrong target at `e` and so block the install of the honest
  selection. Once all entries are cached the value is stable (`cachedRandomizer_stable`). So each
  grind at `e` runs on one base input, and a later grind is a rerun (`baseGrind_rerun`).
* The eager law and the R1 bound do not read the trigger. They hold for each `extra`
  (`hashLaw_eagerWorld`, `potStep_monitoredGame`), so the guard costs nothing there.

## The results

* `evalDist_flatEagerRun` and `evalDist_flatEagerRun_logged` give the eager law for the new
  trigger. `r1Hit_bound` and `split_r1Hit_bound` give the bound of R1.
* `baseCall_key_eq` says that one call is a base call of at most one key
  (`randomizerInput_key_eq`). `hsigned_of_signed` gives the `hsigned` hypothesis of
  `monitoredWorld_signed_grind` at a base call of a signed key.
* `baseGrind_signed_ne` says that a grind at `e` signs no other key. Each trial is a message digest
  input of `e`, and `encodingInputLeafIndex?` reads `e` from it.
* `signedWitness_step_core` is one world call with no grind or with the grind of `grindExtra P ρ`.
  `signedWitnessStep` proves `SignedWitnessStep` of `SigningCacheLog`.
* `CachedWitness` is `SignedWitness` on the randomizer of the cache, with all PRF entries of each
  signed key cached. `cachedWitness_step` keeps it at each world call of the new run.
  `monitoredWorld_cached_signed_grind` is `monitoredWorld_signed_grind` for the new trigger.
* `R1Link`, `PartnerTransfer` and `PartnerCrossing` are the forms of `SigningFlatEager` and
  `SigningAssembly` on the new run. `partnerCrossing_of_link` gives the crossing from the link.

## `R1Link` is false for this trigger

A trigger at a base call fails if no base call comes after the PRF entries of the key are cached.
The argument is on the support, not a Lean proof.

1. The forger asks `H` at the base input of a key `e` and a message `m` with a guess `ρ'` of the
   randomizer. It then asks the trials of the grind up to the first codeword, and a partner
   `(m', r')` with the same digest. `bound e` is unset, so no call is a base call.
2. The forger asks `.tree (treeOf e)`. The setup caches all PRF entries at `e`. Take a support
   point where their XOR is `ρ'`.
3. The forger asks round 1 at `e` on `m`. Round 1 binds `m` and makes no base call. The forger
   asks no round 2 at `e`, so no call is a base call of `e`.
4. The forger outputs a forgery at `e` on `(m', r')` with guessed chain values that verify. It
   asks no PRF or mask entry, so the flag of `hiddenHit` stays false. No operator released chain
   parts at `e`, so `tsigFinish` does not run `honestSignature`.
5. No grind ran at `e`. No logged call installs a target, so `hit` is false. No grind flagged a
   cached trial, so `CachedSelection` is false. No commitment collides, so `AlternativeCommitment`
   is false. `BottomPartnerCase` holds with the selection of step 1.

A variant leaves out step 2. Then a PRF entry of `e` that round 1 does not ask stays uncached,
and `FinalState.selected` reads it as `0`.

Two changes are open, and each needs a decision.

* The trigger runs the grind at each world call after which the PRF entries, the bound message and
  the base answer of a key are all cached. This removes the counterexample with step 2. A later
  grind is a rerun (`baseGrind_rerun`).
* The variant without step 2 is a chain start with an absent PRF entry, as `ForgedStartAbsent`
  (D17). `R1Link` needs this case as a separate row.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningR1FixedProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningHitLaneProof
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

section Eager

/-- The flat run with the eager grind of `cachedExtra` at the keys `x`. -/
def flatEagerRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (Result C × FlatState C) :=
  (flatGame (eagerWorld prims (cachedExtra x.2.1 x.1)) A x).run flatInit

/-- The flat eager run has the law of `flatRun` for the result, the count, the log and the carried
state. The trigger reads the cache, and the law holds for each extra call. -/
theorem evalDist_flatEagerRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, restOf z.2)) <$> flatEagerRun prims A x] =
      𝒟[(fun z => (z.1, restOf z.2)) <$> flatRun prims A x] := by
  rw [flatRun_eq_flatGame]
  exact evalDist_flatGame_eq prims _ _ (hashLaw_eagerWorld prims _) (hashLaw_carry_logged prims) A x

/-- The flat eager run has the law of `loggedRun` for the result, the count and the log. -/
theorem evalDist_flatEagerRun_logged (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[(fun z => (z.1, z.2.1.1.2, z.2.1.2)) <$> flatEagerRun prims A x] =
      𝒟[(fun z => (z.1, z.2.1.2, z.2.2)) <$> SigningCostProof.loggedRun prims A x] := by
  have h := congrArg (fun d => (fun z : Result C × Rest C (TsigState C × Bool) => (z.1, z.2.1.1, z.2.1.2)) <$> d)
    (evalDist_flatEagerRun prims A x)
  simp only [← evalDist_map, Functor.map_map] at h
  rw [← flatRun_logged, Functor.map_map]
  exact h

end Eager

section Bound

/-- The flat eager run of `cachedExtra` with the R1 monitor. -/
def monitoredRun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    ProbComp (Result C × (SigningHitLaneProof.LoggedState C × Monitor) × (TsigState C × Bool)) :=
  (monitoredGame prims keyOf (cachedExtra x.2.1 x.1) A x).run monitoredInit

theorem monitoredRun_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> monitoredRun prims keyOf A x = flatEagerRun prims A x :=
  monitoredGame_forgets prims keyOf (cachedExtra x.2.1 x.1) A x _ _ _

/-- The hit costs `2^-128` for each keyed call of the log in expectation. -/
theorem probEvent_r1Hit_le_logKeyed (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[R1Hit | monitoredRun prims keyOf A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' z, Pr[= z | monitoredRun prims keyOf A x] *
        (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) := by
  classical
  have hinit : CacheSeen (monitoredInit (C := C)).1.1.1.1 (monitoredInit (C := C)).1.2 :=
    fun input h => (h rfl).elim
  have h := (potStep_monitoredGame prims keyOf (cachedExtra x.2.1 x.1) A x monitoredInit hinit).2
  have hrisk : (monitoredInit (C := C)).1.2.risk = 0 := by
    simp [monitoredInit, Monitor.risk, Monitor.empty, XmssSecurity.CappedEncodingMonitor.State.pendingRisk_empty]
  have hlog : logKeyed keyOf (monitoredInit (C := C)).1.1.2 = 0 := rfl
  rw [hrisk, zero_add, hlog] at h
  simp only [Nat.sub_zero] at h
  refine le_trans ?_ h
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun z => ?_
  split_ifs with hz
  · have hone : z.2.1.2.risk = 1 := by simp [Monitor.risk, show z.2.1.2.hit = true from hz]
    rw [hone, mul_one]
    exact le_rfl
  · exact bot_le

/-- The keyed calls of the log of the flat eager run have the law of those of `loggedRun`. -/
theorem expected_logKeyed_eq (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr[= z | monitoredRun prims keyOf A x] * (logKeyed keyOf z.2.1.1.2 : ℝ≥0∞) =
      ∑' z, Pr[= z | SigningCostProof.loggedRun prims A x] * (logKeyed keyOf z.2.2 : ℝ≥0∞) := by
  have h1 := tsum_probOutput_map_mul (monitoredRun prims keyOf A x) (fun z => (z.1, (z.2.1.1, z.2.2)))
    (fun y => (logKeyed keyOf y.2.1.2 : ℝ≥0∞))
  rw [monitoredRun_forget] at h1
  have h2 := tsum_probOutput_map_mul (flatEagerRun prims A x) (fun z => (z.1, z.2.1.1.2, z.2.1.2))
    (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have h3 := tsum_probOutput_map_mul (SigningCostProof.loggedRun prims A x) (fun z => (z.1, z.2.1.2, z.2.2))
    (fun y => (logKeyed keyOf y.2.2 : ℝ≥0∞))
  have hlaw := evalDist_flatEagerRun_logged prims A x
  rw [← h1, ← h3, ← h2]
  exact tsum_congr fun y => by rw [probOutput_congr rfl hlaw]

/-- The bound of R1 for the trigger of `cachedExtra`. The hit costs `2^-128` for each bottom digest
call, as `bottomPartnerLogged_bound`. -/
theorem r1Hit_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[R1Hit | monitoredRun prims (XmssSecurity.encodingInputLeafIndex? x.1) A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine (probEvent_r1Hit_le_logKeyed prims _ A x).trans ?_
  rw [expected_logKeyed_eq]
  gcongr
  exact (expected_logKeyed_le prims _ A x).trans
    (SigningGuessProof.sourceExpectedCost_mono prims A x _ _ (keyedCost_le_bottomDigestCost x))

end Bound

section Split

/-- The flat eager run of `cachedExtra` with the R1 monitor and the flag of a cached trial. -/
def splitRun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    ProbComp (Result C × ((SigningHitLaneProof.LoggedState C × Monitor) × Bool) × (TsigState C × Bool)) :=
  (splitGame prims keyOf (cachedExtra x.2.1 x.1) A x).run ((monitoredInit.1, false), monitoredInit.2)

theorem splitRun_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> splitRun prims keyOf A x = monitoredRun prims keyOf A x :=
  splitGame_forgets prims keyOf (cachedExtra x.2.1 x.1) A x _ _ _

/-- The bound of R1 on the split run. -/
theorem split_r1Hit_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun z => z.2.1.1.2.hit = true | splitRun prims (XmssSecurity.encodingInputLeafIndex? x.1) A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningPartnerLinkProof.bottomDigestCost x) := by
  refine le_trans (le_of_eq ?_) (r1Hit_bound prims A x)
  rw [← splitRun_forget, probEvent_map]
  rfl

end Split

section Assembly

open SigningAssemblyProof SigningUnchargedLoggedProof

/-- The split run of `cachedExtra` at the public parameter and the seeds of the keys. -/
def splitRunAt (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (SplitOutcome C) :=
  splitRun prims (XmssSecurity.encodingInputLeafIndex? x.1) A x

/-- `R1Link` of `SigningFlatEager` on the split run of `cachedExtra`. A bottom partner win with no
cached selection raises the R1 monitor, unless another opening of a commitment is cached. It is
false for this trigger, by the counterexample in the module doc. -/
def R1Link : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z, z ∈ support (splitRunAt prims A x) →
    z.1.1 = (true, false) → SigningPartnerLinkProof.BottomPartnerCase prims x (z.1, z.2.1.1.1.1) →
    ¬CachedSelection z →
    z.2.1.1.2.hit = true ∨ SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1

/-- `PartnerTransfer` of `SigningAssembly` on the split run of `cachedExtra`. -/
def PartnerTransfer : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[LazyPartnerRow prims x | jointRun prims A x] ≤
      Pr[fun z => EagerPartner prims x z ∧ ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 |
        splitRunAt prims A x]

/-- `PartnerCrossing` of `SigningAssembly` on the split run of `cachedExtra`. -/
def PartnerCrossing : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[LazyPartnerRow prims x | jointRun prims A x] ≤
      Pr[R1HitRow | splitRunAt prims A x] + Pr[CachedPartnerRow prims x | splitRunAt prims A x]

set_option maxRecDepth 100000 in
/-- The crossing of the partner row from `R1Link` and the transfer, as
`SigningAssemblyProof.partnerCrossing_of_link`. -/
theorem partnerCrossing_of_link (hlink : R1Link prims (C := C)) (htransfer : PartnerTransfer prims (C := C)) :
    PartnerCrossing prims (C := C) := by
  unfold PartnerCrossing
  intro A q x hx hkeys hq hsmall
  refine (htransfer A q x hx hkeys hq hsmall).trans ((probEvent_mono fun z hz h => ?_).trans (probEvent_or_le _ _ _))
  obtain ⟨⟨hwin, hpartner⟩, halt⟩ := h
  by_cases hcached : CachedSelection z
  · exact Or.inr ⟨⟨hwin, hpartner⟩, hcached⟩
  · rcases hlink A x z hz hwin hpartner hcached with hhit | hcommit
    · exact Or.inl hhit
    · exact (halt hcommit).elim

end Assembly

section Witness

open SigningCacheLogProof

/-- An invariant of each trial of a grind at `e` on `message` holds after the grind. -/
theorem grind_inv (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (e : KeyIndex) (message : Message) (base : Randomness) (Inv : HashCache C × Monitor → Prop)
    (hstep : ∀ randomness s, Inv s → ∀ w ∈ support ((monitoredOracle keyOf
      (.hash (tweakableHashInput P (.message bottomLayer e) (bytesLE 32 message ++ bytesLE 16 randomness)))).run s),
      Inv w.2) :
    ∀ attempts trial s, Inv s → ∀ z ∈ support ((simulateQ (monitoredOracle keyOf)
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial))).run s), Inv z.2 := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s hs z hz
    simp only [grind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | succ n ih =>
    intro trial s hs z hz
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hz
    obtain ⟨a, a1, b, hw, hz⟩ := hz
    have hmid := hstep _ s hs _ hw
    cases hdec : Codeword.decode (truncateHash a) with
    | some encoding =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hmid
    | none =>
      simp only [hdec] at hz
      exact ih (trial + 1) (a1, b) hmid z hz

/-- An invariant of each trial of a grind at `e` on `message` holds after `baseGrind`. -/
theorem baseGrind_inv (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (e : KeyIndex) (message : Message) (answer : HashOutput) (Inv : HashCache C × Monitor → Prop)
    (hstep : ∀ randomness s, Inv s → ∀ w ∈ support ((monitoredOracle keyOf
      (.hash (tweakableHashInput P (.message bottomLayer e) (bytesLE 32 message ++ bytesLE 16 randomness)))).run s),
      Inv w.2)
    (s : HashCache C × Monitor) (hs : Inv s)
    (z : Unit × (HashCache C × Monitor)) (hz : z ∈ support ((simulateQ (monitoredOracle keyOf)
      (baseGrind P e message answer)).run s)) : Inv z.2 := by
  simp only [baseGrind, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact grind_inv keyOf P e message _ Inv hstep _ _ s hs y hy

/-- A call of the lazy `H` with the trial monitor grows the cache. -/
theorem monitoredOracle_cache_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (q : Query C)
    (s : HashCache C × Monitor) (w : HashOutput × (HashCache C × Monitor))
    (hw : w ∈ support ((monitoredOracle keyOf q).run s)) : s.1 ≤ w.2.1 := by
  simp only [monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  exact (randomOracle_support q s.1 v hv).1

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

/-- A grind grows the cache. -/
theorem baseGrind_cache_le (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (e : KeyIndex) (message : Message) (answer : HashOutput)
    (s : HashCache C × Monitor) (z : Unit × (HashCache C × Monitor))
    (hz : z ∈ support ((simulateQ (monitoredOracle keyOf) (baseGrind P e message answer)).run s)) :
    s.1 ≤ z.2.1 :=
  baseGrind_inv keyOf P e message answer (fun w => s.1 ≤ w.1)
    (fun _ w hw v hv => hw.trans (monitoredOracle_cache_le keyOf _ w v hv)) s le_rfl z hz

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- One world call with no grind or with the grind of `grindExtra P ρ`. It keeps the carried state,
grows the cache and keeps `SignedWitness`. A key that it signs is the key of its base call, and the
grind ran under the condition `G`. -/
theorem signedWitness_step_core (P : PublicParameter) (ρ : KeyIndex → Digest)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C → OracleComp (Query C →ₒ HashOutput) Unit)
    (t : (WorldSpec C).Domain) (p : (LoggedState C × Monitor) × (TsigState C × Bool))
    (hwit : SignedWitness P ρ p) (G : Prop)
    (hextra : ∀ p', extra (p.1.1, p.2) t p' = pure () ∨ (G ∧ extra (p.1.1, p.2) t p' = grindExtra P ρ (p.1.1, p.2) t p'))
    (r : (WorldSpec C).Range t × (LoggedState C × Monitor) × (TsigState C × Bool))
    (hr : r ∈ support ((monitoredWorld prims (XmssSecurity.encodingInputLeafIndex? P) extra t).run p)) :
    r.2.2 = p.2 ∧ p.1.1.1.1 ≤ r.2.1.1.1.1 ∧ SignedWitness P ρ r.2 ∧
      ∀ f, r.2.1.2.state.signed f ≠ none → p.1.2.state.signed f ≠ none ∨ (G ∧ BaseCall P f (ρ f) p.2.1 t) := by
  simp only [monitoredWorld, carry, StateT.run_mk, support_bind, support_map, Set.mem_iUnion,
    Set.mem_image] at hr
  obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hr
  have hgrow : p.1.1.1.1 ≤ w.2.1.1 := by
    have hw2 := hw
    simp only [SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hw2
    obtain ⟨v, hv, hvw⟩ := hw2
    rw [← hvw]
    exact SigningCacheProof.countImpl_grows prims t p.1.1.1 v hv
  have hcase0 : y.2 = (w.2.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? P) p.1.2 (hashEntry ⟨t, w.1⟩)) ∨
      ∃ g message answer, G ∧ BaseCall P g (ρ g) p.2.1 t ∧ p.2.1.bound g = some message ∧
      w.2.1.1 (.hash (randomizerInput P bottomLayer g (ρ g) (bytesLE 32 message))) = some answer ∧
      y ∈ support ((simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? P))
        (baseGrind P g message answer)).run
          (w.2.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? P) p.1.2 (hashEntry ⟨t, w.1⟩))) := by
    rcases hextra (w.1, w.2, p.2).2 with he | he
    · rw [he] at hy
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      exact Or.inl (by rw [hy])
    · obtain ⟨hG, he⟩ := he
      rw [he] at hy
      unfold grindExtra at hy
      split_ifs at hy with h
      · cases hb : p.2.1.bound h.choose with
        | none =>
          simp only [hb, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
          exact Or.inl (by rw [hy])
        | some message =>
          cases ha : w.2.1.1 (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) with
          | none =>
            simp only [hb, ha, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
            exact Or.inl (by rw [hy])
          | some answer =>
            simp only [hb, ha] at hy
            exact Or.inr ⟨h.choose, message, answer, hG, h.choose_spec, hb, ha, hy⟩
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        exact Or.inl (by rw [hy])
  simp only [ofRest, restOf] at hy ⊢
  set Q := queryEntryStep (XmssSecurity.encodingInputLeafIndex? P) p.1.2 (hashEntry ⟨t, w.1⟩) with hQ
  have hcase := hcase0
  have hyc : w.2.1.1 ≤ y.2.1 := by
    rcases hcase with h | ⟨g, m, a, -, -, -, -, hg⟩
    · rw [h]
    · exact baseGrind_cache_le _ P g m a _ y hg
  have hsig : ∀ f, y.2.2.state.signed f ≠ none → p.1.2.state.signed f ≠ none ∨
      ∃ message answer, G ∧ BaseCall P f (ρ f) p.2.1 t ∧ p.2.1.bound f = some message ∧
        w.2.1.1 (.hash (randomizerInput P bottomLayer f (ρ f) (bytesLE 32 message))) = some answer ∧
        y ∈ support ((simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? P))
          (baseGrind P f message answer)).run (w.2.1.1, Q)) := by
    intro f hf
    rcases hcase with h | ⟨g, m, a, hG, hb, hbound, ha, hg⟩
    · left
      rw [h] at hf
      change (Q.state.signed f ≠ none) at hf
      rwa [hQ, queryEntryStep_signed] at hf
    · by_cases hfg : f = g
      · subst hfg
        exact Or.inr ⟨m, a, hG, hb, hbound, ha, hg⟩
      · left
        rw [baseGrind_signed_ne P g m a _ y hg f hfg] at hf
        change (Q.state.signed f ≠ none) at hf
        rwa [hQ, queryEntryStep_signed] at hf
  refine ⟨by first | rfl | trivial, hgrow.trans hyc, ?_, fun f hf => ?_⟩
  · intro f hf
    rcases hsig f hf with hold | ⟨m, a, -, -, hbound, ha, hg⟩
    · obtain ⟨m, a, hbound, ha, initial, first, hmem, hle⟩ := hwit f hold
      exact ⟨m, a, hbound, (hgrow.trans hyc) ha, initial, first, hmem, hle.trans (hgrow.trans hyc)⟩
    · refine ⟨m, a, hbound, hyc ha, w.2.1.1, y.2.1, ?_, le_rfl⟩
      rw [← monitoredOracle_run_forget (XmssSecurity.encodingInputLeafIndex? P) _ w.2.1.1 Q, support_map]
      exact ⟨y, hg, rfl⟩
  · rcases hsig f hf with hold | ⟨m, a, hG, hb, -⟩
    · exact Or.inl hold
    · exact Or.inr ⟨hG, hb⟩

/-- `SignedWitnessStep` of `SigningCacheLog`. Each world call of the monitored eager run keeps
`SignedWitness`. -/
theorem signedWitnessStep (P : PublicParameter) (ρ : KeyIndex → Digest) : SignedWitnessStep prims (C := C) P ρ := by
  intro t _ p _ hwit r hr
  exact (signedWitness_step_core prims P ρ (grindExtra P ρ) t p hwit True (fun _ => Or.inr ⟨trivial, rfl⟩) r hr).2.2.1

/-- The `hsigned` hypothesis of `monitoredWorld_signed_grind`. A call that is a base call of a signed
key is a base call of no other key. -/
theorem hsigned_of_signed {P : PublicParameter} {ρ : KeyIndex → Digest} {t : (WorldSpec C).Domain}
    {p : (LoggedState C × Monitor) × (TsigState C × Bool)} {e : KeyIndex} (he : BaseCall P e (ρ e) p.2.1 t)
    (hs : p.1.2.state.signed e ≠ none) : ∀ f, BaseCall P f (ρ f) p.2.1 t → p.1.2.state.signed f ≠ none := by
  intro f hf
  rw [← baseCall_key_eq he hf]
  exact hs

/-- `SignedWitness` on the randomizer of the cache, with all PRF entries of each signed key cached. -/
def CachedWitness (seeds : C.Term → HashOutput) (P : PublicParameter)
    (p : (LoggedState C × Monitor) × (TsigState C × Bool)) : Prop :=
  (∀ e, p.1.2.state.signed e ≠ none → SigningGuessProof.RandomizerCached seeds p.1.1.1.1 e) ∧
    SignedWitness P (SigningGuessProof.cachedRandomizer seeds p.1.1.1.1) p

/-- `RandomizerCached` holds on a larger cache. -/
theorem randomizerCached_mono {seeds : C.Term → HashOutput} {left right : HashCache C} {e : KeyIndex}
    (hle : left ≤ right) (h : SigningGuessProof.RandomizerCached seeds left e) :
    SigningGuessProof.RandomizerCached seeds right e := fun T => by
  obtain ⟨v, hv⟩ := h T
  exact ⟨v, hle hv⟩

set_option maxRecDepth 100000 in
/-- Each world call of the monitored run of `cachedExtra` keeps `CachedWitness`. -/
theorem cachedWitness_step (seeds : C.Term → HashOutput) (P : PublicParameter) (t : (WorldSpec C).Domain)
    (p : (LoggedState C × Monitor) × (TsigState C × Bool)) (hwit : CachedWitness seeds P p)
    (r : (WorldSpec C).Range t × (LoggedState C × Monitor) × (TsigState C × Bool))
    (hr : r ∈ support ((monitoredWorld prims (XmssSecurity.encodingInputLeafIndex? P) (cachedExtra seeds P) t).run p)) :
    CachedWitness seeds P r.2 := by
  classical
  set ρ := SigningGuessProof.cachedRandomizer seeds p.1.1.1.1 with hρ
  set G := ∃ e, SigningGuessProof.RandomizerCached seeds p.1.1.1.1 e ∧ BaseCall P e (ρ e) p.2.1 t with hG
  have hextra : ∀ p', cachedExtra seeds P (p.1.1, p.2) t p' = pure () ∨
      (G ∧ cachedExtra seeds P (p.1.1, p.2) t p' = grindExtra P ρ (p.1.1, p.2) t p') := by
    intro p'
    unfold cachedExtra
    split_ifs with h
    · exact Or.inr ⟨h, rfl⟩
    · exact Or.inl rfl
  obtain ⟨-, hle, hw, hnew⟩ := signedWitness_step_core prims P ρ (cachedExtra seeds P) t p hwit.2 G hextra r hr
  have hcached : ∀ f, r.2.1.2.state.signed f ≠ none → SigningGuessProof.RandomizerCached seeds p.1.1.1.1 f := by
    intro f hf
    rcases hnew f hf with hold | ⟨⟨e, he, hbe⟩, hbf⟩
    · exact hwit.1 f hold
    · rw [← baseCall_key_eq hbe hbf]
      exact he
  refine ⟨fun f hf => randomizerCached_mono hle (hcached f hf), fun f hf => ?_⟩
  have hstable := SigningGuessProof.cachedRandomizer_stable seeds _ _ f hle (hcached f hf)
  rw [← hstable]
  exact hw f hf

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- `monitoredWorld_signed_grind` for the trigger of `cachedExtra`. At a base call of signed keys the
grind leaves the monitor at the query step of the call. -/
theorem monitoredWorld_cached_signed_grind (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (seeds : C.Term → HashOutput) (P : PublicParameter) (t : (WorldSpec C).Domain) (ht : ¬IsProgram t)
    (p : (LoggedState C × Monitor) × (TsigState C × Bool)) (hcov : CacheSeen p.1.1.1.1 p.1.2)
    (hwit : CachedWitness seeds P p)
    (hsigned : ∀ e, BaseCall P e (SigningGuessProof.cachedRandomizer seeds p.1.1.1.1 e) p.2.1 t →
      p.1.2.state.signed e ≠ none)
    (r : (WorldSpec C).Range t × (LoggedState C × Monitor) × (TsigState C × Bool))
    (hr : r ∈ support ((monitoredWorld prims keyOf (cachedExtra seeds P) t).run p)) :
    r.2.1.2 = queryEntryStep keyOf p.1.2 (hashEntry ⟨t, r.1⟩) := by
  classical
  by_cases h : ∃ e, SigningGuessProof.RandomizerCached seeds p.1.1.1.1 e ∧
      BaseCall P e (SigningGuessProof.cachedRandomizer seeds p.1.1.1.1 e) p.2.1 t
  · have heq : (monitoredWorld prims keyOf (cachedExtra seeds P) t).run p =
        (monitoredWorld prims keyOf (grindExtra P (SigningGuessProof.cachedRandomizer seeds p.1.1.1.1)) t).run p := by
      simp only [monitoredWorld, StateT.run_mk]
      refine bind_congr fun z => ?_
      have hc : cachedExtra seeds P (p.1.1, p.2) t z.2 =
          grindExtra P (SigningGuessProof.cachedRandomizer seeds p.1.1.1.1) (p.1.1, p.2) t z.2 := by
        unfold cachedExtra
        exact if_pos h
      rw [hc]
    rw [heq] at hr
    exact monitoredWorld_signed_grind prims keyOf P _ t ht p hcov hwit.2 hsigned r hr
  · simp only [monitoredWorld, carry, StateT.run_mk, support_bind, support_map, Set.mem_iUnion,
      Set.mem_image] at hr
    obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hr
    have hc : cachedExtra seeds P (p.1.1, p.2) t (w.2, p.2) = pure () := by
      unfold cachedExtra
      exact if_neg h
    change y ∈ support ((simulateQ (monitoredOracle keyOf) (cachedExtra seeds P (p.1.1, p.2) t (w.2, p.2))).run _) at hy
    rw [hc] at hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    change y.2.2 = _
    rw [hy]

end Witness

end SigningR1FixedProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.evalDist_flatEagerRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.evalDist_flatEagerRun

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.r1Hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.r1Hit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.split_r1Hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.split_r1Hit_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.signedWitnessStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.signedWitnessStep

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.hsigned_of_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.hsigned_of_signed

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.cachedWitness_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.cachedWitness_step

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.monitoredWorld_cached_signed_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.monitoredWorld_cached_signed_grind

/-- info: 'ThresholdLeanXmssSecurity.SigningR1FixedProof.partnerCrossing_of_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningR1FixedProof.partnerCrossing_of_link
