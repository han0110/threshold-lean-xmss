import ThresholdLeanXmssSecurity.Proof.SigningLane2
import XmssSecurity.Proof.Bridge.Honest
import XmssSecurity.Proof.Deterministic.TrialSampling

/-!
# The threshold signing calls as leanVM steps

This module gives the threshold calls in the terms of leanVM, for one call, with no reference to the
flat run. `SigningCompilerPotential` uses these laws for the lane 2 potential of `SigningLane2`.

* The input map is the identity on bytes. The bottom message digest input is `Partner.input`
  (`messageInput_eq_partnerInput`), with its key as the leaf index
  (`encodingInputLeafIndex?_messageInput`).
* The view `keptView K` keeps the entries of `Th` at the inputs of `K`. A world call on a kept input
  outside the MPC has the state law of the world step of leanVM (`worldCall_stateLaw`).
* The bottom grind is `precomputedSignBoundedAttempts` from the same base (`liftM_grind_eq`).
* The base is the truncation of a fresh answer of `H`. If the randomizer input is fresh and not
  kept, the base call has the law of `signWithBaseStep` (`baseCall_signWithBaseStep`).

## Potential hypotheses

`evalDist_baseCall` and `baseCall_signWithBaseStep` take `topSignedAt secretKey e = true`. The
leanVM key of the flat run must set `topSigned b` to the result of the top grind of the ceremony of
bottom tree `b`. A signing at key `e` must follow a ceremony of tree `topKeyOf e` that did not
abort.

`topSignedAt secretKey e` reads `secretKey.topSigned (topKeyOf e)`. In the threshold run the top
key `b` signs the root of bottom tree `b` in the ceremony of that tree, with the top grind. The top
grind is `topSignFrom` of leanVM, which fills `topSigned` in its key generation.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option backward.isDefEq.respectTransparency false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningLane2BridgeProof

/-! ## The input map -/

/-- The bottom message digest input of the threshold signing is the input `Partner.input` of
leanVM. Both are the same bytes, so the map is the identity. -/
theorem messageInput_eq_partnerInput (parameter : PublicParameter) (key : XmssSecurity.LeafIndex)
    (message : Message) (randomness : Randomizer) :
    tweakableHashInput parameter (.message bottomLayer key) (littleEndianBytes 32 message ++ littleEndianBytes 16 randomness) =
      XmssSecurity.Partner.input parameter key (message, randomness) :=
  XmssSecurity.Bridge.message_input parameter key message randomness

/-- The leaf index that leanVM reads from a threshold message digest input is its key. -/
theorem encodingInputLeafIndex?_messageInput (parameter : PublicParameter) (key : XmssSecurity.LeafIndex)
    (message : Message) (randomness : Randomizer) :
    XmssSecurity.encodingInputLeafIndex? parameter
        (tweakableHashInput parameter (.message bottomLayer key) (littleEndianBytes 32 message ++ littleEndianBytes 16 randomness)) =
      some key := by
  rw [messageInput_eq_partnerInput]
  exact XmssSecurity.encodingInputLeafIndex?_encodingInput parameter key (message, randomness)

/-- A message digest input is not an input of the MPC, so the world answers it with `H`. -/
theorem messageInput_not_mpc (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (payload : HashInput) : ¬MpcInput (tweakableHashInput parameter (.message lay key) payload) :=
  fun h => not_isMsg_of_mpc h (byte23_msg parameter lay key payload)

/-! ## The world call

The view keeps the entries of `Th` at the inputs that `K` selects. The base input of a signing is
not one of them, since leanVM keeps the base private. -/

section World

variable {C : Committee} (prims : Primitives) (K : HashInput → Prop)

open Classical in
/-- The cache of leanVM in a cache of the world. It keeps the entries of `Th` at the inputs of `K`. -/
def keptView (c : HashCache C) : XmssSecurity.HashSpec.QueryCache :=
  QueryCache.ofFn fun x => if K x then c (.hash x) else none

variable {K}

theorem keptView_cacheQuery_of_kept {x : HashInput} (hK : K x) (c : HashCache C) (u : HashOutput) :
    keptView K (c.cacheQuery (.hash x) u) = (keptView K c).cacheQuery x u := by
  refine QueryCache.ext fun y => ?_
  by_cases hy : y = x
  · subst y
    simp [keptView, hK]
  · rw [QueryCache.cacheQuery_of_ne _ _ hy]
    simp only [keptView, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hy (Query.hash.inj h))]

theorem keptView_cacheQuery_of_not {q : Query C} (hq : ∀ x, q = .hash x → ¬K x) (c : HashCache C)
    (u : HashOutput) : keptView K (c.cacheQuery q u) = keptView K c := by
  refine QueryCache.ext fun y => ?_
  simp only [keptView, QueryCache.ofFn_apply]
  split_ifs with hy
  · rw [QueryCache.cacheQuery_of_ne]
    rintro rfl
    exact hq y rfl hy
  · rfl

/-- A world call on a kept input that the MPC does not compute is the random oracle of leanVM on
the view. -/
theorem hashAnswer_keptView {x : HashInput} (hK : K x) (hx : ¬MpcInput x) (c : HashCache C) :
    (fun p => (p.1, keptView K p.2)) <$> (hashAnswer prims (.hash x)).run c =
      (XmssSecurity.romImpl (.inr x)).run (keptView K c) := by
  dsimp only [hashAnswer]
  rw [ite_eq_right hx]
  change _ = (OracleSpec.randomOracle (spec := XmssSecurity.HashSpec) x).run (keptView K c)
  have hc : keptView K c x = c (.hash x) := by simp [keptView, hK]
  cases h : c (.hash x) with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ h, OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ (hc.trans h)]
    simp only [Functor.map_map, keptView_cacheQuery_of_kept hK]
    rfl
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ h, OracleSpec.randomOracle,
      QueryImpl.withCaching_run_some _ (hc.trans h)]
    simp

/-- The state law of a world call on a kept input, with the count that the leanVM tick adds. -/
theorem worldCall_stateLaw (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
    {x : HashInput} (hK : K x) (hx : ¬MpcInput x) (c : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    ((fun p => (((keptView K p.2, trace), k + 1) : XmssSecurity.Ghost.State)) <$>
        (hashAnswer prims (.hash x)).run c) =ᵈ
      ((fun y => y.2) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inl (.inr x))).run ((keptView K c, trace), k)) := by
  refine EvalDistEq.of_eq ?_
  rw [XmssSecurity.Ghost.impl_run, XmssSecurity.Ghost.simulateQ_source_world, ← hashAnswer_keptView prims hK hx c]
  simp only [Functor.map_map, XmssSecurity.signingCacheTraceUpdate, XmssSecurity.Ghost.tick,
    XmssSecurity.Ghost.IsAdvHash, ite_true]

/-- A computation of leanVM that queries only kept inputs outside the MPC runs in the world as the
random oracle of leanVM on the view. -/
theorem roRun_tweakable_keptView {α : Type} {oa : OracleComp HashSpec α}
    (hoa : XmssSecurity.Bridge.OnlyQueries (fun x => K x ∧ ¬MpcInput x) oa) (c : HashCache C) :
    (fun p => (p.1, keptView K p.2)) <$> roRun prims (tweakable oa) c =
      (simulateQ (randomOracle : QueryImpl XmssSecurity.HashSpec
        (StateT XmssSecurity.HashSpec.QueryCache ProbComp)) oa).run (keptView K c) := by
  induction hoa generalizing c with
  | pure a => simp [tweakable_pure, roRun_pure]
  | query x hx next _ ih =>
    rw [tweakable_bind]
    change (fun p => (p.1, keptView K p.2)) <$> roRun prims (tweakable (Verification.oracleHashWithHash x) >>= _) c = _
    rw [tweakable_oracleHash, roRun_bind, roRun_hashQuery, map_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    calc _ = ((fun p => (p.1, keptView K p.2)) <$> (hashAnswer prims (.hash x)).run c) >>=
          fun p => (simulateQ randomOracle (next p.1)).run p.2 := by
          rw [bind_map_left]
          exact bind_congr fun p => ih p.1 p.2
      _ = _ := by
          rw [hashAnswer_keptView prims hx.1 hx.2 c]
          rfl

/-- `worldCall_stateLaw` with the view of the message digest inputs. -/
theorem worldCall_stateLaw_isMsg (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
    {x : HashInput} (hK : IsMsg x) (c : HashCache C) (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    ((fun p => (((keptView IsMsg p.2, trace), k + 1) : XmssSecurity.Ghost.State)) <$>
        (hashAnswer prims (.hash x)).run c) =ᵈ
      ((fun y => y.2) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inl (.inr x))).run ((keptView IsMsg c, trace), k)) :=
  worldCall_stateLaw prims publicKey secretKey hK (fun h => not_isMsg_of_mpc h hK) c trace k

end World

/-! ## The grind

`Scheme.grind` at the bottom layer makes the trials of `precomputedSignBoundedAttempts` of leanVM,
on the same inputs and from the same base. -/

section Grind

variable (secretKey : XmssSecurity.SecretKey) (key : XmssSecurity.LeafIndex) (message : Message)
  (base : Randomizer)

/-- The signature of leanVM from the codeword that the grind finds. -/
def signOf (found : Option (Randomizer × Encoding)) : Option XmssSecurity.Signature :=
  found.map fun p => XmssSecurity.Concrete.precomputedSignWithEncoding secretKey key p.1 p.2

/-- The bottom grind is the table signer of leanVM from the same base. -/
theorem grind_eq_tableSignFrom (attempts trial : ℕ) :
    signOf secretKey key <$>
        (grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) base attempts trial :
          OracleComp HashSpec _) =
      (XmssSecurity.Seeded.tableSignFrom base secretKey key message attempts trial :
        OracleComp XmssSecurity.HashSpec _) := by
  induction attempts generalizing trial with
  | zero => simp [grind, XmssSecurity.Seeded.tableSignFrom, signOf]
  | succ attempts ih =>
    rw [grind, XmssSecurity.Seeded.tableSignFrom]
    simp only [XmssSecurity.Concrete.precomputedSignAttempt, map_bind, bind_assoc]
    rw [XmssSecurity.Bridge.messageDigest_bottom]
    refine bind_congr fun digest => ?_
    rw [XmssSecurity.Bridge.decode_eq]
    cases XmssSecurity.TargetSum.decodeDigest digest with
    | none => simpa using ih (trial + 1)
    | some encoding => simp [signOf]; rfl

/-- Lifted to the world of leanVM, the bottom grind is `precomputedSignBoundedAttempts`. -/
theorem liftM_grind_eq (attempts trial : ℕ) :
    (liftM (show OracleComp XmssSecurity.HashSpec _ from signOf secretKey key <$>
        grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) base attempts trial) :
          OracleComp XmssSecurity.OracleWorld _) =
      XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey key message base attempts trial := by
  rw [grind_eq_tableSignFrom]
  exact XmssSecurity.Seeded.liftM_tableSignFrom base secretKey key message attempts trial

/-- The grind queries only its trial inputs. -/
theorem grind_onlyQueries (S : HashInput → Prop) (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (base : Randomizer) (hS : ∀ t, S (trialInput parameter lay key message base t)) :
    ∀ attempts trial, XmssSecurity.Bridge.OnlyQueries S
      (grind parameter lay key message base attempts trial : OracleComp HashSpec _)
  | 0, _ => .pure _
  | attempts + 1, trial => by
    rw [grind]
    unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash Verification.thWithHash
    simp only [bind_assoc, pure_bind]
    refine (XmssSecurity.Bridge.onlyQueries_query (hS trial)).bind fun output => ?_
    split
    · exact .pure _
    · exact grind_onlyQueries S parameter lay key message base hS attempts (trial + 1)

/-- The base input of a randomizer search is not an input of the MPC. -/
theorem randomizerInput_not_mpc (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) : ¬MpcInput (randomizerInput parameter lay e ρ message) := by
  rintro (⟨P, lay', key, step, l, v, h⟩ | ⟨P, e', ρ', h⟩)
  · have h1 := byte23_randomizer parameter lay e ρ message
    rw [h, tweakableHashInput, tweakBytes, byte23] at h1
    simp only [hashDomainFields, tweakFields] at h1
    clear h
    revert h1
    revert step
    decide
  · have h1 := byte23_randomizer parameter lay e ρ message
    rw [h, byte23_commitment] at h1
    exact absurd h1 (by decide)

end Grind

/-! ## The base call

In the threshold signing the base `R_0` is the truncation of the answer of `H` at the randomizer
input, and the grind follows. leanVM samples the base uniformly (`signWithBase`). The view hides
the randomizer input, so both have the same law when that input is fresh. -/

section Base

variable {C : Committee} (prims : Primitives) {K : HashInput → Prop}
  (secretKey : XmssSecurity.SecretKey) (key : XmssSecurity.LeafIndex) (ρ : Digest) (message : Message)

/-- The base call at bottom key `key` from the opened value `ρ`, as in `signCodeword`. It also
returns the base, which round 1 releases. -/
def baseCall : OracleComp HashSpec (Randomizer × Option (Randomizer × Encoding)) := do
  let base := truncateHash (← Verification.oracleHashWithHash
    (randomizerInput secretKey.parameter bottomLayer key ρ (littleEndianBytes 32 message)))
  let found ← grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) base randomizerAttemptLimit 0
  pure (base, found)

/-- The grind from base `b` with the base in front, in the world of leanVM on a cache. -/
def grindRun (c : XmssSecurity.HashSpec.QueryCache) (b : Randomizer) :
    ProbComp ((Randomizer × Option XmssSecurity.Signature) × XmssSecurity.HashSpec.QueryCache) :=
  (simulateQ XmssSecurity.romImpl (do
    let result ← XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey key message b
      XmssSecurity.signingAttemptLimit 0
    pure (b, result))).run c

theorem roRun_baseCall_rest (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer key (littleEndianBytes 32 message) b t))
    (c : HashCache C) (b : Randomizer) :
    (fun p => ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) <$>
        roRun prims (tweakable (grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) b
          randomizerAttemptLimit 0 >>= fun found => pure (b, found))) c =
      grindRun secretKey key message (keptView K c) b := by
  have hq : XmssSecurity.Bridge.OnlyQueries (fun x => K x ∧ ¬MpcInput x)
      (grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) b randomizerAttemptLimit 0 >>=
        fun found => pure (b, found) : OracleComp HashSpec _) :=
    (grind_onlyQueries _ _ _ _ _ _ (fun t => ⟨hK b t, messageInput_not_mpc _ _ _ _⟩) _ _).bind
      fun _ => .pure _
  have h := roRun_tweakable_keptView prims hq c
  have hmap : (fun p : (Randomizer × Option (Randomizer × Encoding)) × HashCache C =>
      ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) =
      (fun q : (Randomizer × Option (Randomizer × Encoding)) × XmssSecurity.HashSpec.QueryCache =>
        ((q.1.1, signOf secretKey key q.1.2), q.2)) ∘ (fun p => (p.1, keptView K p.2)) := rfl
  rw [hmap, comp_map, h, grindRun, ← liftM_grind_eq]
  have hlift : (do
      let result ← (liftM (show OracleComp XmssSecurity.HashSpec _ from signOf secretKey key <$>
        grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) b XmssSecurity.signingAttemptLimit 0) :
          OracleComp XmssSecurity.OracleWorld _)
      pure (b, result) : OracleComp XmssSecurity.OracleWorld _) =
      liftM (show OracleComp XmssSecurity.HashSpec _ from (fun q => (q.1, signOf secretKey key q.2)) <$>
        (grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) b randomizerAttemptLimit 0 >>=
          fun found => pure (b, found))) := by
    simp [map_eq_bind_pure_comp, liftM_bind]
    rfl
  rw [hlift]
  unfold XmssSecurity.romImpl
  rw [QueryImpl.simulateQ_add_liftM_right, simulateQ_map, StateT.run_map]

/-- The base call on a fresh randomizer input has the law of `signWithBase` of leanVM on the view,
at a key whose top tree is signed. -/
theorem evalDist_baseCall
    (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer key (littleEndianBytes 32 message) b t))
    (hR : ¬K (randomizerInput secretKey.parameter bottomLayer key ρ (littleEndianBytes 32 message)))
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer key ρ
      (littleEndianBytes 32 message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey key = true) :
    ((fun p => ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) <$>
        roRun prims (tweakable (baseCall secretKey key ρ message)) c) =ᵈ
      ((simulateQ XmssSecurity.romImpl (SigningLane2Proof.signWithBase secretKey key message)).run
        (keptView K c)) := by
  rw [baseCall, tweakable_bind, tweakable_oracleHash, roRun_bind,
    roRun_fresh prims _ (randomizerInput_not_mpc _ _ _ _ _) c hfresh, map_bind, bind_map_left]
  have hstep : ∀ u : HashOutput, (fun p => ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) <$>
      roRun prims (tweakable (grind secretKey.parameter bottomLayer key (littleEndianBytes 32 message) (truncateHash u)
        randomizerAttemptLimit 0 >>= fun found => pure (truncateHash u, found)))
        (c.cacheQuery (.hash (randomizerInput secretKey.parameter bottomLayer key ρ (littleEndianBytes 32 message))) u) =
      grindRun secretKey key message (keptView K c) (truncateHash u) := by
    intro u
    rw [roRun_baseCall_rest prims secretKey key message hK, keptView_cacheQuery_of_not]
    intro x hx
    rw [← Query.hash.inj hx]
    exact hR
  simp only [hstep]
  have hsample : (simulateQ XmssSecurity.romImpl (liftM XmssSecurity.Concrete.signingRandomness)).run
      (keptView K c) = (fun base => (base, keptView K c)) <$> XmssSecurity.Concrete.signingRandomness := by
    unfold XmssSecurity.romImpl
    exact roSim.run_liftM (hashSpec := XmssSecurity.HashSpec)
      (randomOracle : QueryImpl XmssSecurity.HashSpec (StateT XmssSecurity.HashSpec.QueryCache ProbComp))
      XmssSecurity.Concrete.signingRandomness _
  rw [SigningLane2Proof.signWithBase, simulateQ_bind, StateT.run_bind, hsample, bind_map_left]
  simp only [htop, ite_true]
  change _ =ᵈ (XmssSecurity.Concrete.signingRandomness >>= grindRun secretKey key message (keptView K c))
  have ht : (truncateHash <$> ($ᵗ HashOutput) : ProbComp Randomizer) =ᵈ
      XmssSecurity.Concrete.signingRandomness := by
    rw [XmssSecurity.Concrete.signingRandomness_eq]
    refine XmssSecurity.Rom.evalDist_truncate_uniformHashOutput.trans ?_
    exact fun p => SampleableType.prEvent_uniformSample_inst_irrel _ _ p
  rw [← bind_map_left (f := truncateHash)]
  exact ht.bind_left _

/-- The base call with the trace entry of leanVM has the law of `signWithBaseStep`. -/
theorem baseCall_signWithBaseStep (request : XmssSecurity.SignRequest)
    (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer request.leafIndex
      (littleEndianBytes 32 request.message) b t))
    (hR : ¬K (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ (littleEndianBytes 32 request.message)))
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ
      (littleEndianBytes 32 request.message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey request.leafIndex = true)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    ((fun p => ((p.1.1, signOf secretKey request.leafIndex p.1.2),
        ((keptView K p.2, trace ++ [⟨request, signOf secretKey request.leafIndex p.1.2, keptView K c,
          keptView K p.2⟩]), k))) <$>
        roRun prims (tweakable (baseCall secretKey request.leafIndex ρ request.message)) c) =ᵈ
      (SigningLane2Proof.signWithBaseStep secretKey request).run ((keptView K c, trace), k) := by
  have h := evalDist_baseCall prims secretKey request.leafIndex ρ request.message hK hR c hfresh htop
  have h' := h.map (fun r : (XmssSecurity.Randomness × Option XmssSecurity.Signature) ×
      XmssSecurity.HashSpec.QueryCache => (r.1, ((r.2, trace ++ [⟨request, r.1.2, keptView K c, r.2⟩]), k)))
  simp only [Functor.map_map] at h'
  rw [SigningLane2Proof.signWithBaseStep, StateT.run_mk]
  exact h'

/-! With `K = IsMsg` the hypotheses on `K` hold. -/

theorem isMsg_trialInput (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (b : Randomizer) (t : ℕ) : IsMsg (trialInput parameter lay key message b t) :=
  byte23_msg _ _ _ _

theorem not_isMsg_randomizerInput (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) : ¬IsMsg (randomizerInput parameter lay e ρ message) := by
  unfold IsMsg
  rw [byte23_randomizer]
  decide

end Base

end SigningLane2BridgeProof

open SigningLane2BridgeProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.liftM_grind_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftM_grind_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.worldCall_stateLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worldCall_stateLaw

end ThresholdLeanXmssSecurity
