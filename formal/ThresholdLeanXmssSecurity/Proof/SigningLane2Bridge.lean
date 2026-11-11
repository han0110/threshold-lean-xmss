import ThresholdLeanXmssSecurity.Proof.SigningLane2
import XmssSecurity.Proof.Bridge.Honest
import XmssSecurity.Proof.Deterministic.TrialSampling

/-!
# The threshold signing calls as leanVM steps

`SigningLane2` needs the threshold calls in the terms of leanVM ("The remaining goals"). This module
gives them for one call, with no reference to the flat run.

* The input map is the identity on bytes. The bottom message digest input is `Partner.input`
  (`messageInput_eq_partnerInput`), injective in the key and the position (`partnerInput_eq_iff`),
  with its key as the leaf index (`encodingInputLeafIndex?_messageInput`).
* The view `keptView K` keeps the entries of `Th` at the inputs of `K`. A world call on a kept input
  outside the MPC has the law of the world step of leanVM (`worldCall_viewLaw`).
* The bottom grind is `precomputedSignBoundedAttempts` from the same base (`liftM_grind_eq`).
* The base is the truncation of a fresh answer of `H`. If the randomizer input is fresh and not
  kept, the base call has the law of `signWithBaseStep` (`baseCall_signWithBaseStep`) and of the
  sign step of leanVM (`baseCall_stateLaw`).
* The top grind is `topSignFrom` of leanVM (`grind_top_eq_topSignFrom`).

## Open

`baseCall_stateLaw` takes `topSignedAt secretKey e = true`. The leanVM key of the flat run must set
`topSigned b` to the result of the top grind of the ceremony of bottom tree `b`, and a signing at
key `e` must follow a ceremony of tree `topKeyOf e` that did not abort.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option backward.isDefEq.respectTransparency false

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningLane2BridgeProof

/-! ## The input map -/

/-- The bottom message digest input of the threshold signing is the input `Partner.input` of
leanVM. Both are the same bytes, so the map is the identity. -/
theorem messageInput_eq_partnerInput (parameter : PublicParameter) (key : XmssSecurity.LeafIndex)
    (message : Message) (randomness : Randomness) :
    tweakableHashInput parameter (.message bottomLayer key) (bytesLE 32 message ++ bytesLE 16 randomness) =
      XmssSecurity.Partner.input parameter key (message, randomness) :=
  XmssSecurity.Bridge.message_input parameter key message randomness

/-- The input map is injective on the key and the position together. -/
theorem partnerInput_eq_iff (parameter : PublicParameter) (key key' : XmssSecurity.LeafIndex)
    (y y' : XmssSecurity.Partner.Position) :
    XmssSecurity.Partner.input parameter key y = XmssSecurity.Partner.input parameter key' y' ↔
      key = key' ∧ y = y' :=
  XmssSecurity.Concrete.CacheView.encodingInput_eq_iff parameter key key' y y'

/-- The leaf index that leanVM reads from a threshold message digest input is its key. -/
theorem encodingInputLeafIndex?_messageInput (parameter : PublicParameter) (key : XmssSecurity.LeafIndex)
    (message : Message) (randomness : Randomness) :
    XmssSecurity.encodingInputLeafIndex? parameter
        (tweakableHashInput parameter (.message bottomLayer key) (bytesLE 32 message ++ bytesLE 16 randomness)) =
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
  fun x => if K x then c (.hash x) else none

variable {K}

theorem keptView_cacheQuery_of_kept {x : HashInput} (hK : K x) (c : HashCache C) (u : HashOutput) :
    keptView K (c.cacheQuery (.hash x) u) = (keptView K c).cacheQuery x u := by
  funext y
  by_cases hy : y = x
  · subst y
    simp [keptView, hK]
  · rw [QueryCache.cacheQuery_of_ne _ _ hy]
    simp only [keptView]
    rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hy (Query.hash.inj h))]

theorem keptView_cacheQuery_of_not {q : Query C} (hq : ∀ x, q = .hash x → ¬K x) (c : HashCache C)
    (u : HashOutput) : keptView K (c.cacheQuery q u) = keptView K c := by
  funext y
  simp only [keptView]
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
  rw [if_neg hx]
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

/-- The view law of a world call on a kept input is the law of the world step of leanVM at any
count. This is the hypothesis `hlaw` of `f1_step_of_viewLaw` to `f4_step_of_viewLaw`. -/
theorem worldCall_viewLaw (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
    {x : HashInput} (hK : K x) (hx : ¬MpcInput x) (c : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun p => (keptView K p.2, trace)) <$> (hashAnswer prims (.hash x)).run c] =
      𝒟[(fun y => y.2.1) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inl (.inr x))).run ((keptView K c, trace), k)] := by
  rw [XmssSecurity.Ghost.impl_run, XmssSecurity.Ghost.simulateQ_source_world, ← hashAnswer_keptView prims hK hx c]
  simp only [Functor.map_map, XmssSecurity.signingCacheTraceUpdate]

/-- The state law of a world call on a kept input, with the count that the leanVM tick adds. This
is the hypothesis `hlaw` of `f3_step_of_law`. -/
theorem worldCall_stateLaw (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
    {x : HashInput} (hK : K x) (hx : ¬MpcInput x) (c : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun p => (((keptView K p.2, trace), k + 1) : XmssSecurity.Ghost.State)) <$>
        (hashAnswer prims (.hash x)).run c] =
      𝒟[(fun y => y.2) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inl (.inr x))).run ((keptView K c, trace), k)] := by
  rw [XmssSecurity.Ghost.impl_run, XmssSecurity.Ghost.simulateQ_source_world, ← hashAnswer_keptView prims hK hx c]
  simp only [Functor.map_map, XmssSecurity.signingCacheTraceUpdate, XmssSecurity.Ghost.tick,
    XmssSecurity.Ghost.IsAdvHash, if_true]

/-- `f1_step` of leanVM at a counted world call on a kept input, for a state that is a world cache
with a fixed trace and the count. -/
theorem f1_step_worldCall (publicKey : XmssSecurity.PublicKey) (secretKey : XmssSecurity.SecretKey)
    {x : HashInput} (hK : K x) (hx : ¬MpcInput x) (c : HashCache C)
    (trace : XmssSecurity.SigningCacheTrace) (n : ℕ) :
    ∑' z, Pr[= z | (fun p => (p.1, (p.2, n + 1))) <$> (hashAnswer prims (.hash x)).run c] *
        XmssSecurity.Ghost.f1 secretKey (SigningLane2Proof.ghostView (fun c' => (keptView K c', trace)) z.2) ≤
      XmssSecurity.Ghost.f1 secretKey (SigningLane2Proof.ghostView (fun c' => (keptView K c', trace)) (c, n)) +
        XmssSecurity.Ghost.cost1 secretKey (.inl (.inr x))
          (SigningLane2Proof.ghostView (fun c' => (keptView K c', trace)) (c, n)) :=
  SigningLane2Proof.f1_step_of_viewLaw publicKey secretKey _ (fun c' => (keptView K c', trace)) (c, n)
    (.inl (.inr x)) n (by
      rw [← worldCall_viewLaw prims publicKey secretKey hK hx c trace n]
      simp only [Functor.map_map])

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
    change (fun p => (p.1, keptView K p.2)) <$> roRun prims (tweakable (Concrete.oracleHash x) >>= _) c = _
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
    𝒟[(fun p => (((keptView IsMsg p.2, trace), k + 1) : XmssSecurity.Ghost.State)) <$>
        (hashAnswer prims (.hash x)).run c] =
      𝒟[(fun y => y.2) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inl (.inr x))).run ((keptView IsMsg c, trace), k)] :=
  worldCall_stateLaw prims publicKey secretKey hK (fun h => not_isMsg_of_mpc h hK) c trace k

end World

/-! ## The grind

`Scheme.grind` at the bottom layer makes the trials of `precomputedSignBoundedAttempts` of leanVM,
on the same inputs and from the same base. -/

section Grind

variable (secretKey : XmssSecurity.SecretKey) (key : XmssSecurity.LeafIndex) (message : Message)
  (base : Randomness)

/-- The signature of leanVM from the codeword that the grind finds. -/
def signOf (found : Option (Randomness × Encoding)) : Option XmssSecurity.Signature :=
  found.map fun p => XmssSecurity.Concrete.precomputedSignWithEncoding secretKey key p.1 p.2

/-- The bottom grind is the table signer of leanVM from the same base. -/
theorem grind_eq_tableSignFrom (attempts trial : ℕ) :
    signOf secretKey key <$>
        (grind secretKey.parameter bottomLayer key (bytesLE 32 message) base attempts trial :
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
        grind secretKey.parameter bottomLayer key (bytesLE 32 message) base attempts trial) :
          OracleComp XmssSecurity.OracleWorld _) =
      XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey key message base attempts trial := by
  rw [grind_eq_tableSignFrom]
  exact XmssSecurity.Seeded.liftM_tableSignFrom base secretKey key message attempts trial

theorem randomizerAttemptLimit_eq : randomizerAttemptLimit = XmssSecurity.signingAttemptLimit := rfl

/-- The grind queries only its trial inputs. -/
theorem grind_onlyQueries (S : HashInput → Prop) (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (base : Randomness) (hS : ∀ t, S (trialInput parameter lay key message base t)) :
    ∀ attempts trial, XmssSecurity.Bridge.OnlyQueries S
      (grind parameter lay key message base attempts trial : OracleComp HashSpec _)
  | 0, _ => .pure _
  | attempts + 1, trial => by
    rw [grind]
    unfold Concrete.messageDigest Concrete.tweakableHash
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
def baseCall : OracleComp HashSpec (Randomness × Option (Randomness × Encoding)) := do
  let base := truncateHash (← Concrete.oracleHash
    (randomizerInput secretKey.parameter bottomLayer key ρ (bytesLE 32 message)))
  let found ← grind secretKey.parameter bottomLayer key (bytesLE 32 message) base randomizerAttemptLimit 0
  pure (base, found)

/-- The grind from base `b` with the base in front, in the world of leanVM on a cache. -/
def grindRun (c : XmssSecurity.HashSpec.QueryCache) (b : Randomness) :
    ProbComp ((Randomness × Option XmssSecurity.Signature) × XmssSecurity.HashSpec.QueryCache) :=
  (simulateQ XmssSecurity.romImpl (do
    let result ← XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey key message b
      XmssSecurity.signingAttemptLimit 0
    pure (b, result))).run c

theorem roRun_baseCall_rest (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer key (bytesLE 32 message) b t))
    (c : HashCache C) (b : Randomness) :
    (fun p => ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) <$>
        roRun prims (tweakable (grind secretKey.parameter bottomLayer key (bytesLE 32 message) b
          randomizerAttemptLimit 0 >>= fun found => pure (b, found))) c =
      grindRun secretKey key message (keptView K c) b := by
  have hq : XmssSecurity.Bridge.OnlyQueries (fun x => K x ∧ ¬MpcInput x)
      (grind secretKey.parameter bottomLayer key (bytesLE 32 message) b randomizerAttemptLimit 0 >>=
        fun found => pure (b, found) : OracleComp HashSpec _) :=
    (grind_onlyQueries _ _ _ _ _ _ (fun t => ⟨hK b t, messageInput_not_mpc _ _ _ _⟩) _ _).bind
      fun _ => .pure _
  have h := roRun_tweakable_keptView prims hq c
  have hmap : (fun p : (Randomness × Option (Randomness × Encoding)) × HashCache C =>
      ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) =
      (fun q : (Randomness × Option (Randomness × Encoding)) × XmssSecurity.HashSpec.QueryCache =>
        ((q.1.1, signOf secretKey key q.1.2), q.2)) ∘ (fun p => (p.1, keptView K p.2)) := rfl
  rw [hmap, comp_map, h, grindRun, ← liftM_grind_eq]
  have hlift : (do
      let result ← (liftM (show OracleComp XmssSecurity.HashSpec _ from signOf secretKey key <$>
        grind secretKey.parameter bottomLayer key (bytesLE 32 message) b XmssSecurity.signingAttemptLimit 0) :
          OracleComp XmssSecurity.OracleWorld _)
      pure (b, result) : OracleComp XmssSecurity.OracleWorld _) =
      liftM (show OracleComp XmssSecurity.HashSpec _ from (fun q => (q.1, signOf secretKey key q.2)) <$>
        (grind secretKey.parameter bottomLayer key (bytesLE 32 message) b randomizerAttemptLimit 0 >>=
          fun found => pure (b, found))) := by
    simp [map_eq_bind_pure_comp, liftM_bind]
    rfl
  rw [hlift]
  unfold XmssSecurity.romImpl
  rw [QueryImpl.simulateQ_add_liftM_right, simulateQ_map, StateT.run_map]

/-- The base call on a fresh randomizer input has the law of `signWithBase` of leanVM on the view,
at a key whose top tree is signed. -/
theorem evalDist_baseCall
    (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer key (bytesLE 32 message) b t))
    (hR : ¬K (randomizerInput secretKey.parameter bottomLayer key ρ (bytesLE 32 message)))
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer key ρ
      (bytesLE 32 message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey key = true) :
    𝒟[(fun p => ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) <$>
        roRun prims (tweakable (baseCall secretKey key ρ message)) c] =
      𝒟[(simulateQ XmssSecurity.romImpl (SigningLane2Proof.signWithBase secretKey key message)).run
        (keptView K c)] := by
  rw [baseCall, tweakable_bind, tweakable_oracleHash, roRun_bind,
    roRun_fresh prims _ (randomizerInput_not_mpc _ _ _ _ _) c hfresh, map_bind, bind_map_left]
  have hstep : ∀ u : HashOutput, (fun p => ((p.1.1, signOf secretKey key p.1.2), keptView K p.2)) <$>
      roRun prims (tweakable (grind secretKey.parameter bottomLayer key (bytesLE 32 message) (truncateHash u)
        randomizerAttemptLimit 0 >>= fun found => pure (truncateHash u, found)))
        (c.cacheQuery (.hash (randomizerInput secretKey.parameter bottomLayer key ρ (bytesLE 32 message))) u) =
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
  simp only [htop, if_true]
  change _ = 𝒟[XmssSecurity.Concrete.signingRandomness >>= grindRun secretKey key message (keptView K c)]
  have ht : 𝒟[(truncateHash <$> ($ᵗ HashOutput) : ProbComp Randomness)] =
      𝒟[XmssSecurity.Concrete.signingRandomness] := by
    rw [XmssSecurity.Concrete.signingRandomness_eq]
    refine XmssSecurity.Rom.evalDist_truncate_uniformHashOutput.trans ?_
    rw [evalDist_uniformSample, evalDist_uniformSample]
    rfl
  rw [← bind_map_left (f := truncateHash), evalDist_bind, evalDist_bind, ht]
  rfl

/-- The base call with the trace entry of leanVM has the law of `signWithBaseStep`. -/
theorem baseCall_signWithBaseStep (request : XmssSecurity.SignRequest)
    (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer request.leafIndex
      (bytesLE 32 request.message) b t))
    (hR : ¬K (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ (bytesLE 32 request.message)))
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ
      (bytesLE 32 request.message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey request.leafIndex = true)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun p => ((p.1.1, signOf secretKey request.leafIndex p.1.2),
        ((keptView K p.2, trace ++ [⟨request, signOf secretKey request.leafIndex p.1.2, keptView K c,
          keptView K p.2⟩]), k))) <$>
        roRun prims (tweakable (baseCall secretKey request.leafIndex ρ request.message)) c] =
      𝒟[(SigningLane2Proof.signWithBaseStep secretKey request).run ((keptView K c, trace), k)] := by
  have h := evalDist_baseCall prims secretKey request.leafIndex ρ request.message hK hR c hfresh htop
  have h' := congrArg (fun d => (fun r : (XmssSecurity.Randomness × Option XmssSecurity.Signature) ×
      XmssSecurity.HashSpec.QueryCache => (r.1, ((r.2, trace ++ [⟨request, r.1.2, keptView K c, r.2⟩]), k))) <$> d) h
  simp only [← evalDist_map, Functor.map_map] at h'
  rw [SigningLane2Proof.signWithBaseStep, StateT.run_mk]
  exact h'

/-- The state law of the base call is the law of the sign step of leanVM. This is the hypothesis
`hlaw` of `f1_step_of_law` to `f4_step_of_law`. -/
theorem baseCall_stateLaw (publicKey : XmssSecurity.PublicKey) (request : XmssSecurity.SignRequest)
    (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer request.leafIndex
      (bytesLE 32 request.message) b t))
    (hR : ¬K (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ (bytesLE 32 request.message)))
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ
      (bytesLE 32 request.message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey request.leafIndex = true)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun p => (((keptView K p.2, trace ++ [⟨request, signOf secretKey request.leafIndex p.1.2,
          keptView K c, keptView K p.2⟩]), k) : XmssSecurity.Ghost.State)) <$>
        roRun prims (tweakable (baseCall secretKey request.leafIndex ρ request.message)) c] =
      𝒟[(fun y => y.2) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inr request)).run ((keptView K c, trace), k)] := by
  have h := congrArg (fun d => Prod.snd <$> d)
    (baseCall_signWithBaseStep prims secretKey ρ request hK hR c hfresh htop trace k)
  simp only [← evalDist_map, Functor.map_map] at h
  exact h.trans (SigningLane2Proof.evalDist_signWithBaseStep publicKey secretKey request _)

/-- `f1_step` of leanVM at the base call, for a state that is a world cache with the trace and the
count. -/
theorem f1_step_baseCall (publicKey : XmssSecurity.PublicKey) (request : XmssSecurity.SignRequest)
    (hK : ∀ b t, K (trialInput secretKey.parameter bottomLayer request.leafIndex
      (bytesLE 32 request.message) b t))
    (hR : ¬K (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ (bytesLE 32 request.message)))
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ
      (bytesLE 32 request.message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey request.leafIndex = true)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    ∑' z, Pr[= z | (fun p => (p.1, (((keptView K p.2, trace ++ [⟨request, signOf secretKey request.leafIndex p.1.2,
          keptView K c, keptView K p.2⟩]), k) : XmssSecurity.Ghost.State))) <$>
        roRun prims (tweakable (baseCall secretKey request.leafIndex ρ request.message)) c] *
        XmssSecurity.Ghost.f1 secretKey z.2 ≤
      XmssSecurity.Ghost.f1 secretKey ((keptView K c, trace), k) +
        XmssSecurity.Ghost.cost1 secretKey (.inr request) ((keptView K c, trace), k) :=
  SigningLane2Proof.f1_step_of_law publicKey secretKey _ id ((keptView K c, trace), k) (.inr request) (by
    simp only [Functor.map_map, id]
    exact baseCall_stateLaw prims secretKey ρ publicKey request hK hR c hfresh htop trace k)

/-! With `K = IsMsg` the hypotheses on `K` hold. -/

theorem isMsg_trialInput (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (b : Randomness) (t : ℕ) : IsMsg (trialInput parameter lay key message b t) :=
  byte23_msg _ _ _ _

theorem not_isMsg_randomizerInput (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) : ¬IsMsg (randomizerInput parameter lay e ρ message) := by
  unfold IsMsg
  rw [byte23_randomizer]
  decide

/-- `baseCall_stateLaw` with the view of the message digest inputs. -/
theorem baseCall_stateLaw_isMsg (publicKey : XmssSecurity.PublicKey) (request : XmssSecurity.SignRequest)
    (c : HashCache C) (hfresh : c (.hash (randomizerInput secretKey.parameter bottomLayer request.leafIndex ρ
      (bytesLE 32 request.message))) = none)
    (htop : XmssSecurity.Concrete.topSignedAt secretKey request.leafIndex = true)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun p => (((keptView IsMsg p.2, trace ++ [⟨request, signOf secretKey request.leafIndex p.1.2,
          keptView IsMsg c, keptView IsMsg p.2⟩]), k) : XmssSecurity.Ghost.State)) <$>
        roRun prims (tweakable (baseCall secretKey request.leafIndex ρ request.message)) c] =
      𝒟[(fun y => y.2) <$>
        (XmssSecurity.Ghost.impl publicKey secretKey (.inr request)).run ((keptView IsMsg c, trace), k)] :=
  baseCall_stateLaw prims secretKey ρ publicKey request (fun b t => isMsg_trialInput _ _ _ _ b t)
    (not_isMsg_randomizerInput _ _ _ _ _) c hfresh htop trace k

end Base

/-! ## The top signature

`topSignedAt secretKey e` reads `secretKey.topSigned (topKeyOf e)`. In the threshold run the top
key `b` signs the root of bottom tree `b` in the ceremony of that tree, with the top grind. The top
grind is `topSignFrom` of leanVM, which fills `topSigned` in its key generation. -/

section Top

/-- Bottom key `k` of bottom tree `b` is under top key `b`. -/
theorem topKeyOf_bottomKey (b k : Fin (2 ^ layerHeight)) :
    XmssSecurity.Bridge.topKey (XmssSecurity.topKeyOf (bottomKey b k)) = topKey b := by
  apply Fin.ext
  have hk := k.isLt
  simp only [XmssSecurity.Bridge.topKey_val, XmssSecurity.topKeyOf, bottomKey, topKey,
    XmssSecurity.treeHeight, layerHeight] at *
  omega

/-- The top grind is `topSignFrom` of leanVM from the same base. -/
theorem grind_top_eq_topSignFrom (parameter : PublicParameter) (key : XmssSecurity.TopIndex)
    (root : Digest) (base : Randomness) (attempts trial : ℕ) :
    (grind parameter topLayer (XmssSecurity.Bridge.topKey key) (bytesLE 16 root) base attempts trial :
        OracleComp HashSpec _) =
      (XmssSecurity.Concrete.topSignFrom parameter key root base attempts trial :
        OracleComp XmssSecurity.HashSpec _) := by
  induction attempts generalizing trial with
  | zero => rfl
  | succ attempts ih =>
    rw [grind, XmssSecurity.Concrete.topSignFrom]
    rw [XmssSecurity.Bridge.messageDigest_top]
    refine bind_congr fun digest => ?_
    rw [XmssSecurity.Bridge.decode_eq]
    cases XmssSecurity.TargetSum.decodeDigest digest with
    | none => exact ih (trial + 1)
    | some encoding => rfl

end Top

end SigningLane2BridgeProof

open SigningLane2BridgeProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.worldCall_viewLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worldCall_viewLaw

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.liftM_grind_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftM_grind_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.baseCall_stateLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms baseCall_stateLaw

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.worldCall_stateLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worldCall_stateLaw

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2BridgeProof.grind_top_eq_topSignFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grind_top_eq_topSignFrom

end ThresholdLeanXmssSecurity
