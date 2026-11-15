import ThresholdLeanXmssSecurity.Proof.SigningAssembly

/-!
# The lane 2 base call on the flat run

This module gives the base-call facts of `SigningLane2Bridge` on the split run of
`SigningFlatEager`. The view is `keptView IsMsg`. `SigningLane2TraceLink` and
`SigningReleasedAlign` use these facts.

* The lane 2 terms read only the parameter of the leanVM key and whether a top key signed.
  `laneKey P` signs every top key, so `htop` holds at every key (`topSignedAt_laneKey`).
* At a base call the eager grind is `baseCall` (`eagerBase_eq_roRun`). On a fresh randomizer
  input, the view and the trace have the law of `signWithBaseStep` at `laneKey`
  (`eagerBase_signWithBaseStep`).
* `cachedFound` reads the result of the grind from a cache that holds its trials
  (`randomOracle_run_evalTh`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLane2FlatProof

open HashSig LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningLane2BridgeProof

variable {C : Committee} (prims : Primitives)

/-! ## The top signature -/

/-- A leanVM key at the public parameter `P` whose top keys all signed. The lane 2 terms read only
the parameter and whether the top key signed, so this key serves for every run at `P`. -/
def laneKey (P : PublicParameter) : XmssSecurity.SecretKey where
  parameter := P
  chainStart := fun _ _ => 0
  chainValue := fun _ _ _ => 0
  treeValue := fun _ _ => 0
  topChainStart := fun _ _ => 0
  topChainValue := fun _ _ _ => 0
  topTreeValue := fun _ _ => 0
  topSigned := fun _ => some (0, fun _ => ⟨0, by decide⟩)

/-- `htop` of `baseCall_signWithBaseStep` holds at every key of `laneKey`. -/
theorem topSignedAt_laneKey (P : PublicParameter) (key : XmssSecurity.LeafIndex) :
    XmssSecurity.Concrete.topSignedAt (laneKey P) key = true := rfl

/-! ## The eager grind as the base call -/

/-- A computation of leanVM that queries only inputs outside the MPC runs on the lazy `H` of the
signing world as it runs in `roRun`. -/
theorem randomOracle_run_eq_roRun {α : Type} {oa : OracleComp HashSpec α}
    (hoa : XmssSecurity.Bridge.OnlyQueries (fun x => ¬MpcInput x) oa) (c : HashCache C) :
    (simulateQ (Query C →ₒ HashOutput).randomOracle
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa)).run c =
      roRun prims (tweakable oa) c := by
  induction hoa generalizing c with
  | pure a => simp [tweakable_pure, roRun_pure]
  | query x hx next _ ih =>
    rw [tweakable_bind]
    change _ = roRun prims (tweakable (Verification.oracleHashWithHash x) >>= _) c
    rw [tweakable_oracleHash, roRun_bind, roRun_hashQuery]
    simp only [simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, hashAnswer, if_neg hx]
    erw [simulateQ_spec_query]
    exact bind_congr fun (p : HashOutput × HashCache C) => ih p.1 p.2

/-- The grind of `baseGrind` with its result. -/
def foundGrind (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput) :
    OracleComp (Query C →ₒ HashOutput) (Option (Randomizer × Encoding)) :=
  simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
    (grind P bottomLayer e (littleEndianBytes 32 message) (truncateHash answer) randomizerAttemptLimit 0)

theorem baseGrind_eq (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput) :
    baseGrind (C := C) P e message answer = (fun _ => ()) <$> foundGrind P e message answer := rfl

/-- The base call of the eager run, the answer at the randomizer input and then the grind, as the
base call `baseCall` of `SigningLane2Bridge`. -/
theorem eagerBase_eq_roRun (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (message : Message)
    (c : HashCache C) :
    ((Query C →ₒ HashOutput).randomOracle (.hash (randomizerInput P bottomLayer e ρ (littleEndianBytes 32 message)))).run c >>=
        (fun p => (simulateQ (Query C →ₒ HashOutput).randomOracle (foundGrind P e message p.1)).run p.2 >>=
          fun w => pure ((truncateHash p.1, w.1), w.2)) =
      roRun prims (tweakable (baseCall (laneKey P) e ρ message)) c := by
  unfold baseCall
  rw [tweakable_bind, tweakable_oracleHash, roRun_bind, roRun_hashQuery]
  simp only [hashAnswer, if_neg (randomizerInput_not_mpc (laneKey P).parameter bottomLayer e ρ
    (littleEndianBytes 32 message))]
  refine bind_congr fun p => ?_
  rw [tweakable_bind, roRun_bind]
  erw [← randomOracle_run_eq_roRun prims
    ((grind_onlyQueries _ _ _ _ _ _ (fun t => messageInput_not_mpc _ _ _ _)) _ _)]
  rfl

include prims in
/-- The base call of the eager run on a fresh randomizer input, with the trace entry of leanVM, has
the law of `signWithBaseStep` on the view. `htop` holds at `laneKey`. -/
theorem eagerBase_signWithBaseStep (P : PublicParameter) (ρ : Digest) (request : XmssSecurity.SignRequest)
    (c : HashCache C)
    (hfresh : c (.hash (randomizerInput P bottomLayer request.leafIndex ρ (littleEndianBytes 32 request.message))) = none)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    ((fun p => ((p.1.1, signOf (laneKey P) request.leafIndex p.1.2),
        ((keptView IsMsg p.2, trace ++ [⟨request, signOf (laneKey P) request.leafIndex p.1.2, keptView IsMsg c,
          keptView IsMsg p.2⟩]), k))) <$>
        (((Query C →ₒ HashOutput).randomOracle
          (.hash (randomizerInput P bottomLayer request.leafIndex ρ (littleEndianBytes 32 request.message)))).run c >>=
          (fun p => (simulateQ (Query C →ₒ HashOutput).randomOracle
            (foundGrind P request.leafIndex request.message p.1)).run p.2 >>=
              fun w => pure ((truncateHash p.1, w.1), w.2)))) =ᵈ
      (SigningLane2Proof.signWithBaseStep (laneKey P) request).run ((keptView IsMsg c, trace), k) := by
  rw [eagerBase_eq_roRun prims P request.leafIndex ρ request.message c]
  exact baseCall_signWithBaseStep prims (laneKey P) ρ request (fun b t => isMsg_trialInput _ _ _ _ b t)
    (not_isMsg_randomizerInput _ _ _ _ _) c hfresh (topSignedAt_laneKey P _) trace k

/-! ## The leanVM trace in the flat state -/

/-- The state of the split run. -/
abbrev SplitState (C : Committee) :=
  ((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) × (TsigState C × Bool)

/-- The cache of a state of the split run. -/
abbrev SplitState.cache (p : SplitState C) : HashCache C := p.1.1.1.1.1

/-- The result of the grind at key `e` read from a cache that holds its trials. -/
def cachedFound (c : HashCache C) (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (message : Message) :
    Option (Randomizer × Encoding) :=
  evalTh (fun x => (c (.hash x)).getD 0)
    (grind P bottomLayer e (littleEndianBytes 32 message)
      (truncateHash ((c (.hash (randomizerInput P bottomLayer e ρ (littleEndianBytes 32 message)))).getD 0))
      randomizerAttemptLimit 0)

/-- Each run of a computation of leanVM on the lazy `H` returns the computation with `H` read from
any cache that extends the final cache. -/
theorem randomOracle_run_evalTh {α : Type} (oa : OracleComp HashSpec α) :
    ∀ (c : HashCache C) z, z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa)).run c) →
      c ≤ z.2 ∧ ∀ c' : HashCache C, z.2 ≤ c' → z.1 = evalTh (fun x => (c' (.hash x)).getD 0) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c z hz
    simp at hz
    subst hz
    exact ⟨le_rfl, fun _ _ => rfl⟩
  | query_bind x k ih =>
    intro c z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    erw [simulateQ_spec_query] at hi
    obtain ⟨hle, hself, -⟩ := randomOracle_support _ c i hi
    obtain ⟨hle', heq⟩ := ih i.1 i.2 z hz
    refine ⟨hle.trans hle', fun c' hc' => ?_⟩
    rw [heq c' hc']
    have hv : (c' (Query.hash x)).getD 0 = i.1 := by
      rw [hc' (hle' hself)]
      rfl
    simp only [evalTh, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    simp only [pure_bind]
    exact congrArg (fun u => simulateQ _ (k u)) hv.symm

/-- A call of `H` on either copy is the lazy `H` with the count of one. -/
theorem countImpl_hashCallAt {input : HashInput} {t : (WorldSpec C).Domain} (ht : HashCallAt input t)
    (s : HashCache C × ℕ) :
    (fun w => (w.2.1, w.2.2)) <$> (SigningCacheProof.countImpl prims t).run s =
      (fun w => (w.2, s.2 + 1)) <$> ((Query C →ₒ HashOutput).randomOracle (.hash input)).run s.1 := by
  rcases ht with rfl | rfl <;>
  · simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, Functor.map_map]
    rfl

/-- The canonical base call of `e` calls `H` at the randomizer input of `e` and its bound message. -/
theorem hashCallAt_of_baseCall {P : PublicParameter} {e : KeyIndex} {ρ : Digest} {st : TsigState C}
    {t : (WorldSpec C).Domain} (ht : BaseCall P e ρ st t) {message : Message} (hm : st.bound e = some message) :
    HashCallAt (randomizerInput P bottomLayer e ρ (littleEndianBytes 32 message)) t := by
  obtain ⟨input, hb, hcall⟩ := ht
  simp only [baseInput, hm] at hb
  have h2 : some (randomizerInput P bottomLayer e ρ (littleEndianBytes 32 message)) = some input := hb
  rw [Option.some.inj h2]
  exact hcall

end SigningLane2FlatProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2FlatProof.eagerBase_signWithBaseStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2FlatProof.eagerBase_signWithBaseStep
