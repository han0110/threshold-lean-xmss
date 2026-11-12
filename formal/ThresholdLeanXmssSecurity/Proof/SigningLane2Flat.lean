import ThresholdLeanXmssSecurity.Proof.SigningAssembly

/-!
# The lane 2 potential on the flat run

This module gives the facts of `SigningLane2Bridge` ("Potential hypotheses") on the split run of `SigningFlatEager`.
The view is `keptView IsMsg`.

## Run and trace laws

* `htop`. The lane 2 terms read only the parameter of the leanVM key and whether a top key signed.
  `laneKey P` signs every top key, so `htop` holds at every key (`topSignedAt_laneKey`).
* The run-level form of `keptView_cacheQuery_of_not`. A world call that writes no message digest
  input keeps the view (`countImpl_keptView`, `carry_logged_keptView`). On the split run this holds
  at each such call other than a canonical base call (`splitWorld_keptView`).
* The trace. `laneRun` is the split run with the leanVM trace in the state. The trace is write-only
  (`laneRun_forget`), so the rows of the split run have the same law on the lane run. `traceStep`
  appends one entry at a canonical base call on a fresh randomizer input, as the states of
  `baseCall_signWithBaseStep`.
* The base call. There the eager grind is `baseCall` (`eagerBase_eq_roRun`), and the view and the
  trace have the law of `signWithBaseStep` at `laneKey` (`splitWorld_baseLaw`).

## Potential hypotheses and their limitations

* `hfresh` is not an invariant. A base call on a cached randomizer input appends no entry, and its
  grind writes trial entries with no sign step of leanVM. So the step facts fail there. `StaleBase`
  names that state. The capped hybrid must stop the potential there and pay the case with the
  input-side flag.
* `BaseTrialsCachedInvariant`. A later base call of a key finds all its trials cached.
* `MsgCallLaw`. A call of `H` at a message digest input is the world step of leanVM.
* The step hypotheses of `probEvent_lane2_le` in the form `countImpl impl p t`, the start facts and
  the coupling of the lane run to the capped hybrid.

## The row `CachedPartnerRow` and the event of leanVM

`CachedPartnerRow` does not imply `ghostEvent` on the lane run. `CachedSelection` is one flag for all
keys, and `EagerPartner` reads the forged key only. Take an outcome with a cached selection at key
`e1` with no partner there, and a partner at the forged key `e2` whose selection was fresh. Then
`PreBad` fails at both keys, `PostBad` fails at `e2` because its selected input was not cached
before its base call, and no key has a stale base. A link to the lane 2 event needs the cached
selection at the forged key.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningLane2FlatProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningLane2BridgeProof

variable {C : Committee} (prims : Primitives)

/-! ## A call outside the view keeps the view -/

/-- A cache that changes only at `q` keeps the view when `q` is not a message digest input. -/
theorem keptView_eq_of_agree {q : Query C} (hq : ∀ x, q = .hash x → ¬IsMsg x) {c c' : HashCache C}
    (h : ∀ q', q' ≠ q → c' q' = c q') : keptView IsMsg c' = keptView IsMsg c := by
  funext y
  simp only [keptView]
  split_ifs with hy
  · exact h _ fun h' => hq y h'.symm hy
  · rfl

/-- A world call that can write `H` at a message digest input. It is a call of `H` on either copy,
or a programming query, at that input. -/
def MsgCall (t : (WorldSpec C).Domain) : Prop :=
  ∃ x, IsMsg x ∧ (HashCallAt x t ∨ ∃ u, t = .inl (.inr (.hash x, u)))

/-- A local call that does not write `H` at a message digest input keeps the view. -/
theorem signingLocal_keptView (u : (LocalSpec C).Domain)
    (hu : ∀ x, IsMsg x → u ≠ .inr (.inl (.hash x))) (c : HashCache C)
    (w : (LocalSpec C).Range u × HashCache C) (hw : w ∈ support ((signingLocalAnswer prims u).run c)) :
    keptView IsMsg w.2 = keptView IsMsg c := by
  rcases u with n | q | y
  · change w ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run c) at hw
    simp [unifFwdImpl] at hw
    obtain ⟨a, rfl⟩ := hw
    rfl
  · obtain ⟨-, -, hrest⟩ := randomOracle_support q c w hw
    exact keptView_eq_of_agree (fun x hx hmsg => hu x hmsg (by rw [hx])) hrest
  · change w ∈ support ((prgAnswer prims y).run c) at hw
    unfold prgAnswer at hw
    rw [StateT.run_bind] at hw
    simp only [support_bind] at hw
    obtain ⟨p', hp', hw⟩ := Set.mem_iUnion₂.mp hw
    simp only [StateT.run_pure, support_pure] at hw
    subst hw
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hp'
    obtain ⟨-, -, hrest⟩ := randomOracle_support _ c p' hp'
    exact keptView_eq_of_agree (fun x hx => by cases hx) hrest

/-- A world call of the signing world that does not write `H` at a message digest input keeps the
view. This is the run-level form of `keptView_cacheQuery_of_not`. -/
theorem countImpl_keptView (t : (WorldSpec C).Domain) (ht : ¬MsgCall t) (s : HashCache C × ℕ)
    (w : (WorldSpec C).Range t × HashCache C × ℕ)
    (hw : w ∈ support ((SigningCacheProof.countImpl prims t).run s)) :
    keptView IsMsg w.2.1 = keptView IsMsg s.1 := by
  simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map,
    Set.mem_image] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  rcases t with (u | x) | u
  · exact signingLocal_keptView prims u (fun y hy hu => ht ⟨y, hy, Or.inl (Or.inl (by rw [hu]))⟩) s.1 r hr
  · change r ∈ support ((programAnswer (C := C) x).run s.1) at hr
    obtain ⟨q, o⟩ := x
    unfold programAnswer at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr with hc
    · simp at hr; subst hr; rfl
    · simp [StateT.run_set] at hr
      subst hr
      refine keptView_eq_of_agree (q := q) (fun y hy hmsg => ht ⟨y, hmsg, Or.inr ⟨o, by rw [hy]⟩⟩) fun q' hq' => ?_
      exact QueryCache.cacheQuery_of_ne _ _ hq'
  · exact signingLocal_keptView prims u (fun y hy hu => ht ⟨y, hy, Or.inl (Or.inr (by rw [hu]))⟩) s.1 r hr

/-- A logged world call that does not write `H` at a message digest input keeps the view. -/
theorem carry_logged_keptView {σ : Type} (t : (WorldSpec C).Domain) (ht : ¬MsgCall t)
    (p : SigningHitLaneProof.LoggedState C × σ)
    (z : (WorldSpec C).Range t × (SigningHitLaneProof.LoggedState C × σ))
    (hz : z ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run p)) :
    keptView IsMsg z.2.1.1.1 = keptView IsMsg p.1.1.1 := by
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, ⟨w, hw, rfl⟩, rfl⟩ := hz
  exact countImpl_keptView prims t ht p.1.1 w hw

set_option linter.constructorNameAsVariable false in
/-- A world call of the split run that is neither a canonical base call nor a call that writes `H`
at a message digest input keeps the view. The eager grind runs only at a canonical base call. -/
theorem splitWorld_keptView (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain) (ht : ¬MsgCall t)
    (p : ((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) × (TsigState C × Bool))
    (hbase : ¬∃ e, BaseCall P e (ρ e) p.2.1 t)
    (z : (WorldSpec C).Range t × (((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) ×
      (TsigState C × Bool)))
    (hz : z ∈ support ((splitWorld prims keyOf (grindExtra P ρ) t).run p)) :
    keptView IsMsg z.2.1.1.1.1.1 = keptView IsMsg p.1.1.1.1.1 := by
  simp only [splitWorld, StateT.run_mk, support_bind, Set.mem_iUnion] at hz
  obtain ⟨z0, hz0, hz⟩ := hz
  have hextra : grindExtra P ρ (p.1.1.1, p.2) t z0.2 = pure () := dif_neg hbase
  rw [hextra, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact carry_logged_keptView prims t ht (p.1.1.1, p.2) z0 hz0

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

/-- `htop` of `baseCall_stateLaw` holds at every key of `laneKey`. -/
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
    change _ = roRun prims (tweakable (Concrete.oracleHash x) >>= _) c
    rw [tweakable_oracleHash, roRun_bind, roRun_hashQuery]
    simp only [simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, hashAnswer, if_neg hx]
    erw [simulateQ_spec_query]
    exact bind_congr fun (p : HashOutput × HashCache C) => ih p.1 p.2

/-- The grind of `baseGrind` with its result. -/
def foundGrind (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput) :
    OracleComp (Query C →ₒ HashOutput) (Option (Randomness × Encoding)) :=
  simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
    (grind P bottomLayer e (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0)

theorem baseGrind_eq (P : PublicParameter) (e : KeyIndex) (message : Message) (answer : HashOutput) :
    baseGrind (C := C) P e message answer = (fun _ => ()) <$> foundGrind P e message answer := rfl

/-- The base call of the eager run, the answer at the randomizer input and then the grind, as the
base call `baseCall` of `SigningLane2Bridge`. -/
theorem eagerBase_eq_roRun (P : PublicParameter) (e : KeyIndex) (ρ : Digest) (message : Message)
    (c : HashCache C) :
    ((Query C →ₒ HashOutput).randomOracle (.hash (randomizerInput P bottomLayer e ρ (bytesLE 32 message)))).run c >>=
        (fun p => (simulateQ (Query C →ₒ HashOutput).randomOracle (foundGrind P e message p.1)).run p.2 >>=
          fun w => pure ((truncateHash p.1, w.1), w.2)) =
      roRun prims (tweakable (baseCall (laneKey P) e ρ message)) c := by
  rw [baseCall, tweakable_bind, tweakable_oracleHash, roRun_bind, roRun_hashQuery]
  simp only [hashAnswer, if_neg (randomizerInput_not_mpc _ _ _ _ _)]
  refine bind_congr fun p => ?_
  rw [tweakable_bind, roRun_bind, ← randomOracle_run_eq_roRun prims
    ((grind_onlyQueries _ _ _ _ _ _ (fun t => messageInput_not_mpc _ _ _ _)) _ _)]
  rfl

include prims in
/-- The base call of the eager run on a fresh randomizer input, with the trace entry of leanVM, has
the law of `signWithBaseStep` on the view. `htop` holds at `laneKey`. -/
theorem eagerBase_signWithBaseStep (P : PublicParameter) (ρ : Digest) (request : XmssSecurity.SignRequest)
    (c : HashCache C)
    (hfresh : c (.hash (randomizerInput P bottomLayer request.leafIndex ρ (bytesLE 32 request.message))) = none)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun p => ((p.1.1, signOf (laneKey P) request.leafIndex p.1.2),
        ((keptView IsMsg p.2, trace ++ [⟨request, signOf (laneKey P) request.leafIndex p.1.2, keptView IsMsg c,
          keptView IsMsg p.2⟩]), k))) <$>
        (((Query C →ₒ HashOutput).randomOracle
          (.hash (randomizerInput P bottomLayer request.leafIndex ρ (bytesLE 32 request.message)))).run c >>=
          (fun p => (simulateQ (Query C →ₒ HashOutput).randomOracle
            (foundGrind P request.leafIndex request.message p.1)).run p.2 >>=
              fun w => pure ((truncateHash p.1, w.1), w.2)))] =
      𝒟[(SigningLane2Proof.signWithBaseStep (laneKey P) request).run ((keptView IsMsg c, trace), k)] := by
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
    Option (Randomness × Encoding) :=
  evalTh (fun x => (c (.hash x)).getD 0)
    (grind P bottomLayer e (bytesLE 32 message)
      (truncateHash ((c (.hash (randomizerInput P bottomLayer e ρ (bytesLE 32 message)))).getD 0))
      randomizerAttemptLimit 0)

open Classical in
/-- The trace step of a world call of the split run. A canonical base call of `e` on a fresh
randomizer input appends the entry of the leanVM sign step. The entry reads the grind result from
the cache after the call, the view before the call and the view after the call. Every other call
keeps the trace. -/
def traceStep (P : PublicParameter) (ρ : KeyIndex → Digest) (p : SplitState C) (t : (WorldSpec C).Domain)
    (p' : SplitState C) (trace : XmssSecurity.SigningCacheTrace) : XmssSecurity.SigningCacheTrace :=
  if h : ∃ e, BaseCall P e (ρ e) p.2.1 t then
    match p.2.1.bound h.choose with
    | some message =>
      if p.cache (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) = none then
        trace ++ [⟨⟨h.choose, message⟩,
          signOf (laneKey P) h.choose (cachedFound p'.cache P h.choose (ρ h.choose) message),
          keptView IsMsg p.cache, keptView IsMsg p'.cache⟩]
      else trace
    | none => trace
  else trace

/-- The world calls of the split run with the leanVM trace. The trace is write-only. -/
def laneWorld (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) :
    QueryImpl (WorldSpec C) (StateT ((((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) ×
      Bool) × XmssSecurity.SigningCacheTrace) × (TsigState C × Bool)) ProbComp) :=
  fun t => StateT.mk fun p => (fun z => (z.1, ((z.2.1, traceStep P ρ (p.1.1, p.2) t z.2 p.1.2), z.2.2))) <$>
    (splitWorld prims keyOf (grindExtra P ρ) t).run (p.1.1, p.2)

theorem laneWorld_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain) :
    Forgets (laneWorld prims keyOf P ρ t) (splitWorld prims keyOf (grindExtra P ρ) t) := by
  intro a b s
  simp only [laneWorld, StateT.run_mk, Functor.map_map]
  exact id_map _

/-- The split run with the leanVM trace. -/
def laneGame (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    StateT ((((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) ×
      XmssSecurity.SigningCacheTrace) × (TsigState C × Bool)) ProbComp (Result C) :=
  gameWith A x (laneWorld prims keyOf P ρ)
    (fun dealt => flatWith (SigningCoreProof.flaggedOracles x dealt) (laneWorld prims keyOf P ρ)) getCarried

theorem laneGame_forgets (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Forgets (laneGame prims keyOf P ρ A x) (splitGame prims keyOf (grindExtra P ρ) A x) := by
  unfold laneGame splitGame gameWith
  dsimp only
  have hW := laneWorld_forgets (C := C) prims keyOf P ρ
  refine forgets_bind (forgets_simulateQ _ _ hW _) fun r => ?_
  rcases r with _ | (top | tree)
  · exact forgets_pure _
  · refine forgets_bind (forgets_simulateQ _ _ (forgets_flatWith _ _ _ hW) _) fun a => ?_
    refine forgets_bind forgets_getCarried fun s => ?_
    refine forgets_bind (forgets_simulateQ _ _ hW _) fun w => ?_
    exact forgets_pure _
  · exact forgets_pure _

/-- The split run with the leanVM trace, from the empty trace. -/
def laneRun (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp (Result C × ((((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) ×
      XmssSecurity.SigningCacheTrace) × (TsigState C × Bool))) :=
  (laneGame prims keyOf P ρ A x).run (((monitoredInit.1, false), []), monitoredInit.2)

/-- Without the trace, the lane run is the split run exactly. So the rows of the split run, such as
`CachedPartnerRow`, read the same law on the lane run. -/
theorem laneRun_forget (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (P : PublicParameter)
    (ρ : KeyIndex → Digest) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, (z.2.1.1, z.2.2))) <$> laneRun prims keyOf P ρ A x = splitRun prims keyOf P ρ A x :=
  laneGame_forgets prims keyOf P ρ A x _ _ _

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
    HashCallAt (randomizerInput P bottomLayer e ρ (bytesLE 32 message)) t := by
  obtain ⟨input, hb, hcall⟩ := ht
  simp only [baseInput, hm] at hb
  have h2 : some (randomizerInput P bottomLayer e ρ (bytesLE 32 message)) = some input := hb
  rw [Option.some.inj h2]
  exact hcall

/-- The trace step at the first canonical base call of a key, on a fresh randomizer input. -/
theorem traceStep_base (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain)
    (p : SplitState C) (h : ∃ e, BaseCall P e (ρ e) p.2.1 t) {message : Message}
    (hm : p.2.1.bound h.choose = some message)
    (hfresh : p.cache (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) = none)
    (p' : SplitState C) (trace : XmssSecurity.SigningCacheTrace) :
    traceStep P ρ p t p' trace = trace ++ [⟨⟨h.choose, message⟩,
      signOf (laneKey P) h.choose (cachedFound p'.cache P h.choose (ρ h.choose) message),
      keptView IsMsg p.cache, keptView IsMsg p'.cache⟩] := by
  unfold traceStep
  rw [dif_pos h]
  simp only [hm, hfresh, if_true]

/-- The eager grind at a canonical base call reads the answer at the randomizer input. -/
theorem grindExtra_base (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain)
    (p : FlatState C) (h : ∃ e, BaseCall P e (ρ e) p.2.1 t) {message : Message}
    (hm : p.2.1.bound h.choose = some message) (p' : FlatState C) (u : HashOutput)
    (hu : p'.1.1.1 (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) = some u) :
    grindExtra P ρ p t p' = baseGrind P h.choose message u := by
  unfold grindExtra
  rw [dif_pos h]
  simp only [hm, hu]

set_option linter.constructorNameAsVariable false in
/-- **The base call of the split run is the sign step of leanVM.** At the first canonical base call
of a key, on a fresh randomizer input, the view and the trace of the split run have the law of
`signWithBaseStep` at `laneKey`. The count of leanVM does not move at a sign step. -/
theorem splitWorld_baseLaw (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (t : (WorldSpec C).Domain) (p : SplitState C)
    (h : ∃ e, BaseCall P e (ρ e) p.2.1 t) {message : Message} (hm : p.2.1.bound h.choose = some message)
    (hfresh : p.cache (.hash (randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message))) = none)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) :
    𝒟[(fun z : (WorldSpec C).Range t × SplitState C => (((keptView IsMsg (SplitState.cache z.2), traceStep P ρ p t z.2 trace), k) : XmssSecurity.Ghost.State)) <$>
        (splitWorld prims keyOf (grindExtra P ρ) t).run p] =
      𝒟[(fun y => y.2) <$> (SigningLane2Proof.signWithBaseStep (laneKey P) ⟨h.choose, message⟩).run
        ((keptView IsMsg p.cache, trace), k)] := by
  have hcall := hashCallAt_of_baseCall h.choose_spec hm
  set R := randomizerInput P bottomLayer h.choose (ρ h.choose) (bytesLE 32 message) with hR
  simp only [splitWorld, StateT.run_mk, map_bind, Functor.map_map]
  let G : HashCache C → XmssSecurity.Ghost.State := fun c' =>
    ((keptView IsMsg c', trace ++ [⟨⟨h.choose, message⟩,
      signOf (laneKey P) h.choose (cachedFound c' P h.choose (ρ h.choose) message),
      keptView IsMsg p.cache, keptView IsMsg c'⟩]), k)
  have hinner : ∀ a ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1, p.2)),
      (fun a_1 : Unit × ((HashCache C × SigningPartnerBoundProof.Monitor) × Bool) =>
        (((keptView IsMsg (SplitState.cache ((((ofRest a_1.2.1.1 (restOf a.2)).1, a_1.2.1.2), a_1.2.2),
          (ofRest a_1.2.1.1 (restOf a.2)).2)), traceStep P ρ p t ((((ofRest a_1.2.1.1 (restOf a.2)).1,
            a_1.2.1.2), a_1.2.2), (ofRest a_1.2.1.1 (restOf a.2)).2) trace), k) : XmssSecurity.Ghost.State)) <$>
        (simulateQ (splitOracle keyOf) (grindExtra P ρ (p.1.1.1, p.2) t a.2)).run
          ((a.2.1.1.1, queryEntryStep keyOf p.1.1.2 (SigningPartnerBoundProof.hashEntry ⟨t, a.1⟩)), p.1.2) =
      (fun y => G y.2) <$> (simulateQ (Query C →ₒ HashOutput).randomOracle
        (grindExtra P ρ (p.1.1.1, p.2) t a.2)).run a.2.1.1.1 := by
    intro a _
    simp only [traceStep_base P ρ t p h hm hfresh]
    rw [← monitoredOracle_run_forget keyOf _ _ (queryEntryStep keyOf p.1.1.2 (SigningPartnerBoundProof.hashEntry ⟨t, a.1⟩)),
      ← splitOracle_run_forget keyOf _ _ p.1.2, Functor.map_map, Functor.map_map]
    rfl
  rw [bind_congr_of_forall_mem_support _ hinner]
  let K : HashCache C → ProbComp XmssSecurity.Ghost.State := fun c1 =>
    (fun y => G y.2) <$> (simulateQ (Query C →ₒ HashOutput).randomOracle
      (baseGrind P h.choose message ((c1 (.hash R)).getD 0))).run c1
  have hK : ∀ a ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1, p.2)),
      (fun y => G y.2) <$> (simulateQ (Query C →ₒ HashOutput).randomOracle
        (grindExtra P ρ (p.1.1.1, p.2) t a.2)).run a.2.1.1.1 = K a.2.1.1.1 := by
    intro a ha
    obtain ⟨w, hw, -, hcache, -⟩ := flatWorld_support prims t (p.1.1.1, p.2) a ha
    obtain ⟨u, hu⟩ := countImpl_hash_cached prims R t hcall _ w hw
    have hu' : a.2.1.1.1 (.hash R) = some u := by rw [hcache]; exact hu
    simp only [K, hu', Option.getD_some]
    rw [grindExtra_base P ρ t (p.1.1.1, p.2) h hm a.2 u hu']
  rw [bind_congr_of_forall_mem_support _ hK]
  have hcarry : (fun a => a.2.1.1.1) <$> (carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1, p.2) =
      (fun w => w.2) <$> ((Query C →ₒ HashOutput).randomOracle (.hash R)).run p.cache := by
    have h2 := congrArg (fun m => Prod.fst <$> m) (countImpl_hashCallAt prims hcall p.1.1.1.1)
    simp only [Functor.map_map] at h2
    simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, Functor.map_map]
    exact h2
  have hbind : ((carry (SigningCostProof.loggedImpl prims) t).run (p.1.1.1, p.2) >>= fun x => K x.2.1.1.1) =
      ((fun w => w.2) <$> ((Query C →ₒ HashOutput).randomOracle (.hash R)).run p.cache) >>= K := by
    rw [← hcarry, bind_map_left]
  rw [hbind, bind_map_left]
  let F : (Randomness × Option (Randomness × Encoding)) × HashCache C → XmssSecurity.Ghost.State := fun q =>
    ((keptView IsMsg q.2, trace ++ [⟨⟨h.choose, message⟩, signOf (laneKey P) h.choose q.1.2, keptView IsMsg p.cache,
      keptView IsMsg q.2⟩]), k)
  have hstep : ∀ w ∈ support (((Query C →ₒ HashOutput).randomOracle (.hash R)).run p.cache),
      K w.2 = F <$> ((simulateQ (Query C →ₒ HashOutput).randomOracle (foundGrind P h.choose message w.1)).run w.2 >>=
        fun y => pure ((truncateHash w.1, y.1), y.2)) := by
    intro w hw
    obtain ⟨-, hself, -⟩ := randomOracle_support _ _ w hw
    simp only [K, hself, Option.getD_some, baseGrind_eq, simulateQ_map, StateT.run_map, Functor.map_map,
      map_bind, map_pure]
    rw [map_eq_bind_pure_comp]
    refine bind_congr_of_forall_mem_support _ fun y hy => ?_
    obtain ⟨hle, hev⟩ := randomOracle_run_evalTh _ w.2 y hy
    have hfound : cachedFound y.2 P h.choose (ρ h.choose) message = y.1 := by
      rw [cachedFound, hev y.2 le_rfl, hle hself, Option.getD_some]
    simp only [Function.comp_apply, G, F, hfound]
  rw [bind_congr_of_forall_mem_support _ hstep, ← map_bind]
  have hlaw := congrArg (fun d => Prod.snd <$> d)
    (eagerBase_signWithBaseStep prims P (ρ h.choose) ⟨h.choose, message⟩ p.cache hfresh trace k)
  simp only [← evalDist_map, Functor.map_map] at hlaw
  refine hlaw.trans ?_
  rw [evalDist_map]
  rfl

/-! ## The interface hypotheses

These are the hypotheses of the lane 2 potential on the lane run. Each is a named `Prop` in
its exact form. -/

/-- The state of the lane run. -/
abbrev LaneState (C : Committee) :=
  (((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) × Bool) ×
    XmssSecurity.SigningCacheTrace) × (TsigState C × Bool)

/-- The leanVM cache and trace of a lane state. -/
def laneView (s : LaneState C) : XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace :=
  (keptView IsMsg s.1.1.1.1.1.1, s.1.2)

/-- A key whose randomizer input is cached and that has no trace entry. Its base call, if any, did
not run on a fresh randomizer input. A call on that input before the release is an input-side hit
of the capped flag. -/
def StaleBase (P : PublicParameter) (ρ : KeyIndex → Digest) (s : LaneState C) : Prop :=
  ∃ e message, s.2.1.bound e = some message ∧
    s.1.1.1.1.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) ≠ none ∧
    e ∉ s.1.2.leafIndices

/-- Each key with a trace entry has its randomizer input cached, and its grind from that answer
finds all its trials cached. -/
def BaseTrialsCached (P : PublicParameter) (ρ : KeyIndex → Digest) (s : LaneState C) : Prop :=
  ∀ e message, s.2.1.bound e = some message → e ∈ s.1.2.leafIndices →
    ∃ u, s.1.1.1.1.1.1 (.hash (randomizerInput P bottomLayer e (ρ e) (bytesLE 32 message))) = some u ∧
      ∀ y ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle (baseGrind P e message u)).run
        s.1.1.1.1.1.1), y.2 = s.1.1.1.1.1.1

/-- Open. `BaseTrialsCached` is an invariant of each call of the lane run other than a programming
query. With it, a later canonical base call of a key keeps the view. This is the cached-trials fact
of item A1. -/
def BaseTrialsCachedInvariant (P : PublicParameter) (ρ : KeyIndex → Digest) : Prop :=
  ∀ (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (t : (WorldSpec C).Domain)
    (s : LaneState C), ¬SigningHitLaneProof.IsProgram t → BaseTrialsCached P ρ s →
    ∀ z ∈ support ((laneWorld prims keyOf P ρ t).run s), BaseTrialsCached P ρ z.2

/-- Open. A call of `H` at a message digest input is the world step of leanVM on the view, and it
keeps the trace. The count of leanVM ticks by one. -/
def MsgCallLaw (P : PublicParameter) (ρ : KeyIndex → Digest) : Prop :=
  ∀ (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (publicKey : XmssSecurity.PublicKey)
    (x : HashInput) (t : (WorldSpec C).Domain), IsMsg x → HashCallAt x t →
    ∀ (s : LaneState C) (k : ℕ),
      𝒟[(fun z : (WorldSpec C).Range t × LaneState C => (((laneView z.2), k + 1) : XmssSecurity.Ghost.State)) <$>
          (laneWorld prims keyOf P ρ t).run s] =
        𝒟[(fun y => y.2) <$> (XmssSecurity.Ghost.impl publicKey (laneKey P) (.inl (.inr x))).run (laneView s, k)]

end SigningLane2FlatProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2FlatProof.splitWorld_baseLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2FlatProof.splitWorld_baseLaw

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2FlatProof.splitWorld_keptView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2FlatProof.splitWorld_keptView

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2FlatProof.laneRun_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2FlatProof.laneRun_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningLane2FlatProof.eagerBase_signWithBaseStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLane2FlatProof.eagerBase_signWithBaseStep
