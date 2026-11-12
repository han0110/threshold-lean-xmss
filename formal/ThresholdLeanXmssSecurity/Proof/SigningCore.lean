import ThresholdLeanXmssSecurity.Proof.SigningSecurity

/-!
# The core of the signing security

`SigningCoreBound` of `Proof/SigningSecurity.lean`, a win with distinct keys and `q < 2 ^ 127`
(steps 1 to 6 of the signing plan of `formal/PROOF.md` without the collision of the keys).

The component lemmas:

* `flaggedRun` runs the game of `keyedRun` with a flag. The flag records a call of the forger on a
  key that the corrupt operators do not hold at the time of the call, namely `H16(seed_T ‖ x)` for a
  hidden term `T` or `H16(K_ij ‖ x ‖ m ‖ J)` for a hidden pair (`hiddenHit`). The flag changes nothing
  else (`keyedRun_eq_flaggedRun`).
* A win with distinct keys either sets the flag or wins without it (`core_split`).
* The core over the keys of `KeyGen'` follows from the core for each fixed key with no collision
  (`hiddenCoreBound_of_at`).
* The first obligation of step 3 with a fixed `H`: an honest signer that accepts `ρ ≠ ρ_e` meets a
  hit on `c_e` (`opened_randomizer_hit`, with `commitmentInput_injective`).

The hypotheses of `signingCoreBound`:

* `SeedHitBound`: the flag costs `seedHitError` (step 1, the cost of the hop to the slots of the
  hidden keys, as `real_sym_hop` and the presampling of `Proof/Tprf.lean`).
* `HiddenCoreAt`: for fixed distinct keys, a win without the flag costs `signingHashError q`
  (steps 2 to 6: the positions, the descent of leanVM over two layers, the hit on `c_e` above, the
  partner bound of a digest call with `ρ_e` opened in round 1, and the two lanes).

Without the flag, the run is the run of the symbolic game, so the hop costs nothing there. A
symbolic game alone is not a valid target for fixed keys: a forger that knows the keys can set the
flag on purpose, see the answers of the symbolic game disagree after a corruption, and then spend
more calls than the budget of the real game allows. So `HiddenCoreAt` keeps the flag.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof

namespace SigningCoreProof

variable {C : Committee} (prims : Primitives)

/-! ## The flag of a call on a hidden key -/

open Classical in
/-- A call of the forger names a key that the corrupt operators `D` do not hold. -/
def hiddenHit (x : Keys3 C) (D : Finset C.Party) : (LocalSpec C).Domain → Bool
  | .inr (.inl (.prf s _)) => decide (∃ T, s = x.2.1 T ∧ ¬Revealed D (.inl T))
  | .inr (.inl (.mask k _ _ _)) => decide (∃ p, k = x.2.2 p ∧ ¬Revealed D (.inr p))
  | _ => false

/-- The lift of the honest computations in `tsigGameWith worldRoles`. -/
abbrev honestLift {β : Type} (oa : OracleComp (RoSpec C) β) : OracleComp (WorldSpec C) β :=
  worldRoles.honest (liftComp oa _)

/-- The oracles of `tsigGameWith worldRoles`. -/
def gameOracles (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (TsigState C) (OracleComp (WorldSpec C))) :=
  (fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) :
      QueryImpl (LocalSpec C) (StateT (TsigState C) (OracleComp (WorldSpec C)))) +
    tsigOracles (fun oa => honestLift oa) dealt

/-- The oracles of `tsigGameWith worldRoles` with the flag of `hiddenHit`. -/
def flaggedOracles (x : Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (TsigState C × Bool) (OracleComp (WorldSpec C)))
  | .inl t => StateT.mk fun p => (fun a => (a, (p.1, p.2 || hiddenHit x p.1.corrupt t))) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))
  | .inr q => StateT.mk fun p => (fun z => (z.1, (z.2, p.2))) <$>
      (tsigOracles (fun oa => honestLift oa) dealt q).run p.1

/-- The initial state of the game. -/
def tsigInit : TsigState C := ⟨∅, fun _ => none, [], fun _ => none⟩

/-- The verification and the freshness check of `tsigGameWith worldRoles`, after the forger. -/
def tsigFinish (dealt : Dealt C (OracleComp (WorldSpec C))) :
    Forgery × TsigState C → OracleComp (WorldSpec C) (Bool × TsigState C × Forgery)
  | (forgery, st) => do
    let verified ← honestLift (tweakable (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ forgery.message
      forgery.signature))
    let fresh ← if (signersAt st forgery.signature.leafIndex forgery.message).card < C.t then pure true else do
      let honest ← honestSignature (fun oa => honestLift oa) dealt forgery.signature.leafIndex forgery.message
      pure (decide (honest ≠ some forgery.signature))
    pure (verified && fresh, st, forgery)

theorem tsigGameWith_eq (dealt : Dealt C (OracleComp (WorldSpec C))) (A : TsigAdversary C) :
    tsigGameWith worldRoles dealt A =
      (simulateQ (gameOracles dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run tsigInit >>=
        tsigFinish dealt := by
  unfold tsigGameWith
  refine bind_congr fun p => ?_
  obtain ⟨forgery, st⟩ := p
  simp only [forgeryWins, tsigFinish, bind_assoc, pure_bind]
  refine bind_congr fun verified => ?_
  split <;> simp <;> rfl

/-- A run of the flagged oracles forgets the flag. -/
theorem simulateQ_run_forget {ι : Type} {spec : OracleSpec ι} {σ τ α : Type} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl₁ : QueryImpl spec (StateT (σ × τ) m)) (impl₂ : QueryImpl spec (StateT σ m))
    (h : ∀ t s b, (fun z => (z.1, z.2.1)) <$> (impl₁ t).run (s, b) = (impl₂ t).run s)
    (oa : OracleComp spec α) (s : σ) (b : τ) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ impl₁ oa).run (s, b) = (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s b with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, map_bind]
    rw [← h t s b, bind_map_left]
    exact bind_congr fun z => ih _ _ _

theorem flaggedOracles_forget (x : Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TsigState C) (b : Bool) :
    (fun z => (z.1, z.2.1)) <$> (flaggedOracles x dealt t).run (s, b) = (gameOracles dealt t).run s := by
  rcases t with t | q
  · simp [flaggedOracles, gameOracles]
  · simp [flaggedOracles, gameOracles, Functor.map_map]

/-- The game of `gameAfter` with the flag of `hiddenHit`. -/
def flaggedAfter (A : TsigAdversary C) (x : Keys3 C) : OracleComp (WorldSpec C) (Bool × Bool) := do
  let value := fun p => liftFree (prfValue x.2.1 p)
  let some (.top top) ← referenceTree (fun oa => liftFree (tweakable oa)) value x.1 emptyTop .top
    | pure (false, false)
  let dealt := dealtWith (fun oa => liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (flaggedOracles x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
    (tsigInit, false)
  (fun w => (w.1, r.2.2)) <$> tsigFinish dealt (r.1, r.2.1)

theorem flaggedAfter_forget (A : TsigAdversary C) (x : Keys3 C) :
    (fun w => w.1) <$> flaggedAfter A x = gameAfter A x := by
  unfold flaggedAfter gameAfter
  rw [map_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp
  · simp only [map_bind, Functor.map_map]
    rw [tsigGameWith_eq, map_bind, ← simulateQ_run_forget _ _ (flaggedOracles_forget x _) _ _ false,
      bind_map_left]
  · simp


/-! ## The flagged run -/

theorem runSigningWorld_map {α β : Type} (f : α → β) (oa : OracleComp (WorldSpec C) α) :
    runSigningWorld prims (f <$> oa) = Prod.map f id <$> runSigningWorld prims oa := by
  unfold runSigningWorld
  simp only [simulateQ_map, WriterT.run_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  erw [Functor.map_map]
  rfl

/-- `keyedRun` with the flag of `hiddenHit`. -/
def flaggedRun (A : TsigAdversary C) : ProbComp (Keys3 C × ((Bool × Bool) × ℕ)) :=
  keyGen3 >>= fun x => (fun r => (x, r)) <$> runSigningWorld prims (flaggedAfter A x)

/-- The flag changes nothing else. -/
theorem keyedRun_eq_flaggedRun (A : TsigAdversary C) :
    keyedRun prims A = (fun z => (z.1, (z.2.1.1, z.2.2))) <$> flaggedRun prims A := by
  unfold keyedRun flaggedRun
  rw [map_bind]
  refine bind_congr fun x => ?_
  rw [← flaggedAfter_forget, runSigningWorld_map, Functor.map_map, Functor.map_map]
  rfl

/-- A win with distinct keys sets the flag or wins without it. -/
theorem core_split (A : TsigAdversary C) :
    Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A] ≤
      Pr[fun z => z.2.1.2 = true | flaggedRun prims A] +
        Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true | flaggedRun prims A] := by
  rw [keyedRun_eq_flaggedRun, probEvent_map]
  refine le_trans (probEvent_mono fun z _ h => ?_) (probEvent_or_le _ _ _)
  by_cases hz : z.2.1.2 = true
  · exact Or.inl hz
  · exact Or.inr ⟨h.1, by simpa using hz, h.2⟩

/-! ## The opened randomizer (step 3 of the plan, the first obligation) -/

/-- `bytesLE_injective` of leanVM (`LeanXmss/Bytes.lean`). The package builds only `LeanXmss.Scheme`
and `LeanXmss.Statement`, so the lemma is repeated here. -/
theorem bytesLE_inj {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) : x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_len (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

/-- `c_e` determines its opening: the input of `c_e` determines `ρ`, by the byte layout of leanVM. -/
theorem commitmentInput_injective (P : PublicParameter) (e : KeyIndex) :
    Function.Injective (commitmentInput P e) := by
  intro ρ ρ' h
  unfold commitmentInput at h
  obtain ⟨h, -⟩ := List.append_inj' h (bytesLE_len 16 0 |>.trans (bytesLE_len 16 0).symm)
  obtain ⟨-, h⟩ := List.append_inj' h ((bytesLE_len 16 (ρ : BitVec (8 * 16))).trans
    (bytesLE_len 16 (ρ' : BitVec (8 * 16))).symm)
  exact bytesLE_inj h

/-- The first obligation of step 3 with a fixed `H`. An honest signer that accepts an opened value
`ρ ≠ ρ_e` against the commitment `c_e = Th(P, A_rnd(e, 1), ρ_e ‖ 0)` meets a hit on `c_e`: another
input at the position of `c_e` gives the output `c_e`. -/
theorem opened_randomizer_hit {h : Query C → HashOutput} (P : PublicParameter) (commitment : Digest)
    (e : KeyIndex) (message : Message) (ρ ρe : Digest)
    (hc : commitment = truncateHash (h (.hash (commitmentInput P e ρe)))) (hne : ρ ≠ ρe)
    (hs : D prims h (signCodeword P commitment e message ρ) ≠ none) :
    commitmentInput P e ρ ≠ commitmentInput P e ρe ∧
      truncateHash (h (.hash (commitmentInput P e ρ))) = truncateHash (h (.hash (commitmentInput P e ρe))) := by
  refine ⟨fun heq => hne (commitmentInput_injective P e heq), ?_⟩
  by_contra hne'
  apply hs
  unfold signCodeword
  change E prims h _ = none
  rw [E_bind, E_oracleHash, if_pos (by rw [hc]; exact hne'), E_pure]

/-! ## The stage interfaces -/

/-- Step 1 of the plan, the cost of the hidden keys. A call of the forger on a key that the corrupt
operators do not hold at that time costs `seedHitError`. The proof follows `real_sym_hop` and the
presampling of `Proof/Tprf.lean` for the signing oracles: until the flag, the hidden keys enter the
view only through their slots, so each call names a hidden key with probability at most
`(C(n, t - 1) + n²) / 2^256`. -/
def SeedHitBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q →
    (Pr[fun z => z.2.1.2 = true | flaggedRun prims A]).toReal ≤ seedHitError C q

/-- Steps 2 to 6 of the plan. A win with distinct keys and no call on a hidden key costs
`signingHashError q`: the hop to the slots of the hidden keys (free without the flag), the positions
of the inputs of `Th`, the descent of leanVM over two layers, the two obligations (a `ρ' ≠ ρ_e` that
opens `c_e` is a hit on `c_e`, and the partner of a digest call with `ρ_e` opened in round 1), and the
two lanes of leanVM with the calls of `KeyGen` as the slack. -/
def HiddenCoreBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q → q < 2 ^ 127 →
    (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true | flaggedRun prims A]).toReal ≤
      signingHashError q

/-! ## The core for fixed keys -/

/-- `HiddenCoreBound` for fixed distinct keys. Without a call on a hidden key, the values of the
keys do not matter, only their distinctness, so the bound holds for each key of `KeyGen'` with its
own budget. -/
def HiddenCoreAt (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C), x ∈ support (keyGen3 (C := C)) →
    ¬KeyCollision x.2.1 x.2.2 → (∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true | runSigningWorld prims (flaggedAfter A x)] ≤
      ENNReal.ofReal (signingHashError q)

/-- The core over the keys of `KeyGen'` from the core for each key. -/
theorem hiddenCoreBound_of_at (h : HiddenCoreAt prims C) : HiddenCoreBound prims C := by
  intro A q hq hsmall
  have hε : 0 ≤ signingHashError q := by unfold signingHashError; positivity
  refine ENNReal.toReal_le_of_le_ofReal hε ?_
  unfold flaggedRun
  refine probEvent_bind_le_of_forall_le fun x hx => ?_
  rw [probEvent_map]
  by_cases hc : KeyCollision x.2.1 x.2.2
  · simp [Function.comp_def, hc]
  · simp only [Function.comp_def, hc, not_false_eq_true, true_and]
    exact h A q x hx hc (queryBound_gameAfter prims A q hq x hx) hsmall

end SigningCoreProof

open SigningCoreProof in
/-- `SigningCoreBound` from the two open stages `SeedHitBound` and `HiddenCoreAt`. -/
theorem signingCoreBound (prims : Primitives) (C : Committee) (seedHit : SeedHitBound prims C)
    (hiddenCoreAt : HiddenCoreAt prims C) : SigningCoreBound prims C := by
  intro A q hq hsmall
  have hiddenCore := hiddenCoreBound_of_at prims hiddenCoreAt
  calc (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A]).toReal
      ≤ (Pr[fun z => z.2.1.2 = true | flaggedRun prims A] +
          Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true |
            flaggedRun prims A]).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) (core_split prims A)
    _ = (Pr[fun z => z.2.1.2 = true | flaggedRun prims A]).toReal +
          (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1.2 = false ∧ z.2.1.1 = true |
            flaggedRun prims A]).toReal :=
        ENNReal.toReal_add probEvent_ne_top probEvent_ne_top
    _ ≤ seedHitError C q + signingHashError q := add_le_add (seedHit A q hq) (hiddenCore A q hq hsmall)
    _ = _ := by ring

/-- info: 'ThresholdLeanXmssSecurity.signingCoreBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCoreBound

end ThresholdLeanXmssSecurity
