import ThresholdLeanXmssSecurity.Proof.Signing
import ThresholdLeanXmssSecurity.Proof.Tprf

/-!
# The signing security

`SigningSecurityStatement` (PRAWNS, Definition 3.2, in the random-oracle model), following the plan
of `formal/PROOF.md`.

The component lemmas:

* `KeyGen'` samples first on the free copy, which costs nothing and leaves the cache, so the game is
  an average over the keys (`tsigGame_eq`, `tsigAdvantage_eq`), and the budget holds for each key
  (`queryBound_gameAfter`).
* Two equal seeds or two equal pair keys cost `seedCollisionError` (`keyCollision_toReal_le`, from
  `probEvent_keyCollision` of the threshold PRF proof).
* For `q ≥ 2 ^ 127` the bound is at least `1` (`signingSecurity_large`).

The core interface: `SigningCoreBound`, a win with distinct keys and `q < 2 ^ 127`. It is steps 1 to 6 of
`formal/PROOF.md` without the collision of the keys.

1. The hop to slots of the hidden keys, as `real_sym_hop` of the threshold PRF proof, for the
   oracles of `tsigOracles`, at `seedHitError`.
2. The positions of the inputs of `Th` and the descent of leanVM over two layers.
3. The two proof obligations of `formal/PROOF.md`: a `ρ' ≠ ρ_e` that opens `c_e` is a hit on
   `c_e`, and the partner bound of a digest call when round 1 opens `ρ_e` before the search.
4. The two lanes of leanVM, two units for each call, with the calls of `KeyGen` as the slack.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof

namespace SigningSecurityProof

variable {C : Committee} (prims : Primitives)

/-! ## The free sample of `KeyGen'` in the signing world -/

theorem signingWorld_inr_inl (t : unifSpec.Domain) (s : HashCache C) :
    (simulateQ (signingWorld prims) (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _)).run.run s =
      (fun a => ((a, 1), s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
  rw [simulateQ_query]
  simp [signingWorld, signingLocalAnswer, unifFwdImpl]

theorem signingWorld_free_liftComp {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (signingWorld prims) (free (C := C) (liftComp p (LocalSpec C)))).run.run s =
      (fun a => ((a, 1), s)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa ih =>
    rw [liftComp_bind, free_bind, simulateQ_bind, free_liftComp_query]
    simp only [WriterT.run_bind, StateT.run_bind]
    erw [signingWorld_inr_inl]
    simp only [bind_map_left, one_mul]
    rw [map_bind]
    congr 1; funext a
    rw [StateT.run_map, ih]
    simp

theorem runSigningWorld_free_bind {α β : Type} (p : ProbComp α) (k : α → OracleComp (WorldSpec C) β) :
    runSigningWorld prims (free (liftComp p (LocalSpec C)) >>= k) = p >>= fun a => runSigningWorld prims (k a) := by
  unfold runSigningWorld
  rw [simulateQ_bind, WriterT.run_bind, StateT.run'_eq, StateT.run_bind, signingWorld_free_liftComp]
  simp only [bind_map_left, map_bind, one_mul, StateT.run'_eq]
  refine bind_congr fun a => ?_
  simp only [StateT.run_map, Functor.map_map]

/-! ## The game after `KeyGen'` -/

/-- The keys of `KeyGen'`, namely the parameter, the seeds and the pair keys. -/
abbrev Keys3 (C : Committee) := PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)

/-- The lift of the honest computations to the free copy. -/
abbrev liftFree {β : Type} (oa : OracleComp (RoSpec C) β) : OracleComp (WorldSpec C) β := free (liftComp oa _)

/-- The game of PRAWNS, Figure 3, after `KeyGen'` gave the keys `x`. -/
def gameAfter (A : TsigAdversary C) (x : Keys3 C) : OracleComp (WorldSpec C) Bool := do
  let value := fun p => liftFree (prfValue x.2.1 p)
  let some (.top top) ← referenceTree (fun oa => liftFree (tweakable oa)) value x.1 emptyTop .top | pure false
  (·.1) <$> tsigGameWith worldRoles (dealtWith (fun oa => liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value) A

theorem free_liftComp_map {α β : Type} (f : α → β) (p : ProbComp α) :
    free (C := C) (liftComp (f <$> p) (LocalSpec C)) = f <$> free (liftComp p (LocalSpec C)) := by
  rw [liftComp_map]
  exact simulateQ_map _ _ _

theorem prawnsKeyGen_eq :
    prawnsKeyGen (C := C) = (fun x : Keys3 C => (x.1, x.2.1, dealtKeys x.1 x.2.1 x.2.2)) <$> keyGen3 := by
  simp [prawnsKeyGen, keyGen3]

/-- The game samples the keys first. -/
theorem tsigGame_eq (A : TsigAdversary C) :
    tsigGame A = free (liftComp keyGen3 (LocalSpec C)) >>= gameAfter A := by
  unfold tsigGame dealerKeyGen dealerKeyGenWith
  rw [prawnsKeyGen_eq]
  dsimp only
  rw [free_liftComp_map, bind_map_left, bind_assoc]
  refine bind_congr fun x => ?_
  unfold gameAfter
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · rfl
  · rw [pure_bind]
  · rfl

/-- A run of the game, with its keys. -/
def keyedRun (A : TsigAdversary C) : ProbComp (Keys3 C × (Bool × ℕ)) :=
  keyGen3 >>= fun x => (fun r => (x, r)) <$> runSigningWorld prims (gameAfter A x)

theorem tsigAdvantage_eq (A : TsigAdversary C) :
    tsigAdvantage prims A = (Pr[fun z => z.2.1 = true | keyedRun prims A]).toReal := by
  unfold tsigAdvantage signingAccepts
  rw [tsigGame_eq]
  rw [runSigningWorld_free_bind]
  unfold keyedRun
  refine congrArg ENNReal.toReal ?_
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  rw [probEvent_map]
  simp only [Function.comp_def]

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The budget of the game bounds the run after each key of `KeyGen'`. -/
theorem queryBound_gameAfter (A : TsigAdversary C) (q : ℕ) (hq : HasSigningQueryBound prims (tsigGame A) q) :
    ∀ x ∈ support (keyGen3 (C := C)), ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q := by
  intro x hx r hr
  refine hq r ?_
  rw [tsigGame_eq, runSigningWorld_free_bind, support_bind]
  exact Set.mem_iUnion₂.mpr ⟨x, hx, hr⟩

/-! ## Collisions of the keys -/

/-- A win either has a collision of the keys or wins with distinct keys. -/
theorem probEvent_win_split (A : TsigAdversary C) :
    Pr[fun z => z.2.1 = true | keyedRun prims A] ≤
      Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3] +
        Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A] := by
  classical
  calc Pr[fun z => z.2.1 = true | keyedRun prims A]
      ≤ Pr[fun z => KeyCollision z.1.2.1 z.1.2.2 ∨ (¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true) |
          keyedRun prims A] :=
        probEvent_mono fun z _ h => by
          by_cases hc : KeyCollision z.1.2.1 z.1.2.2
          · exact Or.inl hc
          · exact Or.inr ⟨hc, h⟩
    _ ≤ Pr[fun z => KeyCollision z.1.2.1 z.1.2.2 | keyedRun prims A] +
          Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A] :=
        probEvent_or_le _ _ _
    _ ≤ _ := by
        refine add_le_add ?_ le_rfl
        refine probEvent_bind_le_of_ite _ _ (fun x : Keys3 C => KeyCollision x.2.1 x.2.2) _ fun x hx => ?_
        rw [probEvent_map]
        simp [Function.comp_def, hx]

theorem collisionCount_le (C : Committee) :
    (C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2 ≤ (C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 := by
  set T := C.n.choose (C.t - 1)
  set P := C.n.choose 2
  have hP : P ≤ C.n ^ 2 := choose_two_le_sq _
  have hT2 : T.choose 2 ≤ T ^ 2 := choose_two_le_sq T
  have hP2 : P.choose 2 ≤ P ^ 2 := choose_two_le_sq P
  have hPP : P ^ 2 ≤ (C.n ^ 2) ^ 2 := Nat.pow_le_pow_left hP 2
  have hsq : (T + C.n ^ 2) ^ 2 = T ^ 2 + 2 * T * C.n ^ 2 + (C.n ^ 2) ^ 2 := by ring
  omega

/-- Two equal seeds or two equal pair keys cost `seedCollisionError`. -/
theorem keyCollision_toReal_le :
    (Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3]).toReal ≤ seedCollisionError C := by
  have h := probEvent_keyCollision (C := C)
  have h' : Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3] ≤
      (((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [ENNReal.div_eq_inv_mul, mul_comm]
    exact h
  refine (toReal_le_div h').trans ?_
  unfold seedCollisionError
  exact div_le_div_of_nonneg_right (by exact_mod_cast collisionCount_le C) (by positivity)

/-! ## The stage interface -/

/-- Steps 1 to 6 of `formal/PROOF.md` for distinct keys and `q < 2 ^ 127`. A win with distinct keys
costs `q / 2 ^ 127` for the hits, the guesses and the partners, and `seedHitError` for a call on a
hidden key. -/
def SigningCoreBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ), HasSigningQueryBound prims (tsigGame A) q → q < 2 ^ 127 →
    (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A]).toReal ≤
      signingHashError q + seedHitError C q

/-- For `q ≥ 2 ^ 127` the bound is at least `1`. -/
theorem signingSecurity_large (A : TsigAdversary C) (q : ℕ) (hq : 2 ^ 127 ≤ q) :
    tsigAdvantage prims A ≤ signingHashError q + seedHitError C q + seedCollisionError C := by
  have hhit : 0 ≤ seedHitError C q := by unfold seedHitError; positivity
  have hcoll : 0 ≤ seedCollisionError C := by unfold seedCollisionError; positivity
  have h1 : tsigAdvantage prims A ≤ 1 := by
    unfold tsigAdvantage signingAccepts
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact probEvent_le_one)
  have h2 : (1 : ℝ) ≤ signingHashError q := by
    unfold signingHashError
    rw [le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast hq
  linarith

end SigningSecurityProof

open SigningSecurityProof in
/-- `SigningSecurityStatement` from the remaining stage `SigningCoreBound`. -/
theorem signingSecurityProof (prims : Primitives) (C : Committee) (core : SigningCoreBound prims C) :
    SigningSecurityStatement prims C := by
  intro A q hq
  by_cases hlarge : 2 ^ 127 ≤ q
  · exact signingSecurity_large prims A q hlarge
  · have hsmall : q < 2 ^ 127 := Nat.lt_of_not_le hlarge
    rw [tsigAdvantage_eq]
    have hs := probEvent_win_split prims A
    calc (Pr[fun z => z.2.1 = true | keyedRun prims A]).toReal
        ≤ (Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3] +
            Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A]).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hs
      _ = (Pr[fun x : Keys3 C => KeyCollision x.2.1 x.2.2 | keyGen3]).toReal +
            (Pr[fun z => ¬KeyCollision z.1.2.1 z.1.2.2 ∧ z.2.1 = true | keyedRun prims A]).toReal :=
          ENNReal.toReal_add probEvent_ne_top probEvent_ne_top
      _ ≤ seedCollisionError C + (signingHashError q + seedHitError C q) :=
          add_le_add keyCollision_toReal_le (core A q hq hsmall)
      _ = _ := by ring


/-- info: 'ThresholdLeanXmssSecurity.signingSecurityProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingSecurityProof

end ThresholdLeanXmssSecurity
