import ThresholdLeanXmss.Statement

/-!
# Threshold leanXMSS, the steps of the proofs

The intermediate statements that the cited proofs use, each named after its source. The proofs of
the claims in `ThresholdLeanXmss/Statement.lean` combine them as follows.

* Theorem 2 follows GS20, Theorem 2. Its steps are the reduction to `t - 1` corruptions (GS20,
  Theorem 1), the `PRG` hop (CDI05), the additive attack of a reshare (GS20, Lemma 4) under the
  consistency of the digests (CGH+18, Protocol 3.3), the coin (GS20, Lemma 3), the check (GS20,
  Lemmas 8 to 11), and the robust openings (GS20, Protocol 6, and MPClan, Appendix B).
* Theorem 4 follows PRAWNS, Theorem 3.1, with Theorem 5.1 and Lemma 5.2 for the threshold PRF.
* Theorem 5 replaces the dealer by the simulator of Theorem 2.
-/

open OracleComp OracleSpec LeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Uniform sampling of the check field. -/
@[reducible] def sampleableField : SampleableType E := SampleableType.ofFintype E

attribute [local instance] sampleableField

/-! ## Terms and quorums -/

/-- A quorum holds every term (PRAWNS, Section 5, first key fact). -/
theorem prawns_quorum_holds_term (J : C.Quorum) (T : C.Term) : ∃ i ∈ J.1, i ∈ C.holders T := by
  sorry

/-- Each term goes to exactly one signer of the quorum, so the parts combine (PRAWNS, Section 5). -/
theorem prawns_L_partition (J : C.Quorum) (T : C.Term) : ∃! i, T ∈ L J i := by
  sorry

/-- A coalition lacks a term (PRAWNS, Section 5, second key fact, and CDI05, Section 3). -/
theorem prawns_coalition_lacks_term (D : C.Coalition) : ∃ T : C.Term, ∀ j ∈ D.1, j ∉ C.holders T := by
  sorry

/-- Two terms have a common holder, so `pairs_i` exists (CDI05, Section 4, with `2t - 2 < n`). -/
theorem cdi05_pair_has_holder (A B : C.Term) : ∃ i, i ∈ C.holders A ∧ i ∈ C.holders B := by
  sorry

/-- The owner of a term is honest, or another holder is honest (MPClan, Appendix B). -/
theorem mpclan_honest_holder (K : Constants C E) (D : C.Coalition) (T : C.Term) :
    K.owner T ∉ D.1 ∨ ∃ h, h ∈ C.holders T ∧ h ∉ D.1 ∧ h ≠ K.owner T := by
  sorry

/-! ## Sharings -/

/-- The context of operator `i` for the local gadgets, which read only `self`. -/
def localContext (i : C.Party) : Context C := ⟨i, ⟨0, fun _ => 0, fun _ => 0⟩, 0⟩

/-- `Conv` of a replicated sharing is a Shamir sharing of degree `t - 1` of the same value (CDI05,
Section 4). -/
theorem cdi05_conv_correct [CharP E 2] (K : Constants C E) (x : C.Term → E) :
    ∃ V : Polynomial E, V.natDegree ≤ C.t - 1 ∧ V.eval 0 = ∑ T, x T ∧
      ∀ i, conv K (localContext i) (fun T _ => x T) 0 = V.eval (K.point i) := by
  sorry

/-- The shares of `MulRep` sum to the product (CDI05, Section 4). -/
theorem cdi05_mulRep_correct {R : Type} [CommRing R] (K : Constants C E) (x y : C.Term → R) :
    ∑ i, mulRep K (localContext i) (fun T _ => x T) (fun T _ => y T) 0 = (∑ T, x T) * ∑ T, y T := by
  sorry

/-- The shares of `MulSh` sum to the inner product, since the product of two polynomials of degree
`t - 1` has degree `n - 1` (GS20, Section 3.2). -/
theorem gs20_mulSh_correct [CharP E 2] (K : Constants C E) (count : ℕ) (X Y : ℕ → Polynomial E)
    (hX : ∀ g, (X g).natDegree ≤ C.t - 1) (hY : ∀ g, (Y g).natDegree ≤ C.t - 1) :
    ∑ i, mulSh K (localContext i) (fun g => (X g).eval (K.point i)) (fun g => (Y g).eval (K.point i)) count =
      ∑ g ∈ range count, (X g).eval 0 * (Y g).eval 0 := by
  sorry

/-- The `t` honest shares fix the polynomial, so an accepted opening is its value at `0` (GS20,
Protocol 6, step 2). -/
theorem gs20_openSh_robust (K : Constants C E) (D : C.Coalition) (V : Polynomial E)
    (hV : V.natDegree ≤ C.t - 1) (share : C.Party → E) (honest : ∀ j ∉ D.1, share j = V.eval (K.point j))
    (accepted : ∀ j, share j =
      ∑ l ∈ univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K (K.point j) l * share l) :
    ∑ l ∈ univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * share l = V.eval 0 := by
  sorry

/-- The parts of a quorum combine to `F(x)` for every fixed `H`, since each mask appears twice. This
is the correctness of PRAWNS, Definition 2.1, for the single pair key of `doc/sign.md`. -/
theorem prawns_combine_correct (keccak : HashInput → HashOutput) (seeds : C.Term → HashOutput)
    (pairKey : C.Pair → HashOutput) (parameter : PublicParameter) (J : C.Quorum) (x : HashInput)
    (m : Message) :
    let keys := fun i : C.Party => (⟨parameter, fun T => if i ∈ C.holders T then seeds T else 0,
      fun j => if h : j = i then 0 else pairKey (C.pairOf i j (Ne.symm h))⟩ : Keys C)
    simulateQ (fixedHash keccak) (do
        let parts ← Concrete.sequenceFin fun i => eval (keys i) i J x m
        pure (combine J parts)) =
      simulateQ (fixedHash keccak) (prfValue seeds x) := by
  sorry

/-! ## Reshare -/

/-- `u_i` of a peer reshare. -/
def peerMessage (K : Constants C E) (v ζ : C.Party → E) (r : C.Term → E) (i : C.Party) : E :=
  v i + ζ i + ∑ U ∈ univ.filter (fun U => U ∉ filledTerms K ∧ K.owner U = i), r U

/-- The terms after a peer reshare when each corrupt `j` gives the other holders of `T_j` the value
`sent j` in place of `u_j`. -/
def peerTerms (K : Constants C E) (D : C.Coalition) (v ζ : C.Party → E) (r : C.Term → E)
    (sent : C.Party → E) : C.Term → E := fun T =>
  if T ∈ filledTerms K then
    ∑ j ∈ univ.filter (K.filled · = T), if j ∈ D.1 then sent j else peerMessage K v ζ r j
  else r T

/-- A peer reshare is secure up to an additive attack (GS20, Lemma 4 and Functionality 7, and
GIP+14). If every honest holder of each filled term receives one value, the honest terms share
`∑ v + δ`, and `δ` depends only on the messages and the view of the corrupt operators. -/
theorem gs20_lemma4_additive_attack [CharP E 2] (K : Constants C E) (D : C.Coalition)
    (v ζ : C.Party → E) (hζ : ∑ i, ζ i = 0) (r : C.Term → E) (sent : C.Party → E) :
    ∑ T, peerTerms K D v ζ r sent T = ∑ i, v i + ∑ j ∈ D.1, (sent j - peerMessage K v ζ r j) := by
  sorry

/-- The peer reshare is private (`doc/dkg.md` 1.6). With uniform masks of the unfilled terms and of
the pairs, the view of the coalition, which is its masks and the messages it receives, has one
distribution for all honest inputs. -/
theorem dkg_reshare_privacy [CharP E 2] (K : Constants C E) (D : C.Coalition) (v v' : C.Party → E)
    (hv : ∀ j ∈ D.1, v j = v' j) :
    let view := fun (w : C.Party → E) (masks : (C.Term → E) × (C.Pair → E)) =>
      let ζ := fun i => ∑ j ∈ univ.erase i, if h : i = j then 0 else masks.2 (C.pairOf i j h)
      let u := fun i => w i + ζ i +
        ∑ U ∈ univ.filter (fun U => U ∉ filledTerms K ∧ K.owner U = i), masks.1 U
      (fun i => if i ∉ D.1 ∧ ∃ j ∈ D.1, j ∈ C.holders (K.filled i) then u i else 0,
       fun T => if ∃ j ∈ D.1, j ∈ C.holders T then masks.1 T else 0,
       fun p : C.Pair => if p.1.1 ∈ D.1 ∨ p.1.2 ∈ D.1 then masks.2 p else 0)
    𝒟[view v <$> ($ᵗ ((C.Term → E) × (C.Pair → E)))] = 𝒟[view v' <$> ($ᵗ ((C.Term → E) × (C.Pair → E)))] := by
  sorry

/-- In collector mode (`doc/dkg.md` 1.6), for one gate, the messages that a corrupt collector
receives and the masks of the coalition have one distribution for all honest inputs, because the
honest pair masks hide each `u_i` and the lacked term hides their sum. -/
theorem dkg_collector_privacy [CharP E 2] (K : Constants C E) (D : C.Coalition) (g : ℕ)
    (v v' : C.Party → E) (hv : ∀ j ∈ D.1, v j = v' j) :
    let view := fun (w : C.Party → E) (masks : (C.Term → E) × (C.Pair → E)) =>
      let ζ := fun i => ∑ j ∈ univ.erase i, if h : i = j then 0 else masks.2 (C.pairOf i j h)
      let u := fun i => w i + ζ i +
        ∑ U ∈ univ.filter (fun U => U ≠ (K.collector g).1 ∧ K.owner U = i), masks.1 U
      (fun i => if i ∉ D.1 ∧ (K.collector g).2 ∈ D.1 then u i else 0,
       if (K.collector g).2 ∉ D.1 ∧ ∃ j ∈ D.1, j ∈ C.holders (K.collector g).1 then ∑ i, u i else 0,
       fun T => if ∃ j ∈ D.1, j ∈ C.holders T then masks.1 T else 0,
       fun p : C.Pair => if p.1.1 ∈ D.1 ∨ p.1.2 ∈ D.1 then masks.2 p else 0)
    𝒟[view v <$> ($ᵗ ((C.Term → E) × (C.Pair → E)))] = 𝒟[view v' <$> ($ᵗ ((C.Term → E) × (C.Pair → E)))] := by
  sorry

/-! ## Consistency, coins and openings -/

/-- If two holders of a term send different digests, every operator, holder or not, aborts at the
comparison (CGH+18, Protocol 3.3, and MPClan, `Π_agree`). This is the split-term fix of `doc/dkg.md`
1.9. -/
theorem cgh18_digests_abort_everywhere (K : Constants C E) (ctx : Context C)
    (payloads : C.Party → Option (Msg E)) (T : C.Term) (h h' : C.Party) (hh : h ∈ C.holders T)
    (hh' : h' ∈ C.holders T)
    (hne : Msg.part (payloads h) (C.terms.idxOf T) ≠ Msg.part (payloads h') (C.terms.idxOf T)) :
    (compareDigests (E := E) payloads : PartyM C E Unit) = failure := by
  sorry

/-- The value of a coin is uniform and independent of the terms that the coalition holds, because
the lacked term is uniform after the `PRG` hop (GS20, Lemma 3 with CDI05). -/
theorem gs20_lemma3_coin_uniform (D : C.Coalition) (held : C.Term → E) :
    𝒟[(fun r : C.Term → E => (∑ T, r T, fun T => if ∃ j ∈ D.1, j ∈ C.holders T then r T else 0)) <$>
        ($ᵗ (C.Term → E))] =
      𝒟[(fun (c : E) (r : C.Term → E) => (c, fun T => if ∃ j ∈ D.1, j ∈ C.holders T then r T else 0)) <$>
        ($ᵗ E) <*> ($ᵗ (C.Term → E))] := by
  sorry

/-! ## The check, as values

`check` on the values it shares. The adversary adds an error to each reshared
value, and each error depends on the coins and the challenges before it (GS20, Lemma 11). -/

/-- The errors of a rushing adversary. For step `j` (the final step is `m`), they are the errors of
the two reshared values from the weight coins and the earlier challenges. -/
abbrev CheckErrors (E : Type) (d : ℕ) := ℕ → (Fin d → E) → List E → E × E

/-- The challenges outside `{0, 1}`. -/
abbrev Challenge (E : Type) [Field E] := {r : E // r ≠ 0 ∧ r ≠ 1}

/-- The value-level check of `count` tuples, with weights, slice steps, halving steps and a final
step. The coin `τ` gives the weights, the challenges `r` fold the vectors, and `mask` is
`(a^(0), b^(0))`. -/
def CheckAccepts (K : Constants C E) (count : ℕ) (x y z : ℕ → Bit) (errors : CheckErrors E (coins count))
    (mask : E × E) (τ : Fin (coins count) → E) (r : Fin (halvings count + 1) → Challenge E) : Prop :=
  let m := halvings count
  let d := coins count
  let s := sliceBits
  let coin := List.ofFn τ
  let lift := fun b : Bit => algebraMap Bit E b
  let wordWeight := fun k => coinProduct coin s (d - s) (wordOf m k) * K.weight (bitOf k)
  let challenge := fun j => (r ⟨j % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩).1
  let earlier := fun j => (List.range j).map challenge
  let claim₀ := ∑ k ∈ range (2 ^ m), coinProduct coin 0 s (sliceOf m k) * wordWeight k * lift (z k)
  let slices := (List.range s).foldl (init := ((fun k => wordWeight k * lift (x k)), fun k => lift (y k), claim₀))
    fun (xs, ys, D) j =>
      let half := 2 ^ (m - j - 1)
      let rest := fun k => ∏ b ∈ range (s - 1 - j), if k.testBit (m - s + b) then coin.getD b 0 else 1
      let t0 := ∑ k ∈ range half, rest k * xs k * ys k + (errors j τ (earlier j)).1
      let tInf := ∑ k ∈ range half, rest k * (xs k + xs (k + half)) * (ys k + ys (k + half)) +
        (errors j τ (earlier j)).2
      let c := coin.getD (s - 1 - j) 0
      let ρ := challenge j
      let fold := fun (v : ℕ → E) k => v k + ρ * (v k + v (k + half))
      (fold xs, fold ys, (1 + ρ) * t0 + ρ * ((D + t0) / c) + ρ * (1 + ρ) * tInf)
  let halved := (List.range (m - s)).foldl (init := slices) fun (A, B, D) j =>
      let half := 2 ^ (m - s - j - 1)
      let c1 := ∑ k ∈ range half, A k * B k + (errors (s + j) τ (earlier (s + j))).1
      let p2 := ∑ k ∈ range half, (A k + A (k + half)) * (B k + B (k + half)) +
        (errors (s + j) τ (earlier (s + j))).2
      let ρ := challenge (s + j)
      let fold := fun (v : ℕ → E) k => v k + ρ * (v k + v (k + half))
      (fold A, fold B, c1 + (D + p2) * ρ + p2 * ρ ^ 2)
  let (A, B, D) := halved
  let (a0, b0) := mask
  let c0 := a0 * b0 + (errors m τ (earlier m)).1
  let q2 := (a0 + A 0) * (b0 + B 0) + (errors m τ (earlier m)).2
  let ρ := challenge m
  (∀ b < s, coin.getD b 0 ≠ 0) ∧
    (a0 + ρ * (a0 + A 0)) * (b0 + ρ * (b0 + B 0)) = c0 + (D + c0 + q2) * ρ + q2 * ρ ^ 2

/-- A halving step keeps a wrong claim wrong for all but two challenges (GS20, Protocol 14 and Lemma
9 with `k = 2`). -/
theorem gs20_lemma9_halving_step [CharP E 2] (lo hi lo' hi' : List E) (claim e0 e2 : E)
    (hwrong : claim ≠ (List.zipWith (· * ·) lo lo').sum + (List.zipWith (· * ·) hi hi').sum)
    (hlen : lo.length = hi.length ∧ lo'.length = hi'.length ∧ lo.length = lo'.length) :
    (univ.filter fun ρ : E =>
      (List.zipWith (· * ·) lo lo').sum + e0 +
          (claim + (List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum + e2) * ρ +
          ((List.zipWith (· * ·) (List.zipWith (· + ·) lo hi) (List.zipWith (· + ·) lo' hi')).sum + e2) * ρ ^ 2 =
        (List.zipWith (· * ·) (List.zipWith (fun a b => a + ρ * (a + b)) lo hi)
          (List.zipWith (fun a b => a + ρ * (a + b)) lo' hi')).sum).card ≤ 2 := by
  sorry

/-- A slice step with a nonzero coin `c` keeps a wrong claim `D ≠ t(0) + c t(1)` wrong for all but
two challenges (Gruen, Section 3, with the slice steps of `doc/dkg.md` 3.3). -/
theorem gruen_slice_step [CharP E 2] (t0 t1 tInf D e0 eInf c : E) (hc : c ≠ 0) (hwrong : D ≠ t0 + c * t1) :
    (univ.filter fun ρ : E =>
      (1 + ρ) * (t0 + e0) + ρ * ((D + (t0 + e0)) / c) + ρ * (1 + ρ) * (tInf + eInf) =
        (1 + ρ) * t0 + ρ * t1 + ρ * (1 + ρ) * tInf).card ≤ 2 := by
  sorry

/-- The final step accepts a wrong claim `D ≠ a b` for at most two challenges (GS20, Protocol 15 and
Lemma 10). -/
theorem gs20_lemma10_final_step [CharP E 2] (a b a0 b0 D e0 e2 : E) (hwrong : D ≠ a * b) :
    (univ.filter fun ρ : E =>
      (a0 + ρ * (a0 + a)) * (b0 + ρ * (b0 + b)) =
        (a0 * b0 + e0) + (D + (a0 * b0 + e0) + ((a0 + a) * (b0 + b) + e2)) * ρ +
          ((a0 + a) * (b0 + b) + e2) * ρ ^ 2).card ≤ 2 := by
  sorry

/-- With a uniform mask and `ρ ≠ 1`, the opened `a^(0) + ρ (a^(0) + a)` is uniform, so it hides `a`
(GS20, Lemma 11, Hybrid 2). -/
theorem gs20_lemma11_final_hides [CharP E 2] (a a' ρ : E) (hρ : ρ ≠ 1) :
    𝒟[(fun a0 : E => a0 + ρ * (a0 + a)) <$> ($ᵗ E)] = 𝒟[(fun a0 : E => a0 + ρ * (a0 + a')) <$> ($ᵗ E)] := by
  sorry

/-- The weighted sum of the errors of the tuples vanishes for at most a `d / |E|` fraction of the
coins, because the weights `x^q` are independent over `F_2` and the tuple errors are bits (GS20,
Lemma 8, with the fixed weights `x^q` of `doc/dkg.md` 3.3). -/
theorem gs20_lemma8_weights (K : Constants C E) (count : ℕ) (x y z : ℕ → Bit)
    (hwrong : ∃ k < 2 ^ halvings count, z k ≠ x k * y k) :
    Pr[fun τ : Fin (coins count) → E =>
        ∑ k ∈ range (2 ^ halvings count),
          coinProduct (List.ofFn τ) 0 sliceBits (sliceOf (halvings count) k) *
            coinProduct (List.ofFn τ) sliceBits (coins count - sliceBits) (wordOf (halvings count) k) *
            K.weight (bitOf k) * algebraMap Bit E (z k - x k * y k) = 0 |
        $ᵗ (Fin (coins count) → E)] ≤
      (coins count : ℝ≥0∞) / Fintype.card E := by
  sorry

/-- The slice step's values from the table of the points of `{0, 1, ∞}^j` equal the inner products
of the folded vectors, term by term (Bagad, Dao, Domb and Thaler, Section 4). So the
implementation's table computes the shares of `check`. -/
theorem bddt_small_value_equivalence {R : Type} [CommRing R] [CharP R 2] (j : ℕ) (x y : ℕ → R) (ρ : Fin j → R) :
    let basis := fun (v : Fin 3) (r : R) => match v with | 0 => 1 + r | 1 => r | 2 => r * (1 + r)
    let entry := fun (v : ℕ → R) (z : Fin j → Fin 3) (k : ℕ) =>
      ∑ h ∈ (univ : Finset (Fin j → Fin 2)), (if ∀ b, (z b).val = 2 ∨ (z b).val = (h b).val then 1 else 0) *
        v (∑ b : Fin j, (h b).val * 2 ^ b.val + 2 ^ j * k)
    let fold := fun (v : ℕ → R) k => ∑ h ∈ (univ : Finset (Fin j → Fin 2)),
      (∏ b : Fin j, if (h b).val = 0 then 1 + ρ b else ρ b) * v (∑ b : Fin j, (h b).val * 2 ^ b.val + 2 ^ j * k)
    ∀ k, (∑ z : Fin j → Fin 3, (∏ b, basis (z b) (ρ b)) * entry x z k * entry y z k) = fold x k * fold y k := by
  sorry

/-- The check rejects wrong tuples except with probability `(d + 2 (m + 1)) / (|E| - 2)`, for every
rushing error and every mask (GS20, Lemmas 8 to 10, as Lemma 11 uses them). -/
theorem gs20_check_sound [CharP E 2] (K : Constants C E) (count : ℕ) (x y z : ℕ → Bit)
    (hwrong : ∃ k < count, z k ≠ x k * y k) (errors : CheckErrors E (coins count)) (mask : E × E)
    [Nonempty (Challenge E)] :
    letI := SampleableType.ofFintype (Challenge E)
    Pr[fun c => CheckAccepts K count x y z errors mask c.1 c.2 |
        do let τ ← $ᵗ (Fin (coins count) → E); let r ← $ᵗ (Fin (halvings count + 1) → Challenge E)
           pure (τ, r)] ≤
      ((coins count + 2 * (halvings count + 1) : ℕ) : ℝ≥0∞) / (Fintype.card E - 2 : ℕ) := by
  sorry

/-- The check accepts correct tuples with no errors, unless a slice coin is zero. -/
theorem gs20_check_complete [CharP E 2] (K : Constants C E) (count : ℕ) (x y : ℕ → Bit) (mask : E × E)
    (τ : Fin (coins count) → E) (r : Fin (halvings count + 1) → Challenge E)
    (hτ : ∀ b < sliceBits, (List.ofFn τ).getD b 0 ≠ 0) :
    CheckAccepts K count x y (fun k => x k * y k) (fun _ _ _ => (0, 0)) mask τ r := by
  sorry

/-! ## Threshold PRF -/

/-- The oracles of PRAWNS, Figure 1, with the quorum as input (PRAWNS, Section 4). -/
inductive TprfQuery (C : Committee)
  | corrupt (i : C.Party)
  | eval (i : C.Party) (J : C.Quorum) (x : HashInput) (ec : Message)
  | challenge (x : HashInput)

def TprfSpec (C : Committee) : OracleSpec (TprfQuery C)
  | .corrupt _ => Option (Keys C)
  | .eval .. => Option Digest
  | .challenge _ => Option Digest

structure TprfState (C : Committee) where
  corrupt : Finset C.Party
  queried : List (HashInput × Message × C.Party)
  challenged : List HashInput
  random : List (HashInput × Digest)

/-- The game `G^tprf(b)` of PRAWNS, Figure 1, for the threshold PRF of `doc/sign.md`. -/
def tprfGame (b : Bool) (A : OracleComp (LocalSpec C + TprfSpec C) Bool) : OracleComp (LocalSpec C) Bool := do
  let (_, seeds, keys) ← liftComp prawnsKeyGen _
  let exposed := fun (st : TprfState C) x =>
    ∃ ec : Message, C.t ≤ (st.corrupt ∪ ((st.queried.filter fun q => q.1 = x ∧ q.2.1 = ec).map (·.2.2)).toFinset).card
  let impl : QueryImpl (TprfSpec C) (StateT (TprfState C) (OracleComp (LocalSpec C))) := fun q =>
    match q with
    | .corrupt i => do
        let st ← get
        if (∃ x ∈ st.challenged, ∃ ec : Message, C.t ≤ (insert i (st.corrupt ∪
            ((st.queried.filter fun q => q.1 = x ∧ q.2.1 = ec).map (·.2.2)).toFinset)).card) ∨
          C.t - 1 < (insert i st.corrupt).card then pure none
        else do set { st with corrupt := insert i st.corrupt }; pure (some (keys i))
    | .eval i J x ec => do
        let st ← get
        if i ∉ J.1 ∨ (x ∈ st.challenged ∧ C.t ≤ (insert i (st.corrupt ∪
            ((st.queried.filter fun q => q.1 = x ∧ q.2.1 = ec).map (·.2.2)).toFinset)).card) then pure none
        else do
          set { st with queried := st.queried ++ [(x, ec, i)] }
          some <$> liftM (eval (keys i) i J x ec : OracleComp (LocalSpec C) Digest)
    | .challenge x => do
        let st ← get
        if exposed st x then pure none else do
        let value ← if !b then liftM (prfValue seeds x : OracleComp (LocalSpec C) Digest) else
          match st.random.find? (·.1 = x) with
          | some (_, y) => pure y
          | none => liftM (liftComp ($ᵗ Digest) (LocalSpec C))
        set { st with challenged := st.challenged ++ [x], random := st.random ++ [(x, value)] }
        pure (some value)
  (simulateQ (QueryImpl.ofLift (LocalSpec C) (StateT (TprfState C) (OracleComp (LocalSpec C))) + impl) A).run'
    ⟨∅, [], [], []⟩

/-- The threshold PRF is adaptively secure with advantage `2 · C(n, t - 1) · q / 2 ^ 256`, with the
PRF advantage `q / 2 ^ 256` of `H16(k ‖ ·)` (PRAWNS, Theorem 5.1 and Lemma 5.2, in the random-oracle
model, for the single pair key of `doc/sign.md`). -/
theorem prawns_thm51_tprf (keccak : HashInput → HashOutput) (aes : Aes)
    (A : OracleComp (LocalSpec C + TprfSpec C) Bool) (q : ℕ)
    (hq : ∀ b, ∀ r ∈ support (runWorld keccak aes (tprfGame b A)), r.2 ≤ q) :
    |(Pr[fun r => r.1 = true | runWorld keccak aes (tprfGame true A)]).toReal -
      (Pr[fun r => r.1 = true | runWorld keccak aes (tprfGame false A)]).toReal| ≤
      2 * C.n.choose (C.t - 1) * q / 2 ^ 256 := by
  sorry

/-- A uniform guess of the `t - 1` corrupt operators is right with probability `1 / C(n, t - 1)`,
independently of the game (PRAWNS, Lemma 5.2). -/
theorem prawns_lemma52_guess (game : ProbComp (Bool × C.Term)) [Nonempty C.Term] :
    letI := SampleableType.ofFintype C.Term
    Pr[fun r => r.1.1 = true ∧ r.2 = r.1.2 | do let g ← game; let T ← $ᵗ C.Term; pure (g, T)] *
        (C.n.choose (C.t - 1) : ℝ≥0∞) = Pr[fun g => g.1 = true | game] := by
  sorry

/-! ## One-time signature -/

/-- A codeword covers another only if they are equal, since all codewords have the same digit sum
(PRAWNS, Definition 3.1, for the codewords of leanXMSS). -/
theorem prawns_cover_free (d d' : Digest) (hd : Codeword.Valid d) (hd' : Codeword.Valid d')
    (hcover : ∀ l, Codeword.encoding d l ≤ Codeword.encoding d' l) :
    Codeword.encoding d = Codeword.encoding d' := by
  sorry

/-! ## Setup -/

/-- The dealer of Theorem 2 is PRAWNS `KeyGen`. With fresh honest contributions and any corrupt
contributions, every term seed, the parameter and every pair key with an honest operator are uniform
and independent, up to a collision of `H` inputs (each input holds a fresh honest part). -/
theorem dkg_dealer_is_prawnsKeyGen (keccak : HashInput → HashOutput) (aes : Aes) (D : C.Coalition)
    (corrupt : C.Party → Contribution C) :
    let honestView := fun (keys : C.Party → Keys C) (seeds : C.Term → HashOutput) =>
      ((keys (firstParty C)).parameter, seeds,
        fun (i j : C.Party) => if i ∉ D.1 ∨ j ∉ D.1 then (keys i).pairKey j else 0)
    tvDist
      ((fun r => r.1) <$> runWorld (C := C) keccak aes (do
        let honest ← Concrete.sequenceFin fun i => liftComp (sampleContribution i) _
        let contributions := fun i => if i ∈ D.1 then corrupt i else honest i
        let keys ← dealerKeys contributions
        let seeds ← deriveSeeds contributions
        pure (honestView keys seeds)))
      ((fun r => r.1) <$> runWorld (C := C) keccak aes (do
        let (_, seeds, keys) ← liftComp prawnsKeyGen _
        pure (honestView keys seeds))) ≤
      ((C.n.choose (C.t - 1) + C.n ^ 2 + 1) ^ 2 : ℕ) / 2 ^ 256 := by
  sorry

/-- Security against `t - 1` corrupt operators gives security against fewer, since an adversary for
`D'` can play the operators of `D' \ D` honestly (GIP+14, Lemma 5.2, and GS20, Theorem 1). After the
last phase, `split` finishes the rounds of those operators. -/
theorem gip14_lemma52_fewer_corrupt (K : Constants C E) (settings : Settings) (circuits : Circuits)
    (keccak : HashInput → HashOutput) (aes : Aes) (schedule : List Tree) (D D' : C.Coalition)
    (hDD' : D.1 ⊆ D'.1) (A : Adversary C E) :
    ∃ (A' : Adversary C E) (split : A'.State → OracleComp (LocalSpec C) (A.State × (C.Party → DkgOutput C))),
      𝒟[(fun r => r.1) <$> runWorld keccak aes (do
          let (state, outputs) ← realExecution K settings circuits D' A' schedule
          let (state, played) ← split state
          pure (state, fun i => if i ∈ D'.1 ∧ i ∉ D.1 then played i else outputs i))] =
        𝒟[(fun r => r.1) <$> runWorld keccak aes (realExecution K settings circuits D A schedule)] := by
  sorry

end ThresholdLeanXmssSecurity
