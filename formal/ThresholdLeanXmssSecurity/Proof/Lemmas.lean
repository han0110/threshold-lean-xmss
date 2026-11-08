import ThresholdLeanXmss.Statement

/-!
# The steps of the proofs

The intermediate results of the cited papers, each named after its source, with no proof. The
proofs of `ThresholdLeanXmss/Statement.lean` combine them as follows.

* The key generation follows GS20, Theorem 2.
* Its gadget steps are `F_rand` from PRSS (CDI05), the reshare (GS20, Lemma 4) and the coin (GS20,
  Lemma 3).
* Its check steps are the digests (CGH+18, Protocol 3.3), the check (GS20, Lemmas 8 to 11), the word
  weights of `src/check.rs`, and the slice steps (Gruen 2024). The challenges come from
  `E \ {0, 1}`, so a step with at most two bad challenges fails with probability at most
  `2 / (|E| - 2)`.
* The outputs open as in MPClan, App. B. The keygen adds the extraction and programming of CDG+18.
* The signing follows PRAWNS, Theorem 3.1, with Theorem 5.1 and Lemma 5.2 for the threshold PRF.
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
theorem prawns_L_partition (J : C.Quorum) (T : C.Term) : ∃! i, i ∈ J.1 ∧ T ∈ L J i := by
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

/-! ## The check -/

/-- A nonzero word of bit differences keeps a nonzero weight, because the weights `x^q` are linearly
independent over `F_2` (`src/check.rs`). -/
theorem check_word_weight_ne_zero (K : Constants C E) (b : Fin (2 ^ wordBits) → Bit) (hb : b ≠ 0) :
    ∑ q, b q • K.weight q ≠ 0 := by
  sorry

/-- The de-linearization keeps a wrong tuple, except with probability `s / (|E| - 1) + (d - s) / |E|`
over its coins. The weight `τ^a` of word `a < 2^d` is multilinear in the `d` coins. The first `s`
coins are the slice coins, which are nonzero because the check aborts on a zero slice coin, and the
expansion draws the other coins from all of `E` (GS20, Lemma 8, with the multilinear weights of the
prototype and Schwartz and Zippel). -/
theorem gs20_lemma8_delinearization (s d : ℕ) (hs : s ≤ d) (δ : ℕ → E) (hδ : ∃ a < 2 ^ d, δ a ≠ 0) :
    ((univ.filter fun τ : (Fin s → {c : E // c ≠ 0}) × (Fin (d - s) → E) =>
        ∑ a ∈ range (2 ^ d), coinProduct (List.ofFn (fun b => (τ.1 b).1) ++ List.ofFn τ.2) 0 d a * δ a = 0).card : ℝ) /
      ((Fintype.card E - 1 : ℝ) ^ s * (Fintype.card E : ℝ) ^ (d - s)) ≤
      s / (Fintype.card E - 1 : ℝ) + (d - s : ℕ) / (Fintype.card E : ℝ) := by
  sorry

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

/-- A slice step keeps a wrong claim wrong for all but two challenges. It keeps the slice coin `c`
out of `x`, so the claim is `D = t(0) + c t(1)` for the quadratic `t(X) = t₀ + t₁ X + t₂ X²` of the
folded inner product. The step reshares `t(0)` and the leading coefficient with additive errors and
interpolates `t(r)` at `0`, `1` and `∞` (Gruen 2024, and `doc/dkg.md` 3.3). -/
theorem gruen_slice_step [CharP E 2] (c D t₀ t₁ t₂ e₀ eInf : E) (hc : c ≠ 0)
    (hwrong : D ≠ t₀ + c * (t₀ + t₁ + t₂)) :
    (univ.filter fun r : E =>
      (1 + r) * (t₀ + e₀) + r * ((D + (t₀ + e₀)) / c) + r * (1 + r) * (t₂ + eInf) =
        t₀ + t₁ * r + t₂ * r ^ 2).card ≤ 2 := by
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

/-! ## Signing -/

/-- A uniform guess of the `t - 1` corrupt operators is right with probability `1 / C(n, t - 1)`,
independently of the game (PRAWNS, Lemma 5.2). -/
theorem prawns_lemma52_guess (game : ProbComp (Bool × C.Term)) [Nonempty C.Term] :
    letI := SampleableType.ofFintype C.Term
    Pr[fun r => r.1.1 = true ∧ r.2 = r.1.2 | do let g ← game; let T ← $ᵗ C.Term; pure (g, T)] *
        (C.n.choose (C.t - 1) : ℝ≥0∞) = Pr[fun g => g.1 = true | game] := by
  sorry

/-- A codeword covers another only if they are equal, since all codewords have the same digit sum
(PRAWNS, Definition 3.1, for the codewords of leanXMSS). -/
theorem prawns_cover_free (d d' : Digest) (hd : Codeword.Valid d) (hd' : Codeword.Valid d')
    (hcover : ∀ l, Codeword.encoding d l ≤ Codeword.encoding d' l) :
    Codeword.encoding d = Codeword.encoding d' := by
  sorry

end ThresholdLeanXmssSecurity
