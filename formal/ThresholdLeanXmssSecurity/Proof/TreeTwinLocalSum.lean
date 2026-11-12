import ThresholdLeanXmssSecurity.Proof.CheckStages

/-!
# The length-one halving claim and the final mask identity

Agreement of Shamir shares at the honest points determines their secret, since there
are at least `t` such points. Applied to the claim difference in `HalvRel`, this
identifies its lacked-term value. Interpolation of the product polynomials then
expresses that value as the honest local-product sum.
-/

open LeanXmss ThresholdLeanXmss Finset

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeTwinLocalSum

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- The Shamir share of operator `i` of the value `e` on the lacked term. -/
def lackedShare (D : C.Coalition) (i : C.Party) (e : E) : E :=
  conv K (localContext i) (fun T _ => if lackedTerm D.1 = some T then e else 0) 0

omit [Fintype E] [DecidableEq E] in
/-- Agreement at the honest points determines the secret of a Shamir sharing. -/
theorem isShamir_eq_of_honest (D : C.Coalition) {f g : C.Party → E} {a b : E}
    (hf : IsShamir K f a) (hg : IsShamir K g b)
    (agree : ∀ i, i ∉ D.1 → f i = g i) : a = b := by
  obtain ⟨P, hP, hP0, hPi⟩ := hf
  obtain ⟨Q, hQ, hQ0, hQi⟩ := hg
  have hPQ : P = Q := poly_eq_of_honest K D P Q
    (degree_lt_of_natDegree P hP) (degree_lt_of_natDegree Q hQ)
    (fun i hi => (hPi i).symm.trans ((agree i hi).trans (hQi i)))
  rw [← hP0, ← hQ0, hPQ]

omit [Fintype E] [DecidableEq E] in
/-- At length one, the halving relation and the shape give the claim difference as
the sum of the local product differences of the honest operators. -/
theorem halvRel_localSum [CharP E 2] (D : C.Coalition)
    (AR BR AD BD : C.Party → ℕ → E) (DR DD : C.Party → E)
    (h : HalvRel K D 1 AR BR AD BD DR DD) (e : E) (T₀ : C.Term)
    (lacked : lackedTerm D.1 = some T₀)
    (shape : ∀ i, i ∉ D.1 → DR i - DD i = lackedShare K D i e) :
    e = ∑ i ∈ univ.filter (· ∉ D.1),
      lagrangeAll K i * (AR i 0 * BR i 0 - AD i 0 * BD i 0) := by
  obtain ⟨a, b, a', b', dA, dB, dD, hA, hB, hA', hB', hCA, hCB,
    hkA, hkB, hkD, hsA, hsB, hlA, hlB, hlD, hsum⟩ := h
  have he : (∑ T, dD T) = e := by
    have hs := isShamir_conv (K := K) (fun T _ => if lackedTerm D.1 = some T then e else 0) 0
    have hs' : IsShamir K (fun i => lackedShare K D i e) e := by
      simpa [lackedShare, lacked, eq_comm] using hs
    exact isShamir_eq_of_honest K D (isShamir_conv (K := K) (fun T _ => dD T) 0) hs'
      (fun i hi => (hlD i hi).symm.trans (shape i hi))
  have hproducts := honest_mulSh_diff K D AR BR AD BD a b a' b'
    hA hB hA' hB' hCA hCB 1
  rw [← he, hsum]
  simpa only [sum_range_one, ← sum_sub_distrib, ← mul_sub] using hproducts.symm

omit [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The mask identity for the challenge `r` and the translation `r / (1 + r)`.
Ported from `.claude/design/TwinSeg_Seg8b.lean`, `finalMask_local`. -/
theorem finalMask_local [CharP E 2] (r lam wa wb A B a b : E) (hr : 1 + r ≠ 0) :
    (1 + r) * (lam * (wa * wb - (wa + r / (1 + r) * a) * (wb + r / (1 + r) * b))) +
      r * (1 + r) * (lam * ((wa + A) * (wb + B) -
        (wa + r / (1 + r) * a + (A + a)) * (wb + r / (1 + r) * b + (B + b)))) =
      r * (lam * (A * B - (A + a) * (B + b))) := by
  have h2 : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
  have hc : r / (1 + r) * (1 + r) = r := div_mul_cancel₀ r hr
  generalize r / (1 + r) = c at hc
  linear_combination (-lam * (a * wb + b * wa + c * a * b) -
    lam * r * (a * (wb + B) + b * (wa + A) + (1 + c) * a * b)) * hc +
    (-lam * r * ((1 + r) * (a * wb + b * wa) + r * (a * B + b * A) +
      a * b * (c + r + r * c))) * h2

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLocalSum.isShamir_eq_of_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isShamir_eq_of_honest

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLocalSum.halvRel_localSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halvRel_localSum

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLocalSum.finalMask_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalMask_local

end ThresholdLeanXmssSecurity.TreeTwinLocalSum
