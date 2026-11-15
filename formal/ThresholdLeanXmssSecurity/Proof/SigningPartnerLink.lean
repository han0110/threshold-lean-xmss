import ThresholdLeanXmssSecurity.Proof.SigningGuessLink

/-!
# The bottom partner half of the uncharged lane

A bottom partner is an outcome of `exposedRun` where the forged digest input at the key `e` of the
forgery differs from the selected input `hk.selected`, and both give the same digest.
`BottomPartnerCase` names this case. `SigningAssembly` uses it to split the win.

`bottomDigestCost` is `digestCost` minus the top digest calls. On a digest call the structural hit
cost and the commitment cost are zero (`structuralHitCost_zero_digest`, `commitment_not_digest`).
The top partner charges only top digest calls (`topDigest_rawCost_le`,
`resolvedTopPartner_bound_topDigest`). So these charged events leave the unit of each bottom digest
call free. `chargedLane_bound_oneRun` in `SigningLinkPaid` uses this unit for the R1 hit, which
pays the partner of a fresh selection. The partner of a cached selection does not use this unit.
It shares the cap of the uncharged lane.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningPartnerLinkProof

open HashSig LeanXmss ThresholdLeanXmss

variable {C : Committee} (prims : Primitives)

/-- The bottom partner case on an outcome of `exposedRun`. The selected input differs from the forged
digest input, and both give the same digest. -/
def BottomPartnerCase (x : SigningSecurityProof.Keys3 C) (r : SigningCostProof.Outcome C) : Prop :=
  ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := SigningCostProof.finalOf x r top state forgery
    let hk := z.honestKey prims
    let signature := XmssSecurity.Bridge.toModelSig forgery.signature
    ∃ selected, hk.selected = some selected ∧ selected ≠ (forgery.message, signature.randomness) ∧
      XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
          x.1 z.key selected =
        XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
          x.1 z.key (forgery.message, signature.randomness)

section Split

attribute [local instance] Classical.propDecidable

/-- The cost of a digest call that is not a top digest call. The top partner of `ChargedOutput`
charges only top digest calls (`topDigest_rawCost_le`), so this part of `digestCost` is free in
the charged lane. -/
def bottomDigestCost (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) : ℕ :=
  SigningGuessLaneProof.digestCost t -
    SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t

theorem topDigest_add_bottomDigestCost (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) :
    SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t + bottomDigestCost x t =
      SigningGuessLaneProof.digestCost t := by
  have h : SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1) t ≤
      SigningGuessLaneProof.digestCost t := by
    convert SigningGuessProof.topDigest_rawCost_le (C := C) x.1 t
  unfold bottomDigestCost
  omega

/-- The top partner charged to the top digest calls alone. -/
theorem resolvedTopPartner_bound_topDigest (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr{let r ←
        SigningDescentProof.exposedRun prims A x}[∃ key, SigningGuessProof.ResolvedTopPartner x key r.2.1] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * SigningGuessProof.sourceExpectedCost prims A x
        (SigningGuessProof.rawDomainCost (SigningGuessProof.anyTopDigestInput x.1)) := by
  convert SigningGuessProof.cachePotential_bound_source prims A x (SigningGuessProof.anyTopDigestInput x.1)
    (SigningGuessProof.topPartnerPotential x) (fun cache => ∃ key, SigningGuessProof.ResolvedTopPartner x key cache)
    (SigningGuessProof.topPartnerPotential_zero x)
    (fun cache he => SigningGuessProof.topPartnerPotential_terminal x cache he)
    (fun input cache => by convert SigningGuessProof.topPartnerPotential_step x input cache using 3)


variable (partner : SigningSecurityProof.Keys3 C → SigningCostProof.Outcome C → Prop)

end Split

end SigningPartnerLinkProof

end ThresholdLeanXmssSecurity
