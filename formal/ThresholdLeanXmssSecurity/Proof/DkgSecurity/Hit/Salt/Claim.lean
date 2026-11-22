import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Whole
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Count
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Step
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Program

/-!
# The part `HitSalt` of the first hit

`hitSalt` gives `HitSalt` by `hitSalt_of_prov` from the four statements `SaltFullLogged`
(`saltFullLogged`), `SaltProv` (`saltProv`), `SaltProvStep` (`saltProvStep`) and `SaltProvCount`
(`saltProvCount`).
-/

set_option autoImplicit false

open ThresholdLeanXmss ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The part `HitSalt` of the first hit. -/
theorem hitSalt : HitSalt prims K circuits settings runLimit :=
  hitSalt_of_prov prims K circuits settings runLimit (saltFullLogged prims K circuits settings runLimit)
    (saltProv K circuits settings runLimit) (saltProvStep prims)
    (saltProvCount prims K circuits settings runLimit)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.hitSalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.hitSalt
