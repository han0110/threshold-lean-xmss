import ThresholdLeanXmssSecurity.Proof.SigningLane2Flat
import ThresholdLeanXmssSecurity.Proof.SigningLinkPaid
import XmssSecurity.Proof.Deterministic.Replay
import XmssSecurity.Proof.ConsistentQueryBound

/-!
# Local laws for the shared signing lane

A message-digest query cannot be a canonical randomizer-base query
(`not_baseCall_of_isMsg`). This holds for every state of the flat lane run.
`message_no_trigger` in `SigningCompilerPotential` uses it.
-/

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningLaneHybridProof

open HashSig LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof
  SigningLane2BridgeProof SigningLane2FlatProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The two copies of the hash oracle preserve the input address. -/
theorem hashCallAt_injective {a b : HashInput} {t : (WorldSpec C).Domain}
    (ha : HashCallAt a t) (hb : HashCallAt b t) : a = b := by
  rcases ha with rfl | rfl <;>
    rcases hb with hb | hb <;> simp_all

/-- A canonical randomizer-base query is outside the message-digest domain. -/
theorem not_baseCall_of_isMsg (P : PublicParameter) (ρ : KeyIndex → Digest)
    (st : TsigState C) {input : HashInput} {t : (WorldSpec C).Domain}
    (hmsg : IsMsg input) (hcall : HashCallAt input t) :
    ¬∃ e, BaseCall P e (ρ e) st t := by
  rintro ⟨e, address, haddress, hbase⟩
  have heq := hashCallAt_injective hcall hbase
  subst address
  cases hb : st.bound e with
  | none => simp [baseInput, hb] at haddress
  | some message =>
    simp only [baseInput, hb] at haddress
    have haddress : randomizerInput P bottomLayer e (ρ e) (littleEndianBytes 32 message) = input :=
      Option.some.inj haddress
    exact not_isMsg_randomizerInput P bottomLayer e (ρ e) (littleEndianBytes 32 message)
      (haddress.symm ▸ hmsg)

end ThresholdLeanXmssSecurity.SigningLaneHybridProof
