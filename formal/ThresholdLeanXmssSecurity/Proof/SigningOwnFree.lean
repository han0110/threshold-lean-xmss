import ThresholdLeanXmssSecurity.Proof.SigningOwnLedger

/-!
# Honest hash calls that the ledger never charges

`FreeInput` holds for a hash input with no candidate and no decoding by the lane 2 key. A call on
such an input is never charged (`free_not_charged`).

* Leaf, node and top digest inputs are free (`free_leaf`, `free_node`, `free_topDigest`). Byte 23
  of an input separates the domains. The domain fields separate a top digest input from a bottom
  message digest input, as in `SigningCompilerO1Events.outsideTrials_chain`.
* The tree routine and the top search query free inputs only (`free_merkleNode`, `free_topGrind`).
* A pending input at a revealed key is not charged (`pending_not_charged`).
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnFree

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningOwnLedger

variable {C : Committee}

attribute [local instance] Classical.propDecidable


/-- A hash input with no candidate and no decoding by the lane 2 key. A call on it is never
charged, in each state. -/
def FreeInput (P : PublicParameter) (input : HashInput) : Prop :=
  hiddenCandidate P input = none ∧
    XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey P).parameter input = none

/-- A call on a free input is not charged. -/
theorem free_not_charged (P : PublicParameter) (seeds : C.Term → HashOutput) (input : HashInput)
    (h : FreeInput P input) (st : (CompilerBackend C × ℕ) × (HiddenKey → Option Digest))
    (g : OwnGhost) : ¬ownCharged P seeds (.hash (.hash input)) st g := by
  rintro ⟨input', heq, ⟨c, hc, -⟩ | ⟨-, hdec, -⟩⟩
  · cases heq
    rw [h.1] at hc
    cases hc
  · cases heq
    rw [h.2] at hdec
    cases hdec

/-- The lane 2 key decodes only bottom message digest inputs. -/
theorem dec_eq_none (P : PublicParameter) (input : HashInput)
    (h : ∀ e payload, input ≠ tweakableHashInput P (.message bottomLayer e) payload) :
    XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey P).parameter input = none := by
  unfold XmssSecurity.Ghost.dec
  rw [dif_neg]
  rintro ⟨⟨e, message, randomness⟩, hy⟩
  refine h e (littleEndianBytes 32 message ++ littleEndianBytes 16 randomness) ?_
  rw [← hy]
  exact (SigningLane2BridgeProof.messageInput_eq_partnerInput P e message randomness).symm

/-- A tweakable input of a domain that is no chain domain, and whose byte 23 is that of a leaf or
a node, has no candidate. -/
theorem hiddenCandidate_leafNode (P : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hchain : ∀ lay key step, hashDomainFields domain ≠ hashDomainFields (.chain lay key step))
    (hbyte : (tweakableHashInput P domain payload)[23]? = some 2 ∨
      (tweakableHashInput P domain payload)[23]? = some 3) :
    hiddenCandidate P (tweakableHashInput P domain payload) = none := by
  have hc : ¬∃ e ρ, tweakableHashInput P domain payload = commitmentInput P e ρ := by
    rintro ⟨e, ρ, h⟩
    rw [h, byte23_commitment] at hbyte
    rcases hbyte with h | h <;> cases h
  have hr : ¬∃ lay e ρ message,
      tweakableHashInput P domain payload = randomizerInput P lay e ρ message := by
    rintro ⟨lay, e, ρ, message, h⟩
    rw [h, byte23_randomizer] at hbyte
    rcases hbyte with h | h <;> cases h
  have hb : ¬∃ e l p v, tweakableHashInput P domain payload =
      XmssSecurity.Concrete.CacheView.chainInput P e l p v := by
    rintro ⟨e, l, p, v, h⟩
    rw [SigningGuessLinkProof.chainInput_eq_bridge P e l p v] at h
    exact hchain _ _ _ (tweakableInput_injective h).1
  have ht : ¬∃ b l p v, tweakableHashInput P domain payload =
      XmssSecurity.Concrete.CacheView.topChainInput P b l p v := by
    rintro ⟨b, l, p, v, h⟩
    rw [SigningGuessLinkProof.topChainInput_eq_bridge P b l p v] at h
    exact hchain _ _ _ (tweakableInput_injective h).1
  simp only [hiddenCandidate, dif_neg hc, dif_neg hr, dif_neg hb, dif_neg ht]

/-- A tweakable input whose byte 23 is not that of a message digest input is decoded by no key. -/
theorem dec_eq_none_of_byte23 (P : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hbyte : (tweakableHashInput P domain payload)[23]? ≠ some 12) :
    XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey P).parameter
      (tweakableHashInput P domain payload) = none := by
  refine dec_eq_none P _ fun e payload' h => hbyte ?_
  rw [h, byte23_msg]

/-- A leaf input is free. -/
theorem free_leaf (P : PublicParameter) (lay : Layer) (key : KeyIndex) (payload : HashInput) :
    FreeInput P (tweakableHashInput P (.leaf lay key) payload) := by
  refine ⟨hiddenCandidate_leafNode P _ payload (fun lay' key' step h => ?_)
    (Or.inl (byte23_leaf P lay key payload)), dec_eq_none_of_byte23 P _ payload ?_⟩
  · simp only [hashDomainFields] at h
    exact absurd (congrArg TweakFields.tag h) (by simp only [tweakFields]; decide)
  · rw [byte23_leaf]
    decide

/-- A node input is free. -/
theorem free_node (P : PublicParameter) (lay : Layer) (level idx : ℕ) (payload : HashInput) :
    FreeInput P (tweakableHashInput P (.node lay level idx) payload) := by
  refine ⟨hiddenCandidate_leafNode P _ payload (fun lay' key' step h => ?_)
    (Or.inr (byte23_node P lay level idx payload)), dec_eq_none_of_byte23 P _ payload ?_⟩
  · simp only [hashDomainFields] at h
    exact absurd (congrArg TweakFields.tag h) (by simp only [tweakFields]; decide)
  · rw [byte23_node]
    decide

/-- A top digest input is free. The lane 2 key decodes bottom encoding inputs only. -/
theorem free_topDigest (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (payload : XmssSecurity.Digest × XmssSecurity.Randomness) :
    FreeInput P (XmssSecurity.Concrete.CacheView.topEncodingInput P b payload) := by
  have hm := XmssSecurity.Bridge.topMessage_input P b payload.1 payload.2
  have hmsg : IsMsg (XmssSecurity.Concrete.CacheView.topEncodingInput P b payload) := by
    unfold XmssSecurity.Concrete.CacheView.topEncodingInput
    rw [← hm]
    exact byte23_msg _ _ _ _
  refine ⟨hiddenCandidate_none_of_isMsg P _ hmsg, dec_eq_none P _ fun e payload' h => ?_⟩
  -- The third clause of `SigningCompilerO1Events.outsideTrials_chain`, with no committee.
  unfold XmssSecurity.Concrete.CacheView.topEncodingInput at h
  rw [← hm] at h
  have hf := congrArg (fun f => f.hi.toNat) (tweakableInput_injective h).1
  norm_num [hashDomainFields, tweakFields, layerHi, topLayer, bottomLayer] at hf

/-- The tree routine queries free inputs only. -/
theorem free_merkleNode (P : PublicParameter) (lay : Layer)
    (chainEnd : KeyIndex → ChainIndex → Digest) (level idx : ℕ) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P) (merkleNode P lay chainEnd level idx) := by
  induction level generalizing idx with
  | zero =>
      exact (XmssSecurity.Bridge.onlyQueries_query (free_leaf P lay _ _)).bind fun _ => .pure _
  | succ level ih =>
      exact (ih _).bind fun _ => (ih _).bind fun _ =>
        (XmssSecurity.Bridge.onlyQueries_query (free_node P lay _ _ _)).bind fun _ => .pure _

/-- The top search queries free inputs only. -/
theorem free_topGrind (P : PublicParameter) (b : Fin (2 ^ layerHeight)) (root : Digest)
    (base : Randomizer) (attempts trial : ℕ) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P)
      (grind P topLayer (topKey b) (littleEndianBytes 16 root) base attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      have hfree := free_topDigest P b (root, base + BitVec.ofNat digestBits trial)
      unfold XmssSecurity.Concrete.CacheView.topEncodingInput at hfree
      rw [← XmssSecurity.Bridge.topMessage_input P b root (base + BitVec.ofNat digestBits trial)] at hfree
      refine ((XmssSecurity.Bridge.onlyQueries_query hfree).bind fun _ => .pure _).bind fun digest => ?_
      cases Codeword.decode digest with
      | some encoding => exact .pure _
      | none => exact ih _

/-- A pending input carries the candidate of its key, and it is no message digest input. So a call
on it at a revealed key is not charged. -/
theorem pending_not_charged (P : PublicParameter) (seeds : C.Term → HashOutput) (p : PendingInput)
    (value : Digest) (st : (CompilerBackend C × ℕ) × (HiddenKey → Option Digest)) (g : OwnGhost)
    (hrev : st.2 p.key ≠ none) :
    ¬ownCharged P seeds (.hash (.hash (p.input P value))) st g := by
  rintro ⟨input', heq, ⟨c, hc, hnone⟩ | ⟨hmsg, -⟩⟩
  · cases heq
    rw [PendingInput.hiddenCandidate] at hc
    cases hc
    exact hrev hnone
  · cases heq
    exact PendingInput.not_isMsg P p value hmsg

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.free_not_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms free_not_charged

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.dec_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dec_eq_none

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.hiddenCandidate_leafNode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms hiddenCandidate_leafNode

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.dec_eq_none_of_byte23' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dec_eq_none_of_byte23

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.free_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms free_leaf

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.free_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms free_node

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.free_topDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms free_topDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.free_merkleNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms free_merkleNode

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.free_topGrind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms free_topGrind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnFree.pending_not_charged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_not_charged

end ThresholdLeanXmssSecurity.SigningOwnFree
