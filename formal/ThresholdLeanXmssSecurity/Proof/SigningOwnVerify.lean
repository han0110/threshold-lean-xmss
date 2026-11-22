import LeanXmss.Scheme
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# The hash calls of the verification

`verify_bound` states that `Verification.verifyWithHash` makes at most `capSlack` hash calls on each path. Each
layer makes one message digest call, at most `chainLength - 1` calls on each of the `chainCount`
chains, one leaf call and `layerHeight` node calls. So the two layers make at most
`2 (1 + 58 · 3 + 1 + 16) = 384` calls.

The proof follows `total_verify` of the newer leanXMSS,
`leanVM/formal/lean_xmss/XmssSecurity/Proof/OwnBudget.lean`, for the pinned `Verification.verifyWithHash`. It
states each bound as `IsQueryBoundP` with the predicate `fun _ => True`, so the lift of
`isQueryBoundP_liftM_of_total` is not necessary.
-/

open OracleComp OracleSpec HashSig LeanXmss

namespace ThresholdLeanXmssSecurity

namespace SigningOwnVerify

attribute [local instance] Classical.propDecidable

/-- The slack of the capped lane in units of `2^-128`, the calls of the verification. -/
def capSlack : ℕ := 384

/-- A hash program with at most `n` calls. -/
abbrev Calls {α : Type} (oa : OracleComp HashSpec α) (n : ℕ) : Prop :=
  IsQueryBoundP oa (fun _ => True) n

theorem calls_bind_le {α β : Type} {oa : OracleComp HashSpec α} {ob : α → OracleComp HashSpec β}
    {a b n : ℕ} (h1 : Calls oa a) (h2 : ∀ x, Calls (ob x) b) (h : a + b ≤ n) :
    Calls (oa >>= ob) n :=
  (isQueryBoundP_bind h1 fun x _ => h2 x).mono h

theorem calls_tweakableHash (P : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    Calls (Verification.tweakableHashWithHash P domain payload : OracleComp HashSpec Digest) 1 := by
  unfold Verification.tweakableHashWithHash Verification.thWithHash Verification.oracleHashWithHash
  simp [Calls]

theorem calls_sequenceFin {α : Type} {n b : ℕ} (f : Fin n → OracleComp HashSpec α)
    (h : ∀ i, Calls (f i) b) : Calls (OverPermutation.sequenceFin f) (n * b) := by
  induction n with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ n ih =>
      unfold OverPermutation.sequenceFin
      exact calls_bind_le (h 0) (fun _ => calls_bind_le (ih _ fun i => h i.succ)
        (fun _ => isQueryBoundP_pure _ _ 0) (Nat.add_zero _).le) (by rw [Nat.succ_mul]; omega)

theorem calls_chainWalk (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (start steps : ℕ) (value : Digest) :
    Calls (Verification.chainWalkWithHash P lay key chainIdx start steps value : OracleComp HashSpec Digest)
      steps := by
  induction steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ steps ih =>
      rw [Verification.chainWalk_eq_succ]
      refine calls_bind_le ih (b := 1) (fun _ => ?_) le_rfl
      split
      · exact calls_tweakableHash _ _ _
      · exact (isQueryBoundP_pure _ _ _)

theorem calls_treeFold (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : ℕ) (value : Digest) :
    Calls (Verification.treeFoldWithHash P lay key path levels value : OracleComp HashSpec Digest) levels := by
  induction levels with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ levels ih =>
      rw [Verification.treeFold_eq_succ]
      refine calls_bind_le ih (b := 1) (fun _ => ?_) le_rfl
      dsimp only
      split <;> exact calls_tweakableHash _ _ _

attribute [local irreducible] layerHeight chainCount in
/-- One layer makes at most `1 + 58 · 3 + 1 + 16 = 192` calls. -/
theorem calls_layerRoot (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    Calls (Verification.layerRootWithHash P lay key message part : OracleComp HashSpec (Option Digest)) 192 := by
  unfold Verification.layerRootWithHash Verification.otsLeafWithHash
  refine calls_bind_le (a := 176) (b := 16) (calls_bind_le (calls_tweakableHash _ _ _) (b := 175)
    (fun digest => ?_) le_rfl) (fun leaf => ?_) le_rfl
  · cases Codeword.decode digest with
    | none => exact isQueryBoundP_pure _ _ _
    | some encoding =>
        dsimp only
        refine calls_bind_le (calls_sequenceFin (b := 3) _ fun chainIdx =>
          (calls_chainWalk _ _ _ _ _ _ _).mono ?_) (b := 1)
          (fun _ => calls_bind_le (calls_tweakableHash _ _ _) (b := 0)
            (fun _ => isQueryBoundP_pure _ _ _) le_rfl) (by unfold chainCount; omega)
        unfold chainLength winternitzBits
        omega
  · cases leaf with
    | none => exact (isQueryBoundP_pure _ _ _)
    | some leaf =>
        exact calls_bind_le (calls_treeFold P lay key part.authenticationPath layerHeight leaf) (b := 0)
          (fun _ => isQueryBoundP_pure _ _ _) (by unfold layerHeight; omega)

/-- The verification makes at most `capSlack` hash calls on each path. -/
theorem verify_bound (publicKey : PublicKey) (message : Message) (signature : Signature) :
    IsQueryBoundP (Verification.verifyWithHash publicKey message signature : OracleComp HashSpec Bool)
      (fun _ => True) capSlack := by
  unfold Verification.verifyWithHash
  refine calls_bind_le (calls_layerRoot _ _ _ _ _) (b := 192) (fun bottomRoot => ?_) le_rfl
  cases bottomRoot with
  | none => exact isQueryBoundP_pure _ _ _
  | some bottomRoot =>
      refine calls_bind_le (calls_layerRoot _ _ _ _ _) (b := 0) (fun root => ?_) le_rfl
      cases root with
      | none => exact isQueryBoundP_pure _ _ _
      | some root => exact isQueryBoundP_pure _ _ _

end SigningOwnVerify

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.calls_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.calls_bind_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.calls_tweakableHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.calls_tweakableHash

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.calls_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.calls_sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.calls_chainWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.calls_chainWalk

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.calls_treeFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.calls_treeFold

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.calls_layerRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.calls_layerRoot

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnVerify.verify_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnVerify.verify_bound
