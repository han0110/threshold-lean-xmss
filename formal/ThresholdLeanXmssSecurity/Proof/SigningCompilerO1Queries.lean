import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareSource
import ThresholdLeanXmssSecurity.Proof.SigningGuessLink

/-! # The query alphabet of the hash programs

- `IsTweakable` holds for the inputs of the tweakable hash `Th`.
- Each hash program of the scheme queries `H` only at tweakable inputs. The lemmas `queries_*` state
  this for each program.
- `queries_noBase` states that such a program makes no bottom base call. `verify_noBase` applies it
  to the verification.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Queries
open SigningCompilerShare

/-- A tweakable hash input. -/
def IsTweakable (input : HashInput) : Prop :=
  ∃ (P : PublicParameter) (domain : HashDomain) (payload : HashInput),
    input = tweakableHashInput P domain payload

/-- `Queries` is monotone in the query alphabet. -/
theorem queries_mono {ι α : Type} {spec : OracleSpec ι} {allowed permit : ι → Prop}
    (hle : ∀ t, allowed t → permit t) (oa : OracleComp spec α) (h : Queries allowed oa) :
    Queries permit oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact Queries.pure a
  | query_bind t next ih =>
      have hb := (isQueryBound_query_bind_iff ..).mp h
      exact (isQueryBound_query_bind_iff ..).mpr ⟨hle t hb.1, fun a => ih a (hb.2 a)⟩

attribute [local irreducible] Queries

/-- A program of tweakable hash calls makes no bottom base call. -/
theorem queries_noBase (P : PublicParameter) {α : Type} (oa : OracleComp HashSpec α)
    (h : Queries IsTweakable oa) :
    Queries (fun input => ∀ e ρ message, input ≠ randomizerInput P bottomLayer e ρ message) oa := by
  refine queries_mono ?_ oa h
  rintro _ ⟨P', domain, payload, rfl⟩ e ρ message heq
  exact SigningGuessLinkProof.randomizerInput_ne_tweakableHashInput _ _ _ _ _ _ _ _ heq.symm

theorem queries_tweakableHash (P : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    Queries IsTweakable (Concrete.tweakableHash P domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash Concrete.oracleHash
  exact (Queries.query _ ⟨P, domain, payload, rfl⟩).bind fun _ => Queries.pure _

theorem queries_sequenceFin {α : Type} {n : ℕ} (f : Fin n → OracleComp HashSpec α)
    (h : ∀ i, Queries IsTweakable (f i)) : Queries IsTweakable (Concrete.sequenceFin f) := by
  induction n with
  | zero => exact Queries.pure _
  | succ n ih =>
      unfold Concrete.sequenceFin
      exact (h 0).bind fun _ => (ih _ fun i => h i.succ).bind fun _ => Queries.pure _

theorem queries_leafHash (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (ends : ChainIndex → Digest) :
    Queries IsTweakable (Concrete.leafHash P lay key ends : OracleComp HashSpec Digest) :=
  queries_tweakableHash _ _ _

theorem queries_messageDigest (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomness) :
    Queries IsTweakable
      (Concrete.messageDigest P lay key message randomness : OracleComp HashSpec Digest) :=
  queries_tweakableHash _ _ _

theorem queries_treeFold (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : ℕ) (value : Digest) :
    Queries IsTweakable
      (Concrete.treeFold P lay key path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => exact Queries.pure _
  | succ levels ih =>
      unfold Concrete.treeFold
      refine ih.bind fun _ => ?_
      dsimp only
      split <;> exact queries_tweakableHash _ _ _

theorem queries_merkleNode (P : PublicParameter) (lay : Layer)
    (chainEnd : KeyIndex → ChainIndex → Digest) (level idx : ℕ) :
    Queries IsTweakable (merkleNode P lay chainEnd level idx) := by
  induction level generalizing idx with
  | zero => exact queries_leafHash _ _ _ _
  | succ level ih =>
      unfold merkleNode
      exact (ih _).bind fun _ => (ih _).bind fun _ => queries_tweakableHash _ _ _

theorem queries_merklePath (P : PublicParameter) (lay : Layer)
    (chainEnd : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    Queries IsTweakable (merklePath P lay chainEnd key) :=
  queries_sequenceFin _ fun _ => queries_merkleNode _ _ _ _ _

theorem queries_grind (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomness) (attempts trial : ℕ) :
    Queries IsTweakable (grind P lay key message base attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact Queries.pure _
  | succ attempts ih =>
      unfold grind
      refine (queries_messageDigest _ _ _ _ _).bind fun digest => ?_
      split
      · exact Queries.pure _
      · exact ih _

/-- Each chain walk queries only tweakable inputs. -/
theorem queries_chainWalk (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (start steps : ℕ) (value : Digest) :
    Queries IsTweakable
      (Concrete.chainWalk P lay key chainIdx start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => exact Queries.pure _
  | succ steps ih =>
      unfold Concrete.chainWalk
      refine ih.bind fun _ => ?_
      split
      · exact queries_tweakableHash _ _ _
      · exact Queries.pure _

/-- Each layer root queries only tweakable inputs. -/
theorem queries_layerRoot (P : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (part : LayerSignature) :
    Queries IsTweakable
      (Concrete.layerRoot P lay key message part : OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.layerRoot Concrete.otsLeaf
  refine Queries.bind ((queries_messageDigest _ _ _ _ _).bind fun digest => ?_) fun leaf => ?_
  · cases Codeword.decode digest with
    | none => exact Queries.pure _
    | some encoding =>
        dsimp only
        exact (queries_sequenceFin _ fun _ => queries_chainWalk _ _ _ _ _ _ _).bind fun _ =>
          (queries_leafHash _ _ _ _).bind fun _ => Queries.pure _
  · cases leaf with
    | none => exact Queries.pure _
    | some leaf =>
        exact (queries_treeFold P lay key part.path layerHeight leaf).bind fun _ => Queries.pure _

theorem queries_verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    Queries IsTweakable
      (Concrete.verify publicKey message signature : OracleComp HashSpec Bool) := by
  unfold Concrete.verify
  refine (queries_layerRoot _ _ _ _ _).bind fun bottomRoot => ?_
  cases bottomRoot with
  | none => exact Queries.pure _
  | some bottomRoot =>
      refine (queries_layerRoot _ _ _ _ _).bind fun root => ?_
      cases root with
      | none => exact Queries.pure _
      | some root => exact Queries.pure _

/-- The verification of the scheme makes no bottom base call. -/
theorem verify_noBase (P : PublicParameter) (publicKey : PublicKey) (message : Message)
    (signature : Signature) :
    Queries (fun input => ∀ e ρ message', input ≠ randomizerInput P bottomLayer e ρ message')
      (Concrete.verify publicKey message signature : OracleComp HashSpec Bool) :=
  queries_noBase P _ (queries_verify publicKey message signature)

end ThresholdLeanXmssSecurity.SigningCompilerO1Queries

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_noBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_noBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_tweakableHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_tweakableHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_leafHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_leafHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_messageDigest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_messageDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_treeFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_treeFold

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_merkleNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_merkleNode

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_merklePath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_merklePath

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_grind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_chainWalk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_chainWalk

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_layerRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_layerRoot

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.queries_verify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Queries.verify_noBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Queries.verify_noBase
