import ThresholdLeanXmssSecurity.Proof.SigningLaneHybridCap

/-! # Threshold-guarded signing compiler

The source records round-2 chain digits and completes their suffixes only under
the prospective release threshold. A successful round 2 sweeps all chains of its
key before recording the signer, including chains skipped at digit 3. Corruption
sweeps keys whose recorded signer count crosses the threshold.

`CompilerCouplingO1` compares the original real guarded event with this fixed
source and the unchanged capped backend. `laneTraceCap_of_compilerO1` derives the
original cap from this coupling and the unchanged local potential step.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningLaneHybridCapO1Proof
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable

/-- The A100 source state, plus the digits that successful round-2 calls used. -/
structure SourceStateO1 (C : Committee) where
  base : SourceState C
  starts : KeyIndex → ChainIndex → Finset Digit

abbrev SourceMO1 (C : Committee) :=
  StateT (SourceStateO1 C) (OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest))

def sourceInitO1 : SourceStateO1 C := ⟨sourceInit, fun _ _ => ∅⟩

/-- Run an A100 source step on the base state. -/
def liftBase {α : Type} (oa : SourceM C α) : SourceMO1 C α :=
  StateT.mk fun st => (fun r => (r.1, { st with base := r.2 })) <$> oa.run st.base

/-- Real `released` after recording signer `i` (Descent:647). -/
abbrev roundTwoReleased (st : TsigState C) (e : KeyIndex) (message : Message) (i : C.Party) : Bool :=
  decide (C.t ≤ (signersAt { st with released := st.released ++ [(e, message, i)] } e message).card)

def firstStart (S : Finset Digit) : Option Digit :=
  (List.finRange chainLength).find? fun d => decide (d ∈ S)

def recordStart (e : KeyIndex) (l : ChainIndex) (pos : Digit) : SourceMO1 C Unit :=
  modify fun st =>
    { st with starts :=
        Function.update st.starts e (Function.update (st.starts e) l (insert pos (st.starts e l))) }

/-- Q from the smallest stored digit; this covers every stored digit. -/
def sourceReleaseCovered (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceMO1 C Unit := do
  match firstStart ((← get).starts e l) with
  | some start => liftBase (sourceReleaseBottomSuffix P seeds e l start)
  | none => pure ()

/-- Keys with a recorded signer whose count reaches `C.t` in this step. -/
def crossedKeys (old new : TsigState C) : List KeyIndex :=
  ((new.released.map (·.1)).dedup).filter fun e => match new.bound e with
    | some m => decide ((signersAt old e m).card < C.t ∧ C.t ≤ (signersAt new e m).card)
    | none => false

/-- Q at every chain of key `e`, each from its smallest stored digit. -/
def sourceReleaseKey (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceMO1 C Unit := do
  let _ ← (List.finRange numChains).mapM fun l => sourceReleaseCovered P seeds e l
  pure ()

/-- The `cpk` values of the real ceremony output of tree `bi`, which read the first commitment job
at a key outside the tree. -/
def patchCpk (bi : Fin (2 ^ layerHeight)) (commitment : KeyIndex → Digest)
    (cpk : KeyIndex → ChainIndex → Digest × Digest × Digest) :
    KeyIndex → ChainIndex → Digest × Digest × Digest :=
  fun e l => if treeOf e = bi then cpk e l else (commitment (bottomKey bi ⟨0, by decide⟩), 0, 0)

/-- A real tree with the `cpk` values of the real ceremony output outside the tree. -/
def patchTree (bi : Fin (2 ^ layerHeight)) (tree : BottomTree) : BottomTree :=
  { tree with cpk := patchCpk bi tree.commitment tree.cpk }

def sourceTsigO1 (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (TsigSpec C) (SourceMO1 C)
  | .corrupt i => do
      let st := (← get).base.signing
      if C.t - 1 < (insert i st.corrupt).card then pure none else
        let new : TsigState C := { st with corrupt := insert i st.corrupt }
        modify fun (s : SourceStateO1 C) => { s with base := { s.base with signing := new } }
        let _ ← (crossedKeys st new).mapM (sourceReleaseKey x.1 x.2.1)
        pure (some (dealtKeys x.1 x.2.1 x.2.2 i))
  | .tree b =>
      (Option.map fun r => (patchTree b r.1, r.2)) <$> liftBase (sourceTsig prims x top (.tree b))
  | .round1 i J e message => liftBase (sourceTsig prims x top (.round1 i J e message))
  | .round2 i J e message parts => do
      let st := (← get).base.signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else
        let atThreshold := roundTwoReleased st e message i
        let some tree ← liftBase (sourceBottomOnce x.1 x.2.1 top (treeOf e)) | pure none
        let own ← liftBase (sourcePart prims x i J (.randomizer bottomLayer e) message)
        let parts := Function.update parts i own
        let some values ← signRound2With (fun oa => liftBase (sourceRoProgram prims x.1 x.2.1 oa))
            (fun p => do
              match p with
              | .chain _ key l pos =>
                  recordStart key l pos
                  if atThreshold then sourceReleaseCovered x.1 x.2.1 key l
              | _ => pure ()
              liftBase (sourcePart prims x i J p message))
            x.1 J (tree.commitment e) e message parts | pure none
        if atThreshold then sourceReleaseKey x.1 x.2.1 e
        modify fun (s : SourceStateO1 C) => { s with base := { s.base with signing :=
          { s.base.signing with released := s.base.signing.released ++ [(e, message, i)] } } }
        pure (some values)

def sourceOraclesO1 (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (LocalSpec C + TsigSpec C) (SourceMO1 C)
  | .inl t => liftBase (sourceOracles prims x top (.inl t))
  | .inr q => do
      let value ← sourceTsigO1 prims x top q
      modify fun (s : SourceStateO1 C) =>
        { s with base := { s.base with exposed := releasedTrees s.base.exposed q } }
      pure value

def sourceGameO1 (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    SourceMO1 C (Bool × TopTree × Forgery) := do
  let top ← liftBase (sourceTopTree x.1 x.2.1)
  let forgery ← simulateQ (sourceOraclesO1 prims x top) (A ⟨top.root, x.1⟩ top)
  let st := (← get).base
  let verifyImpl : QueryImpl HashSpec (SourceMO1 C) := fun input => liftBase (do
    let value ← sourceHash x.1 x.2.1 (.hash input)
    modify fun (s : SourceState C) => { s with candidates :=
      s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
    pure value : SourceM C HashOutput)
  let verified ← simulateQ verifyImpl (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)
  let fresh ← if (signersAt st.signing forgery.signature.leafIndex forgery.message).card < C.t then
    pure true else do
      let honest ← liftBase (sourceHonestSignature prims x top forgery.signature.leafIndex forgery.message)
      pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh, top, forgery)

def sourceProgramO1 (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest)
      ((Bool × TopTree × Forgery) × SourceStateO1 C) :=
  (sourceGameO1 prims A x).run sourceInitO1

abbrev CompilerOutcomeO1 (C : Committee) :=
  ((Bool × TopTree × Forgery) × SourceStateO1 C) ×
    ((CompilerBackend C × ℕ) × (HiddenKey → Option Digest) × Bool)

def compilerRunO1 (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) :
    ProbComp (CompilerOutcomeO1 C) := do
  let s ← $ᵗ (HiddenKey → Digest)
  (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
    (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s)
    (sourceProgramO1 prims A x)).run ((compilerInit, 0), fun _ => none, false)

/-- The left side is A100:1167–1171 verbatim; only the compiler run changes. -/
def CompilerCouplingO1 (prims : Primitives) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr[fun z => SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
      SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
      (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
        SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z) |
      SigningLaneUnionProof.traceRun prims A x] ≤
        Pr[fun r => r.2.2.2 = true ∨ compilerEvent x.1 q r.2.1 | compilerRunO1 prims A x q]

theorem laneTraceCap_of_compilerO1 (prims : Primitives)
    (hstep : CompilerPotentialStep (C := C)) (hcouple : CompilerCouplingO1 (C := C) prims) :
    SigningLaneUnionProof.LaneTraceCap (C := C) prims := by
  intro A q x hx hkeys hq hsmall
  exact SigningCappedExpectProof.probEvent_le_of_capped_expect
    (impl := compilerImpl x.1 x.2.1) (inputSide := deferredInputSide x.1) (p := deferredCounted)
    (run := SigningLaneUnionProof.traceRun prims A x)
    (event := fun z => SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
      SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
      (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
        SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z))
    (keyOf := deferredKey x.1) (point := deferredPoint x.1) (q := q)
    (Inv := CompilerReachable x.1 x.2.1) (f := compilerPotential x.1 q)
    (hinv := fun t st hs r hr => CompilerReachable.step t st r hs hr)
    (hstep := fun t st hs => by
      cases hb : st.1.trace.2 with
      | false => exact hstep x q hsmall t st hs hb
      | true => exact compilerPotential_step_stale x.1 x.2.1 q t st hb)
    (E := compilerEvent x.1 q)
    (hE := compilerEvent_le_potential x.1 q) (oa := sourceProgramO1 prims A x)
    (σ₀ := compilerInit) (hσ₀ := CompilerReachable.initial)
    (hf₀ := compilerPotential_initial x.1 q)
    (hcouple := hcouple A q x hx hkeys hq hsmall)

end ThresholdLeanXmssSecurity.SigningLaneHybridCapO1Proof

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapO1Proof.laneTraceCap_of_compilerO1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningLaneHybridCapO1Proof.laneTraceCap_of_compilerO1
