import ThresholdLeanXmssSecurity.Proof.SigningLaneHybridCapO1
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareSource

/-! # Atomic source syntax for the threshold-guarded compiler

The X source preserves the corrected O1 control flow and stores digits through
its base-state lens. Atomic completions expand to the original O1 source,
including its entire final state. Marks occur at the original call boundaries.
The query alphabet excludes raw PRF plants and constrains all completion points.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof SigningCompilerShare
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

abbrev SourceMXO1 (C : Committee) := StateT (SourceStateO1 C) (OracleComp (SpecX C))

def liftBaseX {α : Type} (oa : SourceMX C α) : SourceMXO1 C α :=
  StateT.mk fun st => (fun r => (r.1, { st with base := r.2 })) <$> oa.run st.base

def recordStartX (e : KeyIndex) (l : ChainIndex) (pos : Digit) : SourceMXO1 C Unit :=
  modify fun st =>
    { st with starts :=
        Function.update st.starts e (Function.update (st.starts e) l (insert pos (st.starts e l))) }

/-- Q from the smallest stored digit; this covers every stored digit. -/
def sourceReleaseCoveredX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceMXO1 C Unit := do
  match firstStart ((← get).starts e l) with
  | some start => liftBaseX (sourceReleaseBottomSuffixX P seeds e l start)
  | none => pure ()

/-- Q at every chain of key `e`, each from its smallest stored digit. -/
def sourceReleaseKeyX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceMXO1 C Unit := do
  let _ ← (List.finRange numChains).mapM fun l => sourceReleaseCoveredX P seeds e l
  pure ()

def sourceTsigO1X (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (TsigSpec C) (SourceMXO1 C)
  | .corrupt i => do
      let st := (← get).base.signing
      if C.t - 1 < (insert i st.corrupt).card then pure none else
        let new : TsigState C := { st with corrupt := insert i st.corrupt }
        modify fun (s : SourceStateO1 C) => { s with base := { s.base with signing := new } }
        let _ ← (crossedKeys st new).mapM (sourceReleaseKeyX x.1 x.2.1)
        pure (some (dealtKeys x.1 x.2.1 x.2.2 i))
  | .tree b => liftBaseX (sourceTsigX prims x top (.tree b))
  | .round1 i J e message => liftBaseX (sourceTsigX prims x top (.round1 i J e message))
  | .round2 i J e message parts => do
      let st := (← get).base.signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else
        let atThreshold := roundTwoReleased st e message i
        let some tree ← liftBaseX (sourceBottomOnceX x.1 x.2.1 top (treeOf e)) | pure none
        let own ← liftBaseX (sourcePartX prims x i J (.randomizer bottomLayer e) message)
        let parts := Function.update parts i own
        let some values ← signRound2With (fun oa => liftBaseX (sourceRoProgramX prims x.1 x.2.1 oa))
            (fun p => do
              match p with
              | .chain _ key l pos =>
                  recordStartX key l pos
                  if atThreshold then sourceReleaseCoveredX x.1 x.2.1 key l
              | _ => pure ()
              liftBaseX (sourcePartX prims x i J p message))
            x.1 J (tree.commitment e) e message parts | pure none
        if atThreshold then sourceReleaseKeyX x.1 x.2.1 e
        modify fun (s : SourceStateO1 C) => { s with base := { s.base with signing :=
          { s.base.signing with released := s.base.signing.released ++ [(e, message, i)] } } }
        pure (some values)

def sourceOraclesO1X (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (LocalSpec C + TsigSpec C) (SourceMXO1 C)
  | .inl t => liftBaseX (sourceOraclesX prims x top (.inl t))
  | .inr q => do
      let _ ← liftM (markQ (C := C) (← get).base.hiddenFlag)
      let value ← sourceTsigO1X prims x top q
      modify fun (s : SourceStateO1 C) =>
        { s with base := { s.base with exposed := releasedTrees s.base.exposed q } }
      pure value

def sourceGameO1X (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    SourceMXO1 C (Bool × TopTree × Forgery) := do
  let _ ← liftM (markQ (C := C) (← get).base.hiddenFlag)
  let top ← liftBaseX (sourceTopTreeX x.1 x.2.1)
  let forgery ← simulateQ (sourceOraclesO1X prims x top) (A ⟨top.root, x.1⟩ top)
  let st := (← get).base
  let _ ← liftM (markQ (C := C) st.hiddenFlag)
  let verifyImpl : QueryImpl HashSpec (SourceMXO1 C) := fun input => liftBaseX (do
    let value ← sourceHashX x.1 x.2.1 (.hash input)
    modify fun (s : SourceState C) => { s with candidates :=
      s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
    pure value : SourceMX C HashOutput)
  let verified ← simulateQ verifyImpl (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)
  let fresh ← if (signersAt st.signing forgery.signature.leafIndex forgery.message).card < C.t then
    pure true else do
      let honest ← liftBaseX (sourceHonestSignatureX prims x top forgery.signature.leafIndex forgery.message)
      pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh, top, forgery)

def sourceProgramO1X (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    OracleComp (SpecX C) ((Bool × TopTree × Forgery) × SourceStateO1 C) :=
  (sourceGameO1X prims A x).run sourceInitO1

def mapXO1 (seeds : C.Term → HashOutput) {α : Type} (p : SourceMXO1 C α) : SourceMO1 C α :=
  StateT.mk fun st => simulateQ (expand seeds) (p.run st)

@[simp] theorem mapXO1_pure (seeds : C.Term → HashOutput) {α : Type} (a : α) :
    mapXO1 seeds (pure a) = pure a := by
  funext st
  simp [mapXO1, StateT.run_pure]

@[simp] theorem mapXO1_bind (seeds : C.Term → HashOutput) {α β : Type}
    (p : SourceMXO1 C α) (f : α → SourceMXO1 C β) :
    mapXO1 seeds (p >>= f) = (mapXO1 seeds p >>= fun a => mapXO1 seeds (f a)) := by
  funext st
  change simulateQ (expand seeds) (p.run st >>= fun z => (f z.1).run z.2) = _
  rw [simulateQ_bind]
  rfl

@[simp] theorem mapXO1_get (seeds : C.Term → HashOutput) :
    mapXO1 seeds (get : SourceMXO1 C (SourceStateO1 C)) = get := by
  funext st
  rfl

@[simp] theorem mapXO1_modify (seeds : C.Term → HashOutput) (f : SourceStateO1 C → SourceStateO1 C) :
    mapXO1 seeds (modify f) = modify f := by
  funext st
  rfl

@[simp] theorem mapXO1_lift (seeds : C.Term → HashOutput) {α : Type} (p : OracleComp (SpecX C) α) :
    mapXO1 seeds (liftM p) = liftM (simulateQ (expand seeds) p) := by
  funext st
  change simulateQ (expand seeds) ((fun a => (a, st)) <$> p) = _
  rw [simulateQ_map]
  rfl

@[simp] theorem mapXO1_map (seeds : C.Term → HashOutput) {α β : Type}
    (f : α → β) (p : SourceMXO1 C α) :
    mapXO1 seeds (f <$> p) = f <$> mapXO1 seeds p := by
  simp only [map_eq_bind_pure_comp, mapXO1_bind, mapXO1_pure, Function.comp_def]

@[simp] theorem mapXO1_ite (seeds : C.Term → HashOutput) {α : Type}
    (p : Prop) [Decidable p] (x y : SourceMXO1 C α) :
    mapXO1 seeds (if p then x else y) = if p then mapXO1 seeds x else mapXO1 seeds y := by
  split <;> rfl

@[simp] theorem mapXO1_mapM (seeds : C.Term → HashOutput) {α β : Type}
    (xs : List α) (f : α → SourceMXO1 C β) :
    mapXO1 seeds (xs.mapM f) = xs.mapM (fun a => mapXO1 seeds (f a)) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.mapM_cons, ih]

@[simp] theorem mapXO1_sequenceFin (seeds : C.Term → HashOutput) {α : Type} {n : ℕ}
    (f : Fin n → SourceMXO1 C α) :
    mapXO1 seeds (Concrete.sequenceFin f) = Concrete.sequenceFin (fun a => mapXO1 seeds (f a)) := by
  induction n with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih => simp [Concrete.sequenceFin, ih]

theorem mapXO1_simulateQ (seeds : C.Term → HashOutput) {ι α : Type} {spec : OracleSpec ι}
    (implX : QueryImpl spec (SourceMXO1 C)) (impl : QueryImpl spec (SourceMO1 C))
    (h : ∀ t, mapXO1 seeds (implX t) = impl t) (oa : OracleComp spec α) :
    mapXO1 seeds (simulateQ implX oa) = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, mapXO1_bind, h, ih]

@[simp] theorem mapXO1_simulate (seeds : C.Term → HashOutput) {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMXO1 C)) (oa : OracleComp spec α) :
    mapXO1 seeds (simulateQ impl oa) = simulateQ (fun t => mapXO1 seeds (impl t)) oa :=
  mapXO1_simulateQ seeds _ _ (fun _ => rfl) oa

@[simp] theorem mapXO1_liftBaseX (seeds : C.Term → HashOutput) {α : Type}
    (oa : SourceMX C α) : mapXO1 seeds (liftBaseX oa) = liftBase (mapX seeds oa) := by
  funext st
  simp [mapXO1, liftBaseX, liftBase, mapX, simulateQ_map]

@[simp] theorem sourceGetO1_ignore {α : Type} (p : SourceMO1 C α) :
    ((get : SourceMO1 C (SourceStateO1 C)) >>= fun _ => p) = p := by
  funext st
  change (pure (st, st) >>= fun z => p.run z.2) = p.run st
  simp

@[simp] theorem mapXO1_recordStart (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (pos : Digit) :
    mapXO1 seeds (recordStartX e l pos) = recordStart e l pos := by
  simp [recordStartX, recordStart]

@[simp] theorem mapXO1_sourceReleaseCovered (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) :
    mapXO1 seeds (sourceReleaseCoveredX P seeds e l) = sourceReleaseCovered P seeds e l := by
  simp only [sourceReleaseCoveredX, sourceReleaseCovered, mapXO1_bind, mapXO1_get]
  congr 1
  funext st
  cases firstStart (st.starts e l) <;> simp

@[simp] theorem mapXO1_sourceReleaseKey (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : mapXO1 seeds (sourceReleaseKeyX P seeds e) = sourceReleaseKey P seeds e := by
  simp [sourceReleaseKeyX, sourceReleaseKey]

@[simp] theorem mapXO1_sourceTsig (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : (TsigSpec C).Domain) : mapXO1 x.2.1 (sourceTsigO1X prims x top q) = sourceTsigO1 prims x top q := by
  cases q <;> simp [sourceTsigO1X, sourceTsigO1, signRound2With]
  case round2 i J e message parts =>
    congr 1
    funext st
    split
    · rfl
    · simp_all
      congr 1
      funext answer
      cases answer with
      | none => simp
      | some tree =>
          simp
          congr 1
          funext own
          congr 1
          funext codeword
          rcases codeword with _ | ⟨randomness, encoding⟩ <;> simp

@[simp] theorem mapXO1_sourceOracles (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : (LocalSpec C + TsigSpec C).Domain) :
    mapXO1 x.2.1 (sourceOraclesO1X prims x top q) = sourceOraclesO1 prims x top q := by
  cases q with
  | inl t =>
      change mapXO1 x.2.1 (liftBaseX (sourceOraclesX prims x top (.inl t))) = _
      rw [mapXO1_liftBaseX, mapX_sourceOracles]
      rfl
  | inr q => simp [sourceOraclesO1X, sourceOraclesO1]

@[simp] theorem mapXO1_sourceGame (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    mapXO1 x.2.1 (sourceGameO1X prims A x) = sourceGameO1 prims A x := by
  simp [sourceGameO1X, sourceGameO1]

/-- Expansion recovers the entire corrected O1 program without a premise. -/
theorem sourceProgramO1_eq_expand (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    sourceProgramO1 prims A x = simulateQ (expand x.2.1) (sourceProgramO1X prims A x) := by
  exact (congrArg (fun p => p.run sourceInitO1) (mapXO1_sourceGame prims A x)).symm

def SafeO1 {α : Type} (oa : SourceMXO1 C α) : Prop :=
  ∀ st, Queries Allowed (oa.run st)

namespace SafeO1
variable {α β : Type}
@[simp] theorem pure (a : α) : SafeO1 (C := C) (pure a) := fun _ => Queries.pure _
theorem bind {oa : SourceMXO1 C α} {f : α → SourceMXO1 C β}
    (h : SafeO1 oa) (hf : ∀ a, SafeO1 (f a)) : SafeO1 (oa >>= f) :=
  fun st => (h st).bind fun z => hf z.1 z.2
@[simp] theorem get : SafeO1 (get : SourceMXO1 C (SourceStateO1 C)) := fun _ => Queries.pure _
@[simp] theorem modify (f : SourceStateO1 C → SourceStateO1 C) :
    SafeO1 (modify f : SourceMXO1 C Unit) := fun _ => Queries.pure _
theorem lift {oa : OracleComp (SpecX C) α} (h : Queries Allowed oa) :
    SafeO1 (C := C) (liftM oa) := fun st => h.map (fun a => (a, st))
theorem map (f : α → β) {oa : SourceMXO1 C α} (h : SafeO1 oa) : SafeO1 (f <$> oa) :=
  fun st => (h st).map (Prod.map f id)
theorem mapM (xs : List α) (f : α → SourceMXO1 C β)
    (h : ∀ a ∈ xs, SafeO1 (f a)) : SafeO1 (xs.mapM f) := by
  induction xs with
  | nil => exact pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      exact (h a (List.mem_cons_self ..)).bind fun b =>
        (ih fun a ha => h a (List.mem_cons_of_mem _ ha)).bind fun bs => pure (b :: bs)
theorem sequenceFin {n : ℕ} (f : Fin n → SourceMXO1 C α) (h : ∀ a, SafeO1 (f a)) :
    SafeO1 (Concrete.sequenceFin f) := by
  induction n with
  | zero => exact pure _
  | succ n ih =>
      exact (h 0).bind fun a => (ih _ fun i => h i.succ).bind fun as => pure _
theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMXO1 C)) (oa : OracleComp spec α)
    (h : ∀ t, SafeO1 (impl t)) : SafeO1 (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (C := C) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      exact (h t).bind ih
end SafeO1

theorem safe_liftBaseX {α : Type} {oa : SourceMX C α} (h : Safe oa) :
    SafeO1 (liftBaseX oa) := fun st => (h st.base).map _

@[simp] theorem safe_markO1 (b : Bool) : SafeO1 (C := C) (liftM (markQ (C := C) b)) :=
  SafeO1.lift (Queries.query _ trivial)

attribute [local irreducible] SafeO1

-- The structural combinators are ports of SigningCompilerShareSource.Safe.
local macro "o1_step" : tactic => `(tactic|
  first
    | with_reducible exact SafeO1.pure _
    | with_reducible exact SafeO1.get
    | with_reducible exact SafeO1.modify _
    | (with_reducible refine SafeO1.bind ?_ (fun a => ?_))
    | with_reducible apply SafeO1.map
    | (with_reducible apply SafeO1.mapM; intro a ha)
    | (with_reducible apply SafeO1.sequenceFin; intro a)
    | with_reducible apply safe_liftBaseX
    | with_reducible apply safe_markO1
    | assumption
    | split
    | (dsimp only; split))

@[simp] theorem safe_recordStartX (e : KeyIndex) (l : ChainIndex) (pos : Digit) :
    SafeO1 (recordStartX (C := C) e l pos) := SafeO1.modify _

@[simp] theorem safe_sourceReleaseCoveredX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SafeO1 (sourceReleaseCoveredX P seeds e l) := by
  unfold sourceReleaseCoveredX
  repeat' first | with_reducible apply safe_sourceReleaseBottomSuffixX | o1_step

@[simp] theorem safe_sourceReleaseKeyX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SafeO1 (sourceReleaseKeyX P seeds e) := by
  unfold sourceReleaseKeyX
  repeat' first | with_reducible apply safe_sourceReleaseCoveredX | o1_step

@[simp] theorem safe_sourceTsigO1X (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : TsigQuery C) : SafeO1 (sourceTsigO1X prims x top q) := by
  cases q <;> unfold sourceTsigO1X
  all_goals repeat' first
    | with_reducible apply safe_sourceTsigX
    | with_reducible apply safe_sourceBottomOnceX
    | with_reducible apply safe_sourcePartX
    | with_reducible apply safe_sourceRoProgramX
    | with_reducible apply safe_recordStartX
    | with_reducible apply safe_sourceReleaseCoveredX
    | with_reducible apply safe_sourceReleaseKeyX
    | unfold signRound2With
    | o1_step

@[simp] theorem safe_sourceOraclesO1X (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : (LocalSpec C + TsigSpec C).Domain) : SafeO1 (sourceOraclesO1X prims x top q) := by
  cases q <;> unfold sourceOraclesO1X
  all_goals repeat' first
    | with_reducible apply safe_sourceOraclesX
    | with_reducible apply safe_sourceTsigO1X
    | o1_step

theorem safe_verifyBaseX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (f : SourceState C → SourceState C) (input : HashSpec.Domain) :
    Safe (do
      let value ← sourceHashX P seeds (.hash input)
      modify f
      pure value : SourceMX C HashOutput) :=
  (safe_sourceHashX P seeds _).bind fun _ => (Safe.modify f).bind fun _ => Safe.pure _

attribute [local irreducible] sourceTopTreeX sourceOraclesO1X sourceHonestSignatureX

@[simp] theorem safe_sourceGameO1X (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    SafeO1 (sourceGameO1X prims A x) := by
  unfold sourceGameO1X
  refine SafeO1.get.bind fun st₀ => ?_
  refine (safe_markO1 st₀.base.hiddenFlag).bind fun _ => ?_
  refine (safe_liftBaseX (safe_sourceTopTreeX x.1 x.2.1)).bind fun top => ?_
  refine (SafeO1.simulate _ _ (safe_sourceOraclesO1X prims x top)).bind fun forgery => ?_
  refine SafeO1.get.bind fun st => ?_
  refine (safe_markO1 st.base.hiddenFlag).bind fun _ => ?_
  refine (SafeO1.simulate _ _ (fun input => safe_liftBaseX (safe_verifyBaseX x.1 x.2.1 _ input))).bind fun verified => ?_
  dsimp only
  split
  · exact (SafeO1.pure _).bind fun _ => SafeO1.pure _
  · exact (safe_liftBaseX (safe_sourceHonestSignatureX prims x top _ _)).bind fun _ =>
      (SafeO1.pure _).bind fun _ => SafeO1.pure _

/-- O1 introduces no raw PRF plants or unconstrained completion points. -/
theorem sourceProgramO1X_allowed (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    Queries Allowed (sourceProgramO1X prims A x) := by
  have h := safe_sourceGameO1X prims A x
  unfold SafeO1 at h
  exact h sourceInitO1

end ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_ite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_ite

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_mapM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sequenceFin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_simulateQ

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_simulate

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_liftBaseX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_liftBaseX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.sourceGetO1_ignore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.sourceGetO1_ignore

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_recordStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_recordStart

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceReleaseCovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceReleaseCovered

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceReleaseKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceReleaseKey

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceTsig' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceTsig

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceOracles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceOracles

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.mapXO1_sourceGame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.sourceProgramO1_eq_expand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.sourceProgramO1_eq_expand

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.modify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.lift

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.simulate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.SafeO1.simulate

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_liftBaseX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_liftBaseX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_markO1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_markO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_recordStartX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_recordStartX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceReleaseCoveredX' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceReleaseCoveredX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceReleaseKeyX' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceReleaseKeyX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceTsigO1X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceTsigO1X

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceOraclesO1X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceOraclesO1X

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_verifyBaseX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_verifyBaseX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceGameO1X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.safe_sourceGameO1X

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.sourceProgramO1X_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SourceProof.sourceProgramO1X_allowed
