import ThresholdLeanXmssSecurity.Proof.SigningCompilerCoupling

/-!
# The signing source query alphabet

The four atomic completion sites stay in their constrained point domain.
Raw PRF plants occur only inside expansion of those atomic completions.
The source syntax bound uses VCV-io's structural `IsQueryBound` with an inert
budget; its combinators follow the source field-preservation proof.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShare
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- Exactly the points completed by the four source completion sites. -/
def Constrained : Point → Prop
  | .randomizer lay e => lay = bottomLayer ∨
      (lay = topLayer ∧ ∃ b, e = topKey b)
  | .chain lay e _ p => (lay = bottomLayer ∧ p.val < 3) ∨
      (lay = topLayer ∧ (∃ b, e = topKey b) ∧ p = digit 0)

abbrev CPoint := {p : Point // Constrained p}

@[simp] theorem constrained_bottom_randomizer (e : KeyIndex) :
    Constrained (.randomizer bottomLayer e) := Or.inl rfl

@[simp] theorem constrained_bottom_chain (e : KeyIndex) (l : ChainIndex)
    (p : Digit) (hp : p.val < 3) : Constrained (.chain bottomLayer e l p) :=
  Or.inl ⟨rfl, hp⟩

@[simp] theorem constrained_top_randomizer (b : XmssSecurity.TopIndex) :
    Constrained (.randomizer topLayer (topKey b)) := Or.inr ⟨rfl, b, rfl⟩

@[simp] theorem constrained_top_chain (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    Constrained (.chain topLayer (topKey b) l (digit 0)) :=
  Or.inr ⟨rfl, ⟨b, rfl⟩, rfl⟩

def DeferredAllowed : DeferredQuery C → Prop
  | .plant (.prf ..) _ => False
  | _ => True

def Allowed : (SpecX C).Domain → Prop
  | .inl (.inl (.inl t)) => DeferredAllowed t
  | .inr (p, _) => Constrained p
  | _ => True

/-- VCV-io's structural bound with an inert budget is a query alphabet bound. -/
def Queries {ι α : Type} {spec : OracleSpec ι} (allowed : ι → Prop)
    (oa : OracleComp spec α) : Prop :=
  oa.IsQueryBound () (fun t _ => allowed t) (fun _ _ => ())

namespace Queries
variable {ι α β : Type} {spec : OracleSpec ι} {allowed : ι → Prop}

@[simp] theorem pure (a : α) : Queries allowed (pure a : OracleComp spec α) := trivial

theorem bind {oa : OracleComp spec α} {f : α → OracleComp spec β}
    (h : Queries allowed oa) (hf : ∀ a, Queries allowed (f a)) :
    Queries allowed (oa >>= f) :=
  isQueryBound_bind (fun _ _ => ()) (fun _ _ _ _ h => ⟨h, h⟩)
    (fun _ _ _ _ _ => ⟨rfl, rfl⟩) h hf

@[simp] theorem query (t : ι) (h : allowed t) :
    Queries allowed (liftM (spec.query t) : OracleComp spec _) :=
  (isQueryBound_query_iff ..).mpr h

theorem map (f : α → β) {oa : OracleComp spec α} (h : Queries allowed oa) :
    Queries allowed (f <$> oa) := (isQueryBound_map_iff ..).mpr h

theorem mapM (xs : List α) (f : α → OracleComp spec β)
    (h : ∀ a ∈ xs, Queries allowed (f a)) : Queries allowed (xs.mapM f) := by
  induction xs with
  | nil => exact pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      exact (h a (List.mem_cons_self ..)).bind fun b =>
        (ih fun a ha => h a (List.mem_cons_of_mem _ ha)).bind fun bs => pure (b :: bs)

theorem simulate {κ : Type} {target : OracleSpec κ} {permit : κ → Prop}
    (impl : QueryImpl spec (OracleComp target)) (oa : OracleComp spec α)
    (h : Queries allowed oa) (hi : ∀ t, allowed t → Queries permit (impl t)) :
    Queries permit (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact pure a
  | query_bind t next ih =>
      have hb := (isQueryBound_query_bind_iff ..).mp h
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      exact (hi t hb.1).bind fun a => ih a (hb.2 a)

end Queries

def Safe {α : Type} (oa : SourceMX C α) : Prop :=
  ∀ st, Queries Allowed (oa.run st)

namespace Safe
variable {α β : Type}
@[simp] theorem pure (a : α) : Safe (C := C) (pure a) := fun _ => Queries.pure _
theorem bind {oa : SourceMX C α} {f : α → SourceMX C β}
    (h : Safe oa) (hf : ∀ a, Safe (f a)) : Safe (oa >>= f) :=
  fun st => (h st).bind fun z => hf z.1 z.2
@[simp] theorem get : Safe (get : SourceMX C (SourceState C)) := fun _ => Queries.pure _
@[simp] theorem modify (f : SourceState C → SourceState C) :
    Safe (modify f : SourceMX C Unit) := fun _ => Queries.pure _
theorem lift {oa : OracleComp (SpecX C) α} (h : Queries Allowed oa) :
    Safe (C := C) (liftM oa) := fun st => h.map (fun a => (a, st))
theorem map (f : α → β) {oa : SourceMX C α} (h : Safe oa) : Safe (f <$> oa) :=
  fun st => (h st).map (Prod.map f id)
theorem mapM (xs : List α) (f : α → SourceMX C β)
    (h : ∀ a ∈ xs, Safe (f a)) : Safe (xs.mapM f) := by
  induction xs with
  | nil => exact pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      exact (h a (List.mem_cons_self ..)).bind fun b =>
        (ih fun a ha => h a (List.mem_cons_of_mem _ ha)).bind fun bs => pure (b :: bs)
theorem sequenceFin {n : ℕ} (f : Fin n → SourceMX C α) (h : ∀ a, Safe (f a)) :
    Safe (Concrete.sequenceFin f) := by
  induction n with
  | zero => exact pure _
  | succ n ih =>
      exact (h 0).bind fun a => (ih _ fun i => h i.succ).bind fun as => pure _
theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMX C)) (oa : OracleComp spec α)
    (h : ∀ t, Safe (impl t)) : Safe (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (C := C) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      exact (h t).bind ih
end Safe

@[simp] theorem safe_deferred (t : DeferredQuery C) (h : DeferredAllowed t) :
    Safe (C := C) (liftM (deferredQueryX t)) := Safe.lift (Queries.query _ h)
@[simp] theorem safe_reveal (k : HiddenKey) :
    Safe (C := C) (liftM (revealQueryX (C := C) k)) := Safe.lift (Queries.query _ trivial)
@[simp] theorem safe_mark (b : Bool) :
    Safe (C := C) (liftM (markQ (C := C) b)) := Safe.lift (Queries.query _ trivial)
@[simp] theorem safe_complete (p : Point) (target : Digest) (hp : Constrained p) :
    Safe (C := C) (liftM (completeQ (C := C) p target)) := Safe.lift (Queries.query _ hp)



theorem Safe.simulate_bound {ι α : Type} {spec : OracleSpec ι} {allowed : ι → Prop}
    (impl : QueryImpl spec (SourceMX C)) (oa : OracleComp spec α)
    (h : Queries allowed oa) (hi : ∀ t, allowed t → Safe (impl t)) :
    Safe (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using Safe.pure (C := C) a
  | query_bind t next ih =>
      have hb := (isQueryBound_query_bind_iff ..).mp h
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (hi t hb.1).bind fun a => ih a (hb.2 a)

attribute [local irreducible] Queries Safe

local macro "source_step" : tactic => `(tactic|
  first
    | with_reducible exact Safe.pure _
    | with_reducible exact Safe.get
    | with_reducible exact Safe.modify _
    | (with_reducible refine Safe.bind ?_ (fun a => ?_))
    | with_reducible apply Safe.map
    | (with_reducible apply Safe.mapM; intro a ha)
    | (with_reducible apply Safe.sequenceFin; intro a)
    | with_reducible apply safe_deferred
    | with_reducible apply safe_reveal
    | with_reducible apply safe_mark
    | with_reducible apply safe_complete
    | with_reducible exact constrained_bottom_randomizer _
    | with_reducible exact constrained_top_randomizer _
    | with_reducible exact constrained_top_chain _ _
    | apply constrained_bottom_chain
    | assumption
    | (solve | simp only [DeferredAllowed] | exact Fin.isLt _ | (change _ < 3; exact Fin.isLt _) | omega)
    | split
    | (dsimp only; split))

@[simp] theorem safe_sourceRevealX (k : HiddenKey) : Safe (sourceRevealX (C := C) k) := by
  unfold sourceRevealX
  repeat' source_step

@[simp] theorem safe_sourceRevealDigestX (d : DeferredDigest) :
    Safe (sourceRevealDigestX (C := C) d) := by
  cases d with
  | known value => exact Safe.pure _
  | secret k => exact safe_sourceRevealX k

@[simp] theorem safe_sourcePlantX (P : PublicParameter) (p : PendingInput) :
    Safe (sourcePlantX (C := C) P p) := by
  unfold sourcePlantX
  repeat' first | with_reducible apply safe_sourceRevealX | with_reducible apply safe_sourceRevealDigestX | source_step

@[simp] theorem safe_sourcePendingX (P : PublicParameter) (p : PendingInput) :
    Safe (sourcePendingX (C := C) P p) := by
  unfold sourcePendingX
  repeat' source_step

@[simp] theorem safe_sourceReleaseOpeningX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : Safe (sourceReleaseOpeningX P seeds e) := by
  unfold sourceReleaseOpeningX
  repeat' first | with_reducible apply safe_sourceRevealX | with_reducible apply safe_sourcePlantX | source_step

@[simp] theorem safe_sourceHashX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) : Safe (sourceHashX P seeds q) := by
  unfold sourceHashX
  repeat' first | with_reducible apply safe_sourceReleaseOpeningX | source_step

@[simp] theorem safe_sourceVirtualX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) : Safe (sourceVirtualX P seeds T p) := by
  unfold sourceVirtualX
  repeat' first | with_reducible apply safe_sourceReleaseOpeningX | source_step

@[simp] theorem safe_sourceBackendX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : DeferredQuery C) (h : DeferredAllowed q) : Safe (sourceBackendX P seeds q) := by
  cases q <;> simp only [sourceBackendX]
  all_goals first | with_reducible apply safe_sourceHashX | with_reducible apply safe_sourcePendingX |
    with_reducible apply safe_sourceVirtualX | exact safe_deferred _ h


theorem queries_backend (t : DeferredQuery C) (h : DeferredAllowed t) :
    Queries DeferredAllowed (backendQuery t) := Queries.query t h

local macro "query_step" : tactic => `(tactic|
  first
    | with_reducible exact Queries.pure _
    | (with_reducible refine Queries.bind ?_ (fun a => ?_))
    | with_reducible apply Queries.map
    | (with_reducible apply Queries.mapM; intro a ha)
    | with_reducible apply queries_backend
    | assumption
    | (solve | simp only [DeferredAllowed])
    | split
    | (dsimp only; split))

theorem queries_deferredBottomRow (e : KeyIndex) (l : ChainIndex) :
    Queries DeferredAllowed (deferredBottomRow (C := C) e l) := by
  have calls : ∀ q ∈ bottomRowPrfCalls C e l, DeferredAllowed q := by
    intro q h
    simp only [bottomRowPrfCalls, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, _, T, _, rfl⟩ := h
    trivial
  unfold deferredBottomRow
  repeat' first | with_reducible apply calls; assumption | query_step

theorem queries_deferredTopEnd (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    Queries DeferredAllowed (deferredTopEnd (C := C) b l) := by
  unfold deferredTopEnd
  repeat' query_step

theorem queries_all {ι α : Type} {spec : OracleSpec ι} (oa : OracleComp spec α) :
    Queries (fun _ => True) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact Queries.pure _
  | query_bind t next ih => exact (Queries.query t trivial).bind ih

theorem queries_deferredHash {α : Type} (oa : OracleComp HashSpec α) :
    Queries DeferredAllowed (deferredHash (C := C) oa) :=
  Queries.simulate _ oa (queries_all oa) (fun _ _ => queries_backend _ trivial)

theorem queries_deferredTopTree (P : PublicParameter) :
    Queries DeferredAllowed (deferredTopTree (C := C) P) := by
  unfold deferredTopTree
  repeat' first | with_reducible apply queries_deferredTopEnd | with_reducible apply queries_deferredHash | query_step

@[simp] theorem safe_sourceTopTreeX (P : PublicParameter) (seeds : C.Term → HashOutput) :
    Safe (sourceTopTreeX P seeds) :=
  Safe.simulate_bound (sourceBackendX P seeds) (deferredTopTree P) (queries_deferredTopTree P) (safe_sourceBackendX P seeds)

@[simp] theorem safe_sourceBottomRowX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : Safe (sourceBottomRowX P seeds e l) :=
  Safe.simulate_bound (sourceBackendX P seeds) (deferredBottomRow e l) (queries_deferredBottomRow e l) (safe_sourceBackendX P seeds)

@[simp] theorem safe_sourceHashProgramX {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp HashSpec α) :
    Safe (sourceHashProgramX P seeds oa) :=
  Safe.simulate_bound (sourceBackendX P seeds) (deferredHash oa) (queries_deferredHash oa) (safe_sourceBackendX P seeds)

@[simp] theorem safe_sourceCommitmentX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : Safe (sourceCommitmentX P seeds e) := by
  unfold sourceCommitmentX
  repeat' first | with_reducible apply safe_sourceVirtualX | with_reducible apply safe_sourcePendingX | source_step

@[simp] theorem safe_sourceTopValueX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) : Safe (sourceTopValueX P seeds b l p) := by
  unfold sourceTopValueX
  repeat' first | with_reducible apply safe_sourceVirtualX | with_reducible apply safe_sourcePendingX | source_step

@[simp] theorem safe_sourceTopRecoverX (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (p : Digit) (initial : DeferredDigest) :
    Safe (sourceTopRecoverX (C := C) P b l p initial) := by
  unfold sourceTopRecoverX
  repeat' first | with_reducible apply safe_sourcePendingX | source_step

@[simp] theorem safe_sourceBottomTreeX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : Safe (sourceBottomTreeX P seeds top b) := by
  unfold sourceBottomTreeX
  repeat' first
    | with_reducible apply safe_sourceBottomRowX
    | with_reducible apply safe_sourceCommitmentX
    | with_reducible apply safe_sourceVirtualX
    | with_reducible apply safe_sourceHashProgramX
    | with_reducible apply safe_sourcePendingX
    | with_reducible apply safe_sourceTopValueX
    | with_reducible apply safe_sourceTopRecoverX
    | source_step

@[simp] theorem safe_sourceBottomOnceX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : Safe (sourceBottomOnceX P seeds top b) := by
  unfold sourceBottomOnceX
  repeat' first | with_reducible apply safe_sourceBottomTreeX | source_step

@[simp] theorem safe_sourceReleaseBottomSuffixX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    Safe (sourceReleaseBottomSuffixX P seeds e l start) := by
  unfold sourceReleaseBottomSuffixX
  repeat' first | with_reducible apply safe_sourceRevealX | with_reducible apply safe_sourcePlantX | source_step
  all_goals
    rename_i pos hpos value branch offset
    exact pos.isLt

@[simp] theorem safe_sourceReturnTreeX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) : Safe (sourceReturnTreeX P seeds b tree) := by
  unfold sourceReturnTreeX
  repeat' first
    | with_reducible apply safe_sourceRevealX
    | with_reducible apply safe_sourceRevealDigestX
    | with_reducible apply safe_sourcePlantX
    | source_step

@[simp] theorem safe_sourceRoX (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : (RoSpec C).Domain) : Safe (sourceRoX prims P seeds q) := by
  cases q <;> unfold sourceRoX
  all_goals repeat' first | with_reducible apply safe_sourceHashX | source_step

@[simp] theorem safe_sourceRoProgramX {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp (RoSpec C) α) :
    Safe (sourceRoProgramX prims P seeds oa) := Safe.simulate _ _ (safe_sourceRoX prims P seeds)

@[simp] theorem safe_sourcePartX (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) : Safe (sourcePartX prims x i J p message) :=
  safe_sourceRoProgramX prims x.1 x.2.1 _

@[simp] theorem safe_sourceTsigX (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : TsigQuery C) : Safe (sourceTsigX prims x top q) := by
  cases q <;> unfold sourceTsigX
  all_goals repeat' first
    | with_reducible apply safe_sourceBottomOnceX
    | with_reducible apply safe_sourceReturnTreeX
    | with_reducible apply safe_sourceRoProgramX
    | with_reducible apply safe_sourceReleaseOpeningX
    | with_reducible apply safe_sourcePartX
    | with_reducible apply safe_sourceReleaseBottomSuffixX
    | (unfold signRound2With)
    | source_step

@[simp] theorem safe_sourceLocalX (prims : Primitives) (x : Keys3 C)
    (q : (LocalSpec C).Domain) : Safe (sourceLocalX prims x q) := by
  cases q <;> unfold sourceLocalX
  all_goals first | exact safe_deferred _ trivial | with_reducible apply safe_sourceRoX

@[simp] theorem safe_sourceOraclesX (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : (LocalSpec C + TsigSpec C).Domain) : Safe (sourceOraclesX prims x top q) := by
  cases q <;> unfold sourceOraclesX
  all_goals repeat' first | with_reducible apply safe_sourceLocalX | with_reducible apply safe_sourceTsigX | source_step

@[simp] theorem safe_sourceHonestSignatureX (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (e : KeyIndex) (message : Message) : Safe (sourceHonestSignatureX prims x top e message) := by
  unfold sourceHonestSignatureX
  repeat' first
    | with_reducible apply safe_sourceBottomTreeX
    | with_reducible apply safe_sourceReleaseOpeningX
    | with_reducible apply safe_sourceRoProgramX
    | with_reducible apply safe_sourceReleaseBottomSuffixX
    | with_reducible apply safe_sourceHashProgramX
    | with_reducible apply safe_sourceRevealDigestX
    | source_step

@[simp] theorem safe_sourceGameX (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    Safe (sourceGameX prims A x) := by
  unfold sourceGameX
  repeat' first
    | with_reducible apply safe_sourceTopTreeX
    | with_reducible apply safe_sourceOraclesX
    | with_reducible apply safe_sourceHashX
    | with_reducible apply safe_sourceHonestSignatureX
    | (with_reducible apply Safe.simulate; intro t)
    | source_step

/-- The actual source has no raw PRF plants and completes only constrained points. -/
theorem sourceProgramX_allowed (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    Queries Allowed (sourceProgramX prims A x) := by
  have h := safe_sourceGameX prims A x
  unfold Safe at h
  exact h sourceInit

end ThresholdLeanXmssSecurity.SigningCompilerShare

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.queries_deferredTopTree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.queries_deferredTopTree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.safe_sourceTsigX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.safe_sourceTsigX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.sourceProgramX_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.sourceProgramX_allowed
