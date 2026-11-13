import ThresholdLeanXmssSecurity.Proof.SigningCompilerShare

/-!
# Signing source marks and share tags

Quiet source segments emit no marks and retain hiddenFlag for every oracle answer.
A call's leading mark equals its final flag, including a local hit marked before
its flag update. Generic share handlers retain the tag of the first bad event.
The source invariants are a bounded X port of SourceKeeps; query syntax follows
SigningCompilerShareSource. Support transport uses VCV-io's stateful inclusion.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShare.Marks
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
attribute [local irreducible] sourceProgramX sourceProgram sourceGameX sourceGame

def NoMark : (SpecX C).Domain → Prop
  | .inl (.inr _) => False
  | _ => True

def Quiet {α : Type} (oa : SourceMX C α) : Prop :=
  ∀ st, Queries NoMark (oa.run st) ∧
    ∀ r ∈ support (oa.run st), r.2.hiddenFlag = st.hiddenFlag

namespace Quiet
variable {α β : Type}
@[simp] theorem pure (a : α) : Quiet (C := C) (pure a) := by
  intro st
  refine ⟨Queries.pure _, ?_⟩
  intro r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  rfl
@[simp] theorem get : Quiet (get : SourceMX C (SourceState C)) := by
  intro st
  refine ⟨Queries.pure _, ?_⟩
  intro r hr
  simp only [StateT.run_get, mem_support_pure_iff] at hr
  subst r
  rfl
theorem modify (f : SourceState C → SourceState C)
    (hf : ∀ st, (f st).hiddenFlag = st.hiddenFlag) : Quiet (modify f : SourceMX C Unit) := by
  intro st
  refine ⟨Queries.pure _, ?_⟩
  intro r hr
  have h : r = ((), f st) := by simpa only [StateT.run_modify, mem_support_pure_iff] using hr
  simpa only [h] using hf st
theorem bind {oa : SourceMX C α} {f : α → SourceMX C β}
    (h : Quiet oa) (hf : ∀ a, Quiet (f a)) : Quiet (oa >>= f) := by
  intro st
  refine ⟨(h st).1.bind (fun z => (hf z.1 z.2).1), ?_⟩
  intro r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact ((hf a.1 a.2).2 r hr).trans ((h st).2 a ha)
theorem lift {oa : OracleComp (SpecX C) α} (h : Queries NoMark oa) :
    Quiet (C := C) (liftM oa) := by
  intro st
  refine ⟨h.map (fun a => (a, st)), ?_⟩
  intro r hr
  change r ∈ support ((fun a => (a, st)) <$> oa) at hr
  obtain ⟨a, _, rfl⟩ := mem_support_map_peel _ _ hr
  rfl
theorem map (f : α → β) {oa : SourceMX C α} (h : Quiet oa) : Quiet (f <$> oa) := by
  simpa only [bind_pure_comp] using h.bind (fun a => pure (f a))
theorem mapM (xs : List α) (f : α → SourceMX C β)
    (h : ∀ a ∈ xs, Quiet (f a)) : Quiet (xs.mapM f) := by
  induction xs with
  | nil => exact pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      exact (h a (List.mem_cons_self ..)).bind fun b =>
        (ih fun a ha => h a (List.mem_cons_of_mem _ ha)).bind fun bs => pure (b :: bs)
theorem sequenceFin {n : ℕ} (f : Fin n → SourceMX C α) (h : ∀ a, Quiet (f a)) :
    Quiet (Concrete.sequenceFin f) := by
  induction n with
  | zero => exact pure _
  | succ n ih =>
      exact (h 0).bind fun a => (ih _ fun i => h i.succ).bind fun as => pure _
theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMX C)) (oa : OracleComp spec α)
    (h : ∀ t, Quiet (impl t)) : Quiet (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (C := C) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (h t).bind ih
end Quiet

@[simp] theorem quiet_deferred (t : DeferredQuery C) :
    Quiet (C := C) (liftM (deferredQueryX t)) := Quiet.lift (Queries.query _ trivial)
@[simp] theorem quiet_reveal (k : HiddenKey) :
    Quiet (C := C) (liftM (revealQueryX (C := C) k)) := Quiet.lift (Queries.query _ trivial)
@[simp] theorem quiet_complete (p : Point) (target : Digest) :
    Quiet (C := C) (liftM (completeQ (C := C) p target)) := Quiet.lift (Queries.query _ trivial)

attribute [local irreducible] Queries Quiet

/- The source helper's structural macro, with the SourceKeeps modify premise. -/
local macro "quiet_step" : tactic => `(tactic|
  first
    | with_reducible exact Quiet.pure _
    | with_reducible exact Quiet.get
    | (with_reducible refine Quiet.modify _ ?_; intro st; rfl)
    | (with_reducible refine Quiet.bind ?_ (fun a => ?_))
    | with_reducible apply Quiet.map
    | (with_reducible apply Quiet.mapM; intro a ha)
    | (with_reducible apply Quiet.sequenceFin; intro a)
    | with_reducible apply quiet_deferred
    | with_reducible apply quiet_reveal
    | with_reducible apply quiet_complete
    | assumption
    | split
    | (dsimp only; split))

@[simp] theorem quiet_sourceRevealX (k : HiddenKey) : Quiet (sourceRevealX (C := C) k) := by
  unfold sourceRevealX
  repeat' quiet_step

@[simp] theorem quiet_sourceRevealDigestX (d : DeferredDigest) :
    Quiet (sourceRevealDigestX (C := C) d) := by
  cases d with
  | known value => exact Quiet.pure _
  | secret k => exact quiet_sourceRevealX k

@[simp] theorem quiet_sourcePlantX (P : PublicParameter) (p : PendingInput) :
    Quiet (sourcePlantX (C := C) P p) := by
  unfold sourcePlantX
  repeat' first | with_reducible apply quiet_sourceRevealX | with_reducible apply quiet_sourceRevealDigestX | quiet_step

@[simp] theorem quiet_sourcePendingX (P : PublicParameter) (p : PendingInput) :
    Quiet (sourcePendingX (C := C) P p) := by
  unfold sourcePendingX
  repeat' quiet_step

@[simp] theorem quiet_sourceReleaseOpeningX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : Quiet (sourceReleaseOpeningX P seeds e) := by
  unfold sourceReleaseOpeningX
  repeat' first | with_reducible apply quiet_sourceRevealX | with_reducible apply quiet_sourcePlantX | quiet_step

@[simp] theorem quiet_sourceHashX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) : Quiet (sourceHashX P seeds q) := by
  unfold sourceHashX
  repeat' first | with_reducible apply quiet_sourceReleaseOpeningX | quiet_step

@[simp] theorem quiet_sourceVirtualX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) : Quiet (sourceVirtualX P seeds T p) := by
  unfold sourceVirtualX
  repeat' first | with_reducible apply quiet_sourceReleaseOpeningX | quiet_step

@[simp] theorem quiet_sourceBackendX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : DeferredQuery C) : Quiet (sourceBackendX P seeds q) := by
  cases q <;> simp only [sourceBackendX]
  all_goals first | with_reducible apply quiet_sourceHashX | with_reducible apply quiet_sourcePendingX |
    with_reducible apply quiet_sourceVirtualX | exact quiet_deferred _

@[simp] theorem quiet_sourceTopTreeX (P : PublicParameter) (seeds : C.Term → HashOutput) :
    Quiet (sourceTopTreeX P seeds) := Quiet.simulate _ _ (quiet_sourceBackendX P seeds)
@[simp] theorem quiet_sourceBottomRowX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : Quiet (sourceBottomRowX P seeds e l) :=
  Quiet.simulate _ _ (quiet_sourceBackendX P seeds)
@[simp] theorem quiet_sourceHashProgramX {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp HashSpec α) :
    Quiet (sourceHashProgramX P seeds oa) := Quiet.simulate _ _ (quiet_sourceBackendX P seeds)

@[simp] theorem quiet_sourceCommitmentX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : Quiet (sourceCommitmentX P seeds e) := by
  unfold sourceCommitmentX
  repeat' first | with_reducible apply quiet_sourceVirtualX | with_reducible apply quiet_sourcePendingX | quiet_step

@[simp] theorem quiet_sourceTopValueX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) : Quiet (sourceTopValueX P seeds b l p) := by
  unfold sourceTopValueX
  repeat' first | with_reducible apply quiet_sourceVirtualX | with_reducible apply quiet_sourcePendingX | quiet_step

@[simp] theorem quiet_sourceTopRecoverX (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (p : Digit) (initial : DeferredDigest) :
    Quiet (sourceTopRecoverX (C := C) P b l p initial) := by
  unfold sourceTopRecoverX
  repeat' first | with_reducible apply quiet_sourcePendingX | quiet_step

@[simp] theorem quiet_sourceBottomTreeX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : Quiet (sourceBottomTreeX P seeds top b) := by
  unfold sourceBottomTreeX
  repeat' first
    | with_reducible apply quiet_sourceBottomRowX
    | with_reducible apply quiet_sourceCommitmentX
    | with_reducible apply quiet_sourceVirtualX
    | with_reducible apply quiet_sourceHashProgramX
    | with_reducible apply quiet_sourcePendingX
    | with_reducible apply quiet_sourceTopValueX
    | with_reducible apply quiet_sourceTopRecoverX
    | quiet_step

@[simp] theorem quiet_sourceBottomOnceX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : Quiet (sourceBottomOnceX P seeds top b) := by
  unfold sourceBottomOnceX
  repeat' first | with_reducible apply quiet_sourceBottomTreeX | quiet_step

@[simp] theorem quiet_sourceReleaseBottomSuffixX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    Quiet (sourceReleaseBottomSuffixX P seeds e l start) := by
  unfold sourceReleaseBottomSuffixX
  repeat' first | with_reducible apply quiet_sourceRevealX | with_reducible apply quiet_sourcePlantX | quiet_step

@[simp] theorem quiet_sourceReturnTreeX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) : Quiet (sourceReturnTreeX P seeds b tree) := by
  unfold sourceReturnTreeX
  repeat' first
    | with_reducible apply quiet_sourceRevealX
    | with_reducible apply quiet_sourceRevealDigestX
    | with_reducible apply quiet_sourcePlantX
    | quiet_step

@[simp] theorem quiet_sourceRoX (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : (RoSpec C).Domain) : Quiet (sourceRoX prims P seeds q) := by
  cases q <;> unfold sourceRoX
  all_goals repeat' first | with_reducible apply quiet_sourceHashX | quiet_step

@[simp] theorem quiet_sourceRoProgramX {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp (RoSpec C) α) :
    Quiet (sourceRoProgramX prims P seeds oa) := Quiet.simulate _ _ (quiet_sourceRoX prims P seeds)

@[simp] theorem quiet_sourcePartX (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) : Quiet (sourcePartX prims x i J p message) :=
  quiet_sourceRoProgramX prims x.1 x.2.1 _

@[simp] theorem quiet_sourceTsigX (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : TsigQuery C) : Quiet (sourceTsigX prims x top q) := by
  cases q <;> unfold sourceTsigX
  all_goals repeat' first
    | with_reducible apply quiet_sourceBottomOnceX
    | with_reducible apply quiet_sourceReturnTreeX
    | with_reducible apply quiet_sourceRoProgramX
    | with_reducible apply quiet_sourceReleaseOpeningX
    | with_reducible apply quiet_sourcePartX
    | with_reducible apply quiet_sourceReleaseBottomSuffixX
    | (unfold signRound2With)
    | quiet_step

@[simp] theorem quiet_sourceLocalX (prims : Primitives) (x : Keys3 C)
    (q : (LocalSpec C).Domain) : Quiet (sourceLocalX prims x q) := by
  cases q <;> unfold sourceLocalX
  all_goals first | exact quiet_deferred _ | with_reducible apply quiet_sourceRoX

@[simp] theorem quiet_sourceHonestSignatureX (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (e : KeyIndex) (message : Message) : Quiet (sourceHonestSignatureX prims x top e message) := by
  unfold sourceHonestSignatureX
  repeat' first
    | with_reducible apply quiet_sourceBottomTreeX
    | with_reducible apply quiet_sourceReleaseOpeningX
    | with_reducible apply quiet_sourceRoProgramX
    | with_reducible apply quiet_sourceReleaseBottomSuffixX
    | with_reducible apply quiet_sourceHashProgramX
    | with_reducible apply quiet_sourceRevealDigestX
    | quiet_step


/-- Verification changes only the candidate log. -/
theorem quiet_verify (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : SourceState C) (input : HashInput) :
    Quiet (do
      let value ← sourceHashX P seeds (.hash input)
      modify fun (s : SourceState C) => { s with candidates := s.candidates ++ SigningGuessLinkProof.callCandidates P st.signing st.exposed input }
      pure value : SourceMX C HashOutput) := by
  repeat' first | with_reducible apply quiet_sourceHashX | quiet_step

theorem Quiet.at {α : Type} {oa : SourceMX C α} (h : Quiet oa) (st : SourceState C) :
    Queries NoMark (oa.run st) ∧ ∀ r ∈ support (oa.run st), r.2.hiddenFlag = st.hiddenFlag := by
  unfold Quiet at h
  exact h st

def callMark (x : Keys3 C) (st : SourceState C) :
    (LocalSpec C + TsigSpec C).Domain → Bool
  | .inl t => st.hiddenFlag || SigningCoreProof.hiddenHit x st.signing.corrupt t
  | .inr _ => st.hiddenFlag

theorem flag_le_callMark (x : Keys3 C) (st : SourceState C)
    (t : (LocalSpec C + TsigSpec C).Domain) : st.hiddenFlag ≤ callMark x st t := by
  cases t with
  | inl t => simp only [callMark]; cases st.hiddenFlag <;> simp
  | inr t => exact le_rfl

/-- The actual remainder after a call's leading mark. -/
def callRest (prims : Primitives) (x : Keys3 C) (top : TopTree) (st : SourceState C) :
    (t : (LocalSpec C + TsigSpec C).Domain) → SourceMX C ((LocalSpec C + TsigSpec C) t)
  | .inl t => do
      let value ← sourceLocalX prims x t
      modify fun (s : SourceState C) => { s with
        hiddenFlag := callMark x st (.inl t)
        candidates := st.candidates ++ unreleasedCandidates x.1 st.signing st.exposed t }
      pure value
  | .inr t => do
      let value ← sourceTsigX prims x top t
      modify fun (s : SourceState C) => { s with exposed := releasedTrees s.exposed t }
      pure value

theorem callRest_noMark (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (st : SourceState C) (t : (LocalSpec C + TsigSpec C).Domain) :
    Queries NoMark ((callRest prims x top st t).run st) := by
  cases t with
  | inl t =>
      simp only [callRest, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
      exact (((quiet_sourceLocalX prims x t).at st).1).bind fun z => Queries.pure _
  | inr t =>
      simp only [callRest, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
      exact (((quiet_sourceTsigX prims x top t).at st).1).bind fun z => Queries.pure _

theorem callRest_flag (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (st : SourceState C) (t : (LocalSpec C + TsigSpec C).Domain)
    (r : (LocalSpec C + TsigSpec C) t × SourceState C)
    (hr : r ∈ support ((callRest prims x top st t).run st)) :
    r.2.hiddenFlag = callMark x st t := by
  cases t with
  | inl t =>
      simp only [callRest, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨z, _, rfl⟩ := hr
      rfl
  | inr t =>
      simp only [callRest, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      exact ((quiet_sourceTsigX prims x top t).at st).2 z hz

/-- M1 anticipates its local call's flag update. Both call branches mark exactly
that call's final flag, for every source answer, and the flag is monotone. -/
theorem sourceOraclesX_marked (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (st : SourceState C) (t : (LocalSpec C + TsigSpec C).Domain) :
    (sourceOraclesX prims x top t).run st =
      markQ (callMark x st t) >>= fun _ => (callRest prims x top st t).run st := by
  cases t <;> simp only [sourceOraclesX, StateT.run_bind, StateT.run_get,
    pure_bind, callMark, callRest]
  all_goals rfl

/-- Every stored bad tag lies below the current source flag. -/
def TagLe (m : Bool) (sh : ShareState C) : Prop :=
  ∀ b k l, sh.bad = some (b, k, l) → b ≤ m

theorem TagLe.mono {m v : Bool} {sh : ShareState C} (h : TagLe m sh)
    (hm : m ≤ v) : TagLe v sh := fun b k l hb => (h b k l hb).trans hm

def TagIs (m : Bool) : (RunSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.read _ _ tag) => tag = m
  | .inr (.complete _ _ tag) => tag = m
  | .inr .view => True

/-- Uniform queries have no tag. -/
theorem queries_uniform {α : Type} (oa : ProbComp α) (m : Bool) :
    Queries (TagIs (C := C) m) (liftM oa : OracleComp (RunSpec C) α) := by
  change Queries (TagIs m) (OracleComp.liftComp oa (RunSpec C))
  rw [OracleComp.liftComp_def]
  exact Queries.simulate _ oa (queries_all oa) (fun t _ => Queries.query (spec := RunSpec C) (.inl t) trivial)

theorem queries_share (m : Bool) (t : SigningShareLazy.ShareQuery C.Term CPoint Bool)
    (h : TagIs m (.inr t)) : Queries (TagIs m) (shareQuery t) := Queries.query _ h

/-- A generic share handler; fresh reads and completions can use any draw law. -/
def handler (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput) :
    QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp) :=
  SigningShareLazy.unifImpl (ShareState C) + SigningShareLazy.impl C.terms τ draw finish

/-- Appending a bad event with the current tag preserves the upper bound. -/
theorem tagLe_update (m : Bool) (sh : ShareState C) (h : TagLe m sh)
    (next : Option (SigningShareLazy.ImplBad Bool))
    (hn : ∀ b k l, next = some (b, k, l) → b ≤ m)
    (sh' : ShareState C) (hb : sh'.bad = (sh.bad <|> next)) : TagLe m sh' := by
  intro b k l hh
  rw [hb] at hh
  cases hold : sh.bad with
  | none => exact hn b k l (by simpa [hold] using hh)
  | some old => exact h b k l (by simpa [hold] using hh)

/-- Only a share query's own tag can become its new first-bad tag. -/
theorem impl_tagLe (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (m : Bool) (t : SigningShareLazy.ShareQuery C.Term CPoint Bool)
    (ht : TagIs m (.inr t)) (sh : ShareState C) (h : TagLe m sh)
    (z : ShareSpec C t × ShareState C)
    (hz : z ∈ support ((SigningShareLazy.impl C.terms τ draw finish t).run sh)) :
    TagLe m z.2 := by
  cases t with
  | view =>
      simp only [SigningShareLazy.impl, StateT.run, mem_support_pure_iff] at hz
      subst z
      exact h
  | read T p tag =>
      change tag = m at ht
      subst tag
      cases hc : sh.cache (T, p) with
      | some value =>
          simp only [SigningShareLazy.impl, StateT.run, hc, mem_support_pure_iff] at hz
          subst z
          exact h
      | none =>
          simp only [SigningShareLazy.impl, StateT.run, hc, mem_support_bind_iff,
            mem_support_pure_iff] at hz
          obtain ⟨v, _, rfl⟩ := hz
          apply tagLe_update m sh h _ _ _ rfl
          intro b k l hb
          simp only [SigningShareLazy.setsBad] at hb
          split at hb <;> simp_all
  | complete p target tag =>
      change tag = m at ht
      subst tag
      by_cases hd : p ∈ sh.done
      · simp only [SigningShareLazy.impl, StateT.run, hd, if_true, mem_support_pure_iff] at hz
        subst z
        exact h
      · cases hs : SigningShareLazy.slack C.terms sh p with
        | none =>
            simp only [SigningShareLazy.impl, StateT.run, hd, if_false, hs,
              mem_support_pure_iff] at hz
            subst z
            apply tagLe_update m sh h _ _ _ rfl
            intro b k l hb
            cases hb
            exact le_rfl
        | some T =>
            simp only [SigningShareLazy.impl, StateT.run, hd, if_false, hs,
              mem_support_bind_iff, mem_support_pure_iff] at hz
            obtain ⟨filled, _, value, _, rfl⟩ := hz
            apply tagLe_update m sh h _ _ _ rfl
            intro b k l hb
            split at hb <;> simp_all

/-- Interpreting a program whose tags are all m retains TagLe m. -/
theorem simulate_tagLe {α : Type} (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (m : Bool) (oa : OracleComp (RunSpec C) α) (ha : Queries (TagIs m) oa)
    (sh : ShareState C) (h : TagLe m sh)
    (z : α × ShareState C)
    (hz : z ∈ support ((simulateQ (handler τ draw finish) oa).run sh)) : TagLe m z.2 := by
  induction oa using OracleComp.inductionOn generalizing sh with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
      subst z
      exact h
  | query_bind t next ih =>
      unfold Queries at ha
      have hh := (isQueryBound_query_bind_iff ..).mp ha
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨mid, hm, hz⟩ := hz
      apply ih mid.1 (by unfold Queries; exact hh.2 mid.1) mid.2 _ hz
      cases t with
      | inl n =>
          simp only [handler, QueryImpl.add_apply_inl, SigningShareLazy.unifImpl,
            StateT.run, support_map] at hm
          obtain ⟨a, _, rfl⟩ := hm
          exact h
      | inr t => exact impl_tagLe τ draw finish m t hh.1 sh h mid hm

/-- The source value of a supported stateful simulation was already supported.
Port of current VCVio StateT/Basic:360; the pinned version uses SetM lifts. -/
theorem mem_support_of_simulate_run {ι α σ : Type} {spec : OracleSpec ι}
    {n : Type → Type} [Monad n] [LawfulMonad n]
    [MonadLiftT n SetM] [LawfulMonadLiftT n SetM]
    (impl : QueryImpl spec (StateT σ n)) (oa : OracleComp spec α) (s : σ)
    {z : α × σ} (hz : z ∈ support ((simulateQ impl oa).run s)) : z.1 ∈ support oa := by
  apply support_simulateQ_run'_subset impl oa s
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ hz

/-- A non-mark backend step uses only its current mark and retains it. -/
theorem backend_noMark (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : (SpecX C).Domain) (ht : NoMark t) (bm : CappedCompilerState C × Bool) :
    Queries (TagIs bm.2) ((shareBackend P seeds q s pads t).run bm) ∧
      ∀ r ∈ support ((shareBackend P seeds q s pads t).run bm), r.2.2 = bm.2 := by
  have ordinary (t : DeferredQuery C ⊕ HiddenKey) :
      Queries (TagIs bm.2) ((ordinaryStep P seeds q s pads t).run bm) ∧
        ∀ r ∈ support ((ordinaryStep P seeds q s pads t).run bm), r.2.2 = bm.2 := by
    constructor
    · exact (queries_share bm.2 .view trivial).bind fun view =>
        (queries_uniform _ bm.2).bind fun result => Queries.pure _
    · intro r hr
      simp only [ordinaryStep, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨view, _, result, _, rfl⟩ := hr
      rfl
  have read (T : C.Term) (p : CPoint) :
      Queries (TagIs bm.2) ((readStep P seeds T p).run bm) ∧
        ∀ r ∈ support ((readStep P seeds T p).run bm), r.2.2 = bm.2 := by
    constructor
    · exact (queries_share bm.2 .view trivial).bind fun view =>
        (queries_share bm.2 (.read T p bm.2) rfl).bind fun value =>
          (queries_share bm.2 .view trivial).bind fun view' =>
            (queries_uniform _ bm.2).bind fun result => Queries.pure _
    · intro r hr
      simp only [readStep, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨view, _, value, _, view', _, result, _, rfl⟩ := hr
      rfl
  cases t with
  | inl t =>
      cases t with
      | inl t =>
          cases t with
          | inr k => exact ordinary (.inr k)
          | inl t =>
              cases t with
              | hash query =>
                  simp only [shareBackend]
                  cases hr : route seeds query with
                  | none => exact ordinary _
                  | some z => exact read z.1 z.2
              | _ => exact ordinary _
      | inr mark => exact ht.elim
  | inr t =>
      rcases t with ⟨p, target⟩
      by_cases hp : Constrained p
      · simp only [shareBackend, hp, dite_true, StateT.run]
        refine ⟨(queries_share bm.2 (.complete ⟨p, hp⟩ target bm.2) rfl).bind
          (fun _ => Queries.pure _), ?_⟩
        intro r hr
        simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        rfl
      · simp only [shareBackend, hp, dite_false, StateT.run]
        refine ⟨Queries.pure _, ?_⟩
        intro r hr
        simp only [mem_support_pure_iff] at hr
        subst r
        rfl

def jointRun {α : Type} (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : OracleComp (SpecX C) α)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) :=
  (simulateQ H ((simulateQ (shareBackend P seeds q s pads) oa).run bm)).run sh

theorem jointRun_bind {α β : Type}
    (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : OracleComp (SpecX C) α)
    (f : α → OracleComp (SpecX C) β) (bm : CappedCompilerState C × Bool) (sh : ShareState C) :
    jointRun H P seeds q s pads (oa >>= f) bm sh =
      jointRun H P seeds q s pads oa bm sh >>= fun r =>
        jointRun H P seeds q s pads (f r.1.1) r.1.2 r.2 := by
  simp only [jointRun, simulateQ_bind, StateT.run_bind]

theorem joint_support {α : Type}
    (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : OracleComp (SpecX C) α)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C)
    (z : (α × (CappedCompilerState C × Bool)) × ShareState C)
    (hz : z ∈ support (jointRun H P seeds q s pads oa bm sh)) : z.1.1 ∈ support oa :=
  mem_support_of_simulate_run _ oa bm (mem_support_of_simulate_run H _ sh hz)

theorem joint_noMark {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (oa : OracleComp (SpecX C) α) (ha : Queries NoMark oa)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) (h : TagLe bm.2 sh)
    (z : (α × (CappedCompilerState C × Bool)) × ShareState C)
    (hz : z ∈ support (jointRun (handler τ draw finish) P seeds q s pads oa bm sh)) :
    z.1.2.2 = bm.2 ∧ TagLe bm.2 z.2 ∧ z.1.1 ∈ support oa := by
  have hp : z.1.2.2 = bm.2 ∧ TagLe bm.2 z.2 := by
    induction oa using OracleComp.inductionOn generalizing bm sh with
    | pure a =>
        simp only [jointRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
        subst z
        exact ⟨rfl, h⟩
    | query_bind t next ih =>
        unfold Queries at ha
        have hb := (isQueryBound_query_bind_iff ..).mp ha
        rw [jointRun_bind] at hz
        simp only [mem_support_bind_iff] at hz
        obtain ⟨mid, hm, hz⟩ := hz
        have hm' : mid ∈ support ((simulateQ (handler τ draw finish)
            ((shareBackend P seeds q s pads t).run bm)).run sh) := by
          simpa only [jointRun, simulateQ_spec_query] using hm
        have hs := backend_noMark P seeds q s pads t hb.1 bm
        have he := hs.2 mid.1 (mem_support_of_simulate_run _ _ _ hm')
        have ht := simulate_tagLe τ draw finish bm.2 _ hs.1 sh h mid hm'
        have result := ih mid.1.1 (by unfold Queries; exact hb.2 mid.1.1) mid.1.2 mid.2 (by simpa only [he] using ht) hz
        exact ⟨result.1.trans he, by simpa only [he] using result.2⟩
  exact ⟨hp.1, hp.2, joint_support _ _ _ _ _ _ _ _ _ z hz⟩

/-- Marks are silent state writes and do not change the share table. -/
theorem joint_mark (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (v : Bool) (bm : CappedCompilerState C × Bool) (sh : ShareState C) :
    jointRun H P seeds q s pads (markQ v) bm sh = pure (((), (bm.1, v)), sh) := by
  simp only [jointRun, markQ, simulateQ_spec_query, shareBackend, StateT.run,
    simulateQ_pure]
  rfl

def TagSafe {α : Type}
    (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : SourceMX C α) : Prop :=
  ∀ (st : SourceState C) (bm : CappedCompilerState C × Bool) (sh : ShareState C),
    bm.2 = st.hiddenFlag → TagLe st.hiddenFlag sh →
    ∀ z ∈ support (jointRun H P seeds q s pads (oa.run st) bm sh),
      z.1.2.2 = z.1.1.2.hiddenFlag ∧ st.hiddenFlag ≤ z.1.1.2.hiddenFlag ∧
        TagLe z.1.1.2.hiddenFlag z.2

namespace TagSafe
variable {α β : Type}
variable {H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp)}
variable {P : PublicParameter} {seeds : C.Term → HashOutput} {q : ℕ}
variable {s : HiddenKey → Digest} {pads : Point → Digest}

theorem pure (a : α) : TagSafe H P seeds q s pads (pure a) := by
  intro st bm sh he ht z hz
  simp only [StateT.run_pure, jointRun, simulateQ_pure, mem_support_pure_iff] at hz
  subst z
  exact ⟨he, le_rfl, ht⟩

theorem bind {oa : SourceMX C α} {f : α → SourceMX C β}
    (h : TagSafe H P seeds q s pads oa) (hf : ∀ a, TagSafe H P seeds q s pads (f a)) :
    TagSafe H P seeds q s pads (oa >>= f) := by
  intro st bm sh he ht z hz
  rw [StateT.run_bind, jointRun_bind] at hz
  simp only [mem_support_bind_iff] at hz
  obtain ⟨mid, hm, hz⟩ := hz
  have hi := h st bm sh he ht mid hm
  have hj := hf mid.1.1.1 mid.1.1.2 mid.1.2 mid.2 hi.1 hi.2.2 z hz
  exact ⟨hj.1, hi.2.1.trans hj.2.1, hj.2.2⟩

theorem map (f : α → β) {oa : SourceMX C α} (h : TagSafe H P seeds q s pads oa) :
    TagSafe H P seeds q s pads (f <$> oa) := by
  simpa only [bind_pure_comp] using h.bind (fun a => pure (f a))

theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMX C)) (oa : OracleComp spec α)
    (h : ∀ t, TagSafe H P seeds q s pads (impl t)) :
    TagSafe H P seeds q s pads (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (H := H) (P := P) (seeds := seeds) (q := q) (s := s) (pads := pads) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (h t).bind ih

/-- A current-flag mark synchronizes the boundary before its continuation. -/
theorem get_mark (f : SourceState C → SourceMX C α)
    (hf : ∀ st, TagSafe H P seeds q s pads (f st)) :
    TagSafe H P seeds q s pads (do
      let st ← get
      let _ ← liftM (markQ (C := C) st.hiddenFlag)
      f st) := by
  intro st bm sh he ht z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  change z ∈ support (jointRun H P seeds q s pads
    (markQ st.hiddenFlag >>= fun _ => (f st).run st) bm sh) at hz
  rw [jointRun_bind, joint_mark] at hz
  simp only [pure_bind] at hz
  exact hf st st (bm.1, st.hiddenFlag) sh rfl ht z hz
end TagSafe

theorem Quiet.tagSafe {α : Type} {oa : SourceMX C α} (h : Quiet oa)
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput) :
    TagSafe (handler τ draw finish) P seeds q s pads oa := by
  intro st bm sh he ht z hz
  have hq := h.at st
  have hj := joint_noMark P seeds q s pads τ draw finish (oa.run st) hq.1
    bm sh (by simpa only [he] using ht) z hz
  have hf := hq.2 z.1.1 hj.2.2
  exact ⟨hj.1.trans (he.trans hf.symm), by simp only [hf]; exact le_rfl,
    by simpa only [hf, he] using hj.2.1⟩

/-- Every actual call restores mark=flag, and all stored tags lie below it. -/
theorem sourceOraclesX_tagSafe (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (t : (LocalSpec C + TsigSpec C).Domain) :
    TagSafe (handler τ draw finish) x.1 x.2.1 q s pads (sourceOraclesX prims x top t) := by
  intro st bm sh he ht z hz
  rw [sourceOraclesX_marked, jointRun_bind, joint_mark] at hz
  simp only [pure_bind] at hz
  have hmono := flag_le_callMark x st t
  have hj := joint_noMark x.1 x.2.1 q s pads τ draw finish
    ((callRest prims x top st t).run st) (callRest_noMark prims x top st t)
    (bm.1, callMark x st t) sh (ht.mono hmono) z hz
  have hf := callRest_flag prims x top st t z.1.1 hj.2.2
  exact ⟨hj.1.trans hf.symm, by simpa only [hf] using hmono,
    by simpa only [hf] using hj.2.1⟩

attribute [local irreducible] TagSafe

/-- Setup, all adaptive calls, verification and the reference signature preserve
mark/flag agreement at their boundaries. -/
theorem sourceGameX_tagSafe (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput) :
    TagSafe (handler τ draw finish) x.1 x.2.1 q s pads (sourceGameX prims A x) := by
  unfold sourceGameX
  apply TagSafe.get_mark
  intro initial
  apply TagSafe.bind ((quiet_sourceTopTreeX x.1 x.2.1).tagSafe x.1 x.2.1 q s pads τ draw finish)
  intro top
  apply TagSafe.bind (TagSafe.simulate _ _
    (sourceOraclesX_tagSafe prims x top q s pads τ draw finish))
  intro forgery
  apply TagSafe.get_mark
  intro st
  apply TagSafe.bind
    ((Quiet.simulate _ _ (quiet_verify x.1 x.2.1 st)).tagSafe x.1 x.2.1 q s pads τ draw finish)
  intro verified
  split <;> simp only [pure_bind]
  · exact TagSafe.pure _
  · exact ((quiet_sourceHonestSignatureX prims x top _ _).tagSafe
      x.1 x.2.1 q s pads τ draw finish).bind fun _ => TagSafe.pure _

@[simp] theorem handler_view (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput) (sh : ShareState C) :
    (simulateQ (handler τ draw finish) (shareQuery (C := C) .view)).run sh =
      pure ((sh.cache, sh.done), sh) := by
  simp only [shareQuery, simulateQ_spec_query, handler, QueryImpl.add_apply_inr,
    SigningShareLazy.impl, StateT.run]

/-- A first bad event tagged true entails the original source's final hidden flag.
The statement covers both lazy and eager handlers without any seed assumption. -/
theorem shareRun_tagTrue (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (z : CompilerOutcome C × ShareState C)
    (hz : z ∈ support ((simulateQ (handler τ draw finish)
      (shareRun prims A x q s pads)).run SigningShareLazy.init))
    (k : SigningShareLazy.Kind) (l : Bool) (hbad : z.2.bad = some (true, k, l)) :
    z.1.1.2.hiddenFlag = true := by
  simp only [shareRun, simulateQ_bind, StateT.run_bind, handler_view, pure_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := sourceGameX_tagSafe prims A x q s pads τ draw finish
  unfold TagSafe at hs
  have hi : TagLe (sourceInit (C := C)).hiddenFlag
      (SigningShareLazy.init (κ := C.Term) (ι := CPoint) (B := SigningShareLazy.ImplBad Bool)) := by
    intro b k l hb
    simp [SigningShareLazy.init] at hb
  have result := hs sourceInit (((compilerInit, 0), fun _ => none, false), false)
    SigningShareLazy.init rfl hi r (by simpa only [jointRun, sourceProgramX] using hr)
  have hb := result.2.2 true k l hbad
  exact Bool.le_iff_imp.mp hb rfl

end ThresholdLeanXmssSecurity.SigningCompilerShare.Marks

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Marks.quiet_sourceTsigX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Marks.quiet_sourceTsigX

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Marks.sourceOraclesX_tagSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Marks.sourceOraclesX_tagSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.Marks.shareRun_tagTrue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.Marks.shareRun_tagTrue
