import ThresholdLeanXmssSecurity.Proof.SigningCompilerPotential
import XmssSecurity.Proof.CappedGlobalChainOutputUniformity
import VCVio.OracleComp.QueryTracking.Iter

/-!
# Concrete coupling components for the capped signing compiler

This module uses the fixed source and backend from `SigningLaneHybridCap`.
The target is its original `CompilerCoupling`, including the real guarded event
and the final count bound. The local count laws below account for the release
and cache bookkeeping performed by the live source interpreter.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningCompilerCouplingProof

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof

variable {C : Committee}

attribute [local instance] Classical.propDecidable

/-- The actual counted calls of the source alphabet; reveals are uncounted. -/
def sourceCounted : DeferredQuery C ⊕ HiddenKey → Prop
  | .inl query => deferredCounted query
  | .inr _ => False

/-- An exact cost of the fixed source computation, for every source state. -/
def SourceCost {α : Type} (oa : SourceM C α) (n : ℕ) : Prop :=
  ∀ st, XmssSecurity.ExactPredicateQueryCount sourceCounted (oa.run st) n

theorem SourceCost.pure {α : Type} (a : α) : SourceCost (C := C) (pure a) 0 := by
  intro st
  exact .pure (a, st)

theorem SourceCost.bind {α β : Type} {oa : SourceM C α} {n m : ℕ}
    (h : SourceCost oa n) (f : α → SourceM C β) (hf : ∀ a, SourceCost (f a) m) :
    SourceCost (oa >>= f) (n + m) := by
  intro st
  rw [StateT.run_bind]
  exact XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind (h st) _ m
    (fun a => hf a.1 a.2)

theorem SourceCost.get : SourceCost (get : SourceM C (SourceState C)) 0 := by
  intro st
  exact .pure (st, st)

theorem SourceCost.modify (f : SourceState C → SourceState C) :
    SourceCost (modify f : SourceM C Unit) 0 := by
  intro st
  exact .pure ((), f st)

theorem SourceCost.lift {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α) (n : ℕ)
    (h : XmssSecurity.ExactPredicateQueryCount sourceCounted oa n) :
    SourceCost (liftM oa : SourceM C α) n := by
  intro st
  change XmssSecurity.ExactPredicateQueryCount sourceCounted
    (oa >>= fun a => Pure.pure (a, st)) n
  simpa only [Nat.add_zero] using
    (XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind h _ 0
      (fun a => XmssSecurity.ExactPredicateQueryCount.pure (a, st)))

set_option backward.isDefEq.respectTransparency false in
theorem exact_deferredQuery (q : DeferredQuery C) :
    XmssSecurity.ExactPredicateQueryCount sourceCounted (deferredQuery q)
      (if deferredCounted q then 1 else 0) := by
  change XmssSecurity.ExactPredicateQueryCount sourceCounted
    (liftM (OracleSpec.query (spec := DeferredSpec C + RevealSpec HiddenKey Digest) (.inl q))) _
  simpa only [bind_pure, sourceCounted, Nat.zero_add] using
    (XmssSecurity.ExactPredicateQueryCount.query (predicate := sourceCounted (C := C)) (.inl q)
      (fun a => (pure a : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) _)) 0
      (fun a => XmssSecurity.ExactPredicateQueryCount.pure a))

theorem exact_revealQuery (k : HiddenKey) :
    XmssSecurity.ExactPredicateQueryCount sourceCounted (revealQuery (C := C) k) 0 := by
  change XmssSecurity.ExactPredicateQueryCount sourceCounted
    (liftM (OracleSpec.query (spec := DeferredSpec C + RevealSpec HiddenKey Digest) (.inr k))) 0
  simpa only [bind_pure, sourceCounted, if_false, Nat.zero_add] using
    (XmssSecurity.ExactPredicateQueryCount.query (predicate := sourceCounted (C := C)) (.inr k)
      (fun a => (pure a : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) _)) 0
      (fun a => XmssSecurity.ExactPredicateQueryCount.pure a))

theorem sourceCost_deferredQuery (q : DeferredQuery C) :
    SourceCost (liftM (deferredQuery q) : SourceM C (DeferredSpec C q))
      (if deferredCounted q then 1 else 0) :=
  SourceCost.lift _ _ (exact_deferredQuery q)

theorem exact_deferredQuery_uncounted (q : DeferredQuery C) (hq : ¬deferredCounted q) :
    XmssSecurity.ExactPredicateQueryCount sourceCounted (deferredQuery q) 0 := by
  simpa only [if_neg hq] using exact_deferredQuery q

theorem sourceCost_deferredQuery_counted (q : DeferredQuery C) (hq : deferredCounted q) :
    SourceCost (liftM (deferredQuery q) : SourceM C (DeferredSpec C q)) 1 := by
  simpa only [if_pos hq] using sourceCost_deferredQuery q

theorem sourceCost_deferredQuery_uncounted (q : DeferredQuery C) (hq : ¬deferredCounted q) :
    SourceCost (liftM (deferredQuery q) : SourceM C (DeferredSpec C q)) 0 :=
  SourceCost.lift _ 0 (exact_deferredQuery_uncounted q hq)

theorem sourceCost_sourceReveal (k : HiddenKey) : SourceCost (sourceReveal (C := C) k) 0 := by
  unfold sourceReveal
  refine SourceCost.get.bind (m := 0) _ fun st => ?_
  cases st.revealed k with
  | some value => exact SourceCost.pure value
  | none =>
      refine (SourceCost.lift _ 0 (exact_revealQuery k)).bind (m := 0) _ fun value => ?_
      exact (SourceCost.modify _).bind (m := 0) _ fun _ => SourceCost.pure value

theorem sourceCost_sourceRevealDigest (d : DeferredDigest) :
    SourceCost (sourceRevealDigest (C := C) d) 0 := by
  cases d with
  | known value => exact SourceCost.pure value
  | secret k => exact sourceCost_sourceReveal k

/-- Silent filling never consumes the hash budget. The corresponding real PRF
query still appears later as a separate counted call. -/
theorem exact_fillTerm (seeds : C.Term → HashOutput) (p : Point) (T : C.Term) :
    XmssSecurity.ExactPredicateQueryCount sourceCounted (fillTerm seeds p T) 0 := by
  unfold fillTerm
  refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
    (exact_deferredQuery_uncounted .snapshot id) _ 0 fun st => ?_
  split
  · refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
      (exact_deferredQuery_uncounted .sample id) _ 0 fun value => ?_
    exact XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
      (exact_deferredQuery_uncounted (.plant (.prf (seeds T) p) value) id) _ 0
      (fun _ => XmssSecurity.ExactPredicateQueryCount.pure ())
  · exact .pure ()

/-- Adaptive slack selection and PRF programming are entirely uncounted. -/
theorem exact_completePrf (seeds : C.Term → HashOutput) (p : Point) (target : Digest) :
    XmssSecurity.ExactPredicateQueryCount sourceCounted (completePrf seeds p target) 0 := by
  unfold completePrf
  refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
    (exact_deferredQuery_uncounted .snapshot id) _ 0 fun st => ?_
  cases firstUnmaterialized seeds st p with
  | none => exact .pure _
  | some slack =>
      have hfill : XmssSecurity.ExactPredicateQueryCount sourceCounted
          ((C.terms.filter (· ≠ slack)).mapM (fillTerm seeds p)) 0 := by
        simpa using (exact_mapM sourceCounted (C.terms.filter (· ≠ slack))
          (fillTerm seeds p) (fun _ => 0) (fun T _ => exact_fillTerm seeds p T))
      refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind hfill _ 0 fun _ => ?_
      refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
        (exact_deferredQuery_uncounted .snapshot id) _ 0 fun st' => ?_
      refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
        (exact_deferredQuery_uncounted .sample id) _ 0 fun high => ?_
      exact exact_deferredQuery_uncounted (.plant (.prf (seeds slack) p)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
          (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds st' p) slack))) id

theorem SourceCost.mapM_zero {α β : Type} (xs : List α) (f : α → SourceM C β)
    (hf : ∀ a ∈ xs, SourceCost (f a) 0) : SourceCost (xs.mapM f) 0 := by
  induction xs with
  | nil => exact SourceCost.pure []
  | cons a xs ih =>
      rw [List.mapM_cons]
      refine (hf a (List.mem_cons_self ..)).bind (m := 0) _ fun b => ?_
      exact (ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))).bind (m := 0) _
        (fun bs => SourceCost.pure (b :: bs))

theorem sourceCost_sourcePlant (P : PublicParameter) (p : PendingInput) :
    SourceCost (sourcePlant (C := C) P p) 0 := by
  unfold sourcePlant
  refine (SourceCost.lift _ 0 (exact_deferredQuery_uncounted (.inspect p) id)).bind
    (m := 0) _ fun answer => ?_
  cases answer with
  | none => exact SourceCost.pure ()
  | some answer =>
      refine (sourceCost_sourceReveal p.key).bind (m := 0) _ fun input => ?_
      refine (sourceCost_sourceRevealDigest answer.low).bind (m := 0) _ fun low => ?_
      exact (SourceCost.lift _ 0 (exact_deferredQuery_uncounted (.plant (.pending P p input)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low))) id)).bind
          (m := 0) _ (fun _ => SourceCost.modify _)

theorem sourceCost_sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceCost (sourceReleaseOpening P seeds e) 0 := by
  unfold sourceReleaseOpening
  refine SourceCost.get.bind (m := 0) _ fun st => ?_
  split
  · refine (sourceCost_sourceReveal (.opening bottomLayer e)).bind (m := 0) _ fun value => ?_
    refine (SourceCost.lift _ 0 (exact_completePrf seeds (.randomizer bottomLayer e) value)).bind
      (m := 0) _ fun _ => ?_
    refine (SourceCost.modify _).bind (m := 0) _ fun _ => ?_
    refine SourceCost.get.bind (m := 0) _ fun st' => ?_
    exact (SourceCost.mapM_zero _ (sourcePlant P)
      (fun p _ => sourceCost_sourcePlant P p)).bind (m := 0) _ (fun _ => SourceCost.pure ())
  · exact SourceCost.pure ()

set_option backward.isDefEq.respectTransparency false in
/-- P may fill and reveal many entries, but an actual hash/PRF call still has
exactly one counted backend query. -/
theorem sourceCost_sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) : SourceCost (sourceHash P seeds q) 1 := by
  have hquery (q : Query C) :
      SourceCost (liftM (deferredQuery (.hash q)) : SourceM C HashOutput) 1 := by
    simpa only [deferredCounted, if_true] using sourceCost_deferredQuery (C := C) (.hash q)
  unfold sourceHash
  cases q with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          dsimp only
          split
          · refine (SourceCost.lift _ 0 (exact_deferredQuery_uncounted .snapshot id)).bind
              (m := 1) _ fun backend => ?_
            refine SourceCost.get.bind (m := 1) _ fun st => ?_
            split
            · exact (sourceCost_sourceReleaseOpening P seeds e).bind (m := 1) _
                (fun _ => hquery _)
            · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
          · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
      | _ => simpa only [pure_bind] using hquery _
  | _ => simpa only [pure_bind] using hquery _

set_option backward.isDefEq.respectTransparency false in
/-- Virtual PRF cache hits and first insertions both consume their actual call;
the release after the call adds no cost. -/
theorem sourceCost_sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) : SourceCost (sourceVirtual P seeds T p) 1 := by
  unfold sourceVirtual
  have hquery : SourceCost (liftM (deferredQuery (C := C) (.virtual T p)) : SourceM C Unit) 1 := by
    simpa only [deferredCounted, if_true] using sourceCost_deferredQuery (C := C) (.virtual T p)
  refine hquery.bind (m := 0) _ fun _ => ?_
  cases p with
  | randomizer lay e =>
      dsimp only
      split
      · refine (SourceCost.lift _ 0 (exact_deferredQuery_uncounted .snapshot id)).bind
          (m := 0) _ fun backend => ?_
        refine SourceCost.get.bind (m := 0) _ fun st => ?_
        split
        · exact sourceCost_sourceReleaseOpening P seeds e
        · exact SourceCost.pure ()
      · exact SourceCost.pure ()
  | _ => exact SourceCost.pure ()

set_option backward.isDefEq.respectTransparency false in
/-- Both pending-cache hits and the concrete post-release fallback retain one
counted call. Recording an already-cached commitment does not add another call. -/
theorem sourceCost_sourcePending (P : PublicParameter) (p : PendingInput) :
    SourceCost (sourcePending (C := C) P p) 1 := by
  have htail (prior : Option DeferredOutput) : SourceCost (do
      let value ← liftM (deferredQuery (C := C) (.pending p))
      if prior.isNone then
        modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
      pure value : SourceM C DeferredOutput) 1 := by
    refine (sourceCost_deferredQuery_counted (.pending p) trivial).bind (m := 0) _ fun value => ?_
    split
    · exact (SourceCost.modify _).bind (m := 0) _ (fun _ => SourceCost.pure value)
    · exact SourceCost.pure value
  unfold sourcePending
  refine (sourceCost_deferredQuery_uncounted (.inspect p) id).bind (m := 1) _ fun prior => ?_
  refine SourceCost.get.bind (m := 1) _ fun st => ?_
  dsimp only
  split
  · refine (sourceCost_deferredQuery_counted (.hash (.hash _)) trivial).bind
      (m := 0) _ fun value => ?_
    refine (sourceCost_deferredQuery_uncounted (.record p value) id).bind (m := 0) _ fun _ => ?_
    exact (SourceCost.modify _).bind (m := 0) _ (fun _ => SourceCost.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (SourceCost.modify _).bind (m := 1) _ (fun _ => htail original)
    · simpa only [pure_bind] using htail original

set_option backward.isDefEq.respectTransparency false in
/-- The live source interpreter preserves the declared cost of every backend
instruction, including all three counted constructors. -/
theorem sourceCost_sourceBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) : SourceCost (sourceBackend P seeds t)
      (if deferredCounted t then 1 else 0) := by
  cases t with
  | hash q => simpa only [sourceBackend, deferredCounted, if_true] using sourceCost_sourceHash P seeds q
  | pending p => simpa only [sourceBackend, deferredCounted, if_true] using sourceCost_sourcePending (C := C) P p
  | virtual T p => simpa only [sourceBackend, deferredCounted, if_true] using sourceCost_sourceVirtual P seeds T p
  | _ => exact sourceCost_deferredQuery _

/-- Exact source costs survive the actual release-aware interpreter. -/
theorem sourceCost_simulateBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    {α : Type} {oa : OracleComp (DeferredSpec C) α} {n : ℕ}
    (h : XmssSecurity.ExactPredicateQueryCount deferredCounted oa n) :
    SourceCost (simulateQ (sourceBackend P seeds) oa) n := by
  induction h with
  | pure a => simpa only [simulateQ_pure] using SourceCost.pure (C := C) a
  | query t next n _ ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      simpa only [Nat.add_comm] using (sourceCost_sourceBackend P seeds t).bind _ ih

/-- The live bottom-row source retains all six prefix calls and all term calls,
even when P releases the opening during the row. -/
theorem sourceCost_sourceBottomRow (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceCost (sourceBottomRow P seeds e l)
      (3 * C.terms.length + 6) :=
  sourceCost_simulateBackend P seeds (exact_deferredBottomRow e l)

abbrev CappedCompilerState (C : Committee) :=
  (CompilerBackend C × ℕ) × (HiddenKey → Option Digest) × Bool

/-- One actual capped-kernel call increments precisely the source's declared
counter, regardless of the cap flag or any cache hit. -/
theorem cappedCompiler_step_count (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run st)) :
    r.2.1.2 = st.1.2 + if sourceCounted t then 1 else 0 := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact SigningLane2Proof.countImpl_support_count (compilerImpl P seeds) deferredCounted t st.1 a ha
  | inr k =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      simp only [sourceCounted, if_false, Nat.add_zero]

/-- Exact source accounting is the count stored by the fixed capped compiler.
It is not an assumed correspondence to the real-world budget. -/
theorem exact_cappedCompiler_run_count (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) {α : Type}
    {oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α} {n : ℕ}
    (h : XmssSecurity.ExactPredicateQueryCount sourceCounted oa n)
    (st : CappedCompilerState C) (r : α × CappedCompilerState C)
    (hr : r ∈ support ((simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s) oa).run st)) :
    r.2.1.2 = st.1.2 + n := by
  induction h generalizing st r with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      exact (Nat.add_zero _).symm
  | query t next n _ ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, hr⟩ := hr
      rw [ih a.1 a.2 r hr, cappedCompiler_step_count P seeds q s t st a ha]
      omega

/-- Execute a local piece of the existing source with the one fixed capped
backend. This is the same interpretation used by `compilerRun`. -/
def runSource {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C) :
    ProbComp ((α × SourceState C) × CappedCompilerState C) :=
  (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
    (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
    (oa.run source)).run backend

theorem runSource_bind {α β : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α) (next : α → SourceM C β)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (oa >>= next) source backend =
      runSource P seeds q s oa source backend >>= fun r =>
        runSource P seeds q s (next r.1.1) r.1.2 r.2 := by
  simp only [runSource, StateT.run_bind, simulateQ_bind]

theorem runSource_pure {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (a : α)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (pure a) source backend = pure ((a, source), backend) := by
  simp only [runSource, StateT.run_pure, simulateQ_pure]

/-- A cached source reveal is answered without touching the backend at all. -/
theorem runSource_sourceReveal_cached (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (k : HiddenKey)
    (source : SourceState C) (backend : CappedCompilerState C) (value : Digest)
    (hk : source.revealed k = some value) :
    runSource P seeds q s (sourceReveal k) source backend = pure ((value, source), backend) := by
  simp only [runSource, sourceReveal, StateT.run_bind, StateT.run_get, pure_bind, hk,
    StateT.run_pure, simulateQ_pure]

/-- A first source reveal performs the actual reveal query and records exactly
the answer returned by the capped handler. It changes neither count nor flag. -/
theorem runSource_sourceReveal_fresh (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (k : HiddenKey)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hk : source.revealed k = none) :
    runSource P seeds q s (sourceReveal k) source backend =
      let value := (backend.2.1 k).getD (s k)
      pure ((value, { source with revealed := Function.update source.revealed k (some value) }),
        (backend.1, Function.update backend.2.1 k (some value), backend.2.2)) := by
  have hlift : (liftM (revealQuery (C := C) k) : SourceM C Digest).run source =
      revealQuery k >>= fun value => pure (value, source) := rfl
  simp only [runSource, sourceReveal, StateT.run_bind, StateT.run_get, pure_bind, hk,
    StateT.run_modify, StateT.run_pure]
  rw [hlift]
  simp only [revealQuery, HasQuery.instOfMonadLift_query,
    simulateQ_bind, simulateQ_pure, SigningCappedExpectProof.cappedHybrid,
    StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  rfl

/-- The source and reveal wrapper store the same previously released coordinates. -/
def RevealRelation (s : HiddenKey → Digest) (source : SourceState C)
    (backend : CappedCompilerState C) : Prop :=
  source.revealed = backend.2.1 ∧ ∀ k value, source.revealed k = some value → value = s k

theorem revealRelation_initial (s : HiddenKey → Digest) :
    RevealRelation (C := C) s sourceInit ((compilerInit, 0), fun _ => none, false) := by
  refine ⟨rfl, ?_⟩
  intro k value hk
  cases hk

/-- The actual source reveal returns the selected secret and preserves the
synchronized reveal relation, with an unchanged concrete backend and flag. -/
theorem sourceReveal_correct (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (k : HiddenKey)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : RevealRelation s source backend)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReveal k) source backend)) :
    r.1.1 = s k ∧ RevealRelation s r.1.2 r.2 ∧
      r.2.1 = backend.1 ∧ r.2.2.2 = backend.2.2 := by
  cases hk : source.revealed k with
  | some value =>
      rw [runSource_sourceReveal_cached P seeds q s k source backend value hk,
        mem_support_pure_iff] at hr
      subst r
      exact ⟨h.2 k value hk, h, rfl, rfl⟩
  | none =>
      rw [runSource_sourceReveal_fresh P seeds q s k source backend hk] at hr
      have hb : backend.2.1 k = none := h.1 ▸ hk
      simp only [hb, Option.getD_none, mem_support_pure_iff] at hr
      subst r
      refine ⟨rfl, ⟨congrArg (fun f => Function.update f k (some (s k))) h.1, ?_⟩, rfl, rfl⟩
      intro key value hvalue
      change Function.update source.revealed k (some (s k)) key = some value at hvalue
      by_cases he : key = k
      · subst key
        simpa only [Function.update_self, Option.some.injEq] using hvalue.symm
      · rw [Function.update_of_ne he] at hvalue
        exact h.2 key value hvalue

/-- Only absent concrete entries whose values the source has deferred are
exceptions to direct cache agreement. Secret coordinates appear only in this
mathematical relation, never in the backend implementation. -/
def SuspendedQuery (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (query : Query C) : Prop :=
  data.cache query = none ∧
    ((∃ p value, data.pending p = some value ∧ query = .hash (p.input P (s p.key))) ∨
      ∃ T p, (T, p) ∈ data.virtual ∧ query = .prf (seeds T) p)

/-- Eager message-digest grinds never address a suspended symbolic cache slot. -/
theorem suspendedQuery_not_message (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (input : HashInput)
    (hi : IsMsg input) : ¬SuspendedQuery P seeds s data (.hash input) := by
  rintro ⟨_, hp | hp⟩
  · obtain ⟨p, value, _, he⟩ := hp
    cases he
    exact PendingInput.not_isMsg P p (s p.key) hi
  · obtain ⟨T, p, _, he⟩ := hp
    cases he

/-- The cache component of the simulation relation. The real cache contains
every pending symbolic answer and agrees with materialized entries elsewhere. -/
structure CacheRelation (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (actual : HashCache C) : Prop where
  agree : ∀ query, ¬SuspendedQuery P seeds s data query → actual query = data.cache query
  pending : ∀ p value, data.pending p = some value →
    actual (.hash (p.input P (s p.key))) = some (value.interpret s)

theorem CacheRelation.cache_le {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) : data.cache ≤ actual := by
  intro query value hv
  rw [h.agree query (by intro hs; have hc := hv.symm.trans hs.1; cases hc)]
  exact hv

theorem CacheRelation.message {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (input : HashInput) (hi : IsMsg input) :
    actual (.hash input) = data.cache (.hash input) :=
  h.agree _ (suspendedQuery_not_message P seeds s data input hi)

theorem cacheRelation_initial (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) : CacheRelation P seeds s deferredInit (∅ : HashCache C) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro p value hp
  cases hp

/-- Materializing the real answer at one suspended point removes that exception
from cache agreement. The pending-answer relation remains intact. -/
theorem CacheRelation.materialize {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (query : Query C) (value : HashOutput)
    (hq : actual query = some value) :
    CacheRelation P seeds s { data with cache := data.cache.cacheQuery query value } actual := by
  refine ⟨?_, h.pending⟩
  intro other ho
  by_cases he : other = query
  · subst other
    simpa only [QueryCache.cacheQuery_self] using hq
  · have hnot : ¬SuspendedQuery P seeds s data other := by
      simpa only [SuspendedQuery, QueryCache.cacheQuery_of_ne _ _ he] using ho
    simpa only [QueryCache.cacheQuery_of_ne _ _ he] using h.agree other hnot

/-- One shared fresh answer extends both caches and preserves every symbolic
pending answer, for an arbitrary number of suspended points. -/
theorem CacheRelation.cacheQuery {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (query : Query C) (value : HashOutput)
    (hq : actual query = none) :
    CacheRelation P seeds s { data with cache := data.cache.cacheQuery query value }
      (actual.cacheQuery query value) := by
  refine ⟨?_, ?_⟩
  · intro other ho
    by_cases he : other = query
    · subst other
      simp only [QueryCache.cacheQuery_self]
    · have hnot : ¬SuspendedQuery P seeds s data other := by
        simpa only [SuspendedQuery, QueryCache.cacheQuery_of_ne _ _ he] using ho
      simpa only [QueryCache.cacheQuery_of_ne _ _ he] using h.agree other hnot
  · intro p answer hp
    exact QueryCache.le_cacheQuery actual hq (h.pending p answer hp)

/-- Conservative planting succeeds whenever the proposed value is the coupled
real answer, including the already-materialized case. -/
theorem deferredPlant_correct (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (query : PlantInput) (value : HashOutput)
    (hv : actual query.query = some value)
    (r : Bool × DeferredState C)
    (hr : r ∈ support ((deferredImpl (.plant query value)).run data)) :
    r.1 = true ∧ CacheRelation P seeds s r.2 actual := by
  cases hc : data.cache query.query with
  | none =>
      simp only [deferredImpl, StateT.run, hc] at hr
      subst r
      exact ⟨rfl, h.materialize query.query value hv⟩
  | some prior =>
      have he : prior = value := Option.some.inj ((h.cache_le hc).symm.trans hv)
      subst prior
      simp only [deferredImpl, StateT.run, hc, decide_true] at hr
      subst r
      exact ⟨rfl, h⟩

open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false in
/-- A real lazy-oracle call and the fixed deferred hash interpreter are coupled
with identical answers outside the current suspended set. This relation permits
all previously allocated pending points and virtual PRF entries at once. -/
theorem relTriple_deferredHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (query : Query C)
    (hq : ¬SuspendedQuery P seeds s data query) :
    RelTriple (((Query C →ₒ HashOutput).randomOracle query).run actual)
      ((deferredImpl (.hash query)).run data)
      (fun a b => a.1 = b.1 ∧ CacheRelation P seeds s b.2 a.2) := by
  change RelTriple (((Query C →ₒ HashOutput).randomOracle query).run actual)
    ((fun r => (r.1, { data with cache := r.2 })) <$>
      (((Query C →ₒ HashOutput).randomOracle query).run data.cache)) _
  have he := h.agree query hq
  cases hc : data.cache query with
  | some value =>
      have ha := he.trans hc
      simp only [OracleSpec.randomOracle,
        QueryImpl.withCaching_run_some _ ha, QueryImpl.withCaching_run_some _ hc, map_pure]
      exact relTriple_pure_pure ⟨rfl, h⟩
  | none =>
      have ha := he.trans hc
      simp only [OracleSpec.randomOracle,
        QueryImpl.withCaching_run_none _ ha, QueryImpl.withCaching_run_none _ hc, Functor.map_map]
      refine relTriple_map (relTriple_post_mono (relTriple_refl _) fun value value' hv => ?_)
      subst value'
      exact ⟨rfl, h.cacheQuery query value ha⟩

/-- Allocating a fresh pending input grows the suspended set. The symbolic
answer is interpreted with its own next-secret coordinate, never with an
unrelated concrete low half. This is the deterministic cache step; its sampling
law is a separate obligation. -/
theorem CacheRelation.allocatePending {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (p : PendingInput) (value : DeferredOutput)
    (hp : data.pending p = none)
    (hq : actual (.hash (p.input P (s p.key))) = none) :
    CacheRelation P seeds s
      { data with pending := Function.update data.pending p (some value) }
      (actual.cacheQuery (.hash (p.input P (s p.key))) (value.interpret s)) := by
  have hm : data.cache (.hash (p.input P (s p.key))) = none := by
    cases hc : data.cache (.hash (p.input P (s p.key))) with
    | none => rfl
    | some old =>
        have he := h.cache_le hc
        rw [hq] at he
        cases he
  refine ⟨?_, ?_⟩
  · intro query hn
    by_cases he : query = .hash (p.input P (s p.key))
    · subst query
      exact (hn ⟨hm, Or.inl ⟨p, value, Function.update_self .., rfl⟩⟩).elim
    · rw [QueryCache.cacheQuery_of_ne _ _ he]
      apply h.agree query
      intro hs
      apply hn
      refine ⟨hs.1, ?_⟩
      rcases hs.2 with hs | hs
      · obtain ⟨other, answer, ho, hquery⟩ := hs
        have hne : other ≠ p := by
          intro heq
          subst other
          rw [hp] at ho
          cases ho
        exact Or.inl ⟨other, answer, by simpa only [Function.update_of_ne hne] using ho, hquery⟩
      · exact Or.inr hs
  · intro other answer ho
    by_cases he : other = p
    · subst other
      change Function.update data.pending p (some value) p = some answer at ho
      simp only [Function.update_self, Option.some.injEq] at ho
      subst answer
      exact QueryCache.cacheQuery_self ..
    · change Function.update data.pending p (some value) other = some answer at ho
      rw [Function.update_of_ne he] at ho
      exact QueryCache.le_cacheQuery actual hq (h.pending other answer ho)

/-- A fresh virtual PRF call also grows the suspended set while preserving all
earlier pending hash answers. Previously sampled term values remain in the real
cache until the adaptive slack programming step materializes them. -/
theorem CacheRelation.allocateVirtual {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (T : C.Term) (p : Point) (value : HashOutput)
    (hq : actual (.prf (seeds T) p) = none) :
    CacheRelation P seeds s { data with virtual := insert (T, p) data.virtual }
      (actual.cacheQuery (.prf (seeds T) p) value) := by
  have hm : data.cache (.prf (seeds T) p) = none := by
    cases hc : data.cache (.prf (seeds T) p) with
    | none => rfl
    | some old =>
        have he := h.cache_le hc
        rw [hq] at he
        cases he
  refine ⟨?_, ?_⟩
  · intro query hn
    by_cases he : query = .prf (seeds T) p
    · subst query
      exact (hn ⟨hm, Or.inr ⟨T, p, Finset.mem_insert_self _ _, rfl⟩⟩).elim
    · rw [QueryCache.cacheQuery_of_ne _ _ he]
      apply h.agree query
      intro hs
      apply hn
      refine ⟨hs.1, ?_⟩
      rcases hs.2 with hs | hs
      · exact Or.inl hs
      · obtain ⟨U, point, hu, hquery⟩ := hs
        exact Or.inr ⟨U, point, Finset.mem_insert_of_mem hu, hquery⟩
  · intro other answer ho
    exact QueryCache.le_cacheQuery actual hq (h.pending other answer ho)

set_option backward.isDefEq.respectTransparency false in
/-- The actual slack sampler uses the truncation of a fresh full hash answer
for its high half. This has the existing leanVM programmed-answer law. -/
theorem evalDist_slack_high (target others : Digest) :
    𝒟[(fun high : HashOutput => XmssSecurity.Rom.hashOutputEquivDigestPair.symm
      (truncateHash high, target ^^^ others)) <$> ($ᵗ HashOutput)] =
    𝒟[XmssSecurity.Rom.sampleHashOutputWithDigest (target ^^^ others)] := by
  rw [XmssSecurity.Rom.sampleHashOutputWithDigest]
  calc
    _ = 𝒟[(fun high : Digest => XmssSecurity.Rom.hashOutputEquivDigestPair.symm
        (high, target ^^^ others)) <$> (truncateHash <$> ($ᵗ HashOutput))] := by
      simp only [Functor.map_map]
    _ = _ := by
      have ht : 𝒟[truncateHash <$> ($ᵗ HashOutput)] = 𝒟[$ᵗ Digest] :=
        XmssSecurity.Rom.evalDist_truncate_uniformHashOutput
      rw [evalDist_map, ht, ← evalDist_map]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- For any already-fixed other-term aggregate, a fresh uniform target and the
compiler's sampled high half are exactly a uniform ordinary PRF answer paired
with the aggregate it determines. -/
theorem evalDist_slack_target (others : Digest) :
    𝒟[(do
      let target ← $ᵗ Digest
      let high ← $ᵗ HashOutput
      pure (target, XmssSecurity.Rom.hashOutputEquivDigestPair.symm
        (truncateHash high, target ^^^ others)) : ProbComp (Digest × HashOutput))] =
      𝒟[(fun value : HashOutput => (truncateHash value ^^^ others, value)) <$> ($ᵗ HashOutput)] := by
  have hbij : Function.Bijective (fun value : Digest => value ^^^ others) :=
    (show Function.Involutive (fun value : Digest => value ^^^ others) from
      fun value => by simp [BitVec.xor_assoc]).bijective
  have hshift :
      𝒟[(do
        let target ← $ᵗ Digest
        let value ← XmssSecurity.Rom.sampleHashOutputWithDigest (target ^^^ others)
        pure (target, value) : ProbComp (Digest × HashOutput))] =
      𝒟[(fun pair : Digest × HashOutput => (pair.1 ^^^ others, pair.2)) <$>
        XmssSecurity.Rom.sampledHashOutputWithDigest] := by
    apply evalDist_ext
    intro result
    have ht := probOutput_bind_bijective_uniform_cross (α := Digest)
      (fun value : Digest => value ^^^ others) hbij
      (fun target => do
        let value ← XmssSecurity.Rom.sampleHashOutputWithDigest (target ^^^ others)
        pure (target, value)) result
    simp only [XmssSecurity.Rom.sampledHashOutputWithDigest, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_apply, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero] at ht ⊢
    convert ht.symm using 1
    rfl
  calc
    _ = 𝒟[(do
        let target ← $ᵗ Digest
        let value ← XmssSecurity.Rom.sampleHashOutputWithDigest (target ^^^ others)
        pure (target, value) : ProbComp (Digest × HashOutput))] := by
      refine OracleComp.DeferredSampling.evalDist_bind_congr_left ($ᵗ Digest) _ _
        (fun target => ?_)
      calc
        _ = 𝒟[(fun value : HashOutput => (target, value)) <$>
            ((fun high : HashOutput => XmssSecurity.Rom.hashOutputEquivDigestPair.symm
              (truncateHash high, target ^^^ others)) <$> ($ᵗ HashOutput))] := by
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        _ = _ := by
          rw [evalDist_map, evalDist_slack_high, ← evalDist_map]
          rw [map_eq_bind_pure_comp]
          rfl
    _ = 𝒟[(fun pair : Digest × HashOutput => (pair.1 ^^^ others, pair.2)) <$>
        XmssSecurity.Rom.sampledHashOutputWithDigest] := hshift
    _ = _ := by
      rw [evalDist_map, XmssSecurity.Rom.evalDist_sampledHashOutputWithDigest_eq_uniform,
        ← evalDist_map, Functor.map_map]
      rfl

/-- An ordinary slack answer determines the aggregate while all other term
values remain fixed. -/
theorem termSum_slack_output (values : C.Term → Digest) (slack : C.Term) (output : HashOutput) :
    termSum (Function.update values slack (truncateHash output)) =
      truncateHash output ^^^ otherTermSum values slack := by
  have h := termSum_program values slack (truncateHash output ^^^ otherTermSum values slack)
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using h

/-- The joint local law used at an adaptively selected absent term. `values`
and `slack` may be selected from the prior cache; the sampled target is fresh.
The existing cache entries are represented unchanged by `values` off `slack`. -/
theorem evalDist_slack_program (values : C.Term → Digest) (slack : C.Term) :
    𝒟[(do
      let target ← $ᵗ Digest
      let high ← $ᵗ HashOutput
      pure (target, XmssSecurity.Rom.hashOutputEquivDigestPair.symm
        (truncateHash high, target ^^^ otherTermSum values slack)) : ProbComp (Digest × HashOutput))] =
      𝒟[(fun output : HashOutput =>
        (termSum (Function.update values slack (truncateHash output)), output)) <$> ($ᵗ HashOutput)] := by
  simpa only [termSum_slack_output] using evalDist_slack_target (otherTermSum values slack)

set_option backward.isDefEq.respectTransparency false in
/-- Uncounted source bookkeeping uses the fixed compiler without changing its
counter, reveal table, or hit flag. -/
theorem runSource_deferredQuery_uncounted (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C) (ht : ¬deferredCounted t)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery t)) source backend =
      (fun r => ((r.1, source), ((r.2, backend.1.2), backend.2.1, backend.2.2))) <$>
        ((compilerImpl P seeds t).run backend.1.1) := by
  change (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
      (deferredQuery t >>= fun value => pure (value, source))).run backend = _
  simp only [deferredQuery, HasQuery.instOfMonadLift_query]
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl, StateT.run_mk,
    cappedCall, ht, false_and, decide_false, Bool.or_false, if_false, Nat.add_zero,
    bind_map_left, Functor.map_map]
  rfl

theorem runSource_inspect (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) (.inspect p))) source backend =
      pure ((backend.1.1.data.pending p, source), backend) := by
  rw [runSource_deferredQuery_uncounted P seeds q s (.inspect p) (by exact not_false)]
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure]
  rfl

theorem runSource_modify (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (f : SourceState C → SourceState C)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (modify f) source backend = pure (((), f source), backend) := by
  simp only [runSource, StateT.run_modify, simulateQ_pure, StateT.run_pure]

/-- Revealing a coordinate changes only the source's stored revealed values. -/
theorem sourceReveal_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (k : HiddenKey)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReveal k) source backend)) :
    r.1.2 = { source with revealed := r.1.2.revealed } := by
  cases hk : source.revealed k with
  | some value =>
      rw [runSource_sourceReveal_cached P seeds q s k source backend value hk,
        mem_support_pure_iff] at hr
      subst r
      rfl
  | none =>
      rw [runSource_sourceReveal_fresh P seeds q s k source backend hk,
        mem_support_pure_iff] at hr
      subst r
      rfl

/-- Materialization reads precisely the selected symbolic coordinate. Its
source frame and concrete backend are preserved apart from revealed values. -/
theorem sourceRevealDigest_correct (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (value : DeferredDigest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : RevealRelation s source backend)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceRevealDigest value) source backend)) :
    r.1.1 = value.interpret s ∧ RevealRelation s r.1.2 r.2 ∧
      r.2.1 = backend.1 ∧ r.2.2.2 = backend.2.2 ∧
      r.1.2 = { source with revealed := r.1.2.revealed } := by
  cases value with
  | known value =>
      rw [sourceRevealDigest, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨rfl, h, rfl, rfl, rfl⟩
  | secret k =>
      obtain ⟨hv, hs, hc, hf⟩ := sourceReveal_correct P seeds q s k source backend h r hr
      exact ⟨hv, hs, hc, hf, sourceReveal_frame P seeds q s k source backend r hr⟩

/-- The source's planting instruction is exactly the conservative deferred
cache update inside the fixed capped backend. -/
theorem runSource_plant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (input : PlantInput) (value : HashOutput)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) (.plant input value))) source backend =
      (fun r => ((r.1, source),
        (({ backend.1.1 with data := r.2 }, backend.1.2), backend.2.1, backend.2.2))) <$>
          ((deferredImpl (.plant input value)).run backend.1.1.data) := by
  rw [runSource_deferredQuery_uncounted P seeds q s (.plant input value) (by exact not_false)]
  simp only [compilerImpl, StateT.run, Functor.map_map]

/-- The live planting routine preserves both relations and succeeds even when
the concrete commitment was queried earlier. It materializes the symbolic next
secret through the reveal interface, without changing source control data,
the compiler trace, or either counter/flag. -/
theorem sourcePlant_correct (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C) (actual : HashCache C)
    (hrev : RevealRelation s source backend)
    (hcache : CacheRelation P seeds s backend.1.1.data actual)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    RevealRelation s r.1.2 r.2 ∧ CacheRelation P seeds s r.2.1.1.data actual ∧
      r.1.2 = { source with revealed := r.1.2.revealed } ∧
      r.2.1 = ({ backend.1.1 with data := r.2.1.1.data }, backend.1.2) ∧
      r.2.2.2 = backend.2.2 := by
  simp only [sourcePlant, runSource_bind, runSource_inspect,
    mem_support_bind_iff] at hr
  obtain ⟨_, rfl, hr⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | none =>
      simp only [hp, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨hrev, hcache, rfl, rfl, rfl⟩
  | some answer =>
      simp only [hp, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨ri, hri, rl, hrl, rp, hrp, hr⟩ := hr
      obtain ⟨hi, hriRev, hriBackend, hriFlag⟩ :=
        sourceReveal_correct P seeds q s p.key source backend hrev ri hri
      have hriSource := sourceReveal_frame P seeds q s p.key source backend ri hri
      obtain ⟨hl, hrlRev, hrlBackend, hrlFlag, hrlSource⟩ :=
        sourceRevealDigest_correct P seeds q s answer.low ri.1.2 ri.2 hriRev rl hrl
      have hb : rl.2.1 = backend.1 := hrlBackend.trans hriBackend
      have hc : CacheRelation P seeds s rl.2.1.1.data actual := by
        rw [hb]
        exact hcache
      rw [runSource_plant] at hrp
      simp only [support_map] at hrp
      obtain ⟨planted, hplanted, rfl⟩ := hrp
      have hv : actual (PlantInput.pending P p ri.1.1).query =
          some (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, rl.1.1)) := by
        rw [hi, hl]
        exact hcache.pending p answer hp
      obtain ⟨hok, hfinal⟩ := deferredPlant_correct P seeds s rl.2.1.1.data actual hc
        (.pending P p ri.1.1) _ hv planted hplanted
      simp only [runSource_modify, mem_support_pure_iff, hok, Bool.and_true] at hr
      subst r
      refine ⟨hrlRev, hfinal, ?_, ?_, hrlFlag.trans hriFlag⟩
      · rw [hrlSource, hriSource]
      · simp only [hb]

set_option backward.isDefEq.respectTransparency false in
/-- At an internal edge the actual pending sampler draws only a uniform high
half; its low half stays the exact symbolic next-coordinate. -/
theorem evalDist_samplePending_internal (p : PendingInput) (k : HiddenKey)
    (hk : p.next = some k) :
    𝒟[samplePending p] =
      𝒟[(fun high : Digest => (⟨high, .secret k⟩ : DeferredOutput)) <$> ($ᵗ Digest)] := by
  have hsplit :
      𝒟[(XmssSecurity.Rom.hashOutputEquivDigestPair : HashOutput → Digest × Digest) <$>
        ($ᵗ HashOutput)] = 𝒟[XmssSecurity.Rom.independentDigestHalves] :=
    XmssSecurity.Rom.evalDist_split_uniformHashOutput_eq_independent
  calc
    _ = 𝒟[(fun halves : Digest × Digest => (⟨halves.1, .secret k⟩ : DeferredOutput)) <$>
        (XmssSecurity.Rom.hashOutputEquivDigestPair <$> ($ᵗ HashOutput))] := by
      simp only [samplePending, hk, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
    _ = 𝒟[(fun halves : Digest × Digest => (⟨halves.1, .secret k⟩ : DeferredOutput)) <$>
        XmssSecurity.Rom.independentDigestHalves] := by
      rw [evalDist_map, hsplit, ← evalDist_map]
    _ = _ := by
      simp only [XmssSecurity.Rom.independentDigestHalves, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro high
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ Digest) (probFailure_uniformSample _) _

set_option backward.isDefEq.respectTransparency false in
/-- Sampling the next coordinate and then the fixed internal pending sampler
is exactly a uniform oracle answer paired with its actual low half. -/
theorem evalDist_samplePending_fresh_next (p : PendingInput) (k : HiddenKey)
    (hk : p.next = some k) (s : HiddenKey → Digest) :
    𝒟[(do
      let next ← $ᵗ Digest
      let answer ← samplePending p
      pure (next, answer.interpret (Function.update s k next)) : ProbComp (Digest × HashOutput))] =
      𝒟[(fun output : HashOutput => (truncateHash output, output)) <$> ($ᵗ HashOutput)] := by
  calc
    _ = 𝒟[XmssSecurity.Rom.sampledHashOutputWithDigest] := by
      change _ = 𝒟[(do
        let next ← $ᵗ Digest
        let output ← XmssSecurity.Rom.sampleHashOutputWithDigest next
        pure (next, output) : ProbComp (Digest × HashOutput))]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro next
      change 𝒟[(fun answer : DeferredOutput =>
        (next, answer.interpret (Function.update s k next))) <$> samplePending p] = _
      rw [evalDist_map, evalDist_samplePending_internal p k hk, ← evalDist_map]
      simp only [DeferredOutput.interpret, DeferredDigest.interpret,
        Function.update_self, XmssSecurity.Rom.sampleHashOutputWithDigest,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      rfl
    _ = _ := XmssSecurity.Rom.evalDist_sampledHashOutputWithDigest_eq_uniform

set_option backward.isDefEq.respectTransparency false in
/-- A fresh terminal pending call has the ordinary lazy-oracle law, including
its full cache update and the newly allocated symbolic-table entry. -/
theorem relTriple_deferredPending_terminal (P : PublicParameter)
    (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (p : PendingInput)
    (hn : p.next = none) (hp : data.pending p = none)
    (ha : actual (.hash (p.input P (s p.key))) = none) :
    RelTriple (((Query C →ₒ HashOutput).randomOracle (.hash (p.input P (s p.key)))).run actual)
      ((deferredImpl (.pending p)).run data)
      (fun a b => a.1 = b.1.interpret s ∧ CacheRelation P seeds s b.2 a.2) := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ ha]
  have hd : (deferredImpl (C := C) (.pending p)).run data =
      (fun output : HashOutput =>
        let halves := XmssSecurity.Rom.hashOutputEquivDigestPair output
        let answer : DeferredOutput := ⟨halves.1, .known halves.2⟩
        (answer, { data with pending := Function.update data.pending p (some answer) })) <$>
        ($ᵗ HashOutput) := by
    simp only [deferredImpl, StateT.run, hp, samplePending, hn,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  change RelTriple
    ((fun output : HashOutput => (output, actual.cacheQuery (.hash (p.input P (s p.key))) output)) <$>
      ($ᵗ HashOutput))
    ((deferredImpl (.pending p)).run data) _
  rw [hd]
  refine relTriple_map (relTriple_post_mono (relTriple_refl _) fun output output' he => ?_)
  subst output'
  have hi : (⟨(XmssSecurity.Rom.hashOutputEquivDigestPair output).1,
      .known (XmssSecurity.Rom.hashOutputEquivDigestPair output).2⟩ : DeferredOutput).interpret s =
      output := XmssSecurity.Rom.hashOutputEquivDigestPair.symm_apply_apply output
  refine ⟨hi.symm, ?_⟩
  simpa only [hi] using h.allocatePending p
    ⟨(XmssSecurity.Rom.hashOutputEquivDigestPair output).1,
      .known (XmssSecurity.Rom.hashOutputEquivDigestPair output).2⟩ hp ha

set_option backward.isDefEq.respectTransparency false in
/-- The next coordinate and the actual symbolic answer retain both halves of
the same fresh ordinary hash output. -/
theorem evalDist_samplePending_pair (p : PendingInput) (k : HiddenKey)
    (hk : p.next = some k) :
    𝒟[(do
      let next ← $ᵗ Digest
      let answer ← samplePending p
      pure (next, answer) : ProbComp (Digest × DeferredOutput))] =
      𝒟[(fun output : HashOutput => (truncateHash output,
        (⟨(XmssSecurity.Rom.hashOutputEquivDigestPair output).1, .secret k⟩ : DeferredOutput))) <$>
        ($ᵗ HashOutput)] := by
  calc
    _ = 𝒟[(do
        let next ← $ᵗ Digest
        let high ← $ᵗ Digest
        pure (next, (⟨high, .secret k⟩ : DeferredOutput)) : ProbComp (Digest × DeferredOutput))] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro next
      change 𝒟[(fun answer : DeferredOutput => (next, answer)) <$> samplePending p] = _
      rw [evalDist_map, evalDist_samplePending_internal p k hk, ← evalDist_map]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    _ = 𝒟[(do
        let high ← $ᵗ Digest
        let next ← $ᵗ Digest
        pure (next, (⟨high, .secret k⟩ : DeferredOutput)) : ProbComp (Digest × DeferredOutput))] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[(fun halves : Digest × Digest =>
        (halves.2, (⟨halves.1, .secret k⟩ : DeferredOutput))) <$>
        XmssSecurity.Rom.independentDigestHalves] := by
      simp only [XmssSecurity.Rom.independentDigestHalves, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, Function.comp_apply]
      rfl
    _ = _ := by
      rw [evalDist_map, ← XmssSecurity.Rom.evalDist_split_uniformHashOutput_eq_independent,
        ← evalDist_map, Functor.map_map]
      rfl

/-- An internal edge never has its own input as its next coordinate. -/
theorem pending_next_ne_key (p : PendingInput) (k : HiddenKey)
    (hk : p.next = some k) : k ≠ p.key := by
  cases p with
  | commitment e => cases hk
  | base lay e message => cases hk
  | bottom e l pos =>
      simp only [PendingInput.next] at hk
      split at hk
      · cases hk
        intro he
        have hv := congrArg (fun key => match key with
          | .bottomChain _ _ position => position.val
          | _ => 0) he
        change pos.val + 1 = pos.val at hv
        omega
      · cases hk
  | top b l pos =>
      simp only [PendingInput.next] at hk
      split at hk
      · cases hk
        intro he
        have hv := congrArg (fun key => match key with
          | .topChain _ _ position => position.val
          | _ => 0) he
        change pos.val + 1 = pos.val at hv
        omega
      · cases hk

/-- Updating a coordinate not yet used by any pending input or low half leaves
the established cache relation unchanged. This is the local dependency check
needed before drawing an internal chain's next coordinate. -/
theorem CacheRelation.updateSecret {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (k : HiddenKey) (value : Digest)
    (hkeys : ∀ p answer, data.pending p = some answer → p.key ≠ k)
    (hlows : ∀ p answer, data.pending p = some answer → answer.low ≠ .secret k) :
    CacheRelation P seeds (Function.update s k value) data actual := by
  refine ⟨?_, ?_⟩
  · intro query hn
    apply h.agree query
    rintro ⟨hc, hp | hv⟩
    · obtain ⟨p, answer, hp, hq⟩ := hp
      apply hn
      refine ⟨hc, Or.inl ⟨p, answer, hp, ?_⟩⟩
      simpa only [Function.update_of_ne (hkeys p answer hp)] using hq
    · exact hn ⟨hc, Or.inr hv⟩
  · intro p answer hp
    rw [Function.update_of_ne (hkeys p answer hp)]
    have he : answer.interpret (Function.update s k value) = answer.interpret s := by
      unfold DeferredOutput.interpret
      cases hl : answer.low with
      | known d => rfl
      | secret key =>
          have hk : key ≠ k := by
            intro he
            exact hlows p answer hp (he ▸ hl)
          simp only [DeferredDigest.interpret, Function.update_of_ne hk]
    rw [he]
    exact h.pending p answer hp

set_option backward.isDefEq.respectTransparency false in
/-- One internal chain edge couples the real cache call to the fixed pending
interpreter. The fresh next coordinate is kept in the output of this local
resampling lemma; it is the low half of that very same real oracle answer. -/
theorem relTriple_deferredPending_internal (P : PublicParameter)
    (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (p : PendingInput) (k : HiddenKey)
    (hn : p.next = some k) (hp : data.pending p = none)
    (ha : actual (.hash (p.input P (s p.key))) = none)
    (hkeys : ∀ prior answer, data.pending prior = some answer → prior.key ≠ k)
    (hlows : ∀ prior answer, data.pending prior = some answer → answer.low ≠ .secret k) :
    RelTriple
      ((fun r : HashOutput × HashCache C => ((truncateHash r.1, r.1), r.2)) <$>
        (((Query C →ₒ HashOutput).randomOracle (.hash (p.input P (s p.key)))).run actual))
      (do
        let next ← $ᵗ Digest
        let r ← (deferredImpl (.pending p)).run data
        pure ((next, r.1), r.2))
      (fun a b => a.1.1 = b.1.1 ∧
        a.1.2 = b.1.2.interpret (Function.update s k b.1.1) ∧
        CacheRelation P seeds (Function.update s k b.1.1) b.2 a.2) := by
  let symbolic (output : HashOutput) : DeferredOutput :=
    ⟨(XmssSecurity.Rom.hashOutputEquivDigestPair output).1, .secret k⟩
  have hright :
      𝒟[(do
        let next ← $ᵗ Digest
        let r ← (deferredImpl (.pending p)).run data
        pure ((next, r.1), r.2) : ProbComp ((Digest × DeferredOutput) × DeferredState C))] =
      𝒟[(fun output : HashOutput =>
        ((truncateHash output, symbolic output),
          { data with pending := Function.update data.pending p (some (symbolic output)) })) <$>
          ($ᵗ HashOutput)] := by
    calc
      _ = 𝒟[(fun pair : Digest × DeferredOutput =>
          (pair, { data with pending := Function.update data.pending p (some pair.2) })) <$>
          (do
            let next ← $ᵗ Digest
            let answer ← samplePending p
            pure (next, answer))] := by
        simp only [deferredImpl, StateT.run, hp, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, Function.comp_apply]
        rfl
      _ = _ := by
        rw [evalDist_map, evalDist_samplePending_pair p k hn, ← evalDist_map, Functor.map_map]
  refine relTriple_of_evalDist_eq_right
    (oa := ((fun r : HashOutput × HashCache C => ((truncateHash r.1, r.1), r.2)) <$>
      (((Query C →ₒ HashOutput).randomOracle (.hash (p.input P (s p.key)))).run actual)))
    hright.symm ?_
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ ha, Functor.map_map]
  refine relTriple_map (relTriple_post_mono (relTriple_refl ($ᵗ HashOutput))
    fun output output' he => ?_)
  subst output'
  have hkey : p.key ≠ k := (pending_next_ne_key p k hn).symm
  have hi : (symbolic output).interpret (Function.update s k (truncateHash output)) = output := by
    simp only [symbolic, DeferredOutput.interpret, DeferredDigest.interpret, Function.update_self]
    exact XmssSecurity.Rom.hashOutputEquivDigestPair.symm_apply_apply output
  refine ⟨rfl, hi.symm, ?_⟩
  have hinput : Function.update s k (truncateHash output) p.key = s p.key :=
    Function.update_of_ne hkey _ _
  have ha' : actual (.hash (p.input P (Function.update s k (truncateHash output) p.key))) = none := by
    rw [hinput]
    exact ha
  have hc := (h.updateSecret k (truncateHash output) hkeys hlows).allocatePending
    p (symbolic output) hp ha'
  rw [hinput, hi] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- Message trials can be coupled directly on the two concrete caches even
while any number of symbolic inputs or virtual PRF terms remain suspended. -/
theorem relTriple_messageHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) (input : HashInput) (hm : IsMsg input) :
    RelTriple (((Query C →ₒ HashOutput).randomOracle (.hash input)).run actual)
      (((Query C →ₒ HashOutput).randomOracle (.hash input)).run data.cache)
      (fun a b => a.1 = b.1 ∧ CacheRelation P seeds s { data with cache := b.2 } a.2) := by
  have he := h.message input hm
  cases hc : data.cache (.hash input) with
  | some value =>
      have ha := he.trans hc
      simp only [OracleSpec.randomOracle,
        QueryImpl.withCaching_run_some _ ha, QueryImpl.withCaching_run_some _ hc]
      exact relTriple_pure_pure ⟨rfl, h⟩
  | none =>
      have ha := he.trans hc
      simp only [OracleSpec.randomOracle,
        QueryImpl.withCaching_run_none _ ha, QueryImpl.withCaching_run_none _ hc]
      refine relTriple_map (relTriple_post_mono (relTriple_refl _) fun value value' hv => ?_)
      subst value'
      exact ⟨rfl, h.cacheQuery (.hash input) value ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual bounded message grind has the same answers on related caches.
This includes already-cached trials and preserves the entire suspended set. -/
theorem relTriple_grind (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (lay : Layer) (e : KeyIndex) (message : HashInput)
    (base : Digest) :
    ∀ (attempts trial : ℕ) (data : DeferredState C) (actual : HashCache C),
      CacheRelation P seeds s data actual →
      RelTriple
        ((simulateQ (Query C →ₒ HashOutput).randomOracle
          (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
            (grind P lay e message base attempts trial))).run actual)
        ((simulateQ (Query C →ₒ HashOutput).randomOracle
          (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
            (grind P lay e message base attempts trial))).run data.cache)
        (fun a b => a.1 = b.1 ∧ CacheRelation P seeds s { data with cache := b.2 } a.2) := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial data actual h
      simp only [grind, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, h⟩
  | succ attempts ih =>
      intro trial data actual h
      simp only [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash,
        HasQuery.instOfMonadLift_query, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, bind_assoc, pure_bind]
      refine relTriple_bind
        (relTriple_messageHash P seeds s data actual h _
          (SigningLane2BridgeProof.isMsg_trialInput P lay e message base trial)) ?_
      intro a b hab
      obtain ⟨he, hc⟩ := hab
      rw [he]
      cases hdecode : Codeword.decode (truncateHash b.1) with
      | some encoding =>
          simp only [simulateQ_pure, StateT.run_pure]
          exact relTriple_pure_pure ⟨rfl, hc⟩
      | none => exact ih (trial + 1) { data with cache := b.2 } a.2 hc

/-- The silent cached-base grind preserves the multi-point cache relation. -/
theorem relTriple_baseGrind (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (e : KeyIndex) (message : Message) (answer : HashOutput)
    (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) :
    RelTriple
      ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningFlatEagerProof.baseGrind P e message answer)).run actual)
      ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningFlatEagerProof.baseGrind P e message answer)).run data.cache)
      (fun a b => a.1 = b.1 ∧ CacheRelation P seeds s { data with cache := b.2 } a.2) := by
  simp only [SigningFlatEagerProof.baseGrind, simulateQ_map, StateT.run_map]
  exact relTriple_map (relTriple_post_mono
    (relTriple_grind P seeds s bottomLayer e (bytesLE 32 message) (truncateHash answer)
      randomizerAttemptLimit 0 data actual h) (fun _ _ hab => ⟨by trivial, hab.2⟩))

/-- Once the trigger parameters agree, the exact cached-extra program used by
the fixed compiler couples on the two caches, including all cached trials. -/
theorem relTriple_cachedExtra (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (before after : SigningFlatProof.FlatState C)
    (call : (WorldSpec C).Domain) (data : DeferredState C) (actual : HashCache C)
    (h : CacheRelation P seeds s data actual) :
    RelTriple
      ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningR1FixedProof.cachedExtra seeds P before call after)).run actual)
      ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningR1FixedProof.cachedExtra seeds P before call after)).run data.cache)
      (fun a b => a.1 = b.1 ∧ CacheRelation P seeds s { data with cache := b.2 } a.2) := by
  unfold SigningR1FixedProof.cachedExtra
  split
  · unfold SigningFlatEagerProof.grindExtra
    split
    · split
      · split
        · exact relTriple_baseGrind P seeds s _ _ _ data actual h
        · simp only [simulateQ_pure, StateT.run_pure]
          exact relTriple_pure_pure ⟨by trivial, h⟩
      · simp only [simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨by trivial, h⟩
    · simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨by trivial, h⟩
  · simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨by trivial, h⟩

/-- The complete message-cache view is identical under the concrete cache
relation, even when the underlying caches contain different hidden entries. -/
theorem CacheRelation.keptView {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) :
    SigningLane2BridgeProof.keptView IsMsg actual =
      SigningLane2BridgeProof.keptView IsMsg data.cache := by
  funext input
  unfold SigningLane2BridgeProof.keptView
  split
  · exact h.message input ‹IsMsg input›
  · rfl

theorem runSource_snapshot (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) .snapshot)) source backend =
      pure ((backend.1.1.data, source), backend) := by
  rw [runSource_deferredQuery_uncounted P seeds q s .snapshot (by exact not_false)]
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure]
  rfl

theorem runSource_sample (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) .sample)) source backend =
      (fun value : HashOutput => ((value, source), backend)) <$> ($ᵗ HashOutput) := by
  rw [runSource_deferredQuery_uncounted P seeds q s .sample (by exact not_false)]
  simp only [compilerImpl, deferredImpl, StateT.run, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Silent filling issues no replacement at a cached term, and otherwise
samples exactly one ordinary full PRF answer while preserving all other data. -/
theorem runSource_fillTerm (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : Point) (T : C.Term)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (fillTerm seeds p T)) source backend =
      match backend.1.1.data.cache (.prf (seeds T) p) with
      | some _ => pure (((), source), backend)
      | none => (fun value : HashOutput => (((), source),
          (({ backend.1.1 with data := { backend.1.1.data with
            cache := backend.1.1.data.cache.cacheQuery (.prf (seeds T) p) value } },
            backend.1.2), backend.2.1, backend.2.2))) <$> ($ᵗ HashOutput) := by
  simp only [fillTerm, liftM_bind, runSource_bind, runSource_snapshot]
  change runSource P seeds q s
    (liftM (if (backend.1.1.data.cache (.prf (seeds T) p)).isNone then do
      let value ← deferredQuery (C := C) .sample
      let _ ← deferredQuery (.plant (.prf (seeds T) p) value)
      pure ()
    else pure ())) source backend = _
  cases hc : backend.1.1.data.cache (.prf (seeds T) p) with
  | some prior =>
      simp only [Option.isNone_some, Bool.false_eq_true, if_false, liftM_pure, runSource_pure]
  | none =>
      simp only [Option.isNone_none, if_true, liftM_bind, liftM_pure,
        runSource_bind, runSource_sample, bind_map_left,
        runSource_plant, deferredImpl, StateT.run, PlantInput.query, runSource_pure]
      simp only [map_eq_bind_pure_comp, pure_bind, hc]
      rfl

theorem firstUnmaterialized_some (seeds : C.Term → HashOutput) (data : DeferredState C)
    (p : Point) (slack : C.Term) (h : firstUnmaterialized seeds data p = some slack) :
    data.cache (.prf (seeds slack) p) = none := by
  have hm := List.find?_some h
  exact Option.isNone_iff_eq_none.mp hm

theorem firstUnmaterialized_none_iff (seeds : C.Term → HashOutput) (data : DeferredState C)
    (p : Point) : firstUnmaterialized seeds data p = none ↔
      ∀ T : C.Term, ∃ value, data.cache (.prf (seeds T) p) = some value := by
  rw [firstUnmaterialized, List.find?_eq_none]
  constructor
  · intro h T
    have ht := h T (mem_terms T)
    cases hc : data.cache (.prf (seeds T) p) with
    | none => exact (ht (by rw [hc]; rfl)).elim
    | some value => exact ⟨value, rfl⟩
  · intro h T _
    obtain ⟨value, hv⟩ := h T
    simp only [hv, Option.isNone_some, Bool.false_eq_true, not_false_eq_true]

/-- Injective term seeds make the final slack write change precisely its one
summand, preserving every previously materialized term value. -/
theorem cachedTerm_cacheQuery (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (data : DeferredState C) (p : Point) (T : C.Term) (value : HashOutput) :
    cachedTerm seeds { data with cache := data.cache.cacheQuery (.prf (seeds T) p) value } p =
      Function.update (cachedTerm seeds data p) T (truncateHash value) := by
  funext U
  by_cases hu : U = T
  · subst U
    simp only [cachedTerm, QueryCache.cacheQuery_self, Option.getD_some, Function.update_self]
  · have hq : (Query.prf (seeds U) p : Query C) ≠ .prf (seeds T) p := by
      intro he
      exact hu (hinj (Query.prf.inj he).1)
    simp only [cachedTerm, QueryCache.cacheQuery_of_ne _ _ hq, Function.update_of_ne hu]

/-- The final concrete slack answer used by `completePrf` makes the aggregate
exactly its supplied target; the choice of the slack term may be adaptive. -/
theorem termSum_final_slack (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (data : DeferredState C) (p : Point) (slack : C.Term) (target : Digest) (high : HashOutput) :
    termSum (cachedTerm seeds
      { data with cache := (data.cache.cacheQuery (.prf (seeds slack) p)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
          (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds data p) slack))) } p) = target := by
  rw [cachedTerm_cacheQuery seeds hinj]
  have hlow : truncateHash (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
      (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds data p) slack)) =
      target ^^^ otherTermSum (cachedTerm seeds data p) slack :=
    congrArg Prod.snd (XmssSecurity.Rom.hashOutputEquivDigestPair.apply_symm_apply _)
  rw [hlow]
  exact termSum_program _ _ _

/-- The supported cache effect of the actual silent term fill. -/
theorem fillTerm_cache (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : Point) (T : C.Term)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (fillTerm seeds p T)) source backend)) :
    backend.1.1.data.cache ≤ r.2.1.1.data.cache ∧
      (∃ value, r.2.1.1.data.cache (.prf (seeds T) p) = some value) ∧
      ∀ query : Query C, query ≠ .prf (seeds T) p →
        r.2.1.1.data.cache query = backend.1.1.data.cache query := by
  rw [runSource_fillTerm] at hr
  cases hc : backend.1.1.data.cache (.prf (seeds T) p) with
  | some value =>
      simp only [hc, mem_support_pure_iff] at hr
      subst r
      exact ⟨le_rfl, ⟨value, hc⟩, fun _ _ => rfl⟩
  | none =>
      simp only [hc, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact ⟨QueryCache.le_cacheQuery _ hc, ⟨value, QueryCache.cacheQuery_self ..⟩,
        fun _ hn => QueryCache.cacheQuery_of_ne _ _ hn⟩

set_option backward.isDefEq.respectTransparency false in
/-- Filling a list preserves every other cache slot, including the missing
slack term that the source deliberately omits from this list. -/
theorem fillTerms_cache (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : Point) (terms : List C.Term) :
    ∀ (source : SourceState C) (backend : CappedCompilerState C)
      (r : (List Unit × SourceState C) × CappedCompilerState C),
      r ∈ support (runSource P seeds q s (liftM (terms.mapM (fillTerm seeds p))) source backend) →
      backend.1.1.data.cache ≤ r.2.1.1.data.cache ∧
        (∀ T ∈ terms, ∃ value, r.2.1.1.data.cache (.prf (seeds T) p) = some value) ∧
        ∀ query : Query C, (∀ T ∈ terms, query ≠ .prf (seeds T) p) →
          r.2.1.1.data.cache query = backend.1.1.data.cache query := by
  induction terms with
  | nil =>
      intro source backend r hr
      simp only [List.mapM_nil, liftM_pure, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨le_rfl, fun _ ht => (List.not_mem_nil ht).elim, fun _ _ => rfl⟩
  | cons T terms ih =>
      intro source backend r hr
      simp only [List.mapM_cons, liftM_bind, liftM_pure, runSource_bind,
        mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      obtain ⟨hhle, hhcached, hhother⟩ := fillTerm_cache P seeds q s p T source backend head hhead
      obtain ⟨htle, htcached, htother⟩ := ih head.1.2 head.2 tail htail
      refine ⟨hhle.trans htle, ?_, ?_⟩
      · intro U hu
        rcases List.mem_cons.mp hu with rfl | hu
        · obtain ⟨value, hv⟩ := hhcached
          exact ⟨value, htle hv⟩
        · exact htcached U hu
      · intro query hquery
        exact (htother query (fun U hu => hquery U (List.mem_cons_of_mem _ hu))).trans
          (hhother query (hquery T (List.mem_cons_self ..)))

set_option backward.isDefEq.respectTransparency false in
/-- The actual PRF completion always materializes every term. Its Boolean
result is exactly the aggregate consistency check, including the no-slack case;
when a slack term is present the final programmed aggregate is the target. -/
theorem completePrf_correct (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (p : Point) (target : Digest) (source : SourceState C) (backend : CappedCompilerState C)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (completePrf seeds p target)) source backend)) :
    (∀ T : C.Term, ∃ value, r.2.1.1.data.cache (.prf (seeds T) p) = some value) ∧
      (r.1.1 = true ↔ termSum (cachedTerm seeds r.2.1.1.data p) = target) ∧
      (firstUnmaterialized seeds backend.1.1.data p ≠ none → r.1.1 = true) := by
  simp only [completePrf, liftM_bind, runSource_bind, runSource_snapshot,
    mem_support_bind_iff] at hr
  obtain ⟨_, rfl, hr⟩ := hr
  cases hfirst : firstUnmaterialized seeds backend.1.1.data p with
  | none =>
      simp only [hfirst, liftM_pure, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨(firstUnmaterialized_none_iff seeds backend.1.1.data p).mp hfirst,
        by simp only [decide_eq_true_eq], fun h => (h rfl).elim⟩
  | some slack =>
      simp only [hfirst, liftM_bind, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨filled, hfilled, snapshot, hsnapshot, sampled, hsampled, hr⟩ := hr
      rw [runSource_snapshot, mem_support_pure_iff] at hsnapshot
      subst snapshot
      rw [runSource_sample] at hsampled
      simp only [support_map] at hsampled
      obtain ⟨high, _, rfl⟩ := hsampled
      obtain ⟨_, hall, hother⟩ := fillTerms_cache P seeds q s p
        (C.terms.filter (· ≠ slack)) source backend filled hfilled
      have hmissing : filled.2.1.1.data.cache (.prf (seeds slack) p) = none := by
        rw [hother (.prf (seeds slack) p)]
        · exact firstUnmaterialized_some seeds backend.1.1.data p slack hfirst
        · intro T ht
          have hn : T ≠ slack := of_decide_eq_true (List.mem_filter.mp ht).2
          intro he
          exact hn (hinj (Query.prf.inj he).1).symm
      let value : HashOutput := XmssSecurity.Rom.hashOutputEquivDigestPair.symm
        (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds filled.2.1.1.data p) slack)
      change r ∈ support (runSource P seeds q s
        (liftM (deferredQuery (C := C) (.plant (.prf (seeds slack) p) value)))
          filled.1.2 filled.2) at hr
      rw [runSource_plant P seeds q s (.prf (seeds slack) p) value filled.1.2 filled.2] at hr
      simp only [deferredImpl, StateT.run, PlantInput.query,
        hmissing, map_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨?_, ?_, fun _ => rfl⟩
      · intro T
        by_cases ht : T = slack
        · subst T
          exact ⟨_, QueryCache.cacheQuery_self ..⟩
        · obtain ⟨value, hv⟩ := hall T (List.mem_filter.mpr ⟨mem_terms T, by simpa using ht⟩)
          exact ⟨value, QueryCache.le_cacheQuery _ hmissing hv⟩
      · exact ⟨fun _ => termSum_final_slack seeds hinj filled.2.1.1.data p slack target high,
          fun _ => rfl⟩

/-- The aggregate installed at P is exactly the randomizer read by the
original cached-extra trigger. -/
theorem cachedRandomizer_termSum (seeds : C.Term → HashOutput) (data : DeferredState C)
    (e : KeyIndex) : SigningGuessProof.cachedRandomizer seeds data.cache e =
      termSum (cachedTerm seeds data (.randomizer bottomLayer e)) := by
  unfold SigningGuessProof.cachedRandomizer termSum cachedTerm
  change TprfCorrectnessProof.toXor
    ((C.terms.map fun T => truncateHash
      ((data.cache (.prf (seeds T) (.randomizer bottomLayer e))).getD 0)).foldl (· ^^^ ·) 0) = _
  rw [List.foldl_map, TprfCorrectnessProof.toXor_foldl _ _ _ terms_nodup]
  simp [TprfCorrectnessProof.toXor_zero, Committee.terms]

/-- PRF completion makes the precise cached-randomizer guard true, and its
reported consistency uses the same randomizer that the trace adapter reads. -/
theorem completePrf_randomizer (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (target : Digest) (source : SourceState C) (backend : CappedCompilerState C)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (completePrf seeds (.randomizer bottomLayer e) target)) source backend)) :
    SigningGuessProof.RandomizerCached seeds r.2.1.1.data.cache e ∧
      (r.1.1 = true ↔ SigningGuessProof.cachedRandomizer seeds r.2.1.1.data.cache e = target) ∧
      (firstUnmaterialized seeds backend.1.1.data (.randomizer bottomLayer e) ≠ none → r.1.1 = true) := by
  obtain ⟨hc, hv, hs⟩ := completePrf_correct P seeds hinj q s
    (.randomizer bottomLayer e) target source backend r hr
  exact ⟨hc, by rwa [cachedRandomizer_termSum], hs⟩

/-- Once the source has materialized a randomizer, its readiness and value
agree with the actual cache. This is the cache part of aligning the triggers. -/
theorem CacheRelation.randomizer {P : PublicParameter} {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {data : DeferredState C} {actual : HashCache C}
    (h : CacheRelation P seeds s data actual) (e : KeyIndex)
    (hc : SigningGuessProof.RandomizerCached seeds data.cache e) :
    SigningGuessProof.RandomizerCached seeds actual e ∧
      SigningGuessProof.cachedRandomizer seeds actual e =
        SigningGuessProof.cachedRandomizer seeds data.cache e := by
  refine ⟨?_, (SigningGuessProof.cachedRandomizer_stable seeds data.cache actual e h.cache_le hc).symm⟩
  intro T
  obtain ⟨value, hv⟩ := hc T
  exact ⟨value, h.cache_le hv⟩

/-- The concrete record update performed by a successful silent plant. -/
def replaceCompilerCache (backend : CappedCompilerState C) (cache : HashCache C) :
    CappedCompilerState C :=
  (({ backend.1.1 with data := { backend.1.1.data with cache := cache } }, backend.1.2),
    backend.2.1, backend.2.2)

set_option backward.isDefEq.respectTransparency false in
/-- The actual sampled-high and plant suffix of `completePrf`, when its
selected slot is still absent. The full capped backend is retained. -/
theorem runSource_slackPlant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : Point) (slack : C.Term) (target : Digest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hm : backend.1.1.data.cache (.prf (seeds slack) p) = none) :
    runSource P seeds q s (do
      let high ← liftM (deferredQuery (C := C) .sample)
      liftM (deferredQuery (C := C) (.plant (.prf (seeds slack) p)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
          (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds backend.1.1.data p) slack)))))
      source backend =
      (fun high : HashOutput => ((true, source), replaceCompilerCache backend
        (backend.1.1.data.cache.cacheQuery (.prf (seeds slack) p)
          (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
            (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds backend.1.1.data p) slack))))) <$>
        ($ᵗ HashOutput) := by
  simp only [runSource_bind, runSource_sample, bind_map_left]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro high
  let value : HashOutput := XmssSecurity.Rom.hashOutputEquivDigestPair.symm
    (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds backend.1.1.data p) slack)
  change runSource P seeds q s
    (liftM (deferredQuery (C := C) (.plant (.prf (seeds slack) p) value))) source backend =
    pure ((true, source), replaceCompilerCache backend
      (backend.1.1.data.cache.cacheQuery (.prf (seeds slack) p) value))
  rw [runSource_plant P seeds q s (.prf (seeds slack) p) value source backend]
  simp only [deferredImpl, StateT.run, PlantInput.query, hm, map_pure]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The fresh-target joint law now includes the actual source suffix and its
entire updated backend. The ordinary side uses the existing silent term fill;
the aggregate is read from its resulting concrete cache. -/
theorem evalDist_slackPlant_fresh (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (p : Point) (slack : C.Term) (source : SourceState C) (backend : CappedCompilerState C)
    (hm : backend.1.1.data.cache (.prf (seeds slack) p) = none) :
    𝒟[(do
      let target ← $ᵗ Digest
      let r ← runSource P seeds q s (do
        let high ← liftM (deferredQuery (C := C) .sample)
        liftM (deferredQuery (C := C) (.plant (.prf (seeds slack) p)
          (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
            (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds backend.1.1.data p) slack)))))
        source backend
      pure (target, r.2) : ProbComp (Digest × CappedCompilerState C))] =
    𝒟[(do
      let r ← runSource P seeds q s (liftM (fillTerm seeds p slack)) source backend
      pure (termSum (cachedTerm seeds r.2.1.1.data p), r.2) : ProbComp (Digest × CappedCompilerState C))] := by
  let write : Digest × HashOutput → Digest × CappedCompilerState C := fun pair =>
    (pair.1, replaceCompilerCache backend
      (backend.1.1.data.cache.cacheQuery (.prf (seeds slack) p) pair.2))
  have h :
      𝒟[write <$> (do
        let target ← $ᵗ Digest
        let high ← $ᵗ HashOutput
        pure (target, XmssSecurity.Rom.hashOutputEquivDigestPair.symm
          (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds backend.1.1.data p) slack)))] =
      𝒟[write <$> ((fun output : HashOutput =>
        (termSum (Function.update (cachedTerm seeds backend.1.1.data p) slack (truncateHash output)), output)) <$>
          ($ᵗ HashOutput))] := by
    rw [evalDist_map, evalDist_slack_program, ← evalDist_map]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, write] at h
  simp only [runSource_slackPlant P seeds q s p slack _ source backend hm,
    runSource_fillTerm, hm, bind_map_left]
  change _ = 𝒟[(do
    let value ← $ᵗ HashOutput
    pure (termSum (cachedTerm seeds
      { backend.1.1.data with cache := backend.1.1.data.cache.cacheQuery (.prf (seeds slack) p) value } p),
      replaceCompilerCache backend
        (backend.1.1.data.cache.cacheQuery (.prf (seeds slack) p) value)) :
        ProbComp (Digest × CappedCompilerState C))]
  simp only [cachedTerm_cacheQuery seeds hinj]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The live completion chooses the missing term, fills the others, then uses
their resulting cache in the sampled-high planting suffix. -/
theorem runSource_completePrf_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : Point) (slack : C.Term) (target : Digest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hfirst : firstUnmaterialized seeds backend.1.1.data p = some slack) :
    runSource P seeds q s (liftM (completePrf seeds p target)) source backend =
      runSource P seeds q s (liftM ((C.terms.filter (· ≠ slack)).mapM (fillTerm seeds p)))
        source backend >>= fun filled =>
      runSource P seeds q s (do
        let high ← liftM (deferredQuery (C := C) .sample)
        liftM (deferredQuery (C := C) (.plant (.prf (seeds slack) p)
          (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
            (truncateHash high, target ^^^ otherTermSum (cachedTerm seeds filled.2.1.1.data p) slack)))))
        filled.1.2 filled.2 := by
  simp only [completePrf, liftM_bind, runSource_bind, runSource_snapshot, pure_bind, hfirst]

set_option backward.isDefEq.respectTransparency false in
/-- For a fresh target, the complete adaptive source routine has the joint law
of ordinary silent term filling and the aggregate thereby determined. All
backend state, including the pre-existing trace, count and flag, is retained. -/
theorem evalDist_completePrf_fresh (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (p : Point) (slack : C.Term) (source : SourceState C) (backend : CappedCompilerState C)
    (hfirst : firstUnmaterialized seeds backend.1.1.data p = some slack) :
    𝒟[(do
      let target ← $ᵗ Digest
      let r ← runSource P seeds q s (liftM (completePrf seeds p target)) source backend
      pure (target, r.2) : ProbComp (Digest × CappedCompilerState C))] =
    𝒟[(do
      let filled ← runSource P seeds q s
        (liftM ((C.terms.filter (· ≠ slack)).mapM (fillTerm seeds p))) source backend
      let r ← runSource P seeds q s (liftM (fillTerm seeds p slack)) filled.1.2 filled.2
      pure (termSum (cachedTerm seeds r.2.1.1.data p), r.2) : ProbComp (Digest × CappedCompilerState C))] := by
  simp only [runSource_completePrf_slack P seeds q s p slack _ source backend hfirst, bind_assoc]
  rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply evalDist_bind_congr
  intro filled hfilled
  have hcache := fillTerms_cache P seeds q s p (C.terms.filter (· ≠ slack))
    source backend filled hfilled
  have hm : filled.2.1.1.data.cache (.prf (seeds slack) p) = none := by
    rw [hcache.2.2 (.prf (seeds slack) p)]
    · exact firstUnmaterialized_some seeds backend.1.1.data p slack hfirst
    · intro T ht he
      have hne : T ≠ slack := of_decide_eq_true (List.mem_filter.mp ht).2
      exact hne (hinj (Query.prf.inj he).1).symm
  exact evalDist_slackPlant_fresh P seeds hinj q s p slack filled.1.2 filled.2 hm

/-- The fixed capped backend never clears a hit, on any source query. -/
theorem cappedCompiler_flag_sticky (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (st : CappedCompilerState C) (hflag : st.2.2 = true)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run st)) :
    r.2.2.2 = true := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      simp only [hflag, Bool.true_or]
  | inr k =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      exact hflag

/-- A hit survives every subsequent piece of the actual source, including
releases, memoized tree returns, and final verification. -/
theorem runSource_flag_sticky {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hflag : backend.2.2 = true)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s oa source backend)) : r.2.2.2 = true :=
  simulateQ_sticky _ (fun st : CappedCompilerState C => st.2.2 = true)
    (cappedCompiler_flag_sticky P seeds q s) (oa.run source) backend hflag r hr

/-- Source continuations cannot reduce the actual capped counter. This does
not require a syntactic bound on answers outside the oracle's support. -/
theorem runSource_count_mono {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s oa source backend)) :
    backend.1.2 ≤ r.2.1.2 := by
  refine simulateQ_sticky _ (fun st : CappedCompilerState C => backend.1.2 ≤ st.1.2)
    ?_ (oa.run source) backend (le_refl _) r hr
  intro t st hst value hvalue
  rw [cappedCompiler_step_count P seeds q s t st value hvalue]
  exact le_trans hst (Nat.le_add_right _ _)

/-- A counted parsed coordinate raises the fixed capped flag independently of
the underlying answer and of whether that answer was cached. -/
theorem cappedCompiler_candidate_hit (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C) (ht : deferredCounted t)
    (k : HiddenKey) (value : Digest)
    (hcandidate : deferredCandidate P t = some (k, value))
    (st : CappedCompilerState C) (hunreleased : st.2.1 k = none)
    (hvalue : s k = value) (hcap : st.1.2 < q)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) (.inl t) ×
      CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
      (.inl t)).run st)) : r.2.2.2 = true := by
  simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
    support_map] at hr
  obtain ⟨a, _, rfl⟩ := hr
  simp only [cappedCall, ht, hcap, and_self, deferredInputSide, deferredKey,
    deferredPoint, hcandidate, Option.isSome_some, Option.getD_some, hunreleased,
    hvalue, not_true_eq_false, and_self, true_or, decide_true, Bool.or_true]

/-- The one parsed hidden coordinate raises the real capped flag before the
underlying hash answer is inspected. Both cached and fresh hash calls count. -/
theorem cappedCompiler_hash_hit (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (input : HashInput) (k : HiddenKey) (value : Digest)
    (hcandidate : hiddenCandidate P input = some (k, value))
    (st : CappedCompilerState C) (hunreleased : st.2.1 k = none)
    (hvalue : s k = value) (hcap : st.1.2 < q)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) (.inl (.hash (.hash input))) ×
      CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
      (.inl (.hash (.hash input)))).run st)) : r.2.2.2 = true :=
  cappedCompiler_candidate_hit P seeds q s (.hash (.hash input)) trivial k value
    hcandidate st hunreleased hvalue hcap r hr

set_option backward.isDefEq.respectTransparency false in
/-- A concrete source hash has no release prefix: P is considered only on PRF
queries. This equality exposes the same capped kernel used by `compilerRun`. -/
theorem runSource_hashInput (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (input : HashInput)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (sourceHash P seeds (.hash input)) source backend =
      (fun r => ((r.1, source), r.2)) <$>
        ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
          (.inl (.hash (.hash input)))).run backend) := by
  simp only [sourceHash, pure_bind]
  change (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
      (deferredQuery (.hash (.hash input)) >>= fun value => pure (value, source))).run backend = _
  simp only [deferredQuery, HasQuery.instOfMonadLift_query, bind_pure_comp,
    simulateQ_map, StateT.run_map, simulateQ_spec_query]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A supported source hash followed by any continuation pays a hit whenever
the complete run is within the cap. The prefix count bound follows from that
final bound, even for an adaptive adversary. -/
theorem runSource_hashInput_hit {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (input : HashInput) (k : HiddenKey) (value : Digest)
    (hcandidate : hiddenCandidate P input = some (k, value))
    (next : HashOutput → SourceM C α) (source : SourceState C)
    (backend : CappedCompilerState C) (hreveal : RevealRelation s source backend)
    (hunreleased : source.revealed k = none) (hvalue : s k = value)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (sourceHash P seeds (.hash input) >>= next) source backend))
    (hcap : r.2.1.2 ≤ q) : r.2.2.2 = true := by
  rw [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  have hmono := runSource_count_mono P seeds q s (next a.1.1) a.1.2 a.2 r hr
  rw [runSource_hashInput, support_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hstep := cappedCompiler_step_count P seeds q s (.inl (.hash (.hash input))) backend b hb
  have hlt : backend.1.2 < q := by
    simp only [sourceCounted, deferredCounted, if_true] at hstep
    have hstep' : b.2.1.2 = backend.1.2 + 1 := hstep
    have hbound : b.2.1.2 ≤ q := le_trans hmono hcap
    omega
  exact runSource_flag_sticky P seeds q s (next b.1) source b.2
    (cappedCompiler_hash_hit P seeds q s input k value hcandidate backend
      (hreveal.1 ▸ hunreleased) hvalue hlt b hb) r hr

/-- The commitment parser returns the opening coordinate and its actual input
digest, independently of the existential witnesses used by the parser. -/
theorem hiddenCandidate_commitmentInput (P : PublicParameter) (e : KeyIndex) (value : Digest) :
    hiddenCandidate P (commitmentInput P e value) = some (.opening bottomLayer e, value) := by
  have hex : ∃ f v, commitmentInput P e value = commitmentInput P f v := ⟨e, value, rfl⟩
  rw [hiddenCandidate, dif_pos hex]
  have hkey := SigningGuessProof.commitmentInput_key_eq P hex.choose_spec.choose_spec
  have hvalue : value = hex.choose_spec.choose := by
    apply SigningCoreProof.commitmentInput_injective P e
    simpa only [← hkey] using hex.choose_spec.choose_spec
  exact congrArg some (Prod.ext (congrArg (HiddenKey.opening bottomLayer) hkey.symm) hvalue.symm)

/-- Canonical randomizer inputs carry precisely their layer, key and opening. -/
theorem hiddenCandidate_randomizerInput (P : PublicParameter) (lay : Layer)
    (e : KeyIndex) (value : Digest) (message : HashInput) :
    hiddenCandidate P (randomizerInput P lay e value message) =
      some (.opening lay e, value) := by
  have hn : ¬∃ f v, randomizerInput P lay e value message = commitmentInput P f v := by
    rintro ⟨f, v, he⟩
    exact SigningGuessProof.commitmentInput_ne_randomizerInput P f e lay v value message he.symm
  have hex : ∃ lay' f v m, randomizerInput P lay e value message =
      randomizerInput P lay' f v m := ⟨lay, e, value, message, rfl⟩
  rw [hiddenCandidate, dif_neg hn, dif_pos hex]
  have he := hex.choose_spec.choose_spec.choose_spec.choose_spec
  have hlayer := SigningGuessProof.randomizerInput_layer_eq P he
  have hkey := SigningGuessProof.randomizerInput_key_eq P he
  have hvalue := (SigningGuessProof.randomizerInput_payload_eq P he).1
  exact congrArg some (Prod.ext (congrArg₂ HiddenKey.opening hlayer.symm hkey.symm) hvalue.symm)

/-- Every symbolic pending input is parsed as its own secret coordinate. -/
theorem PendingInput.hiddenCandidate (P : PublicParameter) (p : PendingInput) (value : Digest) :
    SigningOpeningProof.hiddenCandidate P (p.input P value) = some (p.key, value) := by
  cases p with
  | commitment e => exact hiddenCandidate_commitmentInput P e value
  | base lay e message => exact hiddenCandidate_randomizerInput P lay e value message
  | bottom e l step => exact SigningGuessLinkProof.hiddenCandidate_chainInput P e l step value
  | top b l step => exact SigningGuessLinkProof.hiddenCandidate_topChainInput P b l step value

/-- Materialized pending points cannot be cache-agreement exceptions. The
statement names the concrete cache condition established by release planting. -/
def ReleasedPending (P : PublicParameter) (s : HiddenKey → Digest)
    (source : SourceState C) (data : DeferredState C) : Prop :=
  ∀ p answer, data.pending p = some answer → source.revealed p.key ≠ none →
    data.cache (.hash (p.input P (s p.key))) = some (answer.interpret s)

/-- If a raw hash addresses a suspended pending point, its parsed input is an
unreleased exact secret. Virtual PRF exceptions cannot occur at a hash input. -/
theorem suspendedHash_candidate (P : PublicParameter) (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (source : SourceState C) (data : DeferredState C)
    (hreleased : ReleasedPending P s source data) (input : HashInput)
    (hinput : SuspendedQuery P seeds s data (.hash input)) :
    ∃ k, hiddenCandidate P input = some (k, s k) ∧ source.revealed k = none := by
  rcases hinput with ⟨hcache, hp | hp⟩
  · obtain ⟨p, answer, hp, he⟩ := hp
    have hi : input = p.input P (s p.key) := Query.hash.inj he
    subst input
    refine ⟨p.key, PendingInput.hiddenCandidate P p (s p.key), ?_⟩
    by_contra hn
    have hc := hreleased p answer hp hn
    rw [hcache] at hc
    cases hc
  · obtain ⟨T, point, _, he⟩ := hp
    cases he

/-- For an in-budget continuation with no hit, the current raw hash is outside
the entire pending set. The premise refers to materialization, not to an
assumed oracle agreement or a selected coupling witness. -/
theorem runSource_hashInput_not_suspended {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (input : HashInput) (next : HashOutput → SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hreveal : RevealRelation s source backend)
    (hreleased : ReleasedPending P s source backend.1.1.data)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (sourceHash P seeds (.hash input) >>= next) source backend))
    (hcap : r.2.1.2 ≤ q) (hflag : r.2.2.2 = false) :
    ¬SuspendedQuery P seeds s backend.1.1.data (.hash input) := by
  intro hsuspended
  obtain ⟨k, hcandidate, hk⟩ := suspendedHash_candidate P seeds s source
    backend.1.1.data hreleased input hsuspended
  have hh := runSource_hashInput_hit P seeds q s input k (s k) hcandidate next source
    backend hreveal hk rfl r hr hcap
  rw [hflag] at hh
  cases hh

/-- The two concrete opening constraints needed at a raw source call: the
actual PRF aggregate interprets the secret, and a revealed opening has all its
compiler terms materialized. Preservation by setup and release is separate. -/
structure OpeningRelation (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (source : SourceState C) (data : DeferredState C) (actual : HashCache C) : Prop where
  actualValue : ∀ e, SigningGuessProof.RandomizerCached seeds actual e →
    SigningGuessProof.cachedRandomizer seeds actual e = s (.opening bottomLayer e)
  released : ∀ e, source.revealed (.opening bottomLayer e) ≠ none →
    SigningGuessProof.RandomizerCached seeds data.cache e

set_option backward.isDefEq.respectTransparency false in
/-- The canonical-base predicate at a concrete hash call depends exactly on
the bound message and the carried opening, on either cache. -/
theorem baseCall_hash_iff (P : PublicParameter) (e : KeyIndex) (value : Digest)
    (st : TsigState C) (input : HashInput) :
    SigningFlatProof.BaseCall P e value st (.inr (.inr (.inl (.hash input)))) ↔
      ∃ message, st.bound e = some message ∧
        input = randomizerInput P bottomLayer e value (bytesLE 32 message) := by
  constructor
  · rintro ⟨other, hother, hcall⟩
    have hi : other = input := by
      rcases hcall with h | h
      · cases h
      · cases h
        rfl
    subst other
    simp only [SigningFlatProof.baseInput, Option.map_eq_some_iff] at hother
    obtain ⟨message, hm, hi⟩ := hother
    exact ⟨message, hm, hi.symm⟩
  · rintro ⟨message, hm, rfl⟩
    refine ⟨_, ?_, Or.inr rfl⟩
    simp only [SigningFlatProof.baseInput, hm, Option.map_some]

/-- With the final capped flag down, a real canonical base cannot precede its
source opening release. A readiness mismatch is therefore paid by that flag,
including the case of an earlier cached real base. -/
theorem runSource_hashInput_ready {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (input : HashInput) (next : HashOutput → SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C) (actual : HashCache C)
    (hreveal : RevealRelation s source backend)
    (hopening : OpeningRelation seeds s source backend.1.1.data actual)
    (e : KeyIndex) (hactual : SigningGuessProof.RandomizerCached seeds actual e)
    (hbase : SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds actual e)
      source.signing (.inr (.inr (.inl (.hash input)))))
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (sourceHash P seeds (.hash input) >>= next) source backend))
    (hcap : r.2.1.2 ≤ q) (hflag : r.2.2.2 = false) :
    SigningGuessProof.RandomizerCached seeds backend.1.1.data.cache e := by
  apply hopening.released e
  intro hn
  obtain ⟨message, _, hi⟩ := (baseCall_hash_iff P e _ source.signing input).mp hbase
  have hcandidate : hiddenCandidate P input =
      some (.opening bottomLayer e, s (.opening bottomLayer e)) := by
    rw [hi, hiddenCandidate_randomizerInput, hopening.actualValue e hactual]
  have hh := runSource_hashInput_hit P seeds q s input (.opening bottomLayer e)
    (s (.opening bottomLayer e)) hcandidate next source backend hreveal hn rfl r hr hcap
  rw [hflag] at hh
  cases hh

/-- On a supported in-budget no-hit continuation the real cached-extra trigger
and the fixed compiler trigger agree for this exact raw hash call. -/
theorem runSource_hashInput_trigger_iff {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (input : HashInput) (next : HashOutput → SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C) (actual : HashCache C)
    (hreveal : RevealRelation s source backend)
    (hcache : CacheRelation P seeds s backend.1.1.data actual)
    (hopening : OpeningRelation seeds s source backend.1.1.data actual)
    (hbound : source.signing.bound = backend.1.1.bound)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (sourceHash P seeds (.hash input) >>= next) source backend))
    (hcap : r.2.1.2 ≤ q) (hflag : r.2.2.2 = false) (e : KeyIndex) :
    (SigningGuessProof.RandomizerCached seeds actual e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds actual e)
        source.signing (.inr (.inr (.inl (.hash input))))) ↔
    (SigningGuessProof.RandomizerCached seeds backend.1.1.data.cache e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds backend.1.1.data.cache e)
        (compilerSigning backend.1.1) (.inr (.inr (.inl (.hash input))))) := by
  have hbound' : source.signing.bound = (compilerSigning backend.1.1).bound := hbound
  constructor
  · rintro ⟨ha, hb⟩
    have hc := runSource_hashInput_ready P seeds q s input next source backend actual
      hreveal hopening e ha hb r hr hcap hflag
    refine ⟨hc, ?_⟩
    rw [baseCall_hash_iff] at hb ⊢
    rwa [hbound', (hcache.randomizer e hc).2] at hb
  · rintro ⟨hc, hb⟩
    obtain ⟨ha, hv⟩ := hcache.randomizer e hc
    refine ⟨ha, ?_⟩
    rw [baseCall_hash_iff] at hb ⊢
    rwa [hbound', hv]

/-- A stateful source exposes its own cache while the private random oracle
keeps a separate cache. This exact equality retains the whole visible state;
it is a reification law, not a coupling hypothesis for the signing theorem. -/
def RawStateLaw {σ α : Type} (cache : σ → HashCache C)
    (source : StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) α)
    (actual : StateT σ ProbComp α) : Prop :=
  ∀ st, (simulateQ SigningGuessProof.privateRoImpl (source.run st)).run (cache st) =
    (fun r => (r, cache r.2)) <$> actual.run st

theorem RawStateLaw.pure {σ α : Type} (cache : σ → HashCache C) (value : α) :
    RawStateLaw cache (pure value) (pure value) := by
  intro st
  simp only [StateT.run_pure, simulateQ_pure, map_pure]

theorem RawStateLaw.bind {σ α β : Type} (cache : σ → HashCache C)
    {source : StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) α}
    {actual : StateT σ ProbComp α} (h : RawStateLaw cache source actual)
    (next : α → StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) β)
    (nextActual : α → StateT σ ProbComp β)
    (hn : ∀ value, RawStateLaw cache (next value) (nextActual value)) :
    RawStateLaw cache (source >>= next) (actual >>= nextActual) := by
  intro st
  simp only [StateT.run_bind, simulateQ_bind]
  rw [h st, bind_map_left, map_bind]
  exact bind_congr fun r => hn r.1 r.2

theorem RawStateLaw.get {σ : Type} (cache : σ → HashCache C) :
    RawStateLaw cache get get := by
  intro st
  simp only [StateT.run_get, simulateQ_pure, StateT.run_pure, map_pure]

/-- Local control updates are shared verbatim; only raw calls can extend the
visible cache in this source reification. -/
theorem RawStateLaw.modify {σ : Type} (cache : σ → HashCache C) (f : σ → σ)
    (hf : ∀ st, cache (f st) = cache st) : RawStateLaw cache (modify f) (modify f) := by
  intro st
  simp only [StateT.run_modify, simulateQ_pure, StateT.run_pure, map_pure, hf]

theorem RawStateLaw.map {σ α β : Type} (cache : σ → HashCache C)
    {source : StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) α}
    {actual : StateT σ ProbComp α} (h : RawStateLaw cache source actual) (f : α → β) :
    RawStateLaw cache (f <$> source) (f <$> actual) := by
  simpa only [bind_pure_comp] using RawStateLaw.bind cache h (fun value => Pure.pure (f value))
    (fun value => Pure.pure (f value)) (fun value => RawStateLaw.pure cache (f value))

/-- The existing raw observation handler reconstructs every visible hash entry
online. A private prefix remains invisible until a source call reads its slot. -/
theorem rawObserve_law {α : Type}
    (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α) :
    RawStateLaw (C := C) id (simulateQ SigningGuessProof.privateRoObserve oa)
      (simulateQ SigningGuessProof.privateRoImpl oa) :=
  SigningGuessProof.privateRoObserve_run oa

/-- Reify an arbitrary raw-oracle program already used by the signing source,
retaining both its returned value and the original visible cache. -/
def rawVisibleLocal (prims : Primitives) (t : (LocalSpec C).Domain) :
    StateT (HashCache C) (OracleComp (SigningGuessProof.SigningRawSpec C))
      ((LocalSpec C).Range t) :=
  simulateQ SigningGuessProof.privateRoObserve (SigningGuessProof.signingRawLocal prims t)

theorem rawVisibleLocal_law (prims : Primitives) (t : (LocalSpec C).Domain) :
    RawStateLaw (C := C) id (rawVisibleLocal prims t) (signingLocalAnswer prims t) := by
  rw [← SigningGuessProof.signingRawLocal_eq]
  exact rawObserve_law _

/-- A local raw-cache program can be carried by any visible state. This is the
same cache replacement performed by the original logged and monitored worlds. -/
theorem RawStateLaw.focus {σ α : Type} (cache : σ → HashCache C)
    (replace : σ → HashCache C → σ) (hcache : ∀ st c, cache (replace st c) = c)
    {source : StateT (HashCache C) (OracleComp (SigningGuessProof.SigningRawSpec C)) α}
    {actual : StateT (HashCache C) ProbComp α} (h : RawStateLaw id source actual) :
    RawStateLaw cache
      (StateT.mk fun st => (fun r => (r.1, replace st r.2)) <$> source.run (cache st))
      (StateT.mk fun st => (fun r => (r.1, replace st r.2)) <$> actual.run (cache st)) := by
  intro st
  have he := h (cache st)
  simp only [id_eq] at he
  simp only [StateT.run_mk, simulateQ_map, StateT.run_map, he,
    Functor.map_map, hcache]

/-- Interpretation commutes with a source simulation whose query cases have
already been reified. -/
theorem RawStateLaw.simulateQ {ι σ α : Type} {spec : OracleSpec ι}
    (cache : σ → HashCache C)
    (source : QueryImpl spec (StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C))))
    (actual : QueryImpl spec (StateT σ ProbComp))
    (h : ∀ t, RawStateLaw cache (source t) (actual t)) (oa : OracleComp spec α) :
    RawStateLaw cache (simulateQ source oa) (simulateQ actual oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RawStateLaw.pure cache value
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      exact RawStateLaw.bind cache (h t) _ _ ih

/-- The actual grind monitor, with its cache maintained by the raw source.
Both monitor updates inspect the old monitor exactly as in keyedSplitOracle. -/
def rawKeyedSplitOracle
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    QueryImpl (Query C →ₒ HashOutput)
      (StateT ((HashCache C × SigningPartnerBoundProof.Monitor) ×
        (XmssSecurity.LeafIndex → Bool))
        (OracleComp (SigningGuessProof.SigningRawSpec C))) :=
  fun query => StateT.mk fun st =>
    (fun r => (r.1, ((r.2, SigningFlatEagerProof.trialStep keyOf st.1.2 query r.1),
      fun e => st.2 e || SigningOneRunProof.cachedTrialAt keyOf st.1.2 query r.1 e))) <$>
      (SigningGuessProof.privateRoObserve (.inr query)).run st.1.1

theorem rawKeyedSplitOracle_law
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (query : Query C) :
    RawStateLaw (fun st => st.1.1) (rawKeyedSplitOracle keyOf query)
      (SigningOneRunProof.keyedSplitOracle keyOf query) := by
  intro st
  simp only [rawKeyedSplitOracle, StateT.run_mk, simulateQ_map, StateT.run_map,
    SigningGuessProof.privateRoObserve_query,
    SigningOneRunProof.keyedSplitOracle, SigningFlatEagerProof.monitoredOracle,
    Functor.map_map]
  rfl

/-- The entire actual silent grind is reified with its full monitor and cache,
including cached trials and the per-key cached-selection bits. -/
theorem rawKeyedSplitOracle_run_law {α : Type}
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (oa : OracleComp (Query C →ₒ HashOutput) α) :
    RawStateLaw (fun st => st.1.1) (simulateQ (rawKeyedSplitOracle keyOf) oa)
      (simulateQ (SigningOneRunProof.keyedSplitOracle keyOf) oa) :=
  RawStateLaw.simulateQ _ _ _ (rawKeyedSplitOracle_law keyOf) oa

/-- The raw lowering agrees with every non-programming world call. The actual
signing stages satisfy this restriction on every response branch. -/
theorem rawWorld_eq (prims : Primitives) (t : (WorldSpec C).Domain)
    (ht : ¬SigningHitLaneProof.IsProgram t) :
    simulateQ SigningGuessProof.privateRoImpl (SigningGuessProof.signingRawWorld prims t) =
      SeedHitProof.signImpl prims t := by
  rcases t with (t | program) | t
  · exact SigningGuessProof.signingRawLocal_eq prims t
  · exact (ht trivial).elim
  · exact SigningGuessProof.signingRawLocal_eq prims t

/-- The original counted call and its call-log entry, over the separate raw
oracle. Only actually visited slots enter the visible cache. -/
def rawCarriedLogged (prims : Primitives) (t : (WorldSpec C).Domain) :
    StateT (SigningFlatProof.FlatJointState C)
      (OracleComp (SigningGuessProof.SigningRawSpec C)) ((WorldSpec C).Range t) :=
  StateT.mk fun st =>
    (fun r => (r.1, (((r.2, st.1.1.2 + SeedHitProof.signCost t),
      st.1.2.logQuery t r.1), st.2))) <$>
      (simulateQ SigningGuessProof.privateRoObserve
        (SigningGuessProof.signingRawWorld prims t)).run st.1.1.1

theorem rawCarriedLogged_law (prims : Primitives) (t : (WorldSpec C).Domain)
    (ht : ¬SigningHitLaneProof.IsProgram t) :
    RawStateLaw (fun st => st.1.1.1) (rawCarriedLogged prims t)
      (SigningFlatProof.carry (SigningCostProof.loggedImpl prims) t) := by
  intro st
  simp only [rawCarriedLogged, StateT.run_mk, simulateQ_map, StateT.run_map,
    SigningGuessProof.privateRoObserve_run, rawWorld_eq prims t ht,
    SigningFlatProof.carry, SigningCostProof.loggedImpl, SigningCacheProof.countImpl,
    SeedHitProof.withCount, Functor.map_map]

abbrev RawSplitState (C : Committee) :=
  (((SigningHitLaneProof.LoggedState C × SigningPartnerBoundProof.Monitor) ×
    (XmssSecurity.LeafIndex → Bool)) × SigningJointEagerProof.OpeningState C)

/-- Reification of the fixed split world. `cachedExtra` still reads the visible
state before and after the counted call; the private cache is inaccessible. -/
def rawKeyedSplitWorld (prims : Primitives) (x : Keys3 C) :
    QueryImpl (WorldSpec C)
      (StateT (RawSplitState C) (OracleComp (SigningGuessProof.SigningRawSpec C))) :=
  fun t => StateT.mk fun st => do
    let z ← (rawCarriedLogged prims t).run (st.1.1.1, st.2)
    (fun y => (z.1, ((((SigningFlatEagerProof.ofRest y.2.1.1
      (SigningFlatEagerProof.restOf z.2)).1, y.2.1.2), y.2.2),
      (SigningFlatEagerProof.ofRest y.2.1.1 (SigningFlatEagerProof.restOf z.2)).2))) <$>
        (simulateQ (rawKeyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
          (SigningOneRunProof.jointCachedExtra x.2.1 x.1 (st.1.1.1, st.2) t z.2)).run
            ((z.2.1.1.1, SigningFlatEagerProof.queryEntryStep
              (XmssSecurity.encodingInputLeafIndex? x.1) st.1.1.2
              (SigningPartnerBoundProof.hashEntry ⟨t, z.1⟩)), st.1.2)

theorem rawKeyedSplitWorld_law (prims : Primitives) (x : Keys3 C)
    (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t) :
    RawStateLaw (fun st => st.1.1.1.1.1) (rawKeyedSplitWorld prims x t)
      (SigningOneRunProof.keyedSplitWorld prims (XmssSecurity.encodingInputLeafIndex? x.1)
        (SigningOneRunProof.jointCachedExtra x.2.1 x.1) t) := by
  intro st
  simp only [rawKeyedSplitWorld, SigningOneRunProof.keyedSplitWorld, StateT.run_mk,
    simulateQ_bind, StateT.run_bind]
  rw [rawCarriedLogged_law prims t ht (st.1.1.1, st.2), bind_map_left, map_bind]
  refine bind_congr fun z => ?_
  simp only [simulateQ_map, StateT.run_map]
  rw [rawKeyedSplitOracle_run_law]
  simp only [Functor.map_map]
  rfl

/-- The exact traced world as a source over a private lazy oracle. It retains
the original monitors, candidates, count, visible cache, trace and stale bit. -/
def rawTraceWorld (prims : Primitives) (x : Keys3 C) :
    QueryImpl (WorldSpec C)
      (StateT (SigningLaneUnionProof.TraceState C)
        (OracleComp (SigningGuessProof.SigningRawSpec C))) :=
  fun t => StateT.mk fun st =>
    (fun z => (z.1, ((z.2.1,
      SigningLaneUnionProof.traceStepAt x.2.1 x.1 st.1.1.1.1.1.1 st.2.1.1 t
        z.2.1.1.1.1.1 st.1.2), z.2.2))) <$>
      (rawKeyedSplitWorld prims x t).run (st.1.1, st.2)

theorem rawTraceWorld_law (prims : Primitives) (x : Keys3 C)
    (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t) :
    RawStateLaw (fun st => st.1.1.1.1.1.1) (rawTraceWorld prims x t)
      (SigningLaneUnionProof.traceWorld prims x t) := by
  intro st
  simp only [rawTraceWorld, SigningLaneUnionProof.traceWorld, StateT.run_mk,
    simulateQ_map, StateT.run_map]
  rw [rawKeyedSplitWorld_law prims x t ht (st.1.1, st.2)]
  simp only [Functor.map_map]

/-- Reify every world call of a complete non-programming source, with all
intermediate cache inspections performed in the original visible state. -/
theorem rawTraceWorld_run_law {α : Type} (prims : Primitives) (x : Keys3 C)
    (oa : OracleComp (WorldSpec C) α) (hfree : SigningHitProof.ProgramFree oa) :
    RawStateLaw (fun st => st.1.1.1.1.1.1) (simulateQ (rawTraceWorld prims x) oa)
      (simulateQ (SigningLaneUnionProof.traceWorld prims x) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RawStateLaw.pure _ value
  | query_bind t next ih =>
      obtain ⟨ht, hn⟩ := (SigningHitProof.programFree_queryBind_iff t next).mp hfree
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      exact RawStateLaw.bind _ (rawTraceWorld_law prims x t ht) _ _ (fun value => ih value (hn value))

/-- Flatten the original opening/candidate handler over the reified traced
world. The carried signing state has precisely the original call timing. -/
def rawTraceFlatWith {ι : Type} {spec : OracleSpec ι} (prims : Primitives) (x : Keys3 C)
    (outer : QueryImpl spec (StateT (SigningJointEagerProof.OpeningState C)
      (OracleComp (WorldSpec C)))) :
    QueryImpl spec (StateT (SigningLaneUnionProof.TraceState C)
      (OracleComp (SigningGuessProof.SigningRawSpec C))) :=
  fun t => StateT.mk fun st =>
    (fun z => (z.1.1, (z.2.1, z.1.2))) <$>
      (simulateQ (rawTraceWorld prims x) ((outer t).run st.2)).run st

theorem rawTraceFlatWith_law {ι : Type} {spec : OracleSpec ι}
    (prims : Primitives) (x : Keys3 C)
    (outer : QueryImpl spec (StateT (SigningJointEagerProof.OpeningState C)
      (OracleComp (WorldSpec C)))) (t : ι)
    (hfree : ∀ st, SigningHitProof.ProgramFree ((outer t).run st)) :
    RawStateLaw (fun st => st.1.1.1.1.1.1) (rawTraceFlatWith prims x outer t)
      (SigningFlatEagerProof.flatWith outer (SigningLaneUnionProof.traceWorld prims x) t) := by
  intro st
  simp only [rawTraceFlatWith, SigningFlatEagerProof.flatWith, StateT.run_mk,
    simulateQ_map, StateT.run_map]
  rw [rawTraceWorld_run_law prims x ((outer t).run st.2) (hfree st.2) st]
  simp only [Functor.map_map]

/-- The full actual signing game, reified over the private lazy oracle. Every
visible cache inspection remains inside this source and sees only prior calls. -/
def rawTraceGame (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    StateT (SigningLaneUnionProof.TraceState C)
      (OracleComp (SigningGuessProof.SigningRawSpec C)) (SigningJointEagerProof.JointResult C) :=
  SigningJointEagerProof.jointGameWith A x (rawTraceWorld prims x)
    (fun dealt => rawTraceFlatWith prims x (SigningOpeningProof.openingOracles x dealt))
    (StateT.mk fun st => pure (st.2, st))

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- Exact reification of the original trace game, including setup, adaptive
corruption/signing, candidate logging and final verification. No state field is
discarded and the original count is retained. -/
theorem rawTraceGame_law (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    RawStateLaw (fun st => st.1.1.1.1.1.1) (rawTraceGame prims A x)
      (SigningLaneUnionProof.traceGame prims A x) := by
  unfold rawTraceGame SigningLaneUnionProof.traceGame SigningJointEagerProof.jointGameWith
  dsimp only
  have hsetup : SigningHitProof.ProgramFree
      (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  refine RawStateLaw.bind _ (rawTraceWorld_run_law prims x _ hsetup) _ _ fun result => ?_
  rcases result with _ | (top | tree)
  · exact RawStateLaw.pure _ _
  · refine RawStateLaw.bind _ (RawStateLaw.simulateQ _ _ _
      (fun t => rawTraceFlatWith_law prims x _ t
        (SigningJointEagerProof.programFree_openingOracles x top t)) _) _ _ fun forgery => ?_
    have hget : RawStateLaw (fun st : SigningLaneUnionProof.TraceState C => st.1.1.1.1.1.1)
        (StateT.mk fun st => pure (st.2, st)) SigningFlatEagerProof.getCarried := by
      intro st
      rfl
    refine RawStateLaw.bind _ hget _ _ fun state => ?_
    refine RawStateLaw.bind _ (rawTraceWorld_run_law prims x _
      (SigningJointEagerProof.programFree_tsigFinishLogged x top state.2.1 _)) _ _ fun result => ?_
    exact RawStateLaw.pure _ _
  · exact RawStateLaw.pure _ _

/-- The complete source state is part of the raw computation's result. The
private oracle's own cache is the only component forgotten here. -/
def rawTraceProgram (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    OracleComp (SigningGuessProof.SigningRawSpec C) (SigningLaneUnionProof.TraceOutcome C) :=
  (rawTraceGame prims A x).run
    (((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)),
      SigningOneRunProof.monitoredInit.2)

/-- The raw source has exactly the complete original traced outcome law. -/
theorem traceRun_eq_raw (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl (rawTraceProgram prims A x)).run ∅ =
      SigningLaneUnionProof.traceRun prims A x := by
  have h := congrArg (fun m => Prod.fst <$> m) (rawTraceGame_law prims A x
    (((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)),
      SigningOneRunProof.monitoredInit.2))
  simp only [Functor.map_map] at h
  exact h.trans (id_map _)

/-- Private read-only presampling preserves the original guarded trace event
with its full visible cache. Silent presampled entries are never exposed to
cachedExtra or traceStepAt before an actual source read. -/
theorem traceRun_eq_private_prefix {α : Type} (prims : Primitives)
    (A : TsigAdversary C) (x : Keys3 C) (ghost : OracleComp (Query C →ₒ HashOutput) α) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[Prod.fst <$> (do
        let _ ← simulateQ (Query C →ₒ HashOutput).randomOracle ghost
        simulateQ SigningGuessProof.privateRoImpl (rawTraceProgram prims A x)).run ∅] := by
  have h := SigningGuessProof.randomOracle_private_prefix_private ghost
    (rawTraceProgram prims A x) (∅ : HashCache C)
  rw [traceRun_eq_raw] at h
  exact h.symm

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Every supported privately presampled trace obeys the original budget.
This transports the original real-world bound without a replacement source
budget premise, and includes runs whose hidden-key flag is already raised. -/
theorem rawTraceProgram_prefix_count_le {α : Type} (prims : Primitives)
    (A : TsigAdversary C) (x : Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q)
    (ghost : OracleComp (Query C →ₒ HashOutput) α)
    (pre : α × HashCache C)
    (hpre : pre ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle ghost).run ∅))
    (r : SigningLaneUnionProof.TraceOutcome C × HashCache C)
    (hr : r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (rawTraceProgram prims A x)).run pre.2)) :
    (SigningLaneUnionProof.observed r.1).2.1 ≤ q := by
  apply SigningLaneUnionProof.traceRun_count_le prims A q x hq r.1
  rw [← mem_support_evalDist_iff, traceRun_eq_private_prefix prims A x ghost,
    mem_support_evalDist_iff, support_map]
  refine ⟨r, ?_, rfl⟩
  rw [StateT.run_bind, mem_support_bind_iff]
  refine ⟨pre, hpre, ?_⟩
  with_reducible exact hr

/-- Embed raw uniform/hash accesses in the existing local alphabet, so the
established finite share-slot presampling theorem can interpret this source. -/
def rawToLocal : QueryImpl (SigningGuessProof.SigningRawSpec C) (OracleComp (LocalSpec C))
  | .inl n => query (spec := LocalSpec C) (.inl n)
  | .inr q => query (spec := LocalSpec C) (.inr (.inl q))

def rawAsWorld {α : Type} (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α) :
    OracleComp (WorldSpec C) α :=
  worldRoles.adversary (simulateQ rawToLocal oa)

set_option backward.isDefEq.respectTransparency false in
/-- This embedding changes no answer or private-cache access. Its extra outer
counter is ignored; the original signing counter is inside the source result. -/
theorem rawAsWorld_simulate {α : Type} (prims : Primitives)
    (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α) :
    simulateQ (SeedHitProof.signImpl prims) (rawAsWorld oa) =
      simulateQ SigningGuessProof.privateRoImpl oa := by
  rw [rawAsWorld, SeedHitProof.simulateQ_adversary_split]
  induction oa using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, ih]
      cases t <;> simp only [rawToLocal, HasQuery.instOfMonadLift_query,
        simulateQ_spec_query]
      all_goals rfl

/-- Forget only the auxiliary routing counter. -/
theorem withCount_forget {σ α : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (oa : OracleComp (WorldSpec C) α) (st : σ) (n : ℕ) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (SeedHitProof.withCount impl) oa).run (st, n) =
      (simulateQ impl oa).run st := by
  apply Eq.symm
  apply TprfSecurityProof.StateMap.simulateQ
    (φ := Prod.fst) (oa := oa) (s := (st, n))
  intro t state
  simp only [SeedHitProof.withCount, StateT.run_mk, Functor.map_map]
  exact (id_map _).symm

/-- Split routing affects neither the raw source result nor its visible cache,
which is retained inside that result and is separate from the routing caches. -/
theorem splitRaw_result {α : Type} (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2))
    (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α) :
    Prod.fst <$> (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
      (rawAsWorld oa)).run ((∅, ∅), 0) =
      Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl oa).run ∅ := by
  have hsplit := TprfSecurityProof.StateMap.simulateQ
    (SeedHitProof.stateMap_withCount _ _ _
      (SeedHitProof.stateMap_routedImpl prims x.2.1 x.2.2 hinj)) (rawAsWorld oa)
        ((∅ : HashCache C), 0)
  simp only [Prod.map, id_eq, TprfSecurityProof.splitCache_empty] at hsplit
  rw [hsplit, Functor.map_map]
  have hforget := congrArg (fun program => Prod.fst <$> program)
    (withCount_forget (SeedHitProof.signImpl prims) (rawAsWorld oa) ∅ 0)
  simp only [Functor.map_map, rawAsWorld_simulate] at hforget
  exact hforget

/-- The full original trace source with the private share table sampled first.
The table is used only by the routed oracle, never as the visible trace cache. -/
def presampledTrace (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (table : TprfSecurityProof.Slot C → HashOutput) :
    ProbComp (SigningLaneUnionProof.TraceOutcome C) :=
  Prod.fst <$> (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
    (rawAsWorld (rawTraceProgram prims A x))).run ((∅, TprfSecurityProof.fullTable table), 0)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- Full-table presampling for the exact original guarded trace experiment.
Unlike a final-cache-only projection, the reified source reconstructs the
visible cache before every cached-randomizer trigger and trace decision. -/
theorem traceRun_eq_presampled_slots (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[($ᵗ (TprfSecurityProof.Slot C → HashOutput)) >>= presampledTrace prims A x] := by
  have hinj : Function.Injective (TprfSecurityProof.slotInput x.2.1 x.2.2) := by
    simp only [TprfSecurityProof.KeyCollision, not_or, not_not] at hkeys
    exact TprfSecurityProof.slotInput_injective hkeys.1 hkeys.2
  have h := SigningGuessProof.presample_signing_slots_observe prims x.2.1 x.2.2
    (rawAsWorld (rawTraceProgram prims A x)) (fun result _ _ => result)
    (fun slot => SigningGuessProof.presampled_signing_adversary prims x.2.1 x.2.2 slot _)
    (Finset.univ : Finset (TprfSecurityProof.Slot C)).toList (Finset.nodup_toList _)
    ((∅, ∅), 0) (fun _ _ => rfl)
  have hfill : ∀ table : TprfSecurityProof.Slot C → HashOutput,
      SigningGuessProof.setSigningSlots ((∅, ∅), 0)
        (TprfSecurityProof.fillSlots table (Finset.univ : Finset (TprfSecurityProof.Slot C)).toList
          (SigningGuessProof.signingSlots ((∅, ∅), 0))) =
      ((∅, TprfSecurityProof.fullTable table), 0) := by
    intro table
    dsimp only [SigningGuessProof.setSigningSlots, SigningGuessProof.signingSlots]
    congr 2
    funext slot
    exact TprfSecurityProof.fillSlots_of_mem table _ _ (Finset.mem_toList.mpr (Finset.mem_univ slot))
  simp only [hfill] at h
  change 𝒟[($ᵗ (TprfSecurityProof.Slot C → HashOutput)) >>= presampledTrace prims A x] =
    𝒟[Prod.fst <$> (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
      (rawAsWorld (rawTraceProgram prims A x))).run ((∅, ∅), 0)] at h
  rw [splitRaw_result prims x hinj, traceRun_eq_raw] at h
  exact h.symm

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- The original support-wise cap holds for each complete presampled share
table, with the original trace count still inside the retained outcome. -/
theorem presampledTrace_count_le (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q)
    (table : TprfSecurityProof.Slot C → HashOutput) (r : SigningLaneUnionProof.TraceOutcome C)
    (hr : r ∈ support (presampledTrace prims A x table)) :
    (SigningLaneUnionProof.observed r).2.1 ≤ q := by
  apply SigningLaneUnionProof.traceRun_count_le prims A q x hq r
  rw [← mem_support_evalDist_iff, traceRun_eq_presampled_slots prims A x hkeys,
    mem_support_evalDist_iff, mem_support_bind_iff]
  refine ⟨table, by simp, ?_⟩
  with_reducible exact hr

/-- All aggregate PRF values of the private share table. -/
def tablePrf (table : TprfSecurityProof.Slot C → HashOutput) (point : Point) : Digest :=
  TprfSecurityProof.prfSum table point

/-- A joint change of variables for the private table. Only one PRF term per
point is shifted; no masks or visible cache entries are supplied to the source.
This mathematical reparametrization is not an alternative compiler backend. -/
def refreshAllPrf (slack : C.Term) (table : TprfSecurityProof.Slot C → HashOutput)
    (target : Point → Digest) : TprfSecurityProof.Slot C → HashOutput :=
  TprfSecurityProof.shiftTable [] ∅ Finset.univ slack
    (fun point => TprfSecurityProof.prfSum table point + TprfCorrectnessProof.toXor (target point)) table

theorem refreshAllPrf_value (slack : C.Term) (table : TprfSecurityProof.Slot C → HashOutput)
    (target : Point → Digest) : tablePrf (refreshAllPrf slack table target) = target := by
  funext point
  change TprfSecurityProof.prfSum (refreshAllPrf slack table target) point =
    TprfCorrectnessProof.toXor (target point)
  rw [refreshAllPrf, TprfSecurityProof.prfSum_shiftTable _ _ (Finset.mem_univ point),
    ← add_assoc, TprfSecurityProof.XorDigest.add_self, zero_add]

theorem refreshAllPrf_twice (slack : C.Term) (table : TprfSecurityProof.Slot C → HashOutput)
    (target : Point → Digest) :
    refreshAllPrf slack (refreshAllPrf slack table target) (tablePrf table) = table := by
  have hs : ∀ point, TprfSecurityProof.prfSum (refreshAllPrf slack table target) point =
      TprfCorrectnessProof.toXor (target point) := congrFun (refreshAllPrf_value slack table target)
  rw [refreshAllPrf]
  simp only [hs]
  have hdelta : (fun point => TprfCorrectnessProof.toXor (target point) +
      TprfCorrectnessProof.toXor (tablePrf table point)) =
      (fun point => TprfSecurityProof.prfSum table point + TprfCorrectnessProof.toXor (target point)) :=
    funext fun point => add_comm _ _
  rw [hdelta, refreshAllPrf, TprfSecurityProof.shiftTable_shiftTable]

/-- Retaining the old aggregates makes simultaneous installation bijective. -/
def refreshPrfPair (slack : C.Term)
    (pair : (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)) :
    (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest) :=
  (refreshAllPrf slack pair.1 pair.2, tablePrf pair.1)

theorem refreshPrfPair_involutive (slack : C.Term) : Function.Involutive (refreshPrfPair slack) := by
  rintro ⟨table, target⟩
  exact Prod.ext (refreshAllPrf_twice slack table target) (refreshAllPrf_value slack table target)

/-- Joint uniform law of the entire private table and all its aggregate
targets. The table is retained, so adaptive future queries may inspect it. -/
theorem refreshAllPrf_joint (slack : C.Term) :
    𝒟[(fun pair => (refreshAllPrf slack pair.1 pair.2, pair.2)) <$>
      ($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)))] =
    𝒟[(fun table => (table, tablePrf table)) <$>
      ($ᵗ (TprfSecurityProof.Slot C → HashOutput))] := by
  let observe : ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)) →
      (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest) :=
    fun pair => (pair.1, tablePrf pair.1)
  have he : (fun pair => (refreshAllPrf slack pair.1 pair.2, pair.2)) =
      observe ∘ refreshPrfPair slack := by
    funext pair
    simp only [Function.comp_apply, observe, refreshPrfPair, refreshAllPrf_value]
  have hu := evalDist_map_bijective_uniform_cross
    (α := (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))
    (refreshPrfPair slack) (refreshPrfPair_involutive slack).bijective
  have hm : (fun pair => (refreshAllPrf slack pair.1 pair.2, pair.2)) <$>
      ($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))) =
      observe <$> (refreshPrfPair slack <$>
        ($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)))) := by
    rw [Functor.map_map, he]
    rfl
  rw [hm, evalDist_map, hu, ← evalDist_map]
  have hp : observe <$>
      ($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))) =
      (fun table => (table, tablePrf table)) <$>
        (Prod.fst <$> ($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)))) := by
    rw [Functor.map_map]
  rw [hp, evalDist_map, evalDist_map_fst_uniformSample_prod, ← evalDist_map]

/-- Apply the joint table change to the full adaptive traced experiment,
retaining both its original outcome and the private table/aggregate pair. -/
theorem presampledTrace_joint_prf (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (slack : C.Term) :
    𝒟[do
      let table ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
      let result ← presampledTrace prims A x table
      pure (result, table, tablePrf table)] =
    𝒟[do
      let pair ← $ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))
      let table := refreshAllPrf slack pair.1 pair.2
      let result ← presampledTrace prims A x table
      pure (result, table, pair.2)] := by
  let next : ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)) →
      ProbComp (SigningLaneUnionProof.TraceOutcome C ×
        (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest)) :=
    fun pair => (fun result => (result, pair)) <$> presampledTrace prims A x pair.1
  have h := congrArg (fun d => d >>= fun pair => 𝒟[next pair]) (refreshAllPrf_joint slack)
  simpa only [← evalDist_bind, bind_map_left, next, bind_pure_comp] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual adaptive-slack completion is the exact fixed-target fiber of
ordinary lazy filling. This identity needs no conditional-freshness assertion
about a previously sampled secret and retains arbitrary backend observations. -/
theorem probEvent_completePrf_fiber (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (point : Point) (slack : C.Term) (target : Digest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hfirst : firstUnmaterialized seeds backend.1.1.data point = some slack)
    (event : CappedCompilerState C → Prop) :
    (Fintype.card Digest : ℝ≥0∞)⁻¹ *
      Pr[fun r => event r.2 |
        runSource P seeds q s (liftM (completePrf seeds point target)) source backend] =
      Pr[fun r => termSum (cachedTerm seeds r.2.1.1.data point) = target ∧ event r.2 | do
        let filled ← runSource P seeds q s
          (liftM ((C.terms.filter (· ≠ slack)).mapM (fillTerm seeds point))) source backend
        runSource P seeds q s (liftM (fillTerm seeds point slack)) filled.1.2 filled.2] := by
  let observe : Digest × CappedCompilerState C → Prop :=
    fun pair => pair.1 = target ∧ event pair.2
  have h := probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_completePrf_fresh P seeds hinj q s point slack source backend hfirst)
    (p := observe)
  have hleft : ∀ value : Digest,
      Pr[fun r => value = target ∧ event r.2 |
        runSource P seeds q s (liftM (completePrf seeds point value)) source backend] =
      if value = target then
        Pr[fun r => event r.2 |
          runSource P seeds q s (liftM (completePrf seeds point target)) source backend]
      else 0 := by
    intro value
    by_cases hv : value = target
    · subst value
      simp only [true_and, if_true]
    · simp only [hv, false_and, if_false]
      simpa only [Bool.false_eq_true] using probEvent_false
        (runSource P seeds q s (liftM (completePrf seeds point value)) source backend)
  simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    observe] at h
  simp only [hleft, mul_ite, mul_zero, tsum_ite_eq, probOutput_uniformSample] at h
  simpa only [probEvent_bind_eq_tsum] using h

/-- The original complete trace experiment may sample all aggregate PRF
targets eagerly. The private share table remains correlated with those
targets, and the visible source still observes only actually read entries. -/
theorem traceRun_eq_eager_prf (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))) >>= fun pair =>
        presampledTrace prims A x (refreshAllPrf slack pair.1 pair.2)] := by
  have h := congrArg (fun distribution => Prod.fst <$> distribution)
    (presampledTrace_joint_prf prims A x slack)
  simp only [← evalDist_map, map_bind, map_pure, bind_pure] at h
  rw [traceRun_eq_presampled_slots prims A x hkeys]
  exact h

/-- Resolve the private share slots without exposing them to the source's
visible cache. Every other query still uses the ordinary private oracle. -/
def resolveSlots (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (table : TprfSecurityProof.Slot C → HashOutput) :
    QueryImpl (SigningGuessProof.SigningRawSpec C)
      (OracleComp (SigningGuessProof.SigningRawSpec C))
  | .inl n => query (spec := SigningGuessProof.SigningRawSpec C) (.inl n)
  | .inr input =>
      if h : ∃ slot, TprfSecurityProof.slotInput seeds pairKeys slot = input then
        pure (table h.choose)
      else query (spec := SigningGuessProof.SigningRawSpec C) (.inr input)

def routedRaw (prims : Primitives) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) :
    QueryImpl (SigningGuessProof.SigningRawSpec C)
      (StateT (HashCache C × TprfSecurityProof.SlotCache C) ProbComp)
  | .inl n => SeedHitProof.routedLocal prims seeds pairKeys (.inl n)
  | .inr input => SeedHitProof.routedLocal prims seeds pairKeys (.inr (.inl input))

set_option backward.isDefEq.respectTransparency false in
theorem resolveSlots_stateMap (prims : Primitives) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (table : TprfSecurityProof.Slot C → HashOutput)
    (t : (SigningGuessProof.SigningRawSpec C).Domain) :
    TprfSecurityProof.StateMap (fun cache => (cache, TprfSecurityProof.fullTable table))
      (simulateQ SigningGuessProof.privateRoImpl (resolveSlots seeds pairKeys table t))
      (routedRaw prims seeds pairKeys t) := by
  intro cache
  cases t with
  | inl n =>
      simp only [resolveSlots, routedRaw, SeedHitProof.routedLocal,
        TprfSecurityProof.onCache_run]
      rfl
  | inr input =>
      by_cases h : ∃ slot, TprfSecurityProof.slotInput seeds pairKeys slot = input
      · simp only [resolveSlots, dif_pos h, simulateQ_pure, routedRaw,
          SeedHitProof.routedLocal, TprfSecurityProof.onTable_run,
          StateT.run_pure, map_pure]
        rfl
      · simp only [resolveSlots, dif_neg h, HasQuery.instOfMonadLift_query,
          simulateQ_spec_query, routedRaw,
          SeedHitProof.routedLocal, TprfSecurityProof.onCache_run]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem rawAsWorld_routed {α : Type} (prims : Primitives)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α) :
    simulateQ (SeedHitProof.routedImpl prims seeds pairKeys) (rawAsWorld oa) =
      simulateQ (routedRaw prims seeds pairKeys) oa := by
  rw [rawAsWorld, SeedHitProof.simulateQ_adversary_split]
  induction oa using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, ih]
      cases t <;> simp only [rawToLocal, HasQuery.instOfMonadLift_query,
        simulateQ_spec_query]
      all_goals rfl

/-- Fixed private share slots can be resolved syntactically. The source's
entire result, including its online visible cache, is retained. -/
theorem presampledTrace_eq_resolved (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (table : TprfSecurityProof.Slot C → HashOutput) :
    presampledTrace prims A x table =
      Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (simulateQ (resolveSlots x.2.1 x.2.2 table) (rawTraceProgram prims A x))).run ∅ := by
  have hcount := congrArg (fun program => Prod.fst <$> program)
    (withCount_forget (SeedHitProof.routedImpl prims x.2.1 x.2.2)
      (rawAsWorld (rawTraceProgram prims A x)) (∅, TprfSecurityProof.fullTable table) 0)
  simp only [Functor.map_map, rawAsWorld_routed] at hcount
  unfold presampledTrace
  change _ = _ at hcount
  rw [hcount]
  have hmap := TprfSecurityProof.StateMap.simulateQ
    (resolveSlots_stateMap prims x.2.1 x.2.2 table) (rawTraceProgram prims A x) ∅
  change (simulateQ (routedRaw prims x.2.1 x.2.2) _).run
      (∅, TprfSecurityProof.fullTable table) =
    Prod.map id (fun cache => (cache, TprfSecurityProof.fullTable table)) <$>
      (simulateQ (SigningGuessProof.privateRoImpl ∘ₛ resolveSlots x.2.1 x.2.2 table)
        (rawTraceProgram prims A x)).run ∅ at hmap
  rw [QueryImpl.simulateQ_compose] at hmap
  rw [hmap, Functor.map_map]
  rfl

/-- The exact traced source can be preceded by arbitrary private hash
precomputation after the share table is fixed. Its visible cache and original
counter remain inside the source result. -/
theorem presampledTrace_eq_private_prefix {α : Type} (prims : Primitives)
    (A : TsigAdversary C) (x : Keys3 C)
    (table : TprfSecurityProof.Slot C → HashOutput)
    (ghost : OracleComp (Query C →ₒ HashOutput) α) :
    𝒟[presampledTrace prims A x table] =
      𝒟[Prod.fst <$> (do
        let _ ← simulateQ (Query C →ₒ HashOutput).randomOracle ghost
        simulateQ SigningGuessProof.privateRoImpl
          (simulateQ (resolveSlots x.2.1 x.2.2 table) (rawTraceProgram prims A x))).run ∅] := by
  rw [presampledTrace_eq_resolved]
  exact (SigningGuessProof.randomOracle_private_prefix_private ghost _ ∅).symm

/-- All reference trees can be evaluated privately, with their exact
success/failure results and shared hash cache. This is an oracle program, so
the prefix theorem also covers the data-dependent top-signature search. -/
def privateReferenceForest (P : PublicParameter) (F : Point → Digest) :
    OracleComp (Query C →ₒ HashOutput) (Option (TopTree × List (Option TreeOutput))) := do
  let hash : ∀ {α : Type}, OracleComp HashSpec α → OracleComp (Query C →ₒ HashOutput) α :=
    fun oa => simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa
  let some (.top top) ← referenceTree hash (fun p => pure (F p)) P emptyTop .top
    | pure none
  let trees ← (List.finRange (2 ^ layerHeight)).mapM fun b =>
    referenceTree hash (fun p => pure (F p)) P top (.bottom b)
  pure (some (top, trees))

/-- The original full trace law with both aggregate PRFs and the complete
honest reference forest presampled privately. The original online cache is
still reconstructed by `rawTraceProgram` before each trace inspection. -/
theorem traceRun_eq_eager_forest (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let pair ← $ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))
        Prod.fst <$> (do
          let _ ← simulateQ (Query C →ₒ HashOutput).randomOracle
            (privateReferenceForest x.1 pair.2)
          simulateQ SigningGuessProof.privateRoImpl
            (simulateQ (resolveSlots x.2.1 x.2.2 (refreshAllPrf slack pair.1 pair.2))
              (rawTraceProgram prims A x))).run ∅] := by
  rw [traceRun_eq_eager_prf prims A x hkeys slack]
  apply evalDist_bind_congr
  intro pair _
  exact presampledTrace_eq_private_prefix prims A x _ _

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- After fixing the share table and any supported private prefix, every
supported source execution retains the original real-world query cap. -/
theorem resolvedTrace_prefix_count_le {α : Type} (prims : Primitives)
    (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q)
    (table : TprfSecurityProof.Slot C → HashOutput)
    (ghost : OracleComp (Query C →ₒ HashOutput) α)
    (pre : α × HashCache C)
    (hpre : pre ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle ghost).run ∅))
    (r : SigningLaneUnionProof.TraceOutcome C × HashCache C)
    (hr : r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (simulateQ (resolveSlots x.2.1 x.2.2 table) (rawTraceProgram prims A x))).run pre.2)) :
    (SigningLaneUnionProof.observed r.1).2.1 ≤ q := by
  apply presampledTrace_count_le prims A x hkeys q hq table r.1
  rw [← mem_support_evalDist_iff, presampledTrace_eq_private_prefix prims A x table ghost,
    mem_support_evalDist_iff, support_map]
  refine ⟨r, ?_, rfl⟩
  rw [StateT.run_bind, mem_support_bind_iff]
  refine ⟨pre, hpre, ?_⟩
  with_reducible exact hr

/-- Embed a private hash-only cache in the structured query domain. No PRF or
mask entry is introduced by this embedding. -/
def embedHashCache (cache : QueryCache HashSpec) : HashCache C
  | .hash input => cache input
  | _ => none

theorem embedHashCache_empty : embedHashCache (C := C) ∅ = ∅ := by
  funext q
  cases q <;> rfl

theorem embedHashCache_cacheQuery (cache : QueryCache HashSpec)
    (input : HashInput) (value : HashOutput) :
    embedHashCache (C := C) (cache.cacheQuery input value) =
      (embedHashCache cache).cacheQuery (.hash input) value := by
  funext q
  cases q <;> simp [embedHashCache, QueryCache.cacheQuery]
  rename_i other
  by_cases h : other = input
  · subst other
    simp
  · simp [Function.update_of_ne, h, embedHashCache]

set_option backward.isDefEq.respectTransparency false in
theorem embedHashCache_stateMap (input : HashInput) :
    TprfSecurityProof.StateMap (embedHashCache (C := C))
      (HashSpec.randomOracle input) ((Query C →ₒ HashOutput).randomOracle (.hash input)) := by
  intro cache
  cases hc : cache input with
  | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc,
        QueryImpl.withCaching_run_none _ (show embedHashCache cache (.hash input) = none from hc)]
      simp only [Functor.map_map, Prod.map_apply, id_eq, embedHashCache_cacheQuery]
      rfl
  | some value =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc,
        QueryImpl.withCaching_run_some _ (show embedHashCache cache (.hash input) = some value from hc)]
      rfl

def hashAsQuery {α : Type} (oa : OracleComp HashSpec α) : OracleComp (Query C →ₒ HashOutput) α :=
  simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa

set_option backward.isDefEq.respectTransparency false in
theorem hashAsQuery_run {α : Type} (oa : OracleComp HashSpec α) (cache : QueryCache HashSpec) :
    (simulateQ (Query C →ₒ HashOutput).randomOracle (hashAsQuery oa)).run (embedHashCache cache) =
      Prod.map id embedHashCache <$> (simulateQ HashSpec.randomOracle oa).run cache := by
  have h := TprfSecurityProof.StateMap.simulateQ (embedHashCache_stateMap (C := C)) oa cache
  have hf : ((Query C →ₒ HashOutput).randomOracle ∘ₛ
      fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) =
      (fun input => (Query C →ₒ HashOutput).randomOracle (.hash input)) := by
    funext input
    simp only [QueryImpl.apply_compose, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  rw [hashAsQuery, ← QueryImpl.simulateQ_compose, hf]
  exact h

/-- The oracle form of the pinned all-chain trajectory precomputation. -/
def privateChainColumn (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (keys : List XmssSecurity.ChainKey) :
    OracleComp HashSpec (List XmssSecurity.FullChainTrajectory) :=
  keys.mapM fun key => XmssSecurity.Concrete.chainTrajectory P key chain 0
    (chainLength - 1) (start key chain)

theorem privateChainColumn_run (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (keys : List XmssSecurity.ChainKey) (cache : QueryCache HashSpec) :
    (simulateQ HashSpec.randomOracle (privateChainColumn P start chain keys)).run cache =
      XmssSecurity.Concrete.fixedSeedChainTrajectoriesFromCache P start chain
        (chainLength - 1) cache keys := by
  induction keys generalizing cache with
  | nil => simp only [privateChainColumn, List.mapM_nil, simulateQ_pure, StateT.run_pure]; rfl
  | cons key keys ih =>
      simp only [privateChainColumn, List.mapM_cons, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure,
        XmssSecurity.Concrete.fixedSeedChainTrajectoriesFromCache_cons]
      apply bind_congr
      intro first
      rw [← ih first.2]
      rfl

def privateChains (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) :
    List ChainIndex → OracleComp HashSpec XmssSecurity.CappedChain.AllChainTrajectories
  | [] => pure (fun _ => [])
  | chain :: chains => do
      let first ← privateChainColumn P start chain XmssSecurity.allChainKeys
      let rest ← privateChains P start chains
      pure (Function.update rest chain first)

theorem privateChains_run (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest)
    (chains : List ChainIndex) (cache : QueryCache HashSpec) :
    (simulateQ HashSpec.randomOracle (privateChains P start chains)).run cache =
      XmssSecurity.CappedChain.Concrete.allChainTrajectoriesFromCache P start cache chains := by
  induction chains generalizing cache with
  | nil => simp only [privateChains, simulateQ_pure, StateT.run_pure]; rfl
  | cons chain chains ih =>
      simp only [privateChains, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, privateChainColumn_run]
      apply bind_congr
      intro first
      rw [ih]
      rfl

/-- Resolve the PRF coordinate that starts each bottom or top chain. -/
def prfChainStarts (F : Point → Digest) : XmssSecurity.ChainKey → ChainIndex → Digest
  | .inl e, l => F (.chain bottomLayer e l (digit 0))
  | .inr b, l => F (.chain topLayer (topKey b) l (digit 0))

set_option backward.isDefEq.respectTransparency false in
/-- All canonical chains may be programmed privately using the pinned leanVM
trajectory law. Their complete cache is retained by the adaptive source. -/
theorem presampledTrace_eq_programmed_chains (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (table : TprfSecurityProof.Slot C → HashOutput)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) :
    𝒟[presampledTrace prims A x table] =
      𝒟[do
        let pre ← XmssSecurity.CappedChain.programmedAllChainTrajectoriesFromCache
          x.1 start ∅ XmssSecurity.CappedChain.allChains
        Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
          (simulateQ (resolveSlots x.2.1 x.2.2 table) (rawTraceProgram prims A x))).run
            (embedHashCache pre.2)] := by
  rw [presampledTrace_eq_private_prefix prims A x table
    (hashAsQuery (C := C) (privateChains x.1 start XmssSecurity.CappedChain.allChains))]
  rw [← embedHashCache_empty (C := C)]
  simp only [StateT.run_bind, hashAsQuery_run, privateChains_run, bind_map_left,
    map_bind, Prod.map_snd]
  have hchains := XmssSecurity.CappedChain.evalDist_allChainTrajectories_eq_programmed
    x.1 start XmssSecurity.CappedChain.allChains ∅ XmssSecurity.CappedChain.allChains_nodup
    (fun _ _ _ _ _ _ => rfl)
  rw [evalDist_bind, hchains, ← evalDist_bind]
  rfl

/-- The exact original guarded trace has an eager PRF and programmed-chain
representation, with every visible state field and real call count retained. -/
theorem traceRun_eq_eager_chains (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let pair ← $ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest))
        let pre ← XmssSecurity.CappedChain.programmedAllChainTrajectoriesFromCache
          x.1 (prfChainStarts pair.2) ∅ XmssSecurity.CappedChain.allChains
        Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
          (simulateQ (resolveSlots x.2.1 x.2.2 (refreshAllPrf slack pair.1 pair.2))
            (rawTraceProgram prims A x))).run (embedHashCache pre.2)] := by
  rw [traceRun_eq_eager_prf prims A x hkeys slack]
  apply evalDist_bind_congr
  intro pair _
  exact presampledTrace_eq_programmed_chains prims A x _ _

/-- The distinct threshold-PRF points that seed the global chain family. -/
def chainStartPoint : XmssSecurity.ChainKey × ChainIndex → Point
  | (.inl e, l) => .chain bottomLayer e l (digit 0)
  | (.inr b, l) => .chain topLayer (topKey b) l (digit 0)

theorem chainStartPoint_injective : Function.Injective chainStartPoint := by
  rintro ⟨key, chain⟩ ⟨other, otherChain⟩ h
  cases key <;> cases other <;> simp only [chainStartPoint, Point.chain.injEq] at h
  · exact Prod.ext (congrArg Sum.inl h.2.1) h.2.2.1
  · have := h.1
    contradiction
  · have := h.1
    contradiction
  · refine Prod.ext (congrArg Sum.inr (Fin.ext ?_)) h.2.2.1
    exact congrArg (fun e : KeyIndex => e.val) h.2.1

theorem prfChainStarts_point (F : Point → Digest) (index : XmssSecurity.ChainKey × ChainIndex) :
    prfChainStarts F index.1 index.2 = F (chainStartPoint index) := by
  rcases index with ⟨key, chain⟩
  cases key <;> rfl

/-- Replace only the seed coordinates, retaining every other PRF value. -/
def refreshChainStarts (F : Point → Digest)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) (point : Point) : Digest :=
  if h : ∃ index, chainStartPoint index = point then start h.choose.1 h.choose.2 else F point

theorem refreshChainStarts_value (F : Point → Digest)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) :
    prfChainStarts (refreshChainStarts F start) = start := by
  funext key chain
  rw [prfChainStarts_point _ (key, chain)]
  have h : ∃ index, chainStartPoint index = chainStartPoint (key, chain) := ⟨(key, chain), rfl⟩
  simp only [refreshChainStarts, dif_pos h, chainStartPoint_injective h.choose_spec]

theorem refreshChainStarts_twice (F : Point → Digest)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) :
    refreshChainStarts (refreshChainStarts F start) (prfChainStarts F) = F := by
  funext point
  by_cases h : ∃ index, chainStartPoint index = point
  · simp only [refreshChainStarts, dif_pos h, prfChainStarts_point, h.choose_spec]
  · simp only [refreshChainStarts, dif_neg h]

def refreshChainPair (pair : (Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest)) :
    (Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest) :=
  (refreshChainStarts pair.1 pair.2, prfChainStarts pair.1)

set_option backward.isDefEq.respectTransparency false in
theorem refreshChainPair_involutive : Function.Involutive refreshChainPair := by
  intro pair
  dsimp only [refreshChainPair]
  rw [refreshChainStarts_twice, refreshChainStarts_value]

/-- Joint uniform law retaining the whole PRF function together with the chain
seeds. This permits the existing global trajectory sampler to supply the seeds. -/
theorem refreshChainStarts_joint :
    𝒟[(fun pair => (refreshChainStarts pair.1 pair.2, pair.2)) <$>
      ($ᵗ ((Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest)))] =
    𝒟[(fun F => (F, prfChainStarts F)) <$> ($ᵗ (Point → Digest))] := by
  let observe : ((Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest)) →
      (Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest) :=
    fun pair => (pair.1, prfChainStarts pair.1)
  have he : (fun pair => (refreshChainStarts pair.1 pair.2, pair.2)) =
      observe ∘ refreshChainPair := by
    funext pair
    simp only [Function.comp_apply, observe, refreshChainPair, refreshChainStarts_value]
  have hu := evalDist_map_bijective_uniform_cross
    (α := (Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest))
    refreshChainPair refreshChainPair_involutive.bijective
  have hm : (fun pair => (refreshChainStarts pair.1 pair.2, pair.2)) <$>
      ($ᵗ ((Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest))) =
      observe <$> (refreshChainPair <$>
        ($ᵗ ((Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest)))) := by
    rw [Functor.map_map, he]
    rfl
  rw [hm, evalDist_map, hu, ← evalDist_map]
  have hp : observe <$>
      ($ᵗ ((Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest))) =
      (fun F => (F, prfChainStarts F)) <$>
        (Prod.fst <$> ($ᵗ ((Point → Digest) × (XmssSecurity.ChainKey → ChainIndex → Digest)))) := by
    rw [Functor.map_map]
  rw [hp, evalDist_map, evalDist_map_fst_uniformSample_prod, ← evalDist_map]

set_option backward.isDefEq.respectTransparency false in
/-- The chain-seed change of variables with an arbitrary continuation that
retains both the full PRF function and the sampled seeds. -/
theorem refreshChainStarts_bind {α : Type}
    (next : (Point → Digest) → (XmssSecurity.ChainKey → ChainIndex → Digest) → ProbComp α) :
    𝒟[($ᵗ (Point → Digest)) >>= fun F => next F (prfChainStarts F)] =
      𝒟[do
        let F ← $ᵗ (Point → Digest)
        let start ← XmssSecurity.CappedChain.Concrete.sampleChainStarts
        next (refreshChainStarts F start) start] := by
  have h := congrArg (fun d => d >>= fun pair => 𝒟[next pair.1 pair.2]) refreshChainStarts_joint
  simp only [← evalDist_bind, bind_map_left] at h
  rw [← h, evalDist_bind, ← XmssSecurity.evalDist_independent_uniform_pair,
    ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro F _
  have hstart : 𝒟[XmssSecurity.CappedChain.Concrete.sampleChainStarts] =
      𝒟[($ᵗ (XmssSecurity.ChainKey → ChainIndex → Digest))] := by
    apply SPMF.ext
    intro start
    change Pr[= start | XmssSecurity.CappedChain.Concrete.sampleChainStarts] =
      Pr[= start | ($ᵗ (XmssSecurity.ChainKey → ChainIndex → Digest))]
    rw [XmssSecurity.CappedChain.Concrete.probOutput_sampleChainStarts,
      probOutput_uniformSample]
    rfl
  rw [evalDist_bind, ← hstart, ← evalDist_bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original trace represented using leanVM's complete global chain
material. The PRF function is changed jointly at its seed coordinates; the
entire correlated share table and programmed hash cache feed the source. -/
theorem traceRun_eq_chain_material (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let table ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let F ← $ᵗ (Point → Digest)
        let material ← XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial x.1
        Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
          (simulateQ (resolveSlots x.2.1 x.2.2
              (refreshAllPrf slack table (refreshChainStarts F material.1)))
            (rawTraceProgram prims A x))).run (embedHashCache material.2.2)] := by
  rw [traceRun_eq_eager_chains prims A x hkeys slack, evalDist_bind,
    ← XmssSecurity.evalDist_independent_uniform_pair, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro table _
  have hseed := refreshChainStarts_bind (fun F start => do
    let pre ← XmssSecurity.CappedChain.programmedAllChainTrajectoriesFromCache
      x.1 start ∅ XmssSecurity.CappedChain.allChains
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
      (simulateQ (resolveSlots x.2.1 x.2.2 (refreshAllPrf slack table F))
        (rawTraceProgram prims A x))).run (embedHashCache pre.2))
  simpa only [XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial,
    bind_assoc, pure_bind] using hseed

set_option backward.isDefEq.respectTransparency false in
theorem chainTrajectory_queryBound_address (P : PublicParameter)
    (key : XmssSecurity.ChainKey) (chain : ChainIndex) (value : Digest)
    (domain : XmssSecurity.HashDomain) :
    IsQueryBoundP (XmssSecurity.Concrete.chainTrajectory P key chain 0 (chainLength - 1) value)
      (XmssSecurity.AtHashAddress P domain) 1 := by
  rw [← isQueryBoundP_map_iff _ Vector.back,
    XmssSecurity.Concrete.chainTrajectory_back_map_eq_keyChainWalk]
  cases key with
  | inl e =>
      rw [XmssSecurity.Concrete.keyChainWalk_inl]
      exact XmssSecurity.Concrete.chainWalk_queryBound_atAddress P e chain 0 _ value domain
  | inr b =>
      rw [XmssSecurity.Concrete.keyChainWalk_inr]
      exact XmssSecurity.Concrete.topChainWalk_queryBound_atAddress P b chain 0 _ value domain

set_option backward.isDefEq.respectTransparency false in
theorem privateChainColumn_queryBound (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) (chain targetChain : ChainIndex)
    (target : XmssSecurity.ChainKey) (step : XmssSecurity.ChainStep) :
    IsQueryBoundP (privateChainColumn P start chain XmssSecurity.allChainKeys)
      (XmssSecurity.AtHashAddress P (target.chainDomain targetChain step))
      (if chain = targetChain then 1 else 0) := by
  by_cases hc : chain = targetChain
  · subst targetChain
    simp only [if_true]
    have hbound := isQueryBoundP_listMapM
      (k := fun key : XmssSecurity.ChainKey => if key = target then 1 else 0)
      (f := fun key => XmssSecurity.Concrete.chainTrajectory P key chain 0
        (chainLength - 1) (start key chain))
      (p := XmssSecurity.AtHashAddress P (target.chainDomain chain step)) (fun key => ?_)
      XmssSecurity.allChainKeys
    · simpa only [privateChainColumn, XmssSecurity.allChainKeys, Finset.sum_map_toList,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using hbound
    · by_cases hk : key = target
      · simp only [hk, if_true]
        exact chainTrajectory_queryBound_address P target chain (start target chain) _
      · simp only [hk, if_false]
        apply XmssSecurity.Concrete.chainTrajectory_queryBound_zero_of_avoids
        intro offset hoffset hvalid heq
        exact hk (XmssSecurity.ChainKey.chainDomain_injective heq).1
  · simp only [hc, if_false]
    have hbound := isQueryBoundP_listMapM_const
      (k := 0) (f := fun key : XmssSecurity.ChainKey =>
        XmssSecurity.Concrete.chainTrajectory P key chain 0 (chainLength - 1) (start key chain))
      (p := XmssSecurity.AtHashAddress P (target.chainDomain targetChain step)) (fun key => ?_)
      XmssSecurity.allChainKeys
    · simpa only [privateChainColumn, Nat.mul_zero] using hbound
    · apply XmssSecurity.Concrete.chainTrajectory_queryBound_zero_of_avoids
      intro offset hoffset hvalid heq
      exact hc (XmssSecurity.ChainKey.chainDomain_injective heq).2.1

set_option backward.isDefEq.respectTransparency false in
theorem privateChains_queryBound (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) (chains : List ChainIndex)
    (target : XmssSecurity.ChainKey) (chain : ChainIndex) (step : XmssSecurity.ChainStep) :
    IsQueryBoundP (privateChains P start chains)
      (XmssSecurity.AtHashAddress P (target.chainDomain chain step))
      ((chains.map (fun l => if l = chain then 1 else 0)).sum) := by
  induction chains with
  | nil => simp [privateChains]
  | cons l chains ih =>
      simp only [privateChains, List.map_cons, List.sum_cons]
      apply isQueryBoundP_bind (privateChainColumn_queryBound P start l chain target step)
      intro first _
      simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ih

set_option backward.isDefEq.respectTransparency false in
/-- The private chain prefix contains at most one cached input at each chain
address, even though its cache will later service arbitrary adaptive queries. -/
theorem chainMaterial_unique_address (P : PublicParameter)
    (material : XmssSecurity.CappedChain.GlobalChainTrajectoryMaterial)
    (hm : material ∈ support (XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial P))
    (key : XmssSecurity.ChainKey) (chain : ChainIndex) (step : XmssSecurity.ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hladdr : XmssSecurity.AtHashAddress P (key.chainDomain chain step) left)
    (hraddr : XmssSecurity.AtHashAddress P (key.chainDomain chain step) right)
    (hl : material.2.2 left = some leftOutput) (hr : material.2.2 right = some rightOutput) :
    left = right := by
  have hbound : IsQueryBoundP (privateChains P material.1 XmssSecurity.CappedChain.allChains)
      (XmssSecurity.AtHashAddress P (key.chainDomain chain step)) 1 := by
    simpa only [XmssSecurity.CappedChain.allChains, Finset.sum_map_toList,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      privateChains_queryBound P material.1 XmssSecurity.CappedChain.allChains key chain step
  have hrun := XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial_support_as_actual
    P material hm
  rw [← privateChains_run] at hrun
  exact XmssSecurity.Concrete.CacheReplay.cache_unique_of_query_bound_one _ _ ∅ material.2.2
    material.2.1 hbound (by simp) hrun left right leftOutput rightOutput hladdr hraddr hl hr

def ChainAddress (P : PublicParameter) (input : HashInput) : Prop :=
  ∃ (key : XmssSecurity.ChainKey) (chain : ChainIndex) (step : XmssSecurity.ChainStep),
    XmssSecurity.AtHashAddress P (key.chainDomain chain step) input

set_option backward.isDefEq.respectTransparency false in
theorem chainTrajectory_queryBound_outside (P : PublicParameter)
    (key : XmssSecurity.ChainKey) (chain : ChainIndex) (position steps : ℕ) (value : Digest) :
    IsQueryBoundP (XmssSecurity.Concrete.chainTrajectory P key chain position steps value)
      (fun input => ¬ChainAddress P input) 0 := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [XmssSecurity.Concrete.chainTrajectory_succ]
      apply isQueryBoundP_bind (n := 0) (m := 0) ih
      intro values _
      split
      · rename_i hvalid
        apply isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => by simp)
        simp only [XmssSecurity.Concrete.keyChainHash, XmssSecurity.Concrete.tweakableHash,
          XmssSecurity.Concrete.oracleHash, bind_pure_comp, HasQuery.instOfMonadLift_query,
          isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro h
        exact (h ⟨key, chain, ⟨position + steps, hvalid⟩,
          (XmssSecurity.atHashAddress_tweakableHashInput_iff P _ _ _).mpr rfl⟩).elim
      · simp

set_option backward.isDefEq.respectTransparency false in
theorem privateChains_queryBound_outside (P : PublicParameter)
    (start : XmssSecurity.ChainKey → ChainIndex → Digest) (chains : List ChainIndex) :
    IsQueryBoundP (privateChains P start chains) (fun input => ¬ChainAddress P input) 0 := by
  induction chains with
  | nil => simp [privateChains]
  | cons chain chains ih =>
      rw [privateChains]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_ ?_
      · simpa only [privateChainColumn, Nat.mul_zero] using
          isQueryBoundP_listMapM_const (fun key =>
            chainTrajectory_queryBound_outside P key chain 0 (chainLength - 1) (start key chain))
            XmssSecurity.allChainKeys
      · intro first _
        simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ih

set_option backward.isDefEq.respectTransparency false in
theorem chainMaterial_address_of_cached (P : PublicParameter)
    (material : XmssSecurity.CappedChain.GlobalChainTrajectoryMaterial)
    (hm : material ∈ support (XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial P))
    (input : HashInput) (output : HashOutput) (hc : material.2.2 input = some output) :
    ChainAddress P input := by
  by_contra hno
  have hrun := XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial_support_as_actual
    P material hm
  rw [← privateChains_run] at hrun
  have habsent := XmssSecurity.Concrete.CacheReplay.cache_none_of_zero_query_bound
    (privateChains P material.1 XmssSecurity.CappedChain.allChains) input ∅ material.2.2 material.2.1
    (IsQueryBoundP.of_imp (fun candidate heq => heq ▸ hno)
      (privateChains_queryBound_outside P material.1 XmssSecurity.CappedChain.allChains)) rfl hrun
  rw [hc] at habsent
  contradiction

set_option backward.isDefEq.respectTransparency false in
/-- Every input cached by private chain generation is one of its canonical
edges. This includes the input value, not just its public chain address. -/
theorem chainMaterial_canonical_of_cached (P : PublicParameter)
    (material : XmssSecurity.CappedChain.GlobalChainTrajectoryMaterial)
    (hm : material ∈ support (XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial P))
    (input : HashInput) (output : HashOutput) (hc : material.2.2 input = some output) :
    ∃ edge : XmssSecurity.CappedChain.GlobalChainEdgeIndex,
      XmssSecurity.CappedChain.globalChainTableEdgeInput P
        (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material) edge = input := by
  obtain ⟨key, chain, step, haddr⟩ := chainMaterial_address_of_cached P material hm input output hc
  obtain ⟨canonical, hcanonical, _⟩ :=
    XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial_edgesMatch P material hm
      (chain, key, step)
  refine ⟨(chain, key, step), chainMaterial_unique_address P material hm key chain step
    _ input canonical output ?_ haddr hcanonical hc⟩
  exact XmssSecurity.Concrete.CacheView.keyChainInput_atHashAddress _ _ _ _ _

/-- The complete private chain cache, reconstructed from its labels and high
halves. It is used only in the mathematical source representation. -/
def chainTableCache (P : PublicParameter)
    (table : XmssSecurity.CappedChain.GlobalChainValueIndex → Digest)
    (high : XmssSecurity.CappedChain.GlobalChainEdgeIndex → Digest) : QueryCache HashSpec :=
  fun input => if h : ∃ edge, XmssSecurity.CappedChain.globalChainTableEdgeInput P table edge = input then
    some (XmssSecurity.CappedChain.globalChainEdgeOutputFromHigh high table h.choose) else none

set_option backward.isDefEq.respectTransparency false in
/-- The private prefix cache is determined by the full sampled labels and
high halves; no conditional independence of its contents is assumed. -/
theorem chainMaterial_cache_eq (P : PublicParameter)
    (material : XmssSecurity.CappedChain.GlobalChainTrajectoryMaterial)
    (hm : material ∈ support (XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial P)) :
    material.2.2 = chainTableCache P
      (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material)
      (XmssSecurity.CappedChain.globalChainEdgeHighTableOfCache material.2.2 P
        (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material)) := by
  funext input
  unfold chainTableCache
  split_ifs with h
  · have he : ∃ output : HashOutput,
        material.2.2 (XmssSecurity.CappedChain.globalChainTableEdgeInput P
          (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material) h.choose) = some output ∧
        truncateHash output = XmssSecurity.CappedChain.globalChainTableEdgeTarget
          (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material) h.choose :=
      XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial_edgesMatch P material hm h.choose
    obtain ⟨output, hc, ht⟩ := he
    have hinput : material.2.2 input = some output := by
      erw [← h.choose_spec]
      exact hc
    rw [hinput, XmssSecurity.CappedChain.globalChainEdgeOutputFromHigh_eq_cached
      material.2.2 P _ h.choose output hc ht]
  · cases hc : material.2.2 input with
    | none => rfl
    | some output => exact (h (chainMaterial_canonical_of_cached P material hm input output hc)).elim

set_option backward.isDefEq.respectTransparency false in
theorem chainMaterial_starts_eq (P : PublicParameter)
    (material : XmssSecurity.CappedChain.GlobalChainTrajectoryMaterial)
    (hm : material ∈ support (XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial P)) :
    material.1 = XmssSecurity.CappedChain.globalChainTableSeedTargets
      (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material) := by
  have ho := (mem_support_iff_of_evalDist_eq
    (XmssSecurity.CappedChain.evalDist_programmedGlobalChainTrajectoryMaterial_eq_output P)
    material).mp hm
  have h := XmssSecurity.CappedChain.globalChainRandomnessOfMaterial_secret P material ho
  change XmssSecurity.CappedChain.globalChainTableSeedTargets
    (XmssSecurity.CappedChain.globalChainTrajectoryMaterialTable material) = material.1 at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Use the pinned joint law of every chain label and every high half. The
cache reconstruction above permits arbitrary adaptive source continuations. -/
theorem chainMaterial_view_uniform (P : PublicParameter) :
    𝒟[XmssSecurity.CappedChain.globalChainTableHighViewOfMaterial P <$>
      XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial P] =
    𝒟[XmssSecurity.CappedChain.independentGlobalChainTableHigh] := by
  rw [evalDist_map,
    XmssSecurity.CappedChain.evalDist_programmedGlobalChainTrajectoryMaterial_eq_output,
    ← evalDist_map]
  have hf : XmssSecurity.CappedChain.globalChainTableHighViewOfMaterial P =
      XmssSecurity.CappedChain.globalChainKeygenRandomnessView ∘
        XmssSecurity.CappedChain.globalChainRandomnessOfMaterial P := by
    funext material
    exact (XmssSecurity.CappedChain.globalChainKeygenRandomnessView_ofView _).symm
  have hm : XmssSecurity.CappedChain.globalChainTableHighViewOfMaterial P <$>
      XmssSecurity.CappedChain.outputGlobalChainTrajectoryMaterial P =
      XmssSecurity.CappedChain.globalChainKeygenRandomnessView <$>
        (XmssSecurity.CappedChain.globalChainRandomnessOfMaterial P <$>
          XmssSecurity.CappedChain.outputGlobalChainTrajectoryMaterial P) := by
    rw [Functor.map_map, hf]
    rfl
  rw [hm, evalDist_map, XmssSecurity.CappedChain.evalDist_outputGlobalChainRandomness_eq_uniform,
    ← evalDist_map, XmssSecurity.CappedChain.evalDist_globalChainKeygenRandomnessView_eq_independent]

set_option backward.isDefEq.respectTransparency false in
/-- The original complete trace with independent global chain labels and
high halves. Its entire private cache is reconstructed, rather than discarded
by a marginal projection, before running the original adaptive source. -/
theorem traceRun_eq_independent_chains (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let table ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let F ← $ᵗ (Point → Digest)
        let view ← XmssSecurity.CappedChain.independentGlobalChainTableHigh
        Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
          (simulateQ (resolveSlots x.2.1 x.2.2 (refreshAllPrf slack table
              (refreshChainStarts F (XmssSecurity.CappedChain.globalChainTableSeedTargets view.1))))
            (rawTraceProgram prims A x))).run
              (embedHashCache (chainTableCache x.1 view.1 view.2))] := by
  rw [traceRun_eq_chain_material prims A x hkeys slack]
  apply evalDist_bind_congr
  intro table _
  apply evalDist_bind_congr
  intro F _
  let replay : ((XmssSecurity.CappedChain.GlobalChainValueIndex → Digest) ×
      (XmssSecurity.CappedChain.GlobalChainEdgeIndex → Digest)) →
      ProbComp (SigningLaneUnionProof.TraceOutcome C) := fun view =>
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
      (simulateQ (resolveSlots x.2.1 x.2.2 (refreshAllPrf slack table
          (refreshChainStarts F (XmssSecurity.CappedChain.globalChainTableSeedTargets view.1))))
        (rawTraceProgram prims A x))).run (embedHashCache (chainTableCache x.1 view.1 view.2))
  calc
    _ = 𝒟[(XmssSecurity.CappedChain.globalChainTableHighViewOfMaterial x.1 <$>
        XmssSecurity.CappedChain.programmedGlobalChainTrajectoryMaterial x.1) >>= replay] := by
      erw [bind_map_left]
      apply congrArg evalDist
      apply OracleComp.bind_congr_of_forall_mem_support
      intro material hm
      dsimp only [replay, XmssSecurity.CappedChain.globalChainTableHighViewOfMaterial]
      rw [← chainMaterial_starts_eq x.1 material hm, ← chainMaterial_cache_eq x.1 material hm]
    _ = _ := by
      rw [evalDist_bind, chainMaterial_view_uniform, ← evalDist_bind]
      rfl

abbrev PrfChainTables := (Point → Digest) × (XmssSecurity.CappedChain.GlobalChainValueIndex → Digest)

/-- The exact `HiddenKey` coordinates in the eager PRF and chain tables.
Chain endpoints remain outside this secret table. -/
def hiddenCoordinates (tables : PrfChainTables) : HiddenKey → Digest
  | .opening lay e => tables.1 (.randomizer lay e)
  | .bottomChain e l p => tables.2 (l, .inl e, XmssSecurity.CappedChain.chainStepDigit p)
  | .topChain b l p => tables.2 (l, .inr b, XmssSecurity.CappedChain.chainStepDigit p)

/-- Replace precisely the opening and nonterminal chain coordinates. -/
def installHiddenCoordinates (tables : PrfChainTables) (s : HiddenKey → Digest) : PrfChainTables :=
  ((fun point => match point with
    | .randomizer lay e => s (.opening lay e)
    | .chain .. => tables.1 point),
   fun index => if h : index.2.2.val < XmssSecurity.chainLength - 1 then
     match index.2.1 with
     | .inl e => s (.bottomChain e index.1 ⟨index.2.2.val, h⟩)
     | .inr b => s (.topChain b index.1 ⟨index.2.2.val, h⟩)
   else tables.2 index)

set_option backward.isDefEq.respectTransparency false in
theorem hiddenCoordinates_install (tables : PrfChainTables) (s : HiddenKey → Digest) :
    hiddenCoordinates (installHiddenCoordinates tables s) = s := by
  funext key
  cases key with
  | opening lay e => rfl
  | bottomChain e l p =>
      simp [hiddenCoordinates, installHiddenCoordinates,
        XmssSecurity.CappedChain.chainStepDigit, p.isLt]
  | topChain b l p =>
      simp [hiddenCoordinates, installHiddenCoordinates,
        XmssSecurity.CappedChain.chainStepDigit, p.isLt]

set_option backward.isDefEq.respectTransparency false in
theorem installHiddenCoordinates_twice (tables : PrfChainTables) (s : HiddenKey → Digest) :
    installHiddenCoordinates (installHiddenCoordinates tables s) (hiddenCoordinates tables) = tables := by
  apply Prod.ext
  · funext point
    cases point <;> rfl
  · funext index
    rcases index with ⟨chain, key, pos⟩
    by_cases h : pos.val < XmssSecurity.chainLength - 1
    · cases key <;> simp [installHiddenCoordinates, h, hiddenCoordinates,
        XmssSecurity.CappedChain.chainStepDigit]
    · simp [installHiddenCoordinates, h]

def hiddenCoordinateSwap (pair : PrfChainTables × (HiddenKey → Digest)) :
    PrfChainTables × (HiddenKey → Digest) :=
  (installHiddenCoordinates pair.1 pair.2, hiddenCoordinates pair.1)

theorem hiddenCoordinateSwap_involutive : Function.Involutive hiddenCoordinateSwap := by
  intro pair
  dsimp only [hiddenCoordinateSwap]
  rw [installHiddenCoordinates_twice, hiddenCoordinates_install]

/-- The exact hidden table is uniform jointly with all retained PRF and chain
data. Future observations may depend on the full installed tables. -/
theorem hiddenCoordinates_joint :
    𝒟[(fun pair => (installHiddenCoordinates pair.1 pair.2, pair.2)) <$>
      ($ᵗ (PrfChainTables × (HiddenKey → Digest)))] =
    𝒟[(fun tables => (tables, hiddenCoordinates tables)) <$> ($ᵗ PrfChainTables)] := by
  let observe : PrfChainTables × (HiddenKey → Digest) → PrfChainTables × (HiddenKey → Digest) :=
    fun pair => (pair.1, hiddenCoordinates pair.1)
  have he : (fun pair => (installHiddenCoordinates pair.1 pair.2, pair.2)) =
      observe ∘ hiddenCoordinateSwap := by
    funext pair
    simp only [Function.comp_apply, observe, hiddenCoordinateSwap, hiddenCoordinates_install]
  have hu := evalDist_map_bijective_uniform_cross
    (α := PrfChainTables × (HiddenKey → Digest)) hiddenCoordinateSwap
      hiddenCoordinateSwap_involutive.bijective
  have hm : (fun pair => (installHiddenCoordinates pair.1 pair.2, pair.2)) <$>
      ($ᵗ (PrfChainTables × (HiddenKey → Digest))) =
      observe <$> (hiddenCoordinateSwap <$> ($ᵗ (PrfChainTables × (HiddenKey → Digest)))) := by
    rw [Functor.map_map, he]
    rfl
  rw [hm, evalDist_map, hu, ← evalDist_map]
  have hp : observe <$> ($ᵗ (PrfChainTables × (HiddenKey → Digest))) =
      (fun tables => (tables, hiddenCoordinates tables)) <$>
        (Prod.fst <$> ($ᵗ (PrfChainTables × (HiddenKey → Digest)))) := by
    rw [Functor.map_map]
  rw [hp, evalDist_map, evalDist_map_fst_uniformSample_prod, ← evalDist_map]

/-- The fixed original trace source over a prescribed private share table and
chain cache. This is a representation used by the coupling proof. -/
def eagerTrace (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (slack : C.Term)
    (shares : TprfSecurityProof.Slot C → HashOutput) (tables : PrfChainTables)
    (high : XmssSecurity.CappedChain.GlobalChainEdgeIndex → Digest) :
    ProbComp (SigningLaneUnionProof.TraceOutcome C) :=
  Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
    (simulateQ (resolveSlots x.2.1 x.2.2 (refreshAllPrf slack shares
        (refreshChainStarts tables.1 (XmssSecurity.CappedChain.globalChainTableSeedTargets tables.2))))
      (rawTraceProgram prims A x))).run (embedHashCache (chainTableCache x.1 tables.2 high))

set_option backward.isDefEq.respectTransparency false in
theorem uniformPrfChainTables_law :
    𝒟[do
      let F ← $ᵗ (Point → Digest)
      let labels ← XmssSecurity.CappedChain.independentGlobalChainValueTable
      pure (F, labels)] = 𝒟[($ᵗ PrfChainTables)] := by
  rw [show (do
      let F ← $ᵗ (Point → Digest)
      let labels ← XmssSecurity.CappedChain.independentGlobalChainValueTable
      pure (F, labels)) =
      Prod.mk <$> ($ᵗ (Point → Digest)) <*>
        XmssSecurity.CappedChain.independentGlobalChainValueTable by simp [monad_norm]]
  apply evalDist_ext
  intro pair
  rw [probOutput_seq_map_prod_mk_eq_mul,
    XmssSecurity.CappedChain.independentGlobalChainValueTable_eq_uniform,
    probOutput_uniformSample, probOutput_uniformSample, probOutput_uniformSample]
  simp only [PrfChainTables, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem traceRun_eq_eager_tables (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let shares ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let tables ← $ᵗ PrfChainTables
        let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
        eagerTrace prims A x slack shares tables high] := by
  rw [traceRun_eq_independent_chains prims A x hkeys slack]
  apply evalDist_bind_congr
  intro shares _
  calc
    _ = 𝒟[(do
        let F ← $ᵗ (Point → Digest)
        let labels ← XmssSecurity.CappedChain.independentGlobalChainValueTable
        pure (F, labels)) >>= fun tables => do
          let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
          eagerTrace prims A x slack shares tables high] := by
      simp only [XmssSecurity.CappedChain.independentGlobalChainTableHigh,
        eagerTrace, bind_assoc, pure_bind]
    _ = _ := by
      rw [evalDist_bind, uniformPrfChainTables_law, ← evalDist_bind]
      rfl

/-- The original full trace with A100's exact uniformly sampled `HiddenKey`
table installed jointly into the PRF and chain data. All other sampled data
are retained for the later adaptive source execution. -/
theorem traceRun_eq_eager_hidden (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let shares ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let pair ← $ᵗ (PrfChainTables × (HiddenKey → Digest))
        let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
        eagerTrace prims A x slack shares (installHiddenCoordinates pair.1 pair.2) high] := by
  rw [traceRun_eq_eager_tables prims A x hkeys slack]
  apply evalDist_bind_congr
  intro shares _
  let next : PrfChainTables → ProbComp (SigningLaneUnionProof.TraceOutcome C) := fun tables => do
    let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
    eagerTrace prims A x slack shares tables high
  have h := congrArg (fun d => d >>= fun pair => 𝒟[next pair.1]) hiddenCoordinates_joint
  simpa only [← evalDist_bind, bind_map_left, next] using h.symm

/-- The two public bottom-row pads translate the corresponding PRF targets
by the actual hidden chain labels. -/
def bottomPrfOffset (s : HiddenKey → Digest) : Point → Digest
  | .chain lay e l p => if lay = bottomLayer then
      if p.val = 1 then s (.bottomChain e l ⟨1, by decide⟩)
      else if p.val = 2 then s (.bottomChain e l ⟨2, by decide⟩) else 0
    else 0
  | .randomizer .. => 0

def maskPrfChainTables (s : HiddenKey → Digest) (tables : PrfChainTables) : PrfChainTables :=
  (fun point => tables.1 point ^^^ bottomPrfOffset s point, tables.2)

theorem maskPrfChainTables_involutive (s : HiddenKey → Digest) :
    Function.Involutive (maskPrfChainTables s) := by
  intro tables
  apply Prod.ext
  · funext point
    simp [maskPrfChainTables, BitVec.xor_assoc]
  · rfl

theorem hiddenCoordinates_bind {α : Type} (next : PrfChainTables → ProbComp α) :
    𝒟[($ᵗ PrfChainTables) >>= next] =
      𝒟[do
        let s ← $ᵗ (HiddenKey → Digest)
        let tables ← $ᵗ PrfChainTables
        next (installHiddenCoordinates tables s)] := by
  have h := congrArg (fun d => d >>= fun pair => 𝒟[next pair.1]) hiddenCoordinates_joint
  simp only [← evalDist_bind, bind_map_left] at h
  rw [← h, evalDist_bind, ← XmssSecurity.evalDist_independent_uniform_pair, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ PrfChainTables)
    ($ᵗ (HiddenKey → Digest)) (fun tables s => next (installHiddenCoordinates tables s))

/-- The exact original trace source over one uniform `HiddenKey` table, with
independent bottom pads and chain high halves. The private share table remains
conditioned on the installed aggregate targets. -/
theorem traceRun_eq_symbolic_tables (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let s ← $ᵗ (HiddenKey → Digest)
        let shares ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let tables ← $ᵗ PrfChainTables
        let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
        eagerTrace prims A x slack shares
          (installHiddenCoordinates (maskPrfChainTables s tables) s) high] := by
  rw [traceRun_eq_eager_tables prims A x hkeys slack]
  let next := fun shares s tables => do
    let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
    eagerTrace prims A x slack shares (installHiddenCoordinates tables s) high
  calc
    _ = 𝒟[do
        let shares ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let s ← $ᵗ (HiddenKey → Digest)
        let tables ← $ᵗ PrfChainTables
        next shares s tables] := by
      apply evalDist_bind_congr
      intro shares _
      exact hiddenCoordinates_bind (fun tables => do
        let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
        eagerTrace prims A x slack shares tables high)
    _ = 𝒟[do
        let s ← $ᵗ (HiddenKey → Digest)
        let shares ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let tables ← $ᵗ PrfChainTables
        next shares s tables] :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        ($ᵗ (TprfSecurityProof.Slot C → HashOutput)) ($ᵗ (HiddenKey → Digest))
        (fun shares s => ($ᵗ PrfChainTables) >>= next shares s)
    _ = _ := by
      apply evalDist_bind_congr
      intro s _
      apply evalDist_bind_congr
      intro shares _
      have hu := evalDist_map_bijective_uniform_cross (α := PrfChainTables)
        (maskPrfChainTables s) (maskPrfChainTables_involutive s).bijective
      have hmap := congrArg (fun d => d >>= fun tables => 𝒟[next shares s tables]) hu
      simpa only [← evalDist_bind, bind_map_left, next] using hmap.symm

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- Every supported execution of the fixed symbolic-table representation
obeys the original real-world cap, for every sampled secret table. -/
theorem symbolicTables_count_le (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q)
    (s : HiddenKey → Digest) (shares : TprfSecurityProof.Slot C → HashOutput)
    (tables : PrfChainTables) (high : XmssSecurity.CappedChain.GlobalChainEdgeIndex → Digest)
    (r : SigningLaneUnionProof.TraceOutcome C)
    (hr : r ∈ support (eagerTrace prims A x slack shares
      (installHiddenCoordinates (maskPrfChainTables s tables) s) high)) :
    (SigningLaneUnionProof.observed r).2.1 ≤ q := by
  apply SigningLaneUnionProof.traceRun_count_le prims A q x hq r
  rw [← mem_support_evalDist_iff, traceRun_eq_symbolic_tables prims A x hkeys slack,
    mem_support_evalDist_iff, mem_support_bind_iff]
  refine ⟨s, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨shares, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨tables, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨high, ?_, ?_⟩
  · simp [XmssSecurity.CappedChain.independentGlobalChainHigh]
  · with_reducible exact hr

/-- Ordinary PRF reads with their values discarded. The private cache is kept
in the interpreter; this program does not change the visible trace or count. -/
def fillPrfQueries (seeds : C.Term → HashOutput) (point : Point) (terms : List C.Term) :
    OracleComp (Query C →ₒ HashOutput) (List Unit) :=
  terms.mapM fun T => do
    let _ ← query (spec := Query C →ₒ HashOutput) (.prf (seeds T) point)
    pure ()

@[simp] theorem replaceCompilerCache_twice (backend : CappedCompilerState C)
    (cache cache' : HashCache C) :
    replaceCompilerCache (replaceCompilerCache backend cache) cache' =
      replaceCompilerCache backend cache' := rfl

set_option backward.isDefEq.respectTransparency false in
/-- One silent source fill is an ordinary cache query with its value discarded.
The exact capped backend, including count and trace, is retained. -/
theorem runSource_fillTerm_randomOracle (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (point : Point) (T : C.Term) (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (fillTerm seeds point T)) source backend =
      (fun r => (((), source), replaceCompilerCache backend r.2)) <$>
        (((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run
          backend.1.1.data.cache) := by
  rw [runSource_fillTerm]
  cases hc : backend.1.1.data.cache (.prf (seeds T) point) with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, Functor.map_map]
      rfl
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, map_pure]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole actual silent filling routine is ordinary random-oracle filling,
with its source state and all non-cache backend fields left in place. -/
theorem runSource_fillTerms_randomOracle (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (point : Point) (terms : List C.Term) (source : SourceState C)
    (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (terms.mapM (fillTerm seeds point))) source backend =
      (fun r => ((r.1, source), replaceCompilerCache backend r.2)) <$>
        ((simulateQ (Query C →ₒ HashOutput).randomOracle
          (fillPrfQueries seeds point terms)).run backend.1.1.data.cache) := by
  induction terms generalizing source backend with
  | nil => simp [fillPrfQueries, runSource_pure, replaceCompilerCache]
  | cons T terms ih =>
      simp only [List.mapM_cons, liftM_bind, liftM_pure, runSource_bind,
        runSource_fillTerm_randomOracle, bind_map_left]
      simp only [fillPrfQueries, List.mapM_cons, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, map_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, bind_assoc, pure_bind]
      apply bind_congr
      intro head
      rw [ih]
      simp only [runSource_pure, bind_map_left, map_pure, replaceCompilerCache_twice]
      rfl

/-- A full ordinary filling schedule includes every specified term in the
resulting cache, independently of the initial cache and of repeated reads. -/
theorem fillPrfQueries_cached (seeds : C.Term → HashOutput) (point : Point)
    (terms : List C.Term) (cache : HashCache C)
    (r : List Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (fillPrfQueries seeds point terms)).run cache)) :
    cache ≤ r.2 ∧ ∀ T ∈ terms, ∃ value, r.2 (.prf (seeds T) point) = some value := by
  induction terms generalizing cache r with
  | nil =>
      simp only [fillPrfQueries, List.mapM_nil, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hr
      subst r
      exact ⟨le_rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons T terms ih =>
      simp only [fillPrfQueries, List.mapM_cons, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, HasQuery.instOfMonadLift_query, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, bind_assoc, pure_bind,
        mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨head, hhead, tail, htail, rfl⟩ := hr
      have hh := randomOracle_support (.prf (seeds T) point) cache head hhead
      have ht := ih head.2 tail htail
      refine ⟨hh.1.trans ht.1, ?_⟩
      intro U hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨head.1, ht.1 hh.2.1⟩
      · exact ht.2 U hu

/-- Retain just the cache of an ordinary PRF filling schedule. -/
def fillPrfCache (seeds : C.Term → HashOutput) (point : Point)
    (terms : List C.Term) (cache : HashCache C) : ProbComp (HashCache C) :=
  Prod.snd <$> ((simulateQ (Query C →ₒ HashOutput).randomOracle
    (fillPrfQueries seeds point terms)).run cache)

@[simp] theorem fillPrfCache_nil (seeds : C.Term → HashOutput) (point : Point)
    (cache : HashCache C) : fillPrfCache seeds point [] cache = pure cache := by
  simp [fillPrfCache, fillPrfQueries]

theorem fillPrfCache_cons (seeds : C.Term → HashOutput) (point : Point)
    (T : C.Term) (terms : List C.Term) (cache : HashCache C) :
    fillPrfCache seeds point (T :: terms) cache =
      ((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run cache >>= fun r =>
        fillPrfCache seeds point terms r.2 := by
  simp only [fillPrfCache, fillPrfQueries, List.mapM_cons,
    HasQuery.instOfMonadLift_query, simulateQ_bind, simulateQ_pure,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind]
  simp only [bind_pure_comp]

/-- Replaying an already cached filling schedule is a deterministic no-op. -/
theorem fillPrfCache_resolved (seeds : C.Term → HashOutput) (point : Point)
    (terms : List C.Term) (cache : HashCache C)
    (hc : ∀ T ∈ terms, ∃ value, cache (.prf (seeds T) point) = some value) :
    fillPrfCache seeds point terms cache = pure cache := by
  induction terms with
  | nil => exact fillPrfCache_nil seeds point cache
  | cons T terms ih =>
      obtain ⟨value, hv⟩ := hc T (List.mem_cons_self ..)
      rw [fillPrfCache_cons, QueryImpl.withCaching_run_some _ hv, pure_bind]
      exact ih (fun U hu => hc U (List.mem_cons_of_mem _ hu))

/-- Any earlier consisting of terms that the schedule will fill can be sampled
early, including terms that were already cached. The final cache law is exact. -/
theorem evalDist_fillPrfCache_prefix (seeds : C.Term → HashOutput) (point : Point)
    (terms earlier : List C.Term) (hsub : ∀ T ∈ earlier, T ∈ terms) (cache : HashCache C) :
    𝒟[fillPrfCache seeds point terms cache] =
      𝒟[fillPrfCache seeds point earlier cache >>= fillPrfCache seeds point terms] := by
  induction earlier generalizing cache with
  | nil => simp
  | cons T earlier ih =>
      have hquery := evalDist_randomOracle_run_eq_query_then_of_cached
        (fillPrfQueries seeds point terms) cache (.prf (seeds T) point)
        (fun r hr => (fillPrfQueries_cached seeds point terms cache r hr).2 T
          (hsub T (List.mem_cons_self ..)))
      have hmap := congrArg (fun d => Prod.snd <$> d) hquery
      simp only [← evalDist_map, map_bind] at hmap
      change 𝒟[fillPrfCache seeds point terms cache] =
        𝒟[((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run cache >>=
          fun r => fillPrfCache seeds point terms r.2] at hmap
      rw [hmap, fillPrfCache_cons, bind_assoc]
      apply evalDist_bind_congr
      intro r _
      exact ih (fun U hu => hsub U (List.mem_cons_of_mem _ hu)) r.2

/-- The ordinary full-cache law depends only on which terms are filled, not
on their order or repetitions. -/
theorem evalDist_fillPrfCache_ext (seeds : C.Term → HashOutput) (point : Point)
    (left right : List C.Term) (hmem : ∀ T, T ∈ left ↔ T ∈ right) (cache : HashCache C) :
    𝒟[fillPrfCache seeds point left cache] = 𝒟[fillPrfCache seeds point right cache] := by
  rw [evalDist_fillPrfCache_prefix seeds point left right (fun T h => (hmem T).mpr h) cache]
  conv_rhs => rw [← bind_pure (fillPrfCache seeds point right cache)]
  apply evalDist_bind_congr
  intro result hr
  simp only [fillPrfCache, support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  rw [fillPrfCache_resolved seeds point left r.2]
  intro T ht
  exact (fillPrfQueries_cached seeds point right cache r hr).2 T ((hmem T).mp ht)

theorem fillPrfCache_append (seeds : C.Term → HashOutput) (point : Point)
    (left right : List C.Term) (cache : HashCache C) :
    fillPrfCache seeds point (left ++ right) cache =
      fillPrfCache seeds point left cache >>= fillPrfCache seeds point right := by
  induction left generalizing cache with
  | nil => simp
  | cons T left ih => simp only [List.cons_append, fillPrfCache_cons, ih, bind_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The adaptive completion is the exact fixed-target fiber of the canonical
all-term cache law. This includes every field of the existing capped backend. -/
theorem probEvent_completePrf_fiber_all (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hmissing : firstUnmaterialized seeds backend.1.1.data point ≠ none)
    (event : CappedCompilerState C → Prop) :
    (Fintype.card Digest : ℝ≥0∞)⁻¹ *
      Pr[fun r => event r.2 |
        runSource P seeds q s (liftM (completePrf seeds point target)) source backend] =
      Pr[fun cache =>
        termSum (cachedTerm seeds { backend.1.1.data with cache := cache } point) = target ∧
          event (replaceCompilerCache backend cache) |
        fillPrfCache seeds point C.terms backend.1.1.data.cache] := by
  obtain ⟨slack, hfirst⟩ := Option.ne_none_iff_exists'.mp hmissing
  rw [probEvent_completePrf_fiber P seeds hinj q s point slack target source backend hfirst]
  have hmem : ∀ T : C.Term, T ∈ C.terms.filter (· ≠ slack) ++ [slack] ↔ T ∈ C.terms := by
    intro T
    simp only [List.mem_append, List.mem_filter, List.mem_singleton, mem_terms, true_and,
      decide_eq_true_eq]
    tauto
  have heq := evalDist_fillPrfCache_ext seeds point
    (C.terms.filter (· ≠ slack) ++ [slack]) C.terms hmem backend.1.1.data.cache
  rw [← probEvent_congr' (fun _ _ => Iff.rfl) heq]
  have hsingle : fillPrfCache seeds point [slack] = fun cache =>
      Prod.snd <$> (((Query C →ₒ HashOutput).randomOracle (.prf (seeds slack) point)).run cache) := by
    funext cache
    simp only [fillPrfCache_cons, fillPrfCache_nil, bind_pure_comp]
  rw [fillPrfCache_append, hsingle]
  simp only [runSource_fillTerms_randomOracle, runSource_fillTerm_randomOracle, bind_map_left]
  simp only [fillPrfCache, bind_map_left]
  simp only [probEvent_bind_eq_tsum, probEvent_map, replaceCompilerCache_twice]
  rfl

/-- One ordinary term can be materialized before the actual fixed-target
completion while a distinct slack term remains missing. This is an exact law
for arbitrary observations of the complete capped backend, with no freshness
assumption on the supplied target. -/
theorem probEvent_completePrf_delay_fill (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest)
    (T slack : C.Term) (hne : slack ≠ T) (source : SourceState C)
    (backend : CappedCompilerState C)
    (hslack : backend.1.1.data.cache (.prf (seeds slack) point) = none)
    (event : CappedCompilerState C → Prop) :
    Pr[fun r => event r.2 |
      runSource P seeds q s (liftM (completePrf seeds point target)) source backend] =
    Pr[fun r => event r.2 | do
      let filled ← runSource P seeds q s (liftM (fillTerm seeds point T)) source backend
      runSource P seeds q s (liftM (completePrf seeds point target)) filled.1.2 filled.2] := by
  have missing (st : DeferredState C) (h : st.cache (.prf (seeds slack) point) = none) :
      firstUnmaterialized seeds st point ≠ none := by
    intro hf
    obtain ⟨value, hv⟩ := (firstUnmaterialized_none_iff seeds st point).mp hf slack
    rw [h] at hv
    cases hv
  let eventCache : HashCache C → Prop := fun cache =>
    termSum (cachedTerm seeds { backend.1.1.data with cache := cache } point) = target ∧
      event (replaceCompilerCache backend cache)
  have hright :
      (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        Pr[fun r => event r.2 | do
          let filled ← runSource P seeds q s (liftM (fillTerm seeds point T)) source backend
          runSource P seeds q s (liftM (completePrf seeds point target)) filled.1.2 filled.2] =
      Pr[eventCache | do
        let r ← ((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run
          backend.1.1.data.cache
        fillPrfCache seeds point C.terms r.2] := by
    simp only [runSource_fillTerm_randomOracle, bind_map_left, probEvent_bind_eq_tsum]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro r
    rw [mul_left_comm]
    by_cases hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle
        (.prf (seeds T) point)).run backend.1.1.data.cache)
    · have hs : r.2 (.prf (seeds slack) point) = none := by
        rw [(randomOracle_support (.prf (seeds T) point) backend.1.1.data.cache r hr).2.2]
        · exact hslack
        · intro he
          exact hne (hinj (Query.prf.inj he).1)
      rw [probEvent_completePrf_fiber_all P seeds hinj q s point target source
        (replaceCompilerCache backend r.2) (missing _ hs) event]
      rfl
    · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
  have hearly := evalDist_fillPrfCache_prefix seeds point C.terms [T]
    (fun U _ => mem_terms U) backend.1.1.data.cache
  have hsingle : fillPrfCache seeds point [T] = fun cache =>
      Prod.snd <$> (((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run cache) := by
    funext cache
    simp only [fillPrfCache_cons, fillPrfCache_nil, bind_pure_comp]
  rw [hsingle, bind_map_left] at hearly
  apply (ENNReal.mul_right_inj (a := (Fintype.card Digest : ℝ≥0∞)⁻¹)
    (by simp) (by simp)).mp
  rw [hright, probEvent_completePrf_fiber_all P seeds hinj q s point target source backend
    (missing _ hslack) event]
  exact probEvent_congr' (fun _ _ => Iff.rfl) hearly

/-- The fixed-target postponement law as equality of the complete backend
marginals, suitable for arbitrary adaptive continuations. -/
theorem evalDist_completePrf_delay_fill (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest)
    (T slack : C.Term) (hne : slack ≠ T) (source : SourceState C)
    (backend : CappedCompilerState C)
    (hslack : backend.1.1.data.cache (.prf (seeds slack) point) = none) :
    𝒟[Prod.snd <$> runSource P seeds q s
      (liftM (completePrf seeds point target)) source backend] =
    𝒟[Prod.snd <$> (do
      let filled ← runSource P seeds q s (liftM (fillTerm seeds point T)) source backend
      runSource P seeds q s (liftM (completePrf seeds point target)) filled.1.2 filled.2)] := by
  apply evalDist_ext
  intro result
  simp only [← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_completePrf_delay_fill P seeds hinj q s point target T slack hne
    source backend hslack (fun b => b = result)

set_option backward.isDefEq.respectTransparency false in
/-- A deferred query with no hidden candidate leaves the capped flag unchanged.
Its actual counted-call increment is retained, including cache hits. -/
theorem runSource_deferredQuery_no_candidate (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
    (t : DeferredQuery C) (hc : deferredCandidate P t = none)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery t)) source backend =
      (fun r => ((r.1, source),
        ((r.2, backend.1.2 + if deferredCounted t then 1 else 0), backend.2))) <$>
          ((compilerImpl P seeds t).run backend.1.1) := by
  change (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
      (deferredQuery t >>= fun value => pure (value, source))).run backend = _
  simp only [deferredQuery, HasQuery.instOfMonadLift_query, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, SigningCappedExpectProof.cappedHybrid,
    revealImpl, countImpl, StateT.run_mk, deferredInputSide, hc, Option.isSome_none,
    Bool.false_eq_true, and_false, false_and, false_or, decide_false, Bool.or_false,
    bind_map_left, Functor.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual counted compiler PRF call is precisely one lazy cache query.
Neither a base grind nor a trace update occurs on this structured query. -/
theorem runSource_prfQuery (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (seed : HashOutput) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) (.hash (.prf seed point))))
      source backend =
      (fun r => ((r.1, source),
        (({ backend.1.1 with data := { backend.1.1.data with cache := r.2 } },
          backend.1.2 + 1), backend.2))) <$>
        (((Query C →ₒ HashOutput).randomOracle (.prf seed point)).run
          backend.1.1.data.cache) := by
  rw [runSource_deferredQuery_no_candidate P seeds q s (.hash (.prf seed point)) rfl]
  have noBase : ¬∃ e, SigningGuessProof.RandomizerCached seeds backend.1.1.data.cache e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds backend.1.1.data.cache e)
        (compilerSigning backend.1.1) (.inr (.inr (.inl (.prf seed point)))) := by
    rintro ⟨e, _, input, _, hcall⟩
    rcases hcall with hcall | hcall <;> cases hcall
  rw [SigningCompilerPotential.compiler_hash_no_trigger P seeds (.prf seed point)
    backend.1.1 noBase, Functor.map_map]
  simp only [deferredCounted, if_true]

/-- Increment exactly the existing capped counter. -/
def incrementCompilerCount (backend : CappedCompilerState C) : CappedCompilerState C :=
  ((backend.1.1, backend.1.2 + 1), backend.2)

@[simp] theorem replaceCompilerCache_increment (backend : CappedCompilerState C)
    (cache : HashCache C) :
    replaceCompilerCache (incrementCompilerCount backend) cache =
      incrementCompilerCount (replaceCompilerCache backend cache) := rfl

/-- Interpreting a lifted backend program leaves the source-owned state fixed. -/
theorem runSource_liftM {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest)
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM oa) source backend =
      (fun r => ((r.1, source), r.2)) <$>
        ((simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
          oa).run backend) := by
  unfold runSource
  have hlift : (liftM oa : SourceM C α).run source = (fun a => (a, source)) <$> oa := rfl
  rw [hlift, simulateQ_map, StateT.run_map]

theorem runSource_liftM_source {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest)
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM oa) source backend)) :
    r.1.2 = source := by
  rw [runSource_liftM, support_map] at hr
  obtain ⟨a, _, rfl⟩ := hr
  rfl

/-- A counted term read after completion returns the installed value and
increments the count once, even though it is a cache hit. -/
theorem runSource_completePrf_then_read (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest) (T : C.Term)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (do
      let _ ← liftM (completePrf seeds point target)
      liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))) source backend =
      (fun r => (((r.2.1.1.data.cache (.prf (seeds T) point)).getD 0, source),
        incrementCompilerCount r.2)) <$>
        runSource P seeds q s (liftM (completePrf seeds point target)) source backend := by
  rw [runSource_bind, map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro r hr
  have hs := runSource_liftM_source P seeds q s (completePrf seeds point target)
    source backend r hr
  obtain ⟨value, hv⟩ := (completePrf_correct P seeds hinj q s point target source backend r hr).1 T
  rw [runSource_prfQuery, QueryImpl.withCaching_run_some _ hv, map_pure]
  simp only [Function.comp_apply, hv, Option.getD_some, hs]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact postponement across an actual counted PRF query. Both the returned
term value and the complete backend are retained; the call is still counted
once on either side, including when the term was already cached. -/
theorem probEvent_completePrf_delay_read (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest)
    (T slack : C.Term) (hne : slack ≠ T) (source : SourceState C)
    (backend : CappedCompilerState C)
    (hslack : backend.1.1.data.cache (.prf (seeds slack) point) = none)
    (event : HashOutput → CappedCompilerState C → Prop) :
    Pr[fun r => event r.1.1 r.2 | runSource P seeds q s (do
      let _ ← liftM (completePrf seeds point target)
      liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))) source backend] =
    Pr[fun r => event r.1.1 r.2 | runSource P seeds q s (do
      let value ← liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))
      let _ ← liftM (completePrf seeds point target)
      pure value) source backend] := by
  have missing (st : DeferredState C) (h : st.cache (.prf (seeds slack) point) = none) :
      firstUnmaterialized seeds st point ≠ none := by
    intro hf
    obtain ⟨value, hv⟩ := (firstUnmaterialized_none_iff seeds st point).mp hf slack
    rw [h] at hv
    cases hv
  let eventCache : HashCache C → Prop := fun cache =>
    termSum (cachedTerm seeds { backend.1.1.data with cache := cache } point) = target ∧
      event ((cache (.prf (seeds T) point)).getD 0)
        (incrementCompilerCount (replaceCompilerCache backend cache))
  have hright :
      (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        Pr[fun r => event r.1.1 r.2 | runSource P seeds q s (do
          let value ← liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))
          let _ ← liftM (completePrf seeds point target)
          pure value) source backend] =
      Pr[eventCache | do
        let r ← ((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run
          backend.1.1.data.cache
        fillPrfCache seeds point C.terms r.2] := by
    simp only [runSource_bind, runSource_prfQuery, runSource_pure]
    simp only [bind_map_left, bind_pure_comp]
    simp only [probEvent_bind_eq_tsum, probEvent_map]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro r
    rw [mul_left_comm]
    by_cases hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle
        (.prf (seeds T) point)).run backend.1.1.data.cache)
    · have hs : r.2 (.prf (seeds slack) point) = none := by
        rw [(randomOracle_support (.prf (seeds T) point) backend.1.1.data.cache r hr).2.2]
        · exact hslack
        · intro he
          exact hne (hinj (Query.prf.inj he).1)
      change _ * ((Fintype.card Digest : ℝ≥0∞)⁻¹ *
        Pr[fun done => event r.1 done.2 | runSource P seeds q s
          (liftM (completePrf seeds point target)) source
          (incrementCompilerCount (replaceCompilerCache backend r.2))]) = _
      rw [probEvent_completePrf_fiber_all P seeds hinj q s point target source
        (incrementCompilerCount (replaceCompilerCache backend r.2)) (missing _ hs)]
      congr 1
      apply probEvent_congr' _ rfl
      intro cache hc
      simp only [fillPrfCache, support_map] at hc
      obtain ⟨filled, hfilled, rfl⟩ := hc
      have ht := (randomOracle_support (.prf (seeds T) point) backend.1.1.data.cache r hr).2.1
      have hv := (fillPrfQueries_cached seeds point C.terms r.2 filled hfilled).1 ht
      simp only [replaceCompilerCache_increment, replaceCompilerCache_twice,
        eventCache, hv, Option.getD_some]
      rfl
    · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
  have hearly := evalDist_fillPrfCache_prefix seeds point C.terms [T]
    (fun U _ => mem_terms U) backend.1.1.data.cache
  have hsingle : fillPrfCache seeds point [T] = fun cache =>
      Prod.snd <$> (((Query C →ₒ HashOutput).randomOracle (.prf (seeds T) point)).run cache) := by
    funext cache
    simp only [fillPrfCache_cons, fillPrfCache_nil, bind_pure_comp]
  rw [hsingle, bind_map_left] at hearly
  apply (ENNReal.mul_right_inj (a := (Fintype.card Digest : ℝ≥0∞)⁻¹)
    (by simp) (by simp)).mp
  rw [hright, runSource_completePrf_then_read P seeds hinj]
  erw [probEvent_map]
  change (Fintype.card Digest : ℝ≥0∞)⁻¹ *
    Pr[fun r => event ((r.2.1.1.data.cache (.prf (seeds T) point)).getD 0)
      (incrementCompilerCount r.2) |
      runSource P seeds q s (liftM (completePrf seeds point target)) source backend] = _
  erw [probEvent_completePrf_fiber_all P seeds hinj q s point target source backend
    (missing _ hslack) (fun b => event ((b.1.1.data.cache (.prf (seeds T) point)).getD 0)
      (incrementCompilerCount b))]
  exact probEvent_congr' (fun _ _ => Iff.rfl) hearly

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual source/interpreter law for moving a counted term read
before fixed-target completion. The returned value, source state, cache, trace,
reveal state, flag, and counter are all retained. -/
theorem evalDist_completePrf_delay_read (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest)
    (T slack : C.Term) (hne : slack ≠ T) (source : SourceState C)
    (backend : CappedCompilerState C)
    (hslack : backend.1.1.data.cache (.prf (seeds slack) point) = none) :
    𝒟[runSource P seeds q s (do
      let _ ← liftM (completePrf seeds point target)
      liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))) source backend] =
    𝒟[runSource P seeds q s (do
      let value ← liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))
      let _ ← liftM (completePrf seeds point target)
      pure value) source backend] := by
  let before : SourceM C HashOutput := do
    let _ ← liftM (completePrf seeds point target)
    liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))
  let after : SourceM C HashOutput := do
    let value ← liftM (deferredQuery (C := C) (.hash (.prf (seeds T) point)))
    let _ ← liftM (completePrf seeds point target)
    pure value
  have hb : ∀ r ∈ support (runSource P seeds q s before source backend), r.1.2 = source := by
    intro r hr
    apply runSource_liftM_source P seeds q s (do
      let _ ← completePrf seeds point target
      deferredQuery (C := C) (.hash (.prf (seeds T) point))) source backend r
    simpa only [liftM_bind, before] using hr
  have ha : ∀ r ∈ support (runSource P seeds q s after source backend), r.1.2 = source := by
    intro r hr
    apply runSource_liftM_source P seeds q s (do
      let value ← deferredQuery (C := C) (.hash (.prf (seeds T) point))
      let _ ← completePrf seeds point target
      pure value) source backend r
    simpa only [liftM_bind, liftM_pure, after] using hr
  change 𝒟[runSource P seeds q s before source backend] =
    𝒟[runSource P seeds q s after source backend]
  apply evalDist_ext
  intro result
  simp only [← probEvent_eq_eq_probOutput]
  calc
    _ = Pr[fun r => ((r.1.1, source), r.2) = result |
        runSource P seeds q s before source backend] := by
      apply probEvent_congr' _ rfl
      intro r hr
      rw [← hb r hr]
    _ = Pr[fun r => ((r.1.1, source), r.2) = result |
        runSource P seeds q s after source backend] :=
      probEvent_completePrf_delay_read P seeds hinj q s point target T slack hne
        source backend hslack (fun value st => ((value, source), st) = result)
    _ = _ := by
      apply probEvent_congr' _ rfl
      intro r hr
      rw [← ha r hr]

/-- The finite chain-edge coordinates whose noise is sampled by the compiler. -/
abbrev ChainNoiseIndex := XmssSecurity.CappedChain.GlobalChainEdgeIndex

def chainPending (edge : ChainNoiseIndex) : PendingInput :=
  match edge.2.1 with
  | .inl e => .bottom e edge.1 edge.2.2
  | .inr b => .top b edge.1 edge.2.2

def pendingChain? : PendingInput → Option ChainNoiseIndex
  | .bottom e l p => some (l, .inl e, p)
  | .top b l p => some (l, .inr b, p)
  | _ => none

@[simp] theorem pendingChain_chainPending (edge : ChainNoiseIndex) :
    pendingChain? (chainPending edge) = some edge := by
  rcases edge with ⟨l, e | b, p⟩ <;> rfl

theorem chainPending_injective : Function.Injective chainPending := by
  intro left right he
  have h := congrArg pendingChain? he
  simpa only [pendingChain_chainPending, Option.some.injEq] using h

/-- Extract exactly the symbolic answer used by the frozen `samplePending`. -/
def pendingOutput (p : PendingInput) (value : HashOutput) : DeferredOutput :=
  let halves := XmssSecurity.Rom.hashOutputEquivDigestPair value
  ⟨halves.1, match p.next with
    | some k => .secret k
    | none => .known halves.2⟩

theorem samplePending_eq_map (p : PendingInput) :
    samplePending p = pendingOutput p <$> ($ᵗ HashOutput) := by
  simp only [samplePending, bind_pure_comp]
  rfl

/-- Materialized pending entries never disappear, including after a record
replaces an answer. This is a statement about domains, not value equality. -/
theorem deferredImpl_pending_mono (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) (p : PendingInput)
    (hp : st.pending p ≠ none) : r.2.pending p ≠ none := by
  cases t with
  | hash query =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact hp
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          by_cases he : p = key
          · subst p
            simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
          · simpa only [Function.update_of_ne he] using hp
  | pad point =>
      cases hk : st.pads point with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact hp
  | plant input value =>
      cases hc : st.cache input.query <;>
        simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr <;>
        subst r <;> exact hp
  | sample =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hp
  | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hp
  | record key value =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      by_cases he : p = key
      · subst p
        simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
      · simpa only [Function.update_of_ne he] using hp
  | virtual term point =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp
  | inspect key =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp
  | snapshot =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp
  | bindKey e message =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp

/-- The cached-extra adapter preserves the same pending-domain fact. -/
theorem compilerImpl_pending_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) (p : PendingInput)
    (hp : st.data.pending p ≠ none) : r.2.data.pending p ≠ none := by
  cases t with
  | hash query =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, _, rfl⟩ := hr
      exact deferredImpl_pending_mono (.hash query) st.data a ha p hp
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_pending_mono _ st.data a ha p hp

/-- A private chain-noise cache records only draws already made by the source.
A pre-sampled private cache will be used only after the exact raw-source law;
it is never substituted for the compiler's visible pending map. -/
def ChainNoiseInv (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache)
    (backend : CappedCompilerState C) : Prop :=
  ∀ edge, backend.1.1.data.pending (chainPending edge) = none → noise edge = none

abbrev ChainNoiseSpec := SigningGuessProof.PrivateRoSpec ChainNoiseIndex HashOutput

def chainNoiseRawPending (p : PendingInput) (edge : ChainNoiseIndex)
    (backend : CappedCompilerState C) :
    OracleComp ChainNoiseSpec (DeferredOutput × CappedCompilerState C) :=
  match backend.1.1.data.pending p with
  | some value => pure (value, incrementCompilerCount backend)
  | none => do
      let value ← query (spec := ChainNoiseSpec) (.inr edge)
      let answer := pendingOutput p value
      pure (answer, (({ backend.1.1 with data := { backend.1.1.data with
        pending := Function.update backend.1.1.data.pending p (some answer) } },
          backend.1.2 + 1), backend.2))

/-- Reify only fresh chain-noise draws. Every other actual capped compiler
step is lifted verbatim, and its visible state is retained in the result. -/
def cappedChainNoiseRaw (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) :
    QueryImpl (DeferredSpec C + RevealSpec HiddenKey Digest)
      (StateT (CappedCompilerState C) (OracleComp ChainNoiseSpec))
  | .inl (.pending (.bottom e l p)) => chainNoiseRawPending (.bottom e l p) (l, .inl e, p)
  | .inl (.pending (.top b l p)) => chainNoiseRawPending (.top b l p) (l, .inr b, p)
  | t => fun backend => liftM
      ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)

set_option backward.isDefEq.respectTransparency false in
/-- The exact actual pending kernel, including its one counted call. -/
theorem cappedCompiler_pending_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) (backend : CappedCompilerState C) :
    ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
      (.inl (.pending p))).run backend) =
    match backend.1.1.data.pending p with
    | some answer => pure (answer, incrementCompilerCount backend)
    | none => (fun value : HashOutput =>
        let answer := pendingOutput p value
        (answer, (({ backend.1.1 with data := { backend.1.1.data with
          pending := Function.update backend.1.1.data.pending p (some answer) } },
            backend.1.2 + 1), backend.2))) <$> ($ᵗ HashOutput) := by
  simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl, 
    deferredInputSide, deferredCandidate, Option.isSome_none, Bool.false_eq_true,
    and_false, false_and, false_or, decide_false, Bool.or_false, deferredCounted, if_true,
    compilerImpl, deferredImpl, StateT.run, StateT.mk]
  cases hp : backend.1.1.data.pending p with
  | some answer => simp only [map_pure]; rfl
  | none => simp only [samplePending_eq_map, Functor.map_map]

/-- The private-noise reading kernel exposes exactly one fresh draw when the
visible pending entry is absent. A previously visible answer is replayed. -/
theorem chainNoiseRawPending_run (p : PendingInput) (edge : ChainNoiseIndex)
    (backend : CappedCompilerState C) (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache)
    (hfresh : backend.1.1.data.pending p = none → noise edge = none) :
    (simulateQ SigningGuessProof.privateRoImpl (chainNoiseRawPending p edge backend)).run noise =
    match backend.1.1.data.pending p with
    | some answer => pure ((answer, incrementCompilerCount backend), noise)
    | none => (fun value : HashOutput =>
        let answer := pendingOutput p value
        ((answer, (({ backend.1.1 with data := { backend.1.1.data with
          pending := Function.update backend.1.1.data.pending p (some answer) } },
            backend.1.2 + 1), backend.2)), noise.cacheQuery edge value)) <$> ($ᵗ HashOutput) := by
  cases hp : backend.1.1.data.pending p with
  | some answer => simp only [chainNoiseRawPending, hp, simulateQ_pure, StateT.run_pure]
  | none =>
      simp only [chainNoiseRawPending, hp, HasQuery.instOfMonadLift_query, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_pure, StateT.run_bind, StateT.run_pure,
        SigningGuessProof.privateRoImpl, QueryImpl.add_apply_inr]
      simp only [bind_pure_comp]
      erw [QueryImpl.withCaching_run_none _ (hfresh hp), Functor.map_map]

/-- The actual capped wrapper never deletes visible pending entries. -/
theorem cappedCompiler_pending_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))
    (p : PendingInput) (hp : backend.1.1.data.pending p ≠ none) :
    r.2.1.1.data.pending p ≠ none := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_pending_mono P seeds t backend.1.1 b hb p hp
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      exact hp

/-- The private noise cache can remain in place across any original step. -/
theorem ChainNoiseInv.actual_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache) (backend : CappedCompilerState C)
    (h : ChainNoiseInv noise backend)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
    ChainNoiseInv noise r.2 := by
  intro edge he
  apply h edge
  by_contra hn
  exact cappedCompiler_pending_mono P seeds q s t backend r hr (chainPending edge) hn he

/-- Fresh private chain draws are recorded in the same visible pending domain.
This invariant concerns only visited coordinates; no full table is exposed. -/
theorem chainNoiseRawPending_inv (edge : ChainNoiseIndex)
    (backend : CappedCompilerState C) (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache)
    (h : ChainNoiseInv noise backend)
    (r : (DeferredOutput × CappedCompilerState C) × (ChainNoiseIndex →ₒ HashOutput).QueryCache)
    (hr : r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (chainNoiseRawPending (chainPending edge) edge backend)).run noise)) :
    ChainNoiseInv r.2 r.1.2 := by
  rw [chainNoiseRawPending_run (chainPending edge) edge backend noise (h edge)] at hr
  cases hp : backend.1.1.data.pending (chainPending edge) with
  | some answer =>
      simp only [hp, mem_support_pure_iff] at hr
      subst r
      exact h
  | none =>
      simp only [hp, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      intro other ho
      by_cases he : other = edge
      · subst other
        simp only [Function.update_self] at ho
        cases ho
      · have hne : chainPending other ≠ chainPending edge :=
          fun heq => he (chainPending_injective heq)
        change (noise.cacheQuery edge value) other = none
        rw [QueryCache.cacheQuery_of_ne _ _ he]
        apply h other
        simpa only [Function.update_of_ne hne] using ho

set_option backward.isDefEq.respectTransparency false in
/-- One reified compiler step has exactly the actual step's full visible
result, and keeps its private draw history inside the online pending domain. -/
theorem cappedChainNoiseRaw_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C) (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache)
    (h : ChainNoiseInv noise backend) :
    (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        ((cappedChainNoiseRaw P seeds q s t).run backend)).run noise =
      ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) ∧
    (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      ((cappedChainNoiseRaw P seeds q s t).run backend)).run noise), ChainNoiseInv r.2 r.1.2) := by
  have ordinary (t : DeferredQuery C ⊕ HiddenKey) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
          (liftM ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
            (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))).run noise =
        ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
        (liftM ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))).run noise),
        ChainNoiseInv r.2 r.1.2) := by
    rw [SigningGuessProof.privateRoImpl, roSim.run_liftM]
    constructor
    · simp only [Functor.map_map, id_map']
    · intro r hr
      simp only [support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact h.actual_step P seeds q s t noise backend a ha
  have pending (edge : ChainNoiseIndex) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (chainNoiseRawPending (chainPending edge) edge backend)).run noise =
        ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
          (.inl (.pending (chainPending edge)))).run backend)) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
        (chainNoiseRawPending (chainPending edge) edge backend)).run noise), ChainNoiseInv r.2 r.1.2) := by
    constructor
    · rw [chainNoiseRawPending_run _ edge backend noise (h edge), cappedCompiler_pending_run]
      cases hp : backend.1.1.data.pending (chainPending edge) with
      | none => simp only [Functor.map_map]
      | some value => simp only [map_pure]
    · exact fun r hr => chainNoiseRawPending_inv edge backend noise h r hr
  cases t with
  | inr key => exact ordinary (.inr key)
  | inl t =>
      cases t with
      | pending p =>
          cases p with
          | bottom e l p => exact pending (l, .inl e, p)
          | top b l p => exact pending (l, .inr b, p)
          | commitment e => exact ordinary (.inl (.pending (.commitment e)))
          | base lay e message => exact ordinary (.inl (.pending (.base lay e message)))
      | hash query => exact ordinary (.inl (.hash query))
      | virtual term point => exact ordinary (.inl (.virtual term point))
      | pad point => exact ordinary (.inl (.pad point))
      | inspect p => exact ordinary (.inl (.inspect p))
      | plant input value => exact ordinary (.inl (.plant input value))
      | snapshot => exact ordinary (.inl .snapshot)
      | sample => exact ordinary (.inl .sample)
      | record p value => exact ordinary (.inl (.record p value))
      | uniform n => exact ordinary (.inl (.uniform n))
      | bindKey e message => exact ordinary (.inl (.bindKey e message))

/-- Exact reification of an arbitrary program of the fixed compiler. Every
source-owned field and every capped-backend field remains in the result. -/
theorem cappedChainNoiseRaw_simulate (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (backend : CappedCompilerState C) (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache)
    (h : ChainNoiseInv noise backend) :
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        ((simulateQ (cappedChainNoiseRaw P seeds q s) oa).run backend)).run noise =
      (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
        oa).run backend := by
  induction oa using OracleComp.inductionOn generalizing backend noise with
  | pure value => simp
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      have step := cappedChainNoiseRaw_step P seeds q s t backend noise h
      calc
        _ = (simulateQ SigningGuessProof.privateRoImpl
            ((cappedChainNoiseRaw P seeds q s t).run backend)).run noise >>= fun r =>
          (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
            (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
            (next r.1.1)).run r.1.2 := by
          apply OracleComp.bind_congr_of_forall_mem_support
          intro r hr
          exact ih r.1.1 r.1.2 r.2 (step.2 r hr)
        _ = _ := by
          conv_rhs => rw [← step.1]
          simp only [bind_map_left]

/-- The exact fixed compiler source, reified over a private chain-noise oracle.
The private oracle's cache is absent from the result available to the source. -/
def chainNoiseRawProgram (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) : OracleComp ChainNoiseSpec (CompilerOutcome C) :=
  (simulateQ (cappedChainNoiseRaw x.1 x.2.1 q s) (sourceProgram prims A x)).run
    ((compilerInit, 0), fun _ => none, false)

/-- Full actual compiler reification, with the same secret table and the same
source program. No pending entry is pre-populated in its visible backend. -/
theorem compilerRun_eq_chainNoiseRaw (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) :
    compilerRun prims A x q = (do
      let s ← $ᵗ (HiddenKey → Digest)
      Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (chainNoiseRawProgram prims A x q s)).run ∅) := by
  unfold compilerRun
  apply bind_congr
  intro s
  exact (cappedChainNoiseRaw_simulate x.1 x.2.1 q s (sourceProgram prims A x)
    ((compilerInit, 0), fun _ => none, false) ∅ (fun _ _ => rfl)).symm

/-- Private chain precomputation changes no actual compiler observation. The
visible pending map, visible cache, trace, flag, and count remain source-owned. -/
theorem compilerRun_eq_private_chain_prefix (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) {α : Type} (ghost : OracleComp (ChainNoiseIndex →ₒ HashOutput) α) :
    𝒟[compilerRun prims A x q] = 𝒟[do
      let s ← $ᵗ (HiddenKey → Digest)
      Prod.fst <$> (do
        let _ ← simulateQ (ChainNoiseIndex →ₒ HashOutput).randomOracle ghost
        simulateQ SigningGuessProof.privateRoImpl (chainNoiseRawProgram prims A x q s)).run ∅] := by
  rw [compilerRun_eq_chainNoiseRaw]
  apply evalDist_bind_congr
  intro s _
  exact (SigningGuessProof.randomOracle_private_prefix_private ghost
    (chainNoiseRawProgram prims A x q s) ∅).symm

/-- Resolve a private chain table while forwarding private uniform draws. -/
def resolveChainNoise (table : ChainNoiseIndex → HashOutput) :
    QueryImpl ChainNoiseSpec ProbComp
  | .inl n => query (spec := unifSpec) n
  | .inr edge => pure (table edge)

/-- Coordinate resampling preserves the law of any subsequent private program. -/
theorem chainNoise_update_bind {α : Type} (edge : ChainNoiseIndex)
    (next : (ChainNoiseIndex → HashOutput) → ProbComp α) :
    𝒟[do
      let value ← $ᵗ HashOutput
      let table ← $ᵗ (ChainNoiseIndex → HashOutput)
      next (Function.update table edge value)] =
    𝒟[($ᵗ (ChainNoiseIndex → HashOutput)) >>= next] := by
  have h := congrArg (fun d => d >>= fun table => 𝒟[next table])
    (evalDist_uniformSample_bind_update (D := ChainNoiseIndex) (R := HashOutput) edge)
  simpa only [← evalDist_bind, bind_assoc, pure_bind] using h

set_option backward.isDefEq.respectTransparency false in
/-- Eagerly sampling the finite chain-noise table preserves the entire raw
source result. The table is private; its reads do not populate visible state. -/
theorem privateChainNoise_eq_table {α : Type} (oa : OracleComp ChainNoiseSpec α)
    (noise : (ChainNoiseIndex →ₒ HashOutput).QueryCache) :
    𝒟[Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl oa).run noise] =
    𝒟[do
      let table ← $ᵗ (ChainNoiseIndex → HashOutput)
      simulateQ (resolveChainNoise (tableExtending noise table)) oa] := by
  classical
  induction oa using OracleComp.inductionOn generalizing noise with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ (ChainNoiseIndex → HashOutput)) (by simp) (pure value)).symm
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      cases t with
      | inl n =>
          have hu : (SigningGuessProof.privateRoImpl (D := ChainNoiseIndex)
              (R := HashOutput) (.inl n)).run noise =
              (fun value => (value, noise)) <$>
                (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := rfl
          rw [hu, bind_map_left]
          simp only [resolveChainNoise]
          calc
            _ = 𝒟[do
              let value ← (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
              let table ← $ᵗ (ChainNoiseIndex → HashOutput)
              simulateQ (resolveChainNoise (tableExtending noise table)) (next value)] := by
                apply evalDist_bind_congr
                intro value _
                exact ih value noise
            _ = _ := OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
      | inr edge =>
          change 𝒟[((ChainNoiseIndex →ₒ HashOutput).randomOracle edge).run noise >>= fun r =>
            Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl (next r.1)).run r.2] = _
          simp only [resolveChainNoise, pure_bind]
          cases hn : noise edge with
          | some value =>
              rw [QueryImpl.withCaching_run_some _ hn, pure_bind, ih value noise]
              apply evalDist_bind_congr
              intro table _
              simp only [tableExtending, hn, Option.getD_some]
          | none =>
              rw [QueryImpl.withCaching_run_none _ hn, bind_map_left]
              let replay : (ChainNoiseIndex → HashOutput) → ProbComp α := fun table =>
                simulateQ (resolveChainNoise (tableExtending noise table))
                  (next (tableExtending noise table edge))
              calc
                _ = 𝒟[do
                    let value ← $ᵗ HashOutput
                    let table ← $ᵗ (ChainNoiseIndex → HashOutput)
                    replay (Function.update table edge value)] := by
                  apply evalDist_bind_congr
                  intro value _
                  rw [ih value (noise.cacheQuery edge value)]
                  apply evalDist_bind_congr
                  intro table _
                  dsimp only [replay]
                  rw [tableExtending_cacheQuery,
                    ← tableExtending_update_of_none noise table hn value]
                  simp only [Function.update_self]
                _ = _ := chainNoise_update_bind edge replay

/-- The actual compiler with one independent private chain-noise table. All
source and backend observations are retained, including the original counter. -/
theorem compilerRun_eq_chainNoiseTable (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) :
    𝒟[compilerRun prims A x q] = 𝒟[do
      let s ← $ᵗ (HiddenKey → Digest)
      let table ← $ᵗ (ChainNoiseIndex → HashOutput)
      simulateQ (resolveChainNoise table) (chainNoiseRawProgram prims A x q s)] := by
  rw [compilerRun_eq_chainNoiseRaw]
  apply evalDist_bind_congr
  intro s _
  simpa only [tableExtending_empty] using
    privateChainNoise_eq_table (chainNoiseRawProgram prims A x q s) ∅

/-- A PRF point whose complete concrete term sum has its required value. -/
def PointDone (seeds : C.Term → HashOutput) (data : DeferredState C)
    (point : Point) (target : Digest) : Prop :=
  (∀ T : C.Term, ∃ value, data.cache (.prf (seeds T) point) = some value) ∧
    termSum (cachedTerm seeds data point) = target

/-- Terms held by no corrupt party have not been materialized at this point. -/
def LackedUncached (seeds : C.Term → HashOutput) (D : Finset C.Party)
    (data : DeferredState C) (point : Point) : Prop :=
  ∀ T : C.Term, ¬TprfSecurityProof.Revealed D (.inl T) →
    data.cache (.prf (seeds T) point) = none

/-- The bottom-chain target uses its public pad exactly at positive positions. -/
def bottomReleaseTarget (s : HiddenKey → Digest) (data : DeferredState C)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) : Digest :=
  s (.bottomChain e l pos) ^^^
    if pos.val = 0 then 0 else
      (data.pads (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))).getD 0

/-- Stable-boundary invariant for the fixed P/Q/R release schedule. Each
uncompleted point retains either all lacked terms or a concrete unready term. -/
structure ReleaseSlack (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (source : SourceState C) (data : DeferredState C) : Prop where
  corrupt_bound : source.signing.corrupt.card ≤ C.t - 1
  bottom_opening : ∀ e,
    PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
    (source.signing.bound e = none ∧
      LackedUncached seeds source.signing.corrupt data (.randomizer bottomLayer e)) ∨
    (source.signing.bound e ≠ none ∧ ∃ T : C.Term,
      (T, Point.randomizer bottomLayer e) ∉ data.virtual ∧
        data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none)
  bottom_chain : ∀ e l pos,
    ((pos.val = 0 ∨ data.pads
        (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)) ≠ none) ∧
      PointDone seeds data (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
        (bottomReleaseTarget s data e l pos)) ∨
    LackedUncached seeds source.signing.corrupt data
      (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
  top_opening : ∀ b,
    PointDone seeds data (.randomizer topLayer (topKey b)) (s (.opening topLayer (topKey b))) ∨
    LackedUncached seeds source.signing.corrupt data (.randomizer topLayer (topKey b))
  top_start : ∀ b l,
    PointDone seeds data (.chain topLayer (topKey b) l (digit 0))
      (s (.topChain b l ⟨0, by decide⟩)) ∨
    LackedUncached seeds source.signing.corrupt data (.chain topLayer (topKey b) l (digit 0))
  bottom_released : ∀ e, source.revealed (.opening bottomLayer e) ≠ none →
    PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e))

/-- The empty source and backend satisfy every release-slack clause. -/
theorem releaseSlack_initial (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) :
    ReleaseSlack (C := C) seeds s sourceInit deferredInit := by
  refine ⟨by simp [sourceInit, SigningCoreProof.tsigInit], ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact Or.inr (Or.inl ⟨rfl, fun _ _ => rfl⟩)
  · intro e l pos
    exact Or.inr (fun _ _ => rfl)
  · intro b
    exact Or.inr (fun _ _ => rfl)
  · intro b l
    exact Or.inr (fun _ _ => rfl)
  · intro e h
    exact (h rfl).elim

/-- The threshold corruption guard leaves at least one lacked term. -/
theorem exists_lacked_term (D : Finset C.Party) (hD : D.card ≤ C.t - 1) :
    ∃ T : C.Term, ¬TprfSecurityProof.Revealed D (.inl T) := by
  obtain ⟨T, hT⟩ := prawns_coalition_lacks_term (C := C) ⟨D, hD⟩
  refine ⟨T, ?_⟩
  rintro ⟨i, hi, hhold⟩
  exact hT i hi hhold

/-- Enlarging the corrupt set can only remove lacked terms. -/
theorem LackedUncached.corrupt_mono {seeds : C.Term → HashOutput}
    {D E : Finset C.Party} {data : DeferredState C} {point : Point}
    (h : LackedUncached seeds D data point) (hDE : D ⊆ E) :
    LackedUncached seeds E data point := by
  intro T hT
  apply h T
  rintro ⟨i, hi, hh⟩
  exact hT ⟨i, hDE hi, hh⟩

/-- Adaptive corruption preserves the release-slack alternatives whenever
its actual guard permits the enlarged corrupt set. -/
theorem ReleaseSlack.corrupt_mono {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (D : Finset C.Party)
    (hD : source.signing.corrupt ⊆ D) (hcard : D.card ≤ C.t - 1) :
    ReleaseSlack seeds s { source with signing := { source.signing with corrupt := D } } data := by
  refine ⟨hcard, ?_, ?_, ?_, ?_, h.bottom_released⟩
  · intro e
    rcases h.bottom_opening e with hd | ⟨hb, hu⟩ | ⟨hb, hm⟩
    · exact Or.inl hd
    · exact Or.inr (Or.inl ⟨hb, hu.corrupt_mono hD⟩)
    · exact Or.inr (Or.inr ⟨hb, hm⟩)
  · intro e l pos
    exact (h.bottom_chain e l pos).imp id (fun hu => hu.corrupt_mono hD)
  · intro b
    exact (h.top_opening b).imp id (fun hu => hu.corrupt_mono hD)
  · intro b l
    exact (h.top_start b l).imp id (fun hu => hu.corrupt_mono hD)

/-- One absent term is precisely enough to rule out the no-slack branch. -/
theorem firstUnmaterialized_ne_none_of_missing (seeds : C.Term → HashOutput)
    (data : DeferredState C) (point : Point) (T : C.Term)
    (hT : data.cache (.prf (seeds T) point) = none) :
    firstUnmaterialized seeds data point ≠ none := by
  intro hf
  obtain ⟨value, hv⟩ := (firstUnmaterialized_none_iff seeds data point).mp hf T
  rw [hT] at hv
  cases hv

theorem LackedUncached.missing {seeds : C.Term → HashOutput} {D : Finset C.Party}
    {data : DeferredState C} {point : Point} (h : LackedUncached seeds D data point)
    (hD : D.card ≤ C.t - 1) : firstUnmaterialized seeds data point ≠ none := by
  obtain ⟨T, hT⟩ := exists_lacked_term D hD
  exact firstUnmaterialized_ne_none_of_missing seeds data point T (h T hT)

/-- P's stable-boundary alternatives supply either its finished constraint
or an actual missing concrete PRF entry. -/
theorem ReleaseSlack.bottom_opening_admissible {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex) :
    PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
      firstUnmaterialized seeds data (.randomizer bottomLayer e) ≠ none := by
  rcases h.bottom_opening e with hd | ⟨_, hu⟩ | ⟨_, T, _, hT⟩
  · exact Or.inl hd
  · exact Or.inr (hu.missing h.corrupt_bound)
  · exact Or.inr (firstUnmaterialized_ne_none_of_missing seeds data _ T hT)

/-- A complete constraint survives every conservative concrete cache extension. -/
theorem PointDone.mono {seeds : C.Term → HashOutput} {before after : DeferredState C}
    {point : Point} {target : Digest} (h : PointDone seeds before point target)
    (hle : before.cache ≤ after.cache) : PointDone seeds after point target := by
  refine ⟨fun T => ?_, ?_⟩
  · obtain ⟨value, hv⟩ := h.1 T
    exact ⟨value, hle hv⟩
  · have he : cachedTerm seeds after point = cachedTerm seeds before point := by
      funext T
      obtain ⟨value, hv⟩ := h.1 T
      simp only [cachedTerm, hv, hle hv]
    rw [he]
    exact h.2

set_option backward.isDefEq.respectTransparency false in
/-- At a release boundary, either a finished point or a missing term makes
the actual completion report success and establish its exact target. -/
theorem completePrf_done_or_missing (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (point : Point) (target : Digest) (source : SourceState C) (backend : CappedCompilerState C)
    (h : PointDone seeds backend.1.1.data point target ∨
      firstUnmaterialized seeds backend.1.1.data point ≠ none)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (completePrf seeds point target)) source backend)) :
    r.1.1 = true ∧ PointDone seeds r.2.1.1.data point target := by
  have hc := completePrf_correct P seeds hinj q s point target source backend r hr
  suffices ht : r.1.1 = true from ⟨ht, hc.1, hc.2.1.mp ht⟩
  rcases h with hd | hm
  · have hf := (firstUnmaterialized_none_iff seeds backend.1.1.data point).mpr hd.1
    simp only [completePrf, liftM_bind, runSource_bind, runSource_snapshot,
      mem_support_bind_iff] at hr
    obtain ⟨_, rfl, hr⟩ := hr
    simp only [hf, liftM_pure, runSource_pure, mem_support_pure_iff] at hr
    subst r
    simpa only [decide_eq_true_eq] using hd.2
  · exact hc.2.2 hm

/-- The only deferred calls capable of changing one concrete PRF cache entry. -/
def WritesPrf (seed : HashOutput) (point : Point) : DeferredQuery C → Prop
  | .hash query => query = .prf seed point
  | .plant input _ => input.query (C := C) = .prf seed point
  | _ => False

/-- Deferred backend calls frame every PRF entry they do not address. Pending
plants address the hash domain and therefore cannot change a PRF entry. -/
theorem deferredImpl_prf_frame (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) (seed : HashOutput) (point : Point)
    (ht : ¬WritesPrf seed point t) :
    r.2.cache (.prf seed point) = st.cache (.prf seed point) := by
  cases t with
  | hash query =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact (randomOracle_support query st.cache a ha).2.2 (.prf seed point) (Ne.symm (show query ≠ .prf seed point from ht))
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl
  | pad p =>
      cases hk : st.pads p with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl
  | plant input value =>
      cases hc : st.cache input.query with
      | some prior =>
          simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr
          subst r
          exact QueryCache.cacheQuery_of_ne _ _
            (Ne.symm (show input.query (C := C) ≠ .prf seed point from ht))
  | sample =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | virtual term p =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | inspect p =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | snapshot =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | record p value =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | bindKey e message =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual cached-extra grind adds only trial hashes, so the full compiler
has the same exact PRF frame as its deferred backend. -/
theorem compilerImpl_prf_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) (seed : HashOutput) (point : Point)
    (ht : ¬WritesPrf seed point t) :
    r.2.data.cache (.prf seed point) = st.data.cache (.prf seed point) := by
  cases t with
  | hash query =>
      obtain ⟨a, ha, b, hb, rfl⟩ := SigningCompilerPotential.compiler_hash_support
        P seeds query st r hr
      have frame := SigningReleasedTransferProof.cachedExtra_frame seeds P
        (((st.data.cache, 0), []), compilerSigning st, false)
        (.inr (.inr (.inl query)))
        (((a.2.cache, 0), []), compilerSigning st, false) b (by
          dsimp only [StateT.run] at hb ⊢
          with_reducible exact hb)
      exact (frame.2 (.prf seed point)
        (SigningPartnerCompareProof.outsideTrials_prf P seed point)).trans
          (deferredImpl_prf_frame (.hash query) st.data a ha seed point ht)
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_prf_frame _ st.data a ha seed point ht

def SourceWritesPrf (seed : HashOutput) (point : Point) : DeferredQuery C ⊕ HiddenKey → Prop
  | .inl t => WritesPrf seed point t
  | .inr _ => False

/-- Reveals and counter updates preserve the same concrete PRF cache frame. -/
theorem cappedCompiler_prf_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))
    (seed : HashOutput) (point : Point) (ht : ¬SourceWritesPrf seed point t) :
    r.2.1.1.data.cache (.prf seed point) = backend.1.1.data.cache (.prf seed point) := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_prf_frame P seeds t backend.1.1 b hb seed point ht
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      rfl

/-- A source read of a lacked seed is exactly one of the original hidden-key hits. -/
theorem hiddenHit_lacked_prf (x : Keys3 C) (D : Finset C.Party) (T : C.Term) (point : Point)
    (hT : ¬TprfSecurityProof.Revealed D (.inl T)) :
    SigningCoreProof.hiddenHit x D (.inr (.inl (.prf (x.2.1 T) point))) = true := by
  simp only [SigningCoreProof.hiddenHit, decide_eq_true_eq]
  exact ⟨T, rfl, hT⟩

theorem runSource_get (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s get source backend = pure ((source, source), backend) := by
  simp only [runSource, StateT.run_get, simulateQ_pure, StateT.run_pure]

set_option backward.isDefEq.respectTransparency false in
/-- The original hidden-key flag is updated at the actual adversary-call
boundary, after all of that call's release/cache bookkeeping. -/
theorem sourceOracles_local_hiddenFlag (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (t : (LocalSpec C).Domain)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : ((LocalSpec C t) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceOracles prims x top (.inl t)) source backend)) :
    r.1.2.hiddenFlag = (source.hiddenFlag || SigningCoreProof.hiddenHit x source.signing.corrupt t) := by
  simp only [sourceOracles, runSource_bind, runSource_get, mem_support_bind_iff,
    mem_support_pure_iff] at hr
  obtain ⟨_, rfl, a, ha, b, hb, hr⟩ := hr
  rw [runSource_modify, mem_support_pure_iff] at hb
  subst b
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  rfl

/-- A supported adversary PRF read on a lacked term cannot finish with the
source hidden-key flag down. This uses the original flag, not the capped flag. -/
theorem sourceOracles_lacked_prf_flag (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (T : C.Term) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hT : ¬TprfSecurityProof.Revealed source.signing.corrupt (.inl T))
    (r : (LocalSpec C (.inr (.inl (.prf (x.2.1 T) point))) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s
      (sourceOracles prims x top (.inl (.inr (.inl (.prf (x.2.1 T) point))))) source backend)) :
    r.1.2.hiddenFlag = true := by
  rw [sourceOracles_local_hiddenFlag prims x top q s (.inr (.inl (.prf (x.2.1 T) point))) source backend r hr,
    hiddenHit_lacked_prf x source.signing.corrupt T point hT, Bool.or_true]

set_option backward.isDefEq.respectTransparency false in
/-- The actual corruption branch is a guarded source-state update, with no
backend call or random-oracle effect. -/
theorem runSource_corrupt (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (i : C.Party)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource x.1 x.2.1 q s (sourceTsig prims x top (.corrupt i)) source backend =
    if C.t - 1 < (insert i source.signing.corrupt).card then
      pure ((none, source), backend)
    else pure ((some (dealtKeys x.1 x.2.1 x.2.2 i),
      { source with signing := { source.signing with corrupt := insert i source.signing.corrupt } }), backend) := by
  simp only [sourceTsig, runSource_bind, runSource_get, pure_bind]
  split <;> simp only [runSource_bind, runSource_modify, runSource_pure, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- The release-slack invariant survives each accepted or rejected adaptive
corruption call of the actual signing source. -/
theorem releaseSlack_corrupt (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (i : C.Party)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseSlack x.2.1 s source backend.1.1.data)
    (r : (TsigSpec C (.corrupt i) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceTsig prims x top (.corrupt i)) source backend)) :
    ReleaseSlack x.2.1 s r.1.2 r.2.1.1.data := by
  rw [runSource_corrupt] at hr
  split at hr
  · simp only [mem_support_pure_iff] at hr
    subst r
    exact h
  · rename_i hcard
    simp only [mem_support_pure_iff] at hr
    subst r
    exact h.corrupt_mono _ (Finset.subset_insert _ _) (Nat.le_of_not_gt hcard)

/-- Equal concrete term entries give the same complete-point constraint. -/
theorem PointDone.of_cache_eq {seeds : C.Term → HashOutput} {a b : DeferredState C}
    {point : Point} {target : Digest} (h : PointDone seeds a point target)
    (he : ∀ T, b.cache (.prf (seeds T) point) = a.cache (.prf (seeds T) point)) :
    PointDone seeds b point target := by
  refine ⟨fun T => ?_, ?_⟩
  · simpa only [he T] using h.1 T
  · have hc : cachedTerm seeds b point = cachedTerm seeds a point := by
      funext T
      simp only [cachedTerm, he T]
    rw [hc]
    exact h.2

/-- Release slack depends only on the concrete PRF entries, pads, virtual
entries, binding map, coalition and bottom-opening reveal status. -/
theorem ReleaseSlack.frame {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source source' : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlack seeds s source data)
    (hs : source'.signing = source.signing)
    (hc : ∀ seed point, data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads)
    (hr : ∀ e, source'.revealed (.opening bottomLayer e) ≠ none →
      source.revealed (.opening bottomLayer e) ≠ none) :
    ReleaseSlack seeds s source' data' := by
  have hu : ∀ point, LackedUncached seeds source.signing.corrupt data point →
      LackedUncached seeds source'.signing.corrupt data' point := by
    intro point hh T hT
    rw [hc]
    exact hh T (hs ▸ hT)
  have hd : ∀ point target, PointDone seeds data point target →
      PointDone seeds data' point target := fun _ _ hh => hh.of_cache_eq (fun T => hc _ _)
  refine ⟨hs ▸ h.corrupt_bound, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases h.bottom_opening e with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
    · exact Or.inl (hd _ _ hh)
    · exact Or.inr (Or.inl ⟨hs ▸ hb, hu _ hh⟩)
    · exact Or.inr (Or.inr ⟨hs ▸ hb, T, hv ▸ ht, (hc _ _).trans hh⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with ⟨hh, hk⟩ | hh
    · refine Or.inl ⟨?_, ?_⟩
      · simpa only [hp] using hh
      · simpa only [bottomReleaseTarget, hp] using hd _ _ hk
    · exact Or.inr (hu _ hh)
  · intro b
    exact (h.top_opening b).imp (hd _ _) (hu _)
  · intro b l
    exact (h.top_start b l).imp (hd _ _) (hu _)
  · intro e he
    exact hd _ _ (h.bottom_released e (hr e he))

set_option backward.isDefEq.respectTransparency false in
/-- Completion changes only the concrete cache at the selected PRF point.
It preserves the entire source and the other backend fields, including pads,
virtual entries, visible trace, reveals, count and flag. -/
theorem completePrf_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (completePrf seeds point target)) source backend)) :
    r.1.2 = source ∧ r.2 = replaceCompilerCache backend r.2.1.1.data.cache ∧
      backend.1.1.data.cache ≤ r.2.1.1.data.cache ∧
      ∀ seed other, other ≠ point →
        r.2.1.1.data.cache (.prf seed other) = backend.1.1.data.cache (.prf seed other) := by
  cases hf : firstUnmaterialized seeds backend.1.1.data point with
  | none =>
      simp only [completePrf, liftM_bind, runSource_bind, runSource_snapshot,
        mem_support_bind_iff] at hr
      obtain ⟨_, rfl, hr⟩ := hr
      simp only [hf, liftM_pure, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨rfl, rfl, le_rfl, fun _ _ _ => rfl⟩
  | some slack =>
      rw [runSource_completePrf_slack P seeds q s point slack target source backend hf] at hr
      simp only [runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨filled, hfilled, sampled, hsampled, hr⟩ := hr
      have hfill := fillTerms_cache P seeds q s point
        (C.terms.filter (· ≠ slack)) source backend filled hfilled
      rw [runSource_fillTerms_randomOracle] at hfilled
      simp only [support_map] at hfilled
      obtain ⟨a, _, rfl⟩ := hfilled
      rw [runSource_sample] at hsampled
      simp only [support_map] at hsampled
      obtain ⟨high, _, rfl⟩ := hsampled
      rw [runSource_plant] at hr
      simp only [support_map] at hr
      obtain ⟨planted, hplanted, rfl⟩ := hr
      have hle := deferredImpl_cache_le
        (.plant (.prf (seeds slack) point) _) (replaceCompilerCache backend a.2).1.1.data
        planted hplanted
      have hframe : ∀ seed other, other ≠ point →
          planted.2.cache (.prf seed other) = a.2 (.prf seed other) := by
        intro seed other hne
        apply deferredImpl_prf_frame _ _ planted hplanted
        change Query.prf (C := C) (seeds slack) point ≠ .prf seed other
        intro he
        exact hne (Query.prf.inj he).2.symm
      have hdata : planted.2 =
          { (replaceCompilerCache backend a.2).1.1.data with cache := planted.2.cache } := by
        cases hh : a.2 (.prf (seeds slack) point) with
        | none =>
            simp only [deferredImpl, StateT.run, PlantInput.query,
              replaceCompilerCache, hh, mem_support_pure_iff] at hplanted
            subst planted
            rfl
        | some value =>
            simp only [deferredImpl, StateT.run, PlantInput.query,
              replaceCompilerCache, hh, mem_support_pure_iff] at hplanted
            subst planted
            rfl
      refine ⟨rfl, ?_, hfill.1.trans hle, ?_⟩
      · have hh := congrArg (fun d : DeferredState C =>
          (({ backend.1.1 with data := d }, backend.1.2), backend.2)) hdata
        exact hh
      · intro seed other hne
        exact (hframe seed other hne).trans (hfill.2.2 (.prf seed other) (by
          intro T _ he
          exact hne (Query.prf.inj he).2))

/-- Completion at one bottom randomizer preserves every other release clause
and establishes P's exact target, including the newly revealed opening. -/
theorem ReleaseSlack.complete_bottom {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source source' : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex)
    (hs : source'.signing = source.signing)
    (hc : ∀ seed point, point ≠ .randomizer bottomLayer e →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : ∀ f, f ≠ e → ∀ T : C.Term,
      ((T, Point.randomizer bottomLayer f) ∈ data'.virtual ↔
        (T, Point.randomizer bottomLayer f) ∈ data.virtual))
    (hp : data'.pads = data.pads)
    (hr : ∀ f, f ≠ e → source'.revealed (.opening bottomLayer f) ≠ none →
      source.revealed (.opening bottomLayer f) ≠ none)
    (hd : PointDone seeds data' (.randomizer bottomLayer e) (s (.opening bottomLayer e))) :
    ReleaseSlack seeds s source' data' := by
  have done : ∀ point target, point ≠ .randomizer bottomLayer e →
      PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hn hh => hh.of_cache_eq (fun T => hc _ _ hn)
  have uncache : ∀ point, point ≠ .randomizer bottomLayer e →
      LackedUncached seeds source.signing.corrupt data point →
        LackedUncached seeds source'.signing.corrupt data' point := by
    intro point hn hh T hT
    rw [hc _ _ hn]
    exact hh T (hs ▸ hT)
  refine ⟨hs ▸ h.corrupt_bound, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    by_cases he : f = e
    · subst f
      exact Or.inl hd
    · have hn : Point.randomizer bottomLayer f ≠ .randomizer bottomLayer e := by simpa
      rcases h.bottom_opening f with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
      · exact Or.inl (done _ _ hn hh)
      · exact Or.inr (Or.inl ⟨hs ▸ hb, uncache _ hn hh⟩)
      · exact Or.inr (Or.inr ⟨hs ▸ hb, T, (hv f he T).not.mpr ht, (hc _ _ hn).trans hh⟩)
  · intro f l pos
    rcases h.bottom_chain f l pos with ⟨hh, hk⟩ | hh
    · refine Or.inl ⟨?_, ?_⟩
      · simpa only [hp] using hh
      · simpa only [bottomReleaseTarget, hp] using done _ _ (by simp) hk
    · exact Or.inr (uncache _ (by simp) hh)
  · intro b
    have hn : Point.randomizer topLayer (topKey b) ≠ .randomizer bottomLayer e := by
      simp [topLayer, bottomLayer]
    exact (h.top_opening b).imp (done _ _ hn) (uncache _ hn)
  · intro b l
    exact (h.top_start b l).imp (done _ _ (by simp)) (uncache _ (by simp))
  · intro f hf
    by_cases he : f = e
    · subst f
      exact hd
    · exact done _ _ (by simpa) (h.bottom_released f (hr f he hf))

/-- An opening-key pending point is terminal: its low half is public. -/
theorem PendingInput.next_none_of_opening (p : PendingInput) (lay : Layer) (e : KeyIndex)
    (h : p.key = .opening lay e) : p.next = none := by
  cases p <;> simp_all [PendingInput.key, PendingInput.next]

set_option backward.isDefEq.respectTransparency false in
/-- Planting a terminal point whose input is already revealed introduces no
new reveal. Only its hash entry and the consistency bit can change. -/
theorem sourcePlant_terminal_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hp : p.next = none) (hv : PendingValid backend.1.1.data)
    (hk : source.revealed p.key ≠ none)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    r.1.2 = { source with consistent := r.1.2.consistent } ∧
      r.2 = replaceCompilerCache backend r.2.1.1.data.cache ∧
      ∀ seed point, r.2.1.1.data.cache (.prf seed point) =
        backend.1.1.data.cache (.prf seed point) := by
  simp only [sourcePlant, runSource_bind, runSource_inspect, mem_support_bind_iff] at hr
  obtain ⟨_, rfl, hr⟩ := hr
  cases ha : backend.1.1.data.pending p with
  | none =>
      simp only [ha, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | some answer =>
      obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hk
      rcases hv p answer ha with ⟨key, hn, _⟩ | ⟨_, low, hlow⟩
      · rw [hp] at hn
        cases hn
      · simp only [ha, runSource_bind, runSource_sourceReveal_cached P seeds q s p.key
          source backend value hvalue, pure_bind, sourceRevealDigest, hlow] at hr
        simp only [mem_support_bind_iff] at hr
        obtain ⟨planted, hplanted, hr⟩ := hr
        rw [runSource_plant] at hplanted
        simp only [support_map] at hplanted
        obtain ⟨a, ha', rfl⟩ := hplanted
        simp only [runSource_modify, mem_support_pure_iff] at hr
        subst r
        refine ⟨rfl, ?_, ?_⟩
        · cases hc : backend.1.1.data.cache (PlantInput.pending P p value).query with
          | none =>
              simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at ha'
              subst a
              rfl
          | some prior =>
              simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at ha'
              subst a
              rfl
        · intro seed point
          apply deferredImpl_prf_frame _ _ a ha'
          simp [WritesPrf, PlantInput.query]

/-- The terminal planting suffix preserves all release slack, including its
revealed-opening clause, even if the planted hash conflicts with a prior query. -/
theorem sourcePlant_terminal_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hp : p.next = none) (hv : PendingValid backend.1.1.data)
    (hk : source.revealed p.key ≠ none)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      PendingValid r.2.1.1.data ∧ r.1.2.revealed = source.revealed := by
  obtain ⟨hsource, hbackend, hcache⟩ := sourcePlant_terminal_frame
    P seeds q s p source backend hp hv hk r hr
  have hsign : r.1.2.signing = source.signing := by
    have hh := congrArg SourceState.signing hsource
    exact hh
  have hrev : r.1.2.revealed = source.revealed := by
    have hh := congrArg SourceState.revealed hsource
    exact hh
  have hdata : r.2.1.1.data = { backend.1.1.data with cache := r.2.1.1.data.cache } :=
    congrArg (fun b : CappedCompilerState C => b.1.1.data) hbackend
  have hvirtual := congrArg DeferredState.virtual hdata
  have hpads := congrArg DeferredState.pads hdata
  have hpending := congrArg DeferredState.pending hdata
  refine ⟨hs.frame hsign hcache hvirtual hpads (fun e he => hrev ▸ he), ?_, hrev⟩
  intro key value hk'
  apply hv key value
  rw [hpending] at hk'
  exact hk'

set_option backward.isDefEq.respectTransparency false in
/-- P's whole finite terminal-planting suffix preserves release slack and
all previously recorded reveals. -/
theorem sourcePlants_terminal_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pending : List PendingInput) :
    ∀ (source : SourceState C) (backend : CappedCompilerState C),
      (∀ p ∈ pending, p.next = none ∧ source.revealed p.key ≠ none) →
      PendingValid backend.1.1.data → ReleaseSlack seeds s source backend.1.1.data →
      ∀ r : (List Unit × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (pending.mapM (sourcePlant P)) source backend) →
      ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
        PendingValid r.2.1.1.data ∧ r.1.2.revealed = source.revealed := by
  induction pending with
  | nil =>
      intro source backend _ hv hs r hr
      simp only [List.mapM_nil, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨hs, hv, rfl⟩
  | cons p pending ih =>
      intro source backend hp hv hs r hr
      simp only [List.mapM_cons, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      have hhead' := sourcePlant_terminal_slack P seeds q s p source backend
        (hp p (List.mem_cons_self ..)).1 hv (hp p (List.mem_cons_self ..)).2 hs head hhead
      have htail' := ih head.1.2 head.2 (by
        intro key hk
        obtain ⟨hn, hr⟩ := hp key (List.mem_cons_of_mem _ hk)
        exact ⟨hn, hhead'.2.2 ▸ hr⟩) hhead'.2.1 hhead'.1 tail htail
      exact ⟨htail'.1, htail'.2.1, htail'.2.2.trans hhead'.2.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual P routine preserves release slack and finishes its bottom
randomizer constraint. Its terminal plants may still record hash conflicts. -/
theorem sourceReleaseOpening_slack_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex)
    (source : SourceState C) (backend : CappedCompilerState C) (data : DeferredState C)
    (hs : ReleaseSlack seeds s source data)
    (hcache : ∀ seed point, backend.1.1.data.cache (.prf seed point) = data.cache (.prf seed point))
    (hvirt : ∀ f, f ≠ e → ∀ T : C.Term,
      ((T, Point.randomizer bottomLayer f) ∈ backend.1.1.data.virtual ↔
        (T, Point.randomizer bottomLayer f) ∈ data.virtual))
    (hpad : backend.1.1.data.pads = data.pads)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseOpening P seeds e) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) := by
  have admissible : PointDone seeds backend.1.1.data (.randomizer bottomLayer e)
      (s (.opening bottomLayer e)) ∨
      firstUnmaterialized seeds backend.1.1.data (.randomizer bottomLayer e) ≠ none := by
    rcases hs.bottom_opening_admissible e with hd | hm
    · exact Or.inl (hd.of_cache_eq (fun T => hcache _ _))
    · have hf : firstUnmaterialized seeds backend.1.1.data (.randomizer bottomLayer e) =
          firstUnmaterialized seeds data (.randomizer bottomLayer e) := by
        simp only [firstUnmaterialized, hcache]
      exact Or.inr (hf ▸ hm)
  cases hk : source.revealed (.opening bottomLayer e) with
  | some value =>
      simp only [sourceReleaseOpening, runSource_bind, runSource_get, pure_bind,
        hk, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, runSource_pure,
        mem_support_pure_iff] at hr
      subst r
      have hd := (hs.bottom_released e (by rw [hk]; exact Option.some_ne_none value)).of_cache_eq
        (fun T => hcache _ _)
      exact ⟨hs.complete_bottom e rfl (fun seed point _ => hcache seed point)
        hvirt hpad (fun _ _ he => he) hd, hd⟩
  | none =>
      have hb : backend.2.1 (.opening bottomLayer e) = none := hrev.1 ▸ hk
      simp only [sourceReleaseOpening, runSource_bind, runSource_get, pure_bind,
        hk, Option.isNone_none, ↓reduceIte,
        runSource_sourceReveal_fresh P seeds q s (.opening bottomLayer e) source backend hk,
        hb, Option.getD_none, runSource_modify, runSource_pure,
        mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨completed, hcompleted, planted, hplanted, rfl⟩ := hr
      have hc := completePrf_done_or_missing P seeds hinj q s
        (.randomizer bottomLayer e) (s (.opening bottomLayer e)) _
        (backend.1, Function.update backend.2.1 (.opening bottomLayer e)
          (some (s (.opening bottomLayer e))), backend.2.2)
        admissible completed hcompleted
      have hf := completePrf_frame P seeds q s
        (.randomizer bottomLayer e) (s (.opening bottomLayer e)) _ _ completed hcompleted
      have hdata := congrArg (fun b : CappedCompilerState C => b.1.1.data) hf.2.1
      have hpending := congrArg DeferredState.pending hdata
      have hvirtual := congrArg DeferredState.virtual hdata
      have hpads := congrArg DeferredState.pads hdata
      have hsign := congrArg SourceState.signing hf.1
      have hreveal := congrArg SourceState.revealed hf.1
      change completed.1.2.signing = source.signing at hsign
      change completed.1.2.revealed = Function.update source.revealed
        (.opening bottomLayer e) (some (s (.opening bottomLayer e))) at hreveal
      change completed.2.1.1.data.pending = backend.1.1.data.pending at hpending
      change completed.2.1.1.data.virtual = backend.1.1.data.virtual at hvirtual
      change completed.2.1.1.data.pads = backend.1.1.data.pads at hpads
      have hmid : ReleaseSlack seeds s
          { completed.1.2 with consistent := completed.1.2.consistent && completed.1.1 }
          completed.2.1.1.data := by
        apply hs.complete_bottom (source' :=
          { completed.1.2 with consistent := completed.1.2.consistent && completed.1.1 })
          e hsign (fun seed point hn => (hf.2.2.2 seed point hn).trans (hcache seed point))
          (fun f hfe T => by rw [hvirtual]; exact hvirt f hfe T)
          (hpads.trans hpad) ?_ hc.2
        intro f hfe hrf
        change completed.1.2.revealed (.opening bottomLayer f) ≠ none at hrf
        rw [hreveal, Function.update_of_ne (by simpa using hfe)] at hrf
        exact hrf
      have hvalid : PendingValid completed.2.1.1.data := by
        intro p answer hp
        apply hv p answer
        rw [hpending] at hp
        exact hp
      have hplants := sourcePlants_terminal_slack P seeds q s _ _ _ (by
        intro p hp
        have hkey : p.key = .opening bottomLayer e := of_decide_eq_true (List.mem_filter.mp hp).2
        refine ⟨PendingInput.next_none_of_opening p bottomLayer e hkey, ?_⟩
        change completed.1.2.revealed p.key ≠ none
        rw [hreveal, hkey, Function.update_self]
        exact Option.some_ne_none _) hvalid hmid planted hplanted
      refine ⟨hplants.1, hplants.1.bottom_released e ?_⟩
      rw [hplants.2.2]
      change completed.1.2.revealed (.opening bottomLayer e) ≠ none
      rw [hreveal, Function.update_self]
      exact Option.some_ne_none _

/-- P preserves release slack from an ordinary stable source boundary. -/
theorem sourceReleaseOpening_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseOpening P seeds e) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) :=
  sourceReleaseOpening_slack_frame P seeds hinj q s e source backend backend.1.1.data
    hs (fun _ _ => rfl) (fun _ _ _ => Iff.rfl) rfl hv hrev r hr

/-- A virtual term preserves every release clause unless it finishes readiness
at its own bottom randomizer. At that point P must run before the boundary. -/
theorem ReleaseSlack.virtual_unready {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (T : C.Term) (point : Point)
    (hn : ∀ e, point = .randomizer bottomLayer e →
      ¬OpeningReady seeds { data with virtual := insert (T, point) data.virtual } source.signing e) :
    ReleaseSlack seeds s source { data with virtual := insert (T, point) data.virtual } := by
  refine ⟨h.corrupt_bound, ?_, h.bottom_chain, h.top_opening, h.top_start, h.bottom_released⟩
  intro e
  rcases h.bottom_opening e with hd | ⟨hb, hu⟩ | ⟨hb, U, hv, hc⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨hb, hu⟩)
  · apply Or.inr ∘ Or.inr
    refine ⟨hb, ?_⟩
    by_cases he : point = .randomizer bottomLayer e
    · have hnot : ¬∀ V : C.Term,
          (V, Point.randomizer bottomLayer e) ∈ insert (T, point) data.virtual ∨
            (data.cache (.prf (seeds V) (.randomizer bottomLayer e))).isSome := by
        intro hall
        exact hn e he ⟨hb, hall⟩
      obtain ⟨V, hV⟩ := not_forall.mp hnot
      refine ⟨V, fun hmem => hV (Or.inl hmem), ?_⟩
      cases hh : data.cache (.prf (seeds V) (.randomizer bottomLayer e)) with
      | none => rfl
      | some value => exact (hV (Or.inr (by simp [hh]))).elim
    · refine ⟨U, ?_, hc⟩
      change (U, Point.randomizer bottomLayer e) ∉ insert (T, point) data.virtual
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun heq => he (congrArg Prod.snd heq).symm, hv⟩

/-- The last virtual term leaves the same concrete slack available to P. -/
theorem ReleaseSlack.ready_virtual_missing {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (T : C.Term) (e : KeyIndex)
    (hd : ¬PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (hr : OpeningReady seeds
      { data with virtual := insert (T, Point.randomizer bottomLayer e) data.virtual }
      source.signing e) :
    data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none := by
  rcases h.bottom_opening e with hh | ⟨hb, _⟩ | ⟨_, U, hv, hc⟩
  · exact (hd hh).elim
  · exact (hr.1 hb).elim
  · rcases hr.2 U with hmem | hcached
    · have heq : U = T := by
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · exact congrArg Prod.fst heq
        · exact (hv hmem).elim
      subst U
      exact hc
    · simp only [hc, Option.isSome_none, Bool.false_eq_true] at hcached

/-- Before a raw PRF answer closes readiness, its own term is still missing
unless P's aggregate was already completed. -/
theorem ReleaseSlack.readyAfter_missing {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (query : Query C) (e : KeyIndex)
    (hd : ¬PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (hr : ReadyAfter seeds data source.signing e query) :
    ∃ T : C.Term, query = .prf (seeds T) (.randomizer bottomLayer e) ∧
      data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none := by
  rcases h.bottom_opening e with hh | ⟨hb, _⟩ | ⟨_, T, hv, hc⟩
  · exact (hd hh).elim
  · exact (hr.1 hb).elim
  · refine ⟨T, ?_, hc⟩
    rcases hr.2 T with hmem | hcached | heq
    · exact (hv hmem).elim
    · simp only [hc, Option.isSome_none, Bool.false_eq_true] at hcached
    · exact heq

set_option backward.isDefEq.respectTransparency false in
/-- Each virtual PRF read inserts its virtual slot and retains its one actual
call in the capped counter, including repeated reads. -/
theorem runSource_virtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (T : C.Term) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) (.virtual T point))) source backend =
      pure (((), source), (({ backend.1.1 with data :=
        { backend.1.1.data with virtual := insert (T, point) backend.1.1.data.virtual } },
        backend.1.2 + 1), backend.2)) := by
  rw [runSource_deferredQuery_no_candidate P seeds q s (.virtual T point) rfl]
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure, deferredCounted, if_true]

set_option backward.isDefEq.respectTransparency false in
/-- The actual virtual source call rechecks P after its counted insertion.
It returns to a stable release-slack boundary in every readiness branch. -/
theorem sourceVirtual_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (T : C.Term) (point : Point) (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceVirtual P seeds T point) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data := by
  cases point with
  | chain lay e l pos =>
      simp only [sourceVirtual, runSource_bind, runSource_virtual, pure_bind,
        runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hs.virtual_unready T _ (by intro f hf; cases hf)
  | randomizer lay e =>
      by_cases hl : lay = bottomLayer
      · subst lay
        simp only [sourceVirtual, runSource_bind, runSource_virtual, pure_bind,
          ↓reduceIte, runSource_snapshot, runSource_get] at hr
        split at hr
        · let nextBackend : CappedCompilerState C :=
            (({ backend.1.1 with data := { backend.1.1.data with
                virtual := insert (T, Point.randomizer bottomLayer e) backend.1.1.data.virtual } },
              backend.1.2 + 1), backend.2)
          have hout := sourceReleaseOpening_slack_frame P seeds hinj q s e source nextBackend
            backend.1.1.data hs (fun _ _ => rfl) (by
              intro f hfe U
              change ((U, Point.randomizer bottomLayer f) ∈
                insert (T, Point.randomizer bottomLayer e) backend.1.1.data.virtual ↔ _)
              simp [hfe]) rfl hv hrev r hr
          exact hout.1
        · rename_i hready
          rw [runSource_pure, mem_support_pure_iff] at hr
          subst r
          exact hs.virtual_unready T _ (by
            intro f hf
            have he : e = f := (Point.randomizer.inj hf).2
            subst f
            exact hready)
      · simp only [sourceVirtual, runSource_bind, runSource_virtual, pure_bind,
          hl, ↓reduceIte, runSource_pure, mem_support_pure_iff] at hr
        subst r
        exact hs.virtual_unready T _ (by
          intro f hf
          exact (hl (Point.randomizer.inj hf).1).elim)

/-- Recording a reveal preserves slack when any bottom opening it exposes is
already complete. Reveals of chain coordinates need no additional condition. -/
theorem ReleaseSlack.reveal {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (key : HiddenKey) (value : Digest)
    (ha : ∀ e, key = .opening bottomLayer e →
      PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e))) :
    ReleaseSlack seeds s { source with revealed := Function.update source.revealed key (some value) } data := by
  refine ⟨h.corrupt_bound, h.bottom_opening, h.bottom_chain, h.top_opening, h.top_start, ?_⟩
  intro e he
  by_cases hk : HiddenKey.opening bottomLayer e = key
  · exact ha e hk.symm
  · apply h.bottom_released e
    change Function.update source.revealed key (some value) (.opening bottomLayer e) ≠ none at he
    simpa only [Function.update_of_ne hk] using he

/-- The actual reveal routine preserves release slack under its local opening
condition, for both first reveals and cached repeats. -/
theorem sourceReveal_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (key : HiddenKey)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (ha : ∀ e, key = .opening bottomLayer e →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReveal key) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data := by
  cases hk : source.revealed key with
  | some value =>
      rw [runSource_sourceReveal_cached P seeds q s key source backend value hk,
        mem_support_pure_iff] at hr
      subst r
      exact hs
  | none =>
      rw [runSource_sourceReveal_fresh P seeds q s key source backend hk,
        mem_support_pure_iff] at hr
      subst r
      exact hs.reveal key _ ha

/-- Materializing a deferred digest preserves slack whenever a secret low half
satisfies the same opening condition. -/
theorem sourceRevealDigest_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (value : DeferredDigest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (ha : ∀ e, value = .secret (.opening bottomLayer e) →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceRevealDigest value) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data := by
  cases value with
  | known digest =>
      simp only [sourceRevealDigest, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hs
  | secret key =>
      exact sourceReveal_slack P seeds q s key source backend hs
        (fun e he => ha e (congrArg DeferredDigest.secret he)) r hr

/-- A pending output can name a next chain coordinate, never a randomizer. -/
theorem PendingInput.next_ne_opening (p : PendingInput) (lay : Layer) (e : KeyIndex) :
    p.next ≠ some (.opening lay e) := by
  cases p <;> simp [PendingInput.next]

/-- Reachable pending lows cannot reveal an opening as a chain successor. -/
theorem PendingValid.low_ne_opening {data : DeferredState C} (h : PendingValid data)
    (p : PendingInput) (answer : DeferredOutput) (hp : data.pending p = some answer)
    (lay : Layer) (e : KeyIndex) : answer.low ≠ .secret (.opening lay e) := by
  intro he
  rcases h p answer hp with ⟨key, hn, hl⟩ | ⟨_, value, hl⟩
  · rw [he] at hl
    have hk := DeferredDigest.secret.inj hl
    exact PendingInput.next_ne_opening p lay e (hn.trans (congrArg some hk.symm))
  · rw [he] at hl
    cases hl

set_option backward.isDefEq.respectTransparency false in
/-- A pending plant preserves slack at P, Q and R. Its input may expose a
bottom opening only after that opening's PRF constraint is complete; every
symbolic low half is a chain coordinate by the actual pending invariant. -/
theorem sourcePlant_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hv : PendingValid backend.1.1.data)
    (ha : ∀ e, p.key = .opening bottomLayer e →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data := by
  simp only [sourcePlant, runSource_bind, runSource_inspect, mem_support_bind_iff] at hr
  obtain ⟨_, rfl, hr⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | none =>
      simp only [hp, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hs
  | some answer =>
      simp only [hp, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨ri, hri, rl, hrl, rp, hrp, hr⟩ := hr
      have his := sourceReveal_slack P seeds q s p.key source backend hs ha ri hri
      have hls := sourceRevealDigest_slack P seeds q s answer.low ri.1.2 ri.2 his
        (fun e he => (PendingValid.low_ne_opening hv p answer hp bottomLayer e he).elim) rl hrl
      rw [runSource_plant] at hrp
      simp only [support_map] at hrp
      obtain ⟨planted, hplanted, rfl⟩ := hrp
      simp only [runSource_modify, mem_support_pure_iff] at hr
      subst r
      have hdata : planted.2 = { rl.2.1.1.data with cache := planted.2.cache } := by
        cases hc : rl.2.1.1.data.cache (PlantInput.pending P p ri.1.1).query with
        | none =>
            simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hplanted
            subst planted
            rfl
        | some prior =>
            simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hplanted
            subst planted
            rfl
      have hvirtual := congrArg DeferredState.virtual hdata
      have hpads := congrArg DeferredState.pads hdata
      apply hls.frame (source' := { rl.1.2 with consistent := rl.1.2.consistent && planted.1 })
        rfl ?_ hvirtual hpads (fun _ he => he)
      intro seed point
      apply deferredImpl_prf_frame _ _ planted hplanted
      simp [WritesPrf, PlantInput.query]

/-- The Q alternatives guarantee actual missing slack unless the masked
bottom-chain target is already complete. -/
theorem ReleaseSlack.bottom_chain_admissible {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex) (l : ChainIndex)
    (pos : XmssSecurity.ChainStep) :
    PointDone seeds data (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
      (bottomReleaseTarget s data e l pos) ∨
    firstUnmaterialized seeds data (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)) ≠ none :=
  (h.bottom_chain e l pos).imp And.right (fun hu => hu.missing h.corrupt_bound)

/-- The R opening alternatives guarantee a missing concrete term or the exact
previously completed top randomizer. -/
theorem ReleaseSlack.top_opening_admissible {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (b : XmssSecurity.TopIndex) :
    PointDone seeds data (.randomizer topLayer (topKey b)) (s (.opening topLayer (topKey b))) ∨
      firstUnmaterialized seeds data (.randomizer topLayer (topKey b)) ≠ none :=
  (h.top_opening b).imp id (fun hu => hu.missing h.corrupt_bound)

/-- The same R slack guarantee holds at every top-chain starting point. -/
theorem ReleaseSlack.top_start_admissible {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    PointDone seeds data (.chain topLayer (topKey b) l (digit 0)) (s (.topChain b l ⟨0, by decide⟩)) ∨
      firstUnmaterialized seeds data (.chain topLayer (topKey b) l (digit 0)) ≠ none :=
  (h.top_start b l).imp id (fun hu => hu.missing h.corrupt_bound)

/-- Adding pads conservatively preserves all existing masked targets. An
unallocated positive-position pad can occur only in Q's uncached alternative. -/
theorem ReleaseSlack.pads_mono {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (pads : Point → Option Digest)
    (hp : ∀ point value, data.pads point = some value → pads point = some value) :
    ReleaseSlack seeds s source { data with pads := pads } := by
  refine ⟨h.corrupt_bound, h.bottom_opening, ?_, h.top_opening, h.top_start, h.bottom_released⟩
  intro e l pos
  rcases h.bottom_chain e l pos with ⟨hh, hd⟩ | hu
  · have target : bottomReleaseTarget s { data with pads := pads } e l pos =
        bottomReleaseTarget s data e l pos := by
      by_cases hpos : pos.val = 0
      · simp only [bottomReleaseTarget, hpos, ↓reduceIte]
      · have hn := hh.resolve_left hpos
        obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp hn
        simp only [bottomReleaseTarget, hpos, ↓reduceIte, hv, hp _ _ hv]
    refine Or.inl ⟨?_, ?_⟩
    · rcases hh with hz | hn
      · exact Or.inl hz
      · obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp hn
        exact Or.inr (by
          change pads _ ≠ none
          rw [hp _ _ hv]
          exact Option.some_ne_none value)
    · rw [target]
      exact hd
  · exact Or.inr hu

set_option backward.isDefEq.respectTransparency false in
/-- The actual pad call preserves slack and returns the pad recorded at its
point. Repeated calls replay the same pad and have no charged hash count. -/
theorem sourcePad_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (deferredQuery (C := C) (.pad point))) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      r.2.1.1.data.pads point = some r.1.1 ∧ r.1.2 = source ∧
      r.2 = (({ backend.1.1 with data :=
        { backend.1.1.data with pads := r.2.1.1.data.pads } }, backend.1.2), backend.2) := by
  rw [runSource_deferredQuery_no_candidate P seeds q s (.pad point) rfl] at hr
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  cases hp : backend.1.1.data.pads point with
  | some value =>
      simp only [deferredImpl, hp, mem_support_pure_iff] at hb
      subst b
      exact ⟨hs, hp, rfl, by simp [deferredCounted]⟩
  | none =>
      simp only [deferredImpl, hp, support_map] at hb
      obtain ⟨value, _, rfl⟩ := hb
      refine ⟨hs.pads_mono _ ?_, Function.update_self .., rfl, by simp [deferredCounted]⟩
      intro other previous hprevious
      by_cases he : other = point
      · subst other
        rw [hp] at hprevious
        cases hprevious
      · rw [Function.update_of_ne he]
        exact hprevious

/-- Completing one Q point preserves the other release constraints. The
pad is already present at positive positions and remains fixed. -/
theorem ReleaseSlack.complete_chain {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source source' : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex) (l : ChainIndex)
    (pos : XmssSecurity.ChainStep)
    (hs : source'.signing = source.signing)
    (hc : ∀ seed point,
      point ≠ .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos) →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads)
    (hr : ∀ f, source'.revealed (.opening bottomLayer f) ≠ none →
      source.revealed (.opening bottomLayer f) ≠ none)
    (hpad : pos.val = 0 ∨ data'.pads
      (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)) ≠ none)
    (hd : PointDone seeds data' (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
      (bottomReleaseTarget s data' e l pos)) : ReleaseSlack seeds s source' data' := by
  have done : ∀ point target,
      point ≠ .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos) →
      PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hn hh => hh.of_cache_eq (fun T => hc _ _ hn)
  have uncache : ∀ point,
      point ≠ .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos) →
      LackedUncached seeds source.signing.corrupt data point →
        LackedUncached seeds source'.signing.corrupt data' point := by
    intro point hn hh T hT
    rw [hc _ _ hn]
    exact hh T (hs ▸ hT)
  refine ⟨hs ▸ h.corrupt_bound, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rcases h.bottom_opening f with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
    · exact Or.inl (done _ _ (by simp) hh)
    · exact Or.inr (Or.inl ⟨hs ▸ hb, uncache _ (by simp) hh⟩)
    · exact Or.inr (Or.inr ⟨hs ▸ hb, T, hv ▸ ht, (hc _ _ (by simp)).trans hh⟩)
  · intro f j step
    by_cases he : Point.chain bottomLayer f j (XmssSecurity.CappedChain.chainStepDigit step) =
        .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)
    · obtain ⟨_, he, hj, hstep⟩ := Point.chain.inj he
      have hpos : step = pos := by
        have hh := congrArg (fun d : XmssSecurity.Digit => d.val) hstep
        exact Fin.ext hh
      subst f
      subst j
      subst step
      exact Or.inl ⟨hpad, hd⟩
    · rcases h.bottom_chain f j step with ⟨hh, hk⟩ | hh
      · refine Or.inl ⟨?_, ?_⟩
        · simpa only [hp] using hh
        · simpa only [bottomReleaseTarget, hp] using done _ _ he hk
      · exact Or.inr (uncache _ he hh)
  · intro b
    exact (h.top_opening b).imp (done _ _ (by simp)) (uncache _ (by simp))
  · intro b j
    have hn : Point.chain topLayer (topKey b) j (digit 0) ≠
        .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos) := by
      simp [topLayer, bottomLayer]
    exact (h.top_start b j).imp (done _ _ hn) (uncache _ hn)
  · intro f hf
    exact done _ _ (by simp) (h.bottom_released f (hr f hf))

/-- Q's completion body at one canonical chain position. -/
def sourceBottomCompletion (_P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) : SourceM C Unit := do
  let value ← sourceReveal (.bottomChain e l pos)
  let offset ← if pos.val = 0 then pure (0 : Digest) else
    liftM (deferredQuery (C := C) (.pad (.chain bottomLayer e l
      ⟨pos.val, by have hp := pos.isLt; change pos.val < 4; change pos.val < 3 at hp; omega⟩)))
  let ok ← liftM (completePrf seeds (.chain bottomLayer e l
    ⟨pos.val, by have hp := pos.isLt; change pos.val < 4; change pos.val < 3 at hp; omega⟩) (value ^^^ offset))
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }

/-- These are exactly the completion bodies in the frozen Q source. -/
theorem sourceReleaseBottomSuffix_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    sourceReleaseBottomSuffix P seeds e l start = (do
      let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
      let _ ← keys.mapM (sourceBottomCompletion P seeds e l)
      let _ ← keys.mapM fun p => sourcePlant P (.bottom e l p)
      pure ()) := rfl

/-- The actual Q completion succeeds and preserves every release clause once
its positive-position pad has been allocated. -/
theorem completePrf_chain_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hpad : pos.val = 0 ∨ backend.1.1.data.pads
      (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)) ≠ none)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (completePrf seeds (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
        (bottomReleaseTarget s backend.1.1.data e l pos))) source backend)) :
    r.1.1 = true ∧ ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
        (bottomReleaseTarget s r.2.1.1.data e l pos) := by
  have hd := completePrf_done_or_missing P seeds hinj q s _ _ source backend
    (hs.bottom_chain_admissible e l pos) r hr
  have hf := completePrf_frame P seeds q s _ _ source backend r hr
  have hdata := congrArg (fun b : CappedCompilerState C => b.1.1.data) hf.2.1
  have hvirtual := congrArg DeferredState.virtual hdata
  have hpads := congrArg DeferredState.pads hdata
  change r.2.1.1.data.pads = backend.1.1.data.pads at hpads
  have target : bottomReleaseTarget s r.2.1.1.data e l pos =
      bottomReleaseTarget s backend.1.1.data e l pos := by
    simp only [bottomReleaseTarget, hpads]
  have done : PointDone seeds r.2.1.1.data
      (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
      (bottomReleaseTarget s r.2.1.1.data e l pos) := target.symm ▸ hd.2
  refine ⟨hd.1, ?_, done⟩
  apply hs.complete_chain e l pos (congrArg SourceState.signing hf.1)
    hf.2.2.2 hvirtual hpads (fun f he => hf.1 ▸ he) ?_ done
  simpa only [hpads] using hpad

set_option backward.isDefEq.respectTransparency false in
/-- The exact interpreter decomposition of Q's one-position completion body. -/
theorem runSource_bottomCompletion (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex) (l : ChainIndex)
    (pos : XmssSecurity.ChainStep) (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (sourceBottomCompletion P seeds e l pos) source backend = (do
      let revealed ← runSource P seeds q s (sourceReveal (.bottomChain e l pos)) source backend
      let offset ← runSource P seeds q s
        (if pos.val = 0 then pure (0 : Digest) else
          (liftM (deferredQuery (C := C) (.pad (.chain bottomLayer e l
            (XmssSecurity.CappedChain.chainStepDigit pos)))) : SourceM C Digest))
        revealed.1.2 revealed.2
      let completed ← runSource P seeds q s
        (liftM (completePrf seeds (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
          (revealed.1.1 ^^^ offset.1.1))) offset.1.2 offset.2
      runSource P seeds q s
        (modify fun (st : SourceState C) => { st with consistent := st.consistent && completed.1.1 })
        completed.1.2 completed.2) := by
  by_cases hp : pos.val = 0 <;>
    simp only [sourceBottomCompletion, XmssSecurity.CappedChain.chainStepDigit, hp, ↓reduceIte, runSource_bind]
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual reveal-pad-complete sequence at each Q position returns to a
stable release-slack boundary and installs its exact masked target. -/
theorem sourceBottomCompletion_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceBottomCompletion P seeds e l pos) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
        (bottomReleaseTarget s r.2.1.1.data e l pos) := by
  rw [runSource_bottomCompletion] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, offset, hoffset, completed, hcompleted, hr⟩ := hr
  have hrevealed := sourceReveal_correct P seeds q s (.bottomChain e l pos)
    source backend hrev revealed hreveal
  have hslack := sourceReveal_slack P seeds q s (.bottomChain e l pos)
    source backend hs (by intro f hf; cases hf) revealed hreveal
  have hoff : ReleaseSlack seeds s offset.1.2 offset.2.1.1.data ∧
      (pos.val = 0 ∨ offset.2.1.1.data.pads
        (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)) ≠ none) ∧
      revealed.1.1 ^^^ offset.1.1 = bottomReleaseTarget s offset.2.1.1.data e l pos := by
    by_cases hp : pos.val = 0
    · simp only [hp, ↓reduceIte, runSource_pure, mem_support_pure_iff] at hoffset
      subst offset
      exact ⟨hslack, Or.inl hp, by simp only [bottomReleaseTarget, hp, ↓reduceIte, hrevealed.1]⟩
    · simp only [hp, ↓reduceIte] at hoffset
      have ho := sourcePad_slack P seeds q s _ revealed.1.2 revealed.2 hslack offset hoffset
      refine ⟨ho.1, Or.inr ?_, ?_⟩
      · rw [ho.2.1]
        exact Option.some_ne_none _
      · simp only [bottomReleaseTarget, hp, ↓reduceIte, hrevealed.1,
          ho.2.1, Option.getD_some]
  rw [hoff.2.2] at hcompleted
  have hcomplete := completePrf_chain_slack P seeds hinj q s e l pos
    offset.1.2 offset.2 hoff.1 hoff.2.1 completed hcompleted
  simp only [runSource_modify, mem_support_pure_iff] at hr
  subst r
  refine ⟨?_, hcomplete.2.2⟩
  exact hcomplete.2.1.frame rfl (fun _ _ => rfl) rfl rfl (fun _ he => he)

/-- Reveal synchronization depends only on the two revealed-value maps. -/
theorem RevealRelation.frame {s : HiddenKey → Digest}
    {source source' : SourceState C} {backend backend' : CappedCompilerState C}
    (h : RevealRelation s source backend)
    (hs : source'.revealed = source.revealed) (hb : backend'.2.1 = backend.2.1) :
    RevealRelation s source' backend' := by
  refine ⟨hs.trans (h.1.trans hb.symm), ?_⟩
  intro key value hv
  exact h.2 key value (hs ▸ hv)

/-- Every actual capped backend step preserves the symbolic successor type. -/
theorem cappedCompiler_pendingValid_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C) (hv : PendingValid backend.1.1.data)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
    PendingValid r.2.1.1.data := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_pendingValid P seeds t backend.1.1 hv b hb
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      exact hv

/-- Pending validity is retained through arbitrary actual source continuations. -/
theorem runSource_pendingValid {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s oa source backend)) : PendingValid r.2.1.1.data :=
  simulateQ_sticky _ (fun st : CappedCompilerState C => PendingValid st.1.1.data)
    (cappedCompiler_pendingValid_step P seeds q s) (oa.run source) backend hv r hr

set_option backward.isDefEq.respectTransparency false in
/-- Pending materialization keeps the source and wrapper reveal maps synchronized. -/
theorem sourcePlant_revealRelation (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    RevealRelation s r.1.2 r.2 := by
  simp only [sourcePlant, runSource_bind, runSource_inspect, mem_support_bind_iff] at hr
  obtain ⟨_, rfl, hr⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | none =>
      simp only [hp, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hrev
  | some answer =>
      simp only [hp, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨ri, hri, rl, hrl, rp, hrp, hr⟩ := hr
      have hi := sourceReveal_correct P seeds q s p.key source backend hrev ri hri
      have hl := sourceRevealDigest_correct P seeds q s answer.low ri.1.2 ri.2 hi.2.1 rl hrl
      rw [runSource_plant] at hrp
      simp only [support_map] at hrp
      obtain ⟨planted, _, rfl⟩ := hrp
      simp only [runSource_modify, mem_support_pure_iff] at hr
      subst r
      exact hl.2.1

set_option backward.isDefEq.respectTransparency false in
/-- Q's reveal-pad-complete body also preserves its reveal-map synchronization. -/
theorem sourceBottomCompletion_revealRelation (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex) (l : ChainIndex)
    (pos : XmssSecurity.ChainStep) (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceBottomCompletion P seeds e l pos) source backend)) :
    RevealRelation s r.1.2 r.2 := by
  rw [runSource_bottomCompletion] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, offset, hoffset, completed, hcompleted, hr⟩ := hr
  have hrevealed := sourceReveal_correct P seeds q s (.bottomChain e l pos)
    source backend hrev revealed hreveal
  have hslack := sourceReveal_slack P seeds q s (.bottomChain e l pos)
    source backend hs (by intro f hf; cases hf) revealed hreveal
  have hoff : RevealRelation s offset.1.2 offset.2 := by
    by_cases hp : pos.val = 0
    · simp only [hp, ↓reduceIte, runSource_pure, mem_support_pure_iff] at hoffset
      subst offset
      exact hrevealed.2.1
    · simp only [hp, ↓reduceIte] at hoffset
      have ho := sourcePad_slack P seeds q s _ revealed.1.2 revealed.2 hslack offset hoffset
      have hsource := congrArg SourceState.revealed ho.2.2.1
      have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) ho.2.2.2
      exact hrevealed.2.1.frame hsource hbackend
  have hf := completePrf_frame P seeds q s _ _ offset.1.2 offset.2 completed hcompleted
  have hsource := congrArg SourceState.revealed hf.1
  have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) hf.2.1
  have hfinal := hoff.frame hsource hbackend
  simp only [runSource_modify, mem_support_pure_iff] at hr
  subst r
  exact hfinal

set_option backward.isDefEq.respectTransparency false in
/-- A supported finite source traversal preserves a joint source/backend
invariant whenever its actual per-item source calls preserve it. -/
theorem runSource_mapM_inv {α β : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : α → SourceM C β)
    (I : SourceState C → CappedCompilerState C → Prop) (items : List α)
    (step : ∀ a ∈ items, ∀ source backend, I source backend →
      ∀ r : (β × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (oa a) source backend) → I r.1.2 r.2) :
    ∀ source backend, I source backend →
      ∀ r : (List β × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (items.mapM oa) source backend) → I r.1.2 r.2 := by
  induction items with
  | nil =>
      intro source backend hs r hr
      simp only [List.mapM_nil, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hs
  | cons a items ih =>
      intro source backend hs r hr
      simp only [List.mapM_cons, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ih (fun b hb => step b (List.mem_cons_of_mem _ hb)) head.1.2 head.2
        (step a (List.mem_cons_self ..) source backend hs head hhead) tail htail

set_option backward.isDefEq.respectTransparency false in
/-- The full frozen Q suffix preserves release slack, reveal synchronization
and pending validity, for every start position and every repeated call. -/
theorem sourceReleaseBottomSuffix_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hrev : RevealRelation s source backend) (hv : PendingValid backend.1.1.data)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseBottomSuffix P seeds e l start) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧ RevealRelation s r.1.2 r.2 ∧
      PendingValid r.2.1.1.data := by
  let I := fun source backend => ReleaseSlack seeds s source backend.1.1.data ∧
    RevealRelation s source backend ∧ PendingValid backend.1.1.data
  rw [sourceReleaseBottomSuffix_eq] at hr
  simp only [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨completed, hcompleted, planted, hplanted, hr⟩ := hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  have hc : I completed.1.2 completed.2 := by
    apply runSource_mapM_inv P seeds q s (sourceBottomCompletion P seeds e l) I _
      ?_ source backend ⟨hs, hrev, hv⟩ completed hcompleted
    intro pos _ st b h a ha
    exact ⟨(sourceBottomCompletion_slack P seeds hinj q s e l pos st b h.1 h.2.1 a ha).1,
      sourceBottomCompletion_revealRelation P seeds q s e l pos st b h.1 h.2.1 a ha,
      runSource_pendingValid P seeds q s _ st b h.2.2 a ha⟩
  apply runSource_mapM_inv P seeds q s (fun pos => sourcePlant P (.bottom e l pos)) I _
    ?_ completed.1.2 completed.2 hc planted hplanted
  intro pos _ st b h a ha
  exact ⟨sourcePlant_slack P seeds q s (.bottom e l pos) st b h.1 h.2.2
      (by intro f hf; cases hf) a ha,
    sourcePlant_revealRelation P seeds q s (.bottom e l pos) st b h.2.1 a ha,
    runSource_pendingValid P seeds q s _ st b h.2.2 a ha⟩

/-- R's randomizer point or the zero position of one of its top chains. -/
def topReleasePoint (b : XmssSecurity.TopIndex) : Option ChainIndex → Point
  | none => .randomizer topLayer (topKey b)
  | some l => .chain topLayer (topKey b) l (digit 0)

def topReleaseKey (b : XmssSecurity.TopIndex) : Option ChainIndex → HiddenKey
  | none => .opening topLayer (topKey b)
  | some l => .topChain b l ⟨0, by decide⟩

/-- Each R completion has an exact finished target or a concrete missing term. -/
theorem ReleaseSlack.top_admissible {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (b : XmssSecurity.TopIndex) (kind : Option ChainIndex) :
    PointDone seeds data (topReleasePoint b kind) (s (topReleaseKey b kind)) ∨
      firstUnmaterialized seeds data (topReleasePoint b kind) ≠ none := by
  cases kind with
  | none => exact h.top_opening_admissible b
  | some l => exact h.top_start_admissible b l

/-- Completing one R point preserves every other release constraint. -/
theorem ReleaseSlack.complete_top {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source source' : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlack seeds s source data) (b : XmssSecurity.TopIndex) (kind : Option ChainIndex)
    (hs : source'.signing = source.signing)
    (hc : ∀ seed point, point ≠ topReleasePoint b kind →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads)
    (hr : ∀ e, source'.revealed (.opening bottomLayer e) ≠ none →
      source.revealed (.opening bottomLayer e) ≠ none)
    (hd : PointDone seeds data' (topReleasePoint b kind) (s (topReleaseKey b kind))) :
    ReleaseSlack seeds s source' data' := by
  have done : ∀ point target, point ≠ topReleasePoint b kind →
      PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hn hh => hh.of_cache_eq (fun T => hc _ _ hn)
  have uncache : ∀ point, point ≠ topReleasePoint b kind →
      LackedUncached seeds source.signing.corrupt data point →
        LackedUncached seeds source'.signing.corrupt data' point := by
    intro point hn hh T hT
    rw [hc _ _ hn]
    exact hh T (hs ▸ hT)
  have randomizer_ne : ∀ e, Point.randomizer bottomLayer e ≠ topReleasePoint b kind := by
    intro e
    cases kind <;> simp [topReleasePoint, topLayer, bottomLayer]
  have chain_ne : ∀ e l pos, Point.chain bottomLayer e l pos ≠ topReleasePoint b kind := by
    intro e l pos
    cases kind <;> simp [topReleasePoint, topLayer, bottomLayer]
  refine ⟨hs ▸ h.corrupt_bound, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases h.bottom_opening e with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
    · exact Or.inl (done _ _ (randomizer_ne e) hh)
    · exact Or.inr (Or.inl ⟨hs ▸ hb, uncache _ (randomizer_ne e) hh⟩)
    · exact Or.inr (Or.inr ⟨hs ▸ hb, T, hv ▸ ht, (hc _ _ (randomizer_ne e)).trans hh⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with ⟨hh, hk⟩ | hh
    · refine Or.inl ⟨?_, ?_⟩
      · simpa only [hp] using hh
      · simpa only [bottomReleaseTarget, hp] using done _ _ (chain_ne e l _) hk
    · exact Or.inr (uncache _ (chain_ne e l _) hh)
  · intro f
    by_cases he : Point.randomizer topLayer (topKey f) = topReleasePoint b kind
    · apply Or.inl
      cases kind with
      | none =>
          have hk := (Point.randomizer.inj he).2
          simpa only [topReleasePoint, topReleaseKey, hk] using hd
      | some l => cases he
    · exact (h.top_opening f).imp (done _ _ he) (uncache _ he)
  · intro f j
    by_cases he : Point.chain topLayer (topKey f) j (digit 0) = topReleasePoint b kind
    · apply Or.inl
      cases kind with
      | none => cases he
      | some l =>
          obtain ⟨_, hk, hj, _⟩ := Point.chain.inj he
          have hf : f = b := by
            have hh := congrArg (fun e : KeyIndex => e.val) hk
            exact Fin.ext hh
          subst f
          subst j
          exact hd
    · exact (h.top_start f j).imp (done _ _ he) (uncache _ he)
  · intro e he
    exact done _ _ (randomizer_ne e) (h.bottom_released e (hr e he))

/-- R's actual completion succeeds and preserves the release invariant. -/
theorem completePrf_top_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (kind : Option ChainIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (completePrf seeds (topReleasePoint b kind) (s (topReleaseKey b kind)))) source backend)) :
    r.1.1 = true ∧ ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (topReleasePoint b kind) (s (topReleaseKey b kind)) := by
  have hd := completePrf_done_or_missing P seeds hinj q s _ _ source backend
    (hs.top_admissible b kind) r hr
  have hf := completePrf_frame P seeds q s _ _ source backend r hr
  have hdata := congrArg (fun b : CappedCompilerState C => b.1.1.data) hf.2.1
  have hvirtual := congrArg DeferredState.virtual hdata
  have hpads := congrArg DeferredState.pads hdata
  exact ⟨hd.1, hs.complete_top b kind (congrArg SourceState.signing hf.1)
    hf.2.2.2 hvirtual hpads (fun _ he => hf.1 ▸ he) hd.2, hd.2⟩

/-- R's reveal-and-complete prefix, returning its materialized input. -/
def sourceTopCompletion (seeds : C.Term → HashOutput) (b : XmssSecurity.TopIndex)
    (kind : Option ChainIndex) : SourceM C Digest := do
  let value ← sourceReveal (topReleaseKey b kind)
  let ok ← liftM (completePrf seeds (topReleasePoint b kind) value)
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  pure value

set_option backward.isDefEq.respectTransparency false in
/-- R's actual prefix preserves slack and reveal synchronization and returns
exactly the hidden coordinate used to complete its PRF constraint. -/
theorem sourceTopCompletion_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (kind : Option ChainIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceTopCompletion seeds b kind) source backend)) :
    r.1.1 = s (topReleaseKey b kind) ∧ ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧
      RevealRelation s r.1.2 r.2 ∧
      PointDone seeds r.2.1.1.data (topReleasePoint b kind) (s (topReleaseKey b kind)) := by
  simp only [sourceTopCompletion, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, completed, hcompleted, modified, hmodified, hr⟩ := hr
  have hrevealed := sourceReveal_correct P seeds q s (topReleaseKey b kind)
    source backend hrev revealed hreveal
  have hslack := sourceReveal_slack P seeds q s (topReleaseKey b kind) source backend hs
    (by intro e he; cases kind <;> simp [topReleaseKey, topLayer, bottomLayer] at he) revealed hreveal
  rw [hrevealed.1] at hcompleted
  have hc := completePrf_top_slack P seeds hinj q s b kind revealed.1.2 revealed.2 hslack
    completed hcompleted
  have hf := completePrf_frame P seeds q s _ _ revealed.1.2 revealed.2 completed hcompleted
  have hsource := congrArg SourceState.revealed hf.1
  have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) hf.2.1
  have hfinal := hrevealed.2.1.frame hsource hbackend
  rw [runSource_modify, mem_support_pure_iff] at hmodified
  subst modified
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  exact ⟨hrevealed.1, hc.2.1.frame rfl (fun _ _ => rfl) rfl rfl (fun _ he => he),
    hfinal, hc.2.2⟩

/-- A stored symbolic top-signature value does not name a bottom opening. -/
def NoBottomOpening (value : DeferredDigest) : Prop :=
  ∀ e, value ≠ .secret (.opening bottomLayer e)

/-- R completes a top-chain PRF precisely when its opened suffix starts at zero. -/
def sourceTopStartCompletion (seeds : C.Term → HashOutput) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (start : Digit) : SourceM C Unit :=
  if start.val = 0 then do
    let _ ← sourceTopCompletion seeds b (some l)
    pure ()
  else pure ()

/-- One chain's actual release-and-materialize body inside R. -/
def sourceReturnedChain (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) (l : ChainIndex) : SourceM C Digest := do
  let start := tree.topSignature.encoding l
  let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
  let _ ← keys.mapM fun p => sourceReveal (.topChain b l p)
  sourceTopStartCompletion seeds b l start
  let _ ← keys.mapM fun p => sourcePlant P (.top b l p)
  sourceRevealDigest (tree.topSignature.chainValue l)

/-- The extracted R prefixes and chain bodies are the frozen return-tree source. -/
theorem sourceReturnTree_eq (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) :
    sourceReturnTree P seeds b tree = (do
      let opening ← sourceTopCompletion seeds b none
      let pending := (← get).allocated.filter fun p => p.key = .opening topLayer (topKey b)
      let _ ← pending.mapM (sourcePlant P)
      let values ← Concrete.sequenceFin (sourceReturnedChain P seeds b tree)
      pure (⟨tree.cpk, tree.commitment, tree.root,
        ⟨tree.topSignature.randomness, values, tree.topSignature.path⟩⟩, opening)) := by
  have distribute {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : SourceM C α) (next : α → SourceM C β) :
      ((if condition then yes else no) >>= next) =
        (if condition then yes >>= next else no >>= next) := by
    split <;> rfl
  unfold sourceReturnedChain
  simp only [sourceReturnTree, sourceTopCompletion, sourceTopStartCompletion,
    topReleasePoint, topReleaseKey, distribute, bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Both branches of R's optional start completion preserve the joint invariant. -/
theorem sourceTopStartCompletion_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (start : Digit)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hrev : RevealRelation s source backend) (hv : PendingValid backend.1.1.data)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceTopStartCompletion seeds b l start) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧ RevealRelation s r.1.2 r.2 ∧
      PendingValid r.2.1.1.data := by
  have hv' := runSource_pendingValid P seeds q s _ source backend hv r hr
  by_cases hp : start.val = 0
  · simp only [sourceTopStartCompletion, hp, ↓reduceIte, runSource_bind,
      mem_support_bind_iff, runSource_pure, mem_support_pure_iff] at hr
    obtain ⟨completed, hcompleted, rfl⟩ := hr
    have hc := sourceTopCompletion_slack P seeds hinj q s b (some l) source backend hs hrev
      completed hcompleted
    exact ⟨hc.2.1, hc.2.2.1, hv'⟩
  · simp only [sourceTopStartCompletion, hp, ↓reduceIte, runSource_pure,
      mem_support_pure_iff] at hr
    subst r
    exact ⟨hs, hrev, hv⟩

set_option backward.isDefEq.respectTransparency false in
/-- R's chain body preserves the joint invariant for its stored symbolic value. -/
theorem sourceReturnedChain_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) (l : ChainIndex)
    (hvalue : NoBottomOpening (tree.topSignature.chainValue l))
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hrev : RevealRelation s source backend) (hv : PendingValid backend.1.1.data)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReturnedChain P seeds b tree l) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧ RevealRelation s r.1.2 r.2 ∧
      PendingValid r.2.1.1.data := by
  let I := fun source backend => ReleaseSlack seeds s source backend.1.1.data ∧
    RevealRelation s source backend ∧ PendingValid backend.1.1.data
  simp only [sourceReturnedChain, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, completed, hcompleted, planted, hplanted, hr⟩ := hr
  have hi : I revealed.1.2 revealed.2 := by
    apply runSource_mapM_inv P seeds q s (fun pos => sourceReveal (.topChain b l pos)) I _
      ?_ source backend ⟨hs, hrev, hv⟩ revealed hreveal
    intro pos _ st backend h a ha
    exact ⟨sourceReveal_slack P seeds q s _ st backend h.1
        (by intro e he; cases he) a ha,
      (sourceReveal_correct P seeds q s _ st backend h.2.1 a ha).2.1,
      runSource_pendingValid P seeds q s _ st backend h.2.2 a ha⟩
  have hc := sourceTopStartCompletion_slack P seeds hinj q s b l (tree.topSignature.encoding l)
    revealed.1.2 revealed.2 hi.1 hi.2.1 hi.2.2 completed hcompleted
  have hp : I planted.1.2 planted.2 := by
    apply runSource_mapM_inv P seeds q s (fun pos => sourcePlant P (.top b l pos)) I _
      ?_ completed.1.2 completed.2 hc planted hplanted
    intro pos _ st backend h a ha
    exact ⟨sourcePlant_slack P seeds q s (.top b l pos) st backend h.1 h.2.2
        (by intro e he; cases he) a ha,
      sourcePlant_revealRelation P seeds q s _ st backend h.2.1 a ha,
      runSource_pendingValid P seeds q s _ st backend h.2.2 a ha⟩
  exact ⟨sourceRevealDigest_slack P seeds q s _ planted.1.2 planted.2 hp.1
      (fun e he => (hvalue e he).elim) r hr,
    (sourceRevealDigest_correct P seeds q s _ planted.1.2 planted.2 hp.2.1 r hr).2.1,
    runSource_pendingValid P seeds q s _ planted.1.2 planted.2 hp.2.2 r hr⟩

set_option backward.isDefEq.respectTransparency false in
/-- The same index-order induction as `treeSimHash_state_sequenceFin_invariant`,
applied to the actual two-state source interpreter. -/
theorem runSource_sequenceFin_inv {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (I : SourceState C → CappedCompilerState C → Prop) :
    ∀ n (oa : Fin n → SourceM C α),
      (∀ i source backend, I source backend →
        ∀ r : (α × SourceState C) × CappedCompilerState C,
        r ∈ support (runSource P seeds q s (oa i) source backend) → I r.1.2 r.2) →
      ∀ source backend, I source backend →
        ∀ r : ((Fin n → α) × SourceState C) × CappedCompilerState C,
        r ∈ support (runSource P seeds q s (Concrete.sequenceFin oa) source backend) → I r.1.2 r.2 := by
  intro n
  induction n with
  | zero =>
      intro oa _ source backend hs r hr
      simp only [Concrete.sequenceFin, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hs
  | succ n ih =>
      intro oa step source backend hs r hr
      simp only [Concrete.sequenceFin, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ih (fun i => oa i.succ) (fun i => step i.succ) head.1.2 head.2
        (step 0 source backend hs head hhead) tail htail

set_option backward.isDefEq.respectTransparency false in
/-- The full frozen R source preserves the joint release invariant for stored
signature values whose symbolic coordinates are not bottom openings. -/
theorem sourceReturnTree_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree)
    (hshape : ∀ l, NoBottomOpening (tree.topSignature.chainValue l))
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (hrev : RevealRelation s source backend) (hv : PendingValid backend.1.1.data)
    (r : ((BottomTree × Digest) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReturnTree P seeds b tree) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data ∧ RevealRelation s r.1.2 r.2 ∧
      PendingValid r.2.1.1.data := by
  let I := fun source backend => ReleaseSlack seeds s source backend.1.1.data ∧
    RevealRelation s source backend ∧ PendingValid backend.1.1.data
  rw [sourceReturnTree_eq] at hr
  simp only [runSource_bind, runSource_get, pure_bind, mem_support_bind_iff] at hr
  obtain ⟨opening, hopening, planted, hplanted, values, hvalues, hr⟩ := hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  have ho := sourceTopCompletion_slack P seeds hinj q s b none source backend hs hrev opening hopening
  have hv' := runSource_pendingValid P seeds q s _ source backend hv opening hopening
  have hp : I planted.1.2 planted.2 := by
    apply runSource_mapM_inv P seeds q s (sourcePlant P) I _
      ?_ opening.1.2 opening.2 ⟨ho.2.1, ho.2.2.1, hv'⟩ planted hplanted
    intro p hmem st backend h a ha
    have hkey : p.key = .opening topLayer (topKey b) := of_decide_eq_true (List.mem_filter.mp hmem).2
    apply And.intro (sourcePlant_slack P seeds q s p st backend h.1 h.2.2 ?_ a ha)
    · exact ⟨sourcePlant_revealRelation P seeds q s p st backend h.2.1 a ha,
        runSource_pendingValid P seeds q s _ st backend h.2.2 a ha⟩
    · intro e he
      have hx := hkey.symm.trans he
      simp [topLayer, bottomLayer] at hx
  exact runSource_sequenceFin_inv P seeds q s I numChains (sourceReturnedChain P seeds b tree)
    (fun l st backend h a ha => sourceReturnedChain_slack P seeds hinj q s b tree l (hshape l)
      st backend h.1 h.2.1 h.2.2 a ha) planted.1.2 planted.2 hp values hvalues

/-- An actual pending read never returns an opening as its symbolic low half. -/
theorem runSource_pending_noBottomOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data)
    (r : (DeferredOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (deferredQuery (C := C) (.pending p))) source backend)) :
    NoBottomOpening r.1.1.low := by
  rw [runSource_deferredQuery_no_candidate P seeds q s (.pending p) rfl] at hr
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | some answer =>
      simp only [deferredImpl, hp, mem_support_pure_iff] at hb
      subst b
      exact fun e => PendingValid.low_ne_opening hv p answer hp bottomLayer e
  | none =>
      simp only [deferredImpl, hp, support_map] at hb
      obtain ⟨answer, ha, rfl⟩ := hb
      intro e he
      rcases samplePending_valid p answer ha with ⟨key, hn, hl⟩ | ⟨_, value, hl⟩
      · rw [he] at hl
        have hk := DeferredDigest.secret.inj hl
        exact PendingInput.next_ne_opening p bottomLayer e (hn.trans (congrArg some hk.symm))
      · rw [he] at hl
        cases hl

set_option backward.isDefEq.respectTransparency false in
/-- The live source pending routine has the same low-half shape on cached,
sampled, and concrete post-release hash paths. -/
theorem sourcePending_noBottomOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data)
    (r : (DeferredOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePending P p) source backend)) :
    NoBottomOpening r.1.1.low := by
  have tail (prior : Option DeferredOutput) (st : SourceState C) (back : CappedCompilerState C)
      (hvalid : PendingValid back.1.1.data)
      (a : (DeferredOutput × SourceState C) × CappedCompilerState C)
      (ha : a ∈ support (runSource P seeds q s (do
        let value ← liftM (deferredQuery (C := C) (.pending p))
        if prior.isNone then modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
        pure value : SourceM C DeferredOutput) st back)) : NoBottomOpening a.1.1.low := by
    simp only [runSource_bind, mem_support_bind_iff] at ha
    obtain ⟨pending, hpending, ha⟩ := ha
    have hn := runSource_pending_noBottomOpening P seeds q s p st back hvalid pending hpending
    by_cases hprior : prior.isNone
    · simp only [hprior, ↓reduceIte, runSource_bind, runSource_modify,
        pure_bind, runSource_pure, mem_support_pure_iff] at ha
      subst a
      exact hn
    · simp only [hprior] at ha
      subst a
      exact hn
  simp only [sourcePending, runSource_bind, runSource_inspect, runSource_get, pure_bind] at hr
  split at hr
  · simp only [runSource_bind, mem_support_bind_iff] at hr
    obtain ⟨hashed, _, recorded, _, modified, _, hr⟩ := hr
    rw [runSource_pure, mem_support_pure_iff] at hr
    subst r
    intro e he
    cases he
  · split at hr
    · simp only [runSource_bind, runSource_modify, pure_bind] at hr
      apply tail (backend.1.1.data.pending p) { source with consistent := false } backend hv r
      simpa only [runSource_bind, pure_bind] using hr
    · apply tail (backend.1.1.data.pending p) source backend hv r
      simpa only [runSource_bind, pure_bind] using hr

set_option backward.isDefEq.respectTransparency false in
/-- A finite source traversal whose actual answers have a fixed property
returns a list of answers with that property. Pending validity is carried online. -/
theorem runSource_mapM_values {α β : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : α → SourceM C β) (V : β → Prop) (items : List α)
    (step : ∀ a ∈ items, ∀ source backend, PendingValid backend.1.1.data →
      ∀ r : (β × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (oa a) source backend) → V r.1.1) :
    ∀ source backend, PendingValid backend.1.1.data →
      ∀ r : (List β × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (items.mapM oa) source backend) →
        ∀ value ∈ r.1.1, V value := by
  induction items with
  | nil =>
      intro source backend _ r hr
      simp only [List.mapM_nil, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact fun value hv => (List.not_mem_nil hv).elim
  | cons a items ih =>
      intro source backend hv r hr
      simp only [List.mapM_cons, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      have hfirst := step a (List.mem_cons_self ..) source backend hv head hhead
      have hrest := ih (fun b hb => step b (List.mem_cons_of_mem _ hb)) head.1.2 head.2
        (runSource_pendingValid P seeds q s _ source backend hv head hhead) tail htail
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact hfirst
      · exact hrest value hvalue

set_option backward.isDefEq.respectTransparency false in
/-- The actual top-prefix walk stores only known values or chain coordinates;
its result cannot name a bottom opening. -/
theorem sourceTopValue_noBottomOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : Digit)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data)
    (r : (DeferredDigest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceTopValue P seeds b l pos) source backend)) :
    NoBottomOpening r.1.1 := by
  simp only [sourceTopValue, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨virtual, hvirtual, values, hvalues, hr⟩ := hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  have hvalid := runSource_pendingValid P seeds q s _ source backend hv virtual hvirtual
  have hall := runSource_mapM_values P seeds q s _ (fun value : DeferredOutput => NoBottomOpening value.low)
    _ (fun _ _ st back h a ha => sourcePending_noBottomOpening P seeds q s _ st back h a ha)
    virtual.1.2 virtual.2 hvalid values hvalues
  cases hl : values.1.1.getLast? with
  | none =>
      simp only [Option.map_none, Option.getD_none]
      intro e he
      cases he
  | some value =>
      simp only [Option.map_some, Option.getD_some]
      exact hall value (List.mem_of_getLast? hl)

set_option backward.isDefEq.respectTransparency false in
/-- Indexed source traversal retains each actual answer's fixed property,
with the pending invariant carried through the preceding indices. -/
theorem runSource_sequenceFin_values {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (V : α → Prop) :
    ∀ n (oa : Fin n → SourceM C α),
      (∀ i source backend, PendingValid backend.1.1.data →
        ∀ r : (α × SourceState C) × CappedCompilerState C,
        r ∈ support (runSource P seeds q s (oa i) source backend) → V r.1.1) →
      ∀ source backend, PendingValid backend.1.1.data →
        ∀ r : ((Fin n → α) × SourceState C) × CappedCompilerState C,
        r ∈ support (runSource P seeds q s (Concrete.sequenceFin oa) source backend) →
          ∀ i, V (r.1.1 i) := by
  intro n
  induction n with
  | zero =>
      intro oa _ source backend _ r hr
      simp only [Concrete.sequenceFin, runSource_pure, mem_support_pure_iff] at hr
      subst r
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro oa step source backend hv r hr
      simp only [Concrete.sequenceFin, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      have hfirst := step 0 source backend hv head hhead
      have hrest := ih (fun i => oa i.succ) (fun i => step i.succ) head.1.2 head.2
        (runSource_pendingValid P seeds q s _ source backend hv head hhead) tail htail
      intro i
      exact Fin.cases hfirst hrest i

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- Every successful actual bottom build stores a top-signature value of the
shape required by R. This holds independently of the release/cache relation. -/
theorem sourceBottomTree_noBottomOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (top : TopTree) (b : XmssSecurity.TopIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data)
    (r : (Option DeferredBottomTree × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceBottomTree P seeds top b) source backend))
    (tree : DeferredBottomTree) (ht : r.1.1 = some tree) :
    ∀ l, NoBottomOpening (tree.topSignature.chainValue l) := by
  simp only [sourceBottomTree, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨rows, hrows, commitments, hcommitments, virtual, hvirtual,
    root, hroot, base, hbase, found, hfound, hr⟩ := hr
  have hv1 := runSource_pendingValid P seeds q s _ source backend hv rows (by with_reducible exact hrows)
  have hv2 := runSource_pendingValid P seeds q s _ rows.1.2 rows.2 hv1 commitments (by with_reducible exact hcommitments)
  have hv3 := runSource_pendingValid P seeds q s _ commitments.1.2 commitments.2 hv2 virtual (by with_reducible exact hvirtual)
  have hv4 := runSource_pendingValid P seeds q s _ virtual.1.2 virtual.2 hv3 root (by with_reducible exact hroot)
  have hv5 := runSource_pendingValid P seeds q s _ root.1.2 root.2 hv4 base (by with_reducible exact hbase)
  have hv6 := runSource_pendingValid P seeds q s _ base.1.2 base.2 hv5 found (by with_reducible exact hfound)
  cases hf : found.1.1 with
  | none =>
      simp only [hf, runSource_pure, mem_support_pure_iff] at hr
      have hout := congrArg (fun a : (Option DeferredBottomTree × SourceState C) ×
        CappedCompilerState C => a.1.1) hr
      have impossible := hout.symm.trans ht
      cases impossible
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      simp only [hf, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨values, hvalues, path, hpath, digest, hdigest, hr⟩ := hr
      have hall := runSource_sequenceFin_values P seeds q s NoBottomOpening numChains
        (fun l => sourceTopValue P seeds b l (encoding l))
        (fun l st back h a ha => sourceTopValue_noBottomOpening P seeds q s b l (encoding l) st back h a ha)
        found.1.2 found.2 hv6 values hvalues
      cases hc : Codeword.decode digest.1.1 with
      | none =>
          simp only [hc, runSource_pure, mem_support_pure_iff] at hr
          have hout := congrArg (fun a : (Option DeferredBottomTree × SourceState C) ×
            CappedCompilerState C => a.1.1) hr
          have impossible := hout.symm.trans ht
          cases impossible
      | some checked =>
          simp only [hc] at hr
          split at hr
          · simp only [runSource_bind, runSource_modify, runSource_pure,
              pure_bind, mem_support_pure_iff] at hr
            have hout := congrArg (fun a : (Option DeferredBottomTree × SourceState C) ×
              CappedCompilerState C => a.1.1) hr
            have impossible := hout.symm.trans ht
            cases impossible
          · simp only [runSource_bind, mem_support_bind_iff] at hr
            obtain ⟨ends, _, leaf, _, topRoot, _, hr⟩ := hr
            split at hr
            · rw [runSource_pure, mem_support_pure_iff] at hr
              have hout := congrArg (fun a : (Option DeferredBottomTree × SourceState C) ×
                CappedCompilerState C => a.1.1) hr
              have impossible := hout.symm.trans ht
              cases impossible
            · rw [runSource_pure, mem_support_pure_iff] at hr
              have hout := congrArg (fun a : (Option DeferredBottomTree × SourceState C) ×
                CappedCompilerState C => a.1.1) hr
              have he := Option.some.inj (hout.symm.trans ht)
              rw [← he]
              exact hall

/-- Every successful tree saved by the source has R's symbolic value shape. -/
def StoredTopShape (source : SourceState C) : Prop :=
  ∀ b tree, source.trees b = some (some tree) →
    ∀ l, NoBottomOpening (tree.topSignature.chainValue l)

theorem storedTopShape_initial : StoredTopShape (sourceInit (C := C)) := by
  intro b tree h
  cases h

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- D17's actual stored-or-fresh branch returns only values of the established
shape, including successful memoized results and repeated tree requests. -/
theorem sourceBottomOnce_noBottomOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (top : TopTree) (b : XmssSecurity.TopIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data) (hshape : StoredTopShape source)
    (r : (Option DeferredBottomTree × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceBottomOnce P seeds top b) source backend))
    (tree : DeferredBottomTree) (ht : r.1.1 = some tree) :
    ∀ l, NoBottomOpening (tree.topSignature.chainValue l) := by
  simp only [sourceBottomOnce, runSource_bind, runSource_get, pure_bind] at hr
  cases hb : source.trees b with
  | some prior =>
      simp only [hb, runSource_pure, mem_support_pure_iff] at hr
      subst r
      change prior = some tree at ht
      subst prior
      exact hshape b tree hb
  | none =>
      simp only [hb, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨built, hbuilt, modified, hmodified, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact sourceBottomTree_noBottomOpening P seeds q s top b source backend hv built hbuilt tree ht

/-- Source control fields that tree evaluation and release bookkeeping retain. -/
def sourceControl (source : SourceState C) :=
  (source.signing, source.trees, source.hiddenFlag, source.exposed, source.candidates)

/-- A source program preserves a field for every sequence of oracle answers. -/
def SourceKeeps {α β : Type} (field : SourceState C → β) (oa : SourceM C α) : Prop :=
  ∀ source r, r ∈ support (oa.run source) → field r.2 = field source

theorem SourceKeeps.pure {α β : Type} {field : SourceState C → β} (value : α) :
    SourceKeeps field (pure value) := by
  intro source r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  rfl

theorem SourceKeeps.get {β : Type} {field : SourceState C → β} :
    SourceKeeps field (get : SourceM C (SourceState C)) := by
  intro source r hr
  simp only [StateT.run_get, mem_support_pure_iff] at hr
  subst r
  rfl

theorem SourceKeeps.modify {β : Type} {field : SourceState C → β}
    (f : SourceState C → SourceState C) (hf : ∀ source, field (f source) = field source) :
    SourceKeeps field (modify f : SourceM C Unit) := by
  intro source r hr
  simp only [StateT.run_modify, mem_support_pure_iff] at hr
  subst r
  exact hf source

theorem SourceKeeps.lift {α β : Type} {field : SourceState C → β}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α) :
    SourceKeeps field (liftM oa : SourceM C α) := by
  intro source r hr
  change r ∈ support (oa >>= fun value => Pure.pure (value, source)) at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem SourceKeeps.bind {α β γ : Type} {field : SourceState C → γ}
    {oa : SourceM C α} (h : SourceKeeps field oa) (next : α → SourceM C β)
    (hn : ∀ value, SourceKeeps field (next value)) : SourceKeeps field (oa >>= next) := by
  intro source r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact (hn a.1 a.2 r hr).trans (h source a ha)

theorem SourceKeeps.mapM {α β γ : Type} {field : SourceState C → γ}
    (items : List α) (oa : α → SourceM C β)
    (h : ∀ a ∈ items, SourceKeeps field (oa a)) : SourceKeeps field (items.mapM oa) := by
  induction items with
  | nil => exact SourceKeeps.pure []
  | cons a items ih =>
      rw [List.mapM_cons]
      refine (h a (List.mem_cons_self ..)).bind _ fun value => ?_
      exact (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))).bind _
        (fun values => SourceKeeps.pure (value :: values))

theorem SourceKeeps.sequenceFin {α β : Type} {field : SourceState C → β} :
    ∀ n (oa : Fin n → SourceM C α), (∀ i, SourceKeeps field (oa i)) →
      SourceKeeps field (Concrete.sequenceFin oa) := by
  intro n
  induction n with
  | zero => intro oa _; exact SourceKeeps.pure Fin.elim0
  | succ n ih =>
      intro oa h
      change SourceKeeps field (oa 0 >>= fun head =>
        Concrete.sequenceFin (fun i : Fin n => oa i.succ) >>= fun tail => Pure.pure (Fin.cases head tail : Fin (n + 1) → α))
      exact (h 0).bind _ (fun head => (ih _ (fun i => h i.succ)).bind _
        (fun tail => SourceKeeps.pure (Fin.cases head tail : Fin (n + 1) → α)))

theorem SourceKeeps.simulateQ {ι α β : Type} {spec : OracleSpec ι} {field : SourceState C → β}
    (impl : QueryImpl spec (SourceM C)) (step : ∀ t, SourceKeeps field (impl t))
    (oa : OracleComp spec α) : SourceKeeps field (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using SourceKeeps.pure (field := field) value
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (step t).bind _ ih

/-- A field property proved for all source answers applies to the actual capped
interpreter by VCVio's support inclusion for stateful simulation. -/
theorem SourceKeeps.run {α β : Type} {field : SourceState C → β} {oa : SourceM C α}
    (h : SourceKeeps field oa) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (source : SourceState C) (backend : CappedCompilerState C)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s oa source backend)) : field r.1.2 = field source := by
  apply h source r.1
  apply support_simulateQ_run'_subset
    (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
    (oa.run source) backend
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

theorem sourceControl_sourceReveal (key : HiddenKey) :
    SourceKeeps (sourceControl (C := C)) (sourceReveal key) := by
  unfold sourceReveal
  refine SourceKeeps.get.bind _ fun source => ?_
  cases source.revealed key with
  | some value => exact SourceKeeps.pure value
  | none =>
      refine (SourceKeeps.lift (revealQuery key)).bind _ fun value => ?_
      exact (SourceKeeps.modify (fun st => { st with revealed := Function.update st.revealed key (some value) }) (fun _ => rfl)).bind _ (fun _ => SourceKeeps.pure value)

theorem sourceControl_sourceRevealDigest (value : DeferredDigest) :
    SourceKeeps (sourceControl (C := C)) (sourceRevealDigest value) := by
  cases value with
  | known digest => exact SourceKeeps.pure digest
  | secret key => exact sourceControl_sourceReveal key

theorem sourceControl_sourcePlant (P : PublicParameter) (p : PendingInput) :
    SourceKeeps (sourceControl (C := C)) (sourcePlant P p) := by
  unfold sourcePlant
  refine (SourceKeeps.lift (deferredQuery (.inspect p))).bind _ fun answer => ?_
  cases answer with
  | none => exact SourceKeeps.pure ()
  | some answer =>
      refine (sourceControl_sourceReveal p.key).bind _ fun input => ?_
      refine (sourceControl_sourceRevealDigest answer.low).bind _ fun low => ?_
      exact (SourceKeeps.lift (deferredQuery (.plant (.pending P p input)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low))))).bind _
          (fun ok => SourceKeeps.modify (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl))

theorem sourceControl_sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceKeeps sourceControl (sourceReleaseOpening P seeds e) := by
  unfold sourceReleaseOpening
  refine SourceKeeps.get.bind _ fun source => ?_
  split
  · refine (sourceControl_sourceReveal (.opening bottomLayer e)).bind _ fun value => ?_
    refine (SourceKeeps.lift (completePrf seeds (.randomizer bottomLayer e) value)).bind _ fun ok => ?_
    refine (SourceKeeps.modify (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl)).bind _ fun _ => ?_
    refine SourceKeeps.get.bind _ fun current => ?_
    exact (SourceKeeps.mapM _ (sourcePlant P) (fun p _ => sourceControl_sourcePlant P p)).bind _
      (fun _ => SourceKeeps.pure ())
  · exact SourceKeeps.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput) (query : Query C) :
    SourceKeeps sourceControl (sourceHash P seeds query) := by
  have hquery (query : Query C) :
      SourceKeeps sourceControl (liftM (deferredQuery (.hash query)) : SourceM C HashOutput) := SourceKeeps.lift _
  unfold sourceHash
  cases query with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          dsimp only
          split
          · refine (SourceKeeps.lift (deferredQuery .snapshot)).bind _ fun backend => ?_
            refine SourceKeeps.get.bind _ fun source => ?_
            split
            · exact (sourceControl_sourceReleaseOpening P seeds e).bind _ (fun _ => hquery _)
            · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
          · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
      | _ => simpa only [pure_bind] using hquery _
  | _ => simpa only [pure_bind] using hquery _

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (point : Point) : SourceKeeps sourceControl (sourceVirtual P seeds T point) := by
  unfold sourceVirtual
  refine (SourceKeeps.lift (deferredQuery (.virtual T point))).bind _ fun _ => ?_
  cases point with
  | randomizer lay e =>
      dsimp only
      split
      · refine (SourceKeeps.lift (deferredQuery .snapshot)).bind _ fun backend => ?_
        refine SourceKeeps.get.bind _ fun source => ?_
        split
        · exact sourceControl_sourceReleaseOpening P seeds e
        · exact SourceKeeps.pure ()
      · exact SourceKeeps.pure ()
  | _ => exact SourceKeeps.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourcePending (P : PublicParameter) (p : PendingInput) :
    SourceKeeps (sourceControl (C := C)) (sourcePending P p) := by
  have tail (prior : Option DeferredOutput) : SourceKeeps sourceControl (do
      let value ← liftM (deferredQuery (C := C) (.pending p))
      if prior.isNone then modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
      pure value : SourceM C DeferredOutput) := by
    refine (SourceKeeps.lift (deferredQuery (.pending p))).bind _ fun value => ?_
    split
    · exact (SourceKeeps.modify (fun st => { st with allocated := st.allocated ++ [p] }) (fun _ => rfl)).bind _ (fun _ => SourceKeeps.pure value)
    · exact SourceKeeps.pure value
  unfold sourcePending
  refine (SourceKeeps.lift (deferredQuery (.inspect p))).bind _ fun prior => ?_
  refine SourceKeeps.get.bind _ fun source => ?_
  dsimp only
  split
  · refine (SourceKeeps.lift (deferredQuery (.hash (.hash _)))).bind _ fun value => ?_
    refine (SourceKeeps.lift (deferredQuery (.record p value))).bind _ fun _ => ?_
    exact (SourceKeeps.modify (fun st => { st with allocated := st.allocated ++ [p] }) (fun _ => rfl)).bind _ (fun _ => SourceKeeps.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (SourceKeeps.modify (fun st => { st with consistent := false }) (fun _ => rfl)).bind _ (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-- Every concrete backend source handler keeps these source-owned control fields. -/
theorem sourceControl_sourceBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) : SourceKeeps sourceControl (sourceBackend P seeds t) := by
  cases t with
  | hash query => exact sourceControl_sourceHash P seeds query
  | pending p => exact sourceControl_sourcePending P p
  | virtual T point => exact sourceControl_sourceVirtual P seeds T point
  | _ => exact SourceKeeps.lift _

theorem sourceControl_sourceHashProgram {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : OracleComp HashSpec α) : SourceKeeps sourceControl (sourceHashProgram P seeds oa) :=
  SourceKeeps.simulateQ (sourceBackend P seeds) (sourceControl_sourceBackend P seeds) (deferredHash oa)

theorem sourceControl_sourceBottomRow (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceKeeps sourceControl (sourceBottomRow P seeds e l) :=
  SourceKeeps.simulateQ (sourceBackend P seeds) (sourceControl_sourceBackend P seeds) (deferredBottomRow e l)

theorem sourceControl_sourceTopTree (P : PublicParameter) (seeds : C.Term → HashOutput) :
    SourceKeeps sourceControl (sourceTopTree P seeds) :=
  SourceKeeps.simulateQ (sourceBackend P seeds) (sourceControl_sourceBackend P seeds) (deferredTopTree P)

theorem sourceControl_sourceCommitment (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceKeeps sourceControl (sourceCommitment P seeds e) := by
  unfold sourceCommitment
  refine (SourceKeeps.mapM _ _ (fun T _ => sourceControl_sourceVirtual P seeds T _)).bind _ fun _ => ?_
  exact (sourceControl_sourcePending P (.commitment e)).bind _ (fun _ => SourceKeeps.pure _)

theorem sourceControl_sourceTopValue (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : Digit) :
    SourceKeeps sourceControl (sourceTopValue P seeds b l pos) := by
  unfold sourceTopValue
  refine (SourceKeeps.mapM _ _ (fun T _ => sourceControl_sourceVirtual P seeds T _)).bind _ fun _ => ?_
  exact (SourceKeeps.mapM _ _ (fun i _ => sourceControl_sourcePending P (.top b l _))).bind _
    (fun _ => SourceKeeps.pure _)

theorem sourceControl_sourceTopRecover (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (pos : Digit) (initial : DeferredDigest) :
    SourceKeeps (sourceControl (C := C)) (sourceTopRecover P b l pos initial) := by
  unfold sourceTopRecover
  refine (SourceKeeps.mapM _ _ (fun i _ => sourceControl_sourcePending P (.top b l _))).bind _
    fun values => ?_
  dsimp only
  split
  · exact SourceKeeps.pure _
  · exact (SourceKeeps.modify (field := sourceControl) (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
      (fun _ => SourceKeeps.pure _)

set_option backward.isDefEq.respectTransparency false in
/-- A full actual bottom build preserves binding, stored trees and adversary
control fields, on success as well as every early failure. -/
theorem sourceControl_sourceBottomTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourceKeeps sourceControl (sourceBottomTree P seeds top b) := by
  unfold sourceBottomTree
  refine (SourceKeeps.mapM _ _ (fun el _ => sourceControl_sourceBottomRow P seeds el.1 el.2)).bind _
    fun rows => ?_
  refine (SourceKeeps.mapM _ _ (fun key _ => sourceControl_sourceCommitment P seeds _)).bind _
    fun commitments => ?_
  refine (SourceKeeps.mapM _ _ (fun T _ => sourceControl_sourceVirtual P seeds T _)).bind _ fun _ => ?_
  refine (sourceControl_sourceHashProgram P seeds _).bind _ fun root => ?_
  refine (sourceControl_sourcePending P (.base topLayer (topKey b) (bytesLE 16 root))).bind _ fun base => ?_
  refine (sourceControl_sourceHashProgram P seeds _).bind _ fun found => ?_
  cases found with
  | none => exact SourceKeeps.pure none
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      refine (SourceKeeps.sequenceFin _ _ (fun l => sourceControl_sourceTopValue P seeds b l (encoding l))).bind _
        fun values => ?_
      refine (sourceControl_sourceHashProgram P seeds _).bind _ fun path => ?_
      refine (sourceControl_sourceHashProgram P seeds _).bind _ fun digest => ?_
      cases hd : Codeword.decode digest with
      | none =>
          dsimp only
          exact SourceKeeps.pure none
      | some checked =>
          dsimp only
          split
          · exact (SourceKeeps.modify (field := sourceControl) (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
              (fun _ => SourceKeeps.pure none)
          · refine (SourceKeeps.sequenceFin _ _
              (fun l => sourceControl_sourceTopRecover P b l (encoding l) (values l))).bind _ fun ends => ?_
            refine (sourceControl_sourceHashProgram P seeds _).bind _ fun leaf => ?_
            refine (sourceControl_sourceHashProgram P seeds _).bind _ fun root => ?_
            split <;> exact SourceKeeps.pure _

/-- Source control preservation transports the invariant of saved signatures. -/
theorem StoredTopShape.of_control {source source' : SourceState C}
    (h : StoredTopShape source) (hc : sourceControl source' = sourceControl source) :
    StoredTopShape source' := by
  have htrees := congrArg Prod.fst (congrArg Prod.snd hc)
  intro b tree ht
  apply h b tree
  change source'.trees = source.trees at htrees
  rw [htrees] at ht
  exact ht

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- D17 preserves the shape of every stored successful signature when it
inserts a new build or replays a stored success or failure. -/
theorem sourceBottomOnce_storedTopShape (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (top : TopTree) (b : XmssSecurity.TopIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hv : PendingValid backend.1.1.data) (hshape : StoredTopShape source)
    (r : (Option DeferredBottomTree × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceBottomOnce P seeds top b) source backend)) :
    StoredTopShape r.1.2 := by
  simp only [sourceBottomOnce, runSource_bind, runSource_get, pure_bind] at hr
  cases hb : source.trees b with
  | some prior =>
      simp only [hb, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hshape
  | none =>
      simp only [hb, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨built, hbuilt, modified, hmodified, hr⟩ := hr
      have hc := (sourceControl_sourceBottomTree P seeds top b).run P seeds q s source backend built (by with_reducible exact hbuilt)
      have ht := congrArg Prod.fst (congrArg Prod.snd hc)
      change built.1.2.trees = source.trees at ht
      rw [runSource_modify, mem_support_pure_iff] at hmodified
      subst modified
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      intro f tree hf
      change Function.update built.1.2.trees b (some built.1.1) f = some (some tree) at hf
      by_cases he : f = b
      · subst f
        rw [Function.update_self, Option.some.injEq] at hf
        exact sourceBottomTree_noBottomOpening P seeds q s top b source backend hv built hbuilt tree hf
      · rw [Function.update_of_ne he, ht] at hf
        exact hshape f tree hf

/-- Preservation of a joint invariant by the fixed source interpreter. -/
def SourcePreserves {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (I : SourceState C → CappedCompilerState C → Prop)
    (oa : SourceM C α) : Prop :=
  ∀ source backend, I source backend →
    ∀ r : (α × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s oa source backend) → I r.1.2 r.2

namespace SourcePreserves

variable {P : PublicParameter} {seeds : C.Term → HashOutput} {q : ℕ} {s : HiddenKey → Digest}
  {I : SourceState C → CappedCompilerState C → Prop}

theorem pure {α : Type} (value : α) : SourcePreserves P seeds q s I (Pure.pure value) := by
  intro source backend hs r hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  exact hs

theorem get : SourcePreserves P seeds q s I (get : SourceM C (SourceState C)) := by
  intro source backend hs r hr
  rw [runSource_get, mem_support_pure_iff] at hr
  subst r
  exact hs

theorem modify (f : SourceState C → SourceState C)
    (hf : ∀ source backend, I source backend → I (f source) backend) :
    SourcePreserves P seeds q s I (modify f : SourceM C Unit) := by
  intro source backend hs r hr
  rw [runSource_modify, mem_support_pure_iff] at hr
  subst r
  exact hf source backend hs

theorem bind {α β : Type} {oa : SourceM C α} (h : SourcePreserves P seeds q s I oa)
    (next : α → SourceM C β) (hn : ∀ value, SourcePreserves P seeds q s I (next value)) :
    SourcePreserves P seeds q s I (oa >>= next) := by
  intro source backend hs r hr
  rw [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact hn a.1.1 a.1.2 a.2 (h source backend hs a ha) r hr

theorem mapM {α β : Type} (items : List α) (oa : α → SourceM C β)
    (h : ∀ a ∈ items, SourcePreserves P seeds q s I (oa a)) :
    SourcePreserves P seeds q s I (items.mapM oa) :=
  runSource_mapM_inv P seeds q s oa I items h

theorem sequenceFin {α : Type} (n : ℕ) (oa : Fin n → SourceM C α)
    (h : ∀ i, SourcePreserves P seeds q s I (oa i)) :
    SourcePreserves P seeds q s I (Concrete.sequenceFin oa) :=
  runSource_sequenceFin_inv P seeds q s I n oa h

theorem simulateQ {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (SourceM C))
    (step : ∀ t, SourcePreserves P seeds q s I (impl t)) (oa : OracleComp spec α) :
    SourcePreserves P seeds q s I (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using SourcePreserves.pure (I := I) value
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (step t).bind _ ih

/-- A control-field frame preserves the shape of every saved successful tree. -/
theorem storedTopShape {α : Type} {oa : SourceM C α} (h : SourceKeeps sourceControl oa) :
    SourcePreserves P seeds q s (fun source _ => StoredTopShape source) oa := by
  intro source backend hs r hr
  exact hs.of_control (h.run P seeds q s source backend r hr)

theorem pendingValid {α : Type} (oa : SourceM C α) :
    SourcePreserves P seeds q s (fun _ backend => PendingValid backend.1.1.data) oa :=
  fun source backend hv r hr => runSource_pendingValid P seeds q s oa source backend hv r hr

end SourcePreserves

set_option backward.isDefEq.respectTransparency false in
/-- Raw deferred calls can change the flag but never the reveal wrapper's map. -/
theorem sourceReveals_deferredQuery (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C) :
    SourcePreserves P seeds q s (RevealRelation s) (liftM (deferredQuery t)) := by
  intro source backend hs r hr
  rw [runSource_liftM, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  simp only [deferredQuery, HasQuery.instOfMonadLift_query, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map,
    SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk, support_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact hs

/-- Silent completion leaves both reveal maps in place. -/
theorem sourceReveals_completePrf (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (target : Digest) :
    SourcePreserves P seeds q s (RevealRelation s) (liftM (completePrf seeds point target)) := by
  intro source backend hs r hr
  have hf := completePrf_frame P seeds q s point target source backend r hr
  have hsource := congrArg SourceState.revealed hf.1
  have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) hf.2.1
  exact hs.frame hsource hbackend

theorem sourceReveals_modify (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (f : SourceState C → SourceState C)
    (hf : ∀ source, (f source).revealed = source.revealed) :
    SourcePreserves P seeds q s (RevealRelation s) (modify f : SourceM C Unit) :=
  SourcePreserves.modify f (fun source _ h => h.frame (hf source) rfl)

theorem sourceReveals_sourceReveal (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (key : HiddenKey) :
    SourcePreserves P seeds q s (RevealRelation s) (sourceReveal key) :=
  fun source backend h r hr => (sourceReveal_correct P seeds q s key source backend h r hr).2.1

theorem sourceReveals_sourceRevealDigest (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (value : DeferredDigest) :
    SourcePreserves P seeds q s (RevealRelation s) (sourceRevealDigest value) :=
  fun source backend h r hr => (sourceRevealDigest_correct P seeds q s value source backend h r hr).2.1

theorem sourceReveals_sourcePlant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) :
    SourcePreserves P seeds q s (RevealRelation s) (sourcePlant P p) :=
  sourcePlant_revealRelation P seeds q s p

/-- P synchronizes reveals on every branch, independently of completion or
plant success. This is separate from the release-slack success invariant. -/
theorem sourceReveals_sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex) :
    SourcePreserves P seeds q s (RevealRelation s) (sourceReleaseOpening P seeds e) := by
  unfold sourceReleaseOpening
  refine SourcePreserves.get.bind _ fun source => ?_
  split
  · refine (sourceReveals_sourceReveal P seeds q s (.opening bottomLayer e)).bind _ fun value => ?_
    refine (sourceReveals_completePrf P seeds q s (.randomizer bottomLayer e) value).bind _ fun ok => ?_
    refine (sourceReveals_modify P seeds q s (fun st => { st with consistent := st.consistent && ok })
      (fun _ => rfl)).bind _ fun _ => ?_
    refine SourcePreserves.get.bind _ fun current => ?_
    exact (SourcePreserves.mapM _ (sourcePlant P) (fun p _ => sourceReveals_sourcePlant P seeds q s p)).bind _
      (fun _ => SourcePreserves.pure ())
  · exact SourcePreserves.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceReveals_sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (input : Query C) :
    SourcePreserves P seeds q s (RevealRelation s) (sourceHash P seeds input) := by
  have hquery (input : Query C) : SourcePreserves P seeds q s (RevealRelation s)
      (liftM (deferredQuery (.hash input)) : SourceM C HashOutput) := sourceReveals_deferredQuery P seeds q s _
  unfold sourceHash
  cases input with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          dsimp only
          split
          · refine (sourceReveals_deferredQuery P seeds q s .snapshot).bind _ fun backend => ?_
            refine SourcePreserves.get.bind _ fun source => ?_
            split
            · exact (sourceReveals_sourceReleaseOpening P seeds q s e).bind _ (fun _ => hquery _)
            · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
          · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
      | _ => simpa only [pure_bind] using hquery _
  | _ => simpa only [pure_bind] using hquery _

set_option backward.isDefEq.respectTransparency false in
theorem sourceReveals_sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (T : C.Term) (point : Point) :
    SourcePreserves P seeds q s (RevealRelation s) (sourceVirtual P seeds T point) := by
  unfold sourceVirtual
  refine (sourceReveals_deferredQuery P seeds q s (.virtual T point)).bind _ fun _ => ?_
  cases point with
  | randomizer lay e =>
      dsimp only
      split
      · refine (sourceReveals_deferredQuery P seeds q s .snapshot).bind _ fun backend => ?_
        refine SourcePreserves.get.bind _ fun source => ?_
        split
        · exact sourceReveals_sourceReleaseOpening P seeds q s e
        · exact SourcePreserves.pure ()
      · exact SourcePreserves.pure ()
  | _ => exact SourcePreserves.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceReveals_sourcePending (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) :
    SourcePreserves P seeds q s (RevealRelation s) (sourcePending P p) := by
  have tail (prior : Option DeferredOutput) : SourcePreserves P seeds q s (RevealRelation s) (do
      let value ← liftM (deferredQuery (C := C) (.pending p))
      if prior.isNone then modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
      pure value : SourceM C DeferredOutput) := by
    refine (sourceReveals_deferredQuery P seeds q s (.pending p)).bind _ fun value => ?_
    split
    · exact (sourceReveals_modify P seeds q s (fun st => { st with allocated := st.allocated ++ [p] })
        (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure value)
    · exact SourcePreserves.pure value
  unfold sourcePending
  refine (sourceReveals_deferredQuery P seeds q s (.inspect p)).bind _ fun prior => ?_
  refine SourcePreserves.get.bind _ fun source => ?_
  dsimp only
  split
  · refine (sourceReveals_deferredQuery P seeds q s (.hash (.hash _))).bind _ fun value => ?_
    refine (sourceReveals_deferredQuery P seeds q s (.record p value)).bind _ fun _ => ?_
    exact (sourceReveals_modify P seeds q s (fun st => { st with allocated := st.allocated ++ [p] })
      (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (sourceReveals_modify P seeds q s (fun st => { st with consistent := false })
        (fun _ => rfl)).bind _ (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-- Every concrete source backend handler preserves reveal synchronization. -/
theorem sourceReveals_sourceBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C) :
    SourcePreserves P seeds q s (RevealRelation s) (sourceBackend P seeds t) := by
  cases t with
  | hash input => exact sourceReveals_sourceHash P seeds q s input
  | pending p => exact sourceReveals_sourcePending P seeds q s p
  | virtual T point => exact sourceReveals_sourceVirtual P seeds q s T point
  | _ => exact sourceReveals_deferredQuery P seeds q s _

/-- A concrete PRF read is permitted by the source when its term is held by the
coalition, already cached, or at a bottom randomizer with an assigned message. -/
def SourceReadAllowed (seeds : C.Term → HashOutput) (source : SourceState C)
    (data : DeferredState C) (query : Query C) : Prop :=
  ∀ T point, query = .prf (seeds T) point →
    TprfSecurityProof.Revealed source.signing.corrupt (.inl T) ∨
      data.cache (.prf (seeds T) point) ≠ none ∨
      ∃ e, point = .randomizer bottomLayer e ∧ source.signing.bound e ≠ none

/-- Failure of P's readiness test provides a term untouched by the imminent
query, even when other terms are virtual or concretely cached. -/
theorem not_readyAfter_missing (seeds : C.Term → HashOutput) (data : DeferredState C)
    (source : SourceState C) (e : KeyIndex) (query : Query C)
    (hb : source.signing.bound e ≠ none)
    (hn : ¬ReadyAfter seeds data source.signing e query) :
    ∃ T, (T, Point.randomizer bottomLayer e) ∉ data.virtual ∧
      data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none ∧
      query ≠ .prf (seeds T) (.randomizer bottomLayer e) := by
  have hall : ¬∀ T : C.Term, (T, Point.randomizer bottomLayer e) ∈ data.virtual ∨
      (data.cache (.prf (seeds T) (.randomizer bottomLayer e))).isSome ∨
      query = .prf (seeds T) (.randomizer bottomLayer e) := fun ht => hn ⟨hb, ht⟩
  obtain ⟨T, hT⟩ := not_forall.mp hall
  refine ⟨T, fun hm => hT (Or.inl hm), ?_, fun he => hT (Or.inr (Or.inr he))⟩
  cases hc : data.cache (.prf (seeds T) (.randomizer bottomLayer e)) with
  | none => rfl
  | some value => exact (hT (Or.inr (Or.inl (by simp [hc])))).elim

/-- The PRF-read condition is retained by conservative cache growth and by
source operations that preserve the signing state. -/
theorem SourceReadAllowed.mono {seeds : C.Term → HashOutput}
    {source source' : SourceState C} {data data' : DeferredState C} {query : Query C}
    (h : SourceReadAllowed seeds source data query) (hs : source'.signing = source.signing)
    (hc : data.cache ≤ data'.cache) : SourceReadAllowed seeds source' data' query := by
  intro T point hq
  rcases h T point hq with ht | ht | ⟨e, he, hb⟩
  · exact Or.inl (hs ▸ ht)
  · apply Or.inr ∘ Or.inl
    obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp ht
    exact Option.ne_none_iff_exists'.mpr ⟨value, hc hv⟩
  · exact Or.inr (Or.inr ⟨e, he, hs ▸ hb⟩)

/-- A permitted concrete read preserves every release constraint when P has
already completed or its pre-read readiness test is false. -/
theorem ReleaseSlack.read {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlack seeds s source data) (query : Query C)
    (ha : SourceReadAllowed seeds source data query)
    (hready : ∀ e, (∃ seed, query = .prf seed (.randomizer bottomLayer e)) →
      PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
        ¬ReadyAfter seeds data source.signing e query)
    (hc : data.cache ≤ data'.cache)
    (hf : ∀ seed point, query ≠ .prf seed point →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads) :
    ReleaseSlack seeds s source data' := by
  have hu (point : Point) (unbound : ∀ e, point = .randomizer bottomLayer e →
      source.signing.bound e = none) (old : LackedUncached seeds source.signing.corrupt data point) :
      LackedUncached seeds source.signing.corrupt data' point := by
    intro T hT
    have hneq : query ≠ .prf (seeds T) point := by
      intro he
      rcases ha T point he with ht | ht | ⟨e, he, hb⟩
      · exact hT ht
      · exact ht (old T hT)
      · exact hb (unbound e he)
    exact (hf _ _ hneq).trans (old T hT)
  refine ⟨h.corrupt_bound, ?_, ?_, ?_, ?_, fun e he => (h.bottom_released e he).mono hc⟩
  · intro e
    rcases h.bottom_opening e with hd | ⟨hb, hl⟩ | ⟨hb, T, ht, hm⟩
    · exact Or.inl (hd.mono hc)
    · refine Or.inr (Or.inl ⟨hb, hu _ ?_ hl⟩)
      intro f he
      have hef := (Point.randomizer.inj he).2
      simpa only [← hef] using hb
    · by_cases hq : ∃ seed, query = .prf seed (.randomizer bottomLayer e)
      · rcases hready e hq with hd | hn
        · exact Or.inl (hd.mono hc)
        · obtain ⟨U, hvU, hcU, hqU⟩ := not_readyAfter_missing seeds data source e query hb hn
          exact Or.inr (Or.inr ⟨hb, U, hv ▸ hvU, (hf _ _ hqU).trans hcU⟩)
      · exact Or.inr (Or.inr ⟨hb, T, hv ▸ ht, (hf _ _ (fun he => hq ⟨seeds T, he⟩)).trans hm⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with ⟨hpad, hd⟩ | hl
    · refine Or.inl ⟨by simpa only [hp] using hpad, ?_⟩
      simpa only [bottomReleaseTarget, hp] using hd.mono hc
    · exact Or.inr (hu _ (fun e he => by cases he) hl)
  · intro b
    rcases h.top_opening b with hd | hl
    · exact Or.inl (hd.mono hc)
    · exact Or.inr (hu _ (fun e he => by cases he) hl)
  · intro b l
    rcases h.top_start b l with hd | hl
    · exact Or.inl (hd.mono hc)
    · exact Or.inr (hu _ (fun e he => by cases he) hl)

/-- The full counted and reveal-wrapped compiler preserves every concrete
cache entry through an individual supported call. -/
theorem cappedCompiler_cache_le (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
    backend.1.1.data.cache ≤ r.2.1.1.data.cache := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_cache_le P seeds t backend.1.1 b hb
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      exact le_rfl

/-- Conservative cache growth holds through any actual source continuation. -/
theorem runSource_cache_le {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (source : SourceState C) (backend : CappedCompilerState C)
    (r : (α × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s oa source backend)) :
    backend.1.1.data.cache ≤ r.2.1.1.data.cache :=
  simulateQ_sticky _ (fun st : CappedCompilerState C => backend.1.1.data.cache ≤ st.1.1.data.cache)
    (fun t st hs a ha => hs.trans (cappedCompiler_cache_le P seeds q s t st a ha))
    (oa.run source) backend le_rfl r hr

set_option backward.isDefEq.respectTransparency false in
/-- A hash call and its silent cached-extra trials do not alter virtual entries
or pads. The trials are allowed to extend the visible concrete cache. -/
theorem compiler_hash_virtual_pads (P : PublicParameter) (seeds : C.Term → HashOutput)
    (query : Query C) (backend : CompilerBackend C)
    (r : DeferredSpec C (.hash query) × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds (.hash query)).run backend)) :
    r.2.data.virtual = backend.data.virtual ∧ r.2.data.pads = backend.data.pads := by
  obtain ⟨a, ha, b, _, rfl⟩ := SigningCompilerPotential.compiler_hash_support P seeds query backend r hr
  simp only [deferredImpl, StateT.run, support_map] at ha
  obtain ⟨c, _, rfl⟩ := ha
  exact ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual counted raw read retains release slack under the precise source
read and P-readiness conditions. This includes silent cached-extra work. -/
theorem sourceRawHash_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (query : Query C)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (ha : SourceReadAllowed seeds source backend.1.1.data query)
    (hready : ∀ e, (∃ seed, query = .prf seed (.randomizer bottomLayer e)) →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
        ¬ReadyAfter seeds backend.1.1.data source.signing e query)
    (r : (HashOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (deferredQuery (.hash query))) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data := by
  rw [runSource_liftM, support_map] at hr
  obtain ⟨a, ha', rfl⟩ := hr
  simp only [deferredQuery, HasQuery.instOfMonadLift_query, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map,
    SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    StateT.run_mk, support_map] at ha'
  obtain ⟨b, ⟨c, hc, rfl⟩, rfl⟩ := ha'
  have hfields := compiler_hash_virtual_pads P seeds query backend.1.1 c hc
  exact hs.read query ha hready (compilerImpl_cache_le P seeds (.hash query) backend.1.1 c hc)
    (fun seed point hne => compilerImpl_prf_frame P seeds (.hash query) backend.1.1 c hc seed point hne)
    hfields.1 hfields.2

set_option backward.isDefEq.respectTransparency false in
/-- The release-aware source hash preserves release slack for permitted reads.
When the impending raw read would finish P, the actual source completes P
first and only then returns the counted concrete answer. -/
theorem sourceHash_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (query : Query C)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlack seeds s source backend.1.1.data)
    (ha : SourceReadAllowed seeds source backend.1.1.data query)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (HashOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceHash P seeds query) source backend)) :
    ReleaseSlack seeds s r.1.2 r.2.1.1.data := by
  have raw (hn : ∀ e, ¬∃ seed, query = .prf seed (.randomizer bottomLayer e))
      (hr : r ∈ support (runSource P seeds q s (liftM (deferredQuery (.hash query))) source backend)) :
      ReleaseSlack seeds s r.1.2 r.2.1.1.data :=
    sourceRawHash_slack P seeds q s query source backend hs ha
      (fun e he => (hn e he).elim) r hr
  cases query with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          by_cases hlay : lay = bottomLayer
          · subst lay
            simp only [sourceHash, ↓reduceIte, runSource_bind, runSource_snapshot,
              runSource_get, pure_bind] at hr
            split at hr
            · rename_i hready
              rw [runSource_bind, mem_support_bind_iff] at hr
              obtain ⟨released, hreleased, hr⟩ := hr
              have hp := sourceReleaseOpening_slack P seeds hinj q s e source backend hs hv hrev released hreleased
              have control := (sourceControl_sourceReleaseOpening P seeds e).run P seeds q s
                source backend released hreleased
              have hsign := congrArg Prod.fst control
              have hcache := runSource_cache_le P seeds q s (sourceReleaseOpening P seeds e)
                source backend released hreleased
              refine sourceRawHash_slack P seeds q s _ released.1.2 released.2 hp.1
                (ha.mono hsign hcache) ?_ r hr
              intro f hf
              obtain ⟨seed', he⟩ := hf
              have hef := (Point.randomizer.inj (Query.prf.inj he).2).2
              subst f
              exact Or.inl hp.2
            · rename_i hready
              refine sourceRawHash_slack P seeds q s _ source backend hs ha ?_ r hr
              intro f hf
              obtain ⟨seed', he⟩ := hf
              have hef := (Point.randomizer.inj (Query.prf.inj he).2).2
              subst f
              exact Or.inr hready
          · apply raw
            · intro f
              rintro ⟨seed', he⟩
              exact hlay (Point.randomizer.inj (Query.prf.inj he).2).1
            · simpa only [sourceHash, hlay, ↓reduceIte, pure_bind] using hr
      | _ =>
          apply raw
          · intro e
            rintro ⟨seed', he⟩
            cases (Query.prf.inj he).2
          · simpa only [sourceHash, pure_bind] using hr
  | _ =>
      apply raw
      · intro e
        rintro ⟨seed, he⟩
        cases he
      · simpa only [sourceHash, pure_bind] using hr

/-- The three invariants needed by actual release-aware hash calls. -/
def ReleaseInvariant (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (source : SourceState C) (backend : CappedCompilerState C) : Prop :=
  ReleaseSlack seeds s source backend.1.1.data ∧
    RevealRelation s source backend ∧ PendingValid backend.1.1.data

/-- Honest PRF code may read a fully cached point or an assigned bottom
randomizer. The second alternative relies on P's pre-read readiness check. -/
def PointReadable (seeds : C.Term → HashOutput) (source : SourceState C)
    (data : DeferredState C) (point : Point) : Prop :=
  (∀ T, data.cache (.prf (seeds T) point) ≠ none) ∨
    ∃ e, point = .randomizer bottomLayer e ∧ source.signing.bound e ≠ none

/-- Joint invariant for an honest computation whose PRF queries have one point. -/
def ReadInvariant (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C) : Prop :=
  ReleaseInvariant seeds s source backend ∧ PointReadable seeds source backend.1.1.data point

/-- Completed points are readable by the honest PRF evaluator. -/
theorem PointDone.readable {seeds : C.Term → HashOutput} {source : SourceState C}
    {data : DeferredState C} {point : Point} {target : Digest}
    (h : PointDone seeds data point target) : PointReadable seeds source data point :=
  Or.inl (fun T => Option.ne_none_iff_exists'.mpr (h.1 T))

theorem PointReadable.mono {seeds : C.Term → HashOutput} {source source' : SourceState C}
    {data data' : DeferredState C} {point : Point}
    (h : PointReadable seeds source data point) (hs : source'.signing = source.signing)
    (hc : data.cache ≤ data'.cache) : PointReadable seeds source' data' point := by
  rcases h with h | ⟨e, he, hb⟩
  · refine Or.inl (fun T => ?_)
    obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp (h T)
    exact Option.ne_none_iff_exists'.mpr ⟨value, hc hv⟩
  · exact Or.inr ⟨e, he, hs ▸ hb⟩

/-- A point-local honest query meets the concrete read condition without
requiring its seed to belong to a particular holder. -/
theorem PointReadable.allowed {seeds : C.Term → HashOutput} {source : SourceState C}
    {data : DeferredState C} {point : Point} (h : PointReadable seeds source data point)
    (query : Query C) (hq : ∀ seed p, query = .prf seed p → p = point) :
    SourceReadAllowed seeds source data query := by
  intro T p he
  have hp := hq (seeds T) p he
  subst p
  rcases h with hc | hb
  · exact Or.inr (Or.inl (hc T))
  · exact Or.inr (Or.inr hb)

/-- Actual source calls on one readable point preserve both release slack and
the permission needed by subsequent honest reads of that same point. -/
theorem sourceHash_readInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (point : Point) (query : Query C)
    (hquery : ∀ seed p, query = .prf seed p → p = point) :
    SourcePreserves P seeds q s (ReadInvariant seeds s point) (sourceHash P seeds query) := by
  intro source backend h r hr
  have control := (sourceControl_sourceHash P seeds query).run P seeds q s source backend r hr
  exact ⟨⟨sourceHash_slack P seeds hinj q s query source backend h.1.1
      (h.2.allowed query hquery) h.1.2.2 h.1.2.1 r hr,
    sourceReveals_sourceHash P seeds q s query source backend h.1.2.1 r hr,
    runSource_pendingValid P seeds q s (sourceHash P seeds query) source backend h.1.2.2 r hr⟩,
    h.2.mono (congrArg Prod.fst control)
      (runSource_cache_le P seeds q s (sourceHash P seeds query) source backend r hr)⟩

/-- A non-PRF hash query preserves the release invariant directly. -/
theorem sourceHash_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (query : Query C) (hquery : ∀ seed point, query ≠ .prf seed point) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceHash P seeds query) := by
  intro source backend h r hr
  exact ⟨sourceHash_slack P seeds hinj q s query source backend h.1
      (fun T p he => (hquery (seeds T) p he).elim) h.2.2 h.2.1 r hr,
    sourceReveals_sourceHash P seeds q s query source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s (sourceHash P seeds query) source backend h.2.2 r hr⟩

/-- Mapping a return value does not affect a preserved source invariant. -/
theorem SourcePreserves.map {α β : Type} {P : PublicParameter} {seeds : C.Term → HashOutput}
    {q : ℕ} {s : HiddenKey → Digest} {I : SourceState C → CappedCompilerState C → Prop}
    {oa : SourceM C α} (h : SourcePreserves P seeds q s I oa) (f : α → β) :
    SourcePreserves P seeds q s I (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind _ (fun value => SourcePreserves.pure (f value))

set_option backward.isDefEq.respectTransparency false in
/-- The actual full PRF evaluator reads only its given point, so the readable
point condition suffices throughout all its sequential concrete term reads. -/
theorem sourcePrfValue_readInvariant (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) :
    SourcePreserves P seeds q s (ReadInvariant seeds s point)
      (sourceRoProgram prims P seeds (prfValue seeds point)) := by
  simp only [sourceRoProgram, prfValue, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine (SourcePreserves.mapM _ _ (fun T _ => ?_)).bind _ (fun _ => SourcePreserves.pure _)
  simp only [prf, hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
  exact (sourceHash_readInvariant P seeds hinj q s point (.prf (seeds T) point)
    (fun seed p he => (Query.prf.inj he).2.symm)).map truncateHash

set_option backward.isDefEq.respectTransparency false in
/-- The actual partial PRF evaluator also reads only its given point. Its masks
are separate structured queries, so they preserve the same readable point. -/
theorem sourceEval_readInvariant (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (keys : Keys C) (i : C.Party) (J : C.Quorum)
    (point : Point) (message : Message) :
    SourcePreserves P seeds q s (ReadInvariant seeds s point)
      (sourceRoProgram prims P seeds (eval keys i J point message)) := by
  simp only [sourceRoProgram, eval, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine (SourcePreserves.mapM _ _ (fun T _ => ?_)).bind _ fun terms => ?_
  · simp only [prf, hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
    exact (sourceHash_readInvariant P seeds hinj q s point (.prf (keys.seed T) point)
      (fun seed p he => (Query.prf.inj he).2.symm)).map truncateHash
  · refine (SourcePreserves.mapM _ _ (fun j _ => ?_)).bind _ (fun _ => SourcePreserves.pure _)
    simp only [hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
    exact (sourceHash_readInvariant P seeds hinj q s point (.mask (keys.pairKey j) point message J)
      (fun seed p he => by cases he)).map truncateHash

/-- The round-1 and round-2 partial evaluator is the actual `eval` program with
the dealer's keys; it inherits the point-local read invariant. -/
theorem sourcePart_readInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest)
    (i : C.Party) (J : C.Quorum) (point : Point) (message : Message) :
    SourcePreserves x.1 x.2.1 q s (ReadInvariant x.2.1 s point)
      (sourcePart prims x i J point message) :=
  sourceEval_readInvariant prims x.1 x.2.1 hinj q s _ i J point message

/-- A down original hidden-key flag permits every canonical seed match of an
adversarial structured query; no injectivity assumption is needed here. -/
theorem sourceReadAllowed_of_no_hiddenHit (x : Keys3 C) (source : SourceState C)
    (data : DeferredState C) (query : Query C)
    (hh : SigningCoreProof.hiddenHit x source.signing.corrupt (.inr (.inl query)) = false) :
    SourceReadAllowed x.2.1 source data query := by
  intro T point he
  apply Or.inl
  by_contra ht
  have htrue := hiddenHit_lacked_prf x source.signing.corrupt T point ht
  rw [he] at hh
  rw [hh] at htrue
  cases htrue

set_option backward.isDefEq.respectTransparency false in
/-- Private uniform sampling has no source, cache or release effect. -/
theorem sourceUniform_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (n : ℕ) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (liftM (deferredQuery (C := C) (.uniform n))) := by
  intro source backend h r hr
  rw [runSource_deferredQuery_uncounted P seeds q s (.uniform n) (by exact not_false)] at hr
  simp only [compilerImpl, StateT.run, deferredImpl, Functor.map_map] at hr
  change r ∈ support ((fun value : Fin (n + 1) => ((value, source), backend)) <$>
    (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))) at hr
  rw [support_map] at hr
  obtain ⟨value, _, rfl⟩ := hr
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Each actual local adversary call preserves the release invariant whenever
its original hidden-key test is false. Its PRG branch retains the stream-key call. -/
theorem sourceLocal_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest)
    (t : (LocalSpec C).Domain) (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant x.2.1 s source backend)
    (hh : SigningCoreProof.hiddenHit x source.signing.corrupt t = false)
    (r : (LocalSpec C t × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceLocal prims x t) source backend)) :
    ReleaseInvariant x.2.1 s r.1.2 r.2 := by
  cases t with
  | inl n => exact sourceUniform_releaseInvariant x.1 x.2.1 q s n source backend h r hr
  | inr t =>
      cases t with
      | inl query =>
          exact ⟨sourceHash_slack x.1 x.2.1 hinj q s query source backend h.1
              (sourceReadAllowed_of_no_hiddenHit x source backend.1.1.data query hh) h.2.2 h.2.1 r hr,
            sourceReveals_sourceHash x.1 x.2.1 q s query source backend h.2.1 r hr,
            runSource_pendingValid x.1 x.2.1 q s _ source backend h.2.2 r hr⟩
      | inr inp =>
          exact ((sourceHash_releaseInvariant x.1 x.2.1 hinj q s (.streamKey inp.2.1)
              (fun _ _ he => by cases he)).bind _ (fun _ => SourcePreserves.pure _))
            source backend h r hr

/-- Updating fields outside signing and reveals preserves the joint release
invariant and has no backend effect. -/
theorem ReleaseInvariant.source_frame {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source source' : SourceState C} {backend : CappedCompilerState C}
    (h : ReleaseInvariant seeds s source backend)
    (hs : source'.signing = source.signing) (hr : source'.revealed = source.revealed) :
    ReleaseInvariant seeds s source' backend :=
  ⟨h.1.frame hs (fun _ _ => rfl) rfl rfl (fun _ he => hr ▸ he),
    h.2.1.frame hr rfl, h.2.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- At the original adversary boundary, a final down hidden-key flag supplies
the local no-hit premise. Thus the actual call, including its final flag and
candidate-log update, preserves the release invariant until that original flag. -/
theorem sourceOracles_local_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (t : (LocalSpec C).Domain) (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant x.2.1 s source backend)
    (r : (LocalSpec C t × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceOracles prims x top (.inl t)) source backend))
    (hflag : r.1.2.hiddenFlag = false) : ReleaseInvariant x.2.1 s r.1.2 r.2 := by
  have hlocal := sourceOracles_local_hiddenFlag prims x top q s t source backend r hr
  have hh : SigningCoreProof.hiddenHit x source.signing.corrupt t = false := by
    rw [hflag] at hlocal
    exact (Bool.or_eq_false_iff.mp hlocal.symm).2
  simp only [sourceOracles, runSource_bind, runSource_get, mem_support_bind_iff,
    mem_support_pure_iff] at hr
  obtain ⟨_, rfl, a, ha, b, hb, hr⟩ := hr
  have hi := sourceLocal_releaseInvariant prims x hinj q s t source backend h hh a ha
  rw [runSource_modify, mem_support_pure_iff] at hb
  subst b
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  exact hi.source_frame rfl rfl

/-- Source-only updates that preserve signing and reveal maps preserve the
joint release invariant. -/
theorem sourceModify_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (f : SourceState C → SourceState C)
    (hs : ∀ source, (f source).signing = source.signing)
    (hr : ∀ source, (f source).revealed = source.revealed) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (modify f : SourceM C Unit) :=
  SourcePreserves.modify f (fun source _ h => h.source_frame (hs source) (hr source))

set_option backward.isDefEq.respectTransparency false in
/-- A raw pending read changes only the pending table and count; it preserves
release slack on both the cached and fresh sampling branches. -/
theorem sourceRawPending_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (liftM (deferredQuery (C := C) (.pending p))) := by
  intro source backend h r hr
  refine ⟨?_, sourceReveals_deferredQuery P seeds q s (.pending p) source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2 r hr⟩
  rw [runSource_deferredQuery_no_candidate P seeds q s (.pending p) rfl] at hr
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | some value =>
      simp only [deferredImpl, hp, mem_support_pure_iff] at hb
      subst b
      exact h.1
  | none =>
      simp only [deferredImpl, hp, support_map] at hb
      obtain ⟨value, _, rfl⟩ := hb
      exact h.1.frame rfl (fun _ _ => rfl) rfl rfl (fun _ he => he)

set_option backward.isDefEq.respectTransparency false in
/-- Pending inspection is read-only for both source and backend. -/
theorem sourceInspect_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (liftM (deferredQuery (C := C) (.inspect p))) := by
  intro source backend h r hr
  rw [runSource_inspect, mem_support_pure_iff] at hr
  subst r
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Recording a concrete post-release pending answer changes no PRF entry,
virtual slot or pad. -/
theorem sourceRecord_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) (value : HashOutput) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (liftM (deferredQuery (C := C) (.record p value))) := by
  intro source backend h r hr
  refine ⟨?_, sourceReveals_deferredQuery P seeds q s (.record p value) source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2 r hr⟩
  rw [runSource_deferredQuery_uncounted P seeds q s (.record p value) (by exact not_false)] at hr
  simp only [compilerImpl, deferredImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  simp only [mem_support_pure_iff] at hb
  subst b
  exact h.1.frame rfl (fun _ _ => rfl) rfl rfl (fun _ he => he)

set_option backward.isDefEq.respectTransparency false in
/-- The actual pending handler preserves the release invariant, including its
concrete hash/cache fallback after an opening has already been revealed. -/
theorem sourcePending_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (p : PendingInput) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourcePending P p) := by
  have tail (prior : Option DeferredOutput) : SourcePreserves P seeds q s (ReleaseInvariant seeds s) (do
      let value ← liftM (deferredQuery (C := C) (.pending p))
      if prior.isNone then modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
      pure value : SourceM C DeferredOutput) := by
    refine (sourceRawPending_releaseInvariant P seeds q s p).bind _ fun value => ?_
    split
    · exact (sourceModify_releaseInvariant P seeds q s (fun st => { st with allocated := st.allocated ++ [p] })
        (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure value)
    · exact SourcePreserves.pure value
  unfold sourcePending
  refine (sourceInspect_releaseInvariant P seeds q s p).bind _ fun prior => ?_
  refine SourcePreserves.get.bind _ fun source => ?_
  dsimp only
  split
  · rename_i priorCopy known next input hknown hnext
    have hhash := sourceHash_releaseInvariant P seeds hinj q s (.hash (p.input P input))
        (fun _ _ he => by cases he)
    simp only [sourceHash, pure_bind] at hhash
    refine hhash.bind _ fun value => ?_
    refine (sourceRecord_releaseInvariant P seeds q s p value).bind _ fun _ => ?_
    exact (sourceModify_releaseInvariant P seeds q s (fun st => { st with allocated := st.allocated ++ [p] })
      (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (sourceModify_releaseInvariant P seeds q s (fun st => { st with consistent := false })
        (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-- The actual virtual call, including its P release check, preserves the joint
release invariant. -/
theorem sourceVirtual_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (T : C.Term) (point : Point) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceVirtual P seeds T point) := by
  intro source backend h r hr
  exact ⟨sourceVirtual_slack P seeds hinj q s T point source backend h.1 h.2.2 h.2.1 r hr,
    sourceReveals_sourceVirtual P seeds q s T point source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2 r hr⟩

/-- Both fresh and cached pad reads preserve the joint release invariant. -/
theorem sourcePad_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (liftM (deferredQuery (C := C) (.pad point))) := by
  intro source backend h r hr
  exact ⟨(sourcePad_slack P seeds q s point source backend h.1 r hr).1,
    sourceReveals_deferredQuery P seeds q s (.pad point) source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2 r hr⟩

/-- A typed hash program has no PRF reads, so every actual source call preserves
the joint release invariant. -/
theorem sourceHashProgram_releaseInvariant {α : Type} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (q : ℕ) (s : HiddenKey → Digest) (oa : OracleComp HashSpec α) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceHashProgram P seeds oa) := by
  unfold sourceHashProgram deferredHash
  induction oa using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact SourcePreserves.pure value
  | query_bind input next ih =>
      simp only [simulateQ_bind, backendQuery, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact (sourceHash_releaseInvariant P seeds hinj q s (.hash input)
        (fun _ _ he => by cases he)).bind _ ih

set_option backward.isDefEq.respectTransparency false in
/-- The actual six-call bottom row preserves release slack through its virtual
PRF terms, both public pads and each repeated pending-prefix read. -/
theorem sourceBottomRow_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceBottomRow P seeds e l) := by
  simp only [sourceBottomRow, deferredBottomRow, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_pure, backendQuery, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  refine (SourcePreserves.mapM _ _ (fun t ht => ?_)).bind _ fun _ => ?_
  · obtain ⟨pos, _, hm⟩ := List.mem_flatMap.mp ht
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hm
    exact (sourceVirtual_releaseInvariant P seeds hinj q s T _).bind _ (fun _ => SourcePreserves.pure ())
  · refine (sourcePad_releaseInvariant P seeds q s _).bind _ fun first => ?_
    refine (sourcePad_releaseInvariant P seeds q s _).bind _ fun second => ?_
    exact (SourcePreserves.mapM _ _ (fun p _ => sourcePending_releaseInvariant P seeds hinj q s p)).bind _
      (fun _ => SourcePreserves.pure _)

set_option backward.isDefEq.respectTransparency false in
/-- A top-chain build reads its virtual starting terms and three pending edges
without revealing those chain inputs. -/
theorem sourceTopEnd_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (simulateQ (sourceBackend P seeds) (deferredTopEnd b l)) := by
  simp only [deferredTopEnd, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_pure, backendQuery, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, sourceBackend]
  refine (SourcePreserves.mapM _ _ (fun T _ => sourceVirtual_releaseInvariant P seeds hinj q s T _)).bind _ fun _ => ?_
  refine (sourcePending_releaseInvariant P seeds hinj q s _).bind _ fun _ => ?_
  refine (sourcePending_releaseInvariant P seeds hinj q s _).bind _ fun _ => ?_
  exact (sourcePending_releaseInvariant P seeds hinj q s _).bind _ (fun _ => SourcePreserves.pure _)

/-- The full actual top-tree setup preserves the joint release invariant. -/
theorem sourceTopTree_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceTopTree P seeds) := by
  simp only [sourceTopTree, deferredTopTree, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine (SourcePreserves.mapM _ _ (fun bl _ => sourceTopEnd_releaseInvariant P seeds hinj q s bl.1 bl.2)).bind _
    fun ends => ?_
  exact (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ (fun _ => SourcePreserves.pure _)

/-- A commitment can trigger P during its virtual terms; the subsequent pending
call keeps the concrete cache fallback and preserves release slack. -/
theorem sourceCommitment_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceCommitment P seeds e) := by
  unfold sourceCommitment
  refine (SourcePreserves.mapM _ _ (fun T _ => sourceVirtual_releaseInvariant P seeds hinj q s T _)).bind _ fun _ => ?_
  exact (sourcePending_releaseInvariant P seeds hinj q s _).bind _ (fun _ => SourcePreserves.pure _)

/-- The stored symbolic top-signature prefix preserves the joint release invariant. -/
theorem sourceTopValue_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : Digit) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceTopValue P seeds b l pos) := by
  unfold sourceTopValue
  refine (SourcePreserves.mapM _ _ (fun T _ => sourceVirtual_releaseInvariant P seeds hinj q s T _)).bind _ fun _ => ?_
  exact (SourcePreserves.mapM _ _ (fun _ _ => sourcePending_releaseInvariant P seeds hinj q s _)).bind _
    (fun _ => SourcePreserves.pure _)

/-- The verification suffix of a stored symbolic top signature preserves the
joint release invariant even on its consistency-failure branch. -/
theorem sourceTopRecover_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : Digit) (initial : DeferredDigest) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceTopRecover P b l pos initial) := by
  unfold sourceTopRecover
  refine (SourcePreserves.mapM _ _ (fun _ _ => sourcePending_releaseInvariant P seeds hinj q s _)).bind _ fun values => ?_
  dsimp only
  split
  · exact SourcePreserves.pure _
  · exact (sourceModify_releaseInvariant P seeds q s (fun st => { st with consistent := false })
      (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual bottom-tree construction preserves release slack and
both synchronization invariants, on successful builds and on every failure path. -/
theorem sourceBottomTree_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceBottomTree P seeds top b) := by
  unfold sourceBottomTree
  refine (SourcePreserves.mapM _ _ (fun el _ => sourceBottomRow_releaseInvariant P seeds hinj q s el.1 el.2)).bind _
    fun rows => ?_
  refine (SourcePreserves.mapM _ _ (fun k _ => sourceCommitment_releaseInvariant P seeds hinj q s (bottomKey b k))).bind _
    fun commitments => ?_
  refine (SourcePreserves.mapM _ _ (fun T _ => sourceVirtual_releaseInvariant P seeds hinj q s T _)).bind _
    fun _ => ?_
  refine (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ fun root => ?_
  refine (sourcePending_releaseInvariant P seeds hinj q s _).bind _ fun base => ?_
  refine (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ fun found => ?_
  cases found with
  | none => exact SourcePreserves.pure none
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      refine (SourcePreserves.sequenceFin _ _
        (fun l => sourceTopValue_releaseInvariant P seeds hinj q s b l (encoding l))).bind _ fun values => ?_
      refine (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ fun path => ?_
      refine (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ fun digest => ?_
      cases hd : Codeword.decode digest with
      | none =>
          dsimp only
          exact SourcePreserves.pure none
      | some checked =>
          dsimp only
          split
          · exact (sourceModify_releaseInvariant P seeds q s (fun st => { st with consistent := false })
              (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure none)
          · refine (SourcePreserves.sequenceFin _ _
              (fun l => sourceTopRecover_releaseInvariant P seeds hinj q s b l (encoding l) (values l))).bind _ fun ends => ?_
            refine (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ fun leaf => ?_
            refine (sourceHashProgram_releaseInvariant P seeds hinj q s _).bind _ fun root => ?_
            split <;> exact SourcePreserves.pure _

/-- D17's fresh build and stored success or failure branches all preserve the
joint release invariant. -/
theorem sourceBottomOnce_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceBottomOnce P seeds top b) := by
  unfold sourceBottomOnce
  refine SourcePreserves.get.bind _ fun source => ?_
  cases source.trees b with
  | some tree => exact SourcePreserves.pure tree
  | none =>
      refine (sourceBottomTree_releaseInvariant P seeds hinj q s top b).bind _ fun tree => ?_
      exact (sourceModify_releaseInvariant P seeds q s
        (fun st => { st with trees := Function.update st.trees b (some tree) })
        (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure tree)

/-- Forgetting virtual slots in a comparison state preserves every release
constraint; concrete entries and all targets remain unchanged. -/
theorem ReleaseSlack.virtual_subset {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (virtual : Finset (C.Term × Point))
    (hv : virtual ⊆ data.virtual) : ReleaseSlack seeds s source { data with virtual := virtual } := by
  refine ⟨h.corrupt_bound, ?_, h.bottom_chain, h.top_opening, h.top_start, h.bottom_released⟩
  intro e
  rcases h.bottom_opening e with hd | ⟨hb, hu⟩ | ⟨hb, T, ht, hc⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨hb, hu⟩)
  · exact Or.inr (Or.inr ⟨hb, T, fun hm => ht (hv hm), hc⟩)

/-- Updating the source binding needs only the release alternative at that
one key; every other key's message binding and release constraint is unchanged. -/
theorem ReleaseSlack.bind {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex) (message : Message)
    (he : PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
      ∃ T : C.Term, (T, Point.randomizer bottomLayer e) ∉ data.virtual ∧
        data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none) :
    ReleaseSlack seeds s { source with signing :=
      { source.signing with bound := Function.update source.signing.bound e (some message) } } data := by
  refine ⟨h.corrupt_bound, ?_, h.bottom_chain, h.top_opening, h.top_start, h.bottom_released⟩
  intro f
  by_cases hfe : f = e
  · subst f
    rcases he with hd | hm
    · exact Or.inl hd
    · exact Or.inr (Or.inr ⟨by simp, hm⟩)
  · rcases h.bottom_opening f with hd | ⟨hb, hu⟩ | ⟨hb, hm⟩
    · exact Or.inl hd
    · exact Or.inr (Or.inl ⟨by simpa only [Function.update_of_ne hfe] using hb, hu⟩)
    · exact Or.inr (Or.inr ⟨by simpa only [Function.update_of_ne hfe] using hb, hm⟩)

/-- If binding does not make P ready, the actual unchanged backend already
supplies a stable release-slack boundary. -/
theorem ReleaseSlack.bind_unready {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex) (message : Message)
    (hn : ¬OpeningReady seeds data
      { source.signing with bound := Function.update source.signing.bound e (some message) } e) :
    ReleaseSlack seeds s { source with signing :=
      { source.signing with bound := Function.update source.signing.bound e (some message) } } data := by
  apply h.bind e message
  apply Or.inr
  have hall : ¬∀ T : C.Term, (T, Point.randomizer bottomLayer e) ∈ data.virtual ∨
      (data.cache (.prf (seeds T) (.randomizer bottomLayer e))).isSome :=
    fun ht => hn ⟨by simp, ht⟩
  obtain ⟨T, hT⟩ := not_forall.mp hall
  refine ⟨T, fun hm => hT (Or.inl hm), ?_⟩
  cases hc : data.cache (.prf (seeds T) (.randomizer bottomLayer e)) with
  | none => rfl
  | some value => exact (hT (Or.inr (by simp [hc]))).elim

/-- A newly bound key always has a valid comparison state for P: erase only
that key's virtual slots in the comparison, keeping the actual backend intact.
P's existing frame theorem ignores precisely those selected virtual slots. -/
theorem ReleaseSlack.bind_filtered {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlack seeds s source data) (e : KeyIndex) (message : Message) :
    ReleaseSlack seeds s { source with signing :=
      { source.signing with bound := Function.update source.signing.bound e (some message) } }
      { data with virtual := data.virtual.filter (fun tp => tp.2 ≠ .randomizer bottomLayer e) } := by
  apply (h.virtual_subset _ (Finset.filter_subset _ _)).bind e message
  rcases h.bottom_opening e with hd | ⟨_, hu⟩ | ⟨_, T, _, hc⟩
  · exact Or.inl hd
  · obtain ⟨T, hT⟩ := exists_lacked_term source.signing.corrupt h.corrupt_bound
    exact Or.inr ⟨T, fun hm => (Finset.mem_filter.mp hm).2 rfl, hu T hT⟩
  · exact Or.inr ⟨T, fun hm => (Finset.mem_filter.mp hm).2 rfl, hc⟩

/-- P after the source binds a key runs on the actual backend, even if all its
missing concrete terms were already virtual at the binding boundary. -/
theorem sourceReleaseOpening_after_bind (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (message : Message) (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant seeds s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseOpening P seeds e)
      { source with signing := { source.signing with bound := Function.update source.signing.bound e (some message) } }
      backend)) :
    ReleaseInvariant seeds s r.1.2 r.2 ∧
      PointDone seeds r.2.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) := by
  have hrev : RevealRelation s
      { source with signing := { source.signing with bound := Function.update source.signing.bound e (some message) } }
      backend := h.2.1
  have hp := sourceReleaseOpening_slack_frame P seeds hinj q s e _ backend _
    (h.1.bind_filtered e message) (fun _ _ => rfl) (by
      intro f hfe T
      simp only [Finset.mem_filter]
      refine ⟨fun hm => ⟨hm, ?_⟩, And.left⟩
      intro he
      exact hfe (Point.randomizer.inj he).2) rfl h.2.2 hrev r hr
  exact ⟨⟨hp.1, sourceReveals_sourceReleaseOpening P seeds q s e _ backend hrev r hr,
    runSource_pendingValid P seeds q s _ _ backend h.2.2 r hr⟩, hp.2⟩

/-- The actual write-once backend binding has no data-cache or release effect. -/
theorem runSource_bindKey (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (e : KeyIndex) (message : Message)
    (source : SourceState C) (backend : CappedCompilerState C) :
    runSource P seeds q s (liftM (deferredQuery (C := C) (.bindKey e message))) source backend =
      pure (((), source), (({ backend.1.1 with bound := (if backend.1.1.bound e = none then Function.update backend.1.1.bound e (some message) else backend.1.1.bound) }, backend.1.2), backend.2)) := by
  rw [runSource_deferredQuery_uncounted P seeds q s (.bindKey e message) (by exact not_false)]
  simp only [compilerImpl, StateT.run, map_pure]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual round-1 handler preserves the joint release invariant through
its guards, source and backend binding, immediate P check, and honest partial
PRF evaluation. This covers binding after every term was made virtual. -/
theorem sourceRound1_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) :
    SourcePreserves x.1 x.2.1 q s (ReleaseInvariant x.2.1 s)
      (sourceTsig prims x top (.round1 i J e message)) := by
  intro source backend h r hr
  have part (source' : SourceState C) (backend' : CappedCompilerState C)
      (h' : ReleaseInvariant x.2.1 s source' backend')
      (hp : PointReadable x.2.1 source' backend'.1.1.data (.randomizer bottomLayer e))
      (hr' : r ∈ support (runSource x.1 x.2.1 q s
        (some <$> sourcePart prims x i J (.randomizer bottomLayer e) message) source' backend')) :
      ReleaseInvariant x.2.1 s r.1.2 r.2 :=
    (((sourcePart_readInvariant prims x hinj q s i J (.randomizer bottomLayer e) message).map some)
      source' backend' ⟨h', hp⟩ r hr').1
  simp only [sourceTsig, runSource_bind, runSource_get, pure_bind] at hr
  split at hr
  · rw [runSource_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  · simp only [runSource_bind, runSource_modify, runSource_bindKey, runSource_snapshot, runSource_get, pure_bind] at hr
    let assigned : SourceState C := { source with signing :=
      { source.signing with bound := Function.update source.signing.bound e (some message) } }
    let boundBackend : CappedCompilerState C := (({ backend.1.1 with bound := (if backend.1.1.bound e = none then Function.update backend.1.1.bound e (some message) else backend.1.1.bound) }, backend.1.2), backend.2)
    have hbase : ReleaseInvariant x.2.1 s source boundBackend := h
    split at hr
    · rename_i hready
      rw [runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨released, hreleased, hr⟩ := hr
      have hp := sourceReleaseOpening_after_bind x.1 x.2.1 hinj q s e message source boundBackend hbase
        released (by with_reducible exact hreleased)
      exact part released.1.2 released.2 hp.1 hp.2.readable hr
    · rename_i hready
      have hs : ReleaseSlack x.2.1 s assigned boundBackend.1.1.data := h.1.bind_unready e message hready
      have hi : ReleaseInvariant x.2.1 s assigned boundBackend := ⟨hs, h.2⟩
      exact part assigned boundBackend hi (Or.inr ⟨e, rfl, by simp [assigned]⟩) hr

/-- Every canonical term at a point has a concrete cached answer. -/
def PrfPointCached (seeds : C.Term → HashOutput) (data : DeferredState C) (point : Point) : Prop :=
  ∀ T, data.cache (.prf (seeds T) point) ≠ none

theorem PrfPointCached.mono {seeds : C.Term → HashOutput} {data data' : DeferredState C}
    {point : Point} (h : PrfPointCached seeds data point) (hc : data.cache ≤ data'.cache) :
    PrfPointCached seeds data' point := by
  intro T
  obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp (h T)
  exact Option.ne_none_iff_exists'.mpr ⟨value, hc hv⟩

/-- A sequence of actual source operations retains every point completed by
one of its operations, because all intervening concrete caches grow. -/
theorem runSource_mapM_cached {α β : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (items : List α) (oa : α → SourceM C β)
    (point : α → Point)
    (step : ∀ a ∈ items, ∀ source backend, ReleaseInvariant seeds s source backend →
      ∀ r : (β × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (oa a) source backend) →
        ReleaseInvariant seeds s r.1.2 r.2 ∧ PrfPointCached seeds r.2.1.1.data (point a))
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant seeds s source backend)
    (r : (List β × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (items.mapM oa) source backend)) :
    ReleaseInvariant seeds s r.1.2 r.2 ∧
      ∀ a ∈ items, PrfPointCached seeds r.2.1.1.data (point a) := by
  induction items generalizing source backend r with
  | nil =>
      simp only [List.mapM_nil, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨h, fun _ hm => (List.not_mem_nil hm).elim⟩
  | cons a items ih =>
      simp only [List.mapM_cons, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      have hh := step a (List.mem_cons_self ..) source backend h head hhead
      have ht := ih (fun a ha => step a (List.mem_cons_of_mem _ ha)) head.1.2 head.2 hh.1 tail htail
      refine ⟨ht.1, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hh.2.mono (runSource_cache_le P seeds q s (items.mapM oa) head.1.2 head.2 tail htail)
      · exact ht.2 b hb

set_option backward.isDefEq.respectTransparency false in
/-- After actual Q, every canonical suffix point is concretely cached. This
supplies the honest `eval`/`prfValue` precondition for any returned position. -/
theorem sourceReleaseBottomSuffix_cached (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant seeds s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseBottomSuffix P seeds e l start) source backend)) :
    ∀ pos : XmssSecurity.ChainStep, start.val ≤ pos.val →
      PrfPointCached seeds r.2.1.1.data
        (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos)) := by
  rw [sourceReleaseBottomSuffix_eq] at hr
  simp only [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨completed, hcompleted, planted, hplanted, hr⟩ := hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  have hc := runSource_mapM_cached P seeds q s _ (sourceBottomCompletion P seeds e l)
    (fun pos => .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))
    (fun pos _ source backend hi a ha => by
      have hs := sourceBottomCompletion_slack P seeds hinj q s e l pos source backend hi.1 hi.2.1 a ha
      exact ⟨⟨hs.1, sourceBottomCompletion_revealRelation P seeds q s e l pos source backend hi.1 hi.2.1 a ha,
        runSource_pendingValid P seeds q s _ source backend hi.2.2 a ha⟩,
        fun T => Option.ne_none_iff_exists'.mpr (hs.2.1 T)⟩)
    source backend h completed hcompleted
  intro pos hpos
  have hm : pos ∈ (List.finRange 3).filter (fun p => start.val ≤ p.val) := by simp [hpos]
  exact (hc.2 pos hm).mono (runSource_cache_le P seeds q s _ completed.1.2 completed.2 planted hplanted)

/-- Q at a nonterminal position makes the exact requested point readable. -/
theorem sourceReleaseBottomSuffix_readable (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) (hstart : start.val < 3)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant seeds s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseBottomSuffix P seeds e l start) source backend)) :
    ReadInvariant seeds s (.chain bottomLayer e l start) r.1.2 r.2 := by
  refine ⟨sourceReleaseBottomSuffix_slack P seeds hinj q s e l start source backend h.1 h.2.1 h.2.2 r hr, Or.inl ?_⟩
  have hc := sourceReleaseBottomSuffix_cached P seeds hinj q s e l start source backend h r hr
    ⟨start.val, hstart⟩ (Nat.le_refl _)
  exact hc

set_option backward.isDefEq.respectTransparency false in
/-- R leaves its opening point concretely cached before the tree oracle runs
its counted full PRF read. All later plants and chain releases preserve it. -/
theorem sourceReturnTree_opening_cached (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant seeds s source backend)
    (r : ((BottomTree × Digest) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReturnTree P seeds b tree) source backend)) :
    PrfPointCached seeds r.2.1.1.data (.randomizer topLayer (topKey b)) := by
  rw [sourceReturnTree_eq, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨opening, hopening, hr⟩ := hr
  have ho := sourceTopCompletion_slack P seeds hinj q s b none source backend h.1 h.2.1 opening hopening
  have hc : PrfPointCached seeds opening.2.1.1.data (.randomizer topLayer (topKey b)) :=
    fun T => Option.ne_none_iff_exists'.mpr (ho.2.2.2.1 T)
  exact hc.mono (runSource_cache_le P seeds q s _ opening.1.2 opening.2 r hr)

/-- A projection of preserved source fields is itself preserved. -/
theorem SourceKeeps.comp {α β γ : Type} {field : SourceState C → β} {oa : SourceM C α}
    (h : SourceKeeps field oa) (f : β → γ) : SourceKeeps (fun st => f (field st)) oa :=
  fun source r hr => congrArg f (h source r hr)

/-- D17 updates the saved-tree table while retaining the caller's signing state. -/
theorem sourceSigning_sourceBottomOnce (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourceKeeps (SourceState.signing (C := C)) (sourceBottomOnce P seeds top b) := by
  unfold sourceBottomOnce
  refine SourceKeeps.get.bind _ fun source => ?_
  cases source.trees b with
  | some tree => exact SourceKeeps.pure tree
  | none =>
      refine ((sourceControl_sourceBottomTree P seeds top b).comp Prod.fst).bind _ fun tree => ?_
      exact (SourceKeeps.modify (fun st => { st with trees := Function.update st.trees b (some tree) })
        (fun _ => rfl)).bind _ (fun _ => SourceKeeps.pure tree)

set_option backward.isDefEq.respectTransparency false in
/-- The actual tree oracle builds or replays its D17 result, runs R only on a
successful result, and then reads the already-completed top opening point. -/
theorem sourceTree_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (b : XmssSecurity.TopIndex) (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant x.2.1 s source backend) (hshape : StoredTopShape source)
    (r : (TsigSpec C (.tree b) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceTsig prims x top (.tree b)) source backend)) :
    ReleaseInvariant x.2.1 s r.1.2 r.2 := by
  simp only [sourceTsig, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨built, hbuilt, hr⟩ := hr
  have hb := sourceBottomOnce_releaseInvariant x.1 x.2.1 hinj q s top b source backend h built hbuilt
  cases ht : built.1.1 with
  | none =>
      simp only [ht, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hb
  | some tree =>
      have shape := sourceBottomOnce_noBottomOpening x.1 x.2.1 q s top b source backend h.2.2 hshape built hbuilt tree ht
      simp only [ht, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨returned, hreturned, opened, hopened, hr⟩ := hr
      have ret := sourceReturnTree_slack x.1 x.2.1 hinj q s b tree shape built.1.2 built.2 hb.1 hb.2.1 hb.2.2 returned hreturned
      have cached := sourceReturnTree_opening_cached x.1 x.2.1 hinj q s b tree built.1.2 built.2 hb returned hreturned
      have ho := sourcePrfValue_readInvariant prims x.1 x.2.1 hinj q s (.randomizer topLayer (topKey b))
        returned.1.2 returned.2 ⟨ret, Or.inl cached⟩ opened hopened
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ho.1

/-- Typed hashes interpreted through the honest RO interface preserve the
release invariant, including the stream-key routing of that interface. -/
theorem sourceTweakable_releaseInvariant {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (oa : OracleComp HashSpec α) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceRoProgram prims P seeds (tweakable oa)) := by
  unfold sourceRoProgram tweakable
  induction oa using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact SourcePreserves.pure value
  | query_bind input next ih =>
      simp only [simulateQ_bind, hashQuery, HasQuery.instOfMonadLift_query,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact (sourceHash_releaseInvariant P seeds hinj q s (.hash input)
        (fun _ _ he => by cases he)).bind _ ih

/-- The actual codeword check/search contains only typed hashes. -/
theorem sourceCodeword_releaseInvariant (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (commitment : Digest) (e : KeyIndex) (message : Message) (opening : Digest) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s)
      (sourceRoProgram prims P seeds (signCodeword P commitment e message opening)) :=
  sourceTweakable_releaseInvariant prims P seeds hinj q s _

/-- Q supplies the exact point permission needed by the following actual
partial PRF evaluation in the round-2 callback. -/
theorem sourcePart_after_Q (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (l : ChainIndex) (pos : Digit)
    (hpos : pos.val < 3) (message : Message) :
    SourcePreserves x.1 x.2.1 q s (ReleaseInvariant x.2.1 s) (do
      sourceReleaseBottomSuffix x.1 x.2.1 e l pos
      sourcePart prims x i J (.chain bottomLayer e l pos) message) := by
  intro source backend h r hr
  rw [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨released, hreleased, hr⟩ := hr
  have hp := sourceReleaseBottomSuffix_readable x.1 x.2.1 hinj q s e l pos hpos source backend h released hreleased
  exact (sourcePart_readInvariant prims x hinj q s i J (.chain bottomLayer e l pos) message
    released.1.2 released.2 hp r hr).1

/-- The fixed actual round-2 callback reveals Q before each nonterminal PRF
read selected by the successfully checked codeword. -/
theorem sourceRound2Values_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest)
    (i : C.Party) (J : C.Quorum) (commitment : Digest) (e : KeyIndex)
    (message : Message) (parts : C.Party → Digest) :
    SourcePreserves x.1 x.2.1 q s (ReleaseInvariant x.2.1 s)
      (signRound2With (fun oa => sourceRoProgram prims x.1 x.2.1 oa)
        (fun p => do
          match p with
          | .chain _ key l pos => sourceReleaseBottomSuffix x.1 x.2.1 key l pos
          | _ => pure ()
          sourcePart prims x i J p message)
        x.1 J commitment e message parts) := by
  unfold signRound2With
  refine (sourceCodeword_releaseInvariant prims x.1 x.2.1 hinj q s commitment e message (combine J parts)).bind _
    fun answer => ?_
  cases answer with
  | none => exact SourcePreserves.pure none
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      refine (SourcePreserves.sequenceFin _ _ (fun l => ?_)).bind _ (fun _ => SourcePreserves.pure _)
      split
      · rename_i hpos
        exact (sourcePart_after_Q prims x hinj q s i J e l (encoding l) hpos message).map some
      · exact SourcePreserves.pure none

/-- Appending the original released-signature log changes no release-slack
field or reveal relation. -/
theorem ReleaseInvariant.released {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {source : SourceState C} {backend : CappedCompilerState C}
    (h : ReleaseInvariant seeds s source backend) (e : KeyIndex) (message : Message) (i : C.Party) :
    ReleaseInvariant seeds s { source with signing :=
      { source.signing with released := source.signing.released ++ [(e, message, i)] } } backend :=
  ⟨⟨h.1.corrupt_bound, h.1.bottom_opening, h.1.bottom_chain, h.1.top_opening,
    h.1.top_start, h.1.bottom_released⟩, h.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual round-2 handler preserves the release invariant through
D17 replay/build, the bound randomizer read, codeword selection and every Q callback. -/
theorem sourceRound2_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    SourcePreserves x.1 x.2.1 q s (ReleaseInvariant x.2.1 s)
      (sourceTsig prims x top (.round2 i J e message parts)) := by
  intro source backend h r hr
  simp only [sourceTsig, runSource_bind, runSource_get, pure_bind] at hr
  split at hr
  · rw [runSource_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  · rename_i hguard
    have hbound : source.signing.bound e = some message := by tauto
    rw [runSource_bind, mem_support_bind_iff] at hr
    obtain ⟨built, hbuilt, hr⟩ := hr
    have hb := sourceBottomOnce_releaseInvariant x.1 x.2.1 hinj q s top (treeOf e) source backend h built hbuilt
    have hsign := (sourceSigning_sourceBottomOnce x.1 x.2.1 top (treeOf e)).run x.1 x.2.1 q s source backend built hbuilt
    cases ht : built.1.1 with
    | none =>
        simp only [ht, runSource_pure, mem_support_pure_iff] at hr
        subst r
        exact hb
    | some tree =>
        simp only [ht, runSource_bind, mem_support_bind_iff] at hr
        obtain ⟨own, hown, values, hvalues, hr⟩ := hr
        have hp : ReadInvariant x.2.1 s (.randomizer bottomLayer e) built.1.2 built.2 := by
          refine ⟨hb, Or.inr ⟨e, rfl, ?_⟩⟩
          rw [hsign, hbound]
          exact Option.some_ne_none _
        have ho := sourcePart_readInvariant prims x hinj q s i J (.randomizer bottomLayer e) message
          built.1.2 built.2 hp own hown
        have hv := sourceRound2Values_releaseInvariant prims x hinj q s i J (tree.commitment e) e message
          (Function.update parts i own.1.1) own.1.2 own.2 ho.1 values hvalues
        cases hvalues : values.1.1 with
        | none =>
            simp only [hvalues, runSource_pure, mem_support_pure_iff] at hr
            subst r
            exact hv
        | some signature =>
            simp only [hvalues, runSource_bind, runSource_modify, pure_bind, runSource_pure,
              mem_support_pure_iff] at hr
            subst r
            exact hv.released e message i

/-- Q also supplies the exact point permission for the full PRF evaluator used
by the reference honest signature. -/
theorem sourcePrfValue_after_Q (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (l : ChainIndex) (pos : Digit) (hpos : pos.val < 3) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (do
      sourceReleaseBottomSuffix P seeds e l pos
      sourceRoProgram prims P seeds (prfValue seeds (.chain bottomLayer e l pos))) := by
  intro source backend h r hr
  rw [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨released, hreleased, hr⟩ := hr
  have hp := sourceReleaseBottomSuffix_readable P seeds hinj q s e l pos hpos source backend h released hreleased
  exact (sourcePrfValue_readInvariant prims P seeds hinj q s (.chain bottomLayer e l pos)
    released.1.2 released.2 hp r hr).1

/-- Revealing a signature coordinate cannot newly reveal a bottom opening. -/
theorem sourceRevealDigest_releaseInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (value : DeferredDigest) (hv : NoBottomOpening value) :
    SourcePreserves P seeds q s (ReleaseInvariant seeds s) (sourceRevealDigest value) := by
  intro source backend h r hr
  exact ⟨sourceRevealDigest_slack P seeds q s value source backend h.1
      (fun e he => (hv e he).elim) r hr,
    sourceReveals_sourceRevealDigest P seeds q s value source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2 r hr⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
/-- The exact reference honest-signature suffix preserves the release
invariant through its fresh tree rebuild, P, codeword check, all Q evaluations,
authentication path and final symbolic top-signature reveals. -/
theorem sourceHonestSignature_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (e : KeyIndex) (message : Message) :
    SourcePreserves x.1 x.2.1 q s (ReleaseInvariant x.2.1 s)
      (sourceHonestSignature prims x top e message) := by
  intro source backend h r hr
  simp only [sourceHonestSignature, runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨built, hbuilt, hr⟩ := hr
  have hb := sourceBottomTree_releaseInvariant x.1 x.2.1 hinj q s top (treeOf e) source backend h built hbuilt
  cases ht : built.1.1 with
  | none =>
      simp only [ht, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hb
  | some tree =>
      have shape := sourceBottomTree_noBottomOpening x.1 x.2.1 q s top (treeOf e) source backend h.2.2 built hbuilt tree ht
      simp only [ht, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨released, hreleased, opening, hopening, found, hfound, hr⟩ := hr
      have hp := sourceReleaseOpening_slack x.1 x.2.1 hinj q s e built.1.2 built.2 hb.1 hb.2.2 hb.2.1 released hreleased
      have hi : ReadInvariant x.2.1 s (.randomizer bottomLayer e) released.1.2 released.2 :=
        ⟨⟨hp.1, sourceReveals_sourceReleaseOpening x.1 x.2.1 q s e built.1.2 built.2 hb.2.1 released hreleased,
          runSource_pendingValid x.1 x.2.1 q s _ built.1.2 built.2 hb.2.2 released hreleased⟩, hp.2.readable⟩
      have ho := sourcePrfValue_readInvariant prims x.1 x.2.1 hinj q s (.randomizer bottomLayer e)
        released.1.2 released.2 hi opening hopening
      have hf := sourceCodeword_releaseInvariant prims x.1 x.2.1 hinj q s (tree.commitment e) e message opening.1.1
        opening.1.2 opening.2 ho.1 found hfound
      cases hfound : found.1.1 with
      | none =>
          simp only [hfound, runSource_pure, mem_support_pure_iff] at hr
          subst r
          exact hf
      | some result =>
          rcases result with ⟨randomness, encoding⟩
          simp only [hfound, runSource_bind, mem_support_bind_iff] at hr
          obtain ⟨values, hvalues, path, hpath, topValues, htop, hr⟩ := hr
          have hvaluesInv : ReleaseInvariant x.2.1 s values.1.2 values.2 := by
            apply (SourcePreserves.sequenceFin (P := x.1) (seeds := x.2.1) (q := q) (s := s)
              numChains _ (fun l => ?_)) found.1.2 found.2 hf values hvalues
            split
            · exact SourcePreserves.pure _
            · rename_i hpos
              have hlt : (encoding l).val < 3 := by have hbound := (encoding l).isLt; change (encoding l).val < 4 at hbound; omega
              simpa only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def] using
                (sourcePrfValue_after_Q prims x.1 x.2.1 hinj q s e l (encoding l) hlt).map
                  (fun value => if (encoding l).val = 0 then value else
                    (if (encoding l).val = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ value)
          have hpathInv := sourceHashProgram_releaseInvariant x.1 x.2.1 hinj q s _ values.1.2 values.2 hvaluesInv path hpath
          have htopInv := SourcePreserves.sequenceFin (P := x.1) (seeds := x.2.1) (q := q) (s := s)
            numChains (fun l => sourceRevealDigest (tree.topSignature.chainValue l))
            (fun l => sourceRevealDigest_releaseInvariant x.1 x.2.1 q s _ (shape l))
            path.1.2 path.2 hpathInv topValues htop
          rw [runSource_pure, mem_support_pure_iff] at hr
          subst r
          exact htopInv

theorem SourceKeeps.map {α β γ : Type} {field : SourceState C → γ} {oa : SourceM C α}
    (h : SourceKeeps field oa) (f : α → β) : SourceKeeps field (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind _ (fun value => SourceKeeps.pure (f value))

/-- The honest RO interface preserves the source control fields for every
possible oracle answer, including PRG routing through its stream-key hash. -/
theorem sourceControl_sourceRo (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (t : (RoSpec C).Domain) :
    SourceKeeps sourceControl (sourceRo prims P seeds t) := by
  cases t with
  | inl query => exact sourceControl_sourceHash P seeds query
  | inr inp =>
      exact (sourceControl_sourceHash P seeds (.streamKey inp.2.1)).bind _ (fun _ => SourceKeeps.pure _)

theorem sourceControl_sourceRoProgram {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp (RoSpec C) α) :
    SourceKeeps sourceControl (sourceRoProgram prims P seeds oa) :=
  SourceKeeps.simulateQ (sourceRo prims P seeds) (sourceControl_sourceRo prims P seeds) oa

theorem sourceControl_sourcePart (prims : Primitives) (x : Keys3 C)
    (i : C.Party) (J : C.Quorum) (point : Point) (message : Message) :
    SourceKeeps sourceControl (sourcePart prims x i J point message) :=
  sourceControl_sourceRoProgram prims x.1 x.2.1 _

theorem sourceControl_sourceLocal (prims : Primitives) (x : Keys3 C) (t : (LocalSpec C).Domain) :
    SourceKeeps sourceControl (sourceLocal prims x t) := by
  cases t with
  | inl n => exact SourceKeeps.lift _
  | inr t => exact sourceControl_sourceRo prims x.1 x.2.1 t

/-- Each Q completion changes only reveals, consistency and backend data. -/
theorem sourceControl_sourceBottomCompletion (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) :
    SourceKeeps sourceControl (sourceBottomCompletion P seeds e l pos) := by
  unfold sourceBottomCompletion
  refine (sourceControl_sourceReveal _).bind _ fun value => ?_
  by_cases hp : pos.val = 0
  · simp only [hp, ↓reduceIte, pure_bind]
    refine (SourceKeeps.lift (completePrf seeds _ _)).bind _ fun ok => ?_
    exact SourceKeeps.modify (field := sourceControl) (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl)
  · simp only [hp, ↓reduceIte]
    refine (SourceKeeps.lift (deferredQuery (C := C) (.pad _))).bind _ fun pad => ?_
    refine (SourceKeeps.lift (completePrf seeds _ (value ^^^ (show Digest from pad)))).bind _ fun ok => ?_
    exact SourceKeeps.modify (field := sourceControl) (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl)

theorem sourceControl_sourceReleaseBottomSuffix (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    SourceKeeps sourceControl (sourceReleaseBottomSuffix P seeds e l start) := by
  rw [sourceReleaseBottomSuffix_eq]
  refine (SourceKeeps.mapM _ _ (fun pos _ => sourceControl_sourceBottomCompletion P seeds e l pos)).bind _ fun _ => ?_
  exact (SourceKeeps.mapM _ _ (fun pos _ => sourceControl_sourcePlant P (.bottom e l pos))).bind _ (fun _ => SourceKeeps.pure ())

theorem sourceControl_sourceTopCompletion (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (kind : Option ChainIndex) :
    SourceKeeps sourceControl (sourceTopCompletion seeds b kind) := by
  unfold sourceTopCompletion
  refine (sourceControl_sourceReveal _).bind _ fun value => ?_
  refine (SourceKeeps.lift (completePrf seeds _ value)).bind _ fun ok => ?_
  exact (SourceKeeps.modify (field := sourceControl) (fun st => { st with consistent := st.consistent && ok })
    (fun _ => rfl)).bind _ (fun _ => SourceKeeps.pure value)

theorem sourceControl_sourceReturnedChain (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) (l : ChainIndex) :
    SourceKeeps sourceControl (sourceReturnedChain P seeds b tree l) := by
  unfold sourceReturnedChain
  refine (SourceKeeps.mapM _ _ (fun pos _ => sourceControl_sourceReveal _)).bind _ fun _ => ?_
  have head : SourceKeeps sourceControl (sourceTopStartCompletion seeds b l (tree.topSignature.encoding l)) := by
    unfold sourceTopStartCompletion
    split
    · exact (sourceControl_sourceTopCompletion seeds b (some l)).bind _ (fun _ => SourceKeeps.pure ())
    · exact SourceKeeps.pure ()
  refine head.bind _ fun _ => ?_
  exact (SourceKeeps.mapM _ _ (fun pos _ => sourceControl_sourcePlant P (.top b l pos))).bind _
    (fun _ => sourceControl_sourceRevealDigest _)

theorem sourceControl_sourceReturnTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) :
    SourceKeeps sourceControl (sourceReturnTree P seeds b tree) := by
  rw [sourceReturnTree_eq]
  refine (sourceControl_sourceTopCompletion seeds b none).bind _ fun opening => ?_
  refine SourceKeeps.get.bind _ fun source => ?_
  refine (SourceKeeps.mapM _ _ (fun p _ => sourceControl_sourcePlant P p)).bind _ fun _ => ?_
  exact (SourceKeeps.sequenceFin _ _ (sourceControl_sourceReturnedChain P seeds b tree)).bind _ (fun _ => SourceKeeps.pure _)

/-- The complete round-2 value computation preserves control fields before the
caller appends its released-signature record. -/
theorem sourceControl_sourceRound2Values (prims : Primitives) (x : Keys3 C)
    (i : C.Party) (J : C.Quorum) (commitment : Digest) (e : KeyIndex)
    (message : Message) (parts : C.Party → Digest) :
    SourceKeeps sourceControl
      (signRound2With (fun oa => sourceRoProgram prims x.1 x.2.1 oa)
        (fun p => do
          match p with
          | .chain _ key l pos => sourceReleaseBottomSuffix x.1 x.2.1 key l pos
          | _ => pure ()
          sourcePart prims x i J p message)
        x.1 J commitment e message parts) := by
  unfold signRound2With
  refine (sourceControl_sourceRoProgram prims x.1 x.2.1 _).bind _ fun answer => ?_
  cases answer with
  | none => exact SourceKeeps.pure none
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      refine (SourceKeeps.sequenceFin _ _ (fun l => ?_)).bind _ (fun _ => SourceKeeps.pure _)
      split
      · exact ((sourceControl_sourceReleaseBottomSuffix x.1 x.2.1 e l (encoding l)).bind _
          (fun _ => sourceControl_sourcePart prims x i J _ message)).map some
      · exact SourceKeeps.pure none

/-- Tree rebuilding and final top-coordinate reveals do not alter any of the
source-owned control fields of the reference signature computation. -/
theorem sourceControl_sourceHonestSignature (prims : Primitives) (x : Keys3 C)
    (top : TopTree) (e : KeyIndex) (message : Message) :
    SourceKeeps sourceControl (sourceHonestSignature prims x top e message) := by
  unfold sourceHonestSignature
  refine (sourceControl_sourceBottomTree x.1 x.2.1 top (treeOf e)).bind _ fun built => ?_
  cases built with
  | none => exact SourceKeeps.pure none
  | some tree =>
      refine (sourceControl_sourceReleaseOpening x.1 x.2.1 e).bind _ fun _ => ?_
      refine (sourceControl_sourceRoProgram prims x.1 x.2.1 _).bind _ fun opening => ?_
      refine (sourceControl_sourceRoProgram prims x.1 x.2.1 _).bind _ fun found => ?_
      cases found with
      | none => exact SourceKeeps.pure none
      | some found =>
          rcases found with ⟨randomness, encoding⟩
          refine (SourceKeeps.sequenceFin _ _ (fun l => ?_)).bind _ fun values => ?_
          · split
            · exact SourceKeeps.pure _
            · refine (sourceControl_sourceReleaseBottomSuffix x.1 x.2.1 e l (encoding l)).bind _ fun _ => ?_
              exact (sourceControl_sourceRoProgram prims x.1 x.2.1 _).bind _ (fun _ => SourceKeeps.pure _)
          · refine (sourceControl_sourceHashProgram x.1 x.2.1 _).bind _ fun path => ?_
            exact (SourceKeeps.sequenceFin _ _ (fun _ => sourceControl_sourceRevealDigest _)).bind _
              (fun _ => SourceKeeps.pure _)

/-- Saved signatures retain their symbolic-coordinate shape, and the original
hidden-key flag has a fixed value during honest source operations. -/
def ControlInvariant (flag : Bool) (source : SourceState C) (backend : CappedCompilerState C) : Prop :=
  PendingValid backend.1.1.data ∧ StoredTopShape source ∧ source.hiddenFlag = flag

/-- Source-control frames preserve the shape/flag invariant while the actual
compiler independently preserves pending validity. -/
theorem sourceControl_preserves {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (flag : Bool) (oa : SourceM C α)
    (hcontrol : SourceKeeps sourceControl oa) :
    SourcePreserves P seeds q s (ControlInvariant flag) oa := by
  intro source backend h r hr
  have hc := hcontrol.run P seeds q s source backend r hr
  have hf := congrArg (fun c => c.2.2.1) hc
  exact ⟨runSource_pendingValid P seeds q s oa source backend h.1 r hr,
    h.2.1.of_control hc, hf.trans h.2.2⟩

/-- Source updates outside saved trees and the original flag preserve the
shape/flag invariant. -/
theorem sourceModify_controlInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (flag : Bool) (f : SourceState C → SourceState C)
    (ht : ∀ source, (f source).trees = source.trees)
    (hf : ∀ source, (f source).hiddenFlag = source.hiddenFlag) :
    SourcePreserves P seeds q s (ControlInvariant flag) (modify f : SourceM C Unit) := by
  apply SourcePreserves.modify
  intro source backend h
  refine ⟨h.1, ?_, (hf source).trans h.2.2⟩
  intro b tree hb
  apply h.2.1 b tree
  rw [ht source] at hb
  exact hb

/-- D17 cannot alter the original hidden-key flag. -/
theorem sourceHidden_sourceBottomOnce (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourceKeeps (SourceState.hiddenFlag (C := C)) (sourceBottomOnce P seeds top b) := by
  unfold sourceBottomOnce
  refine SourceKeeps.get.bind _ fun source => ?_
  cases source.trees b with
  | some tree => exact SourceKeeps.pure tree
  | none =>
      refine ((sourceControl_sourceBottomTree P seeds top b).comp (fun c => c.2.2.1)).bind _ fun tree => ?_
      exact (SourceKeeps.modify (fun st => { st with trees := Function.update st.trees b (some tree) })
        (fun _ => rfl)).bind _ (fun _ => SourceKeeps.pure tree)

/-- D17 preserves every saved symbolic signature's shape and the original flag. -/
theorem sourceBottomOnce_controlInvariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (flag : Bool) (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourcePreserves P seeds q s (ControlInvariant flag) (sourceBottomOnce P seeds top b) := by
  intro source backend h r hr
  exact ⟨runSource_pendingValid P seeds q s _ source backend h.1 r hr,
    sourceBottomOnce_storedTopShape P seeds q s top b source backend h.1 h.2.1 r hr,
    ((sourceHidden_sourceBottomOnce P seeds top b).run P seeds q s source backend r hr).trans h.2.2⟩

/-- Every actual signing-oracle branch preserves pending validity, the shape of
all stored successful signatures and the original hidden-key flag. -/
theorem sourceTsig_controlInvariant (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : ℕ) (s : HiddenKey → Digest) (flag : Bool) (t : TsigQuery C) :
    SourcePreserves x.1 x.2.1 q s (ControlInvariant flag) (sourceTsig prims x top t) := by
  have control {α : Type} (oa : SourceM C α) (hc : SourceKeeps sourceControl oa) :=
    sourceControl_preserves x.1 x.2.1 q s flag oa hc
  cases t with
  | corrupt i =>
      unfold sourceTsig
      refine SourcePreserves.get.bind _ fun source => ?_
      dsimp only
      split
      · exact SourcePreserves.pure none
      · exact (sourceModify_controlInvariant x.1 x.2.1 q s flag
          (fun st => { st with signing := { source.signing with corrupt := insert i source.signing.corrupt } })
          (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)
  | tree b =>
      unfold sourceTsig
      refine (sourceBottomOnce_controlInvariant x.1 x.2.1 q s flag top b).bind _ fun built => ?_
      cases built with
      | none => exact SourcePreserves.pure none
      | some tree =>
          refine (control _ (sourceControl_sourceReturnTree x.1 x.2.1 b tree)).bind _ fun returned => ?_
          exact (control _ (sourceControl_sourceRoProgram prims x.1 x.2.1 _)).bind _ (fun _ => SourcePreserves.pure _)
  | round1 i J e message =>
      unfold sourceTsig
      refine SourcePreserves.get.bind _ fun source => ?_
      dsimp only
      split
      · exact SourcePreserves.pure none
      · refine (sourceModify_controlInvariant x.1 x.2.1 q s flag
          (fun st => { st with signing := { source.signing with bound := Function.update source.signing.bound e (some message) } })
          (fun _ => rfl) (fun _ => rfl)).bind _ fun _ => ?_
        refine (control _ (SourceKeeps.lift _)).bind _ fun _ => ?_
        refine (control _ (SourceKeeps.lift _)).bind _ fun backend => ?_
        refine SourcePreserves.get.bind _ fun current => ?_
        split
        · exact (control _ (sourceControl_sourceReleaseOpening x.1 x.2.1 e)).bind _
            (fun _ => (control _ (sourceControl_sourcePart prims x i J _ message)).map some)
        · exact (control _ (sourceControl_sourcePart prims x i J _ message)).map some
  | round2 i J e message parts =>
      unfold sourceTsig
      refine SourcePreserves.get.bind _ fun source => ?_
      dsimp only
      split
      · exact SourcePreserves.pure none
      · refine (sourceBottomOnce_controlInvariant x.1 x.2.1 q s flag top (treeOf e)).bind _ fun built => ?_
        cases built with
        | none => exact SourcePreserves.pure none
        | some tree =>
            refine (control _ (sourceControl_sourcePart prims x i J _ message)).bind _ fun own => ?_
            refine (control _ (sourceControl_sourceRound2Values prims x i J (tree.commitment e) e message
              (Function.update parts i own))).bind _ fun values => ?_
            cases values with
            | none => exact SourcePreserves.pure none
            | some signature =>
                exact (sourceModify_controlInvariant x.1 x.2.1 q s flag
                  (fun st => { st with signing := { st.signing with released := st.signing.released ++ [(e, message, i)] } })
                  (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure _)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual signing call preserves the release invariant when the saved
successful tree signatures have their established symbolic-coordinate shape. -/
theorem sourceTsig_releaseInvariant (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (t : TsigQuery C) (source : SourceState C) (backend : CappedCompilerState C)
    (h : ReleaseInvariant x.2.1 s source backend) (hshape : StoredTopShape source)
    (r : (TsigSpec C t × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceTsig prims x top t) source backend)) :
    ReleaseInvariant x.2.1 s r.1.2 r.2 := by
  cases t with
  | corrupt i =>
      have hs := releaseSlack_corrupt prims x top q s i source backend h.1 r hr
      rw [runSource_corrupt] at hr
      split at hr <;> rw [mem_support_pure_iff] at hr <;> subst r
      · exact ⟨hs, h.2⟩
      · exact ⟨hs, h.2⟩
  | tree b => exact sourceTree_releaseInvariant prims x hinj top q s b source backend h hshape r hr
  | round1 i J e message => exact sourceRound1_releaseInvariant prims x hinj top q s i J e message source backend h r hr
  | round2 i J e message parts => exact sourceRound2_releaseInvariant prims x hinj top q s i J e message parts source backend h r hr

/-- The actual source retains pending validity and saved-signature shape on all
runs. Release slack is required while its original hidden-key flag is down. -/
def GuardedReleaseInvariant (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (source : SourceState C) (backend : CappedCompilerState C) : Prop :=
  PendingValid backend.1.1.data ∧ StoredTopShape source ∧
    (source.hiddenFlag = false → ReleaseInvariant seeds s source backend)

/-- Control-preserving honest computations lift their release invariant to
its original-hidden-flag guarded form. -/
theorem sourceControl_guardedRelease {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (hc : SourceKeeps sourceControl oa)
    (hi : SourcePreserves P seeds q s (ReleaseInvariant seeds s) oa) :
    SourcePreserves P seeds q s (GuardedReleaseInvariant seeds s) oa := by
  intro source backend h r hr
  have control := hc.run P seeds q s source backend r hr
  have flag := congrArg (fun c => c.2.2.1) control
  refine ⟨runSource_pendingValid P seeds q s oa source backend h.1 r hr,
    h.2.1.of_control control, fun hf => ?_⟩
  exact hi source backend (h.2.2 (flag.symm.trans hf)) r hr

/-- Source-only updates outside the guarded invariant's fields preserve it. -/
theorem sourceModify_guardedRelease (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (f : SourceState C → SourceState C)
    (hs : ∀ source, (f source).signing = source.signing)
    (hr : ∀ source, (f source).revealed = source.revealed)
    (ht : ∀ source, (f source).trees = source.trees)
    (hf : ∀ source, (f source).hiddenFlag = source.hiddenFlag) :
    SourcePreserves P seeds q s (GuardedReleaseInvariant seeds s) (modify f : SourceM C Unit) := by
  apply SourcePreserves.modify
  intro source backend h
  refine ⟨h.1, ?_, fun flag => (h.2.2 ((hf source).symm.trans flag)).source_frame (hs source) (hr source)⟩
  intro b tree hb
  apply h.2.1 b tree
  rw [ht source] at hb
  exact hb

set_option backward.isDefEq.respectTransparency false in
/-- The full actual adversary/signing oracle preserves release slack guarded
by the original hidden-key flag, including its candidate and exposed-tree logs. -/
theorem sourceOracles_guardedRelease (prims : Primitives) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (top : TopTree) (q : ℕ) (s : HiddenKey → Digest)
    (t : (LocalSpec C + TsigSpec C).Domain) :
    SourcePreserves x.1 x.2.1 q s (GuardedReleaseInvariant x.2.1 s) (sourceOracles prims x top t) := by
  intro source backend h r hr
  cases t with
  | inl t =>
      simp only [sourceOracles, runSource_bind, runSource_get, mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨_, rfl, a, ha, b, hb, hr⟩ := hr
      have control := sourceControl_preserves x.1 x.2.1 q s source.hiddenFlag _
        (sourceControl_sourceLocal prims x t) source backend ⟨h.1, h.2.1, rfl⟩ a ha
      rw [runSource_modify, mem_support_pure_iff] at hb
      subst b
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨control.1, control.2.1, fun hf => ?_⟩
      have flags := Bool.or_eq_false_iff.mp hf
      have hi := sourceLocal_releaseInvariant prims x hinj q s t source backend (h.2.2 flags.1) flags.2 a ha
      exact hi.source_frame rfl rfl
  | inr t =>
      simp only [sourceOracles, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, b, hb, hr⟩ := hr
      have control := sourceTsig_controlInvariant prims x top q s source.hiddenFlag t
        source backend ⟨h.1, h.2.1, rfl⟩ a ha
      rw [runSource_modify, mem_support_pure_iff] at hb
      subst b
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨control.1, control.2.1, fun hf => ?_⟩
      have hi := sourceTsig_releaseInvariant prims x hinj top q s t source backend
        (h.2.2 (control.2.2.symm.trans hf)) h.2.1 a ha
      exact hi.source_frame rfl rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The complete fixed source game preserves the original-hidden-flag guarded
release invariant, from setup through adaptive calls, verification and the
reference honest signature used by the strong-forgery test. -/
theorem sourceGame_guardedRelease (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) :
    SourcePreserves x.1 x.2.1 q s (GuardedReleaseInvariant x.2.1 s) (sourceGame prims A x) := by
  unfold sourceGame
  refine (sourceControl_guardedRelease x.1 x.2.1 q s _ (sourceControl_sourceTopTree x.1 x.2.1)
    (sourceTopTree_releaseInvariant x.1 x.2.1 hinj q s)).bind _ fun top => ?_
  refine (SourcePreserves.simulateQ _ (sourceOracles_guardedRelease prims x hinj top q s) _).bind _
    fun forgery => ?_
  refine SourcePreserves.get.bind _ fun st => ?_
  refine (SourcePreserves.simulateQ _ (fun input => ?_) _).bind _ fun verified => ?_
  · refine (sourceControl_guardedRelease x.1 x.2.1 q s _ (sourceControl_sourceHash x.1 x.2.1 (.hash input))
      (sourceHash_releaseInvariant x.1 x.2.1 hinj q s (.hash input) (fun _ _ he => by cases he))).bind _ fun value => ?_
    exact (sourceModify_guardedRelease x.1 x.2.1 q s
      (fun source => { source with candidates := source.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input })
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure value)
  · split
    · exact SourcePreserves.pure _
    · exact (sourceControl_guardedRelease x.1 x.2.1 q s _
        (sourceControl_sourceHonestSignature prims x top forgery.signature.leafIndex forgery.message)
        (sourceHonestSignature_releaseInvariant prims x hinj top q s forgery.signature.leafIndex forgery.message)).bind _
        (fun _ => SourcePreserves.pure _)

/-- The actual empty source and capped compiler satisfy the guarded invariant. -/
theorem guardedReleaseInvariant_initial (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) :
    GuardedReleaseInvariant (C := C) seeds s sourceInit ((compilerInit, 0), fun _ => none, false) := by
  have pending : PendingValid (deferredInit (C := C)) := by
    intro p value hp
    cases hp
  exact ⟨pending, storedTopShape_initial, fun _ =>
    ⟨releaseSlack_initial seeds s, revealRelation_initial s, pending⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- In every supported run of the fixed actual source/compiler, a down original
hidden-key flag gives the P/Q/R release-slack invariant and both synchronization
invariants. No coupling to the original trace experiment is assumed here. -/
theorem sourceGame_releaseInvariant (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest)
    (r : ((Bool × TopTree × Forgery) × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource x.1 x.2.1 q s (sourceGame prims A x)
      sourceInit ((compilerInit, 0), fun _ => none, false)))
    (hf : r.1.2.hiddenFlag = false) : ReleaseInvariant x.2.1 s r.1.2 r.2 :=
  (sourceGame_guardedRelease prims A x hinj q s sourceInit
    ((compilerInit, 0), fun _ => none, false) (guardedReleaseInvariant_initial x.2.1 s) r hr).2.2 hf


/-- Existing visible pads survive every primitive backend call. -/
theorem deferredImpl_pads_mono (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) (p : Point)
    (hp : st.pads p ≠ none) : r.2.pads p ≠ none := by
  cases t with
  | pad point =>
      cases hk : st.pads point with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          by_cases he : p = point
          · subst p
            simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
          · simpa only [Function.update_of_ne he] using hp
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact hp
  | plant input value =>
      cases hc : st.cache input.query <;>
        simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr <;>
        subst r <;> exact hp
  | hash query | sample | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hp
  | record key value | virtual term point | inspect key | snapshot | bindKey e message =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp

/-- Silent cached-extra trials preserve the visible pad domain as well. -/
theorem compilerImpl_pads_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) (p : Point)
    (hp : st.data.pads p ≠ none) : r.2.data.pads p ≠ none := by
  cases t with
  | hash query => simpa only [(compiler_hash_virtual_pads P seeds query st r hr).2] using hp
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_pads_mono _ st.data a ha p hp

/-- Private draws occur only at coordinates already visited in the visible pad map. -/
def PadNoiseInv (noise : (Point →ₒ Digest).QueryCache)
    (backend : CappedCompilerState C) : Prop :=
  ∀ point, backend.1.1.data.pads point = none → noise point = none

abbrev PadNoiseSpec := SigningGuessProof.PrivateRoSpec Point Digest

/-- Replay a visible pad, or privately draw and visibly record its first value.
The entire capped state is retained and the count is unchanged. -/
def padNoiseRawRead (point : Point) (backend : CappedCompilerState C) :
    OracleComp PadNoiseSpec (Digest × CappedCompilerState C) :=
  match backend.1.1.data.pads point with
  | some value => pure (value, backend)
  | none => do
      let value ← query (spec := PadNoiseSpec) (.inr point)
      pure (value, (({ backend.1.1 with data := { backend.1.1.data with
        pads := Function.update backend.1.1.data.pads point (some value) } },
          backend.1.2), backend.2))

/-- Reify fresh pad draws only; forward all other actual compiler steps verbatim. -/
def cappedPadNoiseRaw (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) :
    QueryImpl (DeferredSpec C + RevealSpec HiddenKey Digest)
      (StateT (CappedCompilerState C) (OracleComp PadNoiseSpec))
  | .inl (.pad point) => padNoiseRawRead point
  | t => fun backend => liftM
      ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)

set_option backward.isDefEq.respectTransparency false in
/-- The actual uncounted pad kernel, including its complete backend state. -/
theorem cappedCompiler_pad_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (point : Point) (backend : CappedCompilerState C) :
    ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
      (.inl (.pad point))).run backend) =
    match backend.1.1.data.pads point with
    | some value => pure (value, backend)
    | none => (fun value : Digest =>
        (value, (({ backend.1.1 with data := { backend.1.1.data with
          pads := Function.update backend.1.1.data.pads point (some value) } },
            backend.1.2), backend.2))) <$> ($ᵗ Digest) := by
  simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    deferredInputSide, deferredCandidate, Option.isSome_none, Bool.false_eq_true,
    and_false, false_and, false_or, decide_false, Bool.or_false, deferredCounted, if_false,
    compilerImpl, deferredImpl, StateT.run, StateT.mk]
  cases hp : backend.1.1.data.pads point with
  | some value => simp only [map_pure]; rfl
  | none => simp only [Functor.map_map]; rfl

/-- The private read has precisely the actual fresh-pad distribution. -/
theorem padNoiseRawRead_run (point : Point) (backend : CappedCompilerState C)
    (noise : (Point →ₒ Digest).QueryCache)
    (hfresh : backend.1.1.data.pads point = none → noise point = none) :
    (simulateQ SigningGuessProof.privateRoImpl (padNoiseRawRead point backend)).run noise =
    match backend.1.1.data.pads point with
    | some value => pure ((value, backend), noise)
    | none => (fun value : Digest =>
        ((value, (({ backend.1.1 with data := { backend.1.1.data with
          pads := Function.update backend.1.1.data.pads point (some value) } },
            backend.1.2), backend.2)), noise.cacheQuery point value)) <$> ($ᵗ Digest) := by
  cases hp : backend.1.1.data.pads point with
  | some value => simp only [padNoiseRawRead, hp, simulateQ_pure, StateT.run_pure]
  | none =>
      simp only [padNoiseRawRead, hp, HasQuery.instOfMonadLift_query, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_pure, StateT.run_bind, StateT.run_pure,
        SigningGuessProof.privateRoImpl, QueryImpl.add_apply_inr]
      simp only [bind_pure_comp]
      erw [QueryImpl.withCaching_run_none _ (hfresh hp), Functor.map_map]
/-- The actual capped wrapper never deletes visible pads entries. -/
theorem cappedCompiler_pads_mono (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))
    (p : Point) (hp : backend.1.1.data.pads p ≠ none) :
    r.2.1.1.data.pads p ≠ none := by
  cases t with
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact compilerImpl_pads_mono P seeds t backend.1.1 b hb p hp
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      exact hp

/-- The private noise cache can remain in place across any original step. -/
theorem PadNoiseInv.actual_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (noise : (Point →ₒ Digest).QueryCache) (backend : CappedCompilerState C)
    (h : PadNoiseInv noise backend)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
    PadNoiseInv noise r.2 := by
  intro edge he
  apply h edge
  by_contra hn
  exact cappedCompiler_pads_mono P seeds q s t backend r hr edge hn he

/-- Fresh pad draws extend exactly the visited visible domain. -/
theorem padNoiseRawRead_inv (point : Point)
    (backend : CappedCompilerState C) (noise : (Point →ₒ Digest).QueryCache)
    (h : PadNoiseInv noise backend)
    (r : (Digest × CappedCompilerState C) × (Point →ₒ Digest).QueryCache)
    (hr : r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      (padNoiseRawRead point backend)).run noise)) : PadNoiseInv r.2 r.1.2 := by
  rw [padNoiseRawRead_run point backend noise (h point)] at hr
  cases hp : backend.1.1.data.pads point with
  | some answer =>
      simp only [hp, mem_support_pure_iff] at hr
      subst r
      exact h
  | none =>
      simp only [hp, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      intro other ho
      by_cases he : other = point
      · subst other
        simp only [Function.update_self] at ho
        cases ho
      · change (noise.cacheQuery point value) other = none
        rw [QueryCache.cacheQuery_of_ne _ _ he]
        apply h other
        simpa only [Function.update_of_ne he] using ho

set_option backward.isDefEq.respectTransparency false in
/-- One reified compiler step has exactly the actual step's full visible
result, and keeps its private draw history inside the online pad domain. -/
theorem cappedPadNoiseRaw_step (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (backend : CappedCompilerState C) (noise : (Point →ₒ Digest).QueryCache)
    (h : PadNoiseInv noise backend) :
    (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        ((cappedPadNoiseRaw P seeds q s t).run backend)).run noise =
      ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) ∧
    (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
      ((cappedPadNoiseRaw P seeds q s t).run backend)).run noise), PadNoiseInv r.2 r.1.2) := by
  have ordinary (t : DeferredQuery C ⊕ HiddenKey) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
          (liftM ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
            (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))).run noise =
        ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
        (liftM ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend))).run noise),
        PadNoiseInv r.2 r.1.2) := by
    rw [SigningGuessProof.privateRoImpl, roSim.run_liftM]
    constructor
    · simp only [Functor.map_map, id_map']
    · intro r hr
      simp only [support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact h.actual_step P seeds q s t noise backend a ha
  have pad (point : Point) :
      (Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        (padNoiseRawRead point backend)).run noise =
        ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
          (.inl (.pad point))).run backend)) ∧
      (∀ r ∈ support ((simulateQ SigningGuessProof.privateRoImpl
        (padNoiseRawRead point backend)).run noise), PadNoiseInv r.2 r.1.2) := by
    constructor
    · rw [padNoiseRawRead_run point backend noise (h point), cappedCompiler_pad_run]
      cases hp : backend.1.1.data.pads point with
      | none => simp only [Functor.map_map]
      | some value => simp only [map_pure]
    · exact fun r hr => padNoiseRawRead_inv point backend noise h r hr
  cases t with
  | inr key => exact ordinary (.inr key)
  | inl t =>
      cases t with
      | pending p => exact ordinary (.inl (.pending p))
      | hash query => exact ordinary (.inl (.hash query))
      | virtual term point => exact ordinary (.inl (.virtual term point))
      | pad point => exact pad point
      | inspect p => exact ordinary (.inl (.inspect p))
      | plant input value => exact ordinary (.inl (.plant input value))
      | snapshot => exact ordinary (.inl .snapshot)
      | sample => exact ordinary (.inl .sample)
      | record p value => exact ordinary (.inl (.record p value))
      | uniform n => exact ordinary (.inl (.uniform n))
      | bindKey e message => exact ordinary (.inl (.bindKey e message))

/-- Exact reification of an arbitrary program of the fixed compiler. Every
source-owned field and every capped-backend field remains in the result. -/
theorem cappedPadNoiseRaw_simulate (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (backend : CappedCompilerState C) (noise : (Point →ₒ Digest).QueryCache)
    (h : PadNoiseInv noise backend) :
    Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl
        ((simulateQ (cappedPadNoiseRaw P seeds q s) oa).run backend)).run noise =
      (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
        oa).run backend := by
  induction oa using OracleComp.inductionOn generalizing backend noise with
  | pure value => simp
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      have step := cappedPadNoiseRaw_step P seeds q s t backend noise h
      calc
        _ = (simulateQ SigningGuessProof.privateRoImpl
            ((cappedPadNoiseRaw P seeds q s t).run backend)).run noise >>= fun r =>
          (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
            (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
            (next r.1.1)).run r.1.2 := by
          apply OracleComp.bind_congr_of_forall_mem_support
          intro r hr
          exact ih r.1.1 r.1.2 r.2 (step.2 r hr)
        _ = _ := by
          conv_rhs => rw [← step.1]
          simp only [bind_map_left]

section PrivateTable

variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]

/- Source: VCVio/OracleComp/QueryTracking/RandomOracle/EagerTable.lean,
`evalDist_simulateQ_randomOracle_run'_eq_tableExtending`, with the independent
uniform-query case from `privateChainNoise_eq_table` above. This adapter keeps
private uniform draws interleaved and uses the same coordinate marginalization. -/
/-- Resolve a private finite table while forwarding private uniform draws. -/
def resolvePrivateTable (table : D → R) :
    QueryImpl (SigningGuessProof.PrivateRoSpec D R) ProbComp
  | .inl n => query (spec := unifSpec) n
  | .inr edge => pure (table edge)

/-- Coordinate resampling preserves the law of any subsequent private program. -/
theorem privateTable_update_bind {α : Type} (edge : D)
    (next : (D → R) → ProbComp α) :
    𝒟[do
      let value ← $ᵗ R
      let table ← $ᵗ (D → R)
      next (Function.update table edge value)] =
    𝒟[($ᵗ (D → R)) >>= next] := by
  have h := congrArg (fun d => d >>= fun table => 𝒟[next table])
    (evalDist_uniformSample_bind_update (D := D) (R := R) edge)
  simpa only [← evalDist_bind, bind_assoc, pure_bind] using h

set_option backward.isDefEq.respectTransparency false in
/-- Eagerly sampling the finite private table preserves the entire raw
source result. The table is private; its reads do not populate visible state. -/
theorem privateRo_eq_table {α : Type} (oa : OracleComp (SigningGuessProof.PrivateRoSpec D R) α)
    (noise : (D →ₒ R).QueryCache) :
    𝒟[Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl oa).run noise] =
    𝒟[do
      let table ← $ᵗ (D → R)
      simulateQ (resolvePrivateTable (tableExtending noise table)) oa] := by
  classical
  induction oa using OracleComp.inductionOn generalizing noise with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ (D → R)) (by simp) (pure value)).symm
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      cases t with
      | inl n =>
          have hu : (SigningGuessProof.privateRoImpl (D := D)
              (R := R) (.inl n)).run noise =
              (fun value => (value, noise)) <$>
                (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := rfl
          rw [hu, bind_map_left]
          simp only [resolvePrivateTable]
          calc
            _ = 𝒟[do
              let value ← (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
              let table ← $ᵗ (D → R)
              simulateQ (resolvePrivateTable (tableExtending noise table)) (next value)] := by
                apply evalDist_bind_congr
                intro value _
                exact ih value noise
            _ = _ := OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
      | inr edge =>
          change 𝒟[((D →ₒ R).randomOracle edge).run noise >>= fun r =>
            Prod.fst <$> (simulateQ SigningGuessProof.privateRoImpl (next r.1)).run r.2] = _
          simp only [resolvePrivateTable, pure_bind]
          cases hn : noise edge with
          | some value =>
              rw [QueryImpl.withCaching_run_some _ hn, pure_bind, ih value noise]
              apply evalDist_bind_congr
              intro table _
              simp only [tableExtending, hn, Option.getD_some]
          | none =>
              rw [QueryImpl.withCaching_run_none _ hn, bind_map_left]
              let replay : (D → R) → ProbComp α := fun table =>
                simulateQ (resolvePrivateTable (tableExtending noise table))
                  (next (tableExtending noise table edge))
              calc
                _ = 𝒟[do
                    let value ← $ᵗ R
                    let table ← $ᵗ (D → R)
                    replay (Function.update table edge value)] := by
                  apply evalDist_bind_congr
                  intro value _
                  rw [ih value (noise.cacheQuery edge value)]
                  apply evalDist_bind_congr
                  intro table _
                  dsimp only [replay]
                  rw [tableExtending_cacheQuery,
                    ← tableExtending_update_of_none noise table hn value]
                  simp only [Function.update_self]
                _ = _ := privateTable_update_bind edge replay

end PrivateTable

/-- Interpret any actual compiler program using a fixed private pad table.
Only an actual pad read fills the visible pad map. -/
def compilerProgramPads (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (backend : CappedCompilerState C) : ProbComp (α × CappedCompilerState C) :=
  simulateQ (resolvePrivateTable pads)
    ((simulateQ (cappedPadNoiseRaw P seeds q s) oa).run backend)

/-- Eager pad sampling preserves the complete arbitrary-program outcome for
fixed hidden labels. Existing visible pads take priority over the private table. -/
theorem cappedCompiler_eq_padTable (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (backend : CappedCompilerState C) :
    𝒟[(simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
      oa).run backend] = 𝒟[do
        let pads ← $ᵗ (Point → Digest)
        compilerProgramPads P seeds q s pads oa backend] := by
  rw [← cappedPadNoiseRaw_simulate P seeds q s oa backend ∅ (fun _ _ => rfl)]
  simpa only [tableExtending_empty, compilerProgramPads] using
    privateRo_eq_table ((simulateQ (cappedPadNoiseRaw P seeds q s) oa).run backend) ∅

/-- The fixed source with fixed hidden labels and private eager pads. It starts
with the same empty visible backend and returns the entire compiler outcome. -/
def compilerRunPads (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    ProbComp (CompilerOutcome C) :=
  compilerProgramPads x.1 x.2.1 q s pads (sourceProgram prims A x)
    ((compilerInit, 0), fun _ => none, false)

/-- The actual source law for each fixed hidden-label table, with all source
fields, cache, trace, reveals, consistency, flag and count kept joint. -/
theorem sourceProgram_eq_compilerRunPads (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) :
    𝒟[(simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
      (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s)
      (sourceProgram prims A x)).run ((compilerInit, 0), fun _ => none, false)] =
    𝒟[do let pads ← $ᵗ (Point → Digest); compilerRunPads prims A x q s pads] :=
  cappedCompiler_eq_padTable x.1 x.2.1 q s (sourceProgram prims A x)
    ((compilerInit, 0), fun _ => none, false)

/-- Independently sampling hidden labels and eager pads preserves the original
fixed compiler's complete outcome distribution. -/
theorem compilerRun_eq_padTable (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) :
    𝒟[compilerRun prims A x q] = 𝒟[do
      let s ← $ᵗ (HiddenKey → Digest)
      let pads ← $ᵗ (Point → Digest)
      compilerRunPads prims A x q s pads] := by
  unfold compilerRun
  apply evalDist_bind_congr
  intro s _
  exact sourceProgram_eq_compilerRunPads prims A x q s


section EagerPadTransfer
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

/-- Every outcome for a fixed eager pad table is supported by the actual compiler. -/
theorem compilerProgramPads_support (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (backend : CappedCompilerState C) (r : α × CappedCompilerState C)
    (hr : r ∈ support (compilerProgramPads P seeds q s pads oa backend)) :
    r ∈ support ((simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
      oa).run backend) := by
  apply (mem_support_iff_of_evalDist_eq
    (cappedCompiler_eq_padTable P seeds q s oa backend) r).mpr
  rw [mem_support_bind_iff]
  refine ⟨pads, ?_, hr⟩
  rw [support_uniformSample]
  trivial

/-- The actual release invariant holds on every fixed eager-pad source run. -/
theorem compilerRunPads_releaseInvariant (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hinj : Function.Injective x.2.1) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (r : CompilerOutcome C)
    (hr : r ∈ support (compilerRunPads prims A x q s pads))
    (hf : r.1.2.hiddenFlag = false) : ReleaseInvariant x.2.1 s r.1.2 r.2 := by
  apply sourceGame_releaseInvariant prims A x hinj q s r _ hf
  exact compilerProgramPads_support x.1 x.2.1 q s pads (sourceProgram prims A x)
    ((compilerInit, 0), fun _ => none, false) r hr

/-- Except for a pad query, the actual backend preserves the visible pad map. -/
theorem deferredImpl_pads_of_ne (t : DeferredQuery C) (st : DeferredState C)
    (hpad : ∀ p, t ≠ .pad p) (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) : r.2.pads = st.pads := by
  cases t with
  | pad p => exact False.elim (hpad p rfl)
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          rfl
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl
  | plant input value =>
      cases hc : st.cache input.query <;>
        simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hr <;>
        subst r <;> rfl
  | hash query | sample | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | record key value | virtual term point | inspect key | snapshot | bindKey e message =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl

/-- The capped wrapper also preserves visible pads on every non-pad operation. -/
theorem cappedCompiler_pads_of_ne (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (hpad : ∀ p, t ≠ .inl (.pad p)) (backend : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
    r.2.1.1.data.pads = backend.1.1.data.pads := by
  cases t with
  | inr key =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, StateT.run_mk,
        mem_support_pure_iff] at hr
      subst r
      rfl
  | inl t =>
      simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
        StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      cases t with
      | hash query => exact (compiler_hash_virtual_pads P seeds query backend.1.1 b hb).2
      | bindKey e message =>
          simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hb
          subst b
          rfl
      | _ =>
          simp only [compilerImpl, StateT.run, support_map] at hb
          obtain ⟨c, hc, rfl⟩ := hb
          exact deferredImpl_pads_of_ne _ _ (fun p he => hpad p (congrArg Sum.inl he)) c hc

/-- Resolving a private table forwards ordinary randomness verbatim. -/
theorem resolvePrivateTable_lift {D R α : Type} (table : D → R) (oa : ProbComp α) :
    simulateQ (resolvePrivateTable table) (liftM oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
      simp only [liftM_bind, simulateQ_bind]
      congr 1
      funext a
      exact ih a

/-- Visible entries of a fixed eager-pad run agree with its private table. -/
theorem compilerProgramPads_visible (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (backend : CappedCompilerState C)
    (h : ∀ p v, backend.1.1.data.pads p = some v → v = pads p)
    (r : α × CappedCompilerState C)
    (hr : r ∈ support (compilerProgramPads P seeds q s pads oa backend)) :
    ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
  have step (t : DeferredQuery C ⊕ HiddenKey) (backend : CappedCompilerState C)
      (h : ∀ p v, backend.1.1.data.pads p = some v → v = pads p)
      (a : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (ha : a ∈ support (simulateQ (resolvePrivateTable pads)
        ((cappedPadNoiseRaw P seeds q s t).run backend))) :
      ∀ p v, a.2.1.1.data.pads p = some v → v = pads p := by
    have ordinary (ht : ∀ p, t ≠ .inl (.pad p))
        (heq : (cappedPadNoiseRaw P seeds q s t).run backend =
          liftM ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
          (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run backend)) :
        ∀ p v, a.2.1.1.data.pads p = some v → v = pads p := by
      rw [heq, resolvePrivateTable_lift] at ha
      rw [cappedCompiler_pads_of_ne P seeds q s t ht backend a ha]
      exact h
    cases t with
    | inr key => exact ordinary (by intros; simp) rfl
    | inl t =>
      cases t with
      | pad point =>
          change a ∈ support (simulateQ (resolvePrivateTable pads) (padNoiseRawRead point backend)) at ha
          cases hp : backend.1.1.data.pads point with
          | some value =>
              simp only [padNoiseRawRead, hp, simulateQ_pure, mem_support_pure_iff] at ha
              subst a
              exact h
          | none =>
              simp only [padNoiseRawRead, hp, HasQuery.instOfMonadLift_query, simulateQ_bind, simulateQ_query,
                OracleQuery.input_query, OracleQuery.cont_query, id_map,
                resolvePrivateTable, pure_bind, simulateQ_pure, mem_support_pure_iff] at ha
              subst a
              intro p v hv
              by_cases he : p = point
              · subst p
                simpa only [Function.update_self, Option.some.injEq] using hv.symm
              · exact h p v (by simpa only [Function.update_of_ne he] using hv)
      | _ => exact ordinary (by intros; simp) rfl
  induction oa using OracleComp.inductionOn generalizing backend with
  | pure value =>
      simp only [compilerProgramPads, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      exact h
  | query_bind t next ih =>
      simp only [compilerProgramPads, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
        mem_support_bind_iff] at hr
      obtain ⟨a, ha, hr⟩ := hr
      exact ih a.1 a.2 (step t backend h a ha) hr

/-- In the source run, every visible pad is the eager table value. -/
theorem compilerRunPads_visible (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (r : CompilerOutcome C) (hr : r ∈ support (compilerRunPads prims A x q s pads)) :
    ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
  exact compilerProgramPads_visible x.1 x.2.1 q s pads (sourceProgram prims A x)
    ((compilerInit, 0), fun _ => none, false) (by intros p v hv; cases hv) r hr

/-- The retained high half of each eager chain-noise output. -/
def noiseHigh (noise : ChainNoiseIndex → HashOutput) : ChainNoiseIndex → Digest :=
  fun edge => (XmssSecurity.Rom.hashOutputEquivDigestPair (noise edge)).1

/-- Positive chain coordinates from the low noise halves; the zero coordinates
are placeholders overwritten by the hidden-label installation. -/
def noiseLabels (noise : ChainNoiseIndex → HashOutput) :
    XmssSecurity.CappedChain.GlobalChainValueIndex → Digest :=
  XmssSecurity.CappedChain.globalChainTableMaterialEquiv.symm
    (fun _ _ => 0, fun edge => (XmssSecurity.Rom.hashOutputEquivDigestPair (noise edge)).2)

/-- Installation reads the original chain table only at terminal coordinates. -/
theorem install_terminal_only (F : Point → Digest)
    (labels labels' : XmssSecurity.CappedChain.GlobalChainValueIndex → Digest)
    (s : HiddenKey → Digest)
    (h : ∀ index, index.2.2.val = XmssSecurity.chainLength - 1 → labels index = labels' index) :
    installHiddenCoordinates (maskPrfChainTables s (F, labels)) s =
      installHiddenCoordinates (maskPrfChainTables s (F, labels')) s := by
  apply Prod.ext
  · rfl
  · funext index
    dsimp only [installHiddenCoordinates, maskPrfChainTables]
    split
    · rfl
    · apply h
      have hp := index.2.2.isLt
      omega

/-- Changing only the unused seed coordinates cannot change installed tables. -/
theorem install_noiseLabels (F : Point → Digest)
    (seeds : XmssSecurity.ChainKey → ChainIndex → Digest)
    (noise : ChainNoiseIndex → HashOutput) (s : HiddenKey → Digest) :
    installHiddenCoordinates (maskPrfChainTables s (F,
      XmssSecurity.CappedChain.globalChainTableMaterialEquiv.symm
        (seeds, fun edge => (XmssSecurity.Rom.hashOutputEquivDigestPair (noise edge)).2))) s =
      installHiddenCoordinates (maskPrfChainTables s (F, noiseLabels noise)) s := by
  apply install_terminal_only
  intro index hi
  have hn : index.2.2.val ≠ 0 := by rw [hi]; decide
  simp only [noiseLabels, XmssSecurity.CappedChain.globalChainTableMaterialEquiv,
    Equiv.coe_fn_symm_mk, hn, ↓reduceDIte]

/-- Repackage all chain labels and independent high halves as seeds and full
noise outputs, using the pinned global-chain material and hash-pair bijections. -/
def chainNoiseMaterialEquiv :
    ((XmssSecurity.ChainKey → ChainIndex → Digest) ×
      (ChainNoiseIndex → HashOutput)) ≃
    ((XmssSecurity.CappedChain.GlobalChainValueIndex → Digest) ×
      (ChainNoiseIndex → Digest)) where
  toFun material :=
    (XmssSecurity.CappedChain.globalChainTableMaterialEquiv.symm
      (material.1, fun edge => (XmssSecurity.Rom.hashOutputEquivDigestPair (material.2 edge)).2),
     noiseHigh material.2)
  invFun tables :=
    ((XmssSecurity.CappedChain.globalChainTableMaterialEquiv tables.1).1,
     fun edge => XmssSecurity.Rom.hashOutputEquivDigestPair.symm
       (tables.2 edge, (XmssSecurity.CappedChain.globalChainTableMaterialEquiv tables.1).2 edge))
  left_inv material := by
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · funext edge
      exact XmssSecurity.Rom.hashOutputEquivDigestPair.symm_apply_apply (material.2 edge)
  right_inv tables := by
    apply Prod.ext
    · change XmssSecurity.CappedChain.globalChainTableMaterialEquiv.symm
        ((XmssSecurity.CappedChain.globalChainTableMaterialEquiv tables.1).1,
         fun edge => (XmssSecurity.Rom.hashOutputEquivDigestPair
           (XmssSecurity.Rom.hashOutputEquivDigestPair.symm
             (tables.2 edge, (XmssSecurity.CappedChain.globalChainTableMaterialEquiv tables.1).2 edge))).2)
        = tables.1
      simp only [Equiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
    · funext edge
      exact congrArg Prod.fst (XmssSecurity.Rom.hashOutputEquivDigestPair.apply_symm_apply _)

/-- After installation, sampling labels and high halves is exactly sampling
full chain noise; the unused chain seeds have been marginalized away. -/
theorem installedChainNoise_bind {α : Type} (F : Point → Digest) (s : HiddenKey → Digest)
    (next : PrfChainTables → (ChainNoiseIndex → Digest) → ProbComp α) :
    𝒟[do
      let labels ← XmssSecurity.CappedChain.independentGlobalChainValueTable
      let high ← XmssSecurity.CappedChain.independentGlobalChainHigh
      next (installHiddenCoordinates (maskPrfChainTables s (F, labels)) s) high] =
    𝒟[do
      let noise ← $ᵗ (ChainNoiseIndex → HashOutput)
      next (installHiddenCoordinates (maskPrfChainTables s (F, noiseLabels noise)) s)
        (noiseHigh noise)] := by
  let observe := fun tables :
      (XmssSecurity.CappedChain.GlobalChainValueIndex → Digest) × (ChainNoiseIndex → Digest) =>
    next (installHiddenCoordinates (maskPrfChainTables s (F, tables.1)) s) tables.2
  have hu := evalDist_map_bijective_uniform_cross
    (α := (XmssSecurity.ChainKey → ChainIndex → Digest) × (ChainNoiseIndex → HashOutput))
    chainNoiseMaterialEquiv
    chainNoiseMaterialEquiv.bijective
  have hm := congrArg (fun d => d >>= fun tables => 𝒟[observe tables]) hu
  simp only [← evalDist_bind, bind_map_left] at hm
  calc
    _ = 𝒟[($ᵗ ((XmssSecurity.CappedChain.GlobalChainValueIndex → Digest) ×
        (ChainNoiseIndex → Digest))) >>= observe] := by
      conv_rhs => rw [evalDist_bind, ← XmssSecurity.evalDist_independent_uniform_pair, ← evalDist_bind]
      simp only [bind_assoc, pure_bind, observe]
      have hl : 𝒟[XmssSecurity.CappedChain.independentGlobalChainValueTable] =
          𝒟[$ᵗ (XmssSecurity.CappedChain.GlobalChainValueIndex → Digest)] := by
        apply evalDist_ext
        intro labels
        simp only [XmssSecurity.CappedChain.independentGlobalChainValueTable,
          probOutput_uniformSample]
        erw [probOutput_uniformSample]
      have hh : 𝒟[XmssSecurity.CappedChain.independentGlobalChainHigh] =
          𝒟[$ᵗ (ChainNoiseIndex → Digest)] := by
        apply evalDist_ext
        intro high
        simp only [XmssSecurity.CappedChain.independentGlobalChainHigh,
          probOutput_uniformSample]
        erw [probOutput_uniformSample]
      simp only [evalDist_bind, hl, hh]
      rfl
    _ = 𝒟[do
        let material ← $ᵗ ((XmssSecurity.ChainKey → ChainIndex → Digest) ×
          (ChainNoiseIndex → HashOutput))
        next (installHiddenCoordinates (maskPrfChainTables s (F, noiseLabels material.2)) s)
          (noiseHigh material.2)] := by
      rw [← hm]
      apply evalDist_bind_congr
      intro material _
      dsimp only [observe, chainNoiseMaterialEquiv, Equiv.coe_fn_mk]
      rw [install_noiseLabels]
    _ = _ := by
      rw [evalDist_bind, ← XmssSecurity.evalDist_independent_uniform_pair, ← evalDist_bind]
      simp only [bind_assoc, pure_bind]
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ (XmssSecurity.ChainKey → ChainIndex → Digest)) (probFailure_uniformSample _) _

/-- The original trace uses the same hidden labels and full chain-noise table
as the compiler representation, with independent PRF pads and share material. -/
theorem traceRun_eq_symbolic_noise (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (slack : C.Term) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
      𝒟[do
        let s ← $ᵗ (HiddenKey → Digest)
        let shares ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
        let F ← $ᵗ (Point → Digest)
        let noise ← $ᵗ (ChainNoiseIndex → HashOutput)
        eagerTrace prims A x slack shares
          (installHiddenCoordinates (maskPrfChainTables s (F, noiseLabels noise)) s)
          (noiseHigh noise)] := by
  rw [traceRun_eq_symbolic_tables prims A x hkeys slack]
  apply evalDist_bind_congr
  intro s _
  apply evalDist_bind_congr
  intro shares _
  rw [evalDist_bind, ← uniformPrfChainTables_law, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro F _
  exact installedChainNoise_bind F s (eagerTrace prims A x slack shares)

end EagerPadTransfer

end SigningCompilerCouplingProof

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.exact_completePrf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.exact_completePrf
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceCost_sourceBackend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceCost_sourceBackend
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceCost_sourceBottomRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceCost_sourceBottomRow
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.exact_cappedCompiler_run_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.exact_cappedCompiler_run_count
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReveal_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReveal_correct
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.deferredPlant_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.deferredPlant_correct
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.relTriple_deferredHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.relTriple_deferredHash
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.CacheRelation.allocatePending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.CacheRelation.allocatePending
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.CacheRelation.allocateVirtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.CacheRelation.allocateVirtual
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_slack_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_slack_target
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_slack_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_slack_program
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePlant_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePlant_correct
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_samplePending_fresh_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_samplePending_fresh_next
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.relTriple_deferredPending_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.relTriple_deferredPending_terminal
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.CacheRelation.updateSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.CacheRelation.updateSecret
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.relTriple_deferredPending_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.relTriple_deferredPending_internal
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.relTriple_cachedExtra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.relTriple_cachedExtra
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_fillTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_fillTerm
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.completePrf_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.completePrf_correct
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.completePrf_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.completePrf_randomizer
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_slackPlant_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_slackPlant_fresh
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_completePrf_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_completePrf_fresh
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_hashInput_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_hashInput_hit
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_hashInput_trigger_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_hashInput_trigger_iff
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.rawTraceGame_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.rawTraceGame_law
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_private_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_private_prefix
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.rawTraceProgram_prefix_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.rawTraceProgram_prefix_count_le
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_presampled_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_presampled_slots
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.presampledTrace_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.presampledTrace_count_le
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.refreshAllPrf_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.refreshAllPrf_joint
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_eager_prf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_eager_prf
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.probEvent_completePrf_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.probEvent_completePrf_fiber
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.presampledTrace_eq_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.presampledTrace_eq_resolved
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_eager_forest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_eager_forest
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.resolvedTrace_prefix_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.resolvedTrace_prefix_count_le
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_eager_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_eager_chains
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.refreshChainStarts_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.refreshChainStarts_joint
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_chain_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_chain_material
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.chainMaterial_cache_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.chainMaterial_cache_eq
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.chainMaterial_view_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.chainMaterial_view_uniform
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_independent_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_independent_chains
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.hiddenCoordinates_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.hiddenCoordinates_joint
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_symbolic_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_symbolic_tables
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.symbolicTables_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.symbolicTables_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_fillTerms_randomOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_fillTerms_randomOracle
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_fillPrfCache_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_fillPrfCache_ext
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.probEvent_completePrf_fiber_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.probEvent_completePrf_fiber_all
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_completePrf_delay_fill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_completePrf_delay_fill
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_prfQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_prfQuery
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_completePrf_then_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_completePrf_then_read
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.probEvent_completePrf_delay_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.probEvent_completePrf_delay_read
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.evalDist_completePrf_delay_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.evalDist_completePrf_delay_read

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerImpl_pending_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerImpl_pending_mono
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedChainNoiseRaw_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedChainNoiseRaw_step
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedChainNoiseRaw_simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedChainNoiseRaw_simulate
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerRun_eq_chainNoiseRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerRun_eq_chainNoiseRaw
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerRun_eq_private_chain_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerRun_eq_private_chain_prefix
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.privateChainNoise_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.privateChainNoise_eq_table
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerRun_eq_chainNoiseTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerRun_eq_chainNoiseTable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.releaseSlack_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.releaseSlack_initial
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.completePrf_done_or_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.completePrf_done_or_missing
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerImpl_prf_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerImpl_prf_frame
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceOracles_lacked_prf_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceOracles_lacked_prf_flag
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.releaseSlack_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.releaseSlack_corrupt
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.completePrf_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.completePrf_frame
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePlant_terminal_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePlant_terminal_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReleaseOpening_slack_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReleaseOpening_slack_frame
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReleaseOpening_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReleaseOpening_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.ReleaseSlack.ready_virtual_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.ReleaseSlack.ready_virtual_missing
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.ReleaseSlack.readyAfter_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.ReleaseSlack.readyAfter_missing
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceVirtual_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceVirtual_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReveal_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReveal_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePlant_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePlant_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePad_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePad_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.completePrf_chain_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.completePrf_chain_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomCompletion_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomCompletion_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_pendingValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_pendingValid
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomCompletion_revealRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomCompletion_revealRelation
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReleaseBottomSuffix_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReleaseBottomSuffix_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.completePrf_top_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.completePrf_top_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceTopCompletion_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceTopCompletion_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReturnTree_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReturnTree_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePending_noBottomOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePending_noBottomOpening
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceTopValue_noBottomOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceTopValue_noBottomOpening
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomTree_noBottomOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomTree_noBottomOpening
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomOnce_noBottomOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomOnce_noBottomOpening

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.SourceKeeps.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.SourceKeeps.run
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceControl_sourceBackend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceControl_sourceBackend
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceControl_sourceBottomTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceControl_sourceBottomTree
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomOnce_storedTopShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomOnce_storedTopShape
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReveals_sourceBackend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReveals_sourceBackend
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.ReleaseSlack.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.ReleaseSlack.read
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedCompiler_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedCompiler_cache_le
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.runSource_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.runSource_cache_le
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceRawHash_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceRawHash_slack
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceHash_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceHash_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePrfValue_readInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePrfValue_readInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceEval_readInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceEval_readInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePart_readInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePart_readInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceOracles_local_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceOracles_local_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourcePending_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourcePending_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomRow_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomRow_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceTopTree_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceTopTree_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomTree_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomTree_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceBottomOnce_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceBottomOnce_releaseInvariant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReleaseOpening_after_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReleaseOpening_after_bind
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceRound1_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceRound1_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReleaseBottomSuffix_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReleaseBottomSuffix_cached
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReleaseBottomSuffix_readable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReleaseBottomSuffix_readable
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceReturnTree_opening_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceReturnTree_opening_cached
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceTree_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceTree_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceRound2_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceRound2_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceHonestSignature_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceHonestSignature_releaseInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceTsig_controlInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceTsig_controlInvariant
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceOracles_guardedRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceOracles_guardedRelease
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceGame_guardedRelease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceGame_guardedRelease
/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceGame_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceGame_releaseInvariant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedCompiler_pad_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedCompiler_pad_run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedPadNoiseRaw_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedPadNoiseRaw_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedPadNoiseRaw_simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedPadNoiseRaw_simulate

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.privateRo_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.privateRo_eq_table

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.cappedCompiler_eq_padTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.cappedCompiler_eq_padTable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceProgram_eq_compilerRunPads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.sourceProgram_eq_compilerRunPads

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerRun_eq_padTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerRun_eq_padTable

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerProgramPads_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerProgramPads_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerRunPads_releaseInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerRunPads_releaseInvariant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerProgramPads_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerProgramPads_visible

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.compilerRunPads_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.compilerRunPads_visible

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.install_terminal_only' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.install_terminal_only

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.install_noiseLabels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.install_noiseLabels

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.installedChainNoise_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.installedChainNoise_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.traceRun_eq_symbolic_noise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningCompilerCouplingProof.traceRun_eq_symbolic_noise

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity.SigningCompilerCouplingProof

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof

variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Boundary marks are erased by expansion; completion remains one source query. -/
abbrev MarkSpec := Bool →ₒ Unit
abbrev CompleteSpec := (Point × Digest) →ₒ Bool
abbrev SpecX (C : Committee) :=
  DeferredSpec C + RevealSpec HiddenKey Digest + MarkSpec + CompleteSpec
abbrev SourceMX (C : Committee) := StateT (SourceState C) (OracleComp (SpecX C))

def deferredQueryX (q : DeferredQuery C) : OracleComp (SpecX C) (DeferredSpec C q) :=
  liftM (OracleSpec.query (spec := SpecX C) (.inl (.inl (.inl q))))
def revealQueryX (k : HiddenKey) : OracleComp (SpecX C) Digest :=
  liftM (OracleSpec.query (spec := SpecX C) (.inl (.inl (.inr k))))
def markQ (b : Bool) : OracleComp (SpecX C) Unit :=
  liftM (OracleSpec.query (spec := SpecX C) (.inl (.inr b)))
def completeQ (p : Point) (t : Digest) : OracleComp (SpecX C) Bool :=
  liftM (OracleSpec.query (spec := SpecX C) (.inr (p, t)))

def expand (seeds : C.Term → HashOutput) :
    QueryImpl (SpecX C) (OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest))
  | .inl (.inl (.inl q)) => deferredQuery q
  | .inl (.inl (.inr k)) => revealQuery k
  | .inl (.inr _) => pure ()
  | .inr (p, t) => completePrf seeds p t

def sourceRevealX (k : HiddenKey) : SourceMX C Digest := do
  match (← get).revealed k with
  | some value => pure value
  | none =>
      let value ← liftM (revealQueryX (C := C) k)
      modify fun (st : SourceState C) => { st with revealed := Function.update st.revealed k (some value) }
      pure value

def sourceRevealDigestX : DeferredDigest → SourceMX C Digest
  | .known value => pure value
  | .secret k => sourceRevealX k

/-- The source plants only already-allocated points, using reveal-oracle values for
both input and low half. A cache conflict is retained in `consistent`. -/
def sourcePlantX (P : PublicParameter) (p : PendingInput) : SourceMX C Unit := do
  let some answer ← liftM (deferredQueryX (C := C) (.inspect p)) | pure ()
  let input ← sourceRevealX p.key
  let low ← sourceRevealDigestX answer.low
  let ok ← liftM (deferredQueryX (C := C) (.plant (.pending P p input)
    (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low))))
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }

/-- A new pending point whose input was already revealed uses the ordinary cache.
This includes a commitment built after P and previously queried by the forger. -/
def sourcePendingX (P : PublicParameter) (p : PendingInput) : SourceMX C DeferredOutput := do
  let prior ← liftM (deferredQueryX (C := C) (.inspect p))
  let known := (← get).revealed p.key
  match prior, known, p.next with
  | none, some input, none =>
      let value ← liftM (deferredQueryX (C := C) (.hash (.hash (p.input P input))))
      let _ ← liftM (deferredQueryX (C := C) (.record p value))
      let halves := XmssSecurity.Rom.hashOutputEquivDigestPair value
      modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
      pure ⟨halves.1, .known halves.2⟩
  | _, _, _ =>
      if prior.isNone && known.isSome && p.next.isSome then
        modify fun (st : SourceState C) => { st with consistent := false }
      let value ← liftM (deferredQueryX (C := C) (.pending p))
      if prior.isNone then modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
      pure value

/-- P completes the PRF constraint and plants every already-built commitment at the
newly revealed input. -/
def sourceReleaseOpeningX (P : PublicParameter) (_seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceMX C Unit := do
  if ((← get).revealed (.opening bottomLayer e)).isNone then
    let value ← sourceRevealX (.opening bottomLayer e)
    let ok ← liftM (completeQ (C := C) (.randomizer bottomLayer e) value)
    modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
    let pending := (← get).allocated.filter (fun p => p.key = .opening bottomLayer e)
    let _ ← pending.mapM (sourcePlantX P)
    pure ()

/-- Before returning a materialized PRF answer, P sees the cache that this query
will complete. The completing term can therefore still serve as slack. -/
def sourceHashX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) : SourceMX C HashOutput := do
  match q with
  | .prf _ (.randomizer lay e) =>
      if lay = bottomLayer then
        let backend ← liftM (deferredQueryX (C := C) .snapshot)
        if ReadyAfter seeds backend (← get).signing e q then sourceReleaseOpeningX P seeds e
  | _ => pure ()
  liftM (deferredQueryX (C := C) (.hash q))

/-- A virtually cached term completes P after its one counted call. -/
def sourceVirtualX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) : SourceMX C Unit := do
  let _ ← liftM (deferredQueryX (C := C) (.virtual T p))
  match p with
  | .randomizer lay e =>
      if lay = bottomLayer then
        let backend ← liftM (deferredQueryX (C := C) .snapshot)
        if OpeningReady seeds backend (← get).signing e then sourceReleaseOpeningX P seeds e
  | _ => pure ()

/-- Interpret the fixed setup/row programs with source-owned release bookkeeping.
Hash and virtual PRF calls retain one counted backend call apiece. -/
def sourceBackendX (P : PublicParameter) (seeds : C.Term → HashOutput) :
    QueryImpl (DeferredSpec C) (SourceMX C)
  | .hash q => sourceHashX P seeds q
  | .pending p => sourcePendingX P p
  | .virtual T p => sourceVirtualX P seeds T p
  | q => liftM (deferredQueryX q)

def sourceTopTreeX (P : PublicParameter) (seeds : C.Term → HashOutput) : SourceMX C TopTree :=
  simulateQ (sourceBackendX P seeds) (deferredTopTree P)

def sourceBottomRowX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceMX C (Digest × Digest × Digest) :=
  simulateQ (sourceBackendX P seeds) (deferredBottomRow e l)

/-- The commitment source follows `referenceJob`: all PRF terms, then one hash.
P may fire during the terms, and `sourcePendingX` then reuses the concrete cache. -/
def sourceCommitmentX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceMX C Digest := do
  let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.randomizer bottomLayer e)
  let value ← sourcePendingX P (.commitment e)
  pure (match value.low with | .known d => d | .secret _ => 0)


def sourceHashProgramX {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : OracleComp HashSpec α) : SourceMX C α :=
  simulateQ (sourceBackendX P seeds) (deferredHash oa)

/-- The top signature job repeats the prefix walk at its chosen position and keeps
its returned chain value symbolic. -/
def sourceTopValueX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) : SourceMX C DeferredDigest := do
  let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.chain topLayer (topKey b) l (digit 0))
  let values ← (List.finRange p.val).mapM fun i => sourcePendingX P (.top b l
    ⟨i.val, by have hi := i.isLt; have hp := p.isLt; change i.val < 3; change p.val < 4 at hp; omega⟩)
  pure ((values.getLast?.map (·.low)).getD (.secret (.topChain b l ⟨0, by decide⟩)))

/-- The verification suffix of an honestly generated symbolic top chain. -/
def sourceTopRecoverX (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (p : Digit) (initial : DeferredDigest) : SourceMX C Digest := do
  let values ← (List.finRange (3 - p.val)).mapM fun i => sourcePendingX P (.top b l
    ⟨p.val + i.val, by have hi := i.isLt; change p.val + i.val < 3; omega⟩)
  let last := (values.getLast?.map (·.low)).getD initial
  match last with
  | .known value => pure value
  | .secret _ =>
      modify fun (st : SourceState C) => { st with consistent := false }
      pure 0

/-- The actual two-run bottom ceremony, with a symbolic top signature. Both its
prefix signing walk and its verification suffix retain their original hash calls. -/
def sourceBottomTreeX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : SourceMX C (Option DeferredBottomTree) := do
  let indices := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let rows ← indices.mapM fun el => sourceBottomRowX P seeds el.1 el.2
  let commitments ← (List.finRange (2 ^ layerHeight)).mapM fun k =>
    sourceCommitmentX P seeds (bottomKey b k)
  let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.randomizer topLayer (topKey b))
  let cpk := fun e l => rows.getD (indices.idxOf (e, l)) (0, 0, 0)
  let commitment := fun (e : KeyIndex) => commitments.getD (e.val % 2 ^ layerHeight) 0
  let root ← sourceHashProgramX P seeds
    (merkleNode P bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)
  let message := bytesLE 16 root
  let baseAnswer ← sourcePendingX P (.base topLayer (topKey b) message)
  let base := match baseAnswer.low with | .known value => value | .secret _ => 0
  let some (randomness, encoding) ← sourceHashProgramX P seeds
    (grind P topLayer (topKey b) message base randomizerAttemptLimit 0) | pure none
  let values ← Concrete.sequenceFin fun l => sourceTopValueX P seeds b l (encoding l)
  let path ← sourceHashProgramX P seeds (merklePath P topLayer top.chainEnd (topKey b))
  let digest ← sourceHashProgramX P seeds (Concrete.messageDigest P topLayer (topKey b) message randomness)
  let some checked := Codeword.decode digest | pure none
  if checked ≠ encoding then
    modify fun (st : SourceState C) => { st with consistent := false }
    pure none
  else
    let ends ← Concrete.sequenceFin fun l => sourceTopRecoverX P b l (encoding l) (values l)
    let leaf ← sourceHashProgramX P seeds (Concrete.leafHash P topLayer (topKey b) ends)
    let topRoot ← sourceHashProgramX P seeds (Concrete.treeFold P topLayer (topKey b) path layerHeight leaf)
    if topRoot ≠ top.root then pure none else
      pure (some ⟨cpk, commitment, root, ⟨randomness, encoding, values, path⟩⟩)

/-- D17 retains successful and failed symbolic bottom builds. -/
def sourceBottomOnceX (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : SourceMX C (Option DeferredBottomTree) := do
  match (← get).trees b with
  | some tree => pure tree
  | none =>
      let tree ← sourceBottomTreeX P seeds top b
      modify fun (st : SourceState C) => { st with trees := Function.update st.trees b (some tree) }
      pure tree

/-- Q reveals only the canonical suffix and programs its already-masked PRF
points. Its caller supplies the position chosen by the successful codeword check. -/
def sourceReleaseBottomSuffixX (P : PublicParameter) (_seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) : SourceMX C Unit := do
  let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
  let _ ← keys.mapM fun p => do
    let value ← sourceRevealX (.bottomChain e l p)
    let offset ← if p.val = 0 then pure 0 else
      liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l ⟨p.val, by have hp := p.isLt; change p.val < 4; change p.val < 3 at hp; omega⟩)))
    let ok ← liftM (completeQ (C := C) (.chain bottomLayer e l ⟨p.val, by have hp := p.isLt; change p.val < 4; change p.val < 3 at hp; omega⟩) (value ^^^ offset))
    modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  let _ ← keys.mapM fun p => sourcePlantX P (.bottom e l p)
  pure ()

/-- R is invoked only when the tree request has a successful stored result.
Opening and chain suffixes are revealed at this boundary, never during its build. -/
def sourceReturnTreeX (P : PublicParameter) (_seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) : SourceMX C (BottomTree × Digest) := do
  let opening ← sourceRevealX (.opening topLayer (topKey b))
  let ok ← liftM (completeQ (C := C) (.randomizer topLayer (topKey b)) opening)
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  let pending := (← get).allocated.filter fun p => p.key = .opening topLayer (topKey b)
  let _ ← pending.mapM (sourcePlantX P)
  let values ← Concrete.sequenceFin fun l => do
    let start := tree.topSignature.encoding l
    let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
    let _ ← keys.mapM fun p => sourceRevealX (.topChain b l p)
    if start.val = 0 then
      let value ← sourceRevealX (.topChain b l ⟨0, by decide⟩)
      let ok ← liftM (completeQ (C := C) (.chain topLayer (topKey b) l (digit 0)) value)
      modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
    let _ ← keys.mapM fun p => sourcePlantX P (.top b l p)
    sourceRevealDigestX (tree.topSignature.chainValue l)
  pure (⟨tree.cpk, tree.commitment, tree.root,
    ⟨tree.topSignature.randomness, values, tree.topSignature.path⟩⟩, opening)

/-- A PRG call keeps its single charged stream-key lookup; private sampling is free. -/
def sourceRoX (prims : Primitives) (P : PublicParameter) (seeds : C.Term → HashOutput) :
    QueryImpl (RoSpec C) (SourceMX C)
  | .inl q => sourceHashX P seeds q
  | .inr inp => do
      let value ← sourceHashX P seeds (.streamKey inp.2.1)
      pure (prims.aes.eval (truncateHash value) inp.2.2)

def sourceRoProgramX {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp (RoSpec C) α) : SourceMX C α :=
  simulateQ (sourceRoX prims P seeds) oa

def sourcePartX (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) : SourceMX C Digest :=
  sourceRoProgramX prims x.1 x.2.1 (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J p message)

/-- The signing oracle uses the original guards and order of the two rounds.
The backend receives only a write-once message binding. -/
def sourceTsigX (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (TsigSpec C) (SourceMX C)
  | .corrupt i => do
      let st := (← get).signing
      if C.t - 1 < (insert i st.corrupt).card then pure none else
        modify fun (s : SourceState C) => { s with signing := { st with corrupt := insert i st.corrupt } }
        pure (some (dealtKeys x.1 x.2.1 x.2.2 i))
  | .tree b => do
      let some tree ← sourceBottomOnceX x.1 x.2.1 top b | pure none
      let result ← sourceReturnTreeX x.1 x.2.1 b tree
      let opening ← sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.randomizer topLayer (topKey b)))
      pure (some (result.1, opening))
  | .round1 i J e message => do
      let st := (← get).signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ breaksOneMessagePerKey st e message then pure none else
        modify fun (s : SourceState C) => { s with signing :=
          { st with bound := Function.update st.bound e (some message) } }
        let _ ← liftM (deferredQueryX (C := C) (.bindKey e message))
        let backend ← liftM (deferredQueryX (C := C) .snapshot)
        if OpeningReady x.2.1 backend (← get).signing e then sourceReleaseOpeningX x.1 x.2.1 e
        some <$> sourcePartX prims x i J (.randomizer bottomLayer e) message
  | .round2 i J e message parts => do
      let st := (← get).signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else
        let some tree ← sourceBottomOnceX x.1 x.2.1 top (treeOf e) | pure none
        let own ← sourcePartX prims x i J (.randomizer bottomLayer e) message
        let parts := Function.update parts i own
        let some values ← signRound2With (fun oa => sourceRoProgramX prims x.1 x.2.1 oa)
            (fun p => do
              match p with
              | .chain _ key l pos => sourceReleaseBottomSuffixX x.1 x.2.1 key l pos
              | _ => pure ()
              sourcePartX prims x i J p message)
            x.1 J (tree.commitment e) e message parts | pure none
        modify fun (s : SourceState C) => { s with signing :=
          { s.signing with released := s.signing.released ++ [(e, message, i)] } }
        pure (some values)

def sourceLocalX (prims : Primitives) (x : Keys3 C) : QueryImpl (LocalSpec C) (SourceMX C)
  | .inl n => liftM (deferredQueryX (C := C) (.uniform n))
  | .inr q => sourceRoX prims x.1 x.2.1 q

/-- The original hidden-key flag and candidate log are kept at adversary calls. -/
def sourceOraclesX (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (LocalSpec C + TsigSpec C) (SourceMX C)
  | .inl t => do
      let st ← get
      let _ ← liftM (markQ (C := C) (st.hiddenFlag || SigningCoreProof.hiddenHit x st.signing.corrupt t))
      let value ← sourceLocalX prims x t
      modify fun (s : SourceState C) => { s with hiddenFlag := st.hiddenFlag || SigningCoreProof.hiddenHit x st.signing.corrupt t, candidates := st.candidates ++ unreleasedCandidates x.1 st.signing st.exposed t }
      pure value
  | .inr q => do
      let _ ← liftM (markQ (C := C) (← get).hiddenFlag)
      let value ← sourceTsigX prims x top q
      modify fun (s : SourceState C) => { s with exposed := releasedTrees s.exposed q }
      pure value

/-- The reference signature suffix rebuilds the bottom tree as `honestSignature`
does. Its final top-chain reveals occur after its last counted query. -/
def sourceHonestSignatureX (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (e : KeyIndex) (message : Message) : SourceMX C (Option Signature) := do
  let some tree ← sourceBottomTreeX x.1 x.2.1 top (treeOf e) | pure none
  sourceReleaseOpeningX x.1 x.2.1 e
  let opening ← sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.randomizer bottomLayer e))
  let some (randomness, encoding) ← sourceRoProgramX prims x.1 x.2.1
    (signCodeword x.1 (tree.commitment e) e message opening) | pure none
  let values ← Concrete.sequenceFin fun l =>
    if (encoding l).val = 3 then pure (tree.cpk e l).2.2 else do
      sourceReleaseBottomSuffixX x.1 x.2.1 e l (encoding l)
      let value ← sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 (.chain bottomLayer e l (encoding l)))
      pure (if (encoding l).val = 0 then value else
        (if (encoding l).val = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ value)
  let path ← sourceHashProgramX x.1 x.2.1
    (merklePath x.1 bottomLayer (fun key l => (tree.cpk key l).2.2) e)
  let topValues ← Concrete.sequenceFin fun l => sourceRevealDigestX (tree.topSignature.chainValue l)
  let topPart : LayerSignature := ⟨tree.topSignature.randomness, topValues, tree.topSignature.path⟩
  pure (some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, values, path⟩ else topPart⟩)

/-- The fixed setup, adversary and verification program over the capped backend. -/
def sourceGameX (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    SourceMX C (Bool × TopTree × Forgery) := do
  let _ ← liftM (markQ (C := C) (← get).hiddenFlag)
  let top ← sourceTopTreeX x.1 x.2.1
  let forgery ← simulateQ (sourceOraclesX prims x top) (A ⟨top.root, x.1⟩ top)
  let st ← get
  let _ ← liftM (markQ (C := C) st.hiddenFlag)
  let verifyImpl : QueryImpl HashSpec (SourceMX C) := fun input => do
    let value ← sourceHashX x.1 x.2.1 (.hash input)
    modify fun (s : SourceState C) => { s with candidates := s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
    pure value
  let verified ← simulateQ verifyImpl (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)
  let fresh ← if (signersAt st.signing forgery.signature.leafIndex forgery.message).card < C.t then
    pure true else do
      let honest ← sourceHonestSignatureX prims x top forgery.signature.leafIndex forgery.message
      pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh, top, forgery)


def sourceProgramX (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :=
  (sourceGameX prims A x).run sourceInit

def mapX (seeds : C.Term → HashOutput) {α : Type} (p : SourceMX C α) : SourceM C α :=
  StateT.mk fun st => simulateQ (expand seeds) (p.run st)

@[simp] theorem mapX_pure (seeds : C.Term → HashOutput) {α : Type} (a : α) :
    mapX seeds (pure a) = pure a := by
  funext st
  simp [mapX, StateT.run_pure]

@[simp] theorem mapX_bind (seeds : C.Term → HashOutput) {α β : Type}
    (p : SourceMX C α) (f : α → SourceMX C β) :
    mapX seeds (p >>= f) = (mapX seeds p >>= fun a => mapX seeds (f a)) := by
  funext st
  change simulateQ (expand seeds) (p.run st >>= fun z => (f z.1).run z.2) = _
  rw [simulateQ_bind]
  rfl

@[simp] theorem mapX_get (seeds : C.Term → HashOutput) :
    mapX seeds (get : SourceMX C (SourceState C)) = get := by
  funext st
  rfl

@[simp] theorem mapX_modify (seeds : C.Term → HashOutput) (f : SourceState C → SourceState C) :
    mapX seeds (modify f) = modify f := by
  funext st
  rfl

@[simp] theorem mapX_lift (seeds : C.Term → HashOutput) {α : Type} (p : OracleComp (SpecX C) α) :
    mapX seeds (liftM p) = liftM (simulateQ (expand seeds) p) := by
  funext st
  change simulateQ (expand seeds) ((fun a => (a, st)) <$> p) = _
  rw [simulateQ_map]
  rfl

@[simp] theorem expand_deferred (seeds : C.Term → HashOutput) (q : DeferredQuery C) :
    simulateQ (expand seeds) (deferredQueryX q) = deferredQuery q := by
  simp [deferredQueryX, expand]
@[simp] theorem expand_reveal (seeds : C.Term → HashOutput) (k : HiddenKey) :
    simulateQ (expand seeds) (revealQueryX k) = revealQuery k := by
  simp [revealQueryX, expand]
@[simp] theorem expand_mark (seeds : C.Term → HashOutput) (b : Bool) :
    simulateQ (expand seeds) (markQ b) = pure () := by
  simp [markQ, expand]
@[simp] theorem expand_complete (seeds : C.Term → HashOutput) (p : Point) (t : Digest) :
    simulateQ (expand seeds) (completeQ p t) = completePrf seeds p t := by
  simp [completeQ, expand]


@[simp 1100] theorem mapX_deferred (seeds : C.Term → HashOutput) (q : DeferredQuery C) :
    mapX seeds (liftM (deferredQueryX q)) = (liftM (deferredQuery q) : SourceM C _) := by
  rw [mapX_lift, expand_deferred]

@[simp] theorem mapX_map (seeds : C.Term → HashOutput) {α β : Type}
    (f : α → β) (p : SourceMX C α) :
    mapX seeds (f <$> p) = f <$> mapX seeds p := by
  simp only [map_eq_bind_pure_comp, mapX_bind, mapX_pure, Function.comp_def]

@[simp] theorem mapX_ite (seeds : C.Term → HashOutput) {α : Type}
    (p : Prop) [Decidable p] (x y : SourceMX C α) :
    mapX seeds (if p then x else y) = if p then mapX seeds x else mapX seeds y := by
  split <;> rfl

@[simp] theorem mapX_mapM (seeds : C.Term → HashOutput) {α β : Type}
    (xs : List α) (f : α → SourceMX C β) :
    mapX seeds (xs.mapM f) = xs.mapM (fun a => mapX seeds (f a)) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.mapM_cons, ih]

@[simp] theorem mapX_sequenceFin (seeds : C.Term → HashOutput) {α : Type} {n : ℕ}
    (f : Fin n → SourceMX C α) :
    mapX seeds (Concrete.sequenceFin f) = Concrete.sequenceFin (fun a => mapX seeds (f a)) := by
  induction n with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih => simp [Concrete.sequenceFin, ih]

theorem mapX_simulateQ (seeds : C.Term → HashOutput) {ι α : Type} {spec : OracleSpec ι}
    (implX : QueryImpl spec (SourceMX C)) (impl : QueryImpl spec (SourceM C))
    (h : ∀ t, mapX seeds (implX t) = impl t) (oa : OracleComp spec α) :
    mapX seeds (simulateQ implX oa) = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, mapX_bind, h, ih]

@[simp] theorem mapX_simulate (seeds : C.Term → HashOutput) {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMX C)) (oa : OracleComp spec α) :
    mapX seeds (simulateQ impl oa) = simulateQ (fun t => mapX seeds (impl t)) oa :=
  mapX_simulateQ seeds _ _ (fun _ => rfl) oa

theorem mapX_signRound2With (seeds : C.Term → HashOutput)
    (liftX : ∀ {α : Type}, OracleComp (RoSpec C) α → SourceMX C α)
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → SourceM C α)
    (partX : Point → SourceMX C Digest) (part : Point → SourceM C Digest)
    (hlift : ∀ {α} (oa : OracleComp (RoSpec C) α), mapX seeds (liftX oa) = lift oa)
    (hpart : ∀ p, mapX seeds (partX p) = part p)
    (P : PublicParameter) (J : C.Quorum) (commitment : Digest)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    mapX seeds (signRound2With liftX partX P J commitment e message parts) =
      signRound2With lift part P J commitment e message parts := by
  simp only [signRound2With, mapX_bind, hlift]
  congr 1
  funext answer
  rcases answer with _ | ⟨randomness, encoding⟩ <;> simp [hpart]


@[simp] theorem mapX_sourceReveal (seeds : C.Term → HashOutput) (k : HiddenKey) :
    mapX seeds (sourceRevealX k) = sourceReveal k := by
  simp only [sourceRevealX, sourceReveal, mapX_bind, mapX_get]
  congr 1
  funext st
  cases st.revealed k <;> simp

@[simp] theorem mapX_sourceRevealDigest (seeds : C.Term → HashOutput) (d : DeferredDigest) :
    mapX seeds (sourceRevealDigestX d) = sourceRevealDigest d := by
  cases d <;> simp [sourceRevealDigestX, sourceRevealDigest]

@[simp] theorem mapX_sourcePlant (seeds : C.Term → HashOutput) (P : PublicParameter) (p : PendingInput) :
    mapX seeds (sourcePlantX P p) = sourcePlant P p := by
  simp only [sourcePlantX, sourcePlant, mapX_bind, mapX_deferred]
  congr 1
  funext answer
  cases answer <;> simp

@[simp] theorem mapX_sourcePending (seeds : C.Term → HashOutput) (P : PublicParameter) (p : PendingInput) :
    mapX seeds (sourcePendingX P p) = sourcePending P p := by
  simp only [sourcePendingX, sourcePending, mapX_bind, mapX_deferred, mapX_get]
  congr 1
  funext prior
  congr 1
  funext st
  cases prior <;> cases st.revealed p.key <;> cases p.next <;> simp [deferredQueryX, expand]

@[simp] theorem mapX_sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : mapX seeds (sourceReleaseOpeningX P seeds e) = sourceReleaseOpening P seeds e := by
  simp [sourceReleaseOpeningX, sourceReleaseOpening]

@[simp] theorem mapX_sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) : mapX seeds (sourceHashX P seeds q) = sourceHash P seeds q := by
  cases q with
  | prf seed p => cases p <;> simp [sourceHashX, sourceHash, deferredQueryX, expand]
  | _ => simp [sourceHashX, sourceHash, deferredQueryX, expand]

@[simp] theorem mapX_sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) : mapX seeds (sourceVirtualX P seeds T p) = sourceVirtual P seeds T p := by
  cases p <;> simp [sourceVirtualX, sourceVirtual]

@[simp] theorem mapX_sourceBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : DeferredQuery C) : mapX seeds (sourceBackendX P seeds q) = sourceBackend P seeds q := by
  cases q with
  | hash q => exact mapX_sourceHash P seeds q
  | pending p => exact mapX_sourcePending seeds P p
  | virtual T p => exact mapX_sourceVirtual P seeds T p
  | _ => exact mapX_deferred seeds _

@[simp] theorem mapX_sourceTopTree (P : PublicParameter) (seeds : C.Term → HashOutput) :
    mapX seeds (sourceTopTreeX P seeds) = sourceTopTree P seeds :=
  mapX_simulateQ seeds _ _ (mapX_sourceBackend P seeds) _

@[simp] theorem mapX_sourceBottomRow (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : mapX seeds (sourceBottomRowX P seeds e l) = sourceBottomRow P seeds e l :=
  mapX_simulateQ seeds _ _ (mapX_sourceBackend P seeds) _

@[simp] theorem mapX_sourceCommitment (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : mapX seeds (sourceCommitmentX P seeds e) = sourceCommitment P seeds e := by
  simp [sourceCommitmentX, sourceCommitment]
  rfl

@[simp] theorem mapX_sourceHashProgram {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : OracleComp HashSpec α) : mapX seeds (sourceHashProgramX P seeds oa) = sourceHashProgram P seeds oa :=
  mapX_simulateQ seeds _ _ (mapX_sourceBackend P seeds) _

@[simp] theorem mapX_sourceTopValue (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) :
    mapX seeds (sourceTopValueX P seeds b l p) = sourceTopValue P seeds b l p := by
  simp [sourceTopValueX, sourceTopValue]

@[simp] theorem mapX_sourceTopRecover (seeds : C.Term → HashOutput) (P : PublicParameter)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) (initial : DeferredDigest) :
    mapX seeds (sourceTopRecoverX P b l p initial) = sourceTopRecover P b l p initial := by
  simp only [sourceTopRecoverX, sourceTopRecover, mapX_bind, mapX_mapM, mapX_sourcePending]
  congr 1
  funext values
  split <;> simp_all

set_option maxHeartbeats 1000000 in
@[simp] theorem mapX_sourceBottomTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    mapX seeds (sourceBottomTreeX P seeds top b) = sourceBottomTree P seeds top b := by
  simp [sourceBottomTreeX, sourceBottomTree]
  apply bind_congr
  intro rows
  apply bind_congr
  intro commitments
  apply bind_congr
  intro ignored
  apply bind_congr
  intro root
  apply bind_congr
  intro baseAnswer
  apply bind_congr
  intro answer
  rcases answer with _ | ⟨randomness, encoding⟩
  · simp
  · simp
    apply bind_congr
    intro values
    apply bind_congr
    intro path
    apply bind_congr
    intro digest
    cases Codeword.decode digest <;> simp

@[simp] theorem mapX_sourceBottomOnce (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    mapX seeds (sourceBottomOnceX P seeds top b) = sourceBottomOnce P seeds top b := by
  simp only [sourceBottomOnceX, sourceBottomOnce, mapX_bind, mapX_get]
  congr 1
  funext st
  cases st.trees b <;> simp

@[simp] theorem mapX_sourceReleaseBottomSuffix (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    mapX seeds (sourceReleaseBottomSuffixX P seeds e l start) = sourceReleaseBottomSuffix P seeds e l start := by
  simp [sourceReleaseBottomSuffixX, sourceReleaseBottomSuffix]

@[simp] theorem mapX_sourceReturnTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) :
    mapX seeds (sourceReturnTreeX P seeds b tree) = sourceReturnTree P seeds b tree := by
  simp [sourceReturnTreeX, sourceReturnTree]

@[simp] theorem mapX_sourceRo (prims : Primitives) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : (RoSpec C).Domain) : mapX seeds (sourceRoX prims P seeds q) = sourceRo prims P seeds q := by
  cases q <;> simp [sourceRoX, sourceRo]

@[simp] theorem mapX_sourceRoProgram {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp (RoSpec C) α) :
    mapX seeds (sourceRoProgramX prims P seeds oa) = sourceRoProgram prims P seeds oa :=
  mapX_simulateQ seeds _ _ (mapX_sourceRo prims P seeds) _

@[simp] theorem mapX_sourcePart (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) :
    mapX x.2.1 (sourcePartX prims x i J p message) = sourcePart prims x i J p message := by
  simp [sourcePartX, sourcePart]

@[simp] theorem mapX_sourceTsig (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : (TsigSpec C).Domain) : mapX x.2.1 (sourceTsigX prims x top q) = sourceTsig prims x top q := by
  cases q <;> simp [sourceTsigX, sourceTsig, signRound2With]
  case tree b =>
    congr 1
    funext answer
    cases answer <;> simp
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

@[simp] theorem mapX_sourceLocal (prims : Primitives) (x : Keys3 C) (q : (LocalSpec C).Domain) :
    mapX x.2.1 (sourceLocalX prims x q) = sourceLocal prims x q := by
  cases q <;> simp [sourceLocalX, sourceLocal, deferredQueryX, expand]

@[simp] theorem sourceGet_ignore {α : Type} (p : SourceM C α) :
    ((get : SourceM C (SourceState C)) >>= fun _ => p) = p := by
  funext st
  change (pure (st, st) >>= fun z => p.run z.2) = p.run st
  simp

@[simp] theorem mapX_sourceOracles (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (q : (LocalSpec C + TsigSpec C).Domain) :
    mapX x.2.1 (sourceOraclesX prims x top q) = sourceOracles prims x top q := by
  cases q <;> simp [sourceOraclesX, sourceOracles]

@[simp] theorem mapX_sourceHonestSignature (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (e : KeyIndex) (message : Message) :
    mapX x.2.1 (sourceHonestSignatureX prims x top e message) = sourceHonestSignature prims x top e message := by
  simp [sourceHonestSignatureX, sourceHonestSignature]
  congr 1
  funext answer
  cases answer with
  | none => simp
  | some tree =>
      simp
      congr 1
      funext ignored
      congr 1
      funext opening
      congr 1
      funext codeword
      rcases codeword with _ | ⟨randomness, encoding⟩ <;> simp

@[simp] theorem mapX_sourceGame (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    mapX x.2.1 (sourceGameX prims A x) = sourceGame prims A x := by
  simp [sourceGameX, sourceGame]

/-- Expanding the atomic completions and erasing the marks recovers the exact
source program, including its entire final state, without any premise. -/
theorem sourceProgram_eq_expand (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    sourceProgram prims A x = simulateQ (expand x.2.1) (sourceProgramX prims A x) := by
  exact (congrArg (fun p => p.run sourceInit) (mapX_sourceGame prims A x)).symm

end ThresholdLeanXmssSecurity.SigningCompilerCouplingProof

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.mapX_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.mapX_simulateQ

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.mapX_signRound2With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.mapX_signRound2With

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.mapX_sourceGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.mapX_sourceGame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceProgram_eq_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerCouplingProof.sourceProgram_eq_expand
