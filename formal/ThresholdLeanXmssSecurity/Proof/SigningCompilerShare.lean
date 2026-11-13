import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareSource
import ThresholdLeanXmssSecurity.Proof.SigningShareLazy

/-!
# Reifying the signing compiler's constrained shares

The constrained cache is indexed by the four source completion shapes. Its
complement retains the compiler cache, trace, count, reveals and cap flag.
The source alphabet excludes raw PRF plants and completions at other points.
The share interpreter is the lazy table of `SigningShareLazy`; marks supply
its tags without changing the original source state.

Query admissibility uses VCV-io's structural `IsQueryBound`. The cache frame
is `SigningCompilerCouplingProof.compilerImpl_prf_frame`; the XOR bridges
use the pinned threshold PRF's additive representation.
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
set_option allowUnsafeReducibility true in
attribute [local reducible] LeanXmss.digestBits LeanXmss.hashOutputBits
  XmssSecurity.digestBits XmssSecurity.hashOutputBits
attribute [local irreducible] sourceProgramX sourceProgram sourceGameX sourceGame

instance : Fintype CPoint := Fintype.ofFinite CPoint

def key (seeds : C.Term → HashOutput) (z : C.Term × CPoint) : Query C :=
  .prf (seeds z.1) z.2.val

def route (seeds : C.Term → HashOutput) (query : Query C) : Option (C.Term × CPoint) :=
  if h : ∃ z, query = key seeds z then some h.choose else none

theorem key_injective (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds) :
    Function.Injective (key seeds) := by
  rintro ⟨T, p⟩ ⟨U, r⟩ h
  obtain ⟨hs, hp⟩ := Query.prf.inj h
  exact Prod.ext (hinj hs) (Subtype.ext hp)

/-- Routing is exact under the original seed injectivity hypothesis. -/
theorem route_spec (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (query : Query C) (z : C.Term × CPoint) :
    route seeds query = some z ↔ query = key seeds z := by
  unfold route
  split
  next h =>
    constructor
    · intro he
      exact (Option.some.inj he) ▸ h.choose_spec
    · intro he
      exact congrArg some (key_injective seeds hinj (h.choose_spec.symm.trans he))
  next h =>
    constructor
    · intro he; cases he
    · intro he; exact (h ⟨z, he⟩).elim

@[simp] theorem route_key (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (z : C.Term × CPoint) : route seeds (key seeds z) = some z :=
  (route_spec seeds hinj _ z).mpr rfl

abbrev ShareCache (C : Committee) := C.Term × CPoint → Option SigningShareLazy.HashOutput

def merge (seeds : C.Term → HashOutput) (rest : HashCache C) (share : ShareCache C) :
    HashCache C := fun query => match route seeds query with
  | some z => share z
  | none => rest query

def erase (seeds : C.Term → HashOutput) (cache : HashCache C) : HashCache C :=
  fun query => if (route seeds query).isSome then none else cache query

def RestFree (seeds : C.Term → HashOutput) (rest : HashCache C) : Prop :=
  ∀ query z, route seeds query = some z → rest query = none

def DoneCached {B : Type} (st : SigningShareLazy.ShareState C.Term CPoint B) : Prop :=
  ∀ p ∈ st.done, ∀ T, st.cache (T, p) ≠ none

@[simp] theorem merge_key (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (rest : HashCache C) (share : ShareCache C) (z : C.Term × CPoint) :
    merge seeds rest share (key seeds z) = share z := by
  simp [merge, route_key seeds hinj]

theorem restFree_erase (seeds : C.Term → HashOutput) (cache : HashCache C) :
    RestFree seeds (erase seeds cache) := by
  intro query z h
  simp [erase, h]

theorem merge_erase (seeds : C.Term → HashOutput) (rest : HashCache C)
    (share : ShareCache C) : merge seeds (erase seeds rest) share = merge seeds rest share := by
  funext query
  cases h : route seeds query <;> simp [merge, erase, h]

theorem merge_split (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (cache : HashCache C) :
    merge seeds (erase seeds cache) (fun z => cache (key seeds z)) = cache := by
  funext query
  cases h : route seeds query with
  | none => simp [merge, erase, h]
  | some z =>
      have he := (route_spec seeds hinj query z).mp h
      simp only [merge, h]
      subst query
      rfl

def withCache (st : CappedCompilerState C) (cache : HashCache C) : CappedCompilerState C :=
  (({ st.1.1 with data := { st.1.1.data with cache := cache } }, st.1.2), st.2)

def merged (seeds : C.Term → HashOutput) (st : CappedCompilerState C)
    (share : ShareCache C) : CappedCompilerState C :=
  withCache st (merge seeds st.1.1.data.cache share)

def splitRest (seeds : C.Term → HashOutput) (st : CappedCompilerState C) :
    CappedCompilerState C := withCache st (erase seeds st.1.1.data.cache)

abbrev ShareSpec (C : Committee) := SigningShareLazy.ShareSpec C.Term CPoint Bool
abbrev RunSpec (C : Committee) := unifSpec + ShareSpec C
abbrev ShareM (C : Committee) :=
  StateT (CappedCompilerState C × Bool) (OracleComp (RunSpec C))

def shareQuery (t : SigningShareLazy.ShareQuery C.Term CPoint Bool) :
    OracleComp (RunSpec C) (ShareSpec C t) :=
  liftM (OracleSpec.query (spec := RunSpec C) (.inr t))

/-- Fixed pads use the same visible-map priority as `compilerProgramPads`. -/
def padStep (pads : Point → Digest) (p : Point) (st : CappedCompilerState C) :
    Digest × CappedCompilerState C :=
  match st.1.1.data.pads p with
  | some value => (value, st)
  | none => (pads p, (({ st.1.1 with data := { st.1.1.data with
      pads := Function.update st.1.1.data.pads p (some (pads p)) } }, st.1.2), st.2))

/-- All fresh randomness remains in the uniform summand. -/
def ordinary (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    : QueryImpl (DeferredSpec C + RevealSpec HiddenKey Digest)
      (StateT (CappedCompilerState C) ProbComp) := fun t st =>
  match t with
  | .inl (.pad p) => pure (padStep pads p st)
  | t => (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
      (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run st

/-- The existing cached-extra and trace suffix after one PRF cache read. -/
def hashTail (P : PublicParameter) (seeds : C.Term → HashOutput) (query : Query C)
    (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C) :
    ProbComp (HashOutput × CappedCompilerState C) := do
  let before := st.1.1
  let call : (WorldSpec C).Domain := .inr (.inr (.inl query))
  let prefetched ← (simulateQ (Query C →ₒ HashOutput).randomOracle
    (SigningR1FixedProof.cachedExtra seeds P
      (((before.data.cache, 0), []), compilerSigning before, false) call
      (((cache, 0), []), compilerSigning before, false))).run cache
  let next := { before with data := { before.data with cache := prefetched.2 }, trace := SigningLaneUnionProof.traceStepAt seeds P before.data.cache (compilerSigning before) call prefetched.2 before.trace }
  pure (value, ((next, st.1.2 + 1), st.2))

/-- A constrained read supplies the actual merged pre/post caches to the existing
cached-extra and trace handlers. It retains the count even on a cache hit. -/
def readStep (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : CPoint) : ShareM C HashOutput := fun st => do
  let view ← shareQuery (C := C) .view
  let value ← shareQuery (.read T p st.2)
  let view' ← shareQuery (C := C) .view
  let result ← liftM (hashTail P seeds (key seeds (T, p))
    (merged seeds st.1 view.1) value (merge seeds st.1.1.1.data.cache view'.1))
  pure (result.1, (splitRest seeds result.2, st.2))

def ordinaryStep (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) :
    ShareM C ((DeferredSpec C + RevealSpec HiddenKey Digest) t) := fun st => do
  let view ← shareQuery (C := C) .view
  let result ← liftM (ordinary P seeds q s pads t (merged seeds st.1 view.1))
  pure (result.1, (splitRest seeds result.2, st.2))

/-- The nonconstrained completion branch is total. Source admissibility rules it
out; no per-query equivalence is asserted for that branch or raw PRF plants. -/
def shareBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    QueryImpl (SpecX C) (ShareM C)
  | .inl (.inl (.inl (.hash query))) =>
      match route seeds query with
      | some (T, p) => readStep P seeds T p
      | none => ordinaryStep P seeds q s pads (.inl (.hash query))
  | .inl (.inl (.inl t)) => ordinaryStep P seeds q s pads (.inl t)
  | .inl (.inl (.inr k)) => ordinaryStep P seeds q s pads (.inr k)
  | .inl (.inr mark) => fun st => pure ((), st.1, mark)
  | .inr (p, target) => fun st =>
      if hp : Constrained p then do
        let value ← shareQuery (.complete ⟨p, hp⟩ target st.2)
        pure (value, st)
      else pure (false, st)

/-- The full compiler outcome; only share metadata remains in the outer state. -/
def shareRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    OracleComp (RunSpec C) (CompilerOutcome C) := do
  let result ← (simulateQ (shareBackend x.1 x.2.1 q s pads)
    (sourceProgramX prims A x)).run (((compilerInit, 0), fun _ => none, false), false)
  let view ← shareQuery (C := C) .view
  pure (result.1, merged x.2.1 result.2.1 view.1)


open scoped BigOperators

/-- Ordered XOR and the existing additive PRF aggregate use the same operation. -/
theorem xorSum_toXor {α : Type} (xs : List α) (f : α → Digest) :
    TprfCorrectnessProof.toXor (SigningShareLazy.xorSum xs f) =
      (xs.map (TprfCorrectnessProof.toXor ∘ f)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [SigningShareLazy.xorSum, List.foldr_cons,
        TprfSecurityProof.toXor_xor, List.map_cons, List.sum_cons]
      exact congrArg (TprfCorrectnessProof.toXor (f a) + ·) ih

theorem xorSum_terms (f : C.Term → Digest) :
    SigningShareLazy.xorSum C.terms f = termSum f := by
  have h := xorSum_toXor C.terms f
  have hs : (C.terms.map (TprfCorrectnessProof.toXor ∘ f)).sum = termSum f := by
    simp [termSum, Committee.terms, Finset.sum_map_toList, Function.comp_def]
  exact h.trans hs

theorem xorSum_otherTerms (f : C.Term → Digest) (T : C.Term) :
    SigningShareLazy.xorSum (C.terms.filter (· ≠ T)) f = otherTermSum f T := by
  have h := xorSum_toXor (C.terms.filter (· ≠ T)) f
  have hs : ((C.terms.filter (· ≠ T)).map (TprfCorrectnessProof.toXor ∘ f)).sum =
      otherTermSum f T := by
    rw [← List.sum_toFinset _ (terms_nodup.filter _)]
    simp [otherTermSum, Committee.terms, Function.comp_def, Finset.filter_ne']
  exact h.trans hs

theorem cachedTerm_merge (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (st : CappedCompilerState C) {B : Type}
    (share : SigningShareLazy.ShareState C.Term CPoint B) (p : CPoint) :
    cachedTerm seeds (merged seeds st share.cache).1.1.data p.val =
      fun T => SigningShareLazy.low share T p := by
  funext T
  change truncateHash ((merge seeds st.1.1.data.cache share.cache (key seeds (T, p))).getD 0) = _
  erw [merge_key seeds hinj]
  rfl

theorem share_sum (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (st : CappedCompilerState C) {B : Type}
    (share : SigningShareLazy.ShareState C.Term CPoint B) (p : CPoint) :
    SigningShareLazy.sum C.terms share p =
      termSum (cachedTerm seeds (merged seeds st share.cache).1.1.data p.val) := by
  erw [cachedTerm_merge seeds hinj, ← xorSum_terms]
  rfl

theorem share_others (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (st : CappedCompilerState C) {B : Type}
    (share : SigningShareLazy.ShareState C.Term CPoint B) (p : CPoint) (T : C.Term) :
    SigningShareLazy.others C.terms share p T =
      otherTermSum (cachedTerm seeds (merged seeds st share.cache).1.1.data p.val) T := by
  erw [cachedTerm_merge seeds hinj, ← xorSum_otherTerms]
  rfl

theorem share_slack (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (st : CappedCompilerState C) {B : Type}
    (share : SigningShareLazy.ShareState C.Term CPoint B) (p : CPoint) :
    SigningShareLazy.slack C.terms share p =
      firstUnmaterialized seeds (merged seeds st share.cache).1.1.data p.val := by
  unfold SigningShareLazy.slack firstUnmaterialized
  apply congrArg (fun f => C.terms.find? f)
  funext T
  change (share.cache (T, p)).isNone =
    (merge seeds st.1.1.data.cache share.cache (key seeds (T, p))).isNone
  erw [merge_key seeds hinj]

/-- A uniform-only computation leaves the entire share state unchanged. This is
VCV-io's `simulateQ_add_liftComp_left` followed by free-monad induction. -/
theorem unif_lift {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : ProbComp α) (st : σ) :
    (simulateQ (SigningShareLazy.unifImpl σ + impl)
      (liftM oa : OracleComp (unifSpec + spec) α)).run st =
      (fun a => (a, st)) <$> oa := by
  rw [show (liftM oa : OracleComp (unifSpec + spec) α) =
    OracleComp.liftComp oa (unifSpec + spec) from rfl, QueryImpl.simulateQ_add_liftComp_left]
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        SigningShareLazy.unifImpl, bind_map_left, ih, map_bind]
      rfl

abbrev ShareState (C : Committee) :=
  SigningShareLazy.ShareState C.Term CPoint (SigningShareLazy.ImplBad Bool)

def lazyHandler (τ : CPoint → SigningShareLazy.Digest) :
    QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp) :=
  SigningShareLazy.unifImpl (ShareState C) + SigningShareLazy.lazyImpl (Tag := Bool) C.terms τ

@[simp] theorem lazy_shareQuery (τ : CPoint → SigningShareLazy.Digest)
    (t : SigningShareLazy.ShareQuery C.Term CPoint Bool) :
    simulateQ (lazyHandler (C := C) τ) (shareQuery t) =
      SigningShareLazy.lazyImpl C.terms τ t := by
  simp [shareQuery, lazyHandler]

@[simp] theorem lazy_view_run (τ : CPoint → SigningShareLazy.Digest) (share : ShareState C) :
    (simulateQ (lazyHandler τ) (shareQuery (C := C) .view)).run share =
      pure ((share.cache, share.done), share) := by
  rw [lazy_shareQuery]
  rfl

@[simp] theorem lazy_lift (τ : CPoint → SigningShareLazy.Digest)
    {α : Type} (oa : ProbComp α) (share : ShareState C) :
    (simulateQ (lazyHandler τ) (liftM oa : OracleComp (RunSpec C) α)).run share =
      (fun a => (a, share)) <$> oa := unif_lift _ oa share

/-- The pad-table adapter is precisely the fixed-pad ordinary kernel. -/
theorem ordinary_eq_padStep (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C) :
    simulateQ (resolvePrivateTable pads) ((cappedPadNoiseRaw P seeds q s t).run st) =
      ordinary P seeds q s pads t st := by
  cases t with
  | inr k => exact resolvePrivateTable_lift pads _
  | inl t =>
      cases t with
      | pad p =>
          cases h : st.1.1.data.pads p <;>
            simp [cappedPadNoiseRaw, StateT.run, padNoiseRawRead, ordinary, padStep, h,
              resolvePrivateTable]
      | _ => exact resolvePrivateTable_lift pads _

theorem compilerProgramPads_ordinary (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) {α : Type}
    (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (st : CappedCompilerState C) :
    compilerProgramPads P seeds q s pads oa st =
      (simulateQ (ordinary P seeds q s pads) oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp [compilerProgramPads]
  | query_bind t next ih =>
      simp only [compilerProgramPads, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, ordinary_eq_padStep]
      apply bind_congr
      intro z
      exact ih z.1 z.2

/-- Updating a share is exactly the corresponding concrete PRF cache update. -/
theorem merge_update (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (rest : HashCache C) (share : ShareCache C) (z : C.Term × CPoint)
    (value : SigningShareLazy.HashOutput) :
    merge seeds rest (Function.update share z (some value)) =
      (merge seeds rest share).cacheQuery (key seeds z) value := by
  funext query
  by_cases h : query = key seeds z
  · subst query
    erw [merge_key seeds hinj, Function.update_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ h]
    cases hr : route seeds query with
    | none => simp only [merge, hr]
    | some y =>
        have hy : y ≠ z := by
          intro he
          subst y
          exact h ((route_spec seeds hinj query z).mp hr)
        simp only [merge, hr, Function.update_of_ne hy]

@[simp] theorem withCache_withCache (st : CappedCompilerState C)
    (a b : HashCache C) : withCache (withCache st a) b = withCache st b := rfl

@[simp] theorem withCache_same (st : CappedCompilerState C) :
    withCache st st.1.1.data.cache = st := rfl

theorem merged_put (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (st : CappedCompilerState C) (share : ShareState C) (T : C.Term) (p : CPoint)
    (value : SigningShareLazy.HashOutput) :
    merged seeds st (SigningShareLazy.put share T p value).cache =
      withCache (merged seeds st share.cache)
        ((merged seeds st share.cache).1.1.data.cache.cacheQuery (key seeds (T, p)) value) := by
  unfold merged SigningShareLazy.put
  rw [merge_update seeds hinj, withCache_withCache]
  rfl


/-- Uncounted non-pad steps retain the entire cap wrapper. -/
theorem ordinary_uncounted (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C) (ht : ¬deferredCounted t)
    (hpad : ∀ p, t ≠ .pad p) (st : CappedCompilerState C) :
    ordinary P seeds q s pads (.inl t) st =
      (fun r => (r.1, ((r.2, st.1.2), st.2))) <$> (compilerImpl P seeds t).run st.1.1 := by
  have he : ordinary P seeds q s pads (.inl t) st =
      (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s
          (.inl t)).run st := by
    cases t <;> try rfl
    exact (hpad _ rfl).elim
  rw [he]
  simp only [SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl, StateT.run_mk,
    cappedCall, ht, false_and, decide_false, Bool.or_false, if_false, Nat.add_zero,
    Functor.map_map]

@[simp] theorem ordinary_snapshot (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (st : CappedCompilerState C) :
    ordinary P seeds q s pads (.inl .snapshot) st = pure (st.1.1.data, st) := by
  rw [ordinary_uncounted P seeds q s pads .snapshot (by exact not_false) (by intro p; simp)]
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure]

@[simp] theorem ordinary_sample (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (st : CappedCompilerState C) :
    ordinary P seeds q s pads (.inl .sample) st =
      (fun value : HashOutput => (value, st)) <$> ($ᵗ HashOutput) := by
  rw [ordinary_uncounted P seeds q s pads .sample (by exact not_false) (by intro p; simp)]
  simp only [compilerImpl, deferredImpl, StateT.run, Functor.map_map]
  rfl

@[simp] theorem ordinary_plant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (st : CappedCompilerState C)
    (input : PlantInput) (value : HashOutput) :
    ordinary P seeds q s pads (.inl (.plant input value)) st =
      match st.1.1.data.cache input.query with
      | some prior => pure (decide (prior = value), st)
      | none => pure (true, withCache st (st.1.1.data.cache.cacheQuery input.query value)) := by
  rw [ordinary_uncounted P seeds q s pads (.plant input value) (by exact not_false) (by intro p; simp)]
  cases h : st.1.1.data.cache input.query <;>
    simp [compilerImpl, deferredImpl, StateT.run, h, withCache]

@[simp] theorem ordinary_deferredQuery (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C) (st : CappedCompilerState C) :
    (simulateQ (ordinary P seeds q s pads) (deferredQuery t)).run st =
      ordinary P seeds q s pads (.inl t) st := by
  simp only [deferredQuery, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
  rfl

/-- The source's silent fill and the lazy table's one-cell fill make the same draw. -/
theorem fillTerm_merge (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (st : CappedCompilerState C)
    (share : ShareState C) (p : CPoint) (T : C.Term) :
    (simulateQ (ordinary P seeds q s pads) (fillTerm seeds p.val T)).run
      (merged seeds st share.cache) =
      (fun share' => ((), merged seeds st share'.cache)) <$>
        SigningShareLazy.fillTerm (fun _ => $ᵗ SigningShareLazy.HashOutput) p T share := by
  simp only [fillTerm, simulateQ_bind, ordinary_deferredQuery,
    StateT.run_bind, ordinary_snapshot, pure_bind]
  change (simulateQ (ordinary P seeds q s pads)
    (if (merge seeds st.1.1.data.cache share.cache (key seeds (T, p))).isNone then do
      let value ← deferredQuery (C := C) .sample
      let _ ← deferredQuery (.plant (.prf (seeds T) p.val) value)
      pure ()
    else pure ())).run (merged seeds st share.cache) = _
  erw [merge_key seeds hinj]
  cases hc : share.cache (T, p) with
  | some value =>
      simp only [Option.isNone_some, Bool.false_eq_true, if_false, simulateQ_pure,
        StateT.run_pure, SigningShareLazy.fillTerm, hc, map_pure]
  | none =>
      simp only [Option.isNone_none, if_true, simulateQ_bind,
        ordinary_deferredQuery, StateT.run_bind, ordinary_sample, bind_map_left,
        ordinary_plant, simulateQ_pure, StateT.run_pure, SigningShareLazy.fillTerm,
        hc, Functor.map_map]
      have hm : (merged seeds st share.cache).1.1.data.cache
          (PlantInput.query (C := C) (.prf (seeds T) p.val)) = none := by
        exact (merge_key seeds hinj st.1.1.data.cache share.cache (T, p)).trans hc
      simp only [hm, pure_bind]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro value
      simp only [Function.comp_apply]
      erw [merged_put seeds hinj]
      rfl


section ShareFrame
open SigningShareLazy
variable {κ ι B : Type} [DecidableEq κ] [DecidableEq ι]

/- Verbatim port of the private `fillTerms_frame` in SigningShareLazy:1385.
Its cache-only statement does not require the later fiber invariant. -/
/-- Every completion fill preserves prior cache entries and the two non-cache fields. -/
theorem fillTerms_frame (draw : κ × ι → ProbComp SigningShareLazy.HashOutput) (p : ι)
    (todo : List κ) (st : SigningShareLazy.ShareState κ ι B) :
    ∀ st' ∈ support (SigningShareLazy.fillTerms draw p todo st),
      st'.done = st.done ∧ st'.bad = st.bad ∧
      (∀ y v, st.cache y = some v → st'.cache y = some v) ∧
      (∀ y, y.2 ≠ p ∨ y.1 ∉ todo → st'.cache y = st.cache y) ∧
      (∀ a ∈ todo, st'.cache (a, p) ≠ none) := by
  induction todo generalizing st with
  | nil =>
      intro st' h
      have he : st' = st := by simpa [SigningShareLazy.fillTerms] using h
      subst st'
      simp
  | cons a todo ih =>
      intro st' h
      change st' ∈ support (SigningShareLazy.fillTerm draw p a st >>= SigningShareLazy.fillTerms draw p todo) at h
      obtain ⟨mid, hm, hrest⟩ := mem_support_bind_peel _ _ h
      obtain ⟨hd, hb, hkeep, hout, hfilled⟩ := ih mid st' hrest
      cases hc : st.cache (a, p) with
      | some v =>
          have he : mid = st := by simpa [SigningShareLazy.fillTerm, hc] using hm
          subst mid
          refine ⟨hd, hb, hkeep, ?_, ?_⟩
          · intro y hy
            apply hout y
            rcases hy with hy | hy
            · exact Or.inl hy
            · exact Or.inr (fun h => hy (by simp [h]))
          · intro x hx
            rcases List.mem_cons.mp hx with he | he
            · subst x
              rw [hkeep (a, p) v hc]
              exact Option.some_ne_none _
            · exact hfilled x he
      | none =>
          obtain ⟨v, _, rfl⟩ := mem_support_map_peel (fun v => SigningShareLazy.put st a p v) (draw (a, p))
            (by simpa only [SigningShareLazy.fillTerm, hc] using hm)
          refine ⟨hd, hb, ?_, ?_, ?_⟩
          · intro y w hy
            apply hkeep y w
            by_cases he : y = (a, p)
            · subst y
              simp [hc] at hy
            · simp [SigningShareLazy.put, Function.update, he, hy]
          · intro y hy
            have hy' : y.2 ≠ p ∨ y.1 ∉ todo := by
              rcases hy with h | h
              · exact Or.inl h
              · exact Or.inr (fun he => h (by simp [he]))
            rw [hout y hy']
            have hyne : y ≠ (a, p) := by
              intro he
              subst y
              simp at hy
            simp [SigningShareLazy.put, Function.update, hyne]
          · intro x hx
            rcases List.mem_cons.mp hx with he | he
            · subst x
              rw [hkeep (a, p) v (by simp [SigningShareLazy.put])]
              exact Option.some_ne_none _
            · exact hfilled x he


end ShareFrame

/-- Filling a list preserves every already-completed row. -/
theorem doneCached_fillTerms (share : ShareState C) (h : DoneCached share)
    (p : CPoint) (todo : List C.Term) (result : ShareState C)
    (hr : result ∈ support (SigningShareLazy.fillTerms
      (fun _ => $ᵗ SigningShareLazy.HashOutput) p todo share)) : DoneCached result := by
  obtain ⟨hd, _, keep, _, _⟩ := fillTerms_frame _ p todo share result hr
  intro r hd' T
  have hn := h r (hd ▸ hd') T
  cases hc : share.cache (T, r) with
  | none => exact (hn hc).elim
  | some v => rw [keep _ _ hc]; exact Option.some_ne_none _

/-- Lazy completion may set arbitrary bad metadata; its completed rows stay full. -/
theorem doneCached_lazy (τ : CPoint → SigningShareLazy.Digest)
    (share : ShareState C) (h : DoneCached share)
    (query : SigningShareLazy.ShareQuery C.Term CPoint Bool)
    (result : ShareSpec C query × ShareState C)
    (hr : result ∈ support ((SigningShareLazy.lazyImpl C.terms τ query).run share)) :
    DoneCached result.2 := by
  cases query with
  | view =>
      have he : result = ((share.cache, share.done), share) := by
        simpa [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run] using hr
      subst result
      exact h
  | read T p tag =>
      cases hc : share.cache (T, p) with
      | some value =>
          have he : result = (value, share) := by
            simpa [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hc] using hr
          subst result
          exact h
      | none =>
          simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hc,
            mem_support_bind_iff, mem_support_pure_iff] at hr
          obtain ⟨value, _, rfl⟩ := hr
          intro r hd U
          by_cases he : (U, r) = (T, p)
          · simp [SigningShareLazy.put, he]
          · simpa [SigningShareLazy.put, Function.update_of_ne he] using h r hd U
  | complete p target tag =>
      by_cases hd : p ∈ share.done
      · have he : result = (decide (SigningShareLazy.sum C.terms share p = target), share) := by
          simpa [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hd] using hr
        subst result
        exact h
      · cases hs : SigningShareLazy.slack C.terms share p with
        | none =>
            simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hd,
              if_false, hs, mem_support_pure_iff] at hr
            subst result
            exact h
        | some T =>
            simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hd,
              if_false, hs, mem_support_bind_iff, support_map, mem_support_pure_iff] at hr
            obtain ⟨filled, hf, value, ⟨high, _, rfl⟩, rfl⟩ := hr
            have frames := fillTerms_frame (fun _ => $ᵗ SigningShareLazy.HashOutput)
              p (C.terms.filter (· ≠ T)) share filled hf
            have hdone := doneCached_fillTerms share h p _ filled hf
            intro r hr U
            by_cases he : (U, r) = (T, p)
            · simp [SigningShareLazy.put, he]
            · change (Function.update filled.cache (T, p) _ (U, r)) ≠ none
              rw [Function.update_of_ne he]
              rcases Finset.mem_insert.mp hr with hr | hr
              · subst r
                apply frames.2.2.2.2 U
                simp only [List.mem_filter, mem_terms, true_and, ne_eq, decide_eq_true_eq]
                intro hU
                exact he (Prod.ext hU rfl)
              · exact hdone r hr U


/-- Both completion implementations fill the same list in the same order. -/
theorem fillTerms_merge (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (st : CappedCompilerState C)
    (share : ShareState C) (p : CPoint) (todo : List C.Term) :
    (simulateQ (ordinary P seeds q s pads) (todo.mapM (fillTerm seeds p.val))).run
      (merged seeds st share.cache) =
      (fun share' => (List.replicate todo.length (), merged seeds st share'.cache)) <$>
        SigningShareLazy.fillTerms (fun _ => $ᵗ SigningShareLazy.HashOutput) p todo share := by
  induction todo generalizing share with
  | nil => simp [SigningShareLazy.fillTerms]
  | cons T todo ih =>
      simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, fillTerm_merge P seeds hinj,
        bind_map_left, ih, simulateQ_pure, StateT.run_pure, bind_pure_comp,
        Functor.map_map]
      change _ = _ <$> (SigningShareLazy.fillTerm
        (fun _ => $ᵗ SigningShareLazy.HashOutput) p T share >>=
          SigningShareLazy.fillTerms (fun _ => $ᵗ SigningShareLazy.HashOutput) p todo)
      rw [map_bind]
      simp only [simulateQ_map, StateT.run_map, ih, Functor.map_map]
      rfl

/-- Full lazy completion, including repeat completion, has the actual atomic
source completion law after merging the cache. Its bad metadata is unrestricted. -/
theorem complete_merge (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (st : CappedCompilerState C)
    (share : ShareState C) (hdone : DoneCached share)
    (τ : CPoint → SigningShareLazy.Digest) (p : CPoint) (target : Digest) (tag : Bool) :
    (simulateQ (ordinary P seeds q s pads) (completePrf seeds p.val target)).run
      (merged seeds st share.cache) =
      (fun result => (result.1, merged seeds st result.2.cache)) <$>
        (SigningShareLazy.lazyImpl C.terms τ (.complete p target tag)).run share := by
  have hsum := share_sum seeds hinj st share p
  have hslack := share_slack seeds hinj st share p
  simp only [completePrf, simulateQ_bind, ordinary_deferredQuery,
    StateT.run_bind, ordinary_snapshot, pure_bind]
  conv_rhs => simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run]
  by_cases hd : p ∈ share.done
  · have hn : SigningShareLazy.slack C.terms share p = none := by
      apply List.find?_eq_none.mpr
      intro T _
      cases hc : share.cache (T, p) with
      | none => exact (hdone p hd T hc).elim
      | some v => simp
    rw [← hslack, hn]
    simp only [simulateQ_pure, StateT.run_pure, SigningShareLazy.lazyImpl,
      SigningShareLazy.impl, hd, if_true, map_pure, hsum]
  · cases hs : SigningShareLazy.slack C.terms share p with
    | none =>
        rw [← hslack, hs]
        simp only [simulateQ_pure, StateT.run_pure, SigningShareLazy.lazyImpl,
          SigningShareLazy.impl, hd, if_false, hs, map_pure, hsum]
    | some T =>
        rw [← hslack, hs]
        simp only [simulateQ_bind, StateT.run_bind, fillTerms_merge P seeds hinj,
          bind_map_left, ordinary_deferredQuery, ordinary_snapshot, pure_bind,
          ordinary_sample, SigningShareLazy.lazyImpl, SigningShareLazy.impl,
          hd, if_false, hs, map_bind, bind_map_left]
        apply bind_congr_of_forall_mem_support
        intro filled hf
        have hm : filled.cache (T, p) = none := by
          have fr := fillTerms_frame (fun _ => $ᵗ SigningShareLazy.HashOutput)
            p (C.terms.filter (· ≠ T)) share filled hf
          rw [fr.2.2.2.1 (T, p) (Or.inr (by simp))]
          have hfirst := List.find?_some hs
          exact Option.isNone_iff_eq_none.mp hfirst
        have hm' : (merged seeds st filled.cache).1.1.data.cache
            (PlantInput.query (C := C) (.prf (seeds T) p.val)) = none :=
          (merge_key seeds hinj st.1.1.data.cache filled.cache (T, p)).trans hm
        simp only [ordinary_deferredQuery, ordinary_plant, hm', pure_bind,
          bind_map_left, map_pure]
        apply bind_congr
        intro high
        have ho := share_others seeds hinj st filled p T
        rw [ho, ordinary_deferredQuery, ordinary_plant, hm']
        exact congrArg (fun backend : CappedCompilerState C =>
          (pure (true, backend) : ProbComp (Bool × CappedCompilerState C)))
          (merged_put seeds hinj st filled T p
            (SigningShareLazy.pair.symm (SigningShareLazy.lowHash high,
              target ^^^ otherTermSum (cachedTerm seeds (merged seeds st filled.cache).1.1.data p.val) T))).symm


def Inv (seeds : C.Term → HashOutput) (st : CappedCompilerState C × Bool)
    (share : ShareState C) : Prop := RestFree seeds st.1.1.1.data.cache ∧ DoneCached share

def runShareProgram (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) {α : Type} (oa : OracleComp (SpecX C) α)
    (st : CappedCompilerState C × Bool) (share : ShareState C) :=
  (simulateQ (lazyHandler τ) ((simulateQ (shareBackend P seeds q s pads) oa).run st)).run share

def projectResult (seeds : C.Term → HashOutput) {α : Type}
    (result : (α × (CappedCompilerState C × Bool)) × ShareState C) :
    α × CappedCompilerState C :=
  (result.1.1, merged seeds result.1.2.1 result.2.cache)

theorem runShareProgram_bind (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) {α β : Type}
    (oa : OracleComp (SpecX C) α) (next : α → OracleComp (SpecX C) β)
    (st : CappedCompilerState C × Bool) (share : ShareState C) :
    runShareProgram P seeds q s pads τ (oa >>= next) st share =
      runShareProgram P seeds q s pads τ oa st share >>= fun r =>
        runShareProgram P seeds q s pads τ (next r.1.1) r.1.2 r.2 := by
  simp only [runShareProgram, simulateQ_bind, StateT.run_bind]

/-- The local compiler equivalence retains the full backend and carries only
cache fullness and the disjoint cache partition as induction invariants. -/
def StepLaw (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) (t : (SpecX C).Domain) : Prop :=
  ∀ st share, Inv seeds st share →
    (simulateQ (ordinary P seeds q s pads) (expand seeds t)).run
      (merged seeds st.1 share.cache) =
      projectResult seeds <$> runShareProgram P seeds q s pads τ
        (liftM ((SpecX C).query t)) st share ∧
    ∀ result ∈ support (runShareProgram P seeds q s pads τ
      (liftM ((SpecX C).query t)) st share), Inv seeds result.1.2 result.2

/-- Structural program reification uses only admissible one-query laws. -/
theorem program_eq_of_steps (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (steps : ∀ t, Allowed t → StepLaw P seeds q s pads τ t)
    {α : Type} (oa : OracleComp (SpecX C) α) (allowed : Queries Allowed oa)
    (st : CappedCompilerState C × Bool) (share : ShareState C) (hi : Inv seeds st share) :
    (simulateQ (ordinary P seeds q s pads) (simulateQ (expand seeds) oa)).run
      (merged seeds st.1 share.cache) =
      projectResult seeds <$> runShareProgram P seeds q s pads τ oa st share := by
  induction oa using OracleComp.inductionOn generalizing st share with
  | pure a => simp [runShareProgram, projectResult]
  | query_bind t next ih =>
      have ha := (isQueryBound_query_bind_iff ..).mp allowed
      have hs := steps t ha.1 st share hi
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        runShareProgram_bind, map_bind]
      rw [hs.1, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result hr
      exact ih result.1.1 (ha.2 result.1.1) result.1.2 result.2 (hs.2 result hr)

theorem merged_split_of_agree (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (st : CappedCompilerState C) (share : ShareCache C)
    (h : ∀ z, st.1.1.data.cache (key seeds z) = share z) :
    merged seeds (splitRest seeds st) share = st := by
  have hc : merge seeds (erase seeds st.1.1.data.cache) share = st.1.1.data.cache := by
    calc
      _ = merge seeds (erase seeds st.1.1.data.cache)
          (fun z => st.1.1.data.cache (key seeds z)) := by
        apply congrArg (merge seeds (erase seeds st.1.1.data.cache))
        funext z
        exact (h z).symm
      _ = _ := merge_split seeds hinj st.1.1.data.cache
  change withCache (withCache st (erase seeds st.1.1.data.cache))
    (merge seeds (erase seeds st.1.1.data.cache) share) = st
  rw [withCache_withCache, hc, withCache_same]

/-- Fixed pads retain the compiler's existing constrained-entry frame. -/
theorem ordinary_prf_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (result : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : result ∈ support (ordinary P seeds q s pads t st))
    (seed : HashOutput) (p : Point) (ht : ¬SourceWritesPrf seed p t) :
    result.2.1.1.data.cache (.prf seed p) = st.1.1.data.cache (.prf seed p) := by
  cases t with
  | inr k => exact cappedCompiler_prf_frame P seeds q s (.inr k) st result hr seed p ht
  | inl t =>
      cases t with
      | pad point =>
          cases hp : st.1.1.data.pads point <;>
            simp only [ordinary, padStep, hp, mem_support_pure_iff] at hr <;>
            subst result <;> rfl
      | _ => exact cappedCompiler_prf_frame P seeds q s _ st result hr seed p ht

/-- The view and independent-draw adapter keeps share metadata untouched. -/
theorem ordinaryStep_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) (t : DeferredQuery C ⊕ HiddenKey)
    (st : CappedCompilerState C × Bool) (share : ShareState C) :
    (simulateQ (lazyHandler τ) (ordinaryStep P seeds q s pads t st)).run share =
      (fun r => ((r.1, (splitRest seeds r.2, st.2)), share)) <$>
        ordinary P seeds q s pads t (merged seeds st.1 share.cache) := by
  simp only [ordinaryStep, simulateQ_bind, StateT.run_bind, lazy_view_run, pure_bind,
    lazy_lift, bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp,
    simulateQ_map, StateT.run_map, Functor.map_map]

/-- Every forwarded non-share step has the full compiler law after merging. -/
theorem ordinaryStep_merge (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → SigningShareLazy.Digest)
    (t : DeferredQuery C ⊕ HiddenKey)
    (frame : ∀ z : C.Term × CPoint, ¬SourceWritesPrf (seeds z.1) z.2.val t)
    (st : CappedCompilerState C × Bool) (share : ShareState C) :
    projectResult seeds <$>
      (simulateQ (lazyHandler τ) (ordinaryStep P seeds q s pads t st)).run share =
      ordinary P seeds q s pads t (merged seeds st.1 share.cache) := by
  rw [ordinaryStep_run, Functor.map_map, map_eq_bind_pure_comp]
  conv_rhs => rw [← bind_pure (ordinary P seeds q s pads t (merged seeds st.1 share.cache))]
  apply bind_congr_of_forall_mem_support
  intro result hr
  have he : merged seeds (splitRest seeds result.2) share.cache = result.2 := by
    apply merged_split_of_agree seeds hinj
    intro z
    exact (ordinary_prf_frame P seeds q s pads t (merged seeds st.1 share.cache)
      result hr (seeds z.1) z.2.val (frame z)).trans
        (merge_key seeds hinj st.1.1.1.data.cache share.cache z)
  simp only [Function.comp_apply, projectResult, he]


/-- A PRF query is counted once and cannot set the input-side cap flag. -/
theorem ordinary_hash_prf (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (seed : HashOutput) (p : Point) (st : CappedCompilerState C) :
    ordinary P seeds q s pads (.inl (.hash (.prf seed p))) st = (do
      let r ← ((Query C →ₒ HashOutput).randomOracle (.prf seed p)).run st.1.1.data.cache
      hashTail P seeds (.prf seed p) st r.1 r.2) := by
  simp only [ordinary, SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    deferredCounted, deferredInputSide, deferredCandidate, Option.isSome_none,
    Bool.false_eq_true, false_and, and_false, or_false, false_or, decide_false,
    Bool.or_false, if_true, compilerImpl, deferredImpl, StateT.run, StateT.mk,
    map_bind, bind_map_left, Functor.map_map, map_pure, hashTail]

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The actual grind suffix frames all constrained PRF entries. -/
theorem hashTail_frame (P : PublicParameter) (seeds : C.Term → HashOutput)
    (query : Query C) (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (result : HashOutput × CappedCompilerState C)
    (hr : result ∈ support (hashTail P seeds query st value cache))
    (seed : HashOutput) (p : Point) :
    result.2.1.1.data.cache (.prf seed p) = cache (.prf seed p) := by
  simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨prefetched, hp, rfl⟩ := hr
  have frame := SigningReleasedTransferProof.cachedExtra_frame seeds P
    (((st.1.1.data.cache, 0), []), compilerSigning st.1.1, false)
    (.inr (.inr (.inl query))) (((cache, 0), []), compilerSigning st.1.1, false)
    prefetched (by
      dsimp only [StateT.run] at hp ⊢
      with_reducible exact hp)
  exact frame.2 (.prf seed p) (SigningPartnerCompareProof.outsideTrials_prf P seed p)

/-- The lazy share read has exactly the original random-oracle cache law. -/
theorem read_merge (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (rest : HashCache C) (share : ShareState C) (τ : CPoint → SigningShareLazy.Digest)
    (T : C.Term) (p : CPoint) (tag : Bool) :
    (fun r => (r.1, merge seeds rest r.2.cache)) <$>
      (SigningShareLazy.lazyImpl C.terms τ (.read T p tag)).run share =
      ((Query C →ₒ HashOutput).randomOracle (key seeds (T, p))).run
        (merge seeds rest share.cache) := by
  have hm := merge_key seeds hinj rest share.cache (T, p)
  cases hc : share.cache (T, p) with
  | some value =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ (hm.trans hc)]
      simp [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hc]
  | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ (hm.trans hc)]
      simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, hc,
        map_bind, map_pure, bind_pure_comp, SigningShareLazy.put, Functor.map_map]
      simp only [merge_update seeds hinj]
      rfl

/-- The two views expose the share cache only; all extra draws remain independent. -/
theorem readStep_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (τ : CPoint → SigningShareLazy.Digest) (T : C.Term) (p : CPoint)
    (st : CappedCompilerState C × Bool) (share : ShareState C) :
    (simulateQ (lazyHandler τ) (readStep P seeds T p st)).run share = (do
      let r ← (SigningShareLazy.lazyImpl C.terms τ (.read T p st.2)).run share
      let result ← hashTail P seeds (key seeds (T, p)) (merged seeds st.1 share.cache)
        r.1 (merge seeds st.1.1.1.data.cache r.2.cache)
      pure ((result.1, (splitRest seeds result.2, st.2)), r.2)) := by
  simp only [readStep, simulateQ_bind, StateT.run_bind, lazy_view_run, pure_bind,
    lazy_lift, bind_map_left, simulateQ_pure, StateT.run_pure, lazy_shareQuery]
  simp only [SigningShareLazy.lazyImpl, SigningShareLazy.impl, StateT.run, pure_bind]

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The constrained read preserves every source-observable compiler field. -/
theorem readStep_merge (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → SigningShareLazy.Digest)
    (T : C.Term) (p : CPoint) (st : CappedCompilerState C × Bool) (share : ShareState C) :
    projectResult seeds <$>
      (simulateQ (lazyHandler τ) (readStep P seeds T p st)).run share =
      ordinary P seeds q s pads (.inl (.hash (key seeds (T, p))))
        (merged seeds st.1 share.cache) := by
  erw [ordinary_hash_prf, ← read_merge seeds hinj st.1.1.1.data.cache share τ T p st.2,
    bind_map_left, readStep_run, map_bind]
  apply bind_congr
  intro r
  simp only [map_bind, map_pure]
  conv_rhs => change (hashTail P seeds (key seeds (T, p)) (merged seeds st.1 share.cache)
    r.1 (merge seeds st.1.1.1.data.cache r.2.cache))
  conv_rhs => rw [← bind_pure (hashTail P seeds (key seeds (T, p))
    (merged seeds st.1 share.cache) r.1 (merge seeds st.1.1.1.data.cache r.2.cache))]
  apply bind_congr_of_forall_mem_support
  intro result hr
  have he : merged seeds (splitRest seeds result.2) r.2.cache = result.2 := by
    apply merged_split_of_agree seeds hinj
    intro z
    exact (hashTail_frame P seeds (key seeds (T, p)) (merged seeds st.1 share.cache)
      r.1 (merge seeds st.1.1.1.data.cache r.2.cache) result
      (by dsimp only [key] at hr ⊢; with_reducible exact hr) (seeds z.1) z.2.val).trans
        (merge_key seeds hinj st.1.1.1.data.cache r.2.cache z)
  simp only [projectResult, he]


theorem step_mark (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) (mark : Bool) :
    StepLaw P seeds q s pads τ (.inl (.inr mark)) := by
  intro st share hi
  simp only [runShareProgram, simulateQ_spec_query, shareBackend, StateT.run,
    simulateQ_pure, StateT.run_pure, SigningCompilerCouplingProof.expand, map_pure, projectResult,
    mem_support_pure_iff]
  exact ⟨rfl, fun result he => he ▸ hi⟩

theorem shareBackend_complete_run (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (p : Point) (target : Digest) (hp : Constrained p) (st : CappedCompilerState C × Bool) :
    (shareBackend P seeds q s pads (.inr (p, target))).run st =
      (fun a => (a, st)) <$> shareQuery (.complete ⟨p, hp⟩ target st.2) := by
  simp only [shareBackend, dif_pos hp]
  rfl

theorem step_complete (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → SigningShareLazy.Digest)
    (p : Point) (target : Digest) (hp : Constrained p) :
    StepLaw P seeds q s pads τ (.inr (p, target)) := by
  intro st share hi
  have run : runShareProgram P seeds q s pads τ
      (liftM ((SpecX C).query (.inr (p, target)))) st share =
      (fun r => ((r.1, st), r.2)) <$>
        (SigningShareLazy.lazyImpl C.terms τ (.complete ⟨p, hp⟩ target st.2)).run share := by
    rw [runShareProgram, simulateQ_spec_query, shareBackend_complete_run P seeds q s pads p target hp,
      simulateQ_map, StateT.run_map, lazy_shareQuery]
  rw [run]
  constructor
  · simp only [Functor.map_map, Function.comp_apply, projectResult]
    exact complete_merge P seeds hinj q s pads st.1 share hi.2 τ ⟨p, hp⟩ target st.2
  · intro result hr
    simp only [support_map] at hr
    obtain ⟨r, hr, rfl⟩ := hr
    exact ⟨hi.1, doneCached_lazy τ share hi.2 (.complete ⟨p, hp⟩ target st.2) r hr⟩

/-- Forwarded calls are admissible only when they frame the share-owned keys. -/
theorem step_ordinary (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → SigningShareLazy.Digest)
    (t : DeferredQuery C ⊕ HiddenKey)
    (handler : shareBackend P seeds q s pads (.inl (.inl t)) = ordinaryStep P seeds q s pads t)
    (frame : ∀ z : C.Term × CPoint, ¬SourceWritesPrf (seeds z.1) z.2.val t) :
    StepLaw P seeds q s pads τ (.inl (.inl t)) := by
  intro st share hi
  have run : runShareProgram P seeds q s pads τ
      (liftM ((SpecX C).query (.inl (.inl t)))) st share =
      (simulateQ (lazyHandler τ) (ordinaryStep P seeds q s pads t st)).run share := by
    simp only [runShareProgram, simulateQ_spec_query, handler, StateT.run]
  rw [run]
  constructor
  · have hexpand : (simulateQ (ordinary P seeds q s pads)
        (expand seeds (.inl (.inl t)))).run (merged seeds st.1 share.cache) =
        ordinary P seeds q s pads t (merged seeds st.1 share.cache) := by
      cases t <;> simp only [SigningCompilerCouplingProof.expand, deferredQuery, revealQuery,
        HasQuery.instOfMonadLift_query, simulateQ_spec_query] <;> rfl
    rw [hexpand]
    exact (ordinaryStep_merge P seeds hinj q s pads τ t frame st share).symm
  · rw [ordinaryStep_run]
    intro result hr
    obtain ⟨r, _, rfl⟩ := mem_support_map_peel _ _ hr
    exact ⟨restFree_erase seeds _, hi.2⟩

theorem step_read (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → SigningShareLazy.Digest)
    (T : C.Term) (p : CPoint) :
    StepLaw P seeds q s pads τ (.inl (.inl (.inl (.hash (key seeds (T, p)))))) := by
  intro st share hi
  have run : runShareProgram P seeds q s pads τ
      (liftM ((SpecX C).query (.inl (.inl (.inl (.hash (key seeds (T, p)))))))) st share =
      (simulateQ (lazyHandler τ) (readStep P seeds T p st)).run share := by
    simp only [runShareProgram, simulateQ_spec_query, shareBackend, route_key seeds hinj,
      StateT.run]
  rw [run]
  constructor
  · change (simulateQ (ordinary P seeds q s pads)
        (deferredQuery (.hash (key seeds (T, p))))).run (merged seeds st.1 share.cache) = _
    rw [ordinary_deferredQuery]
    exact (readStep_merge P seeds hinj q s pads τ T p st share).symm
  · rw [readStep_run]
    intro result hr
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨r, hr, outcome, _, rfl⟩ := hr
    exact ⟨restFree_erase seeds _, doneCached_lazy τ share hi.2 (.read T p st.2) r hr⟩

/-- The share reification is query-local precisely on the actual source alphabet. -/
theorem step_law (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → SigningShareLazy.Digest)
    (t : (SpecX C).Domain) (ha : Allowed t) : StepLaw P seeds q s pads τ t := by
  rcases t with ((t | k) | mark) | ⟨p, target⟩
  · cases t with
    | hash query =>
        cases hr : route seeds query with
        | some z =>
            have he := (route_spec seeds hinj query z).mp hr
            subst query
            exact step_read P seeds hinj q s pads τ z.1 z.2
        | none =>
            apply step_ordinary P seeds hinj q s pads τ (.inl (.hash query))
            · simp only [shareBackend, hr]
            · intro z he
              have hs := (route_spec seeds hinj query z).mpr he
              rw [hr] at hs
              cases hs
    | plant input value =>
        cases input with
        | prf seed p => exact ha.elim
        | pending parameter point input =>
            apply step_ordinary P seeds hinj q s pads τ (.inl (.plant (.pending parameter point input) value)) rfl
            intro z
            simp [SourceWritesPrf, WritesPrf, PlantInput.query]
    | _ =>
        apply step_ordinary P seeds hinj q s pads τ _ rfl
        intro z
        exact not_false
  · apply step_ordinary P seeds hinj q s pads τ (.inr k) rfl
    intro z
    exact not_false
  · exact step_mark P seeds q s pads τ mark
  · exact step_complete P seeds hinj q s pads τ p target ha


@[simp] theorem merge_empty (seeds : C.Term → HashOutput) :
    merge seeds (∅ : HashCache C) (fun _ => none) = ∅ := by
  funext query
  cases h : route seeds query <;> simp [merge, h]

@[simp] theorem merged_init (seeds : C.Term → HashOutput) :
    merged seeds ((compilerInit, 0), fun _ => none, false)
      (SigningShareLazy.init (κ := C.Term) (ι := CPoint)
        (B := SigningShareLazy.ImplBad Bool)).cache =
      ((compilerInit, 0), fun _ => none, false) := by
  change withCache ((compilerInit, 0), fun _ => none, false)
    (merge seeds ∅ (fun _ => none)) = _
  rw [merge_empty]
  rfl

/-- The final view merges the complete share cache without projecting any
component of the original compiler outcome. -/
theorem shareRun_final (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) :
    Prod.fst <$> (simulateQ (lazyHandler τ) (shareRun prims A x q s pads)).run
      (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) =
      projectResult x.2.1 <$> runShareProgram x.1 x.2.1 q s pads τ
        (sourceProgramX prims A x) (((compilerInit, 0), fun _ => none, false), false)
        (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
  simp only [shareRun, runShareProgram, simulateQ_bind, StateT.run_bind, map_bind,
    lazy_view_run, pure_bind, simulateQ_pure, StateT.run_pure, map_pure,
    bind_pure_comp, projectResult, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The fixed-pad compiler and the lazy share backend have the same full outcome
for arbitrary targets. Seed injectivity is the original collision-free condition. -/
theorem compilerRunPads_eq_shareRun (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hinj : Function.Injective x.2.1) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) :
    compilerRunPads prims A x q s pads =
      Prod.fst <$> (simulateQ (lazyHandler τ) (shareRun prims A x q s pads)).run
        (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
  rw [shareRun_final, compilerRunPads, sourceProgram_eq_expand, compilerProgramPads_ordinary]
  have hi : Inv x.2.1 (((compilerInit, 0), fun _ => none, false), false)
      (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
    constructor
    · intro query z hz
      rfl
    · simp [DoneCached, SigningShareLazy.init]
  simpa only [merged_init] using program_eq_of_steps x.1 x.2.1 q s pads τ
    (step_law x.1 x.2.1 hinj q s pads τ) (sourceProgramX prims A x)
    (sourceProgramX_allowed prims A x) _ _ hi

/-- B2 retains the source output, every source field, the entire merged backend,
trace, count, reveals and cap flag; share metadata stays in the outer state. -/
theorem evalDist_compilerRunPads_eq_shareRun (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (hinj : Function.Injective x.2.1) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest) :
    𝒟[compilerRunPads prims A x q s pads] =
      𝒟[Prod.fst <$> (simulateQ
        (SigningShareLazy.unifImpl (ShareState C) +
          SigningShareLazy.lazyImpl (Tag := Bool) C.terms τ)
        (shareRun prims A x q s pads)).run
          (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool))] := by
  rw [compilerRunPads_eq_shareRun prims A x hinj q s pads τ]
  rfl

end ThresholdLeanXmssSecurity.SigningCompilerShare

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.complete_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.complete_merge

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.readStep_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.readStep_merge

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.evalDist_compilerRunPads_eq_shareRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.evalDist_compilerRunPads_eq_shareRun
