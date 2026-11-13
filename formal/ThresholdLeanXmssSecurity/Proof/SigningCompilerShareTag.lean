import ThresholdLeanXmssSecurity.Proof.SigningCompilerShare

/-!
# Tags for the constrained-share compiler

Arbitrary tags label reads and completions while the compiler state remains
unchanged. Relabelling preserves the complete lazy and eager execution, mapping
only the tag of the optional first-bad record.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShareTag
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare
variable {C : Committee} {Tag Tag' : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
attribute [local irreducible] sourceProgramX sourceProgram sourceGameX sourceGame

abbrev RunSpecT (C : Committee) (Tag : Type) :=
  unifSpec + SigningShareLazy.ShareSpec C.Term CPoint Tag
abbrev ShareMT (C : Committee) (Tag : Type) :=
  StateT (CappedCompilerState C × Bool) (OracleComp (RunSpecT C Tag))

def shareQueryTag (t : SigningShareLazy.ShareQuery C.Term CPoint Tag) :
    OracleComp (RunSpecT C Tag) (SigningShareLazy.ShareSpec C.Term CPoint Tag t) :=
  liftM (OracleSpec.query (spec := RunSpecT C Tag) (.inr t))

def readStepTag (tagOf : CappedCompilerState C × Bool → Tag) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : CPoint) : ShareMT C Tag HashOutput := fun st => do
  let view ← shareQueryTag (C := C) .view
  let value ← shareQueryTag (.read T p (tagOf st))
  let view' ← shareQueryTag (C := C) .view
  let result ← liftM (hashTail P seeds (key seeds (T, p))
    (merged seeds st.1 view.1) value (merge seeds st.1.1.1.data.cache view'.1))
  pure (result.1, (splitRest seeds result.2, st.2))

def ordinaryStepTag (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) :
    ShareMT C Tag ((DeferredSpec C + RevealSpec HiddenKey Digest) t) := fun st => do
  let view ← shareQueryTag (C := C) .view
  let result ← liftM (ordinary P seeds q s pads t (merged seeds st.1 view.1))
  pure (result.1, (splitRest seeds result.2, st.2))

/-- The nonconstrained completion branch is total. Source admissibility rules it
out; no per-query equivalence is asserted for that branch or raw PRF plants. -/
def shareBackendTag (tagOf : CappedCompilerState C × Bool → Tag) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    QueryImpl (SpecX C) (ShareMT C Tag)
  | .inl (.inl (.inl (.hash query))) =>
      match route seeds query with
      | some (T, p) => readStepTag tagOf P seeds T p
      | none => ordinaryStepTag P seeds q s pads (.inl (.hash query))
  | .inl (.inl (.inl t)) => ordinaryStepTag P seeds q s pads (.inl t)
  | .inl (.inl (.inr k)) => ordinaryStepTag P seeds q s pads (.inr k)
  | .inl (.inr mark) => fun st => pure ((), st.1, mark)
  | .inr (p, target) => fun st =>
      if hp : Constrained p then do
        let value ← shareQueryTag (.complete ⟨p, hp⟩ target (tagOf st))
        pure (value, st)
      else pure (false, st)

/-- The full compiler outcome; only share metadata remains in the outer state. -/
def shareRunTag (tagOf : CappedCompilerState C × Bool → Tag) (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    OracleComp (RunSpecT C Tag) (CompilerOutcome C) := do
  let result ← (simulateQ (shareBackendTag tagOf x.1 x.2.1 q s pads)
    (sourceProgramX prims A x)).run (((compilerInit, 0), fun _ => none, false), false)
  let view ← shareQueryTag (C := C) .view
  pure (result.1, merged x.2.1 result.2.1 view.1)


@[simp] theorem shareBackendTag_snd (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    shareBackendTag Prod.snd P seeds q s pads = shareBackend P seeds q s pads := rfl

@[simp] theorem shareRunTag_snd (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    shareRunTag Prod.snd prims A x q s pads = shareRun prims A x q s pads := rfl

/-- Relabel queries and forward every uniform draw unchanged. -/
def retag (f : Tag → Tag') : QueryImpl (RunSpecT C Tag) (OracleComp (RunSpecT C Tag'))
  | .inl t => liftM (OracleSpec.query (spec := RunSpecT C Tag') (.inl t))
  | .inr (.read b p tag) => shareQueryTag (.read b p (f tag))
  | .inr (.complete p target tag) => shareQueryTag (.complete p target (f tag))
  | .inr .view => shareQueryTag .view

@[simp] theorem retag_lift (f : Tag → Tag') {α : Type} (oa : ProbComp α) :
    simulateQ (retag (C := C) f) (liftM oa) = (liftM oa : OracleComp (RunSpecT C Tag') α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      rfl

@[simp] theorem retag_view (f : Tag → Tag') :
    simulateQ (retag (C := C) f) (shareQueryTag .view) = shareQueryTag .view := by
  simp [shareQueryTag, retag]

theorem shareBackendTag_retag (f : Tag → Tag')
    (tagOf : CappedCompilerState C × Bool → Tag)
    (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : (SpecX C).Domain) (st : CappedCompilerState C × Bool) :
    simulateQ (retag f) ((shareBackendTag tagOf P seeds q s pads t).run st) =
      (shareBackendTag (f ∘ tagOf) P seeds q s pads t).run st := by
  rcases t with ((t | k) | mark) | ⟨p, target⟩
  · cases t with
    | hash query =>
      cases h : route seeds query with
      | some z =>
        rcases z with ⟨T, p⟩
        simp [shareBackendTag, h, readStepTag, StateT.run, shareQueryTag,
          simulateQ_bind, retag, retag_lift]; rfl
      | none => simp [shareBackendTag, h, ordinaryStepTag, StateT.run, retag_lift]; rfl
    | _ => simp [shareBackendTag, ordinaryStepTag, StateT.run, retag_lift]; rfl
  · simp [shareBackendTag, ordinaryStepTag, StateT.run, retag_lift]; rfl
  · simp [shareBackendTag, StateT.run]
  · by_cases hp : Constrained p <;>
      simp [shareBackendTag, hp, StateT.run, shareQueryTag, retag]; rfl

theorem shareRunTag_retag (f : Tag → Tag')
    (tagOf : CappedCompilerState C × Bool → Tag)
    (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    shareRunTag (f ∘ tagOf) prims A x q s pads =
      simulateQ (retag f) (shareRunTag tagOf prims A x q s pads) := by
  simp only [shareRunTag, simulateQ_bind, simulateQ_pure, retag_view]
  rw [simulateQ_StateT_compose _ _ _ (shareBackendTag_retag f tagOf x.1 x.2.1 q s pads)]
  rfl


open SigningShareLazy

/-- Preserve the kind and lucky bit of the first bad record. -/
def mapBad (f : Tag → Tag') (st : ShareState κ ι (ImplBad Tag)) :
    ShareState κ ι (ImplBad Tag') :=
  ⟨st.cache, st.done, st.bad.map (fun b => (f b.1, b.2))⟩

section Metadata
variable {κ ι : Type} [DecidableEq κ] [DecidableEq ι]

@[simp] theorem mapBad_put (f : Tag → Tag') (st : ShareState κ ι (ImplBad Tag))
    (b : κ) (p : ι) (v : SigningShareLazy.HashOutput) :
    mapBad f (put st b p v) = put (mapBad f st) b p v := rfl

theorem mapBad_fillTerm (f : Tag → Tag')
    (draw : κ × ι → ProbComp SigningShareLazy.HashOutput)
    (p : ι) (b : κ) (st : ShareState κ ι (ImplBad Tag)) :
    fillTerm draw p b (mapBad f st) = mapBad f <$> fillTerm draw p b st := by
  cases h : st.cache (b, p) <;> simp [SigningShareLazy.fillTerm, mapBad, h, Functor.map_map, put]

theorem mapBad_fillTerms (f : Tag → Tag')
    (draw : κ × ι → ProbComp SigningShareLazy.HashOutput)
    (p : ι) (order : List κ) (st : ShareState κ ι (ImplBad Tag)) :
    fillTerms draw p order (mapBad f st) = mapBad f <$> fillTerms draw p order st := by
  induction order generalizing st with
  | nil => simp [fillTerms]
  | cons b rest ih =>
      simp only [fillTerms, List.foldlM_cons, mapBad_fillTerm, bind_map_left, map_bind]
      exact bind_congr (fun z => ih z)

def implHandler (order : List C.Term) (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest →
      ShareState C.Term CPoint (ImplBad Tag) → ProbComp SigningShareLazy.HashOutput) :
    QueryImpl (RunSpecT C Tag) (StateT (ShareState C.Term CPoint (ImplBad Tag)) ProbComp) :=
  unifImpl (ShareState C.Term CPoint (ImplBad Tag)) + impl order τ draw finish

/-- Mapping first-bad tags commutes with either concrete completion kernel. -/
theorem impl_retag_step (f : Tag → Tag') (order : List C.Term)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest →
      ShareState C.Term CPoint (ImplBad Tag) → ProbComp SigningShareLazy.HashOutput)
    (finish' : C.Term → CPoint → SigningShareLazy.Digest →
      ShareState C.Term CPoint (ImplBad Tag') → ProbComp SigningShareLazy.HashOutput)
    (hf : ∀ b p target st, finish' b p target (mapBad f st) = finish b p target st)
    (t : (RunSpecT C Tag).Domain) (st : ShareState C.Term CPoint (ImplBad Tag)) :
    (simulateQ (implHandler order τ draw finish') (retag f t)).run (mapBad f st) =
      Prod.map id (mapBad f) <$> (implHandler order τ draw finish t).run st := by
  rcases t with t | t
  · simp [implHandler, retag, unifImpl, StateT.run, Prod.map]
  · cases t with
    | view => simp [implHandler, retag, shareQueryTag, impl, StateT.run, mapBad, Prod.map]
    | read b p tag =>
      cases hc : st.cache (b, p) with
      | some v => simp [implHandler, retag, shareQueryTag, impl, StateT.run, mapBad, hc, Prod.map]
      | none =>
        simp only [retag, shareQueryTag, simulateQ_spec_query, implHandler, QueryImpl.add_apply_inr,
          impl, StateT.run, mapBad, hc, map_bind, map_pure]
        apply bind_congr
        intro v
        simp [setsBad, put, sum, low, mapBad, Prod.map, Option.map_or]
    | complete p target tag =>
      by_cases hd : p ∈ st.done
      · simp [implHandler, retag, shareQueryTag, impl, StateT.run, mapBad, hd, sum, low, Prod.map]
      · cases hs : slack order st p with
        | none =>
          have hsl : slack order (mapBad f st) p = none := hs
          simp only [retag, shareQueryTag, simulateQ_spec_query, implHandler,
            QueryImpl.add_apply_inr, impl, StateT.run,
            show (mapBad f st).done = st.done from rfl, if_neg hd, hsl, hs, map_pure]
          cases hb : st.bad <;> simp [mapBad, sum, low, Prod.map, hb]
        | some b =>
          have hsl : slack order (mapBad f st) p = some b := hs
          simp only [retag, shareQueryTag, simulateQ_spec_query, implHandler, QueryImpl.add_apply_inr,
            impl, StateT.run, show (mapBad f st).done = st.done from rfl,
            if_neg hd, hsl, hs, mapBad_fillTerms, bind_map_left, hf, map_bind, map_pure]
          apply bind_congr
          intro filled
          apply bind_congr
          intro v
          by_cases ht : target = τ p <;> cases hb : st.bad <;>
            simp [mapBad, put, Prod.map, ht, hb]

end Metadata


/-- Transport the full run, with arbitrary initial first-bad metadata. -/
theorem impl_retag (f : Tag → Tag') (order : List C.Term)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest →
      ShareState C.Term CPoint (ImplBad Tag) → ProbComp SigningShareLazy.HashOutput)
    (finish' : C.Term → CPoint → SigningShareLazy.Digest →
      ShareState C.Term CPoint (ImplBad Tag') → ProbComp SigningShareLazy.HashOutput)
    (hf : ∀ b p target st, finish' b p target (mapBad f st) = finish b p target st)
    {α : Type} (oa : OracleComp (RunSpecT C Tag) α)
    (st : ShareState C.Term CPoint (ImplBad Tag)) :
    (simulateQ (implHandler order τ draw finish') (simulateQ (retag f) oa)).run (mapBad f st) =
      Prod.map id (mapBad f) <$> (simulateQ (implHandler order τ draw finish) oa).run st := by
  rw [← QueryImpl.simulateQ_compose]
  exact (map_run_simulateQ_eq_of_query_map_eq _ _ (mapBad f)
    (fun t st => (impl_retag_step f order τ draw finish finish' hf t st).symm) oa st).symm

abbrev ShareStateT (C : Committee) (Tag : Type) :=
  SigningShareLazy.ShareState C.Term CPoint (ImplBad Tag)

def lazyHandlerTag (τ : CPoint → SigningShareLazy.Digest) :
    QueryImpl (RunSpecT C Tag) (StateT (ShareStateT C Tag) ProbComp) :=
  unifImpl (ShareStateT C Tag) + lazyImpl (Tag := Tag) C.terms τ

def eagerHandlerTag (τ : CPoint → SigningShareLazy.Digest)
    (g : C.Term × CPoint → SigningShareLazy.HashOutput) :
    QueryImpl (RunSpecT C Tag) (StateT (ShareStateT C Tag) ProbComp) :=
  unifImpl (ShareStateT C Tag) + eagerImpl (Tag := Tag) C.terms τ g

/-- Lazy execution commutes with arbitrary tag maps, including noninjective maps. -/
theorem lazyRun_retag (f : Tag → Tag') (τ : CPoint → SigningShareLazy.Digest)
    {α : Type} (oa : OracleComp (RunSpecT C Tag) α) (st : ShareStateT C Tag) :
    (simulateQ (lazyHandlerTag τ) (simulateQ (retag f) oa)).run (mapBad f st) =
      Prod.map id (mapBad f) <$> (simulateQ (lazyHandlerTag τ) oa).run st := by
  apply impl_retag
  intros
  rfl

/-- Every fixed eager table has the same exact metadata transport. -/
theorem eagerRun_retag (f : Tag → Tag') (τ : CPoint → SigningShareLazy.Digest)
    (g : C.Term × CPoint → SigningShareLazy.HashOutput)
    {α : Type} (oa : OracleComp (RunSpecT C Tag) α) (st : ShareStateT C Tag) :
    (simulateQ (eagerHandlerTag τ g) (simulateQ (retag f) oa)).run (mapBad f st) =
      Prod.map id (mapBad f) <$> (simulateQ (eagerHandlerTag τ g) oa).run st := by
  apply impl_retag
  intros
  rfl

end ThresholdLeanXmssSecurity.SigningCompilerShareTag

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTag.shareRunTag_retag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTag.shareRunTag_retag

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTag.lazyRun_retag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTag.lazyRun_retag

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareTag.eagerRun_retag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShareTag.eagerRun_retag
