import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTag
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareGuarded

/-!
# Cap-tagged first-bad transport for the signing compiler

The paired tag records the source hidden flag and backend cap at the first
share failure. The cap event before that failure transfers from the eager
fiber table to the fixed-pad compiler.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShareCap
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag

-- The following frozen-law port is SigningCompilerShareTable:26–124 with
-- the already generic SigningShareLazy tag specialized to Bool × Bool.
variable {C : Committee}

def capTag (st : CappedCompilerState C × Bool) : Bool × Bool := (st.2, st.1.2.2)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

abbrev FrozenStateC (C : Committee) :=
  SigningShareLazy.ShareState C.Term CPoint (SigningShareLazy.FrozenBad (Bool × Bool))

def lazyRunC (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) : ProbComp (CompilerOutcome C × ShareStateT C (Bool × Bool)) :=
  (simulateQ (lazyHandlerTag τ) (shareRunTag capTag prims A x q s pads)).run SigningShareLazy.init

def eagerHandlerC (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    QueryImpl (RunSpecT C (Bool × Bool)) (StateT (ShareStateT C (Bool × Bool)) ProbComp) :=
  SigningShareLazy.unifImpl (ShareStateT C (Bool × Bool)) +
    SigningShareLazy.eagerImpl (Tag := Bool × Bool) C.terms τ g

def eagerRunC (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput) :
    ProbComp (CompilerOutcome C × ShareStateT C (Bool × Bool)) :=
  (simulateQ (eagerHandlerC τ g) (shareRunTag capTag prims A x q s pads)).run SigningShareLazy.init

def tableRunC (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) : ProbComp (CompilerOutcome C × ShareStateT C (Bool × Bool)) := do
  let u ← $ᵗ (C.Term × CPoint → HashOutput)
  eagerRunC prims A x q s pads τ
    (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u)

@[simp] theorem erase_init :
    SigningShareLazy.erase (SigningShareLazy.init : ShareStateT C (Bool × Bool)) =
      (SigningShareLazy.init : FrozenStateC C) := rfl

private theorem initial_good (τ : CPoint → Digest) :
    SigningShareLazy.Good C.terms τ (SigningShareLazy.init : FrozenStateC C) := by
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.good_init C.terms τ (Or.inl (List.ne_nil_of_mem (mem_terms T)))

private theorem frozen_law (τ : CPoint → Digest) {α : Type}
    (oa : OracleComp (RunSpecT C (Bool × Bool)) α) :
    𝒟[(simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
      SigningShareLazy.lazyFrozen (Tag := Bool × Bool) C.terms τ) oa).run SigningShareLazy.init] =
    𝒟[do let u ← $ᵗ (C.Term × CPoint → HashOutput)
         (simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
           SigningShareLazy.eagerFrozen (Tag := Bool × Bool) C.terms τ
             (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u))
           oa).run SigningShareLazy.init] :=
  SigningShareLazy.lazyFrozen_eq_eagerFrozen C.terms terms_nodup mem_terms τ oa
    SigningShareLazy.init (initial_good τ)

/-- Equality of every full-outcome event before the first bad occurrence. -/
theorem nonbad_law (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (G : CompilerOutcome C × FrozenStateC C → Prop) :
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      lazyRunC prims A x q s pads τ] =
    Pr[fun z => G (z.1, SigningShareLazy.erase z.2) ∧ z.2.bad = none |
      tableRunC prims A x q s pads τ] := by
  unfold lazyRunC lazyHandlerTag
  rw [SigningShareLazy.lazyImpl_frozen_nonbad, erase_init]
  trans Pr[fun z => G z ∧ z.2.bad = none | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
      SigningShareLazy.eagerFrozen (Tag := Bool × Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u))
      (shareRunTag capTag prims A x q s pads)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_law τ _)
  · unfold tableRunC
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_nonbad C.terms τ _
      (shareRunTag capTag prims A x q s pads) SigningShareLazy.init G).symm

/-- The first-bad law retains its tag and kind and forgets only lucky. -/
theorem firstbad_law (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (r : SigningShareLazy.FrozenBad (Bool × Bool)) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      lazyRunC prims A x q s pads τ] =
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some r |
      tableRunC prims A x q s pads τ] := by
  unfold lazyRunC lazyHandlerTag
  rw [SigningShareLazy.lazyImpl_frozen_firstbad, erase_init]
  trans Pr[fun z => z.2.bad = some r | do
    let u ← $ᵗ (C.Term × CPoint → HashOutput)
    (simulateQ (SigningShareLazy.unifImpl (FrozenStateC C) +
      SigningShareLazy.eagerFrozen (Tag := Bool × Bool) C.terms τ
        (SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init : FrozenStateC C) u))
      (shareRunTag capTag prims A x q s pads)).run SigningShareLazy.init]
  · exact probEvent_congr' (fun _ _ => Iff.rfl) (frozen_law τ _)
  · unfold tableRunC
    simp only [probEvent_bind_eq_tsum]
    apply tsum_congr
    intro u
    apply congrArg (fun v => Pr[= u | $ᵗ (C.Term × CPoint → HashOutput)] * v)
    exact (SigningShareLazy.eagerImpl_frozen_firstbad C.terms τ _
      (shareRunTag capTag prims A x q s pads) SigningShareLazy.init r).symm



/-- Forget only the cap component of the first-bad tag. -/
def project (z : CompilerOutcome C × ShareStateT C (Bool × Bool)) :
    CompilerOutcome C × ShareState C := Prod.map id (mapBad Prod.fst) z

theorem lazyRunC_project (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest) :
    project <$> lazyRunC prims A x q s pads τ = Table.lazyRun prims A x q s pads τ := by
  have h := lazyRun_retag (C := C) (Tag := Bool × Bool) Prod.fst τ
    (shareRunTag capTag prims A x q s pads) SigningShareLazy.init
  rw [← shareRunTag_retag] at h
  exact h.symm

theorem eagerRunC_project (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (g : C.Term × CPoint → HashOutput) :
    project <$> eagerRunC prims A x q s pads τ g = Table.eagerRun prims A x q s pads τ g := by
  have h := eagerRun_retag (C := C) (Tag := Bool × Bool) Prod.fst τ g
    (shareRunTag capTag prims A x q s pads) SigningShareLazy.init
  rw [← shareRunTag_retag] at h
  exact h.symm

theorem tableRunC_project (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest) :
    project <$> tableRunC prims A x q s pads τ = Table.tableRun prims A x q s pads τ := by
  simp only [tableRunC, Table.tableRun, map_bind]
  congr 1
  funext u
  exact eagerRunC_project prims A x q s pads τ _

/-- The cap tag leaves the full eager compiler outcome unchanged. -/
theorem tableRunC_fst (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    𝒟[Prod.fst <$> tableRunC prims A x q s pads (NoFalse.tau s pads)] =
      𝒟[do let u ← $ᵗ (C.Term × CPoint → HashOutput)
           Guarded.compilerRunTable prims A x q s pads
             (SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads)
               (SigningShareLazy.init : Table.FrozenState C) u)] := by
  have h := congrArg (fun oa => Prod.fst <$> oa)
    (tableRunC_project prims A x q s pads (NoFalse.tau s pads))
  simp only [Functor.map_map, project, Prod.map, id_eq] at h
  rw [h]
  simp only [Table.tableRun, Guarded.compilerRunTable, map_bind]

/-- False hidden flags at the first share failure have zero mass. -/
theorem tableRunC_falseTag_zero (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    Pr[fun z => ∃ c k l, z.2.bad = some ((false, c), k, l) |
      tableRunC prims A x q s pads (NoFalse.tau s pads)] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro z hz hbad
  obtain ⟨c, k, l, hbad⟩ := hbad
  have hz' : project z ∈ support (Table.tableRun prims A x q s pads (NoFalse.tau s pads)) := by
    rw [← tableRunC_project, support_map]
    exact Set.mem_image_of_mem _ hz
  apply (probEvent_eq_zero_iff.mp (Guarded.tableRun_falseBad_zero prims A x hinj q s pads k))
    (project z) hz'
  simp only [project, Prod.map, mapBad, SigningShareLazy.erase, hbad, Option.map_some]


private theorem ordinary_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((ordinary P seeds q s pads t).run st)) : st.2.2 ≤ r.2.2.2 := by
  have sticky (h : st.2.2 = true) : r.2.2.2 = true := by
    cases t with
    | inr k => exact cappedCompiler_flag_sticky P seeds q s (.inr k) st h r hr
    | inl t =>
      cases t with
      | pad p =>
        simp only [ordinary, StateT.run, mem_support_pure_iff] at hr
        subst r
        cases hp : st.1.1.data.pads p <;> simpa only [padStep, hp] using h
      | _ => exact cappedCompiler_flag_sticky P seeds q s _ st h r hr
  cases h : st.2.2 with
  | false => simp
  | true => simp [sticky h]

def capOnly (st : CappedCompilerState C × Bool) : Bool := st.1.2.2

section CapSupport
attribute [local irreducible] hashTail

/-- Every backend query tags with the starting cap and never lowers that cap.
This is the cap analogue of Marks.backend_noMark, without a NoMark restriction. -/
theorem backend_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : (SpecX C).Domain) (bm : CappedCompilerState C × Bool) :
    Queries (Marks.TagIs (capOnly bm)) ((shareBackendTag capOnly P seeds q s pads t).run bm) ∧
      ∀ r ∈ support ((shareBackendTag capOnly P seeds q s pads t).run bm),
        capOnly bm ≤ capOnly r.2 := by
  have ho (t : DeferredQuery C ⊕ HiddenKey) :
      Queries (Marks.TagIs (capOnly bm)) ((ordinaryStepTag (Tag := Bool) P seeds q s pads t).run bm) ∧
        ∀ r ∈ support ((ordinaryStepTag (Tag := Bool) P seeds q s pads t).run bm), capOnly bm ≤ capOnly r.2 := by
    constructor
    · exact (Marks.queries_share (capOnly bm) .view trivial).bind fun view =>
        (Marks.queries_uniform _ (capOnly bm)).bind fun result => Queries.pure _
    · intro r hr
      simp only [ordinaryStepTag, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨view, _, result, hs, rfl⟩ := hr
      exact ordinary_cap P seeds q s pads t (merged seeds bm.1 view.1) result
        (mem_support_of_mem_support_liftComp (RunSpec C) _ _ hs)
  have hread (T : C.Term) (p : CPoint) :
      Queries (Marks.TagIs (capOnly bm)) ((readStepTag capOnly P seeds T p).run bm) ∧
        ∀ r ∈ support ((readStepTag capOnly P seeds T p).run bm), capOnly bm ≤ capOnly r.2 := by
    constructor
    · dsimp only [readStepTag, StateT.run]
      refine (Marks.queries_share (C := C) (capOnly bm) .view trivial).bind ?_
      intro view
      refine (Marks.queries_share (C := C) (capOnly bm) (.read T p (capOnly bm)) rfl).bind ?_
      intro value
      refine (Marks.queries_share (C := C) (capOnly bm) .view trivial).bind ?_
      intro view'
      refine (Marks.queries_uniform (C := C)
        (hashTail P seeds (key seeds (T, p)) (merged seeds bm.1 view.1) value
          (merge seeds bm.1.1.1.data.cache view'.1)) (capOnly bm)).bind ?_
      intro result
      exact Queries.pure _
    · intro r hr
      simp only [readStepTag, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨view, _, value, _, view', _, result, hs, rfl⟩ := hr
      have hs := mem_support_of_mem_support_liftComp (RunSpec C)
        (hashTail P seeds (key seeds (T, p)) (merged seeds bm.1 view.1) value
          (merge seeds bm.1.1.1.data.cache view'.1)) result hs
      simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hs
      obtain ⟨prefetched, _, rfl⟩ := hs
      exact le_rfl
  cases t with
  | inl t =>
    cases t with
    | inl t =>
      cases t with
      | inr k => exact ho (.inr k)
      | inl t =>
        cases t with
        | hash query =>
          simp only [shareBackendTag]
          cases hr : route seeds query with
          | none => exact ho _
          | some z => exact hread z.1 z.2
        | _ => exact ho _
    | inr mark =>
      refine ⟨Queries.pure _, ?_⟩
      intro r hr
      simp only [shareBackendTag, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact le_rfl
  | inr t =>
    rcases t with ⟨p, target⟩
    by_cases hp : Constrained p
    · simp only [shareBackendTag, hp, dite_true, StateT.run]
      refine ⟨(Marks.queries_share (capOnly bm) (.complete ⟨p, hp⟩ target (capOnly bm)) rfl).bind
        (fun _ => Queries.pure _), ?_⟩
      intro r hr
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, rfl⟩ := hr
      exact le_rfl
    · simp only [shareBackendTag, hp, dite_false, StateT.run]
      refine ⟨Queries.pure _, ?_⟩
      intro r hr
      simp only [mem_support_pure_iff] at hr
      subst r
      exact le_rfl


def capJointRun {α : Type} (H : QueryImpl (RunSpec C) (StateT (ShareState C) ProbComp))
    (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (oa : OracleComp (SpecX C) α)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) :=
  (simulateQ H ((simulateQ (shareBackendTag capOnly P seeds q s pads) oa).run bm)).run sh

/-- Recorded cap tags lie below the current cap throughout any source program. -/
theorem capJoint_tagLe {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (oa : OracleComp (SpecX C) α) (bm : CappedCompilerState C × Bool) (sh : ShareState C)
    (h : Marks.TagLe (capOnly bm) sh)
    (z : (α × (CappedCompilerState C × Bool)) × ShareState C)
    (hz : z ∈ support (capJointRun (Marks.handler τ draw finish) P seeds q s pads oa bm sh)) :
    Marks.TagLe (capOnly z.1.2) z.2 := by
  induction oa using OracleComp.inductionOn generalizing bm sh with
  | pure a =>
    simp only [capJointRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact h
  | query_bind t next ih =>
    simp only [capJointRun, simulateQ_bind, StateT.run_bind,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      mem_support_bind_iff] at hz
    obtain ⟨mid, hm, hz⟩ := hz
    have hs := backend_cap P seeds q s pads t bm
    have he := hs.2 mid.1 (Marks.mem_support_of_simulate_run _ _ _ hm)
    have ht := Marks.simulate_tagLe τ draw finish (capOnly bm) _ hs.1 sh h mid hm
    exact ih mid.1.1 mid.1.2 mid.2 (ht.mono he) hz

/-- The final merge changes only the cache, preserving the cap-tag invariant. -/
theorem capRun_tagLe (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → SigningShareLazy.Digest)
    (draw : C.Term × CPoint → ProbComp SigningShareLazy.HashOutput)
    (finish : C.Term → CPoint → SigningShareLazy.Digest → ShareState C →
      ProbComp SigningShareLazy.HashOutput)
    (z : CompilerOutcome C × ShareState C)
    (hz : z ∈ support ((simulateQ (Marks.handler τ draw finish)
      (shareRunTag capOnly prims A x q s pads)).run SigningShareLazy.init)) :
    Marks.TagLe z.1.2.2.2 z.2 := by
  simp only [shareRunTag, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨r, hr, view, hv, rfl⟩ := hz
  have h := capJoint_tagLe x.1 x.2.1 q s pads τ draw finish
    (sourceProgramX prims A x) _ _ (fun _ _ _ hb => by cases hb) r hr
  change view ∈ support (pure ((r.2.cache, r.2.done), r.2) : ProbComp _) at hv
  simp only [mem_support_pure_iff] at hv
  subst view
  exact h

end CapSupport


/-- The entire erased first-bad record has the same law. -/
theorem erased_bad_law (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest) :
    𝒟[(fun z => (SigningShareLazy.erase z.2).bad) <$> lazyRunC prims A x q s pads τ] =
      𝒟[(fun z => (SigningShareLazy.erase z.2).bad) <$> tableRunC prims A x q s pads τ] := by
  apply evalDist_ext
  intro bad
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  cases bad with
  | none =>
    simpa [SigningShareLazy.erase, Function.comp_def] using
      nonbad_law prims A x q s pads τ (fun _ => True)
  | some r => exact firstbad_law prims A x q s pads τ r

/-- A cap component recorded at first bad persists to the final lazy cap. -/
theorem lazyRunC_capTrue (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (z : CompilerOutcome C × ShareStateT C (Bool × Bool))
    (hz : z ∈ support (lazyRunC prims A x q s pads τ))
    (m : Bool) (k : SigningShareLazy.Kind) (l : Bool)
    (hb : z.2.bad = some ((m, true), k, l)) : z.1.2.2.2 = true := by
  have h := lazyRun_retag (C := C) (Tag := Bool × Bool) Prod.snd τ
    (shareRunTag capTag prims A x q s pads) SigningShareLazy.init
  rw [← shareRunTag_retag] at h
  have hz' : (z.1, mapBad Prod.snd z.2) ∈ support
      ((simulateQ (lazyHandlerTag τ) (shareRunTag capOnly prims A x q s pads)).run
        SigningShareLazy.init) := by
    erw [h]
    rw [support_map]
    exact Set.mem_image_of_mem _ hz
  have bound := capRun_tagLe prims A x q s pads τ (fun _ => $ᵗ SigningShareLazy.HashOutput)
    Witness.lazyFinish (z.1, mapBad Prod.snd z.2) hz'
  exact Bool.le_iff_imp.mp (bound true k l (by simp [mapBad, hb])) rfl

/-- Any lazy first bad on the actual target function entails the source hidden flag. -/
theorem lazyRunC_bad_hidden (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (z : CompilerOutcome C × ShareStateT C (Bool × Bool))
    (hz : z ∈ support (lazyRunC prims A x q s pads (NoFalse.tau s pads)))
    (m c : Bool) (k : SigningShareLazy.Kind) (l : Bool)
    (hb : z.2.bad = some ((m, c), k, l)) : z.1.1.2.hiddenFlag = true := by
  have hz' : project z ∈ support (Table.lazyRun prims A x q s pads (NoFalse.tau s pads)) := by
    rw [← lazyRunC_project, support_map]
    exact Set.mem_image_of_mem _ hz
  cases m with
  | false =>
    have hn := (probEvent_eq_zero_iff.mp
      (NoFalse.lazyRun_falseBad_zero prims A x hinj q s pads k)) (project z) hz'
    exact (hn (by simp [project, mapBad, SigningShareLazy.erase, hb])).elim
  | true =>
    exact Marks.shareRun_tagTrue prims A x q s pads (NoFalse.tau s pads)
      (fun _ => $ᵗ SigningShareLazy.HashOutput) Witness.lazyFinish (project z) hz' k l
      (by simp [project, mapBad, hb])

/-- The cap is already set before any share failure, or at the first failure. -/
def CapEarly (z : CompilerOutcome C × ShareStateT C (Bool × Bool)) : Prop :=
  (z.2.bad = none ∧ z.1.2.2.2 = true) ∨
    ∃ m k l, z.2.bad = some ((m, true), k, l)

def BadCap (bad : Option (SigningShareLazy.FrozenBad (Bool × Bool))) : Prop :=
  ∃ m k, bad = some ((m, true), k)

theorem badCap_iff (z : CompilerOutcome C × ShareStateT C (Bool × Bool)) :
    BadCap (SigningShareLazy.erase z.2).bad ↔
      ∃ m k l, z.2.bad = some ((m, true), k, l) := by
  simp only [BadCap, SigningShareLazy.erase]
  cases hb : z.2.bad with
  | none => simp
  | some r => rcases r with ⟨⟨m, c⟩, k, l⟩; cases c <;> simp

/-- Disjoint events add exactly; port of VCVio's probEvent_or_le proof. -/
private theorem probEvent_or_eq {α : Type} (oa : ProbComp α) (P Q : α → Prop)
    (disjoint : ∀ z, P z → Q z → False) :
    Pr[fun z => P z ∨ Q z | oa] = Pr[P | oa] + Pr[Q | oa] := by
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro z
  by_cases hp : P z <;> by_cases hq : Q z <;> simp_all


/-- The cap-before-first-bad branch transfers without requiring the compiler's
hidden flag to remain false after the two runs diverge. -/
theorem tableRunC_capEarly_le (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    Pr[fun z => z.1.1.2.hiddenFlag = true ∧ CapEarly z |
      tableRunC prims A x q s pads (NoFalse.tau s pads)] ≤
    Pr[fun z => z.1.2.hiddenFlag = true ∧ z.2.2.2 = true |
      compilerRunPads prims A x q s pads] := by
  let N : CompilerOutcome C × ShareStateT C (Bool × Bool) → Prop :=
    fun z => (z.1.1.2.hiddenFlag = true ∧ z.1.2.2.2 = true) ∧ z.2.bad = none
  let B : CompilerOutcome C × ShareStateT C (Bool × Bool) → Prop :=
    fun z => BadCap (SigningShareLazy.erase z.2).bad
  have disjoint : ∀ z, N z → B z → False := by
    intro z hn hb
    obtain ⟨m, k, l, h⟩ := (badCap_iff z).mp hb
    rw [hn.2] at h
    cases h
  have hn : Pr[N | lazyRunC prims A x q s pads (NoFalse.tau s pads)] =
      Pr[N | tableRunC prims A x q s pads (NoFalse.tau s pads)] :=
    nonbad_law prims A x q s pads (NoFalse.tau s pads)
      (fun z => z.1.1.2.hiddenFlag = true ∧ z.1.2.2.2 = true)
  have hb : Pr[B | lazyRunC prims A x q s pads (NoFalse.tau s pads)] =
      Pr[B | tableRunC prims A x q s pads (NoFalse.tau s pads)] := by
    have h : Pr[BadCap | (fun z => (SigningShareLazy.erase z.2).bad) <$>
        lazyRunC prims A x q s pads (NoFalse.tau s pads)] =
        Pr[BadCap | (fun z => (SigningShareLazy.erase z.2).bad) <$>
          tableRunC prims A x q s pads (NoFalse.tau s pads)] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (erased_bad_law prims A x q s pads (NoFalse.tau s pads))
    simpa only [probEvent_map, Function.comp_def, B] using h
  calc
    _ ≤ Pr[fun z => N z ∨ B z | tableRunC prims A x q s pads (NoFalse.tau s pads)] := by
      apply probEvent_mono
      intro z _ h
      rcases h.2 with noBad | bad
      · exact Or.inl ⟨⟨h.1, noBad.2⟩, noBad.1⟩
      · exact Or.inr ((badCap_iff z).mpr bad)
    _ = Pr[N | tableRunC prims A x q s pads (NoFalse.tau s pads)] +
        Pr[B | tableRunC prims A x q s pads (NoFalse.tau s pads)] := probEvent_or_eq _ N B disjoint
    _ = Pr[N | lazyRunC prims A x q s pads (NoFalse.tau s pads)] +
        Pr[B | lazyRunC prims A x q s pads (NoFalse.tau s pads)] := by rw [hn, hb]
    _ = Pr[fun z => N z ∨ B z | lazyRunC prims A x q s pads (NoFalse.tau s pads)] :=
      (probEvent_or_eq _ N B disjoint).symm
    _ ≤ Pr[fun z => z.1.1.2.hiddenFlag = true ∧ z.1.2.2.2 = true |
        lazyRunC prims A x q s pads (NoFalse.tau s pads)] := by
      apply probEvent_mono
      intro z hz h
      rcases h with hn | hb
      · exact hn.1
      · obtain ⟨m, k, l, hb⟩ := (badCap_iff z).mp hb
        exact ⟨lazyRunC_bad_hidden prims A x hinj q s pads z hz m true k l hb,
          lazyRunC_capTrue prims A x q s pads (NoFalse.tau s pads) z hz m k l hb⟩
    _ = _ := by
      rw [compilerRunPads_eq_shareRun prims A x hinj q s pads (NoFalse.tau s pads), probEvent_map]
      have h := congrArg (fun oa =>
        Pr[fun z : CompilerOutcome C × ShareState C =>
          z.1.1.2.hiddenFlag = true ∧ z.1.2.2.2 = true | oa])
        (lazyRunC_project prims A x q s pads (NoFalse.tau s pads))
      simpa only [probEvent_map, project, Prod.map, Function.comp_def, id_eq, Table.lazyRun] using h

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.tableRunC_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRunC_fst

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.tableRunC_falseTag_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRunC_falseTag_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.capJoint_tagLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capJoint_tagLe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.erased_bad_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms erased_bad_law

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShareCap.tableRunC_capEarly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRunC_capEarly_le

end ThresholdLeanXmssSecurity.SigningCompilerShareCap
