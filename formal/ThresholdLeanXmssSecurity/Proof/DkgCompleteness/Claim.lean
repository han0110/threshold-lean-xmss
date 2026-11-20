import ThresholdLeanXmss.Statement.Dkg
import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.SeedGen
import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.BottomRuns

/-!
# The completeness of the setup

`dkgCompleteness` proves the field `dkgCompleteness` of `Theorems`. The honest run of the real setup
gives an output to each operator, except with probability `dkgAbortError`, and its outputs are at
distance at most `dkgCompletenessError` from the outputs of the dealer.

`dkgCompleteness_of_abortOrCorrect` joins the four hops of `Hops.lean` with one premise,
`RealTreeAbortOrCorrect`, which says that each operator of an honest tree run ends with no output or
with the output of the ceremony. `realTreeAbortOrCorrect` proves the premise. A bad common coin of a
check makes every operator abort in the same round, so the honest run gives the output of the dealer
at every operator or no output at every operator. `realTree_bound` of `Proof/Tree.lean` with the
weight `0` charges nothing for such a coin, because its event is false when no operator has an
output. `fixedLocal_support_run` moves the result from the random oracle to a fixed good `H`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCompletenessProof

section Fixed

variable {C : Committee} (prims : Primitives)

/-- An answer of `H` under a good `h` that agrees with the cache is an answer of the random oracle. -/
theorem hashAnswer_mem (h : Query C → HashOutput) (hg : Good prims h) (q : Query C) (s : HashCache C)
    (ha : Agrees h s) : ∃ s', (h q, s') ∈ support ((hashAnswer prims q).run s) ∧ s ≤ s' ∧ Agrees h s' := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    refine ⟨s, ?_, le_rfl, ha⟩
    rw [hashAnswer_of_isFixed prims hm, hg input hm]
    simp
  · rw [hashAnswer_of_not_isFixed prims hq]
    rcases hs : s q with _ | v
    · refine ⟨s.cacheQuery q (h q), ?_, QueryCache.le_cacheQuery _ hs, fun q' v' hq' => ?_⟩
      · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs]
        erw [support_map, Set.mem_image]
        exact ⟨h q, by simp, rfl⟩
      · by_cases e : q' = q
        · subst e; simp at hq'; exact hq'
        · rw [QueryCache.cacheQuery_of_ne _ _ e] at hq'
          exact ha q' v' hq'
    · refine ⟨s, ?_, le_rfl, ha⟩
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs, ha q v hs]
      simp

/-- An answer of a local query under a good `h` that agrees with the cache is an answer of
`localAnswer`. -/
theorem localAnswer_mem (h : Query C → HashOutput) (hg : Good prims h) (t : (LocalSpec C).Domain)
    (s : HashCache C) (ha : Agrees h s) (u : (LocalSpec C).Range t) (hu : u ∈ support (fixedLocal prims h t)) :
    ∃ s', (u, s') ∈ support ((localAnswer prims t).run s) ∧ s ≤ s' ∧ Agrees h s' := by
  rcases t with n | q | x
  · refine ⟨s, ?_, le_rfl, ha⟩
    change (u, s) ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s)
    simp [unifFwdImpl]
  · change u ∈ support (pure (h q) : ProbComp _) at hu
    have hu' : u = h q := by simpa using hu
    subst hu'
    exact hashAnswer_mem prims h hg q s ha
  · change u ∈ support (pure (prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2) : ProbComp _) at hu
    have hu' : u = prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2 := by simpa using hu
    subst hu'
    obtain ⟨s', hs', hle, ha'⟩ := hashAnswer_mem prims h hg (.streamKey x.2.1) s ha
    refine ⟨s', ?_, hle, ha'⟩
    change _ ∈ support ((prgAnswer prims x).run s)
    unfold prgAnswer
    rw [StateT.run_bind]
    simp only [support_bind, Set.mem_iUnion]
    exact ⟨_, hs', by simp⟩

/-- Every run with `H` fixed to a good `h` is a run of the random oracle from each cache that
agrees with `h`, with an end cache that agrees with `h`. -/
theorem fixedLocal_support_run (h : Query C → HashOutput) (hg : Good prims h) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∀ s, Agrees h s → ∀ a ∈ support (simulateQ (fixedLocal prims h) oa),
      ∃ s', (a, s') ∈ support ((simulateQ (localAnswer prims) oa).run s) ∧ s ≤ s' ∧ Agrees h s' := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s ha a hx
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨s, by simp, le_rfl, ha⟩
  | query_bind t k ih =>
    intro s ha a hx
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      support_bind, Set.mem_iUnion] at hx
    obtain ⟨u, hu, hx⟩ := hx
    obtain ⟨s₁, h₁, hle₁, ha₁⟩ := localAnswer_mem prims h hg t s ha u hu
    obtain ⟨s₂, h₂, hle₂, ha₂⟩ := ih u s₁ ha₁ a hx
    refine ⟨s₂, ?_, hle₁.trans hle₂, ha₂⟩
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion]
    exact ⟨(u, s₁), h₁, h₂⟩


end Fixed

section Assembly

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `DkgCompleteness` from `RealTreeAbortOrCorrect`. -/
theorem dkgCompleteness_of_abortOrCorrect
    (correct : ∀ prims, RealTreeAbortOrCorrect K circuits settings prims)
    (batch : 0 < settings.batchSize) (runs : 0 < runLimit)
    (prims : Primitives) (compute : CircuitsCompute circuits prims.Th) (b : Fin (2 ^ layerHeight)) :
    (Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[∃ i,
        (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none]).toReal ≤
        dkgAbortError (E := E) circuits settings C b ∧
      letI : MeasurableSpace (SetupOutputs C) := ⊤
      measureTVDist (Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b))
          (Prod.fst <$> runWorld prims (dealerDkg b)) ≤
        dkgCompletenessError (E := E) circuits settings C b :=
  dkgCompleteness_of_hops K circuits settings runLimit (topRunsHop K circuits settings runLimit)
    (bottomRunsHop_of_abortOrCorrect K circuits settings runLimit correct) seedGenHop dealerAbort
    batch runs prims compute b

/-- An honest run of a tree from a cache with no MPC entry and no coin entry gives, with probability
one, the output of the dealer at every operator or no output at every operator. -/
def RealTreeAbortBound (prims : Primitives) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (o₀ : Option TreeOutput) (s : HashCache C),
    NoMpc s → CacheOK ∅ 0 s →
    (∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree) →
    Pr{let z ← (simulateQ (localAnswer prims)
      (realTree K circuits settings top tree parameter seeds pairKeys)).run' s}[z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none] ≤ 0

omit [Fintype E] [DecidableEq E] in
theorem realTreeAbortOrCorrect_of_bound (prims : Primitives)
    (hbound : RealTreeAbortBound K circuits settings prims) : RealTreeAbortOrCorrect K circuits settings prims := by
  intro hsize top tree parameter seeds pairKeys h hg o ho i
  set a := D prims h ((fun r (_ : C.Party) => r.1) <$> dealerCeremony circuits settings parameter seeds top tree)
  have ha : a ∈ support (simulateQ (fixedLocal prims h) (idealTree circuits settings parameter seeds top tree)) := by
    rw [idealTree, simulateQ_fixedLocal_liftComp]
    simp [a]
  obtain ⟨s₀, hs₀, -, ha₀⟩ := fixedLocal_support_run prims h hg _ ∅ (fun _ _ hq => by cases hq) a ha
  obtain ⟨hn₀, hc₀, o₀, -, ho₀⟩ := idealTree_value prims circuits settings parameter seeds top tree hsize ∅ noMpc_empty cacheOK_empty _ hs₀
  obtain ⟨s₁, hs₁, -, -⟩ := fixedLocal_support_run prims h hg _ s₀ ha₀ o ho
  have hzero := hbound hsize top tree parameter seeds pairKeys o₀ s₀ hn₀ hc₀ ho₀
  have hnot : ¬ (o ≠ (fun _ => o₀) ∧ o ≠ fun _ => none) := by
    intro hev
    refine (lt_of_lt_of_le ((OracleComp.prEvent_pos_iff _ _).2 ⟨o, ?_, hev⟩) hzero).false
    rw [StateT.run'_eq, support_map]
    exact ⟨(o, s₁), hs₁, rfl⟩
  have hceq : o₀ = ceremonyAt prims circuits parameter seeds h top tree := ho₀ h s₀ hg le_rfl ha₀
  by_cases e : o = fun _ => none
  · exact Or.inl (congrFun e i)
  · have : o = fun _ => o₀ := by by_contra e'; exact hnot ⟨e', e⟩
    exact Or.inr (by rw [this, hceq])

/-- `realTree_bound` with the weight `0`. The event is false when no operator has an output, so a
failed coin costs nothing. -/
theorem realTreeAbortBound (prims : Primitives) : RealTreeAbortBound K circuits settings prims := by
  intro hsize top tree parameter seeds pairKeys o₀ s hn hs ho
  let : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩⟩
  simpa using realTree_bound prims K circuits settings parameter seeds pairKeys top tree o₀ s hn hs ho
    (fun z => z ≠ (fun _ => o₀) ∧ z ≠ fun _ => none) (by simp) 0 (by simp) hsize

/-- In an honest run of a tree with `H` fixed to a good function, each operator ends with no output
or with the output of the ceremony. -/
theorem realTreeAbortOrCorrect (prims : Primitives) : RealTreeAbortOrCorrect K circuits settings prims :=
  realTreeAbortOrCorrect_of_bound K circuits settings prims (realTreeAbortBound K circuits settings prims)

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.DkgCompletenessProof.dkgCompleteness_of_abortOrCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCompleteness_of_abortOrCorrect

/-- info: 'ThresholdLeanXmssSecurity.DkgCompletenessProof.realTreeAbortOrCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realTreeAbortOrCorrect

end ThresholdLeanXmssSecurity.DkgCompletenessProof

namespace ThresholdLeanXmssSecurity

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The field `dkgCompleteness` of `Theorems`. -/
theorem dkgCompleteness (compute : CircuitsCompute circuits prims.Th) :
    DkgCompleteness prims K circuits settings runLimit := fun batch runs b =>
  DkgCompletenessProof.dkgCompleteness_of_abortOrCorrect K circuits settings runLimit
    (DkgCompletenessProof.realTreeAbortOrCorrect K circuits settings) batch runs prims compute b

/-- info: 'ThresholdLeanXmssSecurity.dkgCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dkgCompleteness

end ThresholdLeanXmssSecurity
