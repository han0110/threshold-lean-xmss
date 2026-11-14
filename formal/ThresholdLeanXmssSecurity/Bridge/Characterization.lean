import ThresholdLeanXmss.Statement
import VCVio.OracleComp.EvalDist.Sum
import VCVio.OracleComp.Constructions.SampleableType.Measure
import ToMathlib.MeasureTheory.Measure.Coupling.Maximal

/-!
# The probability terms of the statement layer in elementary terms

VCVio at `5f9baf12` gives a computation a measure. VCVio at `cbd4144` gave it a mass function.
This file states what each probability term of `ThresholdLeanXmss/Statement.lean` is, with numbers
of `ℝ≥0∞` and `ℝ` and with sums over the outputs.

The import lines and the part `Dictionary` are the only text that names a definition of one VCVio
revision. Each theorem after the dictionary uses the names of the dictionary. The same theorem
text, with the dictionary of the other revision, states the same fact about that revision.

The three equations `outputProbability_pure`, `outputProbability_query` and `eventProbability_bind`
fix the probability of each output of each computation. `outputProbability_unique` proves this.
-/

set_option autoImplicit false

namespace ThresholdLeanXmss.Characterization

noncomputable section

/-! ## Dictionary -/

open OracleComp OracleSpec HashSig LeanXmss ENNReal

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec] {α β : Type}

/-- The probability that `mx` returns `a`. -/
abbrev outputProbability (mx : OracleComp spec α) (a : α) : ℝ≥0∞ := Pr{let x ← mx}[x = a]

/-- The probability that the output of `mx` satisfies `p`. -/
abbrev eventProbability (mx : OracleComp spec α) (p : α → Prop) : ℝ≥0∞ := Pr{let x ← mx}[p x]

/-- The probability that `mx` returns no output. -/
abbrev failureProbability (mx : OracleComp spec α) : ℝ≥0∞ := prFail mx

/-- The total variation distance of `Completes`. -/
abbrev totalVariation (mx my : OracleComp spec α) : ℝ :=
  letI : MeasurableSpace α := ⊤
  measureTVDist mx my

/-- The equality of two distributions of `DealerTreeStatement`. -/
abbrev SameDistribution (mx my : OracleComp spec α) : Prop := mx =ᵈ my

/-- The real experiment of the PRF game. -/
abbrev prfRealRun {K D R : Type} (prf : PRFScheme K D R) (adversary : PRFScheme.PRFAdversary D R) :
    ProbComp Bool :=
  prf.prfRealExperiment adversary

/-- The ideal experiment of the PRF game. -/
abbrev prfIdealRun {D R : Type} [DecidableEq D] [SampleableType R]
    (adversary : PRFScheme.PRFAdversary D R) : ProbComp Bool :=
  PRFScheme.prfIdealExperiment adversary

/-- The PRF advantage as a real number, as `TreeSecurityStatement` reads it. -/
abbrev prfAdvantageReal {K D R : Type} [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (adversary : PRFScheme.PRFAdversary D R) : ℝ :=
  (prf.prfAdvantage adversary).toReal

/-! ## The evaluation of a computation -/

/-- The computation `pure a` returns `a` with probability 1. -/
theorem outputProbability_pure [DecidableEq α] (a b : α) :
    outputProbability (pure a : OracleComp spec α) b = if b = a then 1 else 0 := by
  simp [prEvent_pure, eq_comm]

/-- One query returns each answer with the same probability. -/
theorem outputProbability_query (t : spec.Domain) (u : spec.Range t) :
    outputProbability (query t : OracleComp spec (spec.Range t)) u =
      (Nat.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  classical
  have := OracleSpec.UniformAnswerMeasure.finite_range (spec := spec) t
  let := Fintype.ofFinite (spec.Range t)
  have hcard : (Finset.univ.filter fun x : spec.Range t => x = u).card = 1 :=
    Finset.card_eq_one.mpr ⟨u, by ext x; simp⟩
  rw [outputProbability, OracleComp.prEvent_query_eq_card_div, hcard, Nat.cast_one, one_div,
    Nat.card_eq_fintype_card]

/-- The probability of an event after `mx >>= f` is the sum over the outputs `a` of `mx` of the
probability of `a` times the probability of the event after `f a`. -/
theorem eventProbability_bind (mx : OracleComp spec α) (f : α → OracleComp spec β) (p : β → Prop) :
    eventProbability (mx >>= f) p = ∑' a, outputProbability mx a * eventProbability (f a) p := by
  have : ∀ t, Finite (spec.Range t) := OracleSpec.UniformAnswerMeasure.finite_range
  exact OracleComp.prEvent_bind_eq_tsum mx f p

/-- The probability of an output after `mx >>= f`, as a sum over the outputs of `mx`. -/
theorem outputProbability_bind (mx : OracleComp spec α) (f : α → OracleComp spec β) (b : β) :
    outputProbability (mx >>= f) b = ∑' a, outputProbability mx a * outputProbability (f a) b :=
  eventProbability_bind mx f _

/-- A function that satisfies the three equations is the probability of an output. -/
theorem outputProbability_unique (P : {α : Type} → OracleComp spec α → α → ℝ≥0∞)
    (pure_eq : ∀ {α : Type} [DecidableEq α] (a b : α),
      P (pure a : OracleComp spec α) b = if b = a then 1 else 0)
    (query_eq : ∀ (t : spec.Domain) (u : spec.Range t),
      P (query t : OracleComp spec (spec.Range t)) u = (Nat.card (spec.Range t) : ℝ≥0∞)⁻¹)
    (bind_eq : ∀ {α β : Type} (mx : OracleComp spec α) (f : α → OracleComp spec β) (b : β),
      P (mx >>= f) b = ∑' a, P mx a * P (f a) b)
    (mx : OracleComp spec α) (a : α) : P mx a = outputProbability mx a := by
  classical
  induction mx using OracleComp.inductionOn with
  | pure x => rw [pure_eq, outputProbability_pure]
  | query_bind t oa ih =>
    rw [bind_eq, outputProbability_bind]
    have hP := query_eq t
    have hquery := outputProbability_query t
    rw [HasQuery.instOfMonadLift_query] at hP hquery
    exact tsum_congr fun u => by rw [hP, hquery, ih]

/-- The probability of an event is the sum of the probabilities of its outputs. -/
theorem eventProbability_eq_tsum (mx : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    eventProbability mx p = ∑' a, if p a then outputProbability mx a else 0 := by
  have : ∀ t, Finite (spec.Range t) := OracleSpec.UniformAnswerMeasure.finite_range
  exact OracleComp.prEvent_eq_tsum_ite mx p

/-- The probabilities of the outputs have the sum 1. -/
theorem tsum_outputProbability (mx : OracleComp spec α) : ∑' a, outputProbability mx a = 1 := by
  have : ∀ t, Finite (spec.Range t) := OracleSpec.UniformAnswerMeasure.finite_range
  exact OracleComp.tsum_prEvent_eq_one mx

/-- A computation always returns an output. -/
theorem failureProbability_eq_zero (mx : OracleComp spec α) : failureProbability mx = 0 :=
  OracleComp.prFail_eq_zero mx

/-! ## The terms of the statement layer -/

/-- The support is the set of the outputs with a probability that is not 0. -/
theorem mem_support_iff (mx : OracleComp spec α) (a : α) :
    a ∈ support mx ↔ outputProbability mx a ≠ 0 :=
  OracleComp.mem_support_iff_prEvent_ne_zero mx a

/-- The total variation distance is the larger one of the two sums of the one-sided differences of
the output probabilities. The two sums are equal, because each computation has the mass 1. -/
theorem totalVariation_eq (mx my : OracleComp spec α) :
    totalVariation mx my =
      (max (∑' a, (outputProbability mx a - outputProbability my a))
        (∑' a, (outputProbability my a - outputProbability mx a))).toReal := by
  classical
  have : ∀ t, Finite (spec.Range t) := OracleSpec.UniformAnswerMeasure.finite_range
  let : MeasurableSpace α := ⊤
  let F : Finset α :=
    (OracleComp.support_finite mx).toFinset ∪ (OracleComp.support_finite my).toFinset
  have hnull : ∀ oz : OracleComp spec α, support oz ⊆ ↑F → 𝒟[oz] (↑F)ᶜ = 0 := by
    intro oz hsub
    have hs := OracleComp.evalDist_ae_mem_support oz
    rw [MeasureTheory.ae_iff] at hs
    exact MeasureTheory.measure_mono_null (fun x hx hxs => hx (hsub hxs)) hs
  have hμ : 𝒟[mx] (↑F)ᶜ = 0 := hnull mx fun a ha => by simp [F, ha]
  have hν : 𝒟[my] (↑F)ᶜ = 0 := hnull my fun a ha => by simp [F, ha]
  have : MeasureTheory.IsProbabilityMeasure 𝒟[mx] := ⟨OracleComp.evalDist_apply_univ_eq_one mx⟩
  have : MeasureTheory.IsProbabilityMeasure 𝒟[my] := ⟨OracleComp.evalDist_apply_univ_eq_one my⟩
  have hsum : ∀ oa ob : OracleComp spec α, 𝒟[oa] (↑F)ᶜ = 0 →
      ∑' a, (outputProbability oa a - outputProbability ob a) =
        ∑ a ∈ F, (𝒟[oa] {a} - 𝒟[ob] {a}) := by
    intro oa ob hoa
    simp only [outputProbability, prEvent_eq_evalDist_singleton]
    refine tsum_eq_sum fun a ha => ?_
    have hzero : 𝒟[oa] {a} = 0 := MeasureTheory.measure_mono_null (by simpa using ha) hoa
    rw [hzero, zero_tsub]
  rw [hsum mx my hμ, hsum my mx hν, MeasureTheory.Measure.sum_tsub_comm hμ hν, max_self,
    ← MeasureTheory.Measure.etvDist_eq_sum_tsub hμ hν]
  rfl

/-- Two computations have the same distribution if and only if each output has the same
probability in the two and the failure has the same probability in the two. -/
theorem sameDistribution_iff (mx my : OracleComp spec α) :
    SameDistribution mx my ↔
      (∀ a, outputProbability mx a = outputProbability my a) ∧
        failureProbability mx = failureProbability my := by
  have : ∀ t, Finite (spec.Range t) := OracleSpec.UniformAnswerMeasure.finite_range
  refine ⟨fun h => ⟨fun a => h (· = a), ?_⟩,
    fun h => OracleComp.evalDistEq_of_forall_prEvent_eq_output h.1⟩
  rw [failureProbability_eq_zero, failureProbability_eq_zero]

/-- The PRF advantage is the absolute difference of the probabilities that the two experiments
return `true`. -/
theorem prfAdvantageReal_eq {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (adversary : PRFScheme.PRFAdversary D R) :
    prfAdvantageReal prf adversary =
      |(outputProbability (prfRealRun prf adversary) true).toReal -
        (outputProbability (prfIdealRun adversary) true).toReal| := by
  rw [outputProbability, outputProbability, prEvent_eq_evalDist_singleton,
    prEvent_eq_evalDist_singleton]
  exact MeasureTheory.Measure.toReal_boolDist _ _

/-- A uniform sample returns each element of a finite type with the same probability. -/
theorem outputProbability_uniformSample (β : Type) [SampleableType β] [Fintype β] (b : β) :
    outputProbability ($ᵗ β) b = (Fintype.card β : ℝ≥0∞)⁻¹ :=
  SampleableType.prEvent_uniformSample_eq_singleton b

/-! ## The same facts for `ProbComp`

`ProbComp` is `OracleComp unifSpec`, so each theorem above holds for it as stated. -/

/-- The one query of `ProbComp` returns each element of `Fin (n + 1)` with the probability
`1 / (n + 1)`. -/
theorem outputProbability_uniformFin (n : ℕ) (i : Fin (n + 1)) :
    outputProbability ($[0..n]) i = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
  (outputProbability_query (spec := unifSpec) n i).trans
    (congrArg (fun k : ℕ => (k : ℝ≥0∞)⁻¹) (Nat.card_fin (n + 1)))

example [DecidableEq α] (a b : α) :
    outputProbability (pure a : ProbComp α) b = if b = a then 1 else 0 :=
  outputProbability_pure a b

example (mx : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    eventProbability (mx >>= f) p = ∑' a, outputProbability mx a * eventProbability (f a) p :=
  eventProbability_bind mx f p

example (mx : ProbComp α) (p : α → Prop) [DecidablePred p] :
    eventProbability mx p = ∑' a, if p a then outputProbability mx a else 0 :=
  eventProbability_eq_tsum mx p

/-! ## The claims of `Statement.lean` that changed their text -/

section Statements

variable {C : Committee} {E : Type} (prims : Primitives)

/-- `accepts` is the probability that the run returns `true`. -/
theorem accepts_eq (oa : OracleComp (WorldSpec C) Bool) :
    accepts prims oa = (eventProbability (runWorld prims oa) fun r => r.1 = true).toReal :=
  rfl

/-- `HasHashQueryBound` bounds the count of each output that has a probability that is not 0. -/
theorem hasHashQueryBound_iff {α : Type} (run : ProbComp (α × ℕ)) (q : ℕ) :
    HasHashQueryBound run q ↔ ∀ r, outputProbability run r ≠ 0 → r.2 ≤ q :=
  forall_congr' fun r => imp_congr_left (mem_support_iff run r)

/-- The outputs of the operators in the honest real run that `Completes` reads. -/
abbrev honestRealOutputs {I O Ih Oh Lh Rh : Type}
    (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O) (fuel : ℕ)
    (Fh : Functionality C Ih Oh Lh Rh) (replyH : Lh → Rh) (x : C.Party → I) :
    ProbComp (C.Party → Option O) :=
  (fun r => r.1.2) <$> runWorld prims
    (realExecution noCoalition (honestAdversary replyH) Fh fuel program x [])

/-- The outputs of the operators in the honest ideal run that `Completes` reads. -/
abbrev honestIdealOutputs {I O L R : Type} (F : Functionality C I O L R) (reply : L → R)
    (x : C.Party → I) : ProbComp (C.Party → Option O) :=
  (fun r => r.1.2) <$> runWorld prims
    (idealExecution (fun oa => oa) noCoalition F (honestSimulator reply) x [])

/-- `Completes` bounds the total variation distance of the two honest runs, as a number that the
output probabilities give. -/
theorem completes_iff {I O L R Ih Oh Lh Rh : Type}
    (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O) (fuel : ℕ)
    (Fh : Functionality C Ih Oh Lh Rh) (replyH : Lh → Rh) (F : Functionality C I O L R)
    (reply : L → R) (valid : C.Coalition → (C.Party → I) → Prop) (ε : ℝ) :
    Completes prims program fuel Fh replyH F reply valid ε ↔
      ∀ x : C.Party → I, valid noCoalition x →
        (max
          (∑' o, (outputProbability (honestRealOutputs prims program fuel Fh replyH x) o -
            outputProbability (honestIdealOutputs prims F reply x) o))
          (∑' o, (outputProbability (honestIdealOutputs prims F reply x) o -
            outputProbability (honestRealOutputs prims program fuel Fh replyH x) o))).toReal ≤ ε := by
  refine forall₂_congr fun x _ => ?_
  rw [← totalVariation_eq]

/-- The run of the dealer of `F_tree` that `DealerTreeStatement` reads. -/
abbrev dealerTreeRun (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) (cache : HashCache C) :
    ProbComp (Option TreeOutput × HashCache C) :=
  (simulateQ (localAnswer prims)
    (liftComp (Prod.fst <$> dealerCeremony circuits settings parameter seeds top tree)
      (LocalSpec C))).run cache

/-- The run of `referenceTree` that `DealerTreeStatement` reads. -/
abbrev referenceTreeRun (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (tree : Tree) (cache : HashCache C) : ProbComp (Option TreeOutput × HashCache C) :=
  (simulateQ (localAnswer prims)
    (liftComp (referenceTree (fun oa => tweakable oa) (prfValue seeds) parameter top tree)
      (LocalSpec C))).run cache

/-- `DealerTreeStatement` says that each pair of a tree and a next cache has the same probability
in the two runs. -/
theorem dealerTreeStatement_iff (circuits : Circuits) (settings : Settings) :
    DealerTreeStatement prims circuits settings C ↔
      (CircuitsCompute circuits prims.Th → 0 < settings.batchSize →
        ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
          (cache : HashCache C) (a : Option TreeOutput × HashCache C),
          outputProbability (dealerTreeRun prims circuits settings parameter seeds top tree cache) a =
            outputProbability (referenceTreeRun prims parameter seeds top tree cache) a) := by
  refine imp_congr_right fun _ => imp_congr_right fun _ =>
    forall₅_congr fun parameter seeds top tree cache => ?_
  refine (sameDistribution_iff (dealerTreeRun prims circuits settings parameter seeds top tree cache)
    (referenceTreeRun prims parameter seeds top tree cache)).trans ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [failureProbability_eq_zero, failureProbability_eq_zero]

variable [Field E] [Fintype E] [Algebra Bit E]

/-- `TreeSecurityStatement` with its PRF term as the absolute difference of the probabilities that
the two experiments of `prgReduction` return `true`. -/
theorem treeSecurityStatement_iff (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    TreeSecurityStatement prims K circuits settings ↔
      (0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree),
        SimulatedBy prims
          (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
          (ceremonyFuel circuits settings) (Ftree circuits settings top tree) DealtInputs
          (treeSimulator K circuits settings top tree) 0 fun D A x z Z q =>
            treeCheckError (E := E) circuits settings tree q + treeHashError circuits settings C tree q +
              streamKeyError C +
              |(outputProbability (prfRealRun (hiddenStreams prims.aes) (prgReduction prims D
                  (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
                    (fun i keys =>
                      (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
                    x z) Z))) true).toReal -
                (outputProbability (prfIdealRun (prgReduction prims D
                  (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
                    (fun i keys =>
                      (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
                    x z) Z))) true).toReal|) := by
  simp only [← prfAdvantageReal_eq]
  rfl

end Statements

end

/-! The build fails if the axioms of a theorem of this file change. -/

/-- info: 'ThresholdLeanXmss.Characterization.outputProbability_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outputProbability_pure

/-- info: 'ThresholdLeanXmss.Characterization.outputProbability_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outputProbability_query

/-- info: 'ThresholdLeanXmss.Characterization.eventProbability_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventProbability_bind

/-- info: 'ThresholdLeanXmss.Characterization.outputProbability_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outputProbability_bind

/-- info: 'ThresholdLeanXmss.Characterization.outputProbability_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outputProbability_unique

/-- info: 'ThresholdLeanXmss.Characterization.eventProbability_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventProbability_eq_tsum

/-- info: 'ThresholdLeanXmss.Characterization.tsum_outputProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tsum_outputProbability

/-- info: 'ThresholdLeanXmss.Characterization.failureProbability_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms failureProbability_eq_zero

/-- info: 'ThresholdLeanXmss.Characterization.mem_support_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_support_iff

/-- info: 'ThresholdLeanXmss.Characterization.totalVariation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalVariation_eq

/-- info: 'ThresholdLeanXmss.Characterization.sameDistribution_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sameDistribution_iff

/-- info: 'ThresholdLeanXmss.Characterization.prfAdvantageReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prfAdvantageReal_eq

/-- info: 'ThresholdLeanXmss.Characterization.outputProbability_uniformSample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outputProbability_uniformSample

/-- info: 'ThresholdLeanXmss.Characterization.outputProbability_uniformFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outputProbability_uniformFin

/-- info: 'ThresholdLeanXmss.Characterization.accepts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepts_eq

/-- info: 'ThresholdLeanXmss.Characterization.hasHashQueryBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasHashQueryBound_iff

/-- info: 'ThresholdLeanXmss.Characterization.completes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms completes_iff

/-- info: 'ThresholdLeanXmss.Characterization.dealerTreeStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerTreeStatement_iff

/-- info: 'ThresholdLeanXmss.Characterization.treeSecurityStatement_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityStatement_iff

end ThresholdLeanXmss.Characterization
