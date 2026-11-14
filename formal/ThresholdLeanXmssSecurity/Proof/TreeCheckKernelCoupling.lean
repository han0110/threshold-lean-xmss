import ThresholdLeanXmssSecurity.Proof.TreeSim

/-!
# Start state and pair keys of the check kernel

`CheckKernelCoupling` (`TreeCheckWalkCoupling`) relates the real check kernel
of A35's fixed family to the family's GS20 hybrid adapter `W.hybrid c o`.

## Start state

At a live checkpoint every honest operator has a checkpoint row, and that row
starts the check where the hybrid adapter starts it:

* its tuples are the adapter's `tuples i`;
* its run state has the history `filledHistory K i (tuples i)` and the
  adapter's `label` and `tag`. The label is `counters.1 + depth + 1`, the one
  that `TreeCheckTailBoundary.counts` computes.

`RowsAligned` states this. `checkpoint_aligned` derives it for the fixed family
from the accepted record of the live continuation.

## Pair keys

The real check draws the mask of an honest pair `{i, j}` from the hidden
stream of each endpoint's own pair key. `PairsAgree` says that the two keys are
equal. `setup_pair_agree` derives this from the PRSS setup alone, with no
collision premise: each honest operator receives the other's reveal unchanged,
so both ask `H` the same `pairQuery`. A logged run keeps each logged answer of
a non-fixed query in its hash cache (`logged_coherent`), so both get the same
answer.

## Kernel and real executions

`realRun` is a real execution in the stream world without its log and hidden
cache; `hybRun` is the hybrid execution of the adapter. `kernel_erase`,
`kernel_start` and `corrupt_rows` identify the check kernel, so projected, with a
`realRun`. `kernel_of_real` gives the kernel's `RelTriple` with
`KernelRelation` from a `realRun` coupling with `Final` and the log coverage
`TreeSimCheckCacheCovered` of every kernel outcome. Its lift through the
projection is the coupling gluing `relTriple_of_map_left`.

## Round transitions

`Coupled n n' ℓ P Q` says that from every start with equal hash caches,
extending the checkpoint cache, and no hidden draw at the label `ℓ` or later,
the real programs `P` (`n` rounds) and the adapter's hybrid programs `Q`
(`n'` rounds) couple with `Final`.

* `coupled_exchange`: one exchange round with the same outgoing mail, with the
  rushing adversary run identically in both worlds (`adversary_run`).
* `coupled_prefix`: a local pass that starts with the same hash queries and is
  pure until its next suspension (`hash_run`).
* `coupled_end`: the last local pass, where the hybrid decides every operator.
* `realRun_doomed`: once an honest program has stopped, a round that respects
  abort frames stops every honest program.

## Facts the coupling relies on

* The real kernel runs `2 * halvings + 5` rounds. The real check uses one round
  for each coin, extend-mult reshare, digest comparison and final opening.
* The hybrid check makes the same rounds, plus one call round for each of
  `randElements` and `randBits`, so `2 * halvings + 7` rounds
  (`check_honest_bound` in `Check.lean`). `checkRounds` gives `+ 8`, and
  `executeRounds` returns as soon as every honest step is done.
  `hybrid_rounds` says that on the same tuple count the hybrid fuel is the
  real kernel's rounds plus three.
* The adversary's oracle calls use `localAnswer` in both worlds.
  `streamWorld` answers only the honest PRG calls under hidden names from the
  hidden cache.
* The adapter's labels, indices and counts are those of the real gadgets
  (`TreeCheckWalkTransport.realCheckGadgets_shapes`).
* Replacing hidden honest PRSS values by fresh samples also needs every
  hidden-cache entry to lie below the check's first label.

The pinned and current leanVM proof libraries were searched. Their cache
lemmas (`CacheAgreement`, `CacheQuerySupport`) concern the XMSS hash cache
only, and they have no synchronous scheduler or PRSS setup. The private
echo-round lemmas of `TreeSetupKeys`, a module that the library does not hold, are copied with their
proofs.

## Modules

This module holds the transfer of a coupling along a map of the left run, `pairQuery`, the echo-round lemmas, `realRun`, `hybRun`,
`Final` and the lemmas on the phases of a real execution. The signing proof reads some of them.

The library does not hold the other modules of the check kernel. They are a part of the proof that
a tree ceremony is secure. They are `TreeCheckWalkCoupling`, which defines `CheckKernelCoupling`,
and the modules with the other declarations of the namespace `TreeCheckKernelCoupling`.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Glue

set_option linter.unusedSectionVars false

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_of_map_left {f : α → γ} {oa : ProbComp α} {ob : ProbComp β} {R : γ → β → Prop}
    (h : RelTriple (f <$> oa) ob R) : RelTriple oa ob (fun a b => R (f a) b) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  have hprob : MeasureTheory.IsProbabilityMeasure 𝒟[oa] := ⟨evalDist_apply_univ_eq_one oa⟩
  have hsupp : ∀ᵐ a ∂𝒟[oa], a ∈ support oa := ae_mem_support oa
  have hfin : (support oa).Finite := PFunctor.FreeM.support_finite oa
  -- The conditional law of `oa` on the fibre of `f` above `y`.
  let k : γ → MeasureTheory.Measure α := fun y => ProbabilityTheory.cond 𝒟[oa] (f ⁻¹' {y})
  let s : Set γ := {y | y ∈ f '' support oa ∧ 𝒟[oa] (f ⁻¹' {y}) ≠ 0}
  have hinit : ExpectationWP.CouplingPost (𝒟[oa].map f) 𝒟[ob] R := by
    rw [← evalDist_map_of_discrete oa f]
    exact relTriple_iff_relWP.1 h
  have hsc : s.Countable := (hfin.countable.image f).mono fun y hy => hy.1
  have hμs : ∀ᵐ y ∂(𝒟[oa].map f), y ∈ s := by
    have hT : ∀ᵐ y ∂(𝒟[oa].map f), y ∈ f '' support oa :=
      (MeasureTheory.ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).2
        (hsupp.mono fun a ha => ⟨a, ha, rfl⟩)
    have hN : (𝒟[oa].map f) {y | y ∈ f '' support oa ∧ 𝒟[oa] (f ⁻¹' {y}) = 0} = 0 := by
      have hc : {y | y ∈ f '' support oa ∧ 𝒟[oa] (f ⁻¹' {y}) = 0}.Countable :=
        (hfin.countable.image f).mono fun y hy => hy.1
      rw [← Set.biUnion_of_singleton {y | y ∈ f '' support oa ∧ 𝒟[oa] (f ⁻¹' {y}) = 0},
        MeasureTheory.measure_biUnion_null_iff hc]
      intro y hy
      rw [MeasureTheory.Measure.map_apply measurable_from_top MeasurableSet.of_discrete]
      exact hy.2
    filter_upwards [hT, MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hN] with y hy hny
    exact ⟨hy, fun h0 => hny ⟨hy, h0⟩⟩
  have hkp : ∀ y ∈ s, ∀ᵐ x ∂k y, x ∈ support oa := fun y _ =>
    hsupp.filter_mono ProbabilityTheory.cond_absolutelyContinuous.ae_le
  have hlq : ∀ b ∈ support ob, ∀ᵐ y ∂MeasureTheory.Measure.dirac b, y ∈ support ob := fun b hb =>
    (MeasureTheory.ae_dirac_iff MeasurableSet.of_discrete).2 hb
  have hstep : ∀ y ∈ s, ∀ b ∈ support ob, R y b →
      ExpectationWP.CouplingPost (k y) (MeasureTheory.Measure.dirac b) (fun a b' => R (f a) b') := by
    intro y hy b _ hR
    have : MeasureTheory.IsProbabilityMeasure (k y) := ProbabilityTheory.cond_isProbabilityMeasure hy.2
    refine ⟨MeasureTheory.Measure.Coupling.prod (k y) (MeasureTheory.Measure.dirac b), ?_⟩
    have hmem := (MeasureTheory.Measure.Coupling.prod (k y) (MeasureTheory.Measure.dirac b)).isCoupling.ae_mem_prod
      (s := f ⁻¹' {y}) (t := {b}) MeasurableSet.of_discrete MeasurableSet.of_discrete
      (ProbabilityTheory.ae_cond_mem MeasurableSet.of_discrete)
      ((MeasureTheory.ae_dirac_iff MeasurableSet.of_discrete).2 rfl)
    filter_upwards [hmem] with z hz
    have h1 : f z.1 = y := hz.1
    have h2 : z.2 = b := hz.2
    show R (f z.1) z.2
    rw [h1, h2]
    exact hR
  -- The law of `oa` is the mixture of its conditional laws on the fibres of `f`.
  have hdis : (𝒟[oa].map f).bind k = 𝒟[oa] := by
    have hpoint : ∀ m : MeasureTheory.Measure α, (∀ᵐ a ∂m, a ∈ support oa) → ∀ A : Set α,
        m A = ∑ a ∈ hfin.toFinset, A.indicator 1 a * m {a} := by
      intro m hm A
      have hr : m.restrict (↑hfin.toFinset : Set α) = m :=
        MeasureTheory.Measure.restrict_eq_self_of_ae_mem (by simpa using hm)
      calc m A = MeasureTheory.lintegral m (fun a => A.indicator 1 a) :=
            (MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete).symm
        _ = MeasureTheory.lintegral (m.restrict (↑hfin.toFinset : Set α)) (fun a => A.indicator 1 a) := by
            rw [hr]
        _ = _ := MeasureTheory.lintegral_finset _ _
    have hconc : ∀ᵐ a ∂((𝒟[oa].map f).bind k), a ∈ support oa :=
      MeasureTheory.Measure.ae_bind_of_ae measurable_from_top MeasurableSet.of_discrete
        (Filter.Eventually.of_forall fun y =>
          hsupp.filter_mono ProbabilityTheory.cond_absolutelyContinuous.ae_le)
    have hsing : ∀ a₀, ((𝒟[oa].map f).bind k) {a₀} = 𝒟[oa] {a₀} := by
      intro a₀
      have hk : ∀ a, k (f a) {a₀} = (f ⁻¹' {f a₀}).indicator
          (fun _ => (𝒟[oa] (f ⁻¹' {f a₀}))⁻¹ * 𝒟[oa] {a₀}) a := by
        intro a
        show ProbabilityTheory.cond 𝒟[oa] (f ⁻¹' {f a}) {a₀} = _
        rw [ProbabilityTheory.cond_apply MeasurableSet.of_discrete]
        by_cases hfa : f a = f a₀
        · rw [Set.indicator_of_mem (show a ∈ f ⁻¹' {f a₀} from hfa), hfa,
            Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (show a₀ ∈ f ⁻¹' {f a₀} from rfl))]
        · have he : f ⁻¹' {f a} ∩ {a₀} = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
            hfa ((show f x = f a from hx.1).symm.trans (congrArg f (show x = a₀ from hx.2)))
          rw [Set.indicator_of_notMem (show a ∉ f ⁻¹' {f a₀} from hfa), he,
            MeasureTheory.measure_empty, mul_zero]
      rw [MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete measurable_from_top.aemeasurable,
        MeasureTheory.lintegral_map measurable_from_top measurable_from_top]
      simp only [hk]
      rw [MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete]
      by_cases h0 : 𝒟[oa] (f ⁻¹' {f a₀}) = 0
      · have hz : 𝒟[oa] {a₀} = 0 :=
          MeasureTheory.measure_mono_null (Set.singleton_subset_iff.2 (show a₀ ∈ f ⁻¹' {f a₀} from rfl)) h0
        rw [hz, h0, mul_zero]
      · rw [mul_comm _ (𝒟[oa] {a₀}), mul_assoc,
          ENNReal.inv_mul_cancel h0 (MeasureTheory.measure_ne_top _ _), mul_one]
    ext A -
    rw [hpoint _ hconc A, hpoint _ hsupp A]
    simp only [hsing]
  have hbind := hinit.bind_of_countable_of_ae_mem (s := s) (t := support ob) (p := support oa)
    (q := support ob) hsc (PFunctor.FreeM.support_finite ob).countable hfin.countable
    (PFunctor.FreeM.support_finite ob).countable hμs (ae_mem_support ob) (k := k)
    (l := MeasureTheory.Measure.dirac) measurable_from_top measurable_from_top hkp hlq hstep
  rw [hdis, MeasureTheory.Measure.bind_dirac] at hbind
  exact relTriple_iff_relWP.2 hbind

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    {P : α → Prop} (h : RelTriple oa ob R) (hp : ∀ a ∈ support oa, P a) :
    RelTriple oa ob (fun a b => R a b ∧ P a) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, ?_⟩
  filter_upwards [hc, ae_mem_support_prod c] with z hz hmem
  exact ⟨hz, hp z.1 hmem.1⟩

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_of_support {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    (h : ∀ a ∈ support oa, ∀ b ∈ support ob, R a b) : RelTriple oa ob R := by
  have left := relTriple_support_left (relTriple_true oa ob) (P := fun a => a ∈ support oa)
    (fun a ha => ha)
  have right := relTriple_symm (relTriple_support_left (relTriple_symm left)
    (P := fun b => b ∈ support ob) (fun b hb => hb))
  exact relTriple_post_mono right fun a b hab => h a hab.1.2 b hab.2

end Glue

section SetupPairs

variable (prims : Primitives) (D : C.Coalition)

/-- The input of `H` that derives the pair key of `p` from the parts of its two
operators. -/
def pairQuery (parts : C.Party → Parts C) (p : C.Pair) : Query C :=
  .derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The derivation input depends only on the two pair parts that it reads. -/
theorem pairQuery_congr (view parts : C.Party → Parts C) (i j : C.Party) (ne : i ≠ j)
    (left : (view i).pair j = (parts i).pair j) (right : (view j).pair i = (parts j).pair i) :
    pairQuery view (C.pairOf i j ne) = pairQuery parts (C.pairOf i j ne) := by
  unfold pairQuery Committee.pairOf
  split_ifs <;> simp only [left, right]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The reveal that an honest active operator sends carries its own pair part. -/
theorem readReveal_pair (parts : Parts C) (i j k : C.Party) :
    (readReveal .prss (Msg.hashesOf (some (Msg.hashes (E := E) (revealTo .prss parts j i)))) i j).pair k =
      parts.pair i := by
  simp [readReveal, revealTo, Msg.hashesOf, List.getD_eq_getElem?_getD]

-- The private echo-round lemmas of `TreeSetupKeys`, kept with their original proofs.
omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private def setupFinishResult
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) : Option (PrssKeys C) :=
  if i ∈ D.1 then none else
    match rows i with
    | none => none
    | some row =>
      let inbox := fun j => if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [row.2.getD j.val 0]
        then some row.1 else none

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem setupFinish_local
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (fun j => prssFinishStep j (rows j)) sent i =
      pure (.done (setupFinishResult D rows sent i)) := by
  by_cases hi : i ∈ D.1
  · cases hrow : rows i <;> simp [roundLocal, prssFinishStep, hrow, hi, setupFinishResult]
  · cases hrow : rows i with
    | none => simp [roundLocal, prssFinishStep, hrow, hi, setupFinishResult]
    | some row =>
      simp only [roundLocal, hrow, prssFinishStep, if_neg hi]
      let inbox : Mail C E := fun j => if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i
      change advance (exchangeResume (fun received => do
        require (∀ j, j ≠ i → Msg.hashesOf (received j) = [row.2.getD j.val 0])
        pure row.1) inbox) = pure (.done (setupFinishResult D rows sent i))
      simp only [setupFinishResult, if_neg hi, hrow]
      change _ = (pure (Step.done (C := C) (E := E) (G := RealSpec)
        (if C.parties.any (fun j => Msg.isAbort (inbox j)) then none
        else if ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [row.2.getD j.val 0]
          then some row.1 else none)) : OracleComp (LocalSpec C) _)
      rw [exchangeResume]
      by_cases ha : C.parties.any (fun j => Msg.isAbort (inbox j)) = true
      · simp only [if_pos ha]
        rfl
      · simp only [if_neg ha]
        rw [advance_require_bind]
        split_ifs <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The final setup round only exchanges and checks the recorded echo hashes. -/
private theorem setupFinish_round (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (rows : C.Party → Option (PrssKeys C × List HashOutput)) :
    stepRound worldRoles D A noFunctionality state (fun i => prssFinishStep i (rows i)) = (do
      let adv ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (prssFinishStep i (rows i)).outbox c else none)
      pure (adv.1, fun i => Step.done (C := C) (E := E) (G := RealSpec)
        (setupFinishResult D rows adv.2 i), adv.2)) := by
  rw [stepRound_real]
  apply bind_congr
  rintro ⟨state', sent⟩
  dsimp only
  rw [show roundLocal D (fun i => prssFinishStep i (rows i)) sent =
    (fun i => pure (.done (setupFinishResult D rows sent i))) from
      funext (setupFinish_local D rows sent)]
  simp only [sequenceFin_pure, free_pure, pure_bind]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem setupFinish_some
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (sent : C.Party → Mail C E) (i : C.Party) (ki : PrssKeys C)
    (hi : setupFinishResult D rows sent i = some ki) :
    i ∉ D.1 ∧ ∃ shared, rows i = some (ki, shared) ∧
      ∀ j, j ≠ i → Msg.hashesOf (if j ∈ D.1 then sent j i else
        (prssFinishStep (E := E) j (rows j)).delivered i) = [shared.getD j.val 0] := by
  unfold setupFinishResult at hi
  split_ifs at hi with hcorrupt
  cases hrow : rows i with
  | none => simp [hrow] at hi
  | some row =>
    simp only [hrow] at hi
    split_ifs at hi with ha hc
    cases hi
    exact ⟨hcorrupt, row.2, rfl, hc⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A key that the echo round returns is the key of its own reveal row. -/
theorem finish_row (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (rows : C.Party → Option (PrssKeys C × List HashOutput)) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality 1 state
        (fun i => prssFinishStep i (rows i)))).run s))
    (i : C.Party) (ki : PrssKeys C) (hi : r.1.2 i = some ki) :
    (∃ shared, rows i = some (ki, shared)) ∧ s.2 <+: r.2.2 := by
  have before := treeSimLoggedWorld_prefix prims D _ s r hr
  refine ⟨?_, before⟩
  rw [executeRounds] at hr
  split_ifs at hr with hd
  · simp only [prssFinishStep_output, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hr
    subst r
    cases hi
  · rw [setupFinish_round] at hr
    simp only [bind_assoc, pure_bind, executeRounds, Step.output, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hr
    obtain ⟨adv, _, rfl⟩ := hr
    obtain ⟨_, shared, row, _⟩ := setupFinish_some D rows adv.1.2 i ki hi
    exact ⟨shared, row⟩

end SetupPairs

section Kernel

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
  (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- A real execution in the stream world: the first local pass and `n` rounds.
It keeps the adversary state, every pending step and the hash cache; the
hidden cache and the log are dropped. -/
def realRun {β : Type} (n : ℕ) (stA : A.State) (P : C.Party → PartyM C E RealSpec β)
    (w : HashCache C × HiddenCache C) :
    ProbComp ((A.State × (C.Party → Step C E RealSpec β)) × HashCache C) :=
  (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D)
    (startSteps worldRoles D P >>= fun steps =>
      executeSteps worldRoles D A noFunctionality n stA steps)).run w

/-- A hybrid execution of the check in the local world. -/
def hybRun (Ad : CheckAdversary C E (List (Tuple C))) (n : ℕ) (st : Ad.State)
    (Q : C.Party → PartyM C E (CheckSpec C E) Unit) (h : HashCache C) :
    ProbComp ((Ad.State × (C.Party → Option Unit)) × HashCache C) :=
  letI : SampleableType E := SampleableType.ofFintype E
  (simulateQ (localAnswer prims) (executePhase localRoles D Ad (checkFunctionalities K) n st Q)).run h

/-- Every honest operator still running in the real execution accepts in the
hybrid one, whose hash cache is part of the real one. -/
def Final {β σ : Type} (x : (A.State × (C.Party → Step C E RealSpec β)) × HashCache C)
    (y : (σ × (C.Party → Option Unit)) × HashCache C) : Prop :=
  ∀ i, i ∉ D.1 → x.1.2 i ≠ .done none → y.2 ≤ x.2 ∧ y.1.2 i = some ()

end Kernel

section Phases

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An adversary computation runs identically in the stream world and in the
local world, and leaves the hidden cache unchanged. -/
theorem adversary_run {α : Type} (p : OracleComp (LocalSpec C) α) (h : HashCache C)
    (c : HiddenCache C) :
    (simulateQ (streamWorld prims D) (worldRoles.adversary p)).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) p).run h := by
  induction p using OracleComp.inductionOn generalizing h with
  | pure a => simp [worldRoles, counted_pure]
  | query_bind t k ih =>
    simp only [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun u => worldRoles.adversary (k u) from rfl,
      adversary_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (simulateQ (streamWorld prims D)
        (liftM (OracleSpec.query (spec := WorldSpec C) (Sum.inl (Sum.inl t))))).run (h, c) =
        (fun r => (r.1, (r.2, c))) <$> (localAnswer prims t).run h := by
      erw [simulateQ_spec_query]
      rfl
    erw [simulateQ_spec_query] at hq
    erw [hq]
    rw [bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 r.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The real exchange steps, as in `startSteps_optionalExchange`. -/
theorem startSteps_world_optionalExchange {β : Type} (outbox : C.Party → Option (Mail C E))
    (f : C.Party → Mail C E → PartyM C E RealSpec β) :
    startSteps worldRoles D (fun i => optionalExchange (outbox i) (f i)) =
      pure (optionalExchangeSteps D outbox f) := by
  unfold startSteps
  calc
    _ = OverPermutation.sequenceFin (fun i => pure (optionalExchangeSteps D outbox f i)) := by
      congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [hi, optionalExchangeSteps]
      · cases hv : outbox i <;>
          simp only [hi, if_false, hv, optionalExchange, optionalExchangeSteps, worldRoles,
            advance_run_failure, advance_exchange_bind, free_pure]
    _ = _ := sequenceFin_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The real local pass after an exchange starts the `afterExchange` programs. -/
theorem roundLocal_optionalExchange {β : Type} (outbox : C.Party → Option (Mail C E))
    (f : C.Party → Mail C E → PartyM C E RealSpec β) (sent : C.Party → Mail C E) :
    free (OverPermutation.sequenceFin (roundLocal D (optionalExchangeSteps D outbox f) sent)) =
      startSteps worldRoles D (fun i => afterExchange D outbox sent i (f i)) := by
  have hin (j : C.Party) :
      (fun k => if k ∈ D.1 then sent k j else (optionalExchangeSteps D outbox f k).delivered j) =
      (fun k => if k ∈ D.1 then sent k j else ((outbox k).getD (fun _ => some .abort)) j) := by
    funext k
    by_cases hk : k ∈ D.1 <;> cases he : outbox k <;>
      simp [hk, he, optionalExchangeSteps, Step.delivered]
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [optionalExchangeSteps, hi, roundLocal, free_pure]
  · cases he : outbox i with
    | none =>
      simp only [optionalExchangeSteps, roundLocal, hi, if_false, he, afterExchange, worldRoles,
        advance_run_failure]
    | some v =>
      have hs : optionalExchangeSteps D outbox f i = .wait v (exchangeResume (f i)) := by
        simp [optionalExchangeSteps, hi, he]
      simp only [roundLocal, hs, if_neg hi, worldRoles]
      congr 1
      rw [hin]
      simp only [afterExchange, he, exchangeResume]
      split_ifs <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A hash-only honest computation runs in the stream world as in the local
world, and leaves the hidden cache unchanged. -/
theorem hash_run {X : Type} (q : OracleComp (Query C →ₒ HashOutput) X) (h : HashCache C)
    (c : HiddenCache C) :
    (simulateQ (streamWorld prims D) (free (liftComp (liftComp q (RoSpec C)) (LocalSpec C)))).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$>
        (simulateQ (localAnswer prims) (liftComp (liftComp q (RoSpec C)) (LocalSpec C))).run h := by
  induction q using OracleComp.inductionOn generalizing h with
  | pure a => simp
  | query_bind t k ih =>
    have split : liftComp (liftComp (OracleComp.lift (OracleSpec.query t) >>= k) (RoSpec C)) (LocalSpec C) =
        liftComp (hashQuery (C := C) t) (LocalSpec C) >>= fun u =>
          liftComp (liftComp (k u) (RoSpec C)) (LocalSpec C) := by
      simp only [liftComp_bind]
      rfl
    have hq : (simulateQ (streamWorld prims D) (free (liftComp (hashQuery (C := C) t) (LocalSpec C)))).run (h, c) =
        (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) (liftComp (hashQuery (C := C) t)
          (LocalSpec C))).run h := by
      have he := simulateQ_spec_query (streamWorld prims D) (.inr (.inr (.inl t)))
      change simulateQ (streamWorld prims D) (free (liftComp (hashQuery (C := C) t) (LocalSpec C))) =
        streamWorld prims D (.inr (.inr (.inl t))) at he
      have he2 := simulateQ_spec_query (localAnswer prims) (.inr (.inl t))
      change simulateQ (localAnswer prims) (liftComp (hashQuery (C := C) t) (LocalSpec C)) =
        localAnswer prims (.inr (.inl t)) at he2
      rw [he, he2]
      rfl
    rw [split, free_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, hq,
      bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 r.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
set_option linter.unusedVariables false in
/-- Computations that run in both worlds alike, sequenced. -/
theorem sequence_run {α : Type} : ∀ {n : ℕ} (F : Fin n → OracleComp (WorldSpec C) α)
    (G : Fin n → OracleComp (LocalSpec C) α) (c : HiddenCache C)
    (same : ∀ i h, (simulateQ (streamWorld prims D) (F i)).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) (G i)).run h) (h : HashCache C),
    (simulateQ (streamWorld prims D) (OverPermutation.sequenceFin F)).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) (OverPermutation.sequenceFin G)).run h
  | 0, F, G, c, same, h => by simp [OverPermutation.sequenceFin]
  | n + 1, F, G, c, same, h => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, map_bind, same 0 h, bind_map_left]
    refine bind_congr fun r => ?_
    rw [sequence_run (fun i => F i.succ) (fun i => G i.succ) c (fun i => same i.succ) r.2]
    simp only [bind_map_left, map_pure]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {α γ : Type} :
    ∀ {n : ℕ} (f : Fin n → m α) (g : Fin n → α → γ),
      OverPermutation.sequenceFin (fun i => g i <$> f i) = (fun xs i => g i (xs i)) <$> OverPermutation.sequenceFin f
  | 0, f, g => by
    simp only [OverPermutation.sequenceFin, map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f, g => by
    simp only [OverPermutation.sequenceFin, map_bind, bind_map_left]
    refine bind_congr fun a => ?_
    rw [sequenceFin_map (fun i => f i.succ) (fun i => g i.succ), bind_map_left]
    refine bind_congr fun xs => ?_
    simp only [map_pure]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The honest hash prefixes of one local pass, in party order. -/
def hashPrefix {X : Type} (W : C.Party → OracleComp (Query C →ₒ HashOutput) X) :
    OracleComp (LocalSpec C) (C.Party → Option X) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure none else
    some <$> liftComp (liftComp (W i) (RoSpec C)) (LocalSpec C)

/-- The steps after the hash prefixes, when the rest of the local pass is pure. -/
def prefixSteps {ι : Type} {G : OracleSpec ι} {X β : Type} (s : C.Party → X → Step C E G β)
    (xs : C.Party → Option X) : C.Party → Step C E G β :=
  fun i => match xs i with
    | none => .done none
    | some x => s i x

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem startSteps_world_prefix {X β : Type} (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (gR : C.Party → X → PartyM C E RealSpec β) (sR : C.Party → X → Step C E RealSpec β)
    (pureR : ∀ i x, advance (gR i x).run = pure (sR i x)) :
    startSteps worldRoles D (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gR i) =
      prefixSteps sR <$> free (hashPrefix D W) := by
  unfold startSteps hashPrefix
  rw [free_sequenceFin]
  refine Eq.trans ?_ (sequenceFin_map (m := OracleComp (WorldSpec C)) _
    (fun (i : C.Party) (o : Option X) => match o with | none => Step.done none | some x => sR i x))
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, free_pure]
  · simp only [if_neg hi, worldRoles, advance_oracleStep_bind, pureR]
    simp [map_eq_bind_pure_comp, free_bind, free_pure]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem startSteps_local_prefix {X β I O : Type}
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (gH : C.Party → X → PartyM C E (CallSpec I O) β) (sH : C.Party → X → Step C E (CallSpec I O) β)
    (pureH : ∀ i x, advance (gH i x).run = pure (sH i x)) :
    startSteps localRoles D (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gH i) =
      prefixSteps sH <$> hashPrefix D W := by
  unfold startSteps hashPrefix
  refine Eq.trans ?_ (sequenceFin_map (m := OracleComp (LocalSpec C)) _
    (fun (i : C.Party) (o : Option X) => match o with | none => Step.done none | some x => sH i x))
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [if_neg hi, localRoles, advance_oracleStep_bind, pureH]
    simp [map_eq_bind_pure_comp]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hashPrefix_run {X : Type} (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (h : HashCache C) (c : HiddenCache C) :
    (simulateQ (streamWorld prims D) (free (hashPrefix D W))).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) (hashPrefix D W)).run h := by
  unfold hashPrefix
  rw [free_sequenceFin]
  apply sequence_run prims D _ _ c
  intro i h
  by_cases hi : i ∈ D.1
  · simp [hi, free_pure]
  · simp only [if_neg hi]
    rw [map_eq_bind_pure_comp, free_bind, simulateQ_bind, simulateQ_bind, StateT.run_bind,
      StateT.run_bind, hash_run prims D (W i) h c, bind_map_left, map_bind]
    simp

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One real exchange round: the rushing adversary, then the resumed programs. -/
theorem realRun_exchange {β : Type} (n : ℕ) (stA : A.State) (outbox : C.Party → Option (Mail C E))
    (f : C.Party → Mail C E → PartyM C E RealSpec β) (w : HashCache C × HiddenCache C)
    (ha : ∃ i, i ∉ D.1 ∧ (outbox i).isSome) :
    realRun prims D A (n + 1) stA (fun i => optionalExchange (outbox i) (f i)) w = (do
      let b ← (simulateQ (streamWorld prims D) (worldRoles.adversary (A.round stA fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then ((outbox i).getD (fun _ => none)) c else none))).run w
      realRun prims D A n b.1.1 (fun i => afterExchange D outbox b.1.2 i (f i)) b.2) := by
  have hn : ¬ ∀ i, i ∉ D.1 → (optionalExchangeSteps D outbox f i).isDone := by
    obtain ⟨i, hi, hv⟩ := ha
    intro h
    cases he : outbox i with
    | none => simp [he] at hv
    | some v => simpa [optionalExchangeSteps, hi, he, Step.isDone] using h i hi
  have hout : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (optionalExchangeSteps D outbox f i).outbox c
      else none) = (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then ((outbox i).getD (fun _ => none)) c
      else none) := by
    funext c i
    by_cases hi : i ∈ D.1 <;> cases he : outbox i <;>
      simp [hi, he, optionalExchangeSteps, Step.outbox]
  unfold realRun
  rw [startSteps_world_optionalExchange, pure_bind, executeSteps, if_neg hn, stepRound_real, hout]
  simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_assoc, pure_bind,
    roundLocal_optionalExchange]

end Phases

end ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_map_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_map_left

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_support

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.adversary_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.adversary_run

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.hash_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.hash_run

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.realRun_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.realRun_exchange

