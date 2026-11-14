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
echo-round lemmas of `TreeSetupKeys` are copied with their proofs.

## Modules

This module holds the gluing of two couplings, `pairQuery`, the echo-round lemmas, `realRun`, `hybRun`,
`Final` and the lemmas on the phases of a real execution. Other modules hold the other declarations
of the namespace `TreeCheckKernelCoupling`.

* `TreeCheckKernelCoupled` holds `adapter`, `Coupled` and `hashPrefix_support`.
* `TreeCheckKernelChecked` holds `RowsAligned`, `checkpoint_aligned`, `PairsAgree`, `pairsAgree`,
  `setup_pair_agree`, `logged_coherent`, `coupled_exchange`, `coupled_prefix` and `coupled_end`.
* `TreeCheckKernelCovered` holds `kernel_erase`, `kernel_start`, `corrupt_rows` and `kernel_of_real`.
* `TreeCheckGadgetPass` holds `realRun_doomed`.
* `TreeCheckKernelClosure` holds `hybrid_rounds`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Glue

set_option linter.unusedSectionVars false

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem spmf_map_apply (g : α → γ) (s : SPMF α) (x : γ) :
    (g <$> s) x = ∑' z, if g z = x then s z else 0 := by
  rw [map_eq_bind_pure_comp, SPMF.bind_apply_eq_tsum]
  congr 1
  funext z
  simp only [Function.comp_apply, SPMF.pure_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

/-- The cells of a coupling above `y`. -/
def cells (y : γ) : Set (Option (γ × β)) := {o | ∃ z, o = some z ∧ z.1 = y}

theorem cells_mass (c : SPMF (γ × β)) (y : γ) :
    ∑' o, (cells (β := β) y).indicator c.toPMF o = (Prod.fst <$> c) y := by
  rw [spmf_map_apply, tsum_option _ ENNReal.summable]
  have hnone : (cells (β := β) y).indicator c.toPMF none = 0 := by
    apply Set.indicator_of_notMem
    rintro ⟨z, h, _⟩
    cases h
  rw [hnone, zero_add]
  congr 1
  funext z
  by_cases hz : z.1 = y
  · rw [Set.indicator_of_mem (show some z ∈ cells (β := β) y from ⟨z, rfl, hz⟩), if_pos hz]
    rfl
  · rw [Set.indicator_of_notMem (by rintro ⟨w, hw, hy⟩; cases hw; exact hz hy), if_neg hz]



/-- The normalized fibre of a coupling above `y`; `q` is an unused default. -/
def fibre (c : SPMF (γ × β)) (q : SPMF β) (y : γ) : SPMF β :=
  if h : ∃ o ∈ cells (β := β) y, o ∈ c.toPMF.support then
    Prod.snd <$> SPMF.mk (c.toPMF.filter (cells y) h)
  else q

theorem fst_mass (c : SPMF (γ × β)) (y : γ) :
    (Prod.fst <$> c) y = ∑' b, c (y, b) := by
  rw [spmf_map_apply]
  refine (ENNReal.tsum_prod (f := fun (y' : γ) (b : β) => if y' = y then c (y', b) else 0)).trans ?_
  rw [tsum_eq_single y]
  · simp
  · intro y' hy
    simp [hy]

theorem fibre_apply (c : SPMF (γ × β)) (q : SPMF β) (y : γ) (b : β)
    (hw : (Prod.fst <$> c) y ≠ 0) :
    fibre c q y b = c (y, b) * ((Prod.fst <$> c) y)⁻¹ := by
  have h : ∃ o ∈ cells (β := β) y, o ∈ c.toPMF.support := by
    rw [fst_mass] at hw
    obtain ⟨b', hb'⟩ := not_forall.mp (fun h => hw (ENNReal.tsum_eq_zero.mpr h))
    exact ⟨some (y, b'), ⟨(y, b'), rfl, rfl⟩, (PMF.mem_support_iff _ _).mpr hb'⟩
  rw [fibre, dif_pos h, spmf_map_apply]
  simp only [show ∀ z, (SPMF.mk (c.toPMF.filter (cells y) h)) z =
    c.toPMF.filter (cells y) h (some z) from fun _ => rfl, PMF.filter_apply, cells_mass]
  rw [show c (y, b) = c.toPMF (some (y, b)) from rfl]
  rw [show (fun z : γ × β => if z.2 = b then (cells (β := β) y).indicator c.toPMF (some z) *
      ((Prod.fst <$> c) y)⁻¹ else 0) =
      fun z => if z = (y, b) then c.toPMF (some (y, b)) * ((Prod.fst <$> c) y)⁻¹ else 0 from ?_]
  · rw [tsum_ite_eq]
  · funext z
    by_cases hz : z = (y, b)
    · subst hz
      rw [if_pos rfl, if_pos rfl, Set.indicator_of_mem (show some (y, b) ∈ cells (β := β) y from ⟨_, rfl, rfl⟩)]
    · rw [if_neg hz]
      by_cases hb : z.2 = b
      · rw [if_pos hb, Set.indicator_of_notMem, zero_mul]
        rintro ⟨w, hw, hy⟩
        cases hw
        exact hz (Prod.ext hy hb)
      · rw [if_neg hb]

/-- The coupling glued along `f`. -/
def glue (p : SPMF α) (q : SPMF β) (f : α → γ) (c : SPMF (γ × β)) : SPMF (α × β) :=
  p >>= fun a => (fun b => (a, b)) <$> fibre c q (f a)

theorem glue_apply (p : SPMF α) (q : SPMF β) (f : α → γ) (c : SPMF (γ × β)) (a : α) (b : β) :
    glue p q f c (a, b) = p a * fibre c q (f a) b := by
  rw [glue, SPMF.bind_apply_eq_tsum, tsum_eq_single a]
  · rw [spmf_map_apply, tsum_eq_single b]
    · simp
    · intro b' hb
      simp [hb]
  · intro a' ha
    rw [spmf_map_apply]
    simp only [Prod.mk.injEq, ENNReal.tsum_eq_zero, mul_eq_zero]
    right
    intro b'
    simp [ha]

theorem fibre_mass (c : SPMF (γ × β)) (q : SPMF β) (y : γ)
    (hw : (Prod.fst <$> c) y ≠ 0) : ∑' b, fibre c q y b = 1 := by
  simp only [fibre_apply c q y _ hw]
  rw [ENNReal.tsum_mul_right, ← fst_mass]
  exact ENNReal.mul_inv_cancel hw (SPMF.apply_ne_top _ _)

theorem mass_le (c : SPMF (γ × β)) (y : γ) (b : β) : c (y, b) ≤ (Prod.fst <$> c) y := by
  rw [fst_mass]
  exact ENNReal.le_tsum b

theorem glue_coupling (p : SPMF α) (q : SPMF β) (f : α → γ) (c : SPMF (γ × β))
    (hc : SPMF.IsCoupling c (f <$> p) q) : SPMF.IsCoupling (glue p q f c) p q := by
  have wmass : ∀ a, p a ≠ 0 → (Prod.fst <$> c) (f a) ≠ 0 := by
    intro a ha
    rw [hc.map_fst, spmf_map_apply]
    exact fun h => ha (le_antisymm ((ENNReal.le_tsum a).trans_eq' (by simp) |>.trans h.le) bot_le)
  constructor
  · ext a
    rw [spmf_map_apply]
    rw [show (fun z : α × β => if z.1 = a then glue p q f c z else 0) =
      fun z => (fun (a' : α) (b : β) => if a' = a then glue p q f c (a', b) else 0) z.1 z.2 from rfl]
    refine (ENNReal.tsum_prod (f := fun (a' : α) (b : β) =>
      if a' = a then glue p q f c (a', b) else 0)).trans ?_
    rw [tsum_eq_single a (fun a' ha => by simp [ha])]
    simp only [if_true, glue_apply]
    rw [ENNReal.tsum_mul_left]
    by_cases ha : p a = 0
    · rw [ha, zero_mul]
    · rw [fibre_mass c q (f a) (wmass a ha), mul_one]
  · ext b
    rw [show q b = (Prod.snd <$> c) b by rw [hc.map_snd], spmf_map_apply, spmf_map_apply]
    rw [show (fun z : α × β => if z.2 = b then glue p q f c z else 0) =
      fun z => (fun (a : α) (b' : β) => if b' = b then glue p q f c (a, b') else 0) z.1 z.2 from rfl]
    refine (ENNReal.tsum_prod (f := fun (a : α) (b' : β) =>
      if b' = b then glue p q f c (a, b') else 0)).trans ?_
    simp only [tsum_ite_eq, glue_apply]
    rw [show (fun z : γ × β => if z.2 = b then c z else 0) =
      fun z => (fun (y : γ) (b' : β) => if b' = b then c (y, b') else 0) z.1 z.2 from rfl]
    refine Eq.trans ?_ (ENNReal.tsum_prod (f := fun (y : γ) (b' : β) =>
      if b' = b then c (y, b') else 0)).symm
    simp only [tsum_ite_eq]
    -- regroup the left sum by `f`
    have regroup : ∑' a, p a * fibre c q (f a) b =
        ∑' y, ∑' a, (if f a = y then p a * fibre c q (f a) b else 0) := by
      rw [ENNReal.tsum_comm]
      congr 1
      funext a
      rw [tsum_eq_single (f a) (fun y hy => by simp [Ne.symm hy])]
      simp
    rw [regroup]
    congr 1
    funext y
    have inner : ∑' a, (if f a = y then p a * fibre c q (f a) b else 0) =
        (∑' a, if f a = y then p a else 0) * fibre c q y b := by
      rw [← ENNReal.tsum_mul_right]
      congr 1
      funext a
      by_cases h : f a = y
      · simp [h]
      · simp [h]
    rw [inner, ← spmf_map_apply, ← hc.map_fst]
    by_cases hw : (Prod.fst <$> c) y = 0
    · rw [hw, zero_mul]
      exact (le_antisymm ((mass_le c y b).trans_eq hw) bot_le).symm
    · rw [fibre_apply c q y b hw, mul_comm, mul_assoc, ENNReal.inv_mul_cancel hw (SPMF.apply_ne_top _ _),
        mul_one]

theorem glue_support (p : SPMF α) (q : SPMF β) (f : α → γ) (c : SPMF (γ × β))
    (hc : SPMF.IsCoupling c (f <$> p) q) (z : α × β) (hz : glue p q f c z ≠ 0) :
    c (f z.1, z.2) ≠ 0 := by
  obtain ⟨a, b⟩ := z
  rw [glue_apply] at hz
  have ha : p a ≠ 0 := fun h => hz (by rw [h, zero_mul])
  have hw : (Prod.fst <$> c) (f a) ≠ 0 := by
    rw [hc.map_fst, spmf_map_apply]
    exact fun h => ha (le_antisymm ((ENNReal.le_tsum a).trans_eq' (by simp) |>.trans h.le) bot_le)
  rw [fibre_apply c q (f a) b hw] at hz
  exact fun h => hz (by rw [h, zero_mul, mul_zero])

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_of_map_left {f : α → γ} {oa : ProbComp α} {ob : ProbComp β} {R : γ → β → Prop}
    (h : RelTriple (f <$> oa) ob R) : RelTriple oa ob (fun a b => R (f a) b) := by
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq β := Classical.decEq β
  letI : DecidableEq γ := Classical.decEq γ
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  have hcpl : SPMF.IsCoupling c.1 (f <$> 𝒟[oa]) 𝒟[ob] :=
    ⟨by rw [c.2.map_fst, evalDist_map], c.2.map_snd⟩
  refine relTriple_iff_relWP.2 ⟨⟨glue 𝒟[oa] 𝒟[ob] f c.1, glue_coupling _ _ f c.1 hcpl⟩, ?_⟩
  intro z hz
  apply hc (f z.1, z.2)
  have hz' : glue 𝒟[oa] 𝒟[ob] f c.1 z ≠ 0 := (SPMF.mem_support_iff _ _).mp hz
  exact (SPMF.mem_support_iff _ _).mpr (glue_support _ _ f c.1 hcpl z hz')

omit [DecidableEq α] [DecidableEq β] [DecidableEq γ] in
theorem relTriple_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    {P : α → Prop} (h : RelTriple oa ob R) (hp : ∀ a ∈ support oa, P a) :
    RelTriple oa ob (fun a b => R a b ∧ P a) := by
  classical
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ⟨hc z hz, hp z.1 ?_⟩⟩
  have hz' : c.1 z ≠ 0 := (SPMF.mem_support_iff _ _).mp hz
  rw [mem_support_iff_evalDist_apply_ne_zero, ← c.2.map_fst]
  intro h0
  apply hz'
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq β := Classical.decEq β
  have := (spmf_map_apply (α := α × β) (γ := α) Prod.fst c.1 z.1)
  rw [h0] at this
  exact (ENNReal.tsum_eq_zero.mp this.symm z).symm ▸ (by simp)

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
    _ = Concrete.sequenceFin (fun i => pure (optionalExchangeSteps D outbox f i)) := by
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
    free (Concrete.sequenceFin (roundLocal D (optionalExchangeSteps D outbox f) sent)) =
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
    (simulateQ (streamWorld prims D) (Concrete.sequenceFin F)).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$> (simulateQ (localAnswer prims) (Concrete.sequenceFin G)).run h
  | 0, F, G, c, same, h => by simp [Concrete.sequenceFin]
  | n + 1, F, G, c, same, h => by
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, map_bind, same 0 h, bind_map_left]
    refine bind_congr fun r => ?_
    rw [sequence_run (fun i => F i.succ) (fun i => G i.succ) c (fun i => same i.succ) r.2]
    simp only [bind_map_left, map_pure]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {α γ : Type} :
    ∀ {n : ℕ} (f : Fin n → m α) (g : Fin n → α → γ),
      Concrete.sequenceFin (fun i => g i <$> f i) = (fun xs i => g i (xs i)) <$> Concrete.sequenceFin f
  | 0, f, g => by
    simp only [Concrete.sequenceFin, map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f, g => by
    simp only [Concrete.sequenceFin, map_bind, bind_map_left]
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
  Concrete.sequenceFin fun i => if i ∈ D.1 then pure none else
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

