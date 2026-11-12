import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoupling

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
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

open TreeCheckWalkCoupling

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

section Coherent

variable (prims : Primitives) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One world call grows the hash cache and caches a random-oracle answer that it logs. -/
theorem stream_query_coherent (P : Query C → Prop) (hP : ∀ q, P q → ¬ IsFixed q)
    (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (u : (WorldSpec C).Range t) (next : HashCache C × HiddenCache C)
    (hr : (u, next) ∈ support ((streamWorld prims D t).run s)) :
    s.1 ≤ next.1 ∧ TreeSimHashRegionCoherent P next.1 [⟨t, u⟩] := by
  refine ⟨?_, ?_⟩
  · apply treeSim_stream_grows prims D (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) t)) s (u, next)
    simpa only [simulateQ_spec_query] using hr
  · intro q h hq ha
    simp only [TreeSimHashAnswer, List.mem_singleton] at ha
    rcases ha with he | he <;> cases he
    all_goals
      simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨v, hv, he⟩ := hr
      cases he
      exact hashAnswer_cached prims (hP _ hq) s.1 v hv

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A logged run keeps every logged random-oracle answer of a region in its hash cache. -/
theorem logged_coherent (P : Query C → Prop) (hP : ∀ q, P q → ¬ IsFixed q)
    {α : Type} (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (hc : TreeSimHashRegionCoherent P s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    TreeSimHashRegionCoherent P r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    apply ih mid.1 mid.2 r _ hr
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hmid
    obtain ⟨⟨u, next⟩, hu, rfl⟩ := hmid
    have hs := stream_query_coherent prims D P hP t s.1 u next hu
    exact (hc.mono hs.1).append hs.2

end Coherent

section SetupPairs

variable (prims : Primitives) (D : C.Coalition)

/-- The input of `H` that derives the pair key of `p` from the parts of its two
operators. -/
def pairQuery (parts : C.Party → Parts C) (p : C.Pair) : Query C :=
  .derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each answer of a pair-key traversal is logged for its own derivation input. -/
theorem pairs_logged (i : C.Party) (q : ∀ j : C.Party, i ≠ j → Query C) (xs : List C.Party)
    (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (xs.mapM fun j => if h : j = i then pure 0 else hashQuery (q j (Ne.symm h)))
        (LocalSpec C)))).run s)) :
    List.Forall₂ (fun j h => ∀ ne : i ≠ j, TreeSimHashAnswer r.2.2 (q j ne) h) xs r.1 := by
  induction xs generalizing s r with
  | nil =>
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact .nil
  | cons j xs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hr
    refine .cons ?_ (ih a.2 b hb)
    intro ne
    have hji : ¬ j = i := fun he => ne he.symm
    simp only [dif_neg hji] at ha
    exact (treeSetup_hash_logged prims D (q j ne) s a ha).imp
      (fun h => (treeSimLoggedWorld_prefix prims D _ a.2 b hb).subset h)
      (fun h => (treeSimLoggedWorld_prefix prims D _ a.2 b hb).subset h)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A successful reveal row has no abort frame, and its pair key with each `j`
is a logged answer for the input derived from its view of the parts. -/
theorem revealData_pairs (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (s : TreeSimState C) (r : Option (PrssKeys C × List HashOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealData i own committed revealed))).run s)) :
    ∀ row, r.1 = some row → (C.parties.any fun k => Msg.isAbort (revealed k)) = false ∧
      ∀ j (ne : i ≠ j), TreeSimHashAnswer r.2.2
        (pairQuery (fun k => if k = i then own else readReveal .prss (Msg.hashesOf (revealed k)) i k)
          (C.pairOf i j ne)) (row.1.pair j) := by
  unfold prssRevealData at hr
  split_ifs at hr with ha
  · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    intro row he
    cases he
  · unfold prssPostRevealData at hr
    simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨opens, _, hr⟩ := hr
    split_ifs at hr with hc
    · simp only [free_bind, free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨keys, hkeys, shared, hshared, rfl⟩ := hr
      intro row he
      cases he
      refine ⟨by simpa using ha, ?_⟩
      intro j ne
      unfold deriveKeys at hkeys
      simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff,
        reduceCtorEq, if_false] at hkeys
      obtain ⟨param, hparam, term, hterm, pair, hpair, rfl⟩ := hkeys
      have hall := pairs_logged prims D i
        (fun j ne => pairQuery (fun k => if k = i then own else
          readReveal .prss (Msg.hashesOf (revealed k)) i k) (C.pairOf i j ne))
        C.parties term.2 pair hpair
      have hj := forall₂_getD_idxOf _ _ _ hall j (by simp [Committee.parties]) 0 ne
      have later := treeSimLoggedWorld_prefix prims D _ pair.2 shared hshared
      have hj' : TreeSimHashAnswer shared.2.2
          (pairQuery (fun k => if k = i then own else
            readReveal .prss (Msg.hashesOf (revealed k)) i k) (C.pairOf i j ne))
          (pair.1.getD (C.parties.idxOf j) 0) :=
        hj.imp (fun h => later.subset h) (fun h => later.subset h)
      simpa [Committee.parties] using hj'
    · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      intro row he
      cases he

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- In the joint reveal traversal, each successful row is honest, and its pair
key with every honest `j` answers the input derived from the actual parts. -/
theorem revealRows_pairs (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : TreeSimState C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent))).run s)) :
    ∀ i row, r.1 i = some row → i ∉ D.1 ∧ ∀ j, j ∉ D.1 → ∀ ne : i ≠ j,
      TreeSimHashAnswer r.2.2 (pairQuery parts (C.pairOf i j ne)) (row.1.pair j) := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [prssRevealRows, free_sequenceFin, simulateQ_sequenceFin] at hr
  apply (sequenceFin_state_post _
    (fun i out cache => ∀ row, out = some row → i ∉ D.1 ∧ ∀ j, j ∉ D.1 → ∀ ne : i ≠ j,
      TreeSimHashAnswer cache.2 (pairQuery parts (C.pairOf i j ne)) (row.1.pair j)) ?_ ?_ s r hr).2
  · intro i cache result hresult
    refine ⟨(treeSimLoggedWorld_prefix prims D _ cache result hresult).subset, ?_⟩
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hresult
      subst result
      intro row he
      cases he
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        intro row he
        obtain ⟨clean, answers⟩ := revealData_pairs prims D i (parts i) (committed i) _ cache result
          hresult row he
        refine ⟨hi, fun j hj ne => ?_⟩
        have activeJ : active j := by
          by_contra inactive
          have abort : Msg.isAbort (prssRevealInbox D active parts sent i j) = true := by
            simp [prssRevealInbox, hj, inactive, Msg.isAbort]
          have any : (C.parties.any fun k => Msg.isAbort (prssRevealInbox D active parts sent i k)) = true :=
            List.any_eq_true.mpr ⟨j, by simp [Committee.parties], abort⟩
          rw [any] at clean
          cases clean
        have inbox : prssRevealInbox D active parts sent i j =
            some (Msg.hashes (revealTo .prss (parts j) j i)) := by
          simp [prssRevealInbox, hj, activeJ, prssRevealOutbox, ne]
        rw [← pairQuery_congr (fun k => if k = i then parts i else
            readReveal .prss (Msg.hashesOf (prssRevealInbox D active parts sent i k)) i k) parts i j ne
          (by simp)
          (by simp only [if_neg (Ne.symm ne), inbox, readReveal_pair])]
        exact answers j ne
      · simp only [if_neg hi, if_neg ha, free_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hresult
        subst result
        intro row he
        cases he
  · intro i out cache next hle h row he
    exact ⟨(h row he).1, fun j hj ne => ((h row he).2 j hj ne).imp (fun x => hle x) (fun x => hle x)⟩

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

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Two honest operators that finish the PRSS setup hold the same key for
their pair. Their reveals reach each other unchanged, so both derive it from
the same input of `H`. No collision premise is needed. -/
theorem setup_pair_agree (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (i j : C.Party) (ne : i ≠ j) (ki kj : PrssKeys C)
    (hi : p.1.2 i = some ki) (hj : p.1.2 j = some kj) :
    ki.pair j = kj.pair i := by
  have coherent : TreeSimHashRegionCoherent (fun q => ¬ IsFixed q) p.2.1.1 p.2.2 := by
    have whole := hp
    simp only [treeSaltSetup, mem_support_bind_iff] at whole
    obtain ⟨start, hstart, phase⟩ := whole
    have first := logged_coherent prims D (fun q => ¬ IsFixed q) (fun _ h => h) _ ((∅, ∅), []) start
      (fun _ _ _ ha => by simp [TreeSimHashAnswer] at ha) hstart
    rw [treeSimRealRoles, ← simulateQ_executePhase] at phase
    exact logged_coherent prims D (fun q => ¬ IsFixed q) (fun _ h => h) _ start.2 p first phase
  simp only [treeSaltSetup, mem_support_bind_iff] at hp
  obtain ⟨start, _, hp⟩ := hp
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  change p ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) start.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run start.2) at hp
  rw [executePhase_prssSetup_prefix] at hp
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨data, _, adv, _, hp⟩ := hp
  split_ifs at hp with habort
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hp
    subst p
    cases hi
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
    obtain ⟨adv', _, rows, hrows, hp⟩ := hp
    obtain ⟨⟨si, rowI⟩, before⟩ := finish_row prims D A _ rows.1 rows.2 p hp i ki hi
    obtain ⟨⟨sj, rowJ⟩, _⟩ := finish_row prims D A _ rows.1 rows.2 p hp j kj hj
    have pairs := revealRows_pairs prims D _ _ _ _ adv'.2 rows hrows
    obtain ⟨honestI, answerI⟩ := pairs i (ki, si) rowI
    obtain ⟨honestJ, answerJ⟩ := pairs j (kj, sj) rowJ
    have left := answerI j honestJ ne
    have right := answerJ i honestI (Ne.symm ne)
    rw [← pairOf_comm i j ne] at right
    have notFixed : ∀ parts : C.Party → Parts C, ¬ IsFixed (pairQuery parts (C.pairOf i j ne)) := by
      rintro _ ⟨_, h, _⟩
      cases h
    have cachedI := coherent _ _ (notFixed _) (left.imp (fun h => before.subset h) (fun h => before.subset h))
    have cachedJ := coherent _ _ (notFixed _) (right.imp (fun h => before.subset h) (fun h => before.subset h))
    exact Option.some.inj (cachedI.symm.trans cachedJ)

end SetupPairs

/-- Each honest checkpoint row starts the check at the hybrid's tuples,
filled history, label and tag. -/
def RowsAligned (K : Constants C E) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (o : TreeCheckTailCheckpoint A) (h : TreeCheckHybrid C E) : Prop :=
  ∀ i, i ∉ D.1 → ∃ data, o.1.2 i = some data ∧ data.2.1.2 = h.tuples i ∧
    data.2.2.history = filledHistory K i (h.tuples i) ∧ data.2.2.label = h.label ∧
    data.2.2.tag = h.tag

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- At every live checkpoint of the fixed family the real check starts at the
hybrid adapter's state. -/
theorem checkpoint_aligned (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) :
    TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
        RowsAligned K D A o (W.hybrid c o) := by
  intro hb top tree D A x z Z q dealt bounded small j p setup c o pre live
  let W := TreeCheckWalkRecipe.family prims K circuits settings top tree D A x Z q bounded j p
  let b := W.boundary c
  obtain ⟨r, run, bad, _⟩ := live
  have preRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := W) (c := c) (o := o) pre)
  have self i : (b.batch.ctx i).self = i := rfl
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  change r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o) at run
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, accepted, _⟩ := bad.2
  have rows := TreeCheckTailBoundary.counts prims K circuits settings D Z b self parameters
    o preRun r run ⟨i, (value, records), accepted⟩
  intro k honest
  obtain ⟨data, present, history, label, tag, _, _⟩ := rows k honest
  have tuples : data.2.1.2 = (W.hybrid c o).tuples k := by
    change data.2.1.2 = ((o.1.2 k).map (·.2.1.2)).getD []
    rw [present]
    rfl
  refine ⟨data, present, tuples, ?_, ?_, ?_⟩
  · rw [← tuples]
    exact history
  · rw [label]
    rfl
  · rw [tag]
    rfl

/-- On the same tuple count, the hybrid adapter's fuel `checkRounds` is the real
kernel's `2 * halvings + 5` rounds plus three. -/
theorem hybrid_rounds (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) :
    TreeCheckWalkRecipe.AtWalk prims K circuits settings fun _ _ _ _ _ _ _ _ _ _ _ W =>
      ∀ c o, let b := (W.boundary c).batch
        checkRounds (W.hybrid c o).counts.sum =
          (2 * halvings (tupleCount (b.jobs.map (circuits b.parameter ·.kind))) + 5) + 3 := by
  intro _ top tree D A x z Z q _ bounded _ j p _ c o
  let W := TreeCheckWalkRecipe.family prims K circuits settings top tree D A x Z q bounded j p
  have sum := TreeCheckBatchWalk.counts_sum (circuits := circuits) (W.boundary c).batch
  change 2 * halvings (((W.boundary c).batch.counts circuits).sum) + 8 = _
  rw [sum]

/-- Two honest operators hold the same key for their pair. -/
def PairsAgree (D : C.Coalition) (setup : C.Party → Option (PrssKeys C)) : Prop :=
  ∀ i j, i ∉ D.1 → j ∉ D.1 → i ≠ j →
    (TreeCheckWalkRecipe.setupKeys setup i).pair j = (TreeCheckWalkRecipe.setupKeys setup j).pair i

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Present honest setup rows agree on their pair keys. -/
theorem pairsAgree (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setup : p ∈ support (treeSaltSetup prims D A x z))
    (present : ∀ i, i ∉ D.1 → (p.1.2 i).isSome) : PairsAgree D p.1.2 := by
  intro i j hi hj ne
  obtain ⟨ki, rowI⟩ := Option.isSome_iff_exists.mp (present i hi)
  obtain ⟨kj, rowJ⟩ := Option.isSome_iff_exists.mp (present j hj)
  rw [TreeCheckWalkRecipe.setupKeys_some p.1.2 i ki rowI,
    TreeCheckWalkRecipe.setupKeys_some p.1.2 j kj rowJ]
  exact setup_pair_agree prims D A x z p setup i j ne ki kj rowI rowJ

-- The abort-persistence proofs of `TreeSimCheck`, as copied in `TreeCheckWalkCoupling`.
omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem step_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (r : A.State × (C.Party → Step C E (CallSpec I O) α) ×
      (C.Party → C.Party → Option (Msg E)))
    (h : r ∈ support (stepRound worldRoles D A F state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : r.2.1 i = .done a := by
  classical
  unfold stepRound at h
  split_ifs at h with hc
  all_goals
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨p, _, next, hn, rfl⟩ := h
    have hh := mem_support_sequenceFin_oc _ next hn i
    simpa only [hi, support_pure, Set.mem_singleton_iff] using hh

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem rounds_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (out : A.State × (C.Party → Option α))
    (h : out ∈ support (executeRounds worldRoles D A F fuel state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : out.2 i = a := by
  classical
  induction fuel generalizing state steps out with
  | zero =>
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at h
    subst out
    exact congrArg Step.output hi
  | succ fuel ih =>
    simp only [executeRounds] at h
    split_ifs at h with hd
    · cases h
      exact congrArg Step.output hi
    · simp only [support_bind, Set.mem_iUnion] at h
      obtain ⟨r, hr, ho⟩ := h
      exact ih r.1 r.2.1 out ho (step_done D A F state steps r hr i a hi)

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

omit [Fintype E] [DecidableEq E] in
/-- The check kernel without its log and hidden cache is a real execution. -/
theorem kernel_erase (circuits : Circuits) (rounds : ℕ) (b : TreeCheckBatchBoundary A)
    (o : TreeCheckTailCheckpoint A)
    (P : C.Party → PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))
    (start : free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))) = startSteps worldRoles D P) :
    (fun s : KernelState A => (s.1, s.2.1.1)) <$> checkKernel prims K circuits D A rounds b o =
      realRun prims D A rounds o.1.1 P o.2.1 := by
  unfold checkKernel realRun
  rw [start]
  have whole := treeSimLoggedWorld_erase prims D
    (startSteps worldRoles D P >>= fun steps =>
      executeSteps worldRoles D A noFunctionality rounds o.1.1 steps) o.2.1 o.2.2
  rw [← whole]
  simp only [simulateQ_bind, StateT.run_bind, Functor.map_map, map_bind]

omit [Fintype E] [DecidableEq E] in
/-- The checkpoint rows of the corrupt operators are empty. -/
theorem corrupt_rows (circuits : Circuits) (settings : Settings) (b : TreeCheckTailBoundary A)
    (o : TreeCheckTailCheckpoint A) (run : o ∈ support (b.pre prims K circuits settings D)) :
    ∀ i ∈ D.1, o.1.2 i = none := by
  have raw := treeCheck_logged_support prims D _ _ run
  unfold executePhase at raw
  rw [mem_support_bind_iff] at raw
  obtain ⟨steps, started, rounds⟩ := raw
  intro i hi
  have start : steps i = .done none := by
    have h := mem_support_sequenceFin_oc _ steps started i
    simpa [hi] using h
  exact rounds_done D A noFunctionality _ b.batch.state steps o.1 rounds i none start

omit [Fintype E] [DecidableEq E] in
/-- The first local pass of the kernel starts the checkpoint rows. -/
theorem kernel_start (circuits : Circuits) (b : TreeCheckBatchBoundary A)
    (o : TreeCheckTailCheckpoint A) (corrupt : ∀ i ∈ D.1, o.1.2 i = none) :
    free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))) =
      startSteps worldRoles D (fun i => (o.1.2 i).elim failure
        (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, continueStep, free_pure]
  · cases he : o.1.2 i <;> simp [hi, he, continueStep, worldRoles, free_pure, advance_pure]

/-- The covered real cache and the hybrid cache inside it give the kernel relation. -/
theorem kernelRelation_of_final (h : TreeCheckHybrid C E) (saved : KernelState A)
    (out : (h.adversary.State × (C.Party → Option Unit)) × HashCache C)
    (covered : TreeSimCheckCacheCovered saved.2.1.1 saved.2.2)
    (final : Final D A (saved.1, saved.2.1.1) out) : KernelRelation D A h saved out := by
  intro good i hi alive
  obtain ⟨le, accept⟩ := final i hi alive
  refine ⟨fun collision => good ?_, accept⟩
  obtain ⟨q, r, u, v, hne, hq, hr, huv⟩ := treeSimCheck_domain_collision_mono le collision
  have huv' : u = v := eq_of_heq huv
  subst v
  have sq : TreeSimHashDomain q := by
    by_contra hn
    simp [splitRegionCache, hn] at hq
  have sr : TreeSimHashDomain r := by
    by_contra hn
    simp [splitRegionCache, hn] at hr
  exact ⟨q, r, u, treeSimHash_domain_budget q sq, treeSimHash_domain_budget r sr, hne,
    covered q u sq (by simpa [splitRegionCache, sq] using hq),
    covered r u sr (by simpa [splitRegionCache, sr] using hr)⟩

/-- A real execution coupled to the hybrid adapter gives the kernel coupling,
once the kernel's final hash cache is covered by its log. -/
theorem kernel_of_real (circuits : Circuits) (h : TreeCheckHybrid C E) (rounds : ℕ)
    (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A)
    (P : C.Party → PartyM C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))
    (start : free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))) = startSteps worldRoles D P)
    (covered : ∀ saved ∈ support (checkKernel prims K circuits D A rounds b o),
      TreeSimCheckCacheCovered saved.2.1.1 saved.2.2)
    (coupled : RelTriple (realRun prims D A rounds o.1.1 P o.2.1) (hybridKernel prims K D h)
      (Final D A)) :
    RelTriple (checkKernel prims K circuits D A rounds b o) (hybridKernel prims K D h)
      (KernelRelation D A h) := by
  rw [← kernel_erase prims K D A circuits rounds b o P start] at coupled
  have strong := relTriple_support_left (relTriple_of_map_left coupled) covered
  exact relTriple_post_mono strong fun saved out related =>
    kernelRelation_of_final D A h saved out related.2 related.1

/-- After a round in which an honest operator has stopped, every honest operator
has stopped when each program respects abort frames. -/
theorem realRun_doomed {β : Type} (n : ℕ) (stA : A.State) (P : C.Party → PartyM C E RealSpec β)
    (w : HashCache C × HiddenCache C)
    (exchange : ∀ i, i ∉ D.1 → TreeSimCheckExchange (P i))
    (dead : ∃ j, j ∉ D.1 ∧ P j = failure) :
    ∀ x ∈ support (realRun prims D A (n + 1) stA P w), ∀ i, i ∉ D.1 → x.1.2 i = .done none := by
  intro x hx
  unfold realRun at hx
  rw [support_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have raw : r.1 ∈ support (startSteps worldRoles D P >>= fun steps =>
      executeSteps worldRoles D A noFunctionality (n + 1) stA steps) := by
    apply OracleComp.support_simulateQ_run'_subset (streamWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  rw [mem_support_bind_iff] at raw
  obtain ⟨steps, started, rounds⟩ := raw
  have each : ∀ i, TreeSimCheckExchangeStep (steps i) := by
    intro i
    have h := mem_support_sequenceFin_oc _ steps started i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, support_pure, Set.mem_singleton_iff] at h
      rw [h]
      rfl
    · simp only [if_neg hi] at h
      exact exchange i hi _ (treeSimCheck_support_free _ h)
  obtain ⟨j, hj, hjP⟩ := dead
  have stopped : steps j = .done none := by
    have h := mem_support_sequenceFin_oc _ steps started j
    simp only [if_neg hj, hjP] at h
    simpa [advance_pure, free_pure] using h
  rw [executeSteps] at rounds
  split_ifs at rounds with hd
  · simp only [support_pure, Set.mem_singleton_iff] at rounds
    intro i hi
    rw [rounds]
    have hstep := each i
    cases he : steps i with
    | done out =>
      rw [he] at hstep
      show steps i = _
      rw [he]
      exact congrArg Step.done hstep
    | wait out resume =>
      have := hd i hi
      rw [he] at this
      exact this.elim
    | call input resume => exact input.elim
  · rw [treeSimCheck_exchange_round_abort D A stA steps each ⟨j, hj, stopped⟩] at rounds
    simp only [bind_assoc, pure_bind, support_bind, Set.mem_iUnion] at rounds
    obtain ⟨b, _, rounds⟩ := rounds
    rw [executeSteps_done worldRoles D A noFunctionality n _ (fun _ => Step.done none)
      (fun i _ => (trivial : True))] at rounds
    simp only [support_pure, Set.mem_singleton_iff] at rounds
    intro i _
    rw [rounds]

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
theorem hashPrefix_support {X : Type} (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (xs : C.Party → Option X) (hx : xs ∈ support (hashPrefix D W)) :
    ∀ i, (i ∈ D.1 → xs i = none) ∧ (i ∉ D.1 → (xs i).isSome) := by
  intro i
  have h := mem_support_sequenceFin_oc _ xs hx i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, support_pure, Set.mem_singleton_iff] at h
    exact ⟨fun _ => h, fun h' => (h' hi).elim⟩
  · simp only [if_neg hi, support_map, Set.mem_image] at h
    obtain ⟨x, _, hx⟩ := h
    exact ⟨fun h' => (hi h').elim, fun _ => by rw [← hx]; rfl⟩

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




variable (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)

/-- The family's GS20 check adversary. -/
abbrev adapter : CheckAdversary C E (List (Tuple C)) :=
  TreeCheckWalkRecipe.checkAdversary prims K D A x prss cache0 label0

/-- From every start with the real hash cache equal to the hybrid one, extending
the checkpoint cache, and no hidden draw at the label `ℓ` or later, the real
programs `P` and the hybrid programs `Q` couple with `Final`. -/
def Coupled {β : Type} (n n' ℓ : ℕ) (P : C.Party → PartyM C E RealSpec β)
    (Q : C.Party → PartyM C E (CheckSpec C E) Unit) : Prop :=
  ∀ (stA : A.State) (h : HashCache C) (c : HiddenCache C), cache0 ≤ h → TreeSimFutureEmpty ℓ c →
    RelTriple (realRun prims D A n stA P (h, c))
      (hybRun prims K D (adapter prims K D A x prss cache0 label0) n' ((stA, ℓ) : A.State × ℕ) Q h)
      (Final D A)

omit [DecidableEq E] in
/-- An exchange round couples the same outgoing messages; the continuations
receive the same incoming mail. -/
theorem coupled_exchange {β : Type} (n n' ℓ : ℕ) (outbox : C.Party → Option (Mail C E))
    (fR : C.Party → Mail C E → PartyM C E RealSpec β)
    (fH : C.Party → Mail C E → PartyM C E (CheckSpec C E) Unit)
    (ha : ∃ i, i ∉ D.1 ∧ (outbox i).isSome)
    (next : ∀ sent : C.Party → Mail C E, Coupled prims K D A x prss cache0 label0 n n' ℓ
      (fun i => afterExchange D outbox sent i (fR i)) (fun i => afterExchange D outbox sent i (fH i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 1) ℓ
      (fun i => optionalExchange (outbox i) (fR i)) (fun i => optionalExchange (outbox i) (fH i)) := by
  intro stA h c hle fresh
  rw [realRun_exchange prims D A n stA outbox fR (h, c) ha]
  unfold hybRun
  rw [executePhase_optionalExchange D _ _ n' _ outbox fH ha]
  simp only [simulateQ_bind, StateT.run_bind]
  let view : C.Party → C.Party → Option (Msg E) := fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then ((outbox i).getD (fun _ => none)) c else none
  have hreal := adversary_run prims D (A.round stA view) h c
  have hhyb : (simulateQ (localAnswer prims)
      ((adapter prims K D A x prss cache0 label0).round ((stA, ℓ) : A.State × ℕ) view)).run h =
      (fun r => (((r.1.1, ℓ), r.1.2), r.2)) <$> (simulateQ (localAnswer prims) (A.round stA view)).run h := by
    simp [adapter, TreeCheckWalkRecipe.checkAdversary, simulateQ_map, StateT.run_map]
  rw [hreal]
  erw [hhyb]
  simp only [bind_map_left]
  have base := relTriple_support_left (relTriple_refl ((simulateQ (localAnswer prims)
    (A.round stA view)).run h)) (fun r hr => (grows_localAnswer prims).simulateQ (A.round stA view) h r hr)
  have mapped : RelTriple ((simulateQ (localAnswer prims) (A.round stA view)).run h)
      ((fun r => (((r.1.1, ℓ), r.1.2), r.2)) <$> (simulateQ (localAnswer prims) (A.round stA view)).run h)
      (fun a b => b = (((a.1.1, ℓ), a.1.2), a.2) ∧ h ≤ a.2) := by
    have := relTriple_map (f := id) (g := fun r : (A.State × (C.Party → C.Party → Option (Msg E))) ×
      HashCache C => (((r.1.1, ℓ), r.1.2), r.2))
      (R := fun a b => b = (((a.1.1, ℓ), a.1.2), a.2) ∧ h ≤ a.2)
      (relTriple_post_mono base (fun a b hab => by rcases hab with ⟨rfl, g⟩; exact ⟨rfl, g⟩))
    simpa using this
  apply relTriple_bind mapped
  rintro r _ ⟨rfl, grow⟩
  exact next r.1.2 r.1.1 r.2 c (hle.trans grow) fresh


omit [DecidableEq E] in
/-- A local pass that starts with the same hash queries and is pure afterwards
couples once the continuations couple on every vector of answers. -/
theorem coupled_prefix {X β : Type} [Inhabited X] (n n' ℓ : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (gR : C.Party → X → PartyM C E RealSpec β) (gH : C.Party → X → PartyM C E (CheckSpec C E) Unit)
    (sR : C.Party → X → Step C E RealSpec β) (sH : C.Party → X → Step C E (CheckSpec C E) Unit)
    (pureR : ∀ i x, advance (gR i x).run = pure (sR i x))
    (pureH : ∀ i x, advance (gH i x).run = pure (sH i x))
    (next : ∀ xs : C.Party → X, Coupled prims K D A x prss cache0 label0 n n' ℓ
      (fun i => gR i (xs i)) (fun i => gH i (xs i))) :
    Coupled prims K D A x prss cache0 label0 n n' ℓ
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gR i)
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gH i) := by
  intro stA h c hle fresh
  unfold realRun hybRun executePhase
  rw [startSteps_world_prefix D W gR sR pureR, startSteps_local_prefix D W gH sH pureH]
  simp only [simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]
  rw [hashPrefix_run prims D W h c, bind_map_left]
  apply relTriple_bind (relTriple_support_left (relTriple_refl _)
    (P := fun r : (C.Party → Option X) × HashCache C => h ≤ r.2 ∧
      ∀ i, (i ∈ D.1 → r.1 i = none) ∧ (i ∉ D.1 → (r.1 i).isSome)) (fun r hr =>
    ⟨(grows_localAnswer prims).simulateQ _ h r hr, hashPrefix_support D W r.1 (by
      apply OracleComp.support_simulateQ_run'_subset (localAnswer prims)
      rw [StateT.run'_eq, support_map]
      exact ⟨r, hr, rfl⟩)⟩))
  rintro r _ ⟨rfl, grow, shape⟩
  let xs : C.Party → X := fun i => (r.1 i).getD default
  have startR : startSteps worldRoles D (fun i => gR i (xs i)) = pure (prefixSteps sR r.1) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi, prefixSteps, (shape i).1 hi]
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((shape i).2 hi)
      simp [hi, prefixSteps, hy, xs, worldRoles, pureR, free_pure]
  have startH : startSteps localRoles D (fun i => gH i (xs i)) = pure (prefixSteps sH r.1) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi, prefixSteps, (shape i).1 hi]
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((shape i).2 hi)
      simp [hi, prefixSteps, hy, xs, localRoles, pureH]
  have hnext := next xs stA r.2 c (hle.trans grow) fresh
  unfold realRun hybRun executePhase at hnext
  rw [startR, startH] at hnext
  simpa only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind] using hnext


omit [DecidableEq E] in
/-- The last local pass: the hybrid decides each operator locally, and every
real operator that it rejects has stopped. -/
theorem coupled_end {β : Type} (n' ℓ : ℕ) (P : C.Party → PartyM C E RealSpec β)
    (Q : C.Party → PartyM C E (CheckSpec C E) Unit) (o : C.Party → Option Unit)
    (decided : ∀ i, advance (Q i).run = pure (.done (o i)))
    (stopped : ∀ i, i ∉ D.1 → o i = none → ∀ step ∈ support (advance (P i).run), step = .done none) :
    Coupled prims K D A x prss cache0 label0 0 n' ℓ P Q := by
  intro stA h c _ _
  have startH : startSteps localRoles D Q = pure (fun i => if i ∈ D.1 then .done none else .done (o i)) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp [hi, localRoles, decided i]
  have hyb : hybRun prims K D (adapter prims K D A x prss cache0 label0) n' ((stA, ℓ) : A.State × ℕ) Q h =
      pure ((((stA, ℓ) : A.State × ℕ), fun i => if i ∈ D.1 then none else o i), h) := by
    unfold hybRun executePhase
    rw [startH, pure_bind]
    cases n' with
    | zero =>
      simp only [executeRounds, simulateQ_pure, StateT.run_pure]
      congr 3
      funext i
      by_cases hi : i ∈ D.1 <;> simp [hi, Step.output]
    | succ n' =>
      rw [executeRounds, if_pos (fun i hi => by simp [hi, Step.isDone])]
      simp only [simulateQ_pure, StateT.run_pure]
      congr 3
      funext i
      by_cases hi : i ∈ D.1 <;> simp [hi, Step.output]
  rw [hyb]
  apply relTriple_of_support
  intro a ha b hb
  have hb' := (mem_support_pure_iff _ _).mp hb
  subst hb'
  unfold realRun at ha
  rw [support_map] at ha
  obtain ⟨r, hr, rfl⟩ := ha
  have grow : h ≤ r.2.1 := treeSim_stream_grows prims D _ (h, c) r hr
  have raw : r.1 ∈ support (startSteps worldRoles D P >>= fun steps =>
      executeSteps worldRoles D A noFunctionality 0 stA steps) := by
    apply OracleComp.support_simulateQ_run'_subset (streamWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  rw [mem_support_bind_iff] at raw
  obtain ⟨steps, started, rounds⟩ := raw
  simp only [executeSteps, support_pure, Set.mem_singleton_iff] at rounds
  intro i hi alive
  refine ⟨grow, ?_⟩
  simp only [if_neg hi]
  cases hoi : o i with
  | some u => rfl
  | none =>
    exfalso
    apply alive
    rw [rounds]
    have h := mem_support_sequenceFin_oc _ steps started i
    simp only [if_neg hi] at h
    exact stopped i hi hoi _ (treeSimCheck_support_free _ h)

end Phases

end ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.hybrid_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.hybrid_rounds

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.logged_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.logged_coherent

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.setup_pair_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.setup_pair_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.pairsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.pairsAgree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.checkpoint_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.checkpoint_aligned

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_map_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_map_left

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.relTriple_of_support

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.kernel_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.kernel_of_real

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.realRun_doomed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.realRun_doomed

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.adversary_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.adversary_run

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.hash_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.hash_run

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.realRun_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.realRun_exchange

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_exchange

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_end

