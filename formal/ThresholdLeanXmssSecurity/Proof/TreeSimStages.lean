import ThresholdLeanXmssSecurity.Proof.TreeSim

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-!
The stages task for the fixed events in the frozen `TreeSim` module.
`treeStages_firstCheck_padded_two_rounds` now composes the real first check
Coin, expansion hashes, zero guard and first slice through its next challenge
Coin. It handles selective aborts and uses concrete finite padding without
resetting the shared dealer cache. The remaining check iterations, their
algebraic invariant and the complete reachable ceremony core remain open.
Actual field PRSS draws realize the GS20 masks for arbitrary encodings,
including repeated holders, visible keys and optional earlier aborts.
`treeStages_extendMult_real_start` constructs the frozen boundary data;
`treeStages_extendMult_aborted` proves the complete selective-abort gadget.
`TreeStagesExtendMultChallenge.coupling` proves the successful reduction
transition through the next Coin entry, with the actual recorded outputs.
`treeStages_extendMult_challenge_preserves` exposes it as a core preservation
case. Challenge hashing and rejection preserve arbitrary private-cache
invariants, including when the dealer has already populated the public cache.
`treeStages_saltedDigest_challenge` proves the complete actual salt PRSS,
history/digest queries, rushing comparison and following Coin entry when held
histories agree. `treeStages_digest_challenge_preserves` supplies its exchange
preservation case. Field ExtendMult preserves this history equality for an
unfilled T₀. For unequal histories, `treeStages_hiddenDigest_fresh` introduces
the standard salted-digest cache swap and proves the entire adaptive counted
continuation up to the fixed salt-guess event. `treeStages_split_digest_round`
closes the rejected check exchange from actual logged split-history evidence.
`treeStages_split_digest_finish` continues that transported-cache branch through
the final distinguisher. `treeStages_saltedDigest_split_finish` proves the entire
split-history suffix from actual salt PRSS to final observation when held
histories agree across the two runs, deriving every hash certificate from the
actual log. Composing unequal-history digest entries and meeting the core's
public-cache equality requirement remain open for hidden digests.
`treeStagesCopyPadding` covers the finite copy-hash domain independently of
private masks. `treeStages_finalMask_open_round` connects the GS20 final-mask
bijection and bounded T₀ correction to the actual next OpenRep entry.
`treeStages_finalMask_simBatch_finish` closes the final field check and the
actual simulator output override, including clear PRF queries, unbounded T₀
correction, batch decoding, selective aborts and any remaining fuel. Its mask
compatibility follows from equal residuals. `treeStagesOutputPadding` proves
both copy and PRF coverage while preserving the dealer cache. Reachability
must still establish the residual, late translation and internal-share
equations. `treeStages_simBatch_next_rounds` composes a nonterminal check,
actual corrected opening, public hash computation, next input queries and
PRSS entry in either mode. `treeStages_actualBatchData` obtains that entry
directly from real and simulated `runJobs`, including zero-layer batches.
`treeStages_openBatchPeer_boundary` supplies the frozen boundary interface.
`treeStagesCeremonyPrfPadding` covers real and dummy PRF seeds for every
later job, including adaptively selected points.
`treeStages_batch_collector_first_round` constructs the GS20 collector masks
from the actual batch inputs and couples the first rushing round through its
forwarding boundary. `TreeStagesCollectorLayer.boundary_round` closes the
collector-to-collector transition for the actual gadgets, including prior
aborts, recorded histories, fresh next masks and the remaining layer schedule.
`TreeStagesCollectorTail.execute_three` composes the entire final collector
and peer Rerand into the check's actual first Coin, including the driver's
stopping test, selective aborts, GS20 masks and fresh later cache labels.
`TreeStagesCollectorSchedule.execute` inducts over all remaining AND layers,
including both exchanges and every optional abort. `treeStages_collector_runJobs_check`
starts from the actual real and simulated `runJobs` programs and their first
PRSS draws, handles zero-depth batches, and reaches the first check Coin in
`2 * depth + 1` driver rounds. `treeStages_collector_input_runJobs_check`
includes the actual input PRF calls and their real logs before those layers.
`treeStages_collector_ceremonyBatch_check` instantiates this composition with
dealt keys, dummy hidden seeds, common PRSS keys and reset histories; finite
padding supplies coverage for all later jobs without clearing dealer answers.
`TreeStagesPeerSchedule.execute` proves the whole peer-layer fold, including
abort propagation and Rerand. `treeStages_input_runJobs_check` and
`treeStages_ceremonyBatch_check` compose actual inputs and all layers in either
mode using `settings.mode.rounds * depth + 1` rounds. The peer theorem also
covers empty outputs when an AND tuple makes the check nonempty; its schedule
retains this tuple-count invariant. `TreeStagesRerandTail.execute_nonempty`
uses the checked tuples rather than requiring nonempty outputs.
`treeStagesCheckAfterCoin` retains the exact remaining check and caller.
Zero-output collector batches, empty checks and the complete check invariant
still need integration into the ceremony schedule.
`TreeStagesReach` retains the real programs and exact log;
its entry and step lemmas prove same-execution replay and empty corrupt outputs.
`treeStages_core_of_reachable_relation` uses these facts to construct the frozen
core from a bounded gadget relation, without a separate replay premise.
Global reachability must instantiate the remaining relation and its progress.
Already-bad prefixes have a complete round core. The remaining good-prefix
ceremony invariant and successful continuation closures are the explicit
`TreeSimStagesGoodCoreGoal` premise of the final assembly theorem.
No hash-bound or check-bound premise is used here.
-/

/-- Decode a finite array in the order used by `elementCodec`. No algebraic
property of the encoding is assumed. -/
def treeStagesDecode (count : ℕ) : (Fin (count * elementBits) → Bit) ≃ (Fin count → E) :=
  ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bit)).trans
    (Equiv.curry (Fin count) (Fin elementBits) Bit)).trans
      (Equiv.piCongrRight fun _ => K.encode.symm)

@[simp] theorem treeStagesDecode_apply (count : ℕ) (bits : Fin (count * elementBits) → Bit)
    (g : Fin count) :
    treeStagesDecode K count bits g = K.encode.symm (fun b => bits (finProdFinEquiv (g, b))) := rfl

/-- Conjugate field addition by the actual encoding equivalence. The result
is a bijection of complete bit blocks, even for non-linear encodings. -/
def treeStagesFieldShift (count : ℕ) (delta : Fin count → E) :
    (Fin (count * elementBits) → Bit) ≃ (Fin (count * elementBits) → Bit) :=
  ((treeStagesDecode K count).trans (Equiv.addRight delta)).trans (treeStagesDecode K count).symm

@[simp] theorem treeStagesFieldShift_decode (count : ℕ) (delta : Fin count → E)
    (bits : Fin (count * elementBits) → Bit) :
    treeStagesDecode K count (treeStagesFieldShift K count delta bits) =
      treeStagesDecode K count bits + delta := by
  simp [treeStagesFieldShift]

/-- Log-preserving fresh-table coupling for any bijection, with exact caches. -/
theorem treeStages_hidden_bij (D : C.Coalition) {n : ℕ} (addr : Fin n → HiddenAddress C)
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (h₁ h₂ : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (hc₁ : ∀ i, c₁ (addr i) = none) (hc₂ : ∀ i, c₂ (addr i) = none)
    (f : (Fin n → Bit) ≃ (Fin n → Bit)) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run ((h₁, c₁), log))
      ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₂, c₂))
      (fun a b => b.1 = f a.1 ∧ a.2.1 = (h₁, cacheFin addr a.1 c₁) ∧
        b.2 = (h₂, cacheFin addr b.1 c₂) ∧ a.2.2 = log ++ treeSimHiddenLog addr a.1) := by
  rw [treeSim_hiddenDraws_log]
  have h : RelTriple
      ((fun r => (r.1, r.2, log ++ treeSimHiddenLog addr r.1)) <$>
        (simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₁, c₁))
      (id <$> (simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₂, c₂))
      (fun a b => b.1 = f a.1 ∧ a.2.1 = (h₁, cacheFin addr a.1 c₁) ∧
        b.2 = (h₂, cacheFin addr b.1 c₂) ∧ a.2.2 = log ++ treeSimHiddenLog addr a.1) := by
    apply relTriple_map
    apply relTriple_post_mono (streamWorld_fresh_rel_bij prims D addr ha hh h₁ h₂ c₁ c₂ hc₁ hc₂ f f.bijective)
    intro a b hab
    exact ⟨hab.1, hab.2.1, hab.2.2, rfl⟩
  simpa only [id_map] using h

/-- A decoded draw has the codec's literal padded tail, which need not be zero. -/
def treeStagesFieldResult (count : ℕ) (vals : Fin count → E) : ℕ → E := fun g =>
  if hg : g < count then vals ⟨g, hg⟩ else K.encode.symm (fun _ => 0)

/-- Exact finite-array form of the real field PRSS draw. -/
theorem treeStages_element_table (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)) =
      (fun bits => treeStagesFieldResult K count (treeStagesDecode K count bits)) <$>
        hiddenDraws (fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)) := by
  simp only [elementCodec, liftComp_bind, liftComp_pure, free_bind, free_pure]
  rw [treeSim_prgBits_table, Nat.mul_comm elementBits count]
  simp only [bind_map_left, bind_pure_comp, Functor.map_map]
  congr 1
  funext bits g
  unfold treeStagesFieldResult
  split_ifs with hg
  · rw [treeStagesDecode_apply]
    congr 1
    funext b
    have hb : elementBits * g + b.val < count * elementBits := by
      have hn := (finProdFinEquiv (⟨g, hg⟩, b)).isLt
      change b.val + elementBits * g < count * elementBits at hn
      omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hb, dif_pos, Option.getD_some]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm]
  · congr 1
    funext b
    have hb : ¬ elementBits * g + b.val < count * elementBits := by
      have hm := Nat.mul_le_mul_right elementBits (Nat.le_of_not_gt hg)
      rw [Nat.mul_comm g elementBits] at hm
      omega
    simp [List.getD_eq_getElem?_getD, hb]

/-- Additive field masks are realized by actual hidden PRSS queries. The real
log and both caches retain the encoded bits, not an assumed linear encoding. -/
theorem treeStages_element_shift (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (key : HashOutput) (label idx count : ℕ) (delta : Fin count → E)
    (h₁ h₂ : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (fresh₁ : ∀ g < count * elementBits, c₁ ((name, key), label, idx, g) = none)
    (fresh₂ : ∀ g < count * elementBits, c₂ ((name, key), label, idx, g) = none) :
    let addr := fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run ((h₁, c₁), log))
      ((simulateQ (streamWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run (h₂, c₂))
      (fun a b => ∃ bits,
        a.1 = treeStagesFieldResult K count (treeStagesDecode K count bits) ∧
        b.1 = treeStagesFieldResult K count (treeStagesDecode K count bits + delta) ∧
        a.2.1 = (h₁, cacheFin addr bits c₁) ∧
        b.2 = (h₂, cacheFin addr (treeStagesFieldShift K count delta bits) c₂) ∧
        a.2.2 = log ++ treeSimHiddenLog addr bits) := by
  dsimp only
  rw [treeStages_element_table]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeStages_hidden_bij prims D
    (fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val))
    (fun i j hij => Fin.ext (congrArg (fun x => x.2.2.2) hij)) (fun _ => hidden)
    h₁ h₂ c₁ c₂ log (fun g => fresh₁ g.val g.isLt) (fun g => fresh₂ g.val g.isLt)
    (treeStagesFieldShift K count delta))
  intro a b hab
  refine ⟨a.1, rfl, ?_, hab.2.1, ?_, hab.2.2.2⟩
  · rw [hab.1, treeStagesFieldShift_decode]
  · rw [← hab.1]
    exact hab.2.2.1

/-- The cache shift may depend on the newly sampled block. Old positions keep
their old shifts; new positions use the difference of their encoded answers. -/
def treeStagesTableDelta {n : ℕ} (addr : Fin n → HiddenAddress C)
    (old : HiddenAddress C → Bit) (a b : Fin n → Bit) (x : HiddenAddress C) : Bit :=
  if h : ∃ i, addr i = x then b h.choose - a h.choose else old x

theorem treeStagesTableDelta_at {n : ℕ} (addr : Fin n → HiddenAddress C)
    (ha : Function.Injective addr) (old : HiddenAddress C → Bit) (a b : Fin n → Bit) (i : Fin n) :
    treeStagesTableDelta addr old a b (addr i) = b i - a i := by
  unfold treeStagesTableDelta
  split_ifs with h
  · rw [ha h.choose_spec]
  · exact False.elim (h ⟨i, rfl⟩)

/-- Every encoded-block bijection gives a valid post-draw cache translation.
Freshness is required for the sampling lemma, not this cache identity. -/
theorem treeStagesTableDelta_related {n : ℕ} (addr : Fin n → HiddenAddress C)
    (ha : Function.Injective addr) (old : HiddenAddress C → Bit) (a b : Fin n → Bit)
    (c₁ c₂ : HiddenCache C) (rel : TreeSimHiddenRel old c₁ c₂) :
    TreeSimHiddenRel (treeStagesTableDelta addr old a b) (cacheFin addr a c₁) (cacheFin addr b c₂) := by
  intro x
  by_cases hx : ∃ i, addr i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [cacheFin_at addr ha, cacheFin_at addr ha, treeStagesTableDelta_at addr ha]
    simp
  · have hne : ∀ i, x ≠ addr i := fun i he => hx ⟨i, he.symm⟩
    rw [cacheFin_of_not_mem addr a c₁ x hne, cacheFin_of_not_mem addr b c₂ x hne]
    simpa only [treeStagesTableDelta, dif_neg hx] using rel x

/-- Only hidden addresses are changed, so the shift stays zero on every
visible stream, regardless of the sampled field masks. -/
theorem treeStagesTableDelta_visible (D : C.Coalition) {n : ℕ} (addr : Fin n → HiddenAddress C)
    (hidden : ∀ i, Hidden D (addr i).1.1) (old : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0) (a b : Fin n → Bit)
    (x : HiddenAddress C) (hx : ¬ Hidden D x.1.1) :
    treeStagesTableDelta addr old a b x = 0 := by
  have h : ¬ ∃ i, addr i = x := by
    rintro ⟨i, rfl⟩
    exact hx (hidden i)
  simp only [treeStagesTableDelta, dif_neg h, visible x hx]

/-- Later labels keep their zero translation; no encoding assumption is used. -/
theorem treeStagesTableDelta_future {n : ℕ} (addr : Fin n → HiddenAddress C) (label : ℕ)
    (labels : ∀ i, (addr i).2.1 = label) (old : HiddenAddress C → Bit)
    (future : TreeSimFutureZero (label + 1) old) (a b : Fin n → Bit) :
    TreeSimFutureZero (label + 1) (treeStagesTableDelta addr old a b) := by
  intro x hx
  have h : ¬ ∃ i, addr i = x := by
    rintro ⟨i, rfl⟩
    have := labels i
    omega
  simpa only [treeStagesTableDelta, dif_neg h] using future x hx

/-- The additive shift has a zero tail, unlike the decoded draw itself. -/
def treeStagesFieldDelta (count : ℕ) (delta : Fin count → E) : ℕ → E := fun g =>
  if hg : g < count then delta ⟨g, hg⟩ else 0

theorem treeStagesFieldResult_add (count : ℕ) (vals delta : Fin count → E) :
    treeStagesFieldResult K count (vals + delta) =
      treeStagesFieldResult K count vals + treeStagesFieldDelta count delta := by
  funext g
  by_cases hg : g < count <;> simp [treeStagesFieldResult, treeStagesFieldDelta, hg]

/-- A table writes only its own label. -/
theorem treeStages_cacheFin_frame {n : ℕ} (addr : Fin n → HiddenAddress C) (label : ℕ)
    (labels : ∀ i, (addr i).2.1 = label) (vals : Fin n → Bit) (cache : HiddenCache C) :
    TreeSimCacheFrame label cache (cacheFin addr vals cache) := by
  intro x hx
  apply cacheFin_of_not_mem
  intro i he
  exact hx (he ▸ labels i)

/-- Actual hidden field draws return shifted field values and an adaptively
chosen bit-cache relation. This is the postcondition needed between successive
PRSS reads; it preserves future-label freshness and every visible stream. -/
theorem treeStages_element_shift_rel (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (key : HashOutput) (label idx count : ℕ) (delta : Fin count → E)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (label + 1) old)
    (h : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (rel : TreeSimHiddenRel old c₁ c₂)
    (fresh₁ : ∀ g < count * elementBits, c₁ ((name, key), label, idx, g) = none)
    (fresh₂ : ∀ g < count * elementBits, c₂ ((name, key), label, idx, g) = none) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run ((h, c₁), log))
      ((simulateQ (streamWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run (h, c₂))
      (fun a b => b.1 = a.1 + treeStagesFieldDelta count delta ∧
        ∃ next, TreeSimStreamRel next a.2 b.2 ∧
          (∀ x, ¬ Hidden D x.1.1 → next x = 0) ∧ TreeSimFutureZero (label + 1) next ∧
          TreeSimCacheFrame label c₁ a.2.1.2 ∧ TreeSimCacheFrame label c₂ b.2.2) := by
  apply relTriple_post_mono (treeStages_element_shift prims K D name hidden key label idx count delta
    h h c₁ c₂ log fresh₁ fresh₂)
  intro a b hab
  obtain ⟨bits, ha, hb, hc, hd, hlog⟩ := hab
  let addr := fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)
  have inj : Function.Injective addr := fun i j hij => Fin.ext (congrArg (fun x => x.2.2.2) hij)
  refine ⟨?_, treeStagesTableDelta addr old bits (treeStagesFieldShift K count delta bits), ?_⟩
  · rw [ha, hb, treeStagesFieldResult_add]
  · refine ⟨?_, treeStagesTableDelta_visible D addr (fun _ => hidden) old visible _ _,
      treeStagesTableDelta_future addr label (fun _ => rfl) old future _ _, ?_, ?_⟩
    · change a.2.1.1 = b.2.1 ∧ _
      rw [hc, hd]
      exact ⟨rfl, treeStagesTableDelta_related addr inj old _ _ c₁ c₂ rel⟩
    · rw [hc]
      exact treeStages_cacheFin_frame addr label (fun _ => rfl) bits c₁
    · rw [hd]
      exact treeStages_cacheFin_frame addr label (fun _ => rfl) _ c₂

/-- A repeated field draw decodes the previously cached block, with its actual
log still appended. It does not create another mask or reset either cache. -/
theorem treeStages_element_cached_logged (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (key : HashOutput) (label idx count : ℕ) (bits : Fin (count * elementBits) → Bit)
    (h : HashCache C) (cache : HiddenCache C) (log : TreeSimLog C)
    (cached : ∀ g, cache ((name, key), label, idx, g.val) = some (bits g)) :
    (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run ((h, cache), log) =
      pure (treeStagesFieldResult K count (treeStagesDecode K count bits), (h, cache),
        log ++ treeSimHiddenLog (fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)) bits) := by
  rw [treeStages_element_table, simulateQ_map, StateT.run_map, treeSim_hiddenDraws_log,
    treeSim_hiddenDraws_cached prims D _ (fun _ => hidden) bits h cache cached]
  simp only [map_pure]

theorem treeStages_element_cached (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (key : HashOutput) (label idx count : ℕ) (bits : Fin (count * elementBits) → Bit)
    (h : HashCache C) (cache : HiddenCache C)
    (cached : ∀ g, cache ((name, key), label, idx, g.val) = some (bits g)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run (h, cache) =
      pure (treeStagesFieldResult K count (treeStagesDecode K count bits), (h, cache)) := by
  rw [treeStages_element_table, simulateQ_map, StateT.run_map,
    treeSim_hiddenDraws_cached prims D _ (fun _ => hidden) bits h cache cached]
  simp only [map_pure]

/-- Field shifts persist at second and subsequent holders. The cache invariant
is unchanged, and the padded tail is translated by zero. -/
theorem treeStages_element_cached_shift (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (key : HashOutput) (label idx count : ℕ) (delta : Fin count → E)
    (bits : Fin (count * elementBits) → Bit) (old : HiddenAddress C → Bit)
    (h : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (rel : TreeSimHiddenRel old c₁ c₂)
    (cached₁ : ∀ g, c₁ ((name, key), label, idx, g.val) = some (bits g))
    (cached₂ : ∀ g, c₂ ((name, key), label, idx, g.val) = some (treeStagesFieldShift K count delta bits g)) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run ((h, c₁), log))
      ((simulateQ (streamWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run (h, c₂))
      (fun a b => b.1 = a.1 + treeStagesFieldDelta count delta ∧ TreeSimStreamRel old a.2 b.2 ∧
        a.2.1 = (h, c₁) ∧ b.2 = (h, c₂)) := by
  rw [treeStages_element_cached_logged prims K D name hidden key label idx count bits h c₁ log cached₁,
    treeStages_element_cached prims K D name hidden key label idx count _ h c₂ cached₂]
  apply relTriple_pure_pure
  exact ⟨by rw [treeStagesFieldShift_decode, treeStagesFieldResult_add], ⟨rfl, rel⟩, rfl, rfl⟩

private theorem treeStages_sequenceFin_rel {α β σ₁ σ₂ : Type} {n : ℕ}
    (f₁ : Fin n → StateT σ₁ ProbComp α) (f₂ : Fin n → StateT σ₂ ProbComp β)
    (I : σ₁ → σ₂ → Prop) (R : Fin n → α → β → Prop)
    (step : ∀ i s₁ s₂, I s₁ s₂ →
      RelTriple ((f₁ i).run s₁) ((f₂ i).run s₂) (fun u v => R i u.1 v.1 ∧ I u.2 v.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : I s₁ s₂) :
    RelTriple ((Concrete.sequenceFin f₁).run s₁) ((Concrete.sequenceFin f₂).run s₂)
      (fun u v => (∀ i, R i (u.1 i) (v.1 i)) ∧ I u.2 v.2) := by
  induction n generalizing s₁ s₂ with
  | zero =>
    simp only [Concrete.sequenceFin, StateT.run_pure]
    exact relTriple_pure_pure ⟨fun i => Fin.elim0 i, hs⟩
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (step 0 s₁ s₂ hs)
    intro u v huv
    apply relTriple_bind (ih (fun i => f₁ i.succ) (fun i => f₂ i.succ)
      (fun i => R i.succ) (fun i => step i.succ) u.2 v.2 huv.2)
    intro us vs hus
    apply relTriple_pure_pure
    refine ⟨?_, hus.2⟩
    intro i
    cases i using Fin.cases with
    | zero => exact huv.1
    | succ i => exact hus.1 i

/-- Visible PRG reads couple over the common public cache and leave arbitrary
private caches untouched. This includes sampling a previously unread AES key. -/
theorem treeStages_visible_query (D : C.Coalition) (x : HiddenAddress C)
    (visible : ¬ Hidden D x.1.1) (h : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (hiddenQuery x)).run ((h, c₁), log))
      ((simulateQ (streamWorld prims D) (hiddenQuery x)).run (h, c₂))
      (fun a b => a.1 = b.1 ∧ a.2.1.1 = b.2.1 ∧ a.2.1.2 = c₁ ∧ b.2.2 = c₂) := by
  unfold hiddenQuery
  erw [simulateQ_spec_query, simulateQ_spec_query]
  simp only [treeSimLoggedWorld, streamWorld, visible, if_false, onHash, localAnswer,
    QueryImpl.add_apply_inr, StateT.run_mk, Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_refl _)
  rintro a b rfl
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every visible field block preserves an arbitrary private-cache invariant. -/
theorem treeStages_element_visible (D : C.Coalition) (name : KeyName C)
    (visible : ¬ Hidden D name) (key : HashOutput) (label idx count : ℕ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (pub : a.1.1 = b.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run b)
      (fun u v => u.1 = v.1 ∧ u.2.1.1 = v.2.1 ∧ u.2.1.2 = a.1.2 ∧ v.2.2 = b.2) := by
  rw [treeStages_element_table]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  unfold hiddenDraws
  rw [simulateQ_sequenceFin, simulateQ_sequenceFin]
  let J : TreeSimState C → (HashCache C × HiddenCache C) → Prop := fun u v =>
    u.1.1 = v.1 ∧ u.1.2 = a.1.2 ∧ v.2 = b.2
  apply relTriple_post_mono (treeStages_sequenceFin_rel _ _ J (fun _ u v => u = v) ?_ a b ⟨pub, rfl, rfl⟩)
  · intro u v huv
    exact ⟨by rw [funext huv.1], huv.2⟩
  · intro g u v huv
    rcases u with ⟨⟨h, c₁⟩, log⟩
    rcases v with ⟨h', c₂⟩
    obtain ⟨hh, hc₁, hc₂⟩ := huv
    dsimp at hh hc₁ hc₂
    subst h'
    apply relTriple_post_mono (treeStages_visible_query prims D ((name, key), label, idx, g.val)
      visible h c₁ c₂ log)
    intro u v huv
    exact ⟨huv.1, huv.2.1, huv.2.2.1.trans hc₁, huv.2.2.2.trans hc₂⟩

/-- A whole current block is either unread in both runs or completely cached
with the encoded field translation. Partial blocks are never assumed fresh. -/
def TreeStagesFieldBlock (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (c₁ c₂ : HiddenCache C) : Prop :=
  ∀ name key, Hidden D name →
    ((∀ g : Fin (count * elementBits), c₁ ((name, key), label, idx, g.val) = none) ∧
      (∀ g : Fin (count * elementBits), c₂ ((name, key), label, idx, g.val) = none)) ∨
    ∃ bits : Fin (count * elementBits) → Bit,
      (∀ g, c₁ ((name, key), label, idx, g.val) = some (bits g)) ∧
      (∀ g, c₂ ((name, key), label, idx, g.val) = some (treeStagesFieldShift K count (delta name) bits g))

/-- The only private addresses written by this PRSS invocation. -/
def TreeStagesFieldRegion (D : C.Coalition) (label idx count : ℕ) (x : HiddenAddress C) : Prop :=
  Hidden D x.1.1 ∧ x.2.1 = label ∧ x.2.2.1 = idx ∧ x.2.2.2 < count * elementBits

/-- Encoded blocks plus an exact frame for all other private addresses. -/
structure TreeStagesFieldCaches (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (base₁ base₂ c₁ c₂ : HiddenCache C) : Prop where
  blocks : TreeStagesFieldBlock K D label idx count delta c₁ c₂
  frame₁ : ∀ x, ¬ TreeStagesFieldRegion D label idx count x → c₁ x = base₁ x
  frame₂ : ∀ x, ¬ TreeStagesFieldRegion D label idx count x → c₂ x = base₂ x

/-- Fresh labels initialize the coherent-block invariant, including `count=0`. -/
theorem treeStages_fieldCaches_initial (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (c₁ c₂ : HiddenCache C)
    (fresh₁ : TreeSimFutureEmpty label c₁) (fresh₂ : TreeSimFutureEmpty label c₂) :
    TreeStagesFieldCaches K D label idx count delta c₁ c₂ c₁ c₂ := by
  refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl⟩
  intro name key hh
  exact Or.inl ⟨fun g => fresh₁ _ le_rfl, fun g => fresh₂ _ le_rfl⟩

/-- Filling one whole hidden block preserves all other encoded blocks and
all addresses outside this invocation. This is a deterministic cache lemma. -/
theorem treeStages_fieldCaches_fill (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (base₁ base₂ c₁ c₂ : HiddenCache C)
    (hc : TreeStagesFieldCaches K D label idx count delta base₁ base₂ c₁ c₂)
    (name : KeyName C) (key : HashOutput) (hidden : Hidden D name)
    (bits : Fin (count * elementBits) → Bit) :
    let addr := fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)
    TreeStagesFieldCaches K D label idx count delta base₁ base₂
      (cacheFin addr bits c₁) (cacheFin addr (treeStagesFieldShift K count (delta name) bits) c₂) := by
  dsimp only
  let addr := fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)
  have inj : Function.Injective addr := fun i j hij => Fin.ext (congrArg (fun x => x.2.2.2) hij)
  refine ⟨?_, ?_, ?_⟩
  · intro other otherKey hh
    by_cases he : (other, otherKey) = (name, key)
    · have hn := congrArg Prod.fst he
      have hk := congrArg Prod.snd he
      dsimp at hn hk
      subst other
      subst otherKey
      exact Or.inr ⟨bits, cacheFin_at addr inj bits c₁,
        cacheFin_at addr inj (treeStagesFieldShift K count (delta name) bits) c₂⟩
    · have miss : ∀ g : Fin (count * elementBits), ∀ i : Fin (count * elementBits),
          ((other, otherKey), label, idx, g.val) ≠ addr i := by
        intro g i h
        exact he (congrArg Prod.fst h)
      have h₁ := fun g => cacheFin_of_not_mem addr bits c₁ _ (miss g)
      have h₂ := fun g => cacheFin_of_not_mem addr (treeStagesFieldShift K count (delta name) bits) c₂ _ (miss g)
      change _ ∨ _
      simp only [← show addr = (fun g : Fin (count * elementBits) => ((name, key), label, idx, g.val)) from rfl, h₁, h₂]
      exact hc.blocks other otherKey hh
  · intro x hx
    rw [cacheFin_of_not_mem addr bits c₁ x (fun i he => hx (by
      rw [he]
      exact ⟨hidden, rfl, rfl, i.isLt⟩))]
    exact hc.frame₁ x hx
  · intro x hx
    rw [cacheFin_of_not_mem addr (treeStagesFieldShift K count (delta name) bits) c₂ x (fun i he => hx (by
      rw [he]
      exact ⟨hidden, rfl, rfl, i.isLt⟩))]
    exact hc.frame₂ x hx

/-- Public caches agree and the private field blocks carry their actual
encoded values. The log is unconstrained and remains the real query log. -/
def TreeStagesFieldRel (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (base₁ base₂ : HiddenCache C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  a.1.1 = b.1 ∧ TreeStagesFieldCaches K D label idx count delta base₁ base₂ a.1.2 b.2

/-- A local field-draw obligation, suitable for fresh, repeated and visible
blocks. The surrounding PRSS proof below handles traversal and restrictions. -/
def TreeStagesFieldDraws (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop) : Prop :=
  ∀ name key a b, J a b → RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run a)
    ((simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name key label idx count) (LocalSpec C)))).run b)
    (fun u v => v.1 = u.1 + treeStagesFieldDelta count (delta name) ∧ J u.2 v.2)

/-- Discharge the field-draw obligation from the coherent-block invariant:
first holders use the encoding bijection, later holders replay it, and visible
streams use their real AES values. No coupling premise remains. -/
theorem treeStages_fieldDraws_closed (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E)
    (visible : ∀ name, ¬ Hidden D name → delta name = 0) (base₁ base₂ : HiddenCache C) :
    TreeStagesFieldDraws prims K D label idx count delta
      (TreeStagesFieldRel K D label idx count delta base₁ base₂) := by
  intro name key a b hab
  rcases a with ⟨⟨h, c₁⟩, log⟩
  rcases b with ⟨h', c₂⟩
  obtain ⟨hpub, hc⟩ := hab
  dsimp at hpub
  subst h'
  by_cases hidden : Hidden D name
  · rcases hc.blocks name key hidden with ⟨fresh₁, fresh₂⟩ | ⟨bits, cached₁, cached₂⟩
    · apply relTriple_post_mono (treeStages_element_shift prims K D name hidden key label idx count (delta name)
        h h c₁ c₂ log (fun g hg => fresh₁ ⟨g, hg⟩) (fun g hg => fresh₂ ⟨g, hg⟩))
      intro u v huv
      obtain ⟨bits, hu, hv, hc₁, hc₂, hlog⟩ := huv
      refine ⟨?_, ?_⟩
      · rw [hu, hv, treeStagesFieldResult_add]
      · change u.2.1.1 = v.2.1 ∧ _
        rw [hc₁, hc₂]
        exact ⟨rfl, treeStages_fieldCaches_fill K D label idx count delta base₁ base₂ c₁ c₂ hc name key hidden bits⟩
    · rw [treeStages_element_cached_logged prims K D name hidden key label idx count bits h c₁ log cached₁,
        treeStages_element_cached prims K D name hidden key label idx count _ h c₂ cached₂]
      exact relTriple_pure_pure ⟨by rw [treeStagesFieldShift_decode, treeStagesFieldResult_add], rfl, hc⟩
  · apply relTriple_post_mono (treeStages_element_visible prims K D name hidden key label idx count
      ((h, c₁), log) (h, c₂) rfl)
    intro u v huv
    refine ⟨?_, huv.2.1, ?_⟩
    · rw [visible name hidden]
      have hz : treeStagesFieldDelta count (0 : Fin count → E) = 0 := by
        funext g
        simp [treeStagesFieldDelta]
      rw [hz, add_zero, huv.1]
    · rw [huv.2.2.1, huv.2.2.2]
      exact hc

private theorem treeStages_mapM_shift {ι α σ₁ σ₂ : Type}
    (f₁ : ι → StateT σ₁ ProbComp α) (f₂ : ι → StateT σ₂ ProbComp α)
    (shift : ι → α → α) (I : σ₁ → σ₂ → Prop) (xs : List ι)
    (step : ∀ i ∈ xs, ∀ s₁ s₂, I s₁ s₂ →
      RelTriple ((f₁ i).run s₁) ((f₂ i).run s₂)
        (fun u v => v.1 = shift i u.1 ∧ I u.2 v.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : I s₁ s₂) :
    RelTriple ((xs.mapM f₁).run s₁) ((xs.mapM f₂).run s₂)
      (fun u v => u.1.length = xs.length ∧ v.1 = List.zipWith shift xs u.1 ∧ I u.2 v.2) := by
  induction xs generalizing s₁ s₂ with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, hs⟩
  | cons i xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (step i (by simp) s₁ s₂ hs)
    intro u v huv
    apply relTriple_bind (ih (fun j hj => step j (by simp [hj])) u.2 v.2 huv.2)
    intro us vs hus
    exact relTriple_pure_pure ⟨by simp [hus.1], by simp [List.zipWith, huv.1, hus.2.1], hus.2.2⟩

private theorem treeStages_getD_zipWith {ι α : Type} (shift : ι → α → α)
    (xs : List ι) (ys : List α) (hlen : ys.length = xs.length)
    (i : ℕ) (hi : i < xs.length) (default : α) :
    (List.zipWith shift xs ys).getD i default = shift xs[i] (ys.getD i default) := by
  have hy : i < ys.length := by omega
  have hz : i < (List.zipWith shift xs ys).length := by simp [hlen, hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz,
    List.getElem?_eq_getElem hy, Option.getD_some, List.getElem_zipWith]

private theorem treeStages_mapM_ro {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (impl : QueryImpl (WorldSpec C) m) (xs : List α) (f : α → OracleComp (RoSpec C) β) :
    simulateQ impl (free (liftComp (xs.mapM f) (LocalSpec C))) =
      xs.mapM (fun x => simulateQ impl (free (liftComp (f x) (LocalSpec C)))) := by
  rw [keygen_liftComp_mapM]
  unfold free
  erw [simulateQ_list_mapM, simulateQ_list_mapM]

/-- Local restrictions of a field-table translation, with zero on unheld
terms and on the diagonal pair. -/
def treeStagesPrssFieldShift (ctx : Context C) (count : ℕ) (delta : KeyName C → Fin count → E) :
    PrssOutput C E :=
  (fun T => if ctx.self ∈ C.holders T then treeStagesFieldDelta count (delta (.term T)) else 0,
    fun j => if hj : j = ctx.self then 0 else
      treeStagesFieldDelta count (delta (.pair (C.pairOf ctx.self j (Ne.symm hj)))))

/-- The real field PRSS invocation, in its original term/pair query order.
The invariant can encode whole-block bijections instead of fixed XOR shifts. -/
theorem treeStages_prss_field_shift (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (draws : TreeStagesFieldDraws prims K D label idx count delta J)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hab : J a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run b)
      (fun u v => v.1 = u.1 + treeStagesPrssFieldShift ctx count delta ∧ J u.2 v.2) := by
  have terms : ∀ a b, J a b → RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (termDraws ctx (elementCodec K) label idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (termDraws ctx (elementCodec K) label idx count) (LocalSpec C)))).run b)
      (fun u v => u.1.length = C.terms.length ∧
        v.1 = List.zipWith (fun T r => r + (treeStagesPrssFieldShift ctx count delta).1 T) C.terms u.1 ∧ J u.2 v.2) := by
    intro a b hab
    unfold termDraws
    rw [treeStages_mapM_ro, treeStages_mapM_ro]
    apply treeStages_mapM_shift
    · intro T _ a b hab
      by_cases held : ctx.self ∈ C.holders T
      · simp only [if_pos held]
        simpa only [treeStagesPrssFieldShift, if_pos held] using draws (.term T) (ctx.prss.term T) a b hab
      · simp only [if_neg held, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨by simp [treeStagesPrssFieldShift, held], hab⟩
    · exact hab
  have pairs : ∀ a b, J a b → RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (pairDraws ctx (elementCodec K) label idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (pairDraws ctx (elementCodec K) label idx count) (LocalSpec C)))).run b)
      (fun u v => u.1.length = C.parties.length ∧
        v.1 = List.zipWith (fun j r => r + (treeStagesPrssFieldShift ctx count delta).2 j) C.parties u.1 ∧ J u.2 v.2) := by
    intro a b hab
    unfold pairDraws
    rw [treeStages_mapM_ro, treeStages_mapM_ro]
    apply treeStages_mapM_shift
    · intro j _ a b hab
      by_cases hj : j = ctx.self
      · simp only [dif_pos hj, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨by simp [treeStagesPrssFieldShift, hj], hab⟩
      · simp only [dif_neg hj]
        simpa only [treeStagesPrssFieldShift, dif_neg hj] using
          draws (.pair (C.pairOf ctx.self j (Ne.symm hj))) (ctx.prss.pair j) a b hab
    · exact hab
  unfold prssDraw
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind (terms a b hab)
  intro r₁ r₂ hr
  apply relTriple_bind (pairs r₁.2 r₂.2 hr.2.2)
  intro z₁ z₂ hz
  apply relTriple_pure_pure
  refine ⟨Prod.ext ?_ ?_, hz.2.2⟩
  · funext T
    dsimp only [Prod.fst, Prod.fst_add, Pi.add_apply]
    rw [hr.2.1, treeStages_getD_zipWith _ _ _ hr.1 _ (List.idxOf_lt_length_of_mem (mem_terms T))]
    simp only [List.getElem_idxOf]
  · funext j
    dsimp only [Prod.fst, Prod.snd, Prod.snd_add, Pi.add_apply]
    rw [hz.2.1, treeStages_getD_zipWith _ _ _ hz.1 j.val (by simpa [Committee.parties] using j.isLt)]
    simp [Committee.parties]

/-- Lift the field draw to the actual peer entry of ExtendMult. Saved
histories, absolute labels, products and continuations stay in the programs. -/
theorem treeStages_field_peer_entry {α : Type} (D : C.Coalition)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (label idx count : ℕ) (v₁ v₂ : ℕ → E) (st₁ st₂ : RunState C)
    (lab₁ : st₁.label = label) (lab₂ : st₂.label = label)
    (k₁ k₂ : Shares C E × RunState C → PartyM C E RealSpec α)
    (delta : KeyName C → Fin count → E)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (draws : TreeStagesFieldDraws prims K D label idx count delta J)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hab : J a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((((prssRandomness ctx₁ (elementCodec K) idx count >>= fun rnd =>
          reshare K ctx₁ (elementCodec K) rnd v₁ count).run st₁) >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((((prssRandomness ctx₂ (elementCodec K) idx count >>= fun rnd =>
          reshare K ctx₂ (elementCodec K) rnd v₂ count).run st₂) >>= k₂).run)))).run b)
      (fun u z => (∃ rnd,
        u.1 = treeSimPeerStep K ctx₁ (elementCodec K) rnd v₁ count st₁ k₁ ∧
        z.1 = treeSimPeerStep K ctx₂ (elementCodec K)
          (rnd + treeStagesPrssFieldShift ctx₁ count delta) v₂ count st₂ k₂) ∧ J u.2 z.2) := by
  rw [treeSim_peer_entry, treeSim_peer_entry, lab₁, lab₂,
    ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeStages_prss_field_shift prims K D ctx₁ label idx count delta J draws a b hab)
  intro u z hu
  exact ⟨⟨u.1, rfl, by rw [hu.1]⟩, hu.2⟩

/-- Recover the adaptive bit translation after a whole field invocation.
Only the current hidden region changes; this also handles nonlinear encodings. -/
def treeStagesFieldCacheDelta (D : C.Coalition) (label idx count : ℕ)
    (old : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C) (x : HiddenAddress C) : Bit :=
  if TreeStagesFieldRegion D label idx count x then
    match c₁ x, c₂ x with
    | some v, some w => w - v
    | _, _ => 0
  else old x

theorem treeStages_fieldCaches_related (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (old : HiddenAddress C → Bit)
    (base₁ base₂ c₁ c₂ : HiddenCache C)
    (hc : TreeStagesFieldCaches K D label idx count delta base₁ base₂ c₁ c₂)
    (hr : TreeSimHiddenRel old base₁ base₂) :
    TreeSimHiddenRel (treeStagesFieldCacheDelta D label idx count old c₁ c₂) c₁ c₂ := by
  intro x
  by_cases hx : TreeStagesFieldRegion D label idx count x
  · rcases x with ⟨⟨name, key⟩, lab, ix, pos⟩
    rcases hx with ⟨hh, hl, hi, hp⟩
    dsimp only at hl hi hp
    subst lab; subst ix
    have region : TreeStagesFieldRegion D label idx count ((name, key), label, idx, pos) :=
      ⟨hh, rfl, rfl, hp⟩
    rcases hc.blocks name key hh with hf | ⟨bits, h₁, h₂⟩
    · simp [treeStagesFieldCacheDelta, region, hf.1 ⟨pos, hp⟩, hf.2 ⟨pos, hp⟩]
    · simp [treeStagesFieldCacheDelta, region, h₁ ⟨pos, hp⟩, h₂ ⟨pos, hp⟩]
  · simp only [treeStagesFieldCacheDelta, if_neg hx, hc.frame₁ x hx, hc.frame₂ x hx]
    exact hr x

theorem treeStages_fieldCacheDelta_visible (D : C.Coalition) (label idx count : ℕ)
    (old : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C)
    (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0) :
    ∀ x, ¬ Hidden D x.1.1 → treeStagesFieldCacheDelta D label idx count old c₁ c₂ x = 0 := by
  intro x hx
  simp [treeStagesFieldCacheDelta, TreeStagesFieldRegion, hx, visible x hx]

theorem treeStages_fieldCacheDelta_future (D : C.Coalition) (label idx count : ℕ)
    (old : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C)
    (future : TreeSimFutureZero (label + 1) old) :
    TreeSimFutureZero (label + 1) (treeStagesFieldCacheDelta D label idx count old c₁ c₂) := by
  intro x hx
  have hn : ¬ TreeStagesFieldRegion D label idx count x := fun h => by
    have := h.2.1
    omega
  simp [treeStagesFieldCacheDelta, hn, future x hx]

theorem treeStages_fieldCaches_future (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E) (base₁ base₂ c₁ c₂ : HiddenCache C)
    (hc : TreeStagesFieldCaches K D label idx count delta base₁ base₂ c₁ c₂)
    (hf₁ : TreeSimFutureEmpty label base₁) (hf₂ : TreeSimFutureEmpty label base₂) :
    TreeSimFutureEmpty (label + 1) c₁ ∧ TreeSimFutureEmpty (label + 1) c₂ := by
  have outside : ∀ x : HiddenAddress C, label + 1 ≤ x.2.1 →
      ¬ TreeStagesFieldRegion D label idx count x := by
    intro x hx h
    have := h.2.1
    omega
  exact ⟨fun x hx => (hc.frame₁ x (outside x hx)).trans (hf₁ x (by omega)),
    fun x hx => (hc.frame₂ x (outside x hx)).trans (hf₂ x (by omega))⟩

/-- GS20 field shifts are zero on all corrupt-visible key names. -/
def treeStagesMaskDelta (D : C.Coalition) (count : ℕ)
    (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E) (name : KeyName C) : Fin count → E :=
  if Hidden D name then
    match name with
    | .parameter => 0
    | .term T => dt T
    | .pair p => dp p
  else 0

theorem treeStagesMaskDelta_visible (D : C.Coalition) (count : ℕ)
    (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E) :
    ∀ name, ¬ Hidden D name → treeStagesMaskDelta D count dt dp name = 0 := by
  intro name hh
  simp [treeStagesMaskDelta, hh]

private theorem treeStages_hidden_pair (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    Hidden D (.pair (C.pairOf i j h)) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  unfold Committee.pairOf
  split_ifs <;> simp [Hidden, and_comm]

/-- The actual field-table translation is precisely the GS20 local mask. -/
theorem treeStages_prssFieldShift_mask (D : C.Coalition) (ctx : Context C) (hi : ctx.self ∉ D.1)
    (count : ℕ) (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E) :
    treeStagesPrssFieldShift ctx count (treeStagesMaskDelta D count dt dp) =
      frandShare D count 0 0 dt dp ctx.self := by
  apply Prod.ext
  · funext T g
    by_cases held : ctx.self ∈ C.holders T
    · by_cases known : KnownTo D.1 T <;> by_cases hg : g < count <;>
        simp [treeStagesPrssFieldShift, treeStagesFieldDelta, treeStagesMaskDelta,
          frandShare, held, Hidden, known, hg]
    · simp [treeStagesPrssFieldShift, frandShare, held]
  · funext j g
    by_cases hj : j = ctx.self
    · subst j
      simp [treeStagesPrssFieldShift, frandShare]
    · by_cases hc : j ∈ D.1 <;> by_cases hg : g < count <;>
        simp [treeStagesPrssFieldShift, treeStagesFieldDelta, treeStagesMaskDelta,
          frandShare, hj, Ne.symm hj, treeStages_hidden_pair, hi, hc, hg]

/-- All honest field peer entries share the same coherent lazy cache.
Repeated holders reuse the encoded shift chosen at the first holder. -/
theorem treeStages_field_all_start {α : Type} (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (label idx count : ℕ) (v₁ v₂ : C.Party → ℕ → E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (draws : TreeStagesFieldDraws prims K D label idx count (treeStagesMaskDelta D count dt dp) J)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : J a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
        ((prssRandomness (ctx₁ i) (elementCodec K) idx count >>= fun rnd =>
          reshare K (ctx₁ i) (elementCodec K) rnd (v₁ i) count).run (st₁ i)) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
        ((prssRandomness (ctx₂ i) (elementCodec K) idx count >>= fun rnd =>
          reshare K (ctx₂ i) (elementCodec K) rnd (v₂ i) count).run (st₂ i)) >>= k₂ i))).run b)
      (fun u z => (∃ rnd, u.1 = treeSimExtendMultWaiting K D ctx₁ count rnd v₁ st₁ k₁ ∧
        z.1 = treeSimExtendMultWaiting K D ctx₂ count
          (fun i => rnd i + frandShare D count 0 0 dt dp i) v₂ st₂ k₂) ∧ J u.2 z.2) := by
  unfold startSteps
  rw [simulateQ_sequenceFin, simulateQ_sequenceFin]
  have step : ∀ i s t, J s t → RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (if i ∈ D.1 then pure (.done none) else worldRoles.honest (advance
          ((((prssRandomness (ctx₁ i) (elementCodec K) idx count >>= fun rnd =>
            reshare K (ctx₁ i) (elementCodec K) rnd (v₁ i) count).run (st₁ i)) >>= k₁ i).run)))).run s)
      ((simulateQ (streamWorld prims D)
        (if i ∈ D.1 then pure (.done none) else worldRoles.honest (advance
          ((((prssRandomness (ctx₂ i) (elementCodec K) idx count >>= fun rnd =>
            reshare K (ctx₂ i) (elementCodec K) rnd (v₂ i) count).run (st₂ i)) >>= k₂ i).run)))).run t)
      (fun u z => (∃ rnd,
        u.1 = treeSimExtendMultWaiting K D ctx₁ count (fun _ => rnd) v₁ st₁ k₁ i ∧
        z.1 = treeSimExtendMultWaiting K D ctx₂ count
          (fun j => rnd + frandShare D count 0 0 dt dp j) v₂ st₂ k₂ i) ∧ J u.2 z.2) := by
    intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨0, by simp [treeSimExtendMultWaiting, hi],
        by simp [treeSimExtendMultWaiting, hi]⟩, hst⟩
    · simp only [if_neg hi]
      apply relTriple_post_mono (treeStages_field_peer_entry prims K D (ctx₁ i) (ctx₂ i)
        ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi) label idx count (v₁ i) (v₂ i)
        (st₁ i) (st₂ i) (lab₁ i hi) (lab₂ i hi) (k₁ i) (k₂ i)
        (treeStagesMaskDelta D count dt dp) J draws s t hst)
      intro u z hu
      obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
      have hs : treeStagesPrssFieldShift (ctx₁ i) count (treeStagesMaskDelta D count dt dp) =
          frandShare D count 0 0 dt dp i := by
        rw [treeStages_prssFieldShift_mask D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
      refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
      · simpa only [treeSimExtendMultWaiting, if_neg hi] using hu
      · simpa only [treeSimExtendMultWaiting, if_neg hi, hs] using hz
  apply relTriple_post_mono (treeStages_sequenceFin_rel _ _ J
    (fun i x y => ∃ rnd,
      x = treeSimExtendMultWaiting K D ctx₁ count (fun _ => rnd) v₁ st₁ k₁ i ∧
      y = treeSimExtendMultWaiting K D ctx₂ count
        (fun j => rnd + frandShare D count 0 0 dt dp j) v₂ st₂ k₂ i) step a b h)
  intro u z hu
  choose rnd h₁ h₂ using hu.1
  exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩

/-- Optional prior outputs enter the field gadget in the driver's order.
An aborted party performs no PRSS draw; live holders still share one coherent
encoded field block. This is the entry needed after a selective abort. -/
theorem treeStages_field_partial_start {α : Type} (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (out : C.Party → Option Unit) (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (label idx count : ℕ) (v₁ v₂ : C.Party → ℕ → E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (draws : TreeStagesFieldDraws prims K D label idx count (treeStagesMaskDelta D count dt dp) J)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : J a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        ((prssRandomness (ctx₁ i) (elementCodec K) idx count >>= fun rnd =>
          reshare K (ctx₁ i) (elementCodec K) rnd (v₁ i) count).run (st₁ i)) >>= k₁ i) out)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        ((prssRandomness (ctx₂ i) (elementCodec K) idx count >>= fun rnd =>
          reshare K (ctx₂ i) (elementCodec K) rnd (v₂ i) count).run (st₂ i)) >>= k₂ i) out)).run b)
      (fun u z => (∃ rnd,
        u.1 = treeSimExtendMultPartial K D ctx₁ (fun i => (out i).isSome) count rnd v₁ st₁ k₁ ∧
        z.1 = treeSimExtendMultPartial K D ctx₂ (fun i => (out i).isSome) count
          (fun i => rnd i + frandShare D count 0 0 dt dp i) v₂ st₂ k₂) ∧ J u.2 z.2) := by
  let Q := fun i x y => ∃ rnd : PrssOutput C E,
    x = treeSimExtendMultPartial K D ctx₁ (fun i => (out i).isSome) count (fun _ => rnd) v₁ st₁ k₁ i ∧
    y = treeSimExtendMultPartial K D ctx₂ (fun i => (out i).isSome) count
      (fun j => rnd + frandShare D count 0 0 dt dp j) v₂ st₂ k₂ i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ out out J Q ?_ a b h)
  · intro u z hu
    choose rnd h₁ h₂ using hu.1
    exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩
  · intro i s t hst
    cases ho : out i with
    | none =>
      simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨0, ?_, ?_⟩, hst⟩ <;> simp [treeSimExtendMultPartial, ho]
    | some x =>
      cases x
      have hi : i ∉ D.1 := fun hi => by simpa [ho] using corrupt i hi
      simp only [treeSimResume]
      apply relTriple_post_mono (treeStages_field_peer_entry prims K D (ctx₁ i) (ctx₂ i)
        ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi) label idx count (v₁ i) (v₂ i)
        (st₁ i) (st₂ i) (lab₁ i hi) (lab₂ i hi) (k₁ i) (k₂ i)
        (treeStagesMaskDelta D count dt dp) J draws s t hst)
      intro u z hu
      obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
      have hs : treeStagesPrssFieldShift (ctx₁ i) count (treeStagesMaskDelta D count dt dp) =
          frandShare D count 0 0 dt dp i := by
        rw [treeStages_prssFieldShift_mask D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
      refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
      · simpa only [treeSimExtendMultPartial, ho, Option.isSome_some, if_true,
          treeSimExtendMultWaiting, if_neg hi] using hu
      · simpa only [treeSimExtendMultPartial, ho, Option.isSome_some, if_true,
          treeSimExtendMultWaiting, if_neg hi, hs] using hz

/-- Concrete ExtendMult data, with GS20 masks obtained from encoded field
blocks. This is the data type consumed by the frozen preservation theorem. -/
def treeStagesExtendMultData (D : C.Coalition) (T₀ : C.Term) (pivotParty : C.Party)
    (pivot : Pivot K D T₀ pivotParty) (δ : HiddenAddress C → Bit) (count : ℕ)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (rnd : C.Party → PrssOutput C E) (v₁ v₂ : C.Party → ℕ → E)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput) :
    TreeSimExtendMultData K D where
  δ := δ
  count := count
  ctx₁ := ctx₁
  ctx₂ := ctx₂
  rnd₁ := rnd
  rnd₂ := fun i => rnd i + frandShare D count 0 0
    (termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))
    (pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))) i
  v₁ := v₁
  v₂ := v₂
  st₁ := st₁
  st₂ := st₂
  k₁ := k₁
  k₂ := k₂
  self₁ := self₁
  self₂ := self₂
  T₀ := T₀
  pivotParty := pivotParty
  pivot := pivot
  masks := fun _ _ => rfl

/-- Actual field PRSS execution constructs the full GS20 boundary data. No
field-mask sampling or PRSS-coupling premise remains. Both private caches and
the adaptive shift are ready for the next absolute protocol label. -/
theorem treeStages_extendMult_start_data (D : C.Coalition) (T₀ : C.Term) (pivotParty : C.Party)
    (pivot : Pivot K D T₀ pivotParty) (old : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (label count : ℕ) (future : TreeSimFutureZero (label + 1) old)
    (v₁ v₂ : C.Party → ℕ → E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
        ((prssRandomness (ctx₁ i) (elementCodec K) 0 count >>= fun rnd =>
          reshare K (ctx₁ i) (elementCodec K) rnd (v₁ i) count).run (st₁ i)) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
        ((prssRandomness (ctx₂ i) (elementCodec K) 0 count >>= fun rnd =>
          reshare K (ctx₂ i) (elementCodec K) rnd (v₂ i) count).run (st₂ i)) >>= k₂ i))).run b)
      (fun u z => ∃ rnd δ,
        let d := treeStagesExtendMultData K D T₀ pivotParty pivot δ count ctx₁ ctx₂ self₁ self₂
          rnd v₁ v₂ st₁ st₂ k₁ k₂
        u.1 = treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        z.1 = treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧
        (∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) ∧ TreeSimFutureZero (label + 1) d.δ ∧
        TreeSimFutureEmpty (label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (label + 1) z.2.2) := by
  let dt := termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E)
  let dp := pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))
  let delta := treeStagesMaskDelta D count dt dp
  let J := TreeStagesFieldRel K D label 0 count delta a.1.2 b.2
  have fresh₂ := treeSim_futureEmpty_related fresh h.2
  have initial : J a b := ⟨h.1, treeStages_fieldCaches_initial K D label 0 count delta _ _ fresh fresh₂⟩
  have draws : TreeStagesFieldDraws prims K D label 0 count delta J :=
    treeStages_fieldDraws_closed prims K D label 0 count delta
      (treeStagesMaskDelta_visible D count dt dp) a.1.2 b.2
  apply relTriple_post_mono (treeStages_field_all_start prims K D ctx₁ ctx₂ self₁ self₂ keys
    label 0 count v₁ v₂ st₁ st₂ lab₁ lab₂ k₁ k₂ dt dp J draws a b initial)
  intro u z hu
  obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
  let δ := treeStagesFieldCacheDelta D label 0 count old u.2.1.2 z.2.2
  refine ⟨rnd, δ, hu, hz, ⟨hc.1, ?_⟩, ?_, ?_, ?_⟩
  · exact treeStages_fieldCaches_related K D label 0 count delta old _ _ _ _ hc.2 h.2
  · exact treeStages_fieldCacheDelta_visible D label 0 count old _ _ visible
  · exact treeStages_fieldCacheDelta_future D label 0 count old _ _ future
  · exact treeStages_fieldCaches_future K D label 0 count delta _ _ _ _ hc.2 fresh fresh₂

/-- Normalize only the ExtendMult projection, retaining the product values
and the original field draw. -/
theorem treeStages_extendMult_program (ctx : Context C) (products : List (Product C E))
    (count : ℕ) (hlen : products.length = count) :
    (realCheckGadgets (G := RealSpec) K ctx).extendMult products =
      (prssRandomness ctx (elementCodec K) 0 count >>= fun rnd =>
        reshare K ctx (elementCodec K) rnd (contextProductValues K ctx products) count) := by
  change (prssRandomness ctx (elementCodec K) 0 products.length >>= fun rnd =>
    reshare K ctx (elementCodec K) rnd (contextProductValues K ctx products) products.length) = _
  rw [hlen]

/-- The preceding construction applies to `realCheckGadgets.extendMult`
itself, with its real product list and saved continuation on each side. -/
theorem treeStages_extendMult_real_start (D : C.Coalition) (T₀ : C.Term) (pivotParty : C.Party)
    (pivot : Pivot K D T₀ pivotParty) (old : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (label count : ℕ) (future : TreeSimFutureZero (label + 1) old)
    (products₁ products₂ : C.Party → List (Product C E))
    (len₁ : ∀ i, (products₁ i).length = count) (len₂ : ∀ i, (products₂ i).length = count)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
        ((realCheckGadgets K (ctx₁ i)).extendMult (products₁ i)).run (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
        ((realCheckGadgets K (ctx₂ i)).extendMult (products₂ i)).run (st₂ i) >>= k₂ i))).run b)
      (fun u z => ∃ rnd δ,
        let d := treeStagesExtendMultData K D T₀ pivotParty pivot δ count ctx₁ ctx₂ self₁ self₂
          rnd (fun i => contextProductValues K (ctx₁ i) (products₁ i))
          (fun i => contextProductValues K (ctx₂ i) (products₂ i)) st₁ st₂ k₁ k₂
        u.1 = treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        z.1 = treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧
        (∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) ∧ TreeSimFutureZero (label + 1) d.δ ∧
        TreeSimFutureEmpty (label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (label + 1) z.2.2) := by
  have p₁ (i : C.Party) := treeStages_extendMult_program K (ctx₁ i) (products₁ i) count (len₁ i)
  have p₂ (i : C.Party) := treeStages_extendMult_program K (ctx₂ i) (products₂ i) count (len₂ i)
  simp only [p₁, p₂]
  exact treeStages_extendMult_start_data prims K D T₀ pivotParty pivot old visible ctx₁ ctx₂
      self₁ self₂ keys label count future
      (fun i => contextProductValues K (ctx₁ i) (products₁ i))
      (fun i => contextProductValues K (ctx₂ i) (products₂ i)) st₁ st₂ lab₁ lab₂ k₁ k₂ a b h fresh

/-- The GS20 cancellation survives a common set of earlier aborts. In
particular, a stopped honest party need not supply a current field mask. -/
theorem treeStages_extendMult_partial_view (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (live : C.Party → Bool) :
    treeSimRoundView D (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
      treeSimRoundView D (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
  rw [treeSim_extendMult_partial_view, treeSim_extendMult_partial_view, d.view K D]

/-- A field peer round after any earlier honest abort is fully coupled,
including the rushing adversary's real queries. Both sides finish with aborts;
no successful-continuation obligation is needed in this case. -/
theorem treeStages_extendMult_partial_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimExtendMultData K D)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel d.δ a b) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧
        u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_extendMult_partial_factor K D A _ _ live stopped,
    treeSim_extendMult_partial_factor K D A _ _ live stopped,
    treeStages_extendMult_partial_view K D d live]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b h)
  intro u z hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨by rw [hz.1], rfl, rfl, hz.2⟩

/-- The actual ExtendMult gadget is fully simulated after a selective
abort: PRSS entry, its shared cache, the rushing response, and abort propagation.
The successful-continuation certificates are not assumptions of this theorem. -/
theorem treeStages_extendMult_aborted (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (out : C.Party → Option Unit) (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (stopped : ∃ i, i ∉ D.1 ∧ out i = none)
    (label count : ℕ) (future : TreeSimFutureZero (label + 1) old)
    (products₁ products₂ : C.Party → List (Product C E))
    (len₁ : ∀ i, (products₁ i).length = count) (len₂ : ∀ i, (products₂ i).length = count)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      (((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        ((realCheckGadgets K (ctx₁ i)).extendMult (products₁ i)).run (st₁ i) >>= k₁ i) out)).run a) >>=
        fun u => (stepRound (treeSimRealRoles prims D) D A noFunctionality state u.1).run u.2)
      (((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        ((realCheckGadgets K (ctx₂ i)).extendMult (products₂ i)).run (st₂ i) >>= k₂ i) out)).run b) >>=
        fun z => (stepRound (treeSimIdealRoles prims D) D A noFunctionality state z.1).run z.2)
      (fun u z => u.1.1 = z.1.1 ∧
        u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
        ∃ δ, TreeSimStreamRel δ u.2 z.2 ∧
          (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero (label + 1) δ ∧
          TreeSimFutureEmpty (label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (label + 1) z.2.2) := by
  let v₁ := fun i => contextProductValues K (ctx₁ i) (products₁ i)
  let v₂ := fun i => contextProductValues K (ctx₂ i) (products₂ i)
  let dt := termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E)
  let dp := pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))
  let delta := treeStagesMaskDelta D count dt dp
  let J := TreeStagesFieldRel K D label 0 count delta a.1.2 b.2
  have fresh₂ := treeSim_futureEmpty_related fresh h.2
  have initial : J a b := ⟨h.1, treeStages_fieldCaches_initial K D label 0 count delta _ _ fresh fresh₂⟩
  have draws : TreeStagesFieldDraws prims K D label 0 count delta J :=
    treeStages_fieldDraws_closed prims K D label 0 count delta
      (treeStagesMaskDelta_visible D count dt dp) a.1.2 b.2
  have p₁ (i : C.Party) := treeStages_extendMult_program K (ctx₁ i) (products₁ i) count (len₁ i)
  have p₂ (i : C.Party) := treeStages_extendMult_program K (ctx₂ i) (products₂ i) count (len₂ i)
  simp only [p₁, p₂]
  apply relTriple_bind (treeStages_field_partial_start prims K D ctx₁ ctx₂ self₁ self₂ keys
    out corrupt label 0 count v₁ v₂ st₁ st₂ lab₁ lab₂ k₁ k₂ dt dp J draws a b initial)
  intro u z hu
  obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
  let δ := treeStagesFieldCacheDelta D label 0 count old u.2.1.2 z.2.2
  let d := treeStagesExtendMultData K D T₀ pivotParty pivot δ count ctx₁ ctx₂ self₁ self₂
    rnd v₁ v₂ st₁ st₂ k₁ k₂
  have hstream : TreeSimStreamRel d.δ u.2 z.2 :=
    ⟨hc.1, treeStages_fieldCaches_related K D label 0 count delta old _ _ _ _ hc.2 h.2⟩
  have hf := treeStages_fieldCaches_future K D label 0 count delta _ _ _ _ hc.2 fresh fresh₂
  have stopped' : ∃ i, i ∉ D.1 ∧ (out i).isSome ≠ true := by
    obtain ⟨i, hi, ho⟩ := stopped
    exact ⟨i, hi, by simp [ho]⟩
  rw [hu, hz]
  apply relTriple_post_mono (treeStages_extendMult_partial_round prims K D A d
    (fun i => (out i).isSome) stopped' state u.2 z.2 hstream)
  intro r t hr
  refine ⟨hr.1, hr.2.1, hr.2.2.1, δ, hr.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · exact treeStages_fieldCacheDelta_visible D label 0 count old _ _ visible
  · exact treeStages_fieldCacheDelta_future D label 0 count old _ _ future
  · rw [hr.2.2.2.2.1]
    exact hf.1
  · rw [hr.2.2.2.2.2]
    exact hf.2

/-- Coin entry after arbitrary recorded gadget outputs. Only program shapes
are fields; its PRSS coupling is proved below. The previous translation can be
an adaptive encoded field translation, not only a fixed bit-block shift. -/
structure TreeStagesCoinNext {β : Type} (D : C.Coalition)
    (k₁ : C.Party → β → PartyM C E RealSpec TreeOutput)
    (k₂ : C.Party → β → PartyM C E RealSpec TreeOutput)
    (out₁ : C.Party → Option β) (out₂ : C.Party → Option β) where
  label : ℕ
  count : ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label
  live : C.Party → Bool
  x₁ : C.Party → β
  x₂ : C.Party → β
  shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none
  shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none
  next₁ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput
  next₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → live i = true →
    k₁ i (x₁ i) = ((realCheckGadgets K (ctx₁ i)).coin count).run (st₁ i) >>= next₁ i
  program₂ : ∀ i, i ∉ D.1 → live i = true →
    k₂ i (x₂ i) = ((realCheckGadgets K (ctx₂ i)).coin count).run (st₂ i) >>= next₂ i

/-- The actual Coin PRSS draws preserve an adaptive previous translation.
Successful field outputs are retained in the saved next continuations. -/
theorem TreeStagesCoinNext.coupling {β : Type} (D : C.Coalition)
    (k₁ : C.Party → β → PartyM C E RealSpec TreeOutput)
    (k₂ : C.Party → β → PartyM C E RealSpec TreeOutput)
    (out₁ : C.Party → Option β) (out₂ : C.Party → Option β)
    (n : TreeStagesCoinNext K D k₁ k₂ out₁ out₂) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (future : TreeSimFutureZero n.label δ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => (∃ rnd,
        u.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
        z.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂) ∧ TreeSimStreamRel δ u.2 z.2) := by
  let Q := fun i (u z : Step C E RealSpec TreeOutput) => ∃ rnd,
    u = treeSimCoinPartial K D n.live n.count (fun _ => rnd) n.st₁ n.next₁ i ∧
    z = treeSimCoinPartial K D n.live n.count (fun _ => rnd) n.st₂ n.next₂ i
  have step : ∀ i s t, TreeSimStreamRel δ s t →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) (out₁ i)))).run s)
        ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) (out₂ i)))).run t)
        (fun u z => Q i u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro i s t hst
    rw [n.shape₁ i, n.shape₂ i]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨0, by simp [treeSimCoinPartial, treeSimCoinWaiting, hi],
        by simp [treeSimCoinPartial, treeSimCoinWaiting, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : n.live i = true
      · simp only [if_pos hl, treeSimResume, n.program₁ i hi hl, n.program₂ i hi hl]
        apply relTriple_post_mono (treeSim_coin_entry_mixed prims K D δ visible (n.ctx₁ i) (n.ctx₂ i)
          ((n.self₁ i hi).trans (n.self₂ i hi).symm) (n.keys i hi) n.count (n.st₁ i) (n.st₂ i)
          ((n.lab₁ i hi).trans (n.lab₂ i hi).symm) (by rw [n.lab₁ i hi]; exact future)
          (n.next₁ i) (n.next₂ i) s t hst)
        intro u z hu
        obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
        refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
        · rw [hu]
          simp only [treeSimCoinPartial, treeSimCoinWaiting, if_pos hl, if_neg hi]
          exact treeSim_coinStep_context K _ _ (n.self₁ i hi) rnd n.count (n.st₁ i) (n.next₁ i)
        · rw [hz]
          simp only [treeSimCoinPartial, treeSimCoinWaiting, if_pos hl, if_neg hi]
          exact treeSim_coinStep_context K _ _ (n.self₂ i hi) rnd n.count (n.st₂ i) (n.next₂ i)
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨0, by simp [treeSimCoinPartial, hl],
          by simp [treeSimCoinPartial, hl]⟩, hst⟩
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D k₁ k₂ out₁ out₂ (TreeSimStreamRel δ) Q step a b hc)
  intro u z hu
  choose rnd h₁ h₂ using hu.1
  exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩

private theorem treeStages_state_sequenceFin_preserves {α σ β : Type} {n : ℕ}
    (q : σ → β) (f : Fin n → StateT σ ProbComp α)
    (step : ∀ i s r, r ∈ support ((f i).run s) → q r.2 = q s)
    (s : σ) (r : (Fin n → α) × σ)
    (hr : r ∈ support ((Concrete.sequenceFin f).run s)) : q r.2 = q s := by
  induction n generalizing s with
  | zero =>
    have heq : r = (Fin.elim0, s) := by simpa [Concrete.sequenceFin] using hr
    subst r
    rfl
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact (ih (fun i => f i.succ) (fun i => step i.succ) u.2 v hv).trans (step 0 s u hu)

/-- Coin resumption writes only its current label, independently of the
type of the earlier gadget's recorded output. -/
theorem treeStages_coin_resume_frame {α β : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (label count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → β → PartyM C E RealSpec α)
    (next : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option β) (x : C.Party → β) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = label)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= next i)
    (s : HashCache C × HiddenCache C) (r : (C.Party → Step C E RealSpec α) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame label s.2 r.2.2 := by
  unfold treeSimResumeAll at hr
  rw [free_sequenceFin, simulateQ_sequenceFin] at hr
  intro y hy
  apply treeStages_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 y) _ _ s r hr
  intro i a b hb
  rw [shape i] at hb
  by_cases hi : i ∈ D.1
  · simp [hi, treeSimResume, free_pure] at hb
    subst b
    rfl
  · simp only [if_neg hi] at hb
    by_cases hl : live i = true
    · simp only [if_pos hl, treeSimResume, program i hi hl] at hb
      have h := treeSim_coin_entry_frame prims K D (ctx i) count (st i) (next i) a b hb
      rw [lab i hi hl] at h
      exact h y hy
    · simp [hl, treeSimResume, free_pure] at hb
      subst b
      rfl

/-- Coin preserves emptiness at every later label on both sides of the
field-mask coupling. The real query log is retained throughout. -/
theorem TreeStagesCoinNext.coupling_fresh {β : Type} (D : C.Coalition)
    (k₁ k₂ : C.Party → β → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option β) (n : TreeStagesCoinNext K D k₁ k₂ out₁ out₂)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero n.label δ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b)
    (fresh : TreeSimFutureEmpty n.label a.1.2) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeSimCacheFrame n.label a.1.2 u.2.1.2 ∧
        TreeSimCacheFrame n.label b.2 z.2.2 ∧
        TreeSimFutureEmpty (n.label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (n.label + 1) z.2.2 ∧
        TreeSimFutureZero (n.label + 1) δ ∧ (∃ rnd,
          u.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
          z.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂) ∧
        TreeSimStreamRel δ u.2 z.2) := by
  apply relTriple_post_mono (treeSim_relTriple_support
    (n.coupling prims K D k₁ k₂ out₁ out₂ δ visible future a b hc))
  intro u z h
  have f₁ : TreeSimCacheFrame n.label a.1.2 u.2.1.2 := by
    apply treeStages_coin_resume_frame prims K D n.ctx₁ n.label n.count n.st₁ k₁ n.next₁
      out₁ n.x₁ n.live (fun i hi _ => n.lab₁ i hi) n.shape₁ n.program₁ a.1 (u.1, u.2.1)
    rw [← treeSimLoggedWorld_erase prims D _ a.1 a.2, support_map]
    exact ⟨u, h.2.1, rfl⟩
  have f₂ := treeStages_coin_resume_frame prims K D n.ctx₂ n.label n.count n.st₂ k₂ n.next₂
    out₂ n.x₂ n.live (fun i hi _ => n.lab₂ i hi) n.shape₂ n.program₂ b z h.2.2
  refine ⟨f₁, f₂, treeSim_futureEmpty_after fresh f₁,
    treeSim_futureEmpty_after (treeSim_futureEmpty_related fresh hc.2) f₂, ?_, h.1⟩
  intro x hx
  exact future x (by omega)

/-- Defaulted outputs retain the next absolute label even at aborted
positions; the default is used only to describe an inactive continuation. -/
theorem treeStages_extendMult_recorded_label {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    ((treeSimExtendMultOutputs K D ctx count rnd v st k sent i).getD (0, nextLabel (st i))).2.label =
      (st i).label + 1 := by
  unfold treeSimExtendMultOutputs treeSimExtendMultReturn
  split_ifs <;> rfl

private theorem treeStages_option_shape {β : Type} (x : Option β) (fallback : β) :
    x = if x.isSome then some (x.getD fallback) else none := by
  cases x <;> rfl

/-- Construct the Coin successor from the actual optional ExtendMult returns.
The two returned histories remain distinct and are carried into their own
continuations; only their success bits and labels are synchronized. -/
def treeStages_extendMult_coinNext (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (sent : C.Party → Mail C E) (label count : ℕ)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (lab₁ : ∀ i, i ∉ D.1 → (d.st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (d.st₂ i).label = label)
    (next₁ next₂ : C.Party → (Shares C E × RunState C) → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i x, d.k₁ i x = ((realCheckGadgets K (d.ctx₁ i)).coin count).run x.2 >>= next₁ i x)
    (program₂ : ∀ i x, d.k₂ i x = ((realCheckGadgets K (d.ctx₂ i)).coin count).run x.2 >>= next₂ i x) :
    TreeStagesCoinNext K D d.k₁ d.k₂
      (treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)
      (treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent) := by
  let out₁ := treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
  let out₂ := treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
  let x₁ := fun i => (out₁ i).getD (0, nextLabel (d.st₁ i))
  let x₂ := fun i => (out₂ i).getD (0, nextLabel (d.st₂ i))
  have live : ∀ i, (out₁ i).isSome = (out₂ i).isSome := by
    intro i
    have h := d.outputs K D sent i
    change Option.Rel _ (out₁ i) (out₂ i) at h
    generalize out₁ i = left at h ⊢
    generalize out₂ i = right at h ⊢
    cases h <;> rfl
  refine {
    label := label + 1
    count := count
    ctx₁ := d.ctx₁
    ctx₂ := d.ctx₂
    self₁ := d.self₁
    self₂ := d.self₂
    keys := keys
    st₁ := fun i => (x₁ i).2
    st₂ := fun i => (x₂ i).2
    lab₁ := ?_
    lab₂ := ?_
    live := fun i => (out₁ i).isSome
    x₁ := x₁
    x₂ := x₂
    shape₁ := ?_
    shape₂ := ?_
    next₁ := fun i => next₁ i (x₁ i)
    next₂ := fun i => next₂ i (x₂ i)
    program₁ := fun i _ _ => program₁ i (x₁ i)
    program₂ := fun i _ _ => program₂ i (x₂ i) }
  · intro i hi
    exact (treeStages_extendMult_recorded_label K D _ _ _ _ _ _ sent i).trans (congrArg (· + 1) (lab₁ i hi))
  · intro i hi
    exact (treeStages_extendMult_recorded_label K D _ _ _ _ _ _ sent i).trans (congrArg (· + 1) (lab₂ i hi))
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₁, treeSimExtendMultOutputs, hi]
    · rw [if_neg hi]
      exact treeStages_option_shape (out₁ i) _
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₂, treeSimExtendMultOutputs, hi]
    · rw [if_neg hi, live i]
      exact treeStages_option_shape (out₂ i) _

/-- A successful ExtendMult round enters the actual next Coin round.
The relation contains the rushing reply, masks, exact recorded states and
saved continuations, and also covers partial success after this exchange. -/
theorem treeStages_extendMult_coin_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimExtendMultData K D)
    (label count : ℕ) (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0)
    (future : TreeSimFutureZero (label + 1) d.δ)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (lab₁ : ∀ i, i ∉ D.1 → (d.st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (d.st₂ i).label = label)
    (next₁ next₂ : C.Party → (Shares C E × RunState C) → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i x, d.k₁ i x = ((realCheckGadgets K (d.ctx₁ i)).coin count).run x.2 >>= next₁ i x)
    (program₂ : ∀ i x, d.k₂ i x = ((realCheckGadgets K (d.ctx₂ i)).coin count).run x.2 >>= next₂ i x)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => ∃ sent rnd,
        let n := treeStages_extendMult_coinNext K D d sent label count keys lab₁ lab₂ next₁ next₂ program₁ program₂
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
        z.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ TreeSimFutureZero (label + 2) d.δ ∧
        TreeSimFutureEmpty (label + 2) u.2.1.2 ∧ TreeSimFutureEmpty (label + 2) z.2.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_extendMult_resume_factor, treeSim_extendMult_resume_factor, d.view K D]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b h)
  intro r₁ r₂ hr
  rw [hr.1]
  let n := treeStages_extendMult_coinNext K D d r₂.1.2 label count keys lab₁ lab₂ next₁ next₂ program₁ program₂
  have fresh' : TreeSimFutureEmpty n.label r₁.2.1.2 := by
    rw [hr.2.2.1]
    exact fresh
  apply relTriple_bind (n.coupling_fresh prims K D d.k₁ d.k₂ _ _ d.δ visible future r₁.2 r₂.2 hr.2.1 fresh')
  intro u z hz
  obtain ⟨_, _, hf₁, hf₂, hδ, ⟨rnd, hu, hz⟩, hc⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨r₂.1.2, rnd, rfl, rfl, rfl, hu, hz, hc, hδ, hf₁, hf₂⟩

/-- The hashes and challenge rejection loop after Coin, with the tag and
absolute label captured before Coin changes the run state. -/
def treeStagesChallengeTail {α : Type} (tag : ℕ) (label : ℕ)
    (body : E × RunState C → PartyM C E RealSpec α)
    (r : List E × RunState C) : PartyM C E RealSpec α := do
  let key ← oracleStep (hashQuery (.coinKey tag label
    (r.1.flatMap fun v => List.ofFn (K.encode v))))
  let some value ← oracleStep (findChallenge K key challengeTries 0) | failure
  body (value, r.2)

theorem treeStages_challenge_prefix {α : Type} (ctx : Context C) (st : RunState C)
    (body : E × RunState C → PartyM C E RealSpec α) :
    (challenge K (realCheckGadgets K ctx)).run st >>= body =
      ((realCheckGadgets K ctx).coin 1).run st >>=
        treeStagesChallengeTail K st.tag st.label body := by
  unfold treeStagesChallengeTail
  simp only [challenge, coinKey, StateT.run_bind,
    StateT.run_get, StateT.run_lift, StateT.run_pure, pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) (funext fun vals => ?_)
  refine congrArg (_ >>= ·) (funext fun key => ?_)
  refine congrArg (_ >>= ·) (funext fun r => ?_)
  cases r <;> simp [StateT.run_lift]

private theorem treeStages_onHash_pure {α : Type} (a : α) :
    onHash (C := C) (pure a) = pure a := by
  apply StateT.ext
  intro s
  simp [onHash]

private theorem treeStages_onHash_bind {α β : Type} (p : StateT (HashCache C) ProbComp α)
    (k : α → StateT (HashCache C) ProbComp β) :
    onHash (p >>= k) = onHash p >>= fun a => onHash (k a) := by
  apply StateT.ext
  intro s
  simp [onHash, StateT.run_bind, map_bind, bind_map_left]

/-- Challenge rejection sampling uses only the public hash cache, including
cache entries installed by the dealer before emulation begins. -/
theorem treeStages_findChallenge_onHash (D : C.Coalition) (key : HashOutput) (tries index : ℕ) :
    ∃ m : StateT (HashCache C) ProbComp (Option E),
      simulateQ (streamWorld prims D)
        (free (liftComp (findChallenge K key tries index) (LocalSpec C))) = onHash m := by
  have single : ∀ q : Query C, simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C))) = onHash (hashAnswer prims q) := by
    intro q
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  induction tries generalizing index with
  | zero => exact ⟨pure none, by simp [findChallenge, liftComp_pure, free_pure, treeStages_onHash_pure]⟩
  | succ tries ih =>
    obtain ⟨m, hm⟩ := ih (index + 1)
    refine ⟨hashAnswer prims (.expand key index) >>= fun h =>
      if elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1 then pure (some (elementOfHash K h)) else m, ?_⟩
    simp only [findChallenge, liftComp_bind, free_bind, simulateQ_bind, single, treeStages_onHash_bind]
    congr 1
    funext h
    cases hd : Classical.propDecidable (elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1) with
    | isTrue ha => simp [ha, liftComp_pure, free_pure, treeStages_onHash_pure]
    | isFalse ha => simpa only [if_neg ha] using hm

theorem treeStages_challengeQuery_onHash (D : C.Coalition) (tag label : ℕ) (values : List E) :
    ∃ m : StateT (HashCache C) ProbComp (Option E),
      simulateQ (streamWorld prims D)
        (free (liftComp (challengeQuery K tag label values) (LocalSpec C))) = onHash m := by
  choose m hm using fun key => treeStages_findChallenge_onHash prims K D key challengeTries 0
  refine ⟨hashAnswer prims (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))) >>= m, ?_⟩
  have single : ∀ q : Query C, simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C))) = onHash (hashAnswer prims q) := by
    intro q
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  simp only [challengeQuery, liftComp_bind, free_bind, simulateQ_bind, single, treeStages_onHash_bind]
  congr 1
  funext key
  exact hm key

/-- Exact factorization of the saved challenge continuation. Its hashes are
executed before the remaining check program, in the original operator order. -/
theorem treeStages_challenge_tail_factor {α : Type} (tag label : ℕ) (values : List E)
    (st : RunState C) (body : E × RunState C → PartyM C E RealSpec α) :
    free (advance (treeStagesChallengeTail K tag label body (values, st)).run) =
      (free (liftComp (challengeQuery K tag label values) (LocalSpec C)) >>= fun r =>
        free (treeSimResume (fun value => body (value, st)) r)) := by
  unfold treeStagesChallengeTail challengeQuery
  simp only [oracleStep_bind, advance_oracleStep_bind, free_bind, liftComp_bind, bind_assoc]
  refine congrArg (_ >>= ·) (funext fun key => ?_)
  refine congrArg (_ >>= ·) (funext fun r => ?_)
  cases r <;> rfl

/-- Hashing and rejection in the actual challenge preserve the stream
relation without a freshness premise. Only the subsequent check body needs a
local continuation proof, at the common challenge actually returned. -/
theorem treeStages_challenge_tail_rel (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (tag label : ℕ) (values : List E) (st₁ st₂ : RunState C)
    (body₁ body₂ : E × RunState C → PartyM C E RealSpec TreeOutput)
    (R : (Step C E RealSpec TreeOutput × TreeSimState C) →
      (Step C E RealSpec TreeOutput × (HashCache C × HiddenCache C)) → Prop)
    (P : HiddenCache C → HiddenCache C → Prop)
    (abort : ∀ a b, TreeSimStreamRel δ a b → P a.1.2 b.2 → R (.done none, a) (.done none, b))
    (next : ∀ r a b, TreeSimStreamRel δ a b → P a.1.2 b.2 →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (body₁ (r, st₁)).run))).run a)
        ((simulateQ (streamWorld prims D) (free (advance (body₂ (r, st₂)).run))).run b) R)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) (hp : P a.1.2 b.2) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (advance (treeStagesChallengeTail K tag label body₁ (values, st₁)).run))).run a)
      ((simulateQ (streamWorld prims D)
        (free (advance (treeStagesChallengeTail K tag label body₂ (values, st₂)).run))).run b) R := by
  rw [treeStages_challenge_tail_factor, treeStages_challenge_tail_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  obtain ⟨m, hm⟩ := treeStages_challengeQuery_onHash prims K D tag label values
  apply relTriple_bind (treeSim_onHash_coupling prims D _ m hm δ a b h)
  intro u z hu
  have hp' : P u.2.1.2 z.2.2 := by
    rw [hu.2.2.1, hu.2.2.2]
    exact hp
  rw [hu.1]
  cases hr : z.1 with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (abort u.2 z.2 hu.2.1 hp')
  | some r => exact next r u.2 z.2 hu.2.1 hp'

/-- Discharge the frozen Coin closure's actual challenge hashes. Its remaining
obligations are the subsequent check bodies and deterministic invariant closure;
there is no query-freshness or challenge-coupling premise. -/
def treeStages_challenge_coinClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (δ : HiddenAddress C → Bit) (st₁ st₂ : C.Party → RunState C)
    (tag label : C.Party → ℕ)
    (body₁ body₂ : C.Party → E × RunState C → PartyM C E RealSpec TreeOutput)
    (initial₁ initial₂ : HiddenCache C) (P : HiddenCache C → HiddenCache C → Prop)
    (initial : P initial₁ initial₂)
    (Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop)
    (abort : ∀ i, Q i (.done none) (.done none))
    (next : ∀ i r a b, TreeSimStreamRel δ a b → P a.1.2 b.2 →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D)
        (free (advance (body₁ i (r, nextLabel (st₁ i))).run))).run a)
        ((simulateQ (streamWorld prims D)
        (free (advance (body₂ i (r, nextLabel (st₂ i))).run))).run b)
        (fun u z => Q i u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ P u.2.1.2 z.2.2))
    (finish : ∀ state s₁ s₂ a b, (∀ i, Q i (s₁ i) (s₂ i)) →
      TreeSimStreamRel δ a b → P a.1.2 b.2 → Bad a ∨ Inv ((state, s₁), a) ((state, s₂), b)) :
    TreeSimCoinClosure prims D A Bad Inv δ st₁ st₂
      (fun i => treeStagesChallengeTail K (tag i) (label i) (body₁ i))
      (fun i => treeStagesChallengeTail K (tag i) (label i) (body₂ i)) initial₁ initial₂ where
  J a b := TreeSimStreamRel δ a b ∧ P a.1.2 b.2
  Q := Q
  entry := by
    intro a b h h₁ h₂
    exact ⟨h, by simpa only [h₁, h₂] using initial⟩
  abort := abort
  continues := by
    intro i vals a b h
    exact treeStages_challenge_tail_rel prims K D δ (tag i) (label i) vals
      (nextLabel (st₁ i)) (nextLabel (st₂ i)) (body₁ i) (body₂ i) _ P
      (fun a b hs hp => ⟨abort i, hs, hp⟩) (next i) a b h.1 h.2
  exit := fun state s₁ s₂ a b hq h => finish state s₁ s₂ a b hq h.1 h.2

/-- A concrete check reduction step: real ExtendMult followed by the real
challenge. The arbitrary remaining check code is saved in `body₁` and `body₂`. -/
structure TreeStagesExtendMultChallenge (D : C.Coalition) where
  T₀ : C.Term
  pivotParty : C.Party
  pivot : Pivot K D T₀ pivotParty
  label : ℕ
  count : ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  products₁ : C.Party → List (Product C E)
  products₂ : C.Party → List (Product C E)
  len₁ : ∀ i, (products₁ i).length = count
  len₂ : ∀ i, (products₂ i).length = count
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label
  body₁ : C.Party → (Shares C E × RunState C) → E × RunState C → PartyM C E RealSpec TreeOutput
  body₂ : C.Party → (Shares C E × RunState C) → E × RunState C → PartyM C E RealSpec TreeOutput

def TreeStagesExtendMultChallenge.k₁ (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (i : C.Party) (x : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K (p.ctx₁ i))).run x.2 >>= p.body₁ i x

def TreeStagesExtendMultChallenge.k₂ (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (i : C.Party) (x : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K (p.ctx₂ i))).run x.2 >>= p.body₂ i x

def TreeStagesExtendMultChallenge.next₁ (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (i : C.Party) (x : Shares C E × RunState C) : List E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K x.2.tag x.2.label (p.body₁ i x)

def TreeStagesExtendMultChallenge.next₂ (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (i : C.Party) (x : Shares C E × RunState C) : List E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K x.2.tag x.2.label (p.body₂ i x)

def TreeStagesExtendMultChallenge.data (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) : TreeSimExtendMultData K D :=
  treeStagesExtendMultData K D p.T₀ p.pivotParty p.pivot δ p.count p.ctx₁ p.ctx₂ p.self₁ p.self₂ rnd
    (fun i => contextProductValues K (p.ctx₁ i) (p.products₁ i))
    (fun i => contextProductValues K (p.ctx₂ i) (p.products₂ i)) p.st₁ p.st₂ (p.k₁ K D) (p.k₂ K D)

def TreeStagesExtendMultChallenge.coinNext (D : C.Coalition) (p : TreeStagesExtendMultChallenge K D)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit) (sent : C.Party → Mail C E) :
    TreeStagesCoinNext K D (p.k₁ K D) (p.k₂ K D)
      (treeSimExtendMultOutputs K D p.ctx₁ p.count rnd
        (fun i => contextProductValues K (p.ctx₁ i) (p.products₁ i)) p.st₁ (p.k₁ K D) sent)
      (treeSimExtendMultOutputs K D p.ctx₂ p.count (p.data K D rnd δ).rnd₂
        (fun i => contextProductValues K (p.ctx₂ i) (p.products₂ i)) p.st₂ (p.k₂ K D) sent) :=
  treeStages_extendMult_coinNext K D (p.data K D rnd δ) sent p.label 1 p.keys p.lab₁ p.lab₂
    (p.next₁ K D) (p.next₂ K D)
    (fun i x => treeStages_challenge_prefix K (p.ctx₁ i) x.2 (p.body₁ i x))
    (fun i x => treeStages_challenge_prefix K (p.ctx₂ i) x.2 (p.body₂ i x))

/-- The complete real reduction transition, from before its field PRSS
through the rushing ExtendMult exchange to the next Coin waiting state.
There is no continuation-coupling hypothesis. Actual product values and
recorded field outputs are retained in the constructed successor. -/
theorem TreeStagesExtendMultChallenge.coupling (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesExtendMultChallenge K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 1) old)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty p.label a.1.2) :
    RelTriple
      (((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
        ((realCheckGadgets K (p.ctx₁ i)).extendMult (p.products₁ i)).run (p.st₁ i) >>= p.k₁ K D i))).run a) >>=
        fun u => (stepRound (treeSimRealRoles prims D) D A noFunctionality state u.1).run u.2)
      (((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
        ((realCheckGadgets K (p.ctx₂ i)).extendMult (p.products₂ i)).run (p.st₂ i) >>= p.k₂ K D i))).run b) >>=
        fun z => (stepRound (treeSimIdealRoles prims D) D A noFunctionality state z.1).run z.2)
      (fun u z => ∃ rnd δ sent coinRnd,
        let n := p.coinNext K D rnd δ sent
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D n.live n.count coinRnd n.st₁ n.next₁ ∧
        z.1.2.1 = treeSimCoinPartial K D n.live n.count coinRnd n.st₂ n.next₂ ∧
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (p.label + 2) δ ∧ TreeSimFutureEmpty (p.label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (p.label + 2) z.2.2) := by
  apply relTriple_bind (treeStages_extendMult_real_start prims K D p.T₀ p.pivotParty p.pivot
    old visible p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys p.label p.count future p.products₁ p.products₂
    p.len₁ p.len₂ p.st₁ p.st₂ p.lab₁ p.lab₂ (p.k₁ K D) (p.k₂ K D) a b h fresh)
  intro u z hu
  obtain ⟨rnd, δ, hu, hz, hc, hv, hf, fresh₁, _⟩ := hu
  rw [hu, hz]
  apply relTriple_post_mono (treeStages_extendMult_coin_round prims K D A (p.data K D rnd δ)
    p.label 1 hv hf p.keys p.lab₁ p.lab₂ (p.next₁ K D) (p.next₂ K D)
    (fun i x => treeStages_challenge_prefix K (p.ctx₁ i) x.2 (p.body₁ i x))
    (fun i x => treeStages_challenge_prefix K (p.ctx₂ i) x.2 (p.body₂ i x)) state u.2 z.2 hc fresh₁)
  intro r t hr
  obtain ⟨sent, coinRnd, hs, hrSent, htSent, hrSteps, htSteps, hstream, hzero, hempty₁, hempty₂⟩ := hr
  exact ⟨rnd, δ, sent, coinRnd, hs, hrSent, htSent, hrSteps, htSteps, hstream, hv, hzero, hempty₁, hempty₂⟩

/-- A reachable reduction boundary with only deterministic invariant closure
left to establish. All field sampling, the adversarial exchange and the next
Coin sampling have already been proved, and are not fields of this predicate. -/
def TreeStagesExtendMultChallengeBoundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ p : TreeStagesExtendMultChallenge K D, ∃ rnd δ,
    a.1.1 = b.1.1 ∧ TreeSimStreamRel δ a.2 b.2 ∧
    (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero (p.label + 1) δ ∧
    TreeSimFutureEmpty (p.label + 1) a.2.1.2 ∧
    (let d := p.data K D rnd δ
     a.1.2 = treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
     b.1.2 = treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∧
    (∀ state sent coinRnd u z,
      let n := p.coinNext K D rnd δ sent
      TreeSimStreamRel δ u z → TreeSimFutureZero (p.label + 2) δ →
      TreeSimFutureEmpty (p.label + 2) u.1.2 → TreeSimFutureEmpty (p.label + 2) z.2 →
      Bad u ∨ Inv ((state, treeSimCoinPartial K D n.live n.count coinRnd n.st₁ n.next₁), u)
        ((state, treeSimCoinPartial K D n.live n.count coinRnd n.st₂ n.next₂), z))

/-- The actual reduction transition supplies a core preservation case. It
can be assigned to `.ceremony` when constructing `TreeSimRoundCore`, so the
stronger generic ExtendMult continuation certificate is unnecessary here. -/
theorem treeStages_extendMult_challenge_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage) (which : TreeSimStage)
    (identify : ∀ a b, stage a = which → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeStagesExtendMultChallengeBoundary K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage which := by
  intro a b hg hinv hbad hdone
  obtain ⟨p, rnd, δ, had, hc, hv, hf, fresh, ⟨ha, hb⟩, close⟩ := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  rw [ha, hb, ← had]
  apply relTriple_post_mono (treeStages_extendMult_coin_round prims K D A (p.data K D rnd δ)
    p.label 1 hv hf p.keys p.lab₁ p.lab₂ (p.next₁ K D) (p.next₂ K D)
    (fun i x => treeStages_challenge_prefix K (p.ctx₁ i) x.2 (p.body₁ i x))
    (fun i x => treeStages_challenge_prefix K (p.ctx₂ i) x.2 (p.body₂ i x)) a.1.1 a.2 b.2 hc fresh)
  intro u z hu
  obtain ⟨sent, coinRnd, hstate, _, _, hu, hz, hstream, hzero, hf₁, hf₂⟩ := hu
  change Bad u.2 ∨ Inv ((u.1.1, u.1.2.1), u.2) ((z.1.1, z.1.2.1), z.2)
  rw [hu, hz, hstate]
  exact close z.1.1 sent coinRnd u.2 z.2 hstream hzero hf₁ hf₂

/-- An unfilled pivot changes stored shares but is never appended to a peer
history. This holds for the actual field encoding without linearity assumptions. -/
theorem treeStages_recordPeer_unfilled (D : C.Coalition) (T₀ : C.Term)
    (lacked : lackedTerm D.1 = some T₀) (unfilled : T₀ ∉ filledTerms K)
    (i : C.Party) (count : ℕ) (difference : ℕ → E) (v : Shares C E)
    (h₁ h₂ : C.Term → List Bit) (history : ∀ T, i ∈ C.holders T → h₁ T = h₂ T) :
    ∀ T, i ∈ C.holders T →
      recordPeer K (elementCodec K) i h₁ v count T =
      recordPeer K (elementCodec K) i h₂ (treeSimFieldHeldShift D i count difference v) count T := by
  intro T held
  simp only [recordPeer, if_pos held, history T held]
  by_cases ht : T = T₀
  · subst T
    have noFiller : ∀ g, filler K .peer T₀ g = none := by
      intro g
      apply List.find?_eq_none.mpr
      intro j _
      intro eq
      exact unfilled (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, of_decide_eq_true eq⟩)
    simp only [noFiller, Option.isSome_none, List.filter_false, List.flatMap_nil]
  · have same : treeSimFieldHeldShift D i count difference v T = v T := by
      funext g
      simp [treeSimFieldHeldShift, lacked, Ne.symm ht]
    rw [same]

/-- In the unfilled-pivot case, successful actual ExtendMult returns preserve
the held-history equality needed at the subsequent salted-digest boundary. -/
theorem TreeSimExtendMultExitRel.history_unfilled (D : C.Coalition)
    (d : TreeSimExtendMultData K D) (unfilled : d.T₀ ∉ filledTerms K)
    (i : C.Party) (honest : i ∉ D.1)
    (history : ∀ T, i ∈ C.holders T → (d.st₁ i).history T = (d.st₂ i).history T)
    (x y : Shares C E × RunState C) (h : TreeSimExtendMultExitRel K D d i x y) :
    ∀ T, i ∈ C.holders T → x.2.history T = y.2.history T := by
  intro T held
  rw [h.2.1, h.2.2]
  simp only [d.self₁ i honest, d.self₂ i honest, h.1]
  exact treeStages_recordPeer_unfilled K D d.T₀ d.pivot.lacked unfilled i d.count _ x.1
    (d.st₁ i).history (d.st₂ i).history history T held

/-- Interpret the actual honest hash program in the shared public cache.
This includes adaptive salted-digest queries and arbitrary dealer cache hits. -/
theorem treeStages_digestQuery_onHash (D : C.Coalition) (i : C.Party)
    (salts : Shares C Bit) (history : C.Term → List Bit) :
    ∃ m : StateT (HashCache C) ProbComp (List HashOutput),
      simulateQ (streamWorld prims D)
        (free (liftComp (digestQuery i salts history) (LocalSpec C))) = onHash m := by
  have single : ∀ q : Query C, simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C))) = onHash (hashAnswer prims q) := by
    intro q
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  unfold digestQuery
  generalize C.terms = terms
  induction terms with
  | nil => exact ⟨pure [], by simp [treeStages_onHash_pure]⟩
  | cons T terms ih =>
    obtain ⟨m, hm⟩ := ih
    by_cases held : i ∈ C.holders T
    · refine ⟨(do
        let h ← hashAnswer prims (.history (history T))
        let d ← hashAnswer prims (.digest (vector 256 (salts T)) h)
        let ds ← m
        pure (d :: ds)), ?_⟩
      simp only [List.mapM_cons, if_pos held, liftComp_bind, liftComp_pure, free_bind,
        free_pure, simulateQ_bind, simulateQ_pure, treeStages_onHash_bind,
        treeStages_onHash_pure, single, hm, bind_assoc]
    · refine ⟨(do let ds ← m; pure (0 :: ds)), ?_⟩
      simp only [List.mapM_cons, if_neg held, pure_bind, liftComp_bind, liftComp_pure,
        free_bind, free_pure, simulateQ_bind, simulateQ_pure, treeStages_onHash_bind,
        treeStages_onHash_pure, hm]

/-- Only held histories and the first 256 salt bits occur in a digest entry. -/
theorem treeStages_digestQuery_congr (i : C.Party) (salts₁ salts₂ : Shares C Bit)
    (history₁ history₂ : C.Term → List Bit)
    (salts : ∀ T, i ∈ C.holders T → ∀ g < 256, salts₁ T g = salts₂ T g)
    (history : ∀ T, i ∈ C.holders T → history₁ T = history₂ T) :
    digestQuery i salts₁ history₁ = digestQuery i salts₂ history₂ := by
  unfold digestQuery
  congr 1
  funext T
  by_cases held : i ∈ C.holders T
  · simp only [if_pos held, history T held, vector_congr' 256 _ _ (salts T held)]
  · simp only [if_neg held]

/-- Couple the real digest entry from equality on its actual held inputs.
Both hash levels run against the existing shared cache, with no freshness
assumption and no change to either private stream table. -/
theorem treeStages_digest_entry (D : C.Coalition) (i : C.Party)
    (ctx₁ ctx₂ : Context C) (self₁ : ctx₁.self = i) (self₂ : ctx₂.self = i)
    (salts₁ salts₂ : Shares C Bit) (st₁ st₂ : RunState C)
    (salts : ∀ T, i ∈ C.holders T → ∀ g < 256, salts₁ T g = salts₂ T g)
    (history : ∀ T, i ∈ C.holders T → st₁.history T = st₂.history T)
    (k₁ k₂ : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        (((compareDigests ctx₁ salts₁).run st₁ >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        (((compareDigests ctx₂ salts₂).run st₂ >>= k₂).run)))).run b)
      (fun u z => (∃ ds,
        u.1 = treeSimCheckStep K (.digests (fun _ => ds)) i (k₁ ((), st₁)) ∧
        z.1 = treeSimCheckStep K (.digests (fun _ => ds)) i (k₂ ((), st₂))) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rw [treeSim_digest_entry, treeSim_digest_entry, self₁, self₂,
    treeStages_digestQuery_congr i salts₁ salts₂ st₁.history st₂.history salts history]
  simp only [simulateQ_map, StateT.run_map]
  obtain ⟨m, hm⟩ := treeStages_digestQuery_onHash prims D i salts₂ st₂.history
  apply relTriple_map
  apply relTriple_post_mono (treeSim_onHash_coupling prims D _ m hm δ a b h)
  intro u z hu
  exact ⟨⟨u.1, rfl, by rw [hu.1]⟩, hu.2⟩

/-- The salt sampling and digest prefix in the real randomization check. -/
def treeStagesSaltedDigest (ctx : Context C) : RunM C E RealSpec Unit := do
  let salts ← (realCheckGadgets K ctx).randBits 256
  compareDigests ctx salts.1

theorem treeStages_saltedDigest_factor (ctx : Context C) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    free (advance (((treeStagesSaltedDigest K ctx).run st >>= k).run)) =
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label 2 256) (LocalSpec C)) >>= fun salts =>
        free (advance (((compareDigests ctx salts.1).run (nextLabel st) >>= k).run))) := by
  unfold treeStagesSaltedDigest
  change free (advance ((((prssRandomness ctx (bitCodec (E := E)) 2 256 >>= fun salts =>
    compareDigests ctx salts.1).run st) >>= k).run)) = _
  rw [prssRandomness_run, bind_assoc]
  simp only [advance_oracleStep_bind, free_bind]

/-- Actual salt PRSS and both digest hash levels, with shared salts derived
from the zero future translation. The unused pair draws and cache frames are
retained; no salt-equality or empty-public-cache premise is needed. -/
theorem treeStages_saltedDigest_entry (D : C.Coalition) (i : C.Party)
    (ctx₁ ctx₂ : Context C) (self₁ : ctx₁.self = i) (self₂ : ctx₂.self = i)
    (keys : ctx₁.prss = ctx₂.prss) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (history : ∀ T, i ∈ C.holders T → st₁.history T = st₂.history T)
    (k₁ k₂ : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero st₁.label δ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (advance (((treeStagesSaltedDigest K ctx₁).run st₁ >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (advance (((treeStagesSaltedDigest K ctx₂).run st₂ >>= k₂).run)))).run b)
      (fun u z => (∃ ds,
        u.1 = treeSimCheckStep K (.digests (fun _ => ds)) i (k₁ ((), nextLabel st₁)) ∧
        z.1 = treeSimCheckStep K (.digests (fun _ => ds)) i (k₂ ((), nextLabel st₂))) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ TreeSimCacheFrame st₁.label a.1.2 u.2.1.2 ∧
        TreeSimCacheFrame st₁.label b.2 z.2.2) := by
  rw [treeStages_saltedDigest_factor, treeStages_saltedDigest_factor, ← lab,
    ← treeSim_prssDraw_context ctx₁ ctx₂ (self₁.trans self₂.symm) keys]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeSim_prssBits_mixed (E := E) prims D δ visible ctx₁ st₁.label 2 256 a b h))
  intro r₁ r₂ hr
  have zero := treeSim_prssShift_zero δ ctx₁ st₁.label 2 256
    (fun name key g _ => future ((name, key), st₁.label, 2, g) (by rfl))
  have masks := hr.1
  simp only [zero, Prod.fst_zero, Prod.snd_zero, add_zero] at masks
  have eq : r₁.1 = r₂.1 := (Prod.ext masks.1 masks.2.1).symm
  have f₁ : TreeSimCacheFrame st₁.label a.1.2 r₁.2.1.2 := by
    apply treeSim_prssBits_frame (E := E) prims D ctx₁ st₁.label 2 256 a.1 (r₁.1, r₁.2.1)
    rw [← treeSimLoggedWorld_erase prims D _ a.1 a.2, support_map]
    exact ⟨r₁, hr.2.1, rfl⟩
  have f₂ := treeSim_prssBits_frame (E := E) prims D ctx₁ st₁.label 2 256 b r₂ hr.2.2
  rw [← eq]
  apply relTriple_post_mono (treeStages_digest_entry prims K D i ctx₁ ctx₂ self₁ self₂
    r₁.1.1 r₁.1.1 (nextLabel st₁) (nextLabel st₂) (fun _ _ _ _ => rfl) history
    k₁ k₂ δ r₁.2 r₂.2 masks.2.2)
  intro u z hu
  exact ⟨hu.1, hu.2.1, by simpa only [hu.2.2.1] using f₁,
    by simpa only [hu.2.2.2] using f₂⟩

/-- The actual digest decision selects the live operators for the following
Coin. Transport aborts and failed digest comparisons both remain inactive. -/
def treeStages_check_coinNext (D : C.Coalition) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (sent : C.Party → Mail C E)
    (label count : ℕ) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (next₁ next₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, k₁ i = ((realCheckGadgets K (ctx₁ i)).coin count).run (st₁ i) >>= next₁ i)
    (program₂ : ∀ i, k₂ i = ((realCheckGadgets K (ctx₂ i)).coin count).run (st₂ i) >>= next₂ i) :
    TreeStagesCoinNext K D (fun i (_ : Unit) => k₁ i) (fun i (_ : Unit) => k₂ i)
      (treeSimCheckResult K D live kind sent) (treeSimCheckResult K D live kind sent) := by
  have shape : ∀ i, treeSimCheckResult K D live kind sent i =
      if i ∈ D.1 then none else
        if (treeSimCheckResult K D live kind sent i).isSome then some () else none := by
    intro i
    by_cases hi : i ∈ D.1
    · simp [treeSimCheckResult, hi]
    · rw [if_neg hi]
      cases h : treeSimCheckResult K D live kind sent i with
      | none => rfl
      | some u => cases u; rfl
  exact {
    label := label, count := count, ctx₁ := ctx₁, ctx₂ := ctx₂,
    self₁ := self₁, self₂ := self₂, keys := keys, st₁ := st₁, st₂ := st₂,
    lab₁ := lab₁, lab₂ := lab₂,
    live := fun i => (treeSimCheckResult K D live kind sent i).isSome,
    x₁ := fun _ => (), x₂ := fun _ => (), shape₁ := shape, shape₂ := shape,
    next₁ := next₁, next₂ := next₂,
    program₁ := fun i _ _ => program₁ i, program₂ := fun i _ _ => program₂ i }

/-- Complete the real check exchange and enter the next real Coin, including
rushing, failed tests, partial aborts and the next private-cache frontier.
Only the actual common outgoing check data and program equations are inputs. -/
theorem treeStages_check_coin_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (label count : ℕ) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (next₁ next₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, k₁ i = ((realCheckGadgets K (ctx₁ i)).coin count).run (st₁ i) >>= next₁ i)
    (program₂ : ∀ i, k₂ i = ((realCheckGadgets K (ctx₂ i)).coin count).run (st₂ i) >>= next₂ i)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero label δ) (state : A.State)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind k₂)).run b)
      (fun u z => ∃ sent rnd,
        let active := fun i => (treeSimCheckResult K D live kind sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D active count rnd st₁ next₁ ∧
        z.1.2.1 = treeSimCoinPartial K D active count rnd st₂ next₂ ∧
        TreeSimStreamRel δ u.2 z.2 ∧ TreeSimFutureZero (label + 1) δ ∧
        TreeSimFutureEmpty (label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (label + 1) z.2.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_check_round_factor, treeSim_check_round_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b h)
  intro r₁ r₂ hr
  rw [hr.1]
  let n := treeStages_check_coinNext K D live kind r₂.1.2 label count ctx₁ ctx₂ self₁ self₂ keys
    st₁ st₂ lab₁ lab₂ k₁ k₂ next₁ next₂ program₁ program₂
  have fresh' : TreeSimFutureEmpty n.label r₁.2.1.2 := by
    rw [hr.2.2.1]
    exact fresh
  apply relTriple_bind (n.coupling_fresh prims K D _ _ _ _ δ visible future r₁.2 r₂.2 hr.2.1 fresh')
  intro u z hz
  obtain ⟨_, _, hf₁, hf₂, hδ, ⟨rnd, hu, hz⟩, hc⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨r₂.1.2, rnd, rfl, rfl, rfl, hu, hz, hc, hδ, hf₁, hf₂⟩

/-- All actual digest entries in driver order. Earlier aborts remain stopped,
and every live operator retains its own history and saved continuation. -/
theorem treeStages_digest_partial_entry (D : C.Coalition) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (salts₁ salts₂ : C.Party → Shares C Bit) (st₁ st₂ : C.Party → RunState C)
    (salts : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      ∀ g < 256, salts₁ i T g = salts₂ i T g)
    (history : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      (st₁ i).history T = (st₂ i).history T)
    (k₁ k₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => (compareDigests (ctx₁ i) (salts₁ i)).run (st₁ i) >>= k₁ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => (compareDigests (ctx₂ i) (salts₂ i)).run (st₂ i) >>= k₂ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b)
      (fun u z => (∃ ds,
        u.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k₁ i ((), st₁ i)) ∧
        z.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k₂ i ((), st₂ i))) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  let J := fun s t => TreeSimStreamRel δ s t ∧ s.1.2 = a.1.2 ∧ t.2 = b.2
  let Q := fun i (u z : Step C E RealSpec TreeOutput) => ∃ ds,
    u = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k₁ j ((), st₁ j)) i ∧
    z = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k₂ j ((), st₂ j)) i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ _ _ J Q ?_ a b ⟨h, rfl, rfl⟩)
  · intro u z hu
    choose ds h₁ h₂ using hu.1
    exact ⟨⟨ds, funext h₁, funext h₂⟩, hu.2⟩
  · intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨[], by simp [treeSimCheckWaiting, hi],
        by simp [treeSimCheckWaiting, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume]
        apply relTriple_post_mono (treeStages_digest_entry prims K D i (ctx₁ i) (ctx₂ i)
          (self₁ i hi) (self₂ i hi) (salts₁ i) (salts₂ i) (st₁ i) (st₂ i)
          (salts i hi hl) (history i hi hl) (k₁ i) (k₂ i) δ s t hst.1)
        intro u z hu
        obtain ⟨⟨ds, hu, hz⟩, hc, hf₁, hf₂⟩ := hu
        exact ⟨⟨ds, by simpa only [treeSimCheckWaiting, if_neg hi, if_pos hl] using hu,
          by simpa only [treeSimCheckWaiting, if_neg hi, if_pos hl] using hz⟩,
          hc, hf₁.trans hst.2.1, hf₂.trans hst.2.2⟩
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨[], by simp [treeSimCheckWaiting, hi, hl],
          by simp [treeSimCheckWaiting, hi, hl]⟩, hst⟩

/-- Interleave each operator's real salt draw and digest queries in driver
order. Shared hidden salts are replayed from the same related tables. -/
theorem treeStages_saltedDigest_partial_entry (D : C.Coalition) (live : C.Party → Bool)
    (label : ℕ) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (history : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      (st₁ i).history T = (st₂ i).history T)
    (k₁ k₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero label δ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx₁ i)).run (st₁ i) >>= k₁ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx₂ i)).run (st₂ i) >>= k₂ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b)
      (fun u z => (∃ ds,
        u.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k₁ i ((), nextLabel (st₁ i))) ∧
        z.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k₂ i ((), nextLabel (st₂ i)))) ∧
        TreeSimStreamRel δ u.2 z.2 ∧
        TreeSimFutureEmpty (label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (label + 1) z.2.2) := by
  let J := fun s t => TreeSimStreamRel δ s t ∧
    TreeSimCacheFrame label a.1.2 s.1.2 ∧ TreeSimCacheFrame label b.2 t.2
  let Q := fun i (u z : Step C E RealSpec TreeOutput) => ∃ ds,
    u = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k₁ j ((), nextLabel (st₁ j))) i ∧
    z = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k₂ j ((), nextLabel (st₂ j))) i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ _ _ J Q ?_ a b
    ⟨h, fun _ _ => rfl, fun _ _ => rfl⟩)
  · intro u z hu
    choose ds h₁ h₂ using hu.1
    exact ⟨⟨ds, funext h₁, funext h₂⟩, hu.2.1, treeSim_futureEmpty_after fresh hu.2.2.1,
      treeSim_futureEmpty_after (treeSim_futureEmpty_related fresh h.2) hu.2.2.2⟩
  · intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨[], by simp [treeSimCheckWaiting, hi],
        by simp [treeSimCheckWaiting, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume]
        apply relTriple_post_mono (treeStages_saltedDigest_entry prims K D i (ctx₁ i) (ctx₂ i)
          (self₁ i hi) (self₂ i hi) (keys i hi) (st₁ i) (st₂ i)
          ((lab₁ i hi).trans (lab₂ i hi).symm) (history i hi hl) (k₁ i) (k₂ i)
          δ visible (by rw [lab₁ i hi]; exact future) s t hst.1)
        intro u z hu
        obtain ⟨⟨ds, hu, hz⟩, hc, hf₁, hf₂⟩ := hu
        rw [lab₁ i hi] at hf₁ hf₂
        exact ⟨⟨ds, by simpa only [treeSimCheckWaiting, if_neg hi, if_pos hl] using hu,
          by simpa only [treeSimCheckWaiting, if_neg hi, if_pos hl] using hz⟩,
          hc, fun x hx => (hf₁ x hx).trans (hst.2.1 x hx),
          fun x hx => (hf₂ x hx).trans (hst.2.2 x hx)⟩
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨[], by simp [treeSimCheckWaiting, hi, hl],
          by simp [treeSimCheckWaiting, hi, hl]⟩, hst⟩

/-- The digest boundary of the real check, with its actual following
challenge. Equality is required only on inputs read by live honest operators. -/
structure TreeStagesDigestChallenge (D : C.Coalition) where
  label : ℕ
  live : C.Party → Bool
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label
  salts₁ : C.Party → Shares C Bit
  salts₂ : C.Party → Shares C Bit
  salts : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
    ∀ g < 256, salts₁ i T g = salts₂ i T g
  history : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
    (st₁ i).history T = (st₂ i).history T
  body₁ : C.Party → E × RunState C → PartyM C E RealSpec TreeOutput
  body₂ : C.Party → E × RunState C → PartyM C E RealSpec TreeOutput

def TreeStagesDigestChallenge.k₁ (D : C.Coalition) (p : TreeStagesDigestChallenge (E := E) D)
    (i : C.Party) (x : Unit × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K (p.ctx₁ i))).run x.2 >>= p.body₁ i

def TreeStagesDigestChallenge.k₂ (D : C.Coalition) (p : TreeStagesDigestChallenge (E := E) D)
    (i : C.Party) (x : Unit × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K (p.ctx₂ i))).run x.2 >>= p.body₂ i

def TreeStagesDigestChallenge.next₁ (D : C.Coalition) (p : TreeStagesDigestChallenge (E := E) D)
    (i : C.Party) : List E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K (p.st₁ i).tag (p.st₁ i).label (p.body₁ i)

def TreeStagesDigestChallenge.next₂ (D : C.Coalition) (p : TreeStagesDigestChallenge (E := E) D)
    (i : C.Party) : List E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K (p.st₂ i).tag (p.st₂ i).label (p.body₂ i)

def TreeStagesDigestChallenge.enter₁ (D : C.Coalition) (p : TreeStagesDigestChallenge (E := E) D) :
    OracleComp (WorldSpec C) (C.Party → Step C E RealSpec TreeOutput) :=
  treeSimResumeAll
    (fun i (_ : Unit) => (compareDigests (p.ctx₁ i) (p.salts₁ i)).run (p.st₁ i) >>= p.k₁ K D i)
    (fun i => if i ∈ D.1 then none else if p.live i then some () else none)

def TreeStagesDigestChallenge.enter₂ (D : C.Coalition) (p : TreeStagesDigestChallenge (E := E) D) :
    OracleComp (WorldSpec C) (C.Party → Step C E RealSpec TreeOutput) :=
  treeSimResumeAll
    (fun i (_ : Unit) => (compareDigests (p.ctx₂ i) (p.salts₂ i)).run (p.st₂ i) >>= p.k₂ K D i)
    (fun i => if i ∈ D.1 then none else if p.live i then some () else none)

/-- The whole digest stage: both actual hash levels, rushing exchange,
digest agreement, transport aborts and the following challenge's Coin entry.
This is a coupling of the concrete programs, not a continuation premise. -/
theorem TreeStagesDigestChallenge.coupling (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesDigestChallenge (E := E) D)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero p.label δ) (state : A.State)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty p.label a.1.2) :
    RelTriple
      (((simulateQ (treeSimLoggedWorld prims D) (p.enter₁ K D)).run a) >>=
        fun u => (stepRound (treeSimRealRoles prims D) D A noFunctionality state u.1).run u.2)
      (((simulateQ (streamWorld prims D) (p.enter₂ K D)).run b) >>=
        fun z => (stepRound (treeSimIdealRoles prims D) D A noFunctionality state z.1).run z.2)
      (fun u z => ∃ ds sent rnd,
        let active := fun i => (treeSimCheckResult K D p.live (.digests ds) sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D active 1 rnd p.st₁ (p.next₁ K D) ∧
        z.1.2.1 = treeSimCoinPartial K D active 1 rnd p.st₂ (p.next₂ K D) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ TreeSimFutureZero (p.label + 1) δ ∧
        TreeSimFutureEmpty (p.label + 1) u.2.1.2 ∧ TreeSimFutureEmpty (p.label + 1) z.2.2) := by
  apply relTriple_bind (treeStages_digest_partial_entry prims K D p.live p.ctx₁ p.ctx₂
    p.self₁ p.self₂ p.salts₁ p.salts₂ p.st₁ p.st₂ p.salts p.history (p.k₁ K D) (p.k₂ K D) δ a b h)
  intro u z hz
  obtain ⟨⟨ds, hu, hz⟩, hc, hf₁, _⟩ := hz
  rw [hu, hz]
  apply relTriple_post_mono (treeStages_check_coin_round prims K D A p.live (.digests ds) p.label 1
    p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys p.st₁ p.st₂ p.lab₁ p.lab₂
    (fun i => p.k₁ K D i ((), p.st₁ i)) (fun i => p.k₂ K D i ((), p.st₂ i))
    (p.next₁ K D) (p.next₂ K D)
    (fun i => treeStages_challenge_prefix K (p.ctx₁ i) (p.st₁ i) (p.body₁ i))
    (fun i => treeStages_challenge_prefix K (p.ctx₂ i) (p.st₂ i) (p.body₂ i))
    δ visible future state u.2 z.2 hc (by rw [hf₁]; exact fresh))
  intro v w hv
  exact ⟨ds, hv⟩

/-- A reached digest exchange needs only deterministic successor closure.
The comparison, rushing call and next challenge PRSS are already proved. -/
def TreeStagesDigestChallengeBoundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ p : TreeStagesDigestChallenge (E := E) D, ∃ ds δ,
    a.1.1 = b.1.1 ∧ TreeSimStreamRel δ a.2 b.2 ∧
    (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero p.label δ ∧
    TreeSimFutureEmpty p.label a.2.1.2 ∧
    a.1.2 = treeSimCheckWaiting K D p.live (.digests ds) (fun i => p.k₁ K D i ((), p.st₁ i)) ∧
    b.1.2 = treeSimCheckWaiting K D p.live (.digests ds) (fun i => p.k₂ K D i ((), p.st₂ i)) ∧
    (∀ state sent coinRnd u z,
      let active := fun i => (treeSimCheckResult K D p.live (.digests ds) sent i).isSome
      TreeSimStreamRel δ u z → TreeSimFutureZero (p.label + 1) δ →
      TreeSimFutureEmpty (p.label + 1) u.1.2 → TreeSimFutureEmpty (p.label + 1) z.2 →
      Bad u ∨ Inv ((state, treeSimCoinPartial K D active 1 coinRnd p.st₁ (p.next₁ K D)), u)
        ((state, treeSimCoinPartial K D active 1 coinRnd p.st₂ (p.next₂ K D)), z))

/-- A preservation case for the actual digest-to-challenge transition.
It can be used by the core's `.ceremony` case without the stronger generic
check closure requiring a continuation proof at every arbitrary party state. -/
theorem treeStages_digest_challenge_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage) (which : TreeSimStage)
    (identify : ∀ a b, stage a = which → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeStagesDigestChallengeBoundary K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage which := by
  intro a b hg hinv hbad hdone
  obtain ⟨p, ds, δ, had, hc, hv, hf, fresh, ha, hb, close⟩ := identify a b hg hinv hbad hdone
  rw [ha, hb, ← had]
  apply relTriple_post_mono (treeStages_check_coin_round prims K D A p.live (.digests ds) p.label 1
    p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys p.st₁ p.st₂ p.lab₁ p.lab₂
    (fun i => p.k₁ K D i ((), p.st₁ i)) (fun i => p.k₂ K D i ((), p.st₂ i))
    (p.next₁ K D) (p.next₂ K D)
    (fun i => treeStages_challenge_prefix K (p.ctx₁ i) (p.st₁ i) (p.body₁ i))
    (fun i => treeStages_challenge_prefix K (p.ctx₂ i) (p.st₂ i) (p.body₂ i))
    δ hv hf a.1.1 a.2 b.2 hc fresh)
  intro u z hu
  obtain ⟨sent, rnd, hs, _, _, hu, hz, hc, hf, he₁, he₂⟩ := hu
  change Bad u.2 ∨ Inv ((u.1.1, u.1.2.1), u.2) ((z.1.1, z.1.2.1), z.2)
  rw [hu, hz, hs]
  exact close z.1.1 sent rnd u.2 z.2 hc hf he₁ he₂

/-- Complete the salted-digest stage of the real check through the next
challenge opening. This preserves the actual order: each salt draw precedes
its history/digest queries, all digest entries precede rushing, and only the
operators passing the real digest test enter Coin. -/
theorem treeStages_saltedDigest_challenge (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (live : C.Party → Bool)
    (label : ℕ) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (history : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      (st₁ i).history T = (st₂ i).history T)
    (body₁ body₂ : C.Party → E × RunState C → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero label δ) (state : A.State)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      (((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx₁ i)).run (st₁ i) >>= fun x =>
          (challenge K (realCheckGadgets K (ctx₁ i))).run x.2 >>= body₁ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a) >>=
        fun u => (stepRound (treeSimRealRoles prims D) D A noFunctionality state u.1).run u.2)
      (((simulateQ (streamWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx₂ i)).run (st₂ i) >>= fun x =>
          (challenge K (realCheckGadgets K (ctx₂ i))).run x.2 >>= body₂ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b) >>=
        fun z => (stepRound (treeSimIdealRoles prims D) D A noFunctionality state z.1).run z.2)
      (fun u z => ∃ ds sent rnd,
        let active := fun i => (treeSimCheckResult K D live (.digests ds) sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D active 1 rnd (fun i => nextLabel (st₁ i))
          (fun i => treeStagesChallengeTail K (st₁ i).tag ((st₁ i).label + 1) (body₁ i)) ∧
        z.1.2.1 = treeSimCoinPartial K D active 1 rnd (fun i => nextLabel (st₂ i))
          (fun i => treeStagesChallengeTail K (st₂ i).tag ((st₂ i).label + 1) (body₂ i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ TreeSimFutureZero (label + 2) δ ∧
        TreeSimFutureEmpty (label + 2) u.2.1.2 ∧ TreeSimFutureEmpty (label + 2) z.2.2) := by
  apply relTriple_bind (treeStages_saltedDigest_partial_entry prims K D live label ctx₁ ctx₂
    self₁ self₂ keys st₁ st₂ lab₁ lab₂ history _ _ δ visible future a b h fresh)
  intro u z hz
  obtain ⟨⟨ds, hu, hz⟩, hc, hf₁, _⟩ := hz
  rw [hu, hz]
  apply relTriple_post_mono (treeStages_check_coin_round prims K D A live (.digests ds) (label + 1) 1
    ctx₁ ctx₂ self₁ self₂ keys (fun i => nextLabel (st₁ i)) (fun i => nextLabel (st₂ i))
    (fun i hi => congrArg (· + 1) (lab₁ i hi)) (fun i hi => congrArg (· + 1) (lab₂ i hi))
    _ _ _ _
    (fun i => treeStages_challenge_prefix K (ctx₁ i) (nextLabel (st₁ i)) (body₁ i))
    (fun i => treeStages_challenge_prefix K (ctx₂ i) (nextLabel (st₂ i)) (body₂ i))
    δ visible (fun x hx => future x (by omega)) state u.2 z.2 hc hf₁)
  intro v w hv
  exact ⟨ds, hv⟩

/-- Public-cache transport for a hidden salted digest. The real transcript
and both private stream tables remain the actual execution states. -/
def TreeStagesDigestRel (salt : List Bit) (h h' : HashOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  b.1 = relabelHashCache (digestSwap salt h h') a.1.1 ∧ TreeSimHiddenRel δ a.1.2 b.2

/-- Lift exact public-cache transport into the logged stream world. This
does not identify the two public caches after differently named queries. -/
theorem treeStages_onHash_transport {α : Type} (D : C.Coalition)
    (p₁ p₂ : OracleComp (WorldSpec C) α) (m₁ m₂ : StateT (HashCache C) ProbComp α)
    (hp₁ : simulateQ (streamWorld prims D) p₁ = onHash m₁)
    (hp₂ : simulateQ (streamWorld prims D) p₂ = onHash m₂)
    (τ : HashCache C → HashCache C)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (transport : m₂.run (τ a.1.1) = (fun r => (r.1, τ r.2)) <$> m₁.run a.1.1)
    (pub : b.1 = τ a.1.1) (hidden : TreeSimHiddenRel δ a.1.2 b.2) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) p₁).run a)
      ((simulateQ (streamWorld prims D) p₂).run b)
      (fun u z => u.1 = z.1 ∧ z.2.1 = τ u.2.1.1 ∧ TreeSimHiddenRel δ u.2.1.2 z.2.2 ∧
        u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  have mapped : (simulateQ (streamWorld prims D) p₂).run b =
      (fun z => (z.1, τ z.2.1, z.2.2)) <$>
        (simulateQ (streamWorld prims D) p₁).run (a.1.1, b.2) := by
    rw [hp₁, hp₂]
    simp only [onHash, StateT.run_mk, pub, transport, Functor.map_map]
  rw [mapped]
  have hr : RelTriple
      (id <$> (simulateQ (treeSimLoggedWorld prims D) p₁).run a)
      ((fun z => (z.1, τ z.2.1, z.2.2)) <$>
        (simulateQ (streamWorld prims D) p₁).run (a.1.1, b.2))
      (fun u z => u.1 = z.1 ∧ z.2.1 = τ u.2.1.1 ∧ TreeSimHiddenRel δ u.2.1.2 z.2.2 ∧
        u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
    apply relTriple_map
    apply relTriple_post_mono (treeSim_onHash_coupling prims D p₁ m₁ hp₁ δ a (a.1.1, b.2) ⟨rfl, hidden⟩)
    intro u z hu
    exact ⟨hu.1, congrArg τ hu.2.1.1.symm, hu.2.1.2, hu.2.2⟩
  simpa only [id_map] using hr

/-- A counted call away from the hidden salt respects digest-cache
transport, including private sampling and the actual AES stream-key queries. -/
theorem treeStages_local_digestSwap_step (D : C.Coalition)
    (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (t : (LocalSpec C).Domain) (safe : digestSaltHit salt t = false)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeStagesDigestRel salt h h' δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run a)
      ((simulateQ (streamWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run b)
      (fun u z => u.1 = z.1 ∧ TreeStagesDigestRel salt h h' δ u.2 z.2 ∧
        u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  have interp := treeSim_stream_adversary prims D (OracleComp.lift (OracleSpec.query t))
  simp only [simulateQ_spec_query] at interp
  apply relTriple_post_mono (treeStages_onHash_transport prims D _ _ _ _ interp interp
    (relabelHashCache (digestSwap salt h h')) δ a b
    ((localDigestAnswer_eq_of_no_salt prims salt h h' t _ safe).trans
      (localAnswer_digestSwap prims salt h h' a.1.1 t)) related.1 related.2)
  intro u z hu
  exact ⟨hu.1, ⟨hu.2.1, hu.2.2.1⟩, hu.2.2.2⟩

theorem treeStages_hiddenSalt_mono (D : C.Coalition) (salt : List Bit)
    {a b : TreeSimLog C} (hpref : a <+: b) (h : TreeSimHiddenSalt D a salt) :
    TreeSimHiddenSalt D b salt := by
  obtain ⟨length, T, key, label, hidden, answers⟩ := h
  exact ⟨length, T, key, label, hidden, fun g => hpref.sublist.subset (answers g)⟩

theorem treeStages_saltGuess_mono (D : C.Coalition)
    {a b : TreeSimLog C} (hpref : a <+: b) (h : TreeSimSaltGuess D a) :
    TreeSimSaltGuess D b := by
  obtain ⟨salt, hist, answer, hidden, hit⟩ := h
  exact ⟨salt, hist, answer, treeStages_hiddenSalt_mono D salt hpref hidden, hpref.sublist.subset hit⟩

/-- The counted query that breaks the transported cache is recorded at its
actual origin; it is not replaced by an unlogged ghost query. -/
theorem treeStages_local_query_log (D : C.Coalition) (t : (LocalSpec C).Domain)
    (s : TreeSimState C) (r : (LocalSpec C).Range t × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run s)) :
    r.2.2 = s.2 ++ [⟨.inl (.inl t), r.1⟩] := by
  rw [adversary_query] at hr
  erw [simulateQ_spec_query] at hr
  change r ∈ support ((fun u => (u.1, u.2, s.2 ++ [⟨.inl (.inl t), u.1⟩])) <$>
    (streamWorld prims D (.inl (.inl t))).run s.1) at hr
  rw [support_map] at hr
  obtain ⟨u, _, rfl⟩ := hr
  rfl

/-- A counted query at a previously drawn hidden salt is exactly the fixed
salt-guess event, for every supported answer of the real logged handler. -/
theorem treeStages_local_query_saltGuess (D : C.Coalition) (salt : List Bit)
    (t : (LocalSpec C).Domain) (hit : digestSaltHit salt t = true)
    (s : TreeSimState C) (hidden : TreeSimHiddenSalt D s.2 salt)
    (r : (LocalSpec C).Range t × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run s)) :
    TreeSimSaltGuess D r.2.2 := by
  have recorded := treeStages_local_query_log prims D t s r hr
  have hidden' := treeStages_hiddenSalt_mono D salt
    (treeSimLoggedWorld_prefix prims D _ s r hr) hidden
  rcases t with n | q | x
  · simp [digestSaltHit] at hit
  · cases q <;> simp only [digestSaltHit, Bool.false_eq_true] at hit
    case digest salt' hist =>
      have eq : salt' = salt := of_decide_eq_true hit
      subst salt'
      refine ⟨salt, hist, r.1, hidden', ?_⟩
      rw [recorded]
      simp
  · simp [digestSaltHit] at hit

/-- The entire adaptive counted computation respects the transported digest
cache until the fixed real salt-guess event. Its random draws and PRG calls
are retained, and the real log records the first distinguishing query. -/
theorem treeStages_local_digestSwap {α : Type} (D : C.Coalition)
    (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (p : OracleComp (LocalSpec C) α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeStagesDigestRel salt h h' δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.adversary p)).run b)
      (fun u z => TreeSimSaltGuess D u.2.2 ∨
        (u.1 = z.1 ∧ TreeStagesDigestRel salt h h' δ u.2 z.2 ∧
          u.2.1.2 = a.1.2 ∧ z.2.2 = b.2)) := by
  induction p using OracleComp.inductionOn generalizing a b with
  | pure x =>
    simp only [worldRoles, adversary_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨rfl, related, rfl, rfl⟩)
  | query_bind t k ih =>
    change RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.adversary (k x))).run a)
      ((simulateQ (streamWorld prims D)
        (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
          fun x => worldRoles.adversary (k x))).run b) _
    simp only [simulateQ_bind, StateT.run_bind]
    have step : RelTriple
        ((simulateQ (treeSimLoggedWorld prims D)
          (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run a)
        ((simulateQ (streamWorld prims D)
          (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))).run b)
        (fun u z => TreeSimSaltGuess D u.2.2 ∨
          (u.1 = z.1 ∧ TreeStagesDigestRel salt h h' δ u.2 z.2 ∧
            u.2.1.2 = a.1.2 ∧ z.2.2 = b.2)) := by
      by_cases hit : digestSaltHit salt t = true
      · apply relTriple_of_support_left
        intro u hu z
        exact Or.inl (treeStages_local_query_saltGuess prims D salt t hit a hidden u hu)
      · have safe : digestSaltHit salt t = false := by
          cases hv : digestSaltHit salt t <;> simp_all
        exact relTriple_post_mono
          (treeStages_local_digestSwap_step prims D salt h h' δ t safe a b related)
          (fun _ _ hp => Or.inr hp)
    apply relTriple_bind (treeSim_relTriple_support step)
    intro u z hu
    rcases hu.1 with bad | good
    · apply relTriple_of_support_left
      intro v hv w
      exact Or.inl (treeStages_saltGuess_mono D
        (treeSimLoggedWorld_prefix prims D _ u.2 v hv) bad)
    · rw [← good.1]
      apply relTriple_post_mono (ih u.1 u.2 z.2
        (treeStages_hiddenSalt_mono D salt (treeSimLoggedWorld_prefix prims D _ a u hu.2.1) hidden) good.2.1)
      intro v w hv
      rcases hv with bad | hv
      · exact Or.inl bad
      · exact Or.inr ⟨hv.1, hv.2.1, hv.2.2.1.trans good.2.2.1, hv.2.2.2.trans good.2.2.2⟩

/-- Both levels of one actual honest digest use the public cache. -/
theorem treeStages_oneDigest_onHash (D : C.Coalition) (salt history : List Bit) :
    simulateQ (streamWorld prims D)
      (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C))) =
      onHash (saltedDigestAnswer prims salt history) := by
  have single : ∀ q : Query C, simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C))) = onHash (hashAnswer prims q) := by
    intro q
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  simp only [oneDigestQuery, saltedDigestAnswer, liftComp_bind, free_bind, simulateQ_bind,
    treeStages_onHash_bind, single]

/-- Different recorded histories have exactly matching digest answers under
the standard digest swap. The inner hashes may already be in the dealer's
cache, and both actual history queries are retained in their own runs. -/
theorem treeStages_oneDigest_transport (D : C.Coalition) (salt history history' : List Bit)
    (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (inner : a.1.1 (.history history) = some h)
    (inner' : a.1.1 (.history history') = some h')
    (related : TreeStagesDigestRel salt h h' δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history') (LocalSpec C)))).run b)
      (fun u z => u.1 = z.1 ∧ TreeStagesDigestRel salt h h' δ u.2 z.2 ∧
        u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  apply relTriple_post_mono (treeStages_onHash_transport prims D _ _ _ _
    (treeStages_oneDigest_onHash prims D salt history)
    (treeStages_oneDigest_onHash prims D salt history')
    (relabelHashCache (digestSwap salt h h')) δ a b
    (saltedDigestAnswer_couple prims salt history history' h h' a.1.1 inner inner') related.1 related.2)
  intro u z hu
  exact ⟨hu.1, ⟨hu.2.1, hu.2.2.1⟩, hu.2.2.2⟩

/-- A complete hidden-digest/adversary transition with unequal histories:
the actual two-level honest hash is followed by an arbitrary adaptive counted
continuation. The only exceptional branch is the fixed real salt-guess event. -/
theorem treeStages_hiddenDigest_adaptive {α : Type} (D : C.Coalition)
    (salt history history' : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (k : HashOutput → OracleComp (LocalSpec C) α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (inner : a.1.1 (.history history) = some h)
    (inner' : a.1.1 (.history history') = some h')
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeStagesDigestRel salt h h' δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)) >>= fun d =>
          worldRoles.adversary (k d))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history') (LocalSpec C)) >>= fun d =>
          worldRoles.adversary (k d))).run b)
      (fun u z => TreeSimSaltGuess D u.2.2 ∨
        (u.1 = z.1 ∧ TreeStagesDigestRel salt h h' δ u.2 z.2 ∧
          u.2.1.2 = a.1.2 ∧ z.2.2 = b.2)) := by
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeStages_oneDigest_transport prims D salt history history' h h' δ a b inner inner' related))
  intro u z hu
  rw [← hu.1.1]
  apply relTriple_post_mono (treeStages_local_digestSwap prims D salt h h' δ (k u.1) u.2 z.2
    (treeStages_hiddenSalt_mono D salt (treeSimLoggedWorld_prefix prims D _ a u hu.2.1) hidden) hu.1.2.1)
  intro v w hv
  rcases hv with bad | hv
  · exact Or.inl bad
  · exact Or.inr ⟨hv.1, hv.2.1, hv.2.2.1.trans hu.1.2.2.1, hv.2.2.2.trans hu.1.2.2.2⟩

/-- Introduce the digest swap from the existing equal-public-cache invariant
at a fresh pair of outer digest addresses. Earlier history queries and dealer
cache contents are retained. -/
theorem treeStages_hiddenDigest_fresh {α : Type} (D : C.Coalition)
    (salt history history' : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (k : HashOutput → OracleComp (LocalSpec C) α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (inner : a.1.1 (.history history) = some h)
    (inner' : a.1.1 (.history history') = some h')
    (fresh : a.1.1 (.digest salt h) = none) (fresh' : a.1.1 (.digest salt h') = none)
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)) >>= fun d =>
          worldRoles.adversary (k d))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) salt history') (LocalSpec C)) >>= fun d =>
          worldRoles.adversary (k d))).run b)
      (fun u z => TreeSimSaltGuess D u.2.2 ∨
        (u.1 = z.1 ∧ TreeStagesDigestRel salt h h' δ u.2 z.2 ∧
          u.2.1.2 = a.1.2 ∧ z.2.2 = b.2)) := by
  apply treeStages_hiddenDigest_adaptive prims D salt history history' h h' δ k a b inner inner' hidden
  refine ⟨?_, related.2⟩
  rw [relabelHashCache_digestSwap_fresh salt h h' a.1.1 fresh fresh']
  exact related.1.symm

theorem treeStages_hashAnswer_mono {a b : TreeSimLog C} (hpref : a <+: b)
    (q : Query C) (h : HashOutput) (answer : TreeSimHashAnswer a q h) :
    TreeSimHashAnswer b q h :=
  answer.imp (fun ha => hpref.sublist.subset ha) (fun ha => hpref.sublist.subset ha)

/-- An honest hash query records its actual answer, including cache hits. -/
theorem treeStages_hash_answer_log (D : C.Coalition) (q : Query C)
    (s : TreeSimState C) (r : HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C)))).run s)) :
    TreeSimHashAnswer r.2.2 q r.1 := by
  change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q)))))).run s) at hr
  erw [simulateQ_spec_query] at hr
  change r ∈ support ((fun u => (u.1, u.2, s.2 ++ [⟨.inr (.inr (.inl q)), u.1⟩])) <$>
    (streamWorld prims D (.inr (.inr (.inl q)))).run s.1) at hr
  rw [support_map] at hr
  obtain ⟨u, _, rfl⟩ := hr
  exact Or.inl (by simp)

/-- Both certificates used by the fixed collision event come from the real
digest execution. Unlogged prefetched history entries need no coverage premise. -/
theorem treeStages_oneDigest_log (D : C.Coalition) (salt history : List Bit)
    (s : TreeSimState C) (r : HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)))).run s)) :
    ∃ h, TreeSimHashAnswer r.2.2 (.history history) h ∧
      TreeSimHashAnswer r.2.2 (.digest salt h) r.1 := by
  simp only [oneDigestQuery, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind,
    support_bind, Set.mem_iUnion] at hr
  obtain ⟨u, hu, hr⟩ := hr
  exact ⟨u.1, treeStages_hashAnswer_mono (treeSimLoggedWorld_prefix prims D _ u.2 r hr) _ _
    (treeStages_hash_answer_log prims D (.history history) s u hu),
    treeStages_hash_answer_log prims D (.digest salt u.1) u.2 r hr⟩

/-- Every held entry of the actual digest-query list has both hash answers
in the same real transcript, including when earlier queries hit the cache. -/
theorem treeStages_digestQueries_log (D : C.Coalition) (i : C.Party)
    (salts : Shares C Bit) (history : C.Term → List Bit) (terms : List C.Term)
    (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (liftComp
      (terms.mapM fun T => if i ∈ C.holders T then
        oneDigestQuery (C := C) (vector 256 (salts T)) (history T) else pure 0)
      (LocalSpec C)))).run s)) :
    ∀ (n : ℕ) T, terms[n]? = some T → i ∈ C.holders T → ∃ h d,
      TreeSimHashAnswer r.2.2 (.history (history T)) h ∧
      TreeSimHashAnswer r.2.2 (.digest (vector 256 (salts T)) h) d ∧ r.1[n]? = some d := by
  induction terms generalizing s r with
  | nil => simp
  | cons T terms ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, hr⟩ := hr
    subst r
    intro n T' hn held
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst T'
      simp only [if_pos held] at hu
      obtain ⟨h, hh, hd⟩ := treeStages_oneDigest_log prims D _ _ s u hu
      have hpref := treeSimLoggedWorld_prefix prims D _ u.2 v hv
      exact ⟨h, u.1, treeStages_hashAnswer_mono hpref _ _ hh,
        treeStages_hashAnswer_mono hpref _ _ hd, rfl⟩
    | succ n =>
      exact ih u.2 v hv n T' hn held

/-- The indices used by the actual check carry logged certificates for every
held term; this is obtained from `digestQuery`, not a cache-coverage premise. -/
theorem treeStages_digestQuery_log (D : C.Coalition) (i : C.Party)
    (salts : Shares C Bit) (history : C.Term → List Bit)
    (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (digestQuery i salts history) (LocalSpec C)))).run s)) :
    ∀ T, i ∈ C.holders T → ∃ h d,
      TreeSimHashAnswer r.2.2 (.history (history T)) h ∧
      TreeSimHashAnswer r.2.2 (.digest (vector 256 (salts T)) h) d ∧
      r.1[C.terms.idxOf T]? = some d := by
  intro T held
  apply treeStages_digestQueries_log prims D i salts history C.terms s r hr
    (C.terms.idxOf T) T _ held
  exact List.getElem?_idxOf (by simp [Committee.terms])

/-- Lift a per-operator transcript certificate through the actual sequential
resumption. Earlier certificates persist in the same final log. -/
theorem treeStages_resumeAll_log {α β : Type} (D : C.Coalition)
    (k : C.Party → β → PartyM C E RealSpec α) (out : C.Party → Option β)
    (P : C.Party → Step C E RealSpec α → TreeSimLog C → Prop)
    (mono : ∀ i v l l', l <+: l' → P i v l → P i v l')
    (step : ∀ i s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (treeSimResume (k i) (out i)))).run s) → P i r.1 r.2.2)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k out)).run s)) :
    ∀ i, P i (r.1 i) r.2.2 := by
  letI : Preorder (TreeSimState C) := {
    le := fun a b => a.2 <+: b.2
    le_refl := fun _ => List.prefix_refl _
    le_trans := fun _ _ _ => List.IsPrefix.trans }
  unfold treeSimResumeAll at hr
  rw [free_sequenceFin, simulateQ_sequenceFin] at hr
  exact (support_sequenceFin_state s _ (fun i v t => P i v t.2)
    (fun i t _ v hv => ⟨treeSimLoggedWorld_prefix prims D _ t v hv, step i t v hv⟩)
    (fun i v t t' hp ht => mono i v t.2 t'.2 ht hp) s (List.prefix_refl _) r hr).2

/-- Actual honest digest entries provide every certificate needed to reject
split histories. Corrupt and previously stopped operators issue no queries. -/
theorem treeStages_digest_partial_log (D : C.Coalition) (live : C.Party → Bool)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s)) :
    ∃ ds, r.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k i ((), st i)) ∧
      ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h d,
        TreeSimHashAnswer r.2.2 (.history ((st i).history T)) h ∧
        TreeSimHashAnswer r.2.2 (.digest (vector 256 (salts i T)) h) d ∧
        (ds i)[C.terms.idxOf T]? = some d := by
  let P := fun i (v : Step C E RealSpec TreeOutput) (log : TreeSimLog C) => ∃ ds,
    v = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k j ((), st j)) i ∧
    (i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h d,
      TreeSimHashAnswer log (.history ((st i).history T)) h ∧
      TreeSimHashAnswer log (.digest (vector 256 (salts i T)) h) d ∧
      ds[C.terms.idxOf T]? = some d)
  have certificates : ∀ i, P i (r.1 i) r.2.2 := by
    apply treeStages_resumeAll_log prims D _ _ P _ _ s r hr
    · intro i v l l' hpref hp
      obtain ⟨ds, hv, hc⟩ := hp
      refine ⟨ds, hv, ?_⟩
      intro hi hl T held
      obtain ⟨h, d, hh, hd, idx⟩ := hc hi hl T held
      exact ⟨h, d, treeStages_hashAnswer_mono hpref _ _ hh,
        treeStages_hashAnswer_mono hpref _ _ hd, idx⟩
    · intro i a u hu
      by_cases hi : i ∈ D.1
      · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hu
        subst u
        exact ⟨[], by simp [treeSimCheckWaiting, hi], fun hn => (hn hi).elim⟩
      · simp only [if_neg hi] at hu
        by_cases hl : live i = true
        · simp only [if_pos hl, treeSimResume] at hu
          change u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
            (worldRoles.honest (advance (((compareDigests (ctx i) (salts i)).run (st i) >>= k i).run)))).run a) at hu
          rw [treeSim_digest_entry (K := K), self i hi] at hu
          simp only [simulateQ_map, StateT.run_map, support_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          exact ⟨v.1, by simp [treeSimCheckWaiting, hi, hl],
            fun _ _ => treeStages_digestQuery_log prims D i (salts i) (st i).history a v hv⟩
        · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hu
          subst u
          exact ⟨[], by simp [treeSimCheckWaiting, hi, hl], fun _ hh => (hl hh).elim⟩
  choose ds steps cert using certificates
  exact ⟨ds, funext steps, cert⟩

/-- Salt generation is included in the real provenance statement. The
certificates name the salts actually sampled by each honest operator. -/
theorem treeStages_saltedDigest_partial_log (D : C.Coalition) (live : C.Party → Bool)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s)) :
    ∃ ds, r.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k i ((), nextLabel (st i))) ∧
      ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ salt h d,
        TreeSimHashAnswer r.2.2 (.history ((st i).history T)) h ∧
        TreeSimHashAnswer r.2.2 (.digest salt h) d ∧ (ds i)[C.terms.idxOf T]? = some d := by
  let P := fun i (v : Step C E RealSpec TreeOutput) (log : TreeSimLog C) => ∃ ds,
    v = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k j ((), nextLabel (st j))) i ∧
    (i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ salt h d,
      TreeSimHashAnswer log (.history ((st i).history T)) h ∧
      TreeSimHashAnswer log (.digest salt h) d ∧ ds[C.terms.idxOf T]? = some d)
  have certificates : ∀ i, P i (r.1 i) r.2.2 := by
    apply treeStages_resumeAll_log prims D _ _ P _ _ s r hr
    · intro i v l l' hpref hp
      obtain ⟨ds, hv, hc⟩ := hp
      refine ⟨ds, hv, ?_⟩
      intro hi hl T held
      obtain ⟨salt, h, d, hh, hd, idx⟩ := hc hi hl T held
      exact ⟨salt, h, d, treeStages_hashAnswer_mono hpref _ _ hh,
        treeStages_hashAnswer_mono hpref _ _ hd, idx⟩
    · intro i a u hu
      by_cases hi : i ∈ D.1
      · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hu
        subst u
        exact ⟨[], by simp [treeSimCheckWaiting, hi], fun hn => (hn hi).elim⟩
      · simp only [if_neg hi] at hu
        by_cases hl : live i = true
        · simp only [if_pos hl, treeSimResume, treeStages_saltedDigest_factor,
            simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hu
          obtain ⟨rnd, hrnd, hu⟩ := hu
          change u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
            (worldRoles.honest (advance (((compareDigests (ctx i) rnd.1.1).run
              (nextLabel (st i)) >>= k i).run)))).run rnd.2) at hu
          rw [treeSim_digest_entry (K := K), self i hi] at hu
          simp only [simulateQ_map, StateT.run_map, support_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          refine ⟨v.1, by simp [treeSimCheckWaiting, hi, hl], ?_⟩
          intro _ _ T held
          obtain ⟨h, d, hh, hd, idx⟩ := treeStages_digestQuery_log prims D i rnd.1.1
            (nextLabel (st i)).history rnd.2 v hv T held
          exact ⟨vector 256 (rnd.1.1 T), h, d, hh, hd, idx⟩
        · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hu
          subst u
          exact ⟨[], by simp [treeSimCheckWaiting, hi, hl], fun _ hh => (hl hh).elim⟩
  choose ds steps cert using certificates
  exact ⟨ds, funext steps, cert⟩

/-- A previously stopped honest party forces the actual check exchange to
stop every honest party, independently of all saved continuations. -/
theorem treeStages_check_inactive (D : C.Coalition) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true)
    (sent : C.Party → Mail C E) (i : C.Party) :
    treeSimCheckResult K D live kind sent i = none := by
  obtain ⟨j, hj, hl⟩ := stopped
  have abort : anyAbort (treeSimCheckInbox D live kind sent i) = true := by
    apply List.any_eq_true.mpr
    exact ⟨j, List.mem_finRange j, by simp [treeSimCheckInbox, hj, hl, Msg.isAbort]⟩
  simp [treeSimCheckResult, abort]

/-- The existing digest rejection criterion applies to the actual driver,
including partial entries and its transport-abort test. -/
theorem treeStages_digest_reject (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput)
    (reject : ∀ sent i, ¬ digestLive (E := E) D ds sent i)
    (sent : C.Party → Mail C E) (i : C.Party) :
    treeSimCheckResult K D live (.digests ds) sent i = none := by
  by_cases all : ∀ j, j ∉ D.1 → live j = true
  · have inbox : treeSimCheckInbox D live (.digests ds) sent i = digestInbox D ds sent i := by
      funext j
      by_cases hj : j ∈ D.1
      · simp [treeSimCheckInbox, digestInbox, hj]
      · simp [treeSimCheckInbox, digestInbox, hj, all j hj, treeSimCheckOut]
    have hr := reject sent i
    unfold treeSimCheckResult
    rw [inbox]
    change (if i ∈ D.1 then none else if live i then
      if anyAbort (digestInbox D ds sent i) then none else
        if DigestsAgree i (ds i) (digestInbox D ds sent i) then some () else none else none) = none
    unfold digestLive at hr
    split_ifs <;> first | rfl | exact False.elim (hr ⟨by assumption, by assumption⟩)
  · push_neg at all
    exact treeStages_check_inactive K D live (.digests ds) all sent i

/-- Fixed real-log certificates suffice to reject split histories. No
collision-free assumption on unlogged dealer padding is introduced. -/
theorem treeStages_split_digest_reject (D : C.Coalition) (log : TreeSimLog C)
    (histories : C.Party → C.Term → List Bit) (split : SplitHistories D histories)
    (ds : C.Party → List HashOutput)
    (recorded : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → ∃ salt h d,
      TreeSimHashAnswer log (.history (histories i T)) h ∧
      TreeSimHashAnswer log (.digest salt h) d ∧ (ds i)[C.terms.idxOf T]? = some d)
    (good : ¬ TreeSimHashCollision log) (sent : C.Party → Mail C E) (i : C.Party) :
    ¬ digestLive D ds sent i := by
  letI : SampleableType E := SampleableType.ofFintype E
  obtain ⟨T, known, j, k, hj, hk, hjT, hkT, _, different⟩ := split
  apply split_digestLive_false D ds sent T j k hj hk hjT hkT _ i
  intro equal
  obtain ⟨salt₁, h₁, d₁, hh₁, hd₁, get₁⟩ := recorded j hj T known hjT
  obtain ⟨salt₂, h₂, d₂, hh₂, hd₂, get₂⟩ := recorded k hk T known hkT
  have deq := Option.some.inj (get₁.symm.trans (equal.trans get₂))
  subst d₂
  by_cases heq : h₁ = h₂
  · subst h₂
    exact good ⟨.history (histories j T), .history (histories k T), h₁, trivial, trivial,
      (fun eq => different (Query.history.inj eq)), hh₁, hh₂⟩
  · exact good ⟨.digest salt₁ h₁, .digest salt₂ h₂, d₁, trivial, trivial,
      (fun eq => heq (Query.digest.inj eq).2), hd₁, hd₂⟩

/-- When the actual check decisions all reject, no saved continuation runs. -/
theorem treeStages_check_rejected_factor (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (k : C.Party → PartyM C E RealSpec TreeOutput)
    (reject : ∀ sent i, treeSimCheckResult K D live kind sent i = none) :
    stepRound worldRoles D A noFunctionality state (treeSimCheckWaiting K D live kind k) = (do
      let p ← worldRoles.adversary (A.round state (treeSimCheckView D live kind))
      pure (p.1, fun _ => Step.done none, p.2)) := by
  rw [treeSim_check_round_factor]
  apply bind_congr
  intro p
  have resume : treeSimResumeAll (fun i (_ : Unit) => k i) (treeSimCheckResult K D live kind p.2) =
      pure (fun _ => Step.done none) := by
    unfold treeSimResumeAll
    rw [sequenceFin_congr_pure _ (fun _ => Step.done none)
      (fun i => by rw [reject p.2 i]; rfl), free_pure]
  rw [resume, pure_bind]

/-- A complete rejected digest exchange under transported caches. The
adversary sees the common digest view and may rush adaptively; outside the
fixed salt-guess event both runs terminate without any continuation premise. -/
theorem treeStages_digest_rejected_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (reject : ∀ sent i, ¬ digestLive (E := E) D ds sent i)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeStagesDigestRel salt h h' δ a b) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live (.digests ds) k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live (.digests ds) k₂)).run b)
      (fun u z => TreeSimSaltGuess D u.2.2 ∨
        (u.1.1 = z.1.1 ∧ u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
          TreeStagesDigestRel salt h h' δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2)) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeStages_check_rejected_factor K D A state live (.digests ds) k₁
      (treeStages_digest_reject K D live ds reject),
    treeStages_check_rejected_factor K D A state live (.digests ds) k₂
      (treeStages_digest_reject K D live ds reject)]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeStages_local_digestSwap prims D salt h h' δ _ a b hidden related)
  intro u z hu
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  rcases hu with bad | good
  · exact Or.inl bad
  · exact Or.inr ⟨by rw [good.1], rfl, rfl, good.2⟩

/-- The split-history branch of the actual check is closed under the fixed
hash event. Collision-freedom is derived from that event, and all later honest
continuations are irrelevant because the real digest test rejects. -/
theorem treeStages_split_digest_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeStagesDigestRel salt h h' δ a b)
    (histories : C.Party → C.Term → List Bit) (split : SplitHistories D histories)
    (recorded : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → ∃ salt h d,
      TreeSimHashAnswer a.2 (.history (histories i T)) h ∧
      TreeSimHashAnswer a.2 (.digest salt h) d ∧ (ds i)[C.terms.idxOf T]? = some d) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live (.digests ds) k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live (.digests ds) k₂)).run b)
      (fun u z => TreeSimHashBad D u.2.2 ∨
        (u.1.1 = z.1.1 ∧ u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
          TreeStagesDigestRel salt h h' δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2)) := by
  by_cases bad : TreeSimHashBad D a.2
  · apply relTriple_of_support_left
    intro u hu z
    apply Or.inl
    apply treeSimHashBad_mono D _ bad
    apply treeSimLoggedWorld_prefix prims D
      (stepRound worldRoles D A noFunctionality state (treeSimCheckWaiting K D live (.digests ds) k₁)) a u
    simpa only [simulateQ_stepRound, treeSimRealRoles] using hu
  · have reject := treeStages_split_digest_reject (E := E) D a.2 histories split ds recorded
      (fun collision => bad (Or.inl collision))
    apply relTriple_post_mono (treeStages_digest_rejected_round prims K D A state live ds reject
      k₁ k₂ salt h h' δ a b hidden related)
    intro u z hu
    exact hu.imp (fun hit => Or.inr hit) id

/-- A transported digest cache is sufficient at the final observation: every
adaptive distinguisher either agrees or records the fixed real salt-guess event.
The selective-abort outputs, rather than the internal public caches, agree. -/
theorem treeStages_observe_digestSwap (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput)
    (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (a : TreeSimRoundOutput A (TreeSimState C))
    (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (hidden : TreeSimHiddenSalt D a.2.2 salt)
    (related : TreeStagesDigestRel salt h h' δ a.2 b.2)
    (state : a.1.1 = b.1.1)
    (outputs : a.1.2 = fun i => if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none) :
    RelTriple (treeSimRealObserve prims D A Z a) (treeSimIdealObserve prims D A Z dealt b)
      (fun x y => TreeSimSaltGuess D x.2 ∨ x.1 = y) := by
  have inputs : a.1 = (b.1.1, fun i =>
      if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none) := Prod.ext state outputs
  have hr := treeStages_local_digestSwap prims D salt h h' δ (Z a.1) a.2 b.2 hidden related
  have mapped : RelTriple
      ((fun r => (r.1, r.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary (Z a.1))).run a.2)
      (Prod.fst <$> (simulateQ (streamWorld prims D) (worldRoles.adversary (Z a.1))).run b.2)
      (fun x y => TreeSimSaltGuess D x.2 ∨ x.1 = y) := by
    apply relTriple_map
    exact relTriple_post_mono hr (fun _ _ hp => hp.imp id (fun good => good.1))
  simpa only [treeSimRealObserve, treeSimIdealObserve, treeSim_stream_adversary,
    onHash, StateT.run_mk, Functor.map_map, StateT.run'_eq, inputs] using mapped

/-- No more rounds or honest queries run after the rejected check. -/
theorem treeStages_rounds_aborted {m : Type → Type} [Monad m]
    (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) :
    executeRounds Ro D A noFunctionality fuel state
      (fun _ => (.done none : Step C E RealSpec TreeOutput)) = pure (state, fun _ => none) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [executeRounds, Step.isDone, Step.output]

/-- A forced check rejection closes the whole remaining ceremony exactly
under the ordinary stream relation, including the final distinguisher. -/
theorem treeStages_check_rejected_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput) (fuel : ℕ)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (reject : ∀ sent i, treeSimCheckResult K D live kind sent i = none)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) :
    RelTriple
      (((executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind k₁)).run a) >>= treeSimRealObserve prims D A Z)
      (((executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind k₂)).run b) >>= treeSimIdealObserve prims D A Z dealt)
      (fun x y => x.1 = y) := by
  have outputs (k : C.Party → PartyM C E RealSpec TreeOutput) :
      (fun i => (treeSimCheckWaiting K D live kind k i).output) = fun _ => none := by
    funext i
    unfold treeSimCheckWaiting
    split_ifs <;> rfl
  have finish : RelTriple
      (treeSimRealObserve prims D A Z ((state, fun _ => none), a))
      (treeSimIdealObserve prims D A Z dealt ((state, fun _ => none), b))
      (fun x y => x.1 = y) :=
    treeSim_observe_good prims D A Z dealt _ _ ⟨rfl, related.1, by funext i; simp⟩
  cases fuel with
  | zero => simpa only [executeRounds, StateT.run_pure, pure_bind, outputs] using finish
  | succ fuel =>
    have done : AllDone D (treeSimCheckWaiting K D live kind k₁) ↔
        AllDone D (treeSimCheckWaiting K D live kind k₂) := by
      unfold AllDone
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      simp only [treeSimCheckWaiting, if_neg hi]
      by_cases hl : live i = true <;> simp [hl, treeSimCheckStep, Step.isDone]
    by_cases stopped : AllDone D (treeSimCheckWaiting K D live kind k₁)
    · rw [executeRounds_succ, if_pos stopped, executeRounds_succ, if_pos (done.mp stopped)]
      simpa only [StateT.run_pure, pure_bind, outputs] using finish
    · rw [executeRounds_succ, if_neg stopped, executeRounds_succ, if_neg (fun h => stopped (done.mpr h))]
      have round : RelTriple
          ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
            (treeSimCheckWaiting K D live kind k₁)).run a)
          ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
            (treeSimCheckWaiting K D live kind k₂)).run b)
          (fun u z => u.1.1 = z.1.1 ∧ u.1.2.1 = (fun _ => .done none) ∧
            z.1.2.1 = (fun _ => .done none) ∧ TreeSimStreamRel δ u.2 z.2) := by
        simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
        rw [treeStages_check_rejected_factor K D A state live kind k₁ reject,
          treeStages_check_rejected_factor K D A state live kind k₂ reject]
        simp only [simulateQ_bind, StateT.run_bind]
        apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b related)
        intro u z hu
        simp only [simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨by rw [hu.1], rfl, rfl, hu.2.1⟩
      simp only [StateT.run_bind, bind_assoc]
      apply relTriple_bind round
      intro u z hu
      rw [hu.2.1, hu.2.2.1, treeStages_rounds_aborted, treeStages_rounds_aborted]
      simp only [StateT.run_pure, pure_bind]
      exact treeSim_observe_good prims D A Z dealt _ _
        ⟨hu.1, hu.2.2.2.1, by funext i; simp⟩

/-- The complete suffix from a split-history check, including all remaining
fuel and the actual final distinguisher. This needs neither a continuation
coupling nor equality of the two public caches. -/
theorem treeStages_split_digest_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput) (fuel : ℕ)
    (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (active : ∃ i, i ∉ D.1 ∧ live i = true)
    (salt : List Bit) (h h' : HashOutput) (δ : HiddenAddress C → Bit)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hidden : TreeSimHiddenSalt D a.2 salt) (related : TreeStagesDigestRel salt h h' δ a b)
    (histories : C.Party → C.Term → List Bit) (split : SplitHistories D histories)
    (recorded : ∀ i, i ∉ D.1 → ∀ T, KnownTo D.1 T → i ∈ C.holders T → ∃ salt h d,
      TreeSimHashAnswer a.2 (.history (histories i T)) h ∧
      TreeSimHashAnswer a.2 (.digest salt h) d ∧ (ds i)[C.terms.idxOf T]? = some d) :
    RelTriple
      (((executeRounds (treeSimRealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCheckWaiting K D live (.digests ds) k₁)).run a) >>= treeSimRealObserve prims D A Z)
      (((executeRounds (treeSimIdealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCheckWaiting K D live (.digests ds) k₂)).run b) >>= treeSimIdealObserve prims D A Z dealt)
      (fun x y => TreeSimHashBad D x.2 ∨ x.1 = y) := by
  have running (k : C.Party → PartyM C E RealSpec TreeOutput) :
      ¬ AllDone D (treeSimCheckWaiting K D live (.digests ds) k) := by
    obtain ⟨i, hi, hl⟩ := active
    intro done
    have impossible := done i hi
    simpa [treeSimCheckWaiting, hi, hl, treeSimCheckStep, Step.isDone] using impossible
  rw [executeRounds_succ, if_neg (running k₁), executeRounds_succ, if_neg (running k₂)]
  simp only [StateT.run_bind, bind_assoc]
  apply relTriple_bind (treeSim_relTriple_support
    (treeStages_split_digest_round prims K D A state live ds k₁ k₂ salt h h' δ a b
      hidden related histories split recorded))
  intro u z hu
  rcases hu.1 with bad | good
  · apply relTriple_of_support_left
    intro x hx y
    apply Or.inl
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨v, hv, hx⟩ := hx
    apply treeSimHashBad_mono D _ bad
    apply List.IsPrefix.trans (treeSimLoggedWorld_prefix prims D
      (executeRounds worldRoles D A noFunctionality fuel u.1.1 u.1.2.1) u.2 v ?_)
    · exact treeSim_observe_prefix prims D A Z v x hx
    · simpa only [simulateQ_executeRounds, treeSimRealRoles] using hv
  · rw [good.2.1, good.2.2.1, treeStages_rounds_aborted, treeStages_rounds_aborted]
    simp only [StateT.run_pure, pure_bind]
    apply relTriple_post_mono (treeStages_observe_digestSwap prims D A Z dealt salt h h' δ
      ((u.1.1, fun _ => none), u.2) ((z.1.1, fun _ => none), z.2)
      (treeStages_hiddenSalt_mono D salt (treeSimLoggedWorld_prefix prims D
        (stepRound worldRoles D A noFunctionality state (treeSimCheckWaiting K D live (.digests ds) k₁))
        a u (by simpa only [simulateQ_stepRound, treeSimRealRoles] using hu.2.1)) hidden)
      good.2.2.2.1 good.1 (by funext i; simp))
    intro x y hx
    exact hx.imp (fun hit => Or.inr hit) id

/-- An active digest waiter determines its broadcast digest list. The
nontrivial committee premise follows automatically from split histories. -/
theorem treeStages_digest_waiting_injective (D : C.Coalition)
    (large : 2 ≤ C.n) (live : C.Party → Bool) (i : C.Party) (hi : i ∉ D.1)
    (hl : live i = true) (ds ds' : C.Party → List HashOutput)
    (k : C.Party → PartyM C E RealSpec TreeOutput)
    (eq : treeSimCheckWaiting K D live (.digests ds) k i =
      treeSimCheckWaiting K D live (.digests ds') k i) : ds i = ds' i := by
  let zero : C.Party := ⟨0, by omega⟩
  let one : C.Party := ⟨1, by omega⟩
  have different : one ≠ zero := by intro e; have := congrArg Fin.val e; simp [one, zero] at this
  obtain ⟨j, hj⟩ : ∃ j : C.Party, j ≠ i := by
    by_cases h : i = zero
    · exact ⟨one, by simpa [h] using different⟩
    · exact ⟨zero, Ne.symm h⟩
  have sent := congrArg (fun v => v.outbox j) eq
  simpa [treeSimCheckWaiting, hi, hl, treeSimCheckStep, Step.outbox,
    treeSimCheckOut, digestOutbox, hj] using sent

/-- The entire split-history suffix of the actual salted check: shared PRSS
salt draws, both digest hash levels in driver order, the rushing adversary,
selective abort, remaining fuel and the final distinguisher. Hash certificates
are derived from the execution. No later continuation coupling is assumed. -/
theorem treeStages_saltedDigest_split_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput) (fuel : ℕ)
    (live : C.Party → Bool) (label : ℕ) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (history : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      (st₁ i).history T = (st₂ i).history T)
    (split : SplitHistories D (fun i => (st₁ i).history))
    (k₁ k₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (future : TreeSimFutureZero label δ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty label a.1.2) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
          (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx₁ i)).run (st₁ i) >>= k₁ i)
          (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a >>= fun u =>
        (executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel state u.1).run u.2 >>=
          treeSimRealObserve prims D A Z)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll
          (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx₂ i)).run (st₂ i) >>= k₂ i)
          (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b >>= fun u =>
        (executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel state u.1).run u.2 >>=
          treeSimIdealObserve prims D A Z dealt)
      (fun x y => TreeSimHashBad D x.2 ∨ x.1 = y) := by
  apply relTriple_bind (treeSim_relTriple_support
    (treeStages_saltedDigest_partial_entry prims K D live label ctx₁ ctx₂ self₁ self₂ keys
      st₁ st₂ lab₁ lab₂ history k₁ k₂ δ visible future a b related fresh))
  intro u z hu
  by_cases bad : TreeSimHashBad D u.2.2
  · apply relTriple_of_support_left
    intro x hx y
    apply Or.inl
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨v, hv, hx⟩ := hx
    apply treeSimHashBad_mono D _ bad
    apply List.IsPrefix.trans (treeSimLoggedWorld_prefix prims D
      (executeRounds worldRoles D A noFunctionality fuel state u.1) u.2 v ?_)
    · exact treeSim_observe_prefix prims D A Z v x hx
    · simpa only [simulateQ_executeRounds, treeSimRealRoles] using hv
  · obtain ⟨⟨ds, steps₁, steps₂⟩, hc, _⟩ := hu.1
    obtain ⟨actual, steps, certificates⟩ := treeStages_saltedDigest_partial_log prims K D live
      ctx₁ self₁ st₁ k₁ a u hu.2.1
    have same : ∀ i, i ∉ D.1 → live i = true → ds i = actual i := by
      intro i hi hl
      exact treeStages_digest_waiting_injective K D split.two_le_n live i hi hl ds actual _
        (congrFun (steps₁.symm.trans steps) i)
    have reject : ∀ sent i, treeSimCheckResult K D live (.digests ds) sent i = none := by
      by_cases inactive : ∃ i, i ∉ D.1 ∧ live i ≠ true
      · exact fun sent i => treeStages_check_inactive K D live (.digests ds) inactive sent i
      · have allLive : ∀ i, i ∉ D.1 → live i = true := by
          intro i hi
          by_contra hn
          exact inactive ⟨i, hi, hn⟩
        apply treeStages_digest_reject K D live ds
        apply treeStages_split_digest_reject D u.2.2 (fun i => (st₁ i).history) split ds
        · intro i hi T _ held
          rw [same i hi (allLive i hi)]
          exact certificates i hi (allLive i hi) T held
        · exact fun collision => bad (Or.inl collision)
    rw [steps₁, steps₂]
    apply relTriple_post_mono
      (treeStages_check_rejected_finish prims K D A state Z dealt fuel live (.digests ds)
        (fun i => k₁ i ((), nextLabel (st₁ i)))
        (fun i => k₂ i ((), nextLabel (st₂ i))) reject δ u.2 z.2 hc)
    intro x y he
    exact Or.inr he

/-- Coverage of the finite copy-query domain for a batch length. Prefix
padding can establish this without predicting any private mask or output. -/
def TreeStagesCopyCovered (count : ℕ) (cache : HashCache C) : Prop :=
  ∀ v : Fin count → Bit, ∃ h, cache (.copy (List.ofFn v)) = some h

def treeStagesCopyDigests (count : ℕ) (cache : HashCache C) (v : Shares C Bit) : List HashOutput :=
  C.terms.map fun T => (cache (.copy (vector count (v T)))).getD 0

theorem treeStages_copy_covered_vector (count : ℕ) (cache : HashCache C)
    (covered : TreeStagesCopyCovered count cache) (v : ℕ → Bit) :
    cache (.copy (vector count v)) = some ((cache (.copy (vector count v))).getD 0) := by
  have shape : List.ofFn (fun i : Fin count => v i) = vector count v := by
    apply List.ext_getElem
    · simp [vector]
    · intro i hi hj
      simp [vector]
  obtain ⟨h, hh⟩ := covered (fun i => v i)
  rw [shape] at hh
  simp [hh]

/-- All actual copy calls, including unused unheld copies, replay the padded
cache. Their order and returned list are unchanged. -/
theorem treeStages_copyHashes_run (count : ℕ) (cache : HashCache C) (v : Shares C Bit)
    (covered : TreeStagesCopyCovered count cache) :
    (C.terms.mapM (fun T => hashAnswer prims (.copy (vector count (v T))))).run cache =
      pure (treeStagesCopyDigests count cache v, cache) := by
  have cached := fun T => treeStages_copy_covered_vector count cache covered (v T)
  unfold treeStagesCopyDigests
  generalize C.terms = terms
  induction terms with
  | nil => rfl
  | cons T terms ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure,
      hashAnswer_run_cached prims (by rintro ⟨_, heq, _⟩; cases heq) (cached T),
      pure_bind, ih, List.map_cons]

/-- Cached digests of held copies are all that occur in an outgoing opening
bundle. The owner-membership invariant also covers the clear copies. -/
theorem treeStages_openOut_cached_congr (i : C.Party) (count : ℕ)
    (cache : HashCache C) (v w : Shares C Bit)
    (held : ∀ T, i ∈ C.holders T → v T = w T) :
    treeSimOpenOut K i count v (treeStagesCopyDigests count cache v) =
      treeSimOpenOut K i count w (treeStagesCopyDigests count cache w) := by
  funext j
  unfold treeSimOpenOut
  split_ifs with hj
  · rfl
  · congr 2
    simp only [List.cons.injEq, Msg.bits.injEq, Msg.hashes.injEq, and_true]
    constructor
    · apply List.flatMap_congr
      intro T hT
      have owner : K.owner T = i := (List.mem_filter.mp hT).2 |> of_decide_eq_true |> And.right
      rw [held T (owner ▸ K.owner_held T)]
    · unfold treeStagesCopyDigests
      rw [← List.map_prod_left_eq_zip, ← List.map_prod_left_eq_zip]
      simp only [List.filterMap_map]
      congr 1
      funext T
      dsimp only [Function.comp_apply]
      split_ifs with ht
      · rw [held T ht.2.1]
      · rfl

/-- Copy prefetching installs all requested strings and preserves prior
public answers. It may start from the dealer's populated cache. -/
theorem treeStages_prefetch_copies {α : Type} (xs : List α) (bits : α → List Bit)
    (cache : HashCache C) (r : List HashOutput × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (xs.mapM fun x => liftComp (hashQuery (C := C) (.copy (bits x))) (LocalSpec C))).run cache)) :
    cache ≤ r.2 ∧ ∀ x ∈ xs, ∃ h, r.2 (.copy (bits x)) = some h := by
  induction xs generalizing cache r with
  | nil =>
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl, by simp⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    rw [simulateQ_localAnswer_hash] at hu
    have head := hashAnswer_cached prims (by rintro ⟨_, heq, _⟩; cases heq) cache u hu
    obtain ⟨grows, tail⟩ := ih u.2 v hv
    refine ⟨(grows_hashAnswer prims _ cache u hu).trans grows, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨u.1, grows head⟩
    · exact tail y hy

/-- A finite, unobserved prefix suitable for the frozen core's padding slot.
Its size is irrelevant to the counted adversary; it is used only by the exact
prefetch identity already proved in `TreeSim`. -/
def treeStagesCopyPadding (count : ℕ) : OracleComp (LocalSpec C) Unit := do
  let _ ← (Finset.univ : Finset (Fin count → Bit)).toList.mapM fun v =>
    liftComp (hashQuery (C := C) (.copy (List.ofFn v))) (LocalSpec C)
  pure ()

theorem treeStages_copyPadding_covered (count : ℕ) (cache : HashCache C)
    (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (treeStagesCopyPadding (C := C) count)).run cache)) :
    cache ≤ r.2 ∧ TreeStagesCopyCovered count r.2 := by
  simp only [treeStagesCopyPadding, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  obtain ⟨hg, hc⟩ := treeStages_prefetch_copies prims _ List.ofFn cache u hu
  exact ⟨hg, fun v => hc v (by simp)⟩

/-- Padding coverage survives every actual ceremony query, including hashes
and private PRSS calls. -/
theorem treeStages_copyCovered_mono (count : ℕ) {a b : HashCache C} (h : a ≤ b)
    (covered : TreeStagesCopyCovered count a) : TreeStagesCopyCovered count b := by
  intro v
  obtain ⟨digest, hd⟩ := covered v
  exact ⟨digest, h hd⟩

/-- A supported opening entry has a completely determined output and
unchanged caches when the copy domain is covered. The real query log remains. -/
theorem treeStages_open_entry_cached (D : C.Coalition) (ctx : Context C) (count : ℕ)
    (v : Shares C Bit) (k : (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (s : HashCache C × HiddenCache C) (covered : TreeStagesCopyCovered count s.1) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((openRep K ctx v count >>= k).run)))).run s =
      pure (treeSimOpenStep K ctx.self count v (treeStagesCopyDigests count s.1 v) k, s) := by
  rw [treeSim_open_entry]
  simp only [simulateQ_map, StateT.run_map]
  have hash := treeSim_hashes_onHash prims D (C.terms.map fun T => Query.copy (vector count (v T)))
  simp only [List.mapM_map, Function.comp_def] at hash
  rw [show treeSimOpenCopyHashes count v = C.terms.mapM (fun T => hashQuery (.copy (vector count (v T)))) from rfl,
    hash]
  simp only [onHash, StateT.run_mk, treeStages_copyHashes_run prims count s.1 v covered,
    map_pure]

/-- The actual T₀-corrected opening entry couples without any unused-copy
assumption. Both sets of copy queries replay the finite padded domain. -/
theorem treeStages_open_entry_padded (D : C.Coalition) (i : C.Party)
    (ctx₁ ctx₂ : Context C) (self₁ : ctx₁.self = i) (self₂ : ctx₂.self = i)
    (count : ℕ) (v w : Shares C Bit) (held : ∀ T, i ∈ C.holders T → v T = w T)
    (k₁ k₂ : (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered count a.1.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest
        (advance ((openRep K ctx₁ v count >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest
        (advance ((openRep K ctx₂ w count >>= k₂).run)))).run b)
      (fun u z =>
        u.1 = treeSimOpenStep K i count v (treeStagesCopyDigests count a.1.1 v) k₁ ∧
        z.1 = treeSimOpenStep K i count v (treeStagesCopyDigests count a.1.1 v) k₂ ∧
        u.2.1 = a.1 ∧ z.2 = b ∧ TreeSimStreamRel δ u.2 z.2) := by
  have left : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest
      (advance ((openRep K ctx₁ v count >>= k₁).run)))).run a),
      u.1 = treeSimOpenStep K i count v (treeStagesCopyDigests count a.1.1 v) k₁ ∧ u.2.1 = a.1 := by
    intro u hu
    have erased : (u.1, u.2.1) ∈ support ((simulateQ (streamWorld prims D) (worldRoles.honest
        (advance ((openRep K ctx₁ v count >>= k₁).run)))).run a.1) := by
      rw [← treeSimLoggedWorld_erase prims D _ a.1 a.2, support_map]
      exact ⟨u, hu, rfl⟩
    rw [treeStages_open_entry_cached prims K D ctx₁ count v k₁ a.1 covered] at erased
    simpa only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, self₁] using erased
  have idealCovered : TreeStagesCopyCovered count b.1 := by rw [← related.1]; exact covered
  rw [treeStages_open_entry_cached prims K D ctx₂ count w k₂ b idealCovered]
  have step : treeSimOpenStep K ctx₂.self count w (treeStagesCopyDigests count b.1 w) k₂ =
      treeSimOpenStep K i count v (treeStagesCopyDigests count a.1.1 v) k₂ := by
    rw [self₂, ← related.1]
    exact (treeSim_openStep_congr K i count v w _ _ k₂ held
      (treeStages_openOut_cached_congr K i count a.1.1 v w held)).symm
  rw [step]
  apply relTriple_post_mono (treeSim_relTriple_support (relTriple_true _ _))
  intro u z hz
  obtain ⟨ho, hs⟩ := left u hz.2.1
  have heq := hz.2.2
  simp only [support_pure, Set.mem_singleton_iff] at heq
  subst z
  exact ⟨ho, rfl, hs, rfl, by simpa only [TreeSimStreamRel, hs] using related⟩

/-- OpenRep entry for the driver's actual optional continuations. Padding
covers unused copies on both sides; held copies and outgoing bundles agree. -/
theorem treeStages_open_partial_padded (D : C.Coalition) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (v w : C.Party → Shares C Bit)
    (held : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → v i T = w i T)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered count a.1.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => openRep K (ctx₁ i) (v i) count >>= k₁ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => openRep K (ctx₂ i) (w i) count >>= k₂ i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b)
      (fun u z =>
        u.1 = treeSimOpenPartial K D live count v (fun i => treeStagesCopyDigests count a.1.1 (v i)) k₁ ∧
        z.1 = treeSimOpenPartial K D live count v (fun i => treeStagesCopyDigests count a.1.1 (v i)) k₂ ∧
        u.2.1 = a.1 ∧ z.2 = b ∧ TreeSimStreamRel δ u.2 z.2) := by
  let J := fun s t => s.1 = a.1 ∧ t = b ∧ TreeSimStreamRel δ s t
  let Q := fun i x y =>
    x = treeSimOpenPartial K D live count v (fun j => treeStagesCopyDigests count a.1.1 (v j)) k₁ i ∧
    y = treeSimOpenPartial K D live count v (fun j => treeStagesCopyDigests count a.1.1 (v j)) k₂ i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ _ _ J Q ?_ a b ⟨rfl, rfl, related⟩)
  · intro u z hu
    exact ⟨funext (fun i => (hu.1 i).1), funext (fun i => (hu.1 i).2), hu.2⟩
  · intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨by simp [treeSimOpenPartial, hi],
        by simp [treeSimOpenPartial, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume]
        apply relTriple_post_mono (treeStages_open_entry_padded prims K D i (ctx₁ i) (ctx₂ i)
          (self₁ i hi) (self₂ i hi) count (v i) (w i) (held i hi hl) (k₁ i) (k₂ i)
          δ s t hst.2.2 (by rw [hst.1]; exact covered))
        intro u z hu
        refine ⟨⟨?_, ?_⟩, hu.2.2.1.trans hst.1, hu.2.2.2.1.trans hst.2.1, hu.2.2.2.2⟩
        · simpa only [treeSimOpenPartial, if_neg hi, if_pos hl, hst.1] using hu.1
        · simpa only [treeSimOpenPartial, if_neg hi, if_pos hl, hst.1] using hu.2.1
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨by simp [treeSimOpenPartial, hi, hl],
          by simp [treeSimOpenPartial, hi, hl]⟩, hst⟩

/-- The real final-check exchange followed by the actual OpenRep prefix.
The adversary may rush and select aborts; no continuation coupling is assumed. -/
theorem treeStages_check_open_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (v w : C.Party → Shares C Bit)
    (held : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → v i T = w i T)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered count a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) count >>= k₁ i))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₂ i) (w i) count >>= k₂ i))).run b)
      (fun u z => ∃ sent ds,
        let active := fun i => (treeSimCheckResult K D live kind sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimOpenPartial K D active count v ds k₁ ∧
        z.1.2.1 = treeSimOpenPartial K D active count v ds k₂ ∧
        TreeSimStreamRel δ u.2 z.2 ∧ TreeStagesCopyCovered count u.2.1.1 ∧
        u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_check_round_factor, treeSim_check_round_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D δ _ a b related))
  intro u z hu
  have hc := hu.1
  have cover := treeStages_copyCovered_mono count
    (treeSim_logged_grows prims D _ a u hu.2.1) covered
  rw [← hc.1]
  let active := fun i => (treeSimCheckResult K D live kind u.1.2 i).isSome
  have shape : treeSimCheckResult K D live kind u.1.2 =
      fun i => if i ∈ D.1 then none else if active i then some () else none := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCheckResult, hi]
    · rw [if_neg hi]
      cases hv : treeSimCheckResult K D live kind u.1.2 i <;> simp [active, hv]
  rw [shape]
  apply relTriple_bind (treeStages_open_partial_padded prims K D active ctx₁ ctx₂ self₁ self₂
    count v w (fun i hi _ => held i hi) k₁ k₂ δ u.2 z.2 hc.2.1 cover)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  refine ⟨u.1.2, (fun i => treeStagesCopyDigests count u.2.1.1 (v i)),
    rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2.2.2, ?_, ?_, ?_⟩
  · simpa only [hp.2.2.1] using cover
  · exact (congrArg Prod.snd hp.2.2.1).trans hc.2.2.1
  · exact (congrArg Prod.snd hp.2.2.2.1).trans hc.2.2.2

/-- A final-check waiter depends only on its own three-element vector.
Previously aborted and corrupt operators do not expose that vector. -/
theorem treeStages_check_opening_congr (D : C.Coalition) (live : C.Party → Bool)
    (v w : C.Party → ℕ → E) (k : C.Party → PartyM C E RealSpec TreeOutput)
    (same : ∀ i, i ∉ D.1 → live i = true → v i = w i) :
    treeSimCheckWaiting K D live (.opening v) k = treeSimCheckWaiting K D live (.opening w) k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCheckWaiting, hi]
  · by_cases hl : live i = true
    · simp [treeSimCheckWaiting, hi, hl, treeSimCheckStep, treeSimCheckOut,
        TreeSimCheckAccept, same i hi hl]
    · simp [treeSimCheckWaiting, hi, hl]

/-- The GS20 final-mask bijection aligns the actual last check exchange;
the simulator's T₀ correction then cancels the internal bit-share shift at
OpenRep entry. Copy padding accounts for every unheld query as well. The
triangular table translation and its algebraic compatibility are explicit;
there is no hypothesis coupling the adversary or any later continuation. -/
theorem treeStages_finalMask_open_round (D : C.Coalition)
    (Adv : Adversary C E (Keys C) PEmpty PEmpty) (state : Adv.State)
    (live : C.Party → Bool) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (T₀ : C.Term) (hidden : ¬ KnownTo D.1 T₀)
    (r : E) (delta : MaskTable C E) (deltaD : C.Term → E)
    (A B V A' B' V' : C.Party → E) (w q : MaskTable C E)
    (hr : 1 + r ≠ 0) (knownDelta : ∀ T, KnownTo D.1 T → ∀ g, delta T g = 0)
    (knownD : ∀ T, KnownTo D.1 T → deltaD T = 0)
    (compat : (1+r)*maskedResultDelta K D known attack r delta w A B A' B' 0 +
      r*(∑ T, deltaD T) + r*(1+r)*maskedResultDelta K D known attack r delta w A B A' B' 1 = 0)
    (rec : ∀ i, i ∉ D.1 → live i = true → i ∈ receivers)
    (localA : ∀ i, i ∉ D.1 → live i = true → A i - A' i =
      conv K (localContext i) (fun T _ => delta T 0) 0)
    (localB : ∀ i, i ∉ D.1 → live i = true → B i - B' i =
      conv K (localContext i) (fun T _ => delta T 1) 0)
    (localD : ∀ i, i ∉ D.1 → live i = true → V i - V' i =
      conv K (localContext i) (fun T _ => deltaD T) 0)
    (count : ℕ) (difference : ℕ → Bit) (v : C.Party → Shares C Bit)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered count a.1.1) :
    let field₁ := finalMaskVector K D known knownQ attack offset receivers r A B V w q
    let field₂ := finalMaskVector K D known knownQ attack offset receivers r A' B' V'
      (maskTableEquiv r delta w)
      (finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD q)
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D Adv noFunctionality state
        (treeSimCheckWaiting K D live (.opening field₁)
          (fun i => openRep K (ctx₁ i) (v i) count >>= k₁ i))).run a)
      ((stepRound (treeSimIdealRoles prims D) D Adv noFunctionality state
        (treeSimCheckWaiting K D live (.opening field₂) (fun i => openRep K (ctx₂ i)
          (treeSimShift D (treeSimHeldShift D i count difference (v i))
            (fun g => if g < count then difference g else 0)) count >>= k₂ i))).run b)
      (fun u z => ∃ sent ds,
        let active := fun i => (treeSimCheckResult K D live (.opening field₁) sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimOpenPartial K D active count v ds k₁ ∧
        z.1.2.1 = treeSimOpenPartial K D active count v ds k₂ ∧
        TreeSimStreamRel δ u.2 z.2 ∧ TreeStagesCopyCovered count u.2.1.1 ∧
        u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  letI : SampleableType E := SampleableType.ofFintype E
  dsimp only
  have same : ∀ i, i ∉ D.1 → live i = true →
      finalMaskVector K D known knownQ attack offset receivers r A' B' V'
        (maskTableEquiv r delta w)
        (finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD q) i =
      finalMaskVector K D known knownQ attack offset receivers r A B V w q i := by
    intro i hi hl
    exact (finalMaskVector_bijection K D known knownQ attack offset receivers T₀ hidden r delta deltaD
      A B V A' B' V' w q hr knownDelta knownD compat i hi (rec i hi hl)
      (localA i hi hl) (localB i hi hl) (localD i hi hl)).symm
  rw [treeStages_check_opening_congr K D live _ _ _ same]
  apply treeStages_check_open_round prims K D Adv state live _ ctx₁ ctx₂ self₁ self₂
    count v _ _ k₁ k₂ δ a b related covered
  intro i _ T hT
  exact (treeSim_open_shift_held D i count difference (v i) T hT).symm

/-- The terminal OpenRep exchange runs the real copy checks and then
returns the same per-party output in both executions. The claim permits
inconsistent malicious messages and selective abort; it does not assume the
opened values are correct or that different honest parties agree. -/
theorem treeStages_open_terminal_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (f : C.Party → (ℕ → Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out => pure (f i out)))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out => pure (f i out)))).run b)
      (fun u z => u.1 = z.1 ∧ (∀ i, (u.1.2.1 i).isDone) ∧ u.2.1.1 = z.2.1) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [stepRound_real]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b related)
  intro u z hu
  rw [← hu.1]
  let close := TreeSimOpenLocalClosure.terminal prims K D live count v ds u.1.2 f f
  apply relTriple_bind (close.all prims K D live count v ds u.1.2 _ _ u.2 z.2 hu.2.1.1)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  have steps : ∀ i, p.1 i = q.1 i ∧ (p.1 i).isDone := by
    intro i
    rcases hp.1 i with abort | ⟨out, h₁, h₂⟩
    · exact ⟨abort.1.trans abort.2.symm, by rw [abort.1]; trivial⟩
    · exact ⟨h₁.trans h₂.symm, by rw [h₁]; trivial⟩
  exact ⟨by rw [funext (fun i => (steps i).1)], fun i => (steps i).2, hp.2⟩

/-- A fully stopped vector is returned unchanged at every fuel value. -/
theorem treeStages_rounds_done {m : Type → Type} [Monad m]
    (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec TreeOutput)
    (done : ∀ i, (steps i).isDone) :
    executeRounds Ro D A noFunctionality fuel state steps = pure (state, fun i => (steps i).output) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [executeRounds_succ, if_pos (show AllDone D steps from fun i _ => done i)]

/-- The complete terminal opening suffix, respecting actual driver stopping
and arbitrary remaining fuel. It preserves the adversary state, every returned
option, and the public cache, without assuming output correctness. -/
theorem treeStages_open_terminal_rounds (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (f : C.Party → (ℕ → Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel state
        (treeSimOpenPartial K D live count v ds (fun i out => pure (f i out)))).run a)
      ((executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel state
        (treeSimOpenPartial K D live count v ds (fun i out => pure (f i out)))).run b)
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1) := by
  cases fuel with
  | zero =>
    simp only [executeRounds, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, related.1⟩
  | succ fuel =>
    rw [executeRounds_succ, executeRounds_succ]
    split_ifs with stopped
    · simp only [StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, related.1⟩
    · simp only [StateT.run_bind]
      apply relTriple_bind (treeStages_open_terminal_round prims K D A state live count v ds f δ a b related)
      intro u z hu
      have rightDone : ∀ i, (z.1.2.1 i).isDone := by rw [← hu.1]; exact hu.2.1
      rw [treeStages_rounds_done _ D A fuel _ _ hu.2.1,
        treeStages_rounds_done _ D A fuel _ _ rightDone]
      simp only [StateT.run_pure]
      exact relTriple_pure_pure ⟨by rw [hu.1], hu.2.2⟩

/-- A complete final-check/OpenRep suffix using the real two exchanges and
all copy hashes. Honest held shares may differ internally before correction;
only the corrected held copies must agree. -/
theorem treeStages_check_open_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (v w : C.Party → Shares C Bit)
    (held : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → v i T = w i T)
    (f : C.Party → (ℕ → Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered count a.1.1) :
    RelTriple
      ((executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) count >>= fun out => pure (f i out)))).run a)
      ((executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₂ i) (w i) count >>= fun out => pure (f i out)))).run b)
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1) := by
  have outputs (k : C.Party → PartyM C E RealSpec TreeOutput) :
      (fun i => (treeSimCheckWaiting K D live kind k i).output) = fun _ => none := by
    funext i
    unfold treeSimCheckWaiting
    split_ifs <;> rfl
  cases fuel with
  | zero =>
    simp only [executeRounds, StateT.run_pure, outputs]
    exact relTriple_pure_pure ⟨rfl, related.1⟩
  | succ fuel =>
    have done (k : C.Party → PartyM C E RealSpec TreeOutput) :
        AllDone D (treeSimCheckWaiting K D live kind k) ↔ ∀ i, i ∉ D.1 → live i ≠ true := by
      unfold AllDone
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      by_cases hl : live i = true <;>
        simp [treeSimCheckWaiting, hi, hl, treeSimCheckStep, Step.isDone]
    rw [executeRounds_succ, executeRounds_succ, done, done]
    split_ifs with stopped
    · simp only [StateT.run_pure, outputs]
      exact relTriple_pure_pure ⟨rfl, related.1⟩
    · simp only [StateT.run_bind]
      apply relTriple_bind (treeStages_check_open_round prims K D A state live kind ctx₁ ctx₂
        self₁ self₂ count v w held (fun i out => pure (f i out)) (fun i out => pure (f i out))
        δ a b related covered)
      intro u z hu
      obtain ⟨sent, ds, stateEq, _, _, steps₁, steps₂, hc, _⟩ := hu
      rw [steps₁, steps₂, ← stateEq]
      exact treeStages_open_terminal_rounds prims K D A u.1.1 fuel _ count v ds f δ u.2 z.2 hc

/-- Factor the actual replicated opening without discarding its initial
or reconstructed-copy hashes. -/
theorem treeStages_openRep_factor {α : Type} (ctx : Context C) (count : ℕ)
    (v : Shares C Bit) (k : (ℕ → Bit) → PartyM C E RealSpec α) :
    (openRep K ctx v count >>= k) = (do
      let ds ← oracleStep (treeSimOpenCopyHashes count v)
      let inbox ← exchange (treeSimOpenOut K ctx.self count v ds)
      let copy := treeSimOpenCopy K ctx.self count v inbox
      let hashes ← oracleStep (treeSimOpenCopyHashes count copy)
      require (TreeSimOpenValid K ctx.self inbox hashes)
      k (fun g => ∑ T, copy T g)) := by
  simp only [openRep, bind_assoc, pure_bind]
  rfl

/-- Every outgoing bit and every copy hash reads only the requested prefix.
This includes the initial hashes of unheld copies. -/
theorem treeStages_openOut_prefix (i : C.Party) (count : ℕ) (v w : Shares C Bit)
    (same : ∀ T g, g < count → v T g = w T g) (ds : List HashOutput) :
    treeSimOpenOut K i count v ds = treeSimOpenOut K i count w ds := by
  have hv : ∀ T, vector count (v T) = vector count (w T) :=
    fun T => vector_congr' count _ _ (same T)
  funext j
  unfold treeSimOpenOut
  simp_rw [hv]

theorem treeStages_openHashes_prefix (count : ℕ) (v w : Shares C Bit)
    (same : ∀ T g, g < count → v T g = w T g) :
    treeSimOpenCopyHashes count v = treeSimOpenCopyHashes count w := by
  have hv : ∀ T, vector count (v T) = vector count (w T) :=
    fun T => vector_congr' count _ _ (same T)
  simp only [treeSimOpenCopyHashes, hv]

/-- Actual OpenRep programs agree for bounded consumers even when their
unbounded share functions have different tails. This is a program equality,
so it also applies inside saved ceremony continuations. -/
theorem treeStages_openRep_prefix {α : Type} (ctx : Context C) (count : ℕ)
    (v w : Shares C Bit) (same : ∀ T g, g < count → v T g = w T g)
    (k : (ℕ → Bit) → PartyM C E RealSpec α)
    (consume : ∀ x y, (∀ g, g < count → x g = y g) → k x = k y) :
    (openRep K ctx v count >>= k) = (openRep K ctx w count >>= k) := by
  rw [treeStages_openRep_factor, treeStages_openRep_factor,
    treeStages_openHashes_prefix count v w same]
  apply bind_congr
  intro ds
  rw [treeStages_openOut_prefix K ctx.self count v w same ds]
  apply bind_congr
  intro inbox
  have copied : ∀ T g, g < count →
      treeSimOpenCopy K ctx.self count v inbox T g = treeSimOpenCopy K ctx.self count w inbox T g := by
    intro T g hg
    unfold treeSimOpenCopy
    split_ifs
    · exact same T g hg
    · rfl
  dsimp only
  rw [treeStages_openHashes_prefix count _ _ copied]
  apply bind_congr
  intro hashes
  apply congrArg (fun p => require (TreeSimOpenValid K ctx.self inbox hashes) >>= fun _ => p)
  apply consume
  intro g hg
  exact Finset.sum_congr rfl (fun T _ => copied T g hg)

/-- The simulator's actual unbounded T₀ correction is identical to its
bounded correction throughout every queried or emitted copy string. -/
theorem treeStages_openRep_shift_prefix {α : Type} (D : C.Coalition) (ctx : Context C)
    (count : ℕ) (v : Shares C Bit) (shift : ℕ → Bit)
    (k : (ℕ → Bit) → PartyM C E RealSpec α)
    (consume : ∀ x y, (∀ g, g < count → x g = y g) → k x = k y) :
    (openRep K ctx (treeSimShift D v shift) count >>= k) =
      (openRep K ctx (treeSimShift D v (fun g => if g < count then shift g else 0)) count >>= k) := by
  apply treeStages_openRep_prefix K ctx count _ _ _ k consume
  intro T g hg
  simp [treeSimShift, hg]

/-- The exact batch decoder used by `runWith`: split the opened prefix at
the cumulative output widths of the jobs. -/
def treeStagesBatchDecode (widths : List ℕ) (opened : ℕ → Bit) : List (List Bit) :=
  widths.zipIdx.map fun (width, k) => vector width fun g => opened ((widths.take k).sum + g)

theorem treeStages_batchDecode_prefix (widths : List ℕ) (x y : ℕ → Bit)
    (same : ∀ g, g < widths.sum → x g = y g) :
    treeStagesBatchDecode widths x = treeStagesBatchDecode widths y := by
  unfold treeStagesBatchDecode
  apply List.map_congr_left
  rintro ⟨width, k⟩ hk
  apply vector_congr'
  intro g hg
  apply same
  have index := List.mem_zipIdx_iff_getElem?.mp hk
  have bound : (widths.take k).sum + width ≤ widths.sum := by
    have split := List.take_append_drop k widths
    have first : (widths.drop k).head? = some width := by simpa using index
    cases hd : widths.drop k with
    | nil => simp [hd] at first
    | cons a tail =>
      have heq : a = width := by simpa [hd] using first
      subst a
      have sums := congrArg List.sum split
      simp only [List.sum_append, hd, List.sum_cons] at sums
      omega
  omega

/-- The complete final-check suffix with the simulator's actual unbounded
T₀ correction and the exact batch decoder. No equality of unused tail bits
is required. -/
theorem treeStages_check_shift_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (widths : List ℕ) (v : C.Party → Shares C Bit) (shift : ℕ → Bit)
    (f : C.Party → List (List Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1) :
    RelTriple
      ((executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind (fun i =>
          openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
            pure (f i (treeStagesBatchDecode widths out))))).run a)
      ((executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind (fun i =>
          openRep K (ctx₂ i)
            (treeSimShift D (treeSimHeldShift D i widths.sum shift (v i)) shift) widths.sum >>=
              fun out => pure (f i (treeStagesBatchDecode widths out))))).run b)
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1) := by
  simp_rw [treeStages_openRep_shift_prefix K D _ widths.sum _ shift _
    (fun x y h => congrArg (fun out => pure (f _ out))
      (treeStages_batchDecode_prefix widths x y h))]
  apply treeStages_check_open_finish prims K D A state fuel live kind ctx₁ ctx₂ self₁ self₂
    widths.sum v _ _ (fun i out => f i (treeStagesBatchDecode widths out)) δ a b related covered
  intro i _ T held
  exact (treeSim_open_shift_held D i widths.sum shift (v i) T held).symm

/-- Cached PRF answers determine the clear output of each actual job. -/
def treeStagesCachedPrf (cache : HashCache C) (seeds : C.Term → HashOutput) (x : Point) : Digest :=
  (C.terms.map fun T => truncateHash ((cache (.prf (seeds T) x)).getD 0)).foldl (· ^^^ ·) 0

def treeStagesCachedJob (cache : HashCache C) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (job : Job) : List Bit :=
  (circuits parameter job.kind).eval
    ((job.points.map (treeStagesCachedPrf cache seeds)).flatMap bitsOfDigest)

def TreeStagesPrfCovered (cache : HashCache C) (seeds : C.Term → HashOutput)
    (jobs : List Job) : Prop :=
  ∀ job ∈ jobs, ∀ x ∈ job.points, ∀ T, ∃ h, cache (.prf (seeds T) x) = some h

private theorem treeStages_mapM_cached {α β σ : Type} (f : α → StateT σ ProbComp β)
    (values : α → β) (xs : List α) (state : σ)
    (h : ∀ x ∈ xs, (f x).run state = pure (values x, state)) :
    (xs.mapM f).run state = pure (xs.map values, state) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, h x (by simp), pure_bind]
    rw [ih (fun y hy => h y (by simp [hy]))]
    simp

/-- Replay respects the actual nested traversal, without exchanging or
removing any oracle calls. -/
theorem treeStages_ro_mapM_replay {α β : Type} (D : C.Coalition)
    (xs : List α) (f : α → OracleComp (RoSpec C) β) (values : α → β)
    (cache : HashCache C × HiddenCache C)
    (h : ∀ x ∈ xs, (simulateQ (streamWorld prims D)
      (free (liftComp (f x) (LocalSpec C)))).run cache = pure (values x, cache)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (xs.mapM f) (LocalSpec C)))).run cache = pure (xs.map values, cache) := by
  rw [keygen_liftComp_mapM]
  unfold free
  erw [simulateQ_list_mapM, simulateQ_list_mapM]
  exact treeStages_mapM_cached _ values xs cache h

theorem treeStages_prfValue_replay (D : C.Coalition) (seeds : C.Term → HashOutput)
    (x : Point) (cache : HashCache C × HiddenCache C)
    (covered : ∀ T, ∃ h, cache.1 (.prf (seeds T) x) = some h) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prfValue seeds x) (LocalSpec C)))).run cache =
        pure (treeStagesCachedPrf cache.1 seeds x, cache) := by
  have single (T : C.Term) : (simulateQ (streamWorld prims D)
      (free (liftComp (prf (C := C) (seeds T) x) (LocalSpec C)))).run cache =
        pure (truncateHash ((cache.1 (.prf (seeds T) x)).getD 0), cache) := by
    obtain ⟨h, hh⟩ := covered T
    unfold prf
    simp only [map_eq_bind_pure_comp, liftComp_bind, liftComp_pure, free_bind,
      free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    have queryEq : simulateQ (streamWorld prims D)
        (free (liftComp (hashQuery (C := C) (.prf (seeds T) x)) (LocalSpec C))) =
          onHash (hashAnswer prims (.prf (seeds T) x)) := by
      unfold hashQuery
      erw [simulateQ_spec_query]
      rfl
    rw [queryEq]
    simp [onHash, hashAnswer_run_cached prims (by rintro ⟨_, heq, _⟩; cases heq) hh, hh]
  unfold prfValue
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [treeStages_ro_mapM_replay prims D C.terms _ _ cache (fun T _ => single T), pure_bind]
  rfl

theorem treeStages_evalJob_replay (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (job : Job) (cache : HashCache C × HiddenCache C)
    (covered : ∀ x ∈ job.points, ∀ T, ∃ h, cache.1 (.prf (seeds T) x) = some h) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (evalJob circuits parameter seeds job) (LocalSpec C)))).run cache =
        pure (treeStagesCachedJob circuits cache.1 parameter seeds job, cache) := by
  unfold evalJob
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [treeStages_ro_mapM_replay prims D job.points _ _ cache
    (fun x hx => treeStages_prfValue_replay prims D seeds x cache (covered x hx)), pure_bind]
  rfl

/-- All clear-evaluation calls in the actual simulator replay the public
cache and leave its hidden stream table untouched. -/
theorem treeStages_evalJobs_replay (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (jobs : List Job) (cache : HashCache C × HiddenCache C)
    (covered : TreeStagesPrfCovered cache.1 seeds jobs) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (jobs.mapM (evalJob circuits parameter seeds)) (LocalSpec C)))).run cache =
        pure (jobs.map (treeStagesCachedJob circuits cache.1 parameter seeds), cache) := by
  exact treeStages_ro_mapM_replay prims D jobs _ _ cache
    (fun job hj => treeStages_evalJob_replay prims circuits D parameter seeds job cache (covered job hj))

/-- Expose the actual simulator output override, including its clear oracle
calls and its unchanged run state. -/
theorem treeStages_simOutput_factor {α : Type} (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) (ctx : Context C)
    (batch count : ℕ) (jobs : List Job) (v : Shares C Bit) (st : RunState C)
    (k : ((ℕ → Bit) × RunState C) → PartyM C E RealSpec α) :
    (((treeSimGadgets K circuits settings D parameter seeds openings ctx batch jobs).output v count).run st >>= k) =
      (do
        let clear ← oracleStep (jobs.mapM (evalJob circuits parameter seeds))
        let shift := fun g => (openings.getD batch []).flatten.getD g 0 + clear.flatten.getD g 0
        openRep K ctx (treeSimShift D v shift) count >>= fun out => k (out, st)) := by
  simp only [treeSimGadgets, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]

/-- Actual clear-evaluation calls can be replayed before any continuation of
an operator, including its next exchange. -/
theorem treeStages_clear_advance_replay {α : Type} (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (jobs : List Job) (cache : HashCache C × HiddenCache C)
    (covered : TreeStagesPrfCovered cache.1 seeds jobs)
    (k : List (List Bit) → PartyM C E RealSpec α) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((oracleStep (jobs.mapM (evalJob circuits parameter seeds)) >>= k).run)))).run cache =
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((k (jobs.map (treeStagesCachedJob circuits cache.1 parameter seeds))).run)))).run cache := by
  simp only [worldRoles, advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  rw [treeStages_evalJobs_replay prims circuits D parameter seeds jobs cache covered, pure_bind]

/-- The actual simulator output prefix, with every clear query retained,
reduces to its corrected opening under concrete cache coverage. -/
theorem treeStages_simOutput_advance {α : Type} (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) (ctx : Context C)
    (batch count : ℕ) (jobs : List Job) (v : Shares C Bit) (st : RunState C)
    (k : ((ℕ → Bit) × RunState C) → PartyM C E RealSpec α)
    (cache : HashCache C × HiddenCache C) (covered : TreeStagesPrfCovered cache.1 seeds jobs) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((((treeSimGadgets K circuits settings D parameter seeds openings ctx batch jobs).output v count).run st >>= k).run)))).run cache =
    (simulateQ (streamWorld prims D) (worldRoles.honest (advance ((openRep K ctx
      (treeSimShift D v (fun g => (openings.getD batch []).flatten.getD g 0 +
        (jobs.map (treeStagesCachedJob circuits cache.1 parameter seeds)).flatten.getD g 0)) count >>=
          fun out => k (out, st)).run)))).run cache := by
  rw [treeStages_simOutput_factor]
  exact treeStages_clear_advance_replay prims circuits D parameter seeds jobs cache covered _

theorem treeStages_prfCovered_mono {a b : HashCache C} (h : a ≤ b)
    (seeds : C.Term → HashOutput) (jobs : List Job) (covered : TreeStagesPrfCovered a seeds jobs) :
    TreeStagesPrfCovered b seeds jobs := by
  intro job hj x hx T
  obtain ⟨answer, ha⟩ := covered job hj x hx T
  exact ⟨answer, h ha⟩

/-- Public-cache growth cannot change the already determined clear jobs. -/
theorem treeStages_cachedJobs_mono {a b : HashCache C} (h : a ≤ b)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (jobs : List Job)
    (covered : TreeStagesPrfCovered a seeds jobs) :
    jobs.map (treeStagesCachedJob circuits a parameter seeds) =
      jobs.map (treeStagesCachedJob circuits b parameter seeds) := by
  apply List.map_congr_left
  intro job hj
  unfold treeStagesCachedJob
  congr 2
  apply List.map_congr_left
  intro x hx
  unfold treeStagesCachedPrf
  congr 1
  apply List.map_congr_left
  intro T _
  obtain ⟨answer, ha⟩ := covered job hj x hx T
  rw [ha, h ha]

/-- Prefetching any finite list of random-oracle addresses installs all of
them, including repeated addresses, while preserving the dealer's cache. -/
theorem treeStages_prefetch_queries (qs : List (Query C))
    (random : ∀ q ∈ qs, ¬ IsFixed q) (cache : HashCache C) (r : List HashOutput × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (qs.mapM fun q => liftComp (hashQuery q) (LocalSpec C))).run cache)) :
    cache ≤ r.2 ∧ ∀ q ∈ qs, ∃ h, r.2 q = some h := by
  induction qs generalizing cache r with
  | nil =>
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl, by simp⟩
  | cons q qs ih =>
    simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    rw [simulateQ_localAnswer_hash] at hu
    have head := hashAnswer_cached prims (random q (by simp)) cache u hu
    obtain ⟨grows, tail⟩ := ih (fun x hx => random x (by simp [hx])) u.2 v hv
    refine ⟨(grows_hashAnswer prims _ cache u hu).trans grows, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨u.1, grows head⟩
    · exact tail x hx

/-- This finite padding makes all simulator clear-job evaluations replayable.
It contains only the PRF addresses actually used by the supplied jobs. -/
def treeStagesPrfPadding (seeds : C.Term → HashOutput) (jobs : List Job) :
    OracleComp (LocalSpec C) Unit := do
  let qs : List (Query C) := jobs.flatMap fun job => job.points.flatMap fun x => C.terms.map fun T => Query.prf (seeds T) x
  let _ ← qs.mapM fun q => liftComp (hashQuery q) (LocalSpec C)
  pure ()

theorem treeStages_prfPadding_covered (seeds : C.Term → HashOutput) (jobs : List Job)
    (cache : HashCache C) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (treeStagesPrfPadding seeds jobs)).run cache)) :
    cache ≤ r.2 ∧ TreeStagesPrfCovered r.2 seeds jobs := by
  simp only [treeStagesPrfPadding, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  obtain ⟨grows, covered⟩ := treeStages_prefetch_queries prims _ (by
    intro q hq
    obtain ⟨job, _, x, _, T, _, rfl⟩ := by
      simpa only [List.mem_flatMap, List.mem_map] using hq
    rintro ⟨_, heq, _⟩
    cases heq) cache u hu
  refine ⟨grows, ?_⟩
  intro job hj x hx T
  apply covered
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨job, hj, x, hx, T, by simp [Committee.terms], rfl⟩

/-- The correction used verbatim by the simulator's output override. -/
def treeStagesCorrection (openings : List (List (List Bit))) (batch : ℕ)
    (clear : List (List Bit)) (g : ℕ) : Bit :=
  (openings.getD batch []).flatten.getD g 0 + clear.flatten.getD g 0

/-- The real simulator output override followed by the actual batch decoder. -/
def treeStagesSimBatchOutput (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) (ctx : Context C)
    (batch : ℕ) (jobs : List Job) (widths : List ℕ) (v : Shares C Bit) (st : RunState C)
    (f : List (List Bit) → TreeOutput) : PartyM C E RealSpec TreeOutput := do
  let out ← ((treeSimGadgets K circuits settings D parameter seeds openings ctx batch jobs).output v widths.sum).run st
  pure (f (treeStagesBatchDecode widths out.1))

/-- Entry coupling for the actual simulator output override: clear-job
queries, unbounded T₀ correction, both sets of copy hashes, and batch decoding. -/
theorem treeStages_simBatch_entry (D : C.Coalition) (i : C.Party)
    (ctx₁ ctx₂ : Context C) (self₁ : ctx₁.self = i) (self₂ : ctx₂.self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : Shares C Bit) (st : RunState C)
    (f : List (List Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((openRep K ctx₁ v widths.sum >>= fun out => pure (f (treeStagesBatchDecode widths out))).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeStagesSimBatchOutput K circuits settings D parameter seeds openings ctx₂ batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) v) st f).run)))).run b)
      (fun u z =>
        u.1 = treeSimOpenStep K i widths.sum v (treeStagesCopyDigests widths.sum a.1.1 v)
          (fun out => pure (f (treeStagesBatchDecode widths out))) ∧
        z.1 = u.1 ∧ u.2.1 = a.1 ∧ z.2 = b ∧ TreeSimStreamRel δ u.2 z.2) := by
  unfold treeStagesSimBatchOutput
  rw [treeStages_simOutput_advance prims K circuits settings D parameter seeds openings ctx₂
    batch widths.sum jobs _ st _ b prfCovered, clearEq]
  rw [treeStages_openRep_shift_prefix K D ctx₂ widths.sum _ _ _
    (fun x y h => congrArg (fun out => pure (f out)) (treeStages_batchDecode_prefix widths x y h))]
  apply relTriple_post_mono (treeStages_open_entry_padded prims K D i ctx₁ ctx₂ self₁ self₂
    widths.sum v _ (fun T hT => (treeSim_open_shift_held D i widths.sum
      (treeStagesCorrection openings batch clear) v T hT).symm)
    (fun out => pure (f (treeStagesBatchDecode widths out)))
    (fun out => pure (f (treeStagesBatchDecode widths out))) δ a b related covered)
  intro u z hu
  exact ⟨hu.1, hu.2.1.trans hu.1.symm, hu.2.2⟩

/-- Sequential optional entries for the actual simulator override. Any
subset of honest parties may already have aborted. -/
theorem treeStages_simBatch_partial (D : C.Coalition) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (f : C.Party → List (List Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
          pure (f i (treeStagesBatchDecode widths out)))
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => treeStagesSimBatchOutput K circuits settings D parameter seeds openings
          (ctx₂ i) batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (f i))
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b)
      (fun u z =>
        u.1 = treeSimOpenPartial K D live widths.sum v
          (fun i => treeStagesCopyDigests widths.sum a.1.1 (v i))
          (fun i out => pure (f i (treeStagesBatchDecode widths out))) ∧
        z.1 = u.1 ∧ u.2.1 = a.1 ∧ z.2 = b ∧ TreeSimStreamRel δ u.2 z.2) := by
  let expected := treeSimOpenPartial K D live widths.sum v
    (fun i => treeStagesCopyDigests widths.sum a.1.1 (v i))
    (fun i out => pure (f i (treeStagesBatchDecode widths out)))
  let J := fun s t => s.1 = a.1 ∧ t = b ∧ TreeSimStreamRel δ s t
  let Q := fun i x y => x = expected i ∧ y = x
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ _ _ J Q ?_ a b ⟨rfl, rfl, related⟩)
  · intro u z hu
    exact ⟨funext (fun i => (hu.1 i).1), funext (fun i => (hu.1 i).2), hu.2⟩
  · intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨by simp [expected, treeSimOpenPartial, hi], rfl⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume]
        apply relTriple_post_mono (treeStages_simBatch_entry prims K circuits settings D i
          (ctx₁ i) (ctx₂ i) (self₁ i hi) (self₂ i hi) parameter seeds openings batch jobs widths
          clear (v i) (st i) (f i) δ s t hst.2.2
          (by rw [hst.1]; exact covered) (by rw [hst.2.1]; exact prfCovered)
          (by rw [hst.2.1]; exact clearEq))
        intro u z hu
        refine ⟨⟨?_, hu.2.1⟩, hu.2.2.1.trans hst.1, hu.2.2.2.1.trans hst.2.1, hu.2.2.2.2⟩
        simpa only [expected, treeSimOpenPartial, if_neg hi, if_pos hl, hst.1] using hu.1
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨by simp [expected, treeSimOpenPartial, hi, hl], rfl⟩, hst⟩

/-- Final-check exchange with the actual output override on the ideal side.
The rushing adversary may extend the shared cache before the clear replay. -/
theorem treeStages_simBatch_check_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (f : C.Party → List (List Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
          pure (f i (treeStagesBatchDecode widths out))))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind (fun i => treeStagesSimBatchOutput K circuits settings D
          parameter seeds openings (ctx₂ i) batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (f i)))).run b)
      (fun u z => ∃ sent ds,
        let active := fun i => (treeSimCheckResult K D live kind sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimOpenPartial K D active widths.sum v ds
          (fun i out => pure (f i (treeStagesBatchDecode widths out))) ∧
        z.1.2.1 = u.1.2.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧
        TreeStagesCopyCovered widths.sum u.2.1.1 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_check_round_factor, treeSim_check_round_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D δ _ a b related))
  intro u z hu
  have hc := hu.1
  have grows := treeSim_logged_grows prims D _ a u hu.2.1
  have cover := treeStages_copyCovered_mono widths.sum grows covered
  have idealGrows : b.1 ≤ z.2.1 := by rw [← related.1, ← hc.2.1.1]; exact grows
  have prfCover := treeStages_prfCovered_mono idealGrows seeds jobs prfCovered
  have replay := (treeStages_cachedJobs_mono circuits idealGrows parameter seeds jobs prfCovered).symm.trans clearEq
  rw [← hc.1]
  let active := fun i => (treeSimCheckResult K D live kind u.1.2 i).isSome
  have shape : treeSimCheckResult K D live kind u.1.2 =
      fun i => if i ∈ D.1 then none else if active i then some () else none := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCheckResult, hi]
    · rw [if_neg hi]
      cases hv : treeSimCheckResult K D live kind u.1.2 i <;> simp [active, hv]
  rw [shape]
  apply relTriple_bind (treeStages_simBatch_partial prims K circuits settings D active ctx₁ ctx₂ self₁ self₂
    parameter seeds openings batch jobs widths clear v st f δ u.2 z.2 hc.2.1 cover prfCover replay)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  refine ⟨u.1.2, (fun i => treeStagesCopyDigests widths.sum u.2.1.1 (v i)),
    rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2.2.2, ?_, ?_, ?_⟩
  · simpa only [hp.2.2.1] using cover
  · exact (congrArg Prod.snd hp.2.2.1).trans hc.2.2.1
  · exact (congrArg Prod.snd hp.2.2.2.1).trans hc.2.2.2

/-- Complete actual final-check/output suffix, including the simulator's
clear queries and correction, decoder, selective aborts and fuel exhaustion. -/
theorem treeStages_simBatch_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (f : C.Party → List (List Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
          pure (f i (treeStagesBatchDecode widths out))))).run a)
      ((executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel state
        (treeSimCheckWaiting K D live kind (fun i => treeStagesSimBatchOutput K circuits settings D
          parameter seeds openings (ctx₂ i) batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (f i)))).run b)
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1) := by
  have outputs (k : C.Party → PartyM C E RealSpec TreeOutput) :
      (fun i => (treeSimCheckWaiting K D live kind k i).output) = fun _ => none := by
    funext i
    unfold treeSimCheckWaiting
    split_ifs <;> rfl
  cases fuel with
  | zero =>
    simp only [executeRounds, StateT.run_pure, outputs]
    exact relTriple_pure_pure ⟨rfl, related.1⟩
  | succ fuel =>
    have done (k : C.Party → PartyM C E RealSpec TreeOutput) :
        AllDone D (treeSimCheckWaiting K D live kind k) ↔ ∀ i, i ∉ D.1 → live i ≠ true := by
      unfold AllDone
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      by_cases hl : live i = true <;>
        simp [treeSimCheckWaiting, hi, hl, treeSimCheckStep, Step.isDone]
    rw [executeRounds_succ, executeRounds_succ, done, done]
    split_ifs with stopped
    · simp only [StateT.run_pure, outputs]
      exact relTriple_pure_pure ⟨rfl, related.1⟩
    · simp only [StateT.run_bind]
      apply relTriple_bind (treeStages_simBatch_check_round prims K circuits settings D A state live kind
        ctx₁ ctx₂ self₁ self₂ parameter seeds openings batch jobs widths clear v st f δ a b related
        covered prfCovered clearEq)
      intro u z hu
      obtain ⟨sent, ds, stateEq, _, _, steps₁, steps₂, hc, _⟩ := hu
      rw [steps₂, steps₁, ← stateEq]
      exact treeStages_open_terminal_rounds prims K D A u.1.1 fuel _ widths.sum v ds
        (fun i out => f i (treeStagesBatchDecode widths out)) δ u.2 z.2 hc

/-- Both coverage conditions used by the actual output suffix have a single
finite padding witness. Existing dealer answers are preserved. -/
def treeStagesOutputPadding (seeds : C.Term → HashOutput) (jobs : List Job) (count : ℕ) :
    OracleComp (LocalSpec C) Unit :=
  treeStagesPrfPadding seeds jobs >>= fun _ => treeStagesCopyPadding count

theorem treeStages_outputPadding_covered (seeds : C.Term → HashOutput) (jobs : List Job)
    (count : ℕ) (cache : HashCache C) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (treeStagesOutputPadding seeds jobs count)).run cache)) :
    cache ≤ r.2 ∧ TreeStagesPrfCovered r.2 seeds jobs ∧ TreeStagesCopyCovered count r.2 := by
  simp only [treeStagesOutputPadding, simulateQ_bind, StateT.run_bind,
    support_bind, Set.mem_iUnion] at hr
  obtain ⟨u, hu, hr⟩ := hr
  obtain ⟨hg, hp⟩ := treeStages_prfPadding_covered prims seeds jobs cache u hu
  obtain ⟨hg', hc⟩ := treeStages_copyPadding_covered prims count u.2 r hr
  exact ⟨hg.trans hg', treeStages_prfCovered_mono hg' seeds jobs hp, hc⟩

/-- GS20's last field-mask translation followed by the complete actual
simulator output suffix. Equal multiplication residuals imply the scalar
compatibility condition; it is not a separate assumption about the masks. -/
theorem treeStages_finalMask_simBatch_finish (D : C.Coalition)
    (Adv : Adversary C E (Keys C) PEmpty PEmpty) (state : Adv.State) (fuel : ℕ)
    (live : C.Party → Bool) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (known knownQ : Shares C E) (attack : ℕ → E) (offset : C.Party → Shares C E)
    (receivers : Finset C.Party) (T₀ : C.Term) (hidden : ¬ KnownTo D.1 T₀)
    (r : E) (delta : MaskTable C E) (deltaD : C.Term → E)
    (A B V A' B' V' : C.Party → E) (w q : MaskTable C E)
    (a₀ b₀ a₀' b₀' d₀ d₀' : E)
    (hr : 1 + r ≠ 0) (knownDelta : ∀ T, KnownTo D.1 T → ∀ g, delta T g = 0)
    (knownD : ∀ T, KnownTo D.1 T → deltaD T = 0)
    (shamirA : IsShamir K A a₀) (shamirB : IsShamir K B b₀)
    (shamirA' : IsShamir K A' a₀') (shamirB' : IsShamir K B' b₀')
    (corruptA : ∀ i ∈ D.1, A i = A' i) (corruptB : ∀ i ∈ D.1, B i = B' i)
    (sumA : ∑ T, delta T 0 = a₀ - a₀') (sumB : ∑ T, delta T 1 = b₀ - b₀')
    (sumD : ∑ T, deltaD T = d₀ - d₀') (residual : d₀ - a₀*b₀ = d₀' - a₀'*b₀')
    (rec : ∀ i, i ∉ D.1 → live i = true → i ∈ receivers)
    (localA : ∀ i, i ∉ D.1 → live i = true → A i - A' i =
      conv K (localContext i) (fun T _ => delta T 0) 0)
    (localB : ∀ i, i ∉ D.1 → live i = true → B i - B' i =
      conv K (localContext i) (fun T _ => delta T 1) 0)
    (localD : ∀ i, i ∉ D.1 → live i = true → V i - V' i =
      conv K (localContext i) (fun T _ => deltaD T) 0)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (f : C.Party → List (List Bit) → TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    let field₁ := finalMaskVector K D known knownQ attack offset receivers r A B V w q
    let field₂ := finalMaskVector K D known knownQ attack offset receivers r A' B' V'
      (maskTableEquiv r delta w)
      (finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD q)
    RelTriple
      ((executeRounds (treeSimRealRoles prims D) D Adv noFunctionality fuel state
        (treeSimCheckWaiting K D live (.opening field₁)
          (fun i => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
            pure (f i (treeStagesBatchDecode widths out))))).run a)
      ((executeRounds (treeSimIdealRoles prims D) D Adv noFunctionality fuel state
        (treeSimCheckWaiting K D live (.opening field₂) (fun i =>
          treeStagesSimBatchOutput K circuits settings D parameter seeds openings (ctx₂ i) batch jobs widths
            (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (f i)))).run b)
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1) := by
  letI : SampleableType E := SampleableType.ofFintype E
  dsimp only
  have compat := maskedResultDelta_compatible K D known attack r delta w A B A' B'
    a₀ b₀ a₀' b₀' d₀ d₀' deltaD hr knownDelta shamirA shamirB shamirA' shamirB'
    corruptA corruptB sumA sumB sumD residual
  have same : ∀ i, i ∉ D.1 → live i = true →
      finalMaskVector K D known knownQ attack offset receivers r A' B' V'
        (maskTableEquiv r delta w)
        (finalTableEquiv T₀ r (maskedResultDelta K D known attack r delta w A B A' B') deltaD q) i =
      finalMaskVector K D known knownQ attack offset receivers r A B V w q i := by
    intro i hi hl
    exact (finalMaskVector_bijection K D known knownQ attack offset receivers T₀ hidden r delta deltaD
      A B V A' B' V' w q hr knownDelta knownD compat i hi (rec i hi hl)
      (localA i hi hl) (localB i hi hl) (localD i hi hl)).symm
  rw [treeStages_check_opening_congr K D live _ _ _ same]
  exact treeStages_simBatch_finish prims K circuits settings D Adv state fuel live _ ctx₁ ctx₂ self₁ self₂
    parameter seeds openings batch jobs widths clear v st f δ a b related covered prfCovered clearEq

/-- Replay a single PRF query from the already populated public cache. -/
theorem treeStages_prf_replay (D : C.Coalition) (seed : HashOutput) (x : Point)
    (cache : HashCache C × HiddenCache C) (covered : ∃ h, cache.1 (.prf seed x) = some h) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prf (C := C) seed x) (LocalSpec C)))).run cache =
        pure (truncateHash ((cache.1 (.prf seed x)).getD 0), cache) := by
  obtain ⟨h, hh⟩ := covered
  unfold prf
  simp only [map_eq_bind_pure_comp, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind]
  have queryEq : simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery (C := C) (.prf seed x)) (LocalSpec C))) =
        onHash (hashAnswer prims (.prf seed x)) := by
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  rw [queryEq]
  simp [onHash, hashAnswer_run_cached prims (by rintro ⟨_, heq, _⟩; cases heq) hh, hh,
    liftComp_pure, free_pure]

private theorem treeStages_ro_map_replay {α β : Type} (D : C.Coalition)
    (p : OracleComp (RoSpec C) α) (f : α → β) (value : α) (cache : HashCache C × HiddenCache C)
    (h : (simulateQ (streamWorld prims D) (free (liftComp p (LocalSpec C)))).run cache = pure (value, cache)) :
    (simulateQ (streamWorld prims D) (free (liftComp (f <$> p) (LocalSpec C)))).run cache =
      pure (f value, cache) := by
  simp only [map_eq_bind_pure_comp, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind, h, pure_bind]
  simp [liftComp_pure, free_pure]

private theorem treeStages_ro_flatMapM_replay {α β : Type} (D : C.Coalition)
    (xs : List α) (f : α → OracleComp (RoSpec C) (List β)) (values : α → List β)
    (cache : HashCache C × HiddenCache C)
    (h : ∀ x ∈ xs, (simulateQ (streamWorld prims D)
      (free (liftComp (f x) (LocalSpec C)))).run cache = pure (values x, cache)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (xs.flatMapM f) (LocalSpec C)))).run cache = pure (xs.flatMap values, cache) := by
  induction xs with
  | nil => simp [liftComp_pure, free_pure]
  | cons x xs ih =>
    simp only [List.flatMapM_cons, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind,
      h x (by simp), pure_bind, ih (fun y hy => h y (by simp [hy]))]
    simp [liftComp_pure, free_pure]

/-- The concrete input wires obtained by replaying a batch's PRF queries. -/
def treeStagesCachedInputs (cache : HashCache C) (ctx : Context C) (job : Job) : C.Term → List Bit :=
  fun T => if ctx.self ∈ C.holders T then
    inputBits (fun q => (cache q).getD 0) ctx.keys.seed job T else []

theorem treeStages_inputQuery_replay (D : C.Coalition) (ctx : Context C) (job : Job)
    (cache : HashCache C × HiddenCache C)
    (covered : ∀ x ∈ job.points, ∀ T, ∃ h, cache.1 (.prf (ctx.keys.seed T) x) = some h) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (inputQuery ctx job) (LocalSpec C)))).run cache =
        pure (treeStagesCachedInputs cache.1 ctx job, cache) := by
  have term (T : C.Term) : (simulateQ (streamWorld prims D) (free (liftComp
      (if ctx.self ∈ C.holders T then job.points.flatMapM fun x =>
        bitsOfDigest <$> prf (C := C) (ctx.keys.seed T) x else pure []) (LocalSpec C)))).run cache =
      pure (treeStagesCachedInputs cache.1 ctx job T, cache) := by
    by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held, treeStagesCachedInputs, inputBits]
      exact treeStages_ro_flatMapM_replay prims D job.points _ _ cache (fun x hx =>
        treeStages_ro_map_replay prims D _ bitsOfDigest _ cache
          (treeStages_prf_replay prims D (ctx.keys.seed T) x cache (covered x hx T)))
    · simp [held, treeStagesCachedInputs, liftComp_pure, free_pure]
  unfold inputQuery
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [treeStages_ro_mapM_replay prims D C.terms _ _ cache (fun T _ => term T), pure_bind]
  congr 2
  funext T
  exact getD_terms_idxOf _ _ T

theorem treeStages_inputQueries_replay (D : C.Coalition) (ctx : Context C) (jobs : List Job)
    (cache : HashCache C × HiddenCache C) (covered : TreeStagesPrfCovered cache.1 ctx.keys.seed jobs) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (jobs.mapM (inputQuery ctx)) (LocalSpec C)))).run cache =
        pure (jobs.map (treeStagesCachedInputs cache.1 ctx), cache) := by
  exact treeStages_ro_mapM_replay prims D jobs _ _ cache
    (fun job hj => treeStages_inputQuery_replay prims D ctx job cache (covered job hj))

/-- Cached input wires remain fixed under subsequent public-cache growth. -/
theorem treeStages_cachedInputs_mono {a b : HashCache C} (h : a ≤ b)
    (ctx : Context C) (jobs : List Job) (covered : TreeStagesPrfCovered a ctx.keys.seed jobs) :
    jobs.map (treeStagesCachedInputs a ctx) = jobs.map (treeStagesCachedInputs b ctx) := by
  apply List.map_congr_left
  intro job hj
  funext T
  unfold treeStagesCachedInputs
  split_ifs with held
  · unfold inputBits
    apply List.flatMap_congr
    intro x hx
    obtain ⟨v, hv⟩ := covered job hj x hx T
    dsimp only
    rw [hv, h hv]
  · rfl

/-- Two concrete cache replays may return different private inputs. Their
real log is retained and both caches are unchanged. -/
theorem treeStages_readOnly_pair {α β : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (q : OracleComp (WorldSpec C) β)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (x : α) (y : β)
    (ha : (simulateQ (streamWorld prims D) p).run a.1 = pure (x, a.1))
    (hb : (simulateQ (streamWorld prims D) q).run b = pure (y, b)) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) p).run a)
      ((simulateQ (streamWorld prims D) q).run b)
      (fun u z => u.1 = x ∧ z.1 = y ∧ u.2.1 = a.1 ∧ z.2 = b) := by
  rw [hb]
  apply relTriple_post_mono (treeSim_relTriple_support (relTriple_true _ _))
  intro u z hu
  have erased : (u.1, u.2.1) ∈ support ((simulateQ (streamWorld prims D) p).run a.1) := by
    rw [← treeSimLoggedWorld_erase prims D p a.1 a.2, support_map]
    exact ⟨u, hu.2.1, rfl⟩
  rw [ha, support_pure, Set.mem_singleton_iff] at erased
  have hz := hu.2.2
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst z
  exact ⟨congrArg Prod.fst erased, rfl, congrArg Prod.snd erased, rfl⟩

/-- The actual next-batch input queries followed by its first peer PRSS
and reshare entry. `value` can be the first AND layer or output rerandomizer. -/
def treeStagesBatchPeerProgram (ctx : Context C) (jobs : List Job) (idx count : ℕ)
    (value : List (C.Term → List Bit) → ℕ → Bit) (st : RunState C)
    (k : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) :
    PartyM C E RealSpec TreeOutput := do
  let inputs ← jobs.mapM (inputShares ctx)
  treeSimPeerProgram K ctx idx count (value inputs) st (k inputs)

/-- Actual next-batch entry over the common padded cache, with possibly
different honest seeds. The real input queries are logged; no input oracle
or PRSS-draw coupling is assumed. -/
theorem treeStages_batchPeer_entry (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (jobs : List Job) (idx count : ℕ) (base : HashCache C)
    (covered₁ : TreeStagesPrfCovered base ctx₁.keys.seed jobs)
    (covered₂ : TreeStagesPrfCovered base ctx₂.keys.seed jobs)
    (value₁ value₂ : List (C.Term → List Bit) → ℕ → Bit)
    (st₁ st₂ : RunState C) (label : st₁.label = st₂.label)
    (k₁ k₂ : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (base_le : base ≤ a.1.1) :
    let inputs₁ := jobs.map (treeStagesCachedInputs base ctx₁)
    let inputs₂ := jobs.map (treeStagesCachedInputs base ctx₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((treeStagesBatchPeerProgram K ctx₁ jobs idx count value₁ st₁ k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeStagesBatchPeerProgram K ctx₂ jobs idx count value₂ st₂ k₂).run)))).run b)
      (fun u z => TreeSimPeerRel K δ ctx₁ ctx₂ idx count (value₁ inputs₁) (value₂ inputs₂)
        st₁ st₂ (k₁ inputs₁) (k₂ inputs₂) u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  have base_le₂ : base ≤ b.1 := by rw [← related.1]; exact base_le
  have replay₁ := treeStages_inputQueries_replay prims D ctx₁ jobs a.1
    (treeStages_prfCovered_mono base_le _ _ covered₁)
  have replay₂ := treeStages_inputQueries_replay prims D ctx₂ jobs b
    (treeStages_prfCovered_mono base_le₂ _ _ covered₂)
  rw [← treeStages_cachedInputs_mono base_le ctx₁ jobs covered₁] at replay₁
  rw [← treeStages_cachedInputs_mono base_le₂ ctx₂ jobs covered₂] at replay₂
  unfold treeStagesBatchPeerProgram
  simp only [inputShares_fun, mapM_oracleStep, worldRoles, advance_oracleStep_bind,
    free_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeStages_readOnly_pair prims D _ _ a b _ _ replay₁ replay₂)
  intro u z hu
  rw [hu.1, hu.2.1]
  have rel : TreeSimStreamRel δ u.2 z.2 := by
    simpa only [TreeSimStreamRel, hu.2.2.1, hu.2.2.2] using related
  apply relTriple_post_mono (treeSim_relTriple_support (treeSim_peer_start_mixed prims K D δ visible
    ctx₁ ctx₂ self keys idx count _ _ st₁ st₂ label _ _ u.2 z.2 rel))
  intro x y hxy
  have grows : base ≤ u.2.1.1 := by rw [hu.2.2.1]; exact base_le
  exact ⟨hxy.1.1, hxy.1.2, grows.trans (treeSim_logged_grows prims D _ u.2 x hxy.2.1)⟩

/-- Concrete next-batch entry data. The two input seeds and saved
continuations may differ; the public schedule and PRSS keys coincide. -/
structure TreeStagesBatchPeerData (C : Committee) (E : Type) (base : HashCache C) where
  ctx₁ : Context C
  ctx₂ : Context C
  self : ctx₁.self = ctx₂.self
  keys : ctx₁.prss = ctx₂.prss
  jobs : List Job
  idx : ℕ
  count : ℕ
  covered₁ : TreeStagesPrfCovered base ctx₁.keys.seed jobs
  covered₂ : TreeStagesPrfCovered base ctx₂.keys.seed jobs
  value₁ : List (C.Term → List Bit) → ℕ → Bit
  value₂ : List (C.Term → List Bit) → ℕ → Bit
  st₁ : RunState C
  st₂ : RunState C
  label : st₁.label = st₂.label
  k₁ : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  k₂ : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput

def TreeStagesBatchPeerData.real {base : HashCache C} (d : TreeStagesBatchPeerData C E base) :
    PartyM C E RealSpec TreeOutput :=
  treeStagesBatchPeerProgram K d.ctx₁ d.jobs d.idx d.count d.value₁ d.st₁ d.k₁

def TreeStagesBatchPeerData.ideal {base : HashCache C} (d : TreeStagesBatchPeerData C E base) :
    PartyM C E RealSpec TreeOutput :=
  treeStagesBatchPeerProgram K d.ctx₂ d.jobs d.idx d.count d.value₂ d.st₂ d.k₂

def TreeStagesBatchPeerData.rel {base : HashCache C} (d : TreeStagesBatchPeerData C E base)
    (δ : HiddenAddress C → Bit) (x y : Step C E RealSpec TreeOutput) : Prop :=
  let inputs₁ := d.jobs.map (treeStagesCachedInputs base d.ctx₁)
  let inputs₂ := d.jobs.map (treeStagesCachedInputs base d.ctx₂)
  TreeSimPeerRel K δ d.ctx₁ d.ctx₂ d.idx d.count (d.value₁ inputs₁) (d.value₂ inputs₂)
    d.st₁ d.st₂ (d.k₁ inputs₁) (d.k₂ inputs₂) x y

theorem TreeStagesBatchPeerData.entry {base : HashCache C} (d : TreeStagesBatchPeerData C E base)
    (D : C.Coalition) (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (d.real K).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance (d.ideal K).run))).run b)
      (fun u z => d.rel K δ u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) :=
  treeStages_batchPeer_entry prims K D δ visible d.ctx₁ d.ctx₂ d.self d.keys d.jobs d.idx d.count
    base d.covered₁ d.covered₂ d.value₁ d.value₂ d.st₁ d.st₂ d.label d.k₁ d.k₂ a b related grows

/-- The post-opening relation retains each party's actual reconstruction,
including selective aborts, and its complete next-batch peer continuation. -/
def TreeStagesOpenBatchPeerRel (base : HashCache C) (δ : HiddenAddress C → Bit)
    (next : C.Party → (ℕ → Bit) → TreeStagesBatchPeerData C E base)
    (i : C.Party) (x y : Step C E RealSpec TreeOutput) : Prop :=
  (x = .done none ∧ y = .done none) ∨ ∃ out, (next i out).rel K δ x y

/-- Actual copy checks followed by actual next-batch inputs and peer PRSS.
This supplies the frozen local closure without a continuation-coupling
hypothesis. The cache may already contain dealer and earlier batch queries. -/
def treeStages_openBatchPeer_localClosure (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (next : C.Party → (ℕ → Bit) → TreeStagesBatchPeerData C E base) :
    TreeSimOpenLocalClosure prims K D live count v ds sent
      (fun i out => (next i out).real K) (fun i out => (next i out).ideal K) where
  J := fun a b => TreeSimStreamRel δ a b ∧ base ≤ a.1.1
  Q := TreeStagesOpenBatchPeerRel K base δ next
  cache := fun _ _ h => h.1.1
  head := by
    intro i a b out u z h hsu _ _ _ hc hf₁ hf₂
    refine ⟨⟨hc, ?_⟩, h.2.trans (treeSim_logged_grows prims D _ a u hsu)⟩
    simpa only [hf₁, hf₂] using h.1.2
  abort := fun _ => Or.inl ⟨rfl, rfl⟩
  continues := by
    intro i a b out u z _ _ _ _ _ hj
    apply relTriple_post_mono ((next i out).entry prims K D δ visible u.2 z.2 hj.1 hj.2)
    intro x y hxy
    exact ⟨Or.inr ⟨out, hxy.1⟩, hxy.2⟩

/-- A full nonterminal OpenRep round, through the next batch's real input
queries and PRSS draw. Operator order, rushing and aborts are unchanged. -/
theorem treeStages_openBatchPeer_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (next : C.Party → (ℕ → Bit) → TreeStagesBatchPeerData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out => (next i out).real K))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out => (next i out).ideal K))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∀ i, TreeStagesOpenBatchPeerRel K base δ next i (u.1.2.1 i) (z.1.2.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [stepRound_real, stepRound_real]
  have view := treeSim_open_view K D live count v ds (fun i out => (next i out).real K)
    (fun i out => (next i out).ideal K)
  unfold treeSimRoundView at view
  rw [view]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D δ _ a b related))
  intro u z hu
  rw [← hu.1.1]
  let close := treeStages_openBatchPeer_localClosure prims K D live count v ds u.1.2 base δ visible next
  apply relTriple_bind (close.all prims K D live count v ds u.1.2 _ _ u.2 z.2
    ⟨hu.1.2.1, grows.trans (treeSim_logged_grows prims D _ a u hu.2.1)⟩)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, hp⟩

/-- Number of sharings in the first exchange of a peer-mode batch. -/
def treeStagesPeerHeadCount (circs : List Circuit) : ℕ :=
  match List.range (depth circs) with
  | [] => (outputsOf circs).length
  | layer :: _ => (gatesAt circs layer).length

/-- Factor the first actual peer entry of a batch. A batch with no AND
layers starts at Rerand; otherwise its first layer starts at multiplication.
The remaining real gadgets, run state and caller continuation are retained. -/
theorem treeStages_runJobs_peer_head (ctx : Context C) (gadgets : RunGadgets C E RealSpec)
    (circs : List Circuit) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (mult : ∀ x y count, gadgets.mult x y count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshare K ctx bitCodec rnd (mulRep K ctx x y) count))
    (rerand : ∀ v count, gadgets.rerand v count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count)) :
    ∃ (value : List (C.Term → List Bit) → ℕ → Bit)
      (k : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput),
      ∀ inputs, ((runJobs K gadgets circs inputs).run st >>= finish) =
        treeSimPeerProgram K ctx 0 (treeStagesPeerHeadCount circs) (value inputs) st (k inputs) := by
  generalize layers : List.range (depth circs) = ls
  cases ls with
  | nil =>
    simp only [treeStagesPeerHeadCount, layers]
    refine ⟨(fun inputs => ownerSum K ctx (outputShares K circs inputs)),
      (fun inputs z => ((do
        gadgets.verify [⟨outputShares K circs inputs, one K, z.1, (outputsOf circs).length, .peer⟩]
        let opened ← gadgets.output z.1 (outputsOf circs).length
        pure (assemble circs opened)).run z.2 >>= finish)), ?_⟩
    intro inputs
    simp only [treeSimPeerProgram, runJobs_eq, layers, List.foldlM_nil, pure_bind, tailBody, rerand,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, List.nil_append]
  | cons layer ls =>
    simp only [treeStagesPeerHeadCount, layers]
    refine ⟨
      (fun inputs => mulRep K ctx (layerX K circs layer inputs) (layerY K circs layer inputs)),
      (fun inputs z => ((ls.foldlM (layerBody K gadgets circs)
        (appendLayer circs layer inputs z.1,
          [⟨layerX K circs layer inputs, layerY K circs layer inputs, z.1,
            (gatesAt circs layer).length, gadgets.mode⟩]) >>= tailBody K gadgets circs).run z.2 >>= finish)), ?_⟩
    intro inputs
    simp only [treeSimPeerProgram, runJobs_eq, layers, List.foldlM_cons, layerBody, mult,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, List.nil_append]

/-- Both real and simulated peer-mode batches have the concrete next-entry
form used above. The simulator's actual output override stays in the tail. -/
theorem treeStages_simBatch_peer_head (D : C.Coalition) (ctx : Context C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (st : RunState C)
    (mode : settings.mode = .peer)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    ∃ count value k,
      ((jobs.mapM (inputShares ctx) >>= fun inputs =>
        (runJobs K (treeSimGadgets K circuits settings D parameter seeds openings ctx batch jobs)
          (jobs.map (circuits parameter ·.kind)) inputs).run st >>= finish) : PartyM C E RealSpec TreeOutput) =
        treeStagesBatchPeerProgram K ctx jobs 0 count value st k := by
  obtain ⟨value, k, head⟩ := treeStages_runJobs_peer_head K ctx
    (treeSimGadgets K circuits settings D parameter seeds openings ctx batch jobs)
    (jobs.map (circuits parameter ·.kind)) st finish
    (by intro x y n; simp [treeSimGadgets, realRunGadgets, mode, reshareWith])
    (by intro v n; rfl)
  refine ⟨treeStagesPeerHeadCount (jobs.map (circuits parameter ·.kind)), value, k, ?_⟩
  unfold treeStagesBatchPeerProgram
  apply bind_congr
  exact head

/-- Build the next-entry data from the actual real and simulated batches.
No program-shape or gadget-coupling premise remains. Both cases of the public
circuit depth use the same first-exchange size. -/
theorem treeStages_actualPeerBatchData (D : C.Coalition) (base : HashCache C)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (covered₁ : TreeStagesPrfCovered base ctx₁.keys.seed jobs)
    (covered₂ : TreeStagesPrfCovered base ctx₂.keys.seed jobs)
    (st₁ st₂ : RunState C) (label : st₁.label = st₂.label) (mode : settings.mode = .peer)
    (finish₁ finish₂ : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    ∃ d : TreeStagesBatchPeerData C E base,
      d.real K = (jobs.mapM (inputShares ctx₁) >>= fun inputs =>
        (runJobs K (realRunGadgets K ctx₁ settings.mode)
          (jobs.map (circuits parameter ·.kind)) inputs).run st₁ >>= finish₁) ∧
      d.ideal K = (jobs.mapM (inputShares ctx₂) >>= fun inputs =>
        (runJobs K (treeSimGadgets K circuits settings D parameter ctx₂.keys.seed openings ctx₂ batch jobs)
          (jobs.map (circuits parameter ·.kind)) inputs).run st₂ >>= finish₂) := by
  obtain ⟨value₁, k₁, head₁⟩ := treeStages_runJobs_peer_head K ctx₁
    (realRunGadgets K ctx₁ settings.mode) (jobs.map (circuits parameter ·.kind)) st₁ finish₁
    (by intro x y n; simp [realRunGadgets, mode, reshareWith]) (by intro v n; rfl)
  obtain ⟨value₂, k₂, head₂⟩ := treeStages_runJobs_peer_head K ctx₂
    (treeSimGadgets K circuits settings D parameter ctx₂.keys.seed openings ctx₂ batch jobs)
    (jobs.map (circuits parameter ·.kind)) st₂ finish₂
    (by intro x y n; simp [treeSimGadgets, realRunGadgets, mode, reshareWith]) (by intro v n; rfl)
  refine ⟨⟨ctx₁, ctx₂, self, keys, jobs, 0, treeStagesPeerHeadCount (jobs.map (circuits parameter ·.kind)),
    covered₁, covered₂, value₁, value₂, st₁, st₂, label, k₁, k₂⟩, ?_, ?_⟩
  · unfold TreeStagesBatchPeerData.real treeStagesBatchPeerProgram
    apply bind_congr
    intro inputs
    exact (head₁ inputs).symm
  · unfold TreeStagesBatchPeerData.ideal treeStagesBatchPeerProgram
    apply bind_congr
    intro inputs
    exact (head₂ inputs).symm

/-- The concrete nonterminal transition supplies the frozen OpenRep boundary
interface. Only membership of the resulting configurations in the global
ceremony invariant is a remaining deterministic obligation. -/
theorem treeStages_openBatchPeer_boundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (state : A.State) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (next : C.Party → (ℕ → Bit) → TreeStagesBatchPeerData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1)
    (finish : ∀ state steps₁ steps₂ a b,
      (∀ i, TreeStagesOpenBatchPeerRel K base δ next i (steps₁ i) (steps₂ i)) →
      TreeSimStreamRel δ a b → base ≤ a.1.1 → Bad a ∨ Inv ((state, steps₁), a) ((state, steps₂), b)) :
    TreeSimOpenBoundary prims K D A Bad Inv
      ((state, treeSimOpenPartial K D live count v ds (fun i out => (next i out).real K)), a)
      ((state, treeSimOpenPartial K D live count v ds (fun i out => (next i out).ideal K)), b) := by
  refine ⟨δ, live, count, v, ds, (fun i out => (next i out).real K),
    (fun i out => (next i out).ideal K), rfl, related, rfl, rfl, ⟨{ next := ?_ }⟩⟩
  intro state' sent u z reach rel _ _
  let close := treeStages_openBatchPeer_localClosure prims K D live count v ds sent base δ visible next
  refine ⟨close, ⟨rel, grows.trans (treeSim_logged_grows prims D _ a _ reach.1)⟩, ?_⟩
  intro x y _ _ hxy hj
  exact finish state' x.1 y.1 x.2 y.2 hxy hj.1 hj.2

/-- A computation containing only hash calls leaves the hidden cache alone. -/
theorem treeStages_hashOnly_onHash {α : Type} (D : C.Coalition)
    (p : OracleComp (Query C →ₒ HashOutput) α) :
    simulateQ (streamWorld prims D) (free (liftComp (simulateQ (hashQuery (C := C)) p) (LocalSpec C))) =
      onHash (simulateQ (hashAnswer prims) p) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [liftComp_pure, free_pure, treeStages_onHash_pure]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftComp_bind, free_bind,
      treeStages_onHash_bind, ih]
    have single : simulateQ (streamWorld prims D)
        (free (liftComp (hashQuery (C := C) q) (LocalSpec C))) =
          onHash (hashAnswer prims q) := by
      unfold hashQuery
      erw [simulateQ_spec_query]
      rfl
    rw [single]

/-- The hash-only spelling of the actual input program. -/
def treeStagesInputHashes (ctx : Context C) (job : Job) :
    OracleComp (Query C →ₒ HashOutput) (C.Term → List Bit) := do
  let terms ← C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then job.points.flatMapM fun x =>
      (bitsOfDigest ∘ truncateHash) <$> OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) (.prf (ctx.keys.seed T) x))
    else pure []
  pure fun T => terms.getD (C.terms.idxOf T) []

theorem treeStages_inputHashes (ctx : Context C) (job : Job) :
    simulateQ (hashQuery (C := C)) (treeStagesInputHashes ctx job) = inputQuery ctx job := by
  have points (T : C.Term) :
      simulateQ (hashQuery (C := C)) (job.points.flatMapM fun x =>
        (bitsOfDigest ∘ truncateHash) <$> OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) (.prf (ctx.keys.seed T) x))) =
      job.points.flatMapM (fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x) := by
    induction job.points with
    | nil => simp
    | cons x xs ih => simp [List.flatMapM_cons, ih, prf, Functor.map_map]
  simp only [treeStagesInputHashes, inputQuery, simulateQ_bind, simulateQ_pure,
    simulateQ_list_mapM]
  congr 1
  apply congrArg (List.mapM · C.terms)
  funext T
  split_ifs <;> simp [points]

theorem treeStages_inputQueries_onHash (D : C.Coalition) (ctx : Context C) (jobs : List Job) :
    simulateQ (streamWorld prims D)
      (free (liftComp (jobs.mapM (inputQuery ctx)) (LocalSpec C))) =
      onHash (simulateQ (hashAnswer prims) (jobs.mapM (treeStagesInputHashes ctx))) := by
  have inputs : simulateQ (hashQuery (C := C)) (jobs.mapM (treeStagesInputHashes ctx)) =
      jobs.mapM (inputQuery ctx) := by simp only [simulateQ_list_mapM, treeStages_inputHashes]
  rw [← inputs]
  exact treeStages_hashOnly_onHash prims D _

/-- Every adaptive public leanXMSS computation acts only on the shared
hash cache. This includes previously cached dealer answers and fixed `Th`
inputs; it does not assume that the public queries are fresh. -/
theorem treeStages_tweakable_onHash {α : Type} (D : C.Coalition)
    (p : OracleComp HashSpec α) :
    simulateQ (streamWorld prims D) (free (liftComp (tweakable (C := C) p) (LocalSpec C))) =
      onHash (simulateQ (fun q => hashAnswer prims (.hash q)) p) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [tweakable, liftComp_pure, free_pure, treeStages_onHash_pure]
  | query_bind q k ih =>
    simp only [tweakable] at *
    simp only [simulateQ_bind, simulateQ_spec_query, liftComp_bind, free_bind,
      treeStages_onHash_bind, ih]
    have single : simulateQ (streamWorld prims D)
        (free (liftComp (hashQuery (C := C) (.hash q)) (LocalSpec C))) =
          onHash (hashAnswer prims (.hash q)) := by
      unfold hashQuery
      erw [simulateQ_spec_query]
      rfl
    rw [single]

/-- The actual public computation between two batches, followed by next
input queries and the next peer entry. The public result may choose the jobs
and the full saved continuation adaptively. -/
theorem treeStages_publicBatchPeer_entry {α : Type} (D : C.Coalition)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : OracleComp HashSpec α) (next : α → TreeStagesBatchPeerData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        ((oracleStep (tweakable pubCode) >>= fun x => (next x).real K).run)))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        ((oracleStep (tweakable pubCode) >>= fun x => (next x).ideal K).run)))).run b)
      (fun u z => (∃ x, (next x).rel K δ u.1 z.1) ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_onHash_coupling prims D _ _
    (treeStages_tweakable_onHash prims D pubCode) δ a b related))
  intro u z hu
  rw [← hu.1.1]
  apply relTriple_post_mono ((next u.1).entry prims K D δ visible u.2 z.2 hu.1.2.1
    (grows.trans (treeSim_logged_grows prims D _ a u hu.2.1)))
  intro x y hxy
  exact ⟨⟨u.1, hxy.1⟩, hxy.2⟩

/-- Extend the nonterminal opening closure through the actual adaptive
public leanXMSS code between batches, as well as input and PRSS queries. -/
def treeStages_openPublicBatchPeer_localClosure {α : Type} (D : C.Coalition)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : C.Party → (ℕ → Bit) → OracleComp HashSpec α)
    (next : C.Party → (ℕ → Bit) → α → TreeStagesBatchPeerData C E base) :
    TreeSimOpenLocalClosure prims K D live count v ds sent
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K)
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K) where
  J := fun a b => TreeSimStreamRel δ a b ∧ base ≤ a.1.1
  Q := fun i x y => (x = .done none ∧ y = .done none) ∨ ∃ out result, (next i out result).rel K δ x y
  cache := fun _ _ h => h.1.1
  head := by
    intro i a b out u z h hsu _ _ _ hc hf₁ hf₂
    refine ⟨⟨hc, ?_⟩, h.2.trans (treeSim_logged_grows prims D _ a u hsu)⟩
    simpa only [hf₁, hf₂] using h.1.2
  abort := fun _ => Or.inl ⟨rfl, rfl⟩
  continues := by
    intro i a b out u z _ _ _ _ _ hj
    apply relTriple_post_mono (treeStages_publicBatchPeer_entry prims K D base δ visible
      (pubCode i out) (next i out) u.2 z.2 hj.1 hj.2)
    intro x y hxy
    exact ⟨Or.inr ⟨out, hxy.1⟩, hxy.2⟩

/-- Full nonterminal OpenRep preservation through public computation and
next-batch entry, with no assumed coupling of any of those computations. -/
theorem treeStages_openPublicBatchPeer_round {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : C.Party → (ℕ → Bit) → OracleComp HashSpec α)
    (next : C.Party → (ℕ → Bit) → α → TreeStagesBatchPeerData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out =>
          oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out =>
          oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∀ i, (u.1.2.1 i = .done none ∧ z.1.2.1 i = .done none) ∨
          ∃ out result, (next i out result).rel K δ (u.1.2.1 i) (z.1.2.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [stepRound_real, stepRound_real]
  have view := treeSim_open_view K D live count v ds
    (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K)
    (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K)
  unfold treeSimRoundView at view
  rw [view]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D δ _ a b related))
  intro u z hu
  rw [← hu.1.1]
  let close := treeStages_openPublicBatchPeer_localClosure prims K D live count v ds u.1.2 base δ visible pubCode next
  apply relTriple_bind (close.all prims K D live count v ds u.1.2 _ _ u.2 z.2
    ⟨hu.1.2.1, grows.trans (treeSim_logged_grows prims D _ a u hu.2.1)⟩)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, hp⟩

/-- All PRF points form a finite domain, including points selected by
later public computations. No bound on the number of adaptive jobs is used. -/
def treeStagesAllPoints : List Point :=
  ((Finset.univ : Finset (Layer × KeyIndex × ChainIndex × Digit)).toList.map
    (fun (lay, e, l, p) => Point.chain lay e l p)) ++
  ((Finset.univ : Finset (Layer × KeyIndex)).toList.map (fun (lay, e) => Point.randomizer lay e))

theorem treeStages_mem_allPoints (x : Point) : x ∈ treeStagesAllPoints := by
  cases x <;> simp [treeStagesAllPoints]

/-- Full PRF coverage for a fixed finite list of seed values. -/
def TreeStagesSeedsCovered (cache : HashCache C) (seeds : List HashOutput) : Prop :=
  ∀ seed ∈ seeds, ∀ x : Point, ∃ h, cache (.prf seed x) = some h

def treeStagesSeedPadding (seeds : List HashOutput) : OracleComp (LocalSpec C) Unit := do
  let qs : List (Query C) := seeds.flatMap fun seed => treeStagesAllPoints.map (Query.prf seed)
  let _ ← qs.mapM fun q => liftComp (hashQuery q) (LocalSpec C)
  pure ()

theorem treeStages_seedPadding_covered (seeds : List HashOutput) (cache : HashCache C)
    (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (treeStagesSeedPadding (C := C) seeds)).run cache)) :
    cache ≤ r.2 ∧ TreeStagesSeedsCovered r.2 seeds := by
  simp only [treeStagesSeedPadding, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  obtain ⟨grows, covered⟩ := treeStages_prefetch_queries prims _ (by
    intro q hq
    obtain ⟨seed, _, x, _, rfl⟩ := by simpa only [List.mem_flatMap, List.mem_map] using hq
    rintro ⟨_, heq, _⟩
    cases heq) cache u hu
  refine ⟨grows, ?_⟩
  intro seed hs x
  apply covered
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨seed, hs, x, treeStages_mem_allPoints x, rfl⟩

theorem treeStages_seedsCovered_mono {a b : HashCache C} (h : a ≤ b)
    (seeds : List HashOutput) (covered : TreeStagesSeedsCovered a seeds) :
    TreeStagesSeedsCovered b seeds := by
  intro seed hs x
  obtain ⟨v, hv⟩ := covered seed hs x
  exact ⟨v, h hv⟩

theorem treeStages_seedsCovered_jobs (cache : HashCache C) (seeds : List HashOutput)
    (covered : TreeStagesSeedsCovered cache seeds) (termSeeds : C.Term → HashOutput)
    (mem : ∀ T, termSeeds T ∈ seeds) (jobs : List Job) :
    TreeStagesPrfCovered cache termSeeds jobs := by
  intro job _ x _ T
  exact covered (termSeeds T) (mem T) x

/-- One concrete finite prefix covers the real and dummy seeds for every
later batch, including adaptively chosen jobs. It preserves all dealer answers. -/
def treeStagesCeremonyPrfPadding (seeds : C.Term → HashOutput) : OracleComp (LocalSpec C) Unit :=
  treeStagesSeedPadding (0 :: C.terms.map seeds)

theorem treeStages_ceremonyPrfPadding_covered (D : C.Coalition) (seeds : C.Term → HashOutput)
    (cache : HashCache C) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (treeStagesCeremonyPrfPadding seeds)).run cache)) :
    cache ≤ r.2 ∧ ∀ jobs,
      TreeStagesPrfCovered r.2 seeds jobs ∧
      TreeStagesPrfCovered r.2 (fun T => if KnownTo D.1 T then seeds T else 0) jobs := by
  obtain ⟨grows, covered⟩ := treeStages_seedPadding_covered prims _ cache r hr
  refine ⟨grows, fun jobs => ⟨?_, ?_⟩⟩
  · exact treeStages_seedsCovered_jobs r.2 _ covered seeds
      (fun T => by simp [Committee.terms]) jobs
  · apply treeStages_seedsCovered_jobs r.2 _ covered _ _ jobs
    intro T
    split_ifs <;> simp [Committee.terms]

/-- The actual simulator batch output with an arbitrary saved continuation. -/
def treeStagesSimBatchResume (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) (ctx : Context C)
    (batch : ℕ) (jobs : List Job) (widths : List ℕ) (v : Shares C Bit) (st : RunState C)
    (k : List (List Bit) → PartyM C E RealSpec TreeOutput) : PartyM C E RealSpec TreeOutput := do
  let out ← ((treeSimGadgets K circuits settings D parameter seeds openings ctx batch jobs).output v widths.sum).run st
  k (treeStagesBatchDecode widths out.1)

/-- The simulator's output-prefix alignment preserves both full saved
continuations, so it applies to nonterminal ceremony batches. -/
theorem treeStages_simBatch_resume_entry (D : C.Coalition) (i : C.Party)
    (ctx₁ ctx₂ : Context C) (self₁ : ctx₁.self = i) (self₂ : ctx₂.self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : Shares C Bit) (st : RunState C)
    (k₁ k₂ : List (List Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((openRep K ctx₁ v widths.sum >>= fun out => k₁ (treeStagesBatchDecode widths out)).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeStagesSimBatchResume K circuits settings D parameter seeds openings ctx₂ batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) v) st k₂).run)))).run b)
      (fun u z =>
        u.1 = treeSimOpenStep K i widths.sum v (treeStagesCopyDigests widths.sum a.1.1 v)
          (fun out => k₁ (treeStagesBatchDecode widths out)) ∧
        z.1 = treeSimOpenStep K i widths.sum v (treeStagesCopyDigests widths.sum a.1.1 v)
          (fun out => k₂ (treeStagesBatchDecode widths out)) ∧
        u.2.1 = a.1 ∧ z.2 = b ∧ TreeSimStreamRel δ u.2 z.2) := by
  unfold treeStagesSimBatchResume
  rw [treeStages_simOutput_advance prims K circuits settings D parameter seeds openings ctx₂
    batch widths.sum jobs _ st _ b prfCovered, clearEq]
  rw [treeStages_openRep_shift_prefix K D ctx₂ widths.sum _ _ _
    (fun x y h => congrArg k₂ (treeStages_batchDecode_prefix widths x y h))]
  exact treeStages_open_entry_padded prims K D i ctx₁ ctx₂ self₁ self₂ widths.sum v _
    (fun T hT => (treeSim_open_shift_held D i widths.sum
      (treeStagesCorrection openings batch clear) v T hT).symm)
    (fun out => k₁ (treeStagesBatchDecode widths out))
    (fun out => k₂ (treeStagesBatchDecode widths out)) δ a b related covered

/-- Ordered partial entries with arbitrary saved batch continuations. -/
theorem treeStages_simBatch_resume_partial (D : C.Coalition) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k₁ k₂ : C.Party → List (List Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
          k₁ i (treeStagesBatchDecode widths out))
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll
        (fun i (_ : Unit) => treeStagesSimBatchResume K circuits settings D parameter seeds openings
          (ctx₂ i) batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (k₂ i))
        (fun i => if i ∈ D.1 then none else if live i then some () else none))).run b)
      (fun u z =>
        u.1 = treeSimOpenPartial K D live widths.sum v
          (fun i => treeStagesCopyDigests widths.sum a.1.1 (v i))
          (fun i out => k₁ i (treeStagesBatchDecode widths out)) ∧
        z.1 = treeSimOpenPartial K D live widths.sum v
          (fun i => treeStagesCopyDigests widths.sum a.1.1 (v i))
          (fun i out => k₂ i (treeStagesBatchDecode widths out)) ∧ u.2.1 = a.1 ∧ z.2 = b ∧ TreeSimStreamRel δ u.2 z.2) := by
  let expected₁ := treeSimOpenPartial K D live widths.sum v
    (fun i => treeStagesCopyDigests widths.sum a.1.1 (v i))
    (fun i out => k₁ i (treeStagesBatchDecode widths out))
  let expected₂ := treeSimOpenPartial K D live widths.sum v
    (fun i => treeStagesCopyDigests widths.sum a.1.1 (v i))
    (fun i out => k₂ i (treeStagesBatchDecode widths out))
  let J := fun s t => s.1 = a.1 ∧ t = b ∧ TreeSimStreamRel δ s t
  let Q := fun i x y => x = expected₁ i ∧ y = expected₂ i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ _ _ J Q ?_ a b ⟨rfl, rfl, related⟩)
  · intro u z hu
    exact ⟨funext (fun i => (hu.1 i).1), funext (fun i => (hu.1 i).2), hu.2⟩
  · intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨by simp [expected₁, treeSimOpenPartial, hi], by simp [expected₂, treeSimOpenPartial, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume]
        apply relTriple_post_mono (treeStages_simBatch_resume_entry prims K circuits settings D i
          (ctx₁ i) (ctx₂ i) (self₁ i hi) (self₂ i hi) parameter seeds openings batch jobs widths
          clear (v i) (st i) (k₁ i) (k₂ i) δ s t hst.2.2
          (by rw [hst.1]; exact covered) (by rw [hst.2.1]; exact prfCovered)
          (by rw [hst.2.1]; exact clearEq))
        intro u z hu
        refine ⟨⟨?_, ?_⟩, hu.2.2.1.trans hst.1, hu.2.2.2.1.trans hst.2.1, hu.2.2.2.2⟩
        · simpa only [expected₁, treeSimOpenPartial, if_neg hi, if_pos hl, hst.1] using hu.1
        · simpa only [expected₂, treeSimOpenPartial, if_neg hi, if_pos hl, hst.1] using hu.2.1
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨by simp [expected₁, treeSimOpenPartial, hi, hl], by simp [expected₂, treeSimOpenPartial, hi, hl]⟩, hst⟩

/-- The actual final-check exchange for nonterminal batches, retaining both
saved continuations through the simulator's clear queries and correction. -/
theorem treeStages_simBatch_resume_check_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k₁ k₂ : C.Party → List (List Bit) → PartyM C E RealSpec TreeOutput)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
          k₁ i (treeStagesBatchDecode widths out)))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live kind (fun i => treeStagesSimBatchResume K circuits settings D
          parameter seeds openings (ctx₂ i) batch jobs widths
          (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (k₂ i)))).run b)
      (fun u z => ∃ sent ds,
        let active := fun i => (treeSimCheckResult K D live kind sent i).isSome
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimOpenPartial K D active widths.sum v ds
          (fun i out => k₁ i (treeStagesBatchDecode widths out)) ∧
        z.1.2.1 = treeSimOpenPartial K D active widths.sum v ds
          (fun i out => k₂ i (treeStagesBatchDecode widths out)) ∧ TreeSimStreamRel δ u.2 z.2 ∧
        TreeStagesCopyCovered widths.sum u.2.1.1 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_check_round_factor, treeSim_check_round_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D δ _ a b related))
  intro u z hu
  have hc := hu.1
  have grows := treeSim_logged_grows prims D _ a u hu.2.1
  have cover := treeStages_copyCovered_mono widths.sum grows covered
  have idealGrows : b.1 ≤ z.2.1 := by rw [← related.1, ← hc.2.1.1]; exact grows
  have prfCover := treeStages_prfCovered_mono idealGrows seeds jobs prfCovered
  have replay := (treeStages_cachedJobs_mono circuits idealGrows parameter seeds jobs prfCovered).symm.trans clearEq
  rw [← hc.1]
  let active := fun i => (treeSimCheckResult K D live kind u.1.2 i).isSome
  have shape : treeSimCheckResult K D live kind u.1.2 =
      fun i => if i ∈ D.1 then none else if active i then some () else none := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCheckResult, hi]
    · rw [if_neg hi]
      cases hv : treeSimCheckResult K D live kind u.1.2 i <;> simp [active, hv]
  rw [shape]
  apply relTriple_bind (treeStages_simBatch_resume_partial prims K circuits settings D active ctx₁ ctx₂ self₁ self₂
    parameter seeds openings batch jobs widths clear v st k₁ k₂ δ u.2 z.2 hc.2.1 cover prfCover replay)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  refine ⟨u.1.2, (fun i => treeStagesCopyDigests widths.sum u.2.1.1 (v i)),
    rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2.2.2, ?_, ?_, ?_⟩
  · simpa only [hp.2.2.1] using cover
  · exact (congrArg Prod.snd hp.2.2.1).trans hc.2.2.1
  · exact (congrArg Prod.snd hp.2.2.2.1).trans hc.2.2.2

/-- Compose the actual check and opening transitions of a nonterminal
batch. The simulator's clear replay and correction precede OpenRep; afterward
the real copy checks, public computation, next inputs and PRSS entry run in
operator order. No coupling of a later continuation is an assumption. -/
theorem treeStages_simBatch_nextPeer_rounds {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : C.Party → List (List Bit) → OracleComp HashSpec α)
    (next : C.Party → List (List Bit) → α → TreeStagesBatchPeerData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1)
    (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    let k₁ := fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K
    let k₂ := fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K
    RelTriple
      ((do
        let p ← stepRound (treeSimRealRoles prims D) D A noFunctionality state
          (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
            k₁ i (treeStagesBatchDecode widths out)))
        stepRound (treeSimRealRoles prims D) D A noFunctionality p.1 p.2.1).run a)
      ((do
        let p ← stepRound (treeSimIdealRoles prims D) D A noFunctionality state
          (treeSimCheckWaiting K D live kind (fun i => treeStagesSimBatchResume K circuits settings D
            parameter seeds openings (ctx₂ i) batch jobs widths
            (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (k₂ i)))
        stepRound (treeSimIdealRoles prims D) D A noFunctionality p.1 p.2.1).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∀ i, (u.1.2.1 i = .done none ∧ z.1.2.1 i = .done none) ∨
          ∃ out result, (next i (treeStagesBatchDecode widths out) result).rel K δ (u.1.2.1 i) (z.1.2.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  simp only [StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeStages_simBatch_resume_check_round prims K circuits settings D A state live kind
      ctx₁ ctx₂ self₁ self₂ parameter seeds openings batch jobs widths clear v st
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K)
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K)
      δ a b related covered prfCovered clearEq))
  intro u z hu
  obtain ⟨sent, ds, same, _, _, steps₁, steps₂, hc, _⟩ := hu.1
  have support := hu.2.1
  simp only [← simulateQ_stepRound, treeSimRealRoles] at support
  have grows' := grows.trans (treeSim_logged_grows prims D _ a u support)
  rw [steps₁, steps₂, ← same]
  exact treeStages_openPublicBatchPeer_round prims K D A u.1.1 _ widths.sum v ds base δ visible
    (fun i out => pubCode i (treeStagesBatchDecode widths out))
    (fun i out => next i (treeStagesBatchDecode widths out)) u.2 z.2 hc grows'

/-- The real first reshare program, for either configured mode. -/
def treeStagesReshareProgram (ctx : Context C) (mode : ReshareMode) (idx count : ℕ)
    (v : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) : PartyM C E RealSpec TreeOutput :=
  (prssRandomness ctx bitCodec idx count >>= fun rnd => reshareWith K ctx mode rnd v count).run st >>= k

/-- The suspended first exchange records the actual mode, PRSS masks and
saved continuation. Collector forwarding remains in the collector step. -/
def TreeStagesReshareEntryRel (mode : ReshareMode) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (idx count : ℕ) (v₁ v₂ : ℕ → Bit)
    (st₁ st₂ : RunState C)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (x y : Step C E RealSpec TreeOutput) : Prop :=
  match mode with
  | .peer => TreeSimPeerRel K δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y
  | .collector => TreeSimCollectorEntryRel K δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ x y

theorem treeStages_reshare_entry (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (mode : ReshareMode) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C) (label : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        ((treeStagesReshareProgram K ctx₁ mode idx count v₁ st₁ k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        ((treeStagesReshareProgram K ctx₂ mode idx count v₂ st₂ k₂).run)))).run b)
      (fun u z => TreeStagesReshareEntryRel K mode δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  cases mode with
  | peer =>
    exact treeSim_peer_start_mixed prims K D δ visible ctx₁ ctx₂ self keys idx count
      v₁ v₂ st₁ st₂ label k₁ k₂ a b related
  | collector =>
    exact treeSim_collector_entry_mixed prims K D δ visible ctx₁ ctx₂ self keys idx count
      v₁ v₂ st₁ st₂ label k₁ k₂ a b related

/-- Actual next input queries followed by the configured reshare entry. -/
def treeStagesBatchProgram (ctx : Context C) (mode : ReshareMode) (jobs : List Job) (idx count : ℕ)
    (value : List (C.Term → List Bit) → ℕ → Bit) (st : RunState C)
    (k : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) :
    PartyM C E RealSpec TreeOutput := do
  let inputs ← jobs.mapM (inputShares ctx)
  treeStagesReshareProgram K ctx mode idx count (value inputs) st (k inputs)

 /-- Both modes replay inputs and couple their real PRSS entry, including
repeated stream reads and the dealer's populated public cache. -/
theorem treeStages_batch_entry (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (mode : ReshareMode) (jobs : List Job) (idx count : ℕ) (base : HashCache C)
    (covered₁ : TreeStagesPrfCovered base ctx₁.keys.seed jobs)
    (covered₂ : TreeStagesPrfCovered base ctx₂.keys.seed jobs)
    (value₁ value₂ : List (C.Term → List Bit) → ℕ → Bit)
    (st₁ st₂ : RunState C) (label : st₁.label = st₂.label)
    (k₁ k₂ : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (base_le : base ≤ a.1.1) :
    let inputs₁ := jobs.map (treeStagesCachedInputs base ctx₁)
    let inputs₂ := jobs.map (treeStagesCachedInputs base ctx₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((treeStagesBatchProgram K ctx₁ mode jobs idx count value₁ st₁ k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeStagesBatchProgram K ctx₂ mode jobs idx count value₂ st₂ k₂).run)))).run b)
      (fun u z => TreeStagesReshareEntryRel K mode δ ctx₁ ctx₂ idx count (value₁ inputs₁) (value₂ inputs₂)
        st₁ st₂ (k₁ inputs₁) (k₂ inputs₂) u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  have base_le₂ : base ≤ b.1 := by rw [← related.1]; exact base_le
  have replay₁ := treeStages_inputQueries_replay prims D ctx₁ jobs a.1
    (treeStages_prfCovered_mono base_le _ _ covered₁)
  have replay₂ := treeStages_inputQueries_replay prims D ctx₂ jobs b
    (treeStages_prfCovered_mono base_le₂ _ _ covered₂)
  rw [← treeStages_cachedInputs_mono base_le ctx₁ jobs covered₁] at replay₁
  rw [← treeStages_cachedInputs_mono base_le₂ ctx₂ jobs covered₂] at replay₂
  unfold treeStagesBatchProgram
  simp only [inputShares_fun, mapM_oracleStep, worldRoles, advance_oracleStep_bind,
    free_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeStages_readOnly_pair prims D _ _ a b _ _ replay₁ replay₂)
  intro u z hu
  rw [hu.1, hu.2.1]
  have rel : TreeSimStreamRel δ u.2 z.2 := by
    simpa only [TreeSimStreamRel, hu.2.2.1, hu.2.2.2] using related
  apply relTriple_post_mono (treeSim_relTriple_support (treeStages_reshare_entry prims K D δ visible mode
    ctx₁ ctx₂ self keys idx count _ _ st₁ st₂ label _ _ u.2 z.2 rel))
  intro x y hxy
  have grows : base ≤ u.2.1.1 := by rw [hu.2.2.1]; exact base_le
  exact ⟨hxy.1.1, hxy.1.2, grows.trans (treeSim_logged_grows prims D _ u.2 x hxy.2.1)⟩

/-- Next-batch data with its actual first-exchange mode. A zero-layer
collector-mode batch still starts with the peer Rerand gadget. -/
structure TreeStagesBatchData (C : Committee) (E : Type) (base : HashCache C)
    extends TreeStagesBatchPeerData C E base where
  mode : ReshareMode

def TreeStagesBatchData.real {base : HashCache C} (d : TreeStagesBatchData C E base) :
    PartyM C E RealSpec TreeOutput :=
  treeStagesBatchProgram K d.ctx₁ d.mode d.jobs d.idx d.count d.value₁ d.st₁ d.k₁

def TreeStagesBatchData.ideal {base : HashCache C} (d : TreeStagesBatchData C E base) :
    PartyM C E RealSpec TreeOutput :=
  treeStagesBatchProgram K d.ctx₂ d.mode d.jobs d.idx d.count d.value₂ d.st₂ d.k₂

def TreeStagesBatchData.rel {base : HashCache C} (d : TreeStagesBatchData C E base)
    (δ : HiddenAddress C → Bit) (x y : Step C E RealSpec TreeOutput) : Prop :=
  let inputs₁ := d.jobs.map (treeStagesCachedInputs base d.ctx₁)
  let inputs₂ := d.jobs.map (treeStagesCachedInputs base d.ctx₂)
  TreeStagesReshareEntryRel K d.mode δ d.ctx₁ d.ctx₂ d.idx d.count (d.value₁ inputs₁) (d.value₂ inputs₂)
    d.st₁ d.st₂ (d.k₁ inputs₁) (d.k₂ inputs₂) x y

theorem TreeStagesBatchData.entry {base : HashCache C} (d : TreeStagesBatchData C E base)
    (D : C.Coalition) (δ : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (d.real K).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance (d.ideal K).run))).run b)
      (fun u z => d.rel K δ u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) :=
  treeStages_batch_entry prims K D δ visible d.ctx₁ d.ctx₂ d.self d.keys d.mode d.jobs d.idx d.count
    base d.covered₁ d.covered₂ d.value₁ d.value₂ d.st₁ d.st₂ d.label d.k₁ d.k₂ a b related grows

/-- Rerand is a peer reshare even when all AND layers use collectors. -/
def treeStagesHeadMode (mode : ReshareMode) (circs : List Circuit) : ReshareMode :=
  match List.range (depth circs) with
  | [] => .peer
  | _ :: _ => mode

/-- Factor the real first exchange in either mode, preserving all remaining
layers, checks, simulator overrides and caller state. -/
theorem treeStages_runJobs_head (ctx : Context C) (mode : ReshareMode) (gadgets : RunGadgets C E RealSpec)
    (circs : List Circuit) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (mult : ∀ x y count, gadgets.mult x y count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshareWith K ctx mode rnd (mulRep K ctx x y) count))
    (rerand : ∀ v count, gadgets.rerand v count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count)) :
    ∃ (value : List (C.Term → List Bit) → ℕ → Bit)
      (k : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput),
      ∀ inputs, ((runJobs K gadgets circs inputs).run st >>= finish) =
        treeStagesReshareProgram K ctx (treeStagesHeadMode mode circs) 0 (treeStagesPeerHeadCount circs) (value inputs) st (k inputs) := by
  generalize layers : List.range (depth circs) = ls
  cases ls with
  | nil =>
    simp only [treeStagesPeerHeadCount, treeStagesHeadMode, layers]
    refine ⟨(fun inputs => ownerSum K ctx (outputShares K circs inputs)),
      (fun inputs z => ((do
        gadgets.verify [⟨outputShares K circs inputs, one K, z.1, (outputsOf circs).length, .peer⟩]
        let opened ← gadgets.output z.1 (outputsOf circs).length
        pure (assemble circs opened)).run z.2 >>= finish)), ?_⟩
    intro inputs
    simp only [treeStagesReshareProgram, reshareWith, runJobs_eq, layers, List.foldlM_nil, pure_bind, tailBody, rerand,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, List.nil_append]
  | cons layer ls =>
    simp only [treeStagesPeerHeadCount, treeStagesHeadMode, layers]
    refine ⟨
      (fun inputs => mulRep K ctx (layerX K circs layer inputs) (layerY K circs layer inputs)),
      (fun inputs z => ((ls.foldlM (layerBody K gadgets circs)
        (appendLayer circs layer inputs z.1,
          [⟨layerX K circs layer inputs, layerY K circs layer inputs, z.1,
            (gatesAt circs layer).length, gadgets.mode⟩]) >>= tailBody K gadgets circs).run z.2 >>= finish)), ?_⟩
    intro inputs
    simp only [treeStagesReshareProgram, reshareWith, runJobs_eq, layers, List.foldlM_cons, layerBody, mult,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, List.nil_append]

/-- Actual batch data for both modes. The public circuit schedule determines
the same first-exchange mode and count in the two executions. -/
theorem treeStages_actualBatchData (D : C.Coalition) (base : HashCache C)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (covered₁ : TreeStagesPrfCovered base ctx₁.keys.seed jobs)
    (covered₂ : TreeStagesPrfCovered base ctx₂.keys.seed jobs)
    (st₁ st₂ : RunState C) (label : st₁.label = st₂.label)
    (finish₁ finish₂ : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    ∃ d : TreeStagesBatchData C E base,
      d.ctx₁ = ctx₁ ∧ d.ctx₂ = ctx₂ ∧ d.st₁ = st₁ ∧ d.st₂ = st₂ ∧ d.jobs = jobs ∧
      d.idx = 0 ∧ d.count = treeStagesPeerHeadCount (jobs.map (circuits parameter ·.kind)) ∧
      d.mode = treeStagesHeadMode settings.mode (jobs.map (circuits parameter ·.kind)) ∧
      d.real K = (jobs.mapM (inputShares ctx₁) >>= fun inputs =>
        (runJobs K (realRunGadgets K ctx₁ settings.mode)
          (jobs.map (circuits parameter ·.kind)) inputs).run st₁ >>= finish₁) ∧
      d.ideal K = (jobs.mapM (inputShares ctx₂) >>= fun inputs =>
        (runJobs K (treeSimGadgets K circuits settings D parameter ctx₂.keys.seed openings ctx₂ batch jobs)
          (jobs.map (circuits parameter ·.kind)) inputs).run st₂ >>= finish₂) := by
  obtain ⟨value₁, k₁, head₁⟩ := treeStages_runJobs_head K ctx₁ settings.mode
    (realRunGadgets K ctx₁ settings.mode) (jobs.map (circuits parameter ·.kind)) st₁ finish₁
    (by intro x y n; rfl) (by intro v n; rfl)
  obtain ⟨value₂, k₂, head₂⟩ := treeStages_runJobs_head K ctx₂ settings.mode
    (treeSimGadgets K circuits settings D parameter ctx₂.keys.seed openings ctx₂ batch jobs)
    (jobs.map (circuits parameter ·.kind)) st₂ finish₂
    (by intro x y n; rfl) (by intro v n; rfl)
  refine ⟨⟨⟨ctx₁, ctx₂, self, keys, jobs, 0, treeStagesPeerHeadCount (jobs.map (circuits parameter ·.kind)),
    covered₁, covered₂, value₁, value₂, st₁, st₂, label, k₁, k₂⟩,
    treeStagesHeadMode settings.mode (jobs.map (circuits parameter ·.kind))⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold TreeStagesBatchData.real treeStagesBatchProgram
    apply bind_congr
    intro inputs
    exact (head₁ inputs).symm
  · unfold TreeStagesBatchData.ideal treeStagesBatchProgram
    apply bind_congr
    intro inputs
    exact (head₂ inputs).symm

/-- Adaptive public computation followed by actual next-batch input and
PRSS queries, in either reshare mode. -/
theorem treeStages_publicBatch_entry {α : Type} (D : C.Coalition)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : OracleComp HashSpec α) (next : α → TreeStagesBatchData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        ((oracleStep (tweakable pubCode) >>= fun x => (next x).real K).run)))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        ((oracleStep (tweakable pubCode) >>= fun x => (next x).ideal K).run)))).run b)
      (fun u z => (∃ x, (next x).rel K δ u.1 z.1) ∧ TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_onHash_coupling prims D _ _
    (treeStages_tweakable_onHash prims D pubCode) δ a b related))
  intro u z hu
  rw [← hu.1.1]
  apply relTriple_post_mono ((next u.1).entry prims K D δ visible u.2 z.2 hu.1.2.1
    (grows.trans (treeSim_logged_grows prims D _ a u hu.2.1)))
  intro x y hxy
  exact ⟨⟨u.1, hxy.1⟩, hxy.2⟩

/-- Extend the nonterminal opening closure through the actual adaptive
public leanXMSS code between batches, as well as input and PRSS queries. -/
def treeStages_openPublicBatch_localClosure {α : Type} (D : C.Coalition)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : C.Party → (ℕ → Bit) → OracleComp HashSpec α)
    (next : C.Party → (ℕ → Bit) → α → TreeStagesBatchData C E base) :
    TreeSimOpenLocalClosure prims K D live count v ds sent
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K)
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K) where
  J := fun a b => TreeSimStreamRel δ a b ∧ base ≤ a.1.1
  Q := fun i x y => (x = .done none ∧ y = .done none) ∨ ∃ out result, (next i out result).rel K δ x y
  cache := fun _ _ h => h.1.1
  head := by
    intro i a b out u z h hsu _ _ _ hc hf₁ hf₂
    refine ⟨⟨hc, ?_⟩, h.2.trans (treeSim_logged_grows prims D _ a u hsu)⟩
    simpa only [hf₁, hf₂] using h.1.2
  abort := fun _ => Or.inl ⟨rfl, rfl⟩
  continues := by
    intro i a b out u z _ _ _ _ _ hj
    apply relTriple_post_mono (treeStages_publicBatch_entry prims K D base δ visible
      (pubCode i out) (next i out) u.2 z.2 hj.1 hj.2)
    intro x y hxy
    exact ⟨Or.inr ⟨out, hxy.1⟩, hxy.2⟩

/-- Full nonterminal OpenRep preservation through public computation and
next-batch entry, with no assumed coupling of any of those computations. -/
theorem treeStages_openPublicBatch_round {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : C.Party → (ℕ → Bit) → OracleComp HashSpec α)
    (next : C.Party → (ℕ → Bit) → α → TreeStagesBatchData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out =>
          oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimOpenPartial K D live count v ds (fun i out =>
          oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∀ i, (u.1.2.1 i = .done none ∧ z.1.2.1 i = .done none) ∨
          ∃ out result, (next i out result).rel K δ (u.1.2.1 i) (z.1.2.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [stepRound_real, stepRound_real]
  have view := treeSim_open_view K D live count v ds
    (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K)
    (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K)
  unfold treeSimRoundView at view
  rw [view]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D δ _ a b related))
  intro u z hu
  rw [← hu.1.1]
  let close := treeStages_openPublicBatch_localClosure prims K D live count v ds u.1.2 base δ visible pubCode next
  apply relTriple_bind (close.all prims K D live count v ds u.1.2 _ _ u.2 z.2
    ⟨hu.1.2.1, grows.trans (treeSim_logged_grows prims D _ a u hu.2.1)⟩)
  intro p q hp
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, hp⟩

/-- The complete nonterminal check/opening transition through public code
and next-batch entry, for both peer and collector settings. -/
theorem treeStages_simBatch_next_rounds {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job) (widths : List ℕ)
    (clear : List (List Bit)) (v : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (base : HashCache C) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (pubCode : C.Party → List (List Bit) → OracleComp HashSpec α)
    (next : C.Party → List (List Bit) → α → TreeStagesBatchData C E base)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1)
    (covered : TreeStagesCopyCovered widths.sum a.1.1)
    (prfCovered : TreeStagesPrfCovered b.1 seeds jobs)
    (clearEq : jobs.map (treeStagesCachedJob circuits b.1 parameter seeds) = clear) :
    let k₁ := fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K
    let k₂ := fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K
    RelTriple
      ((do
        let p ← stepRound (treeSimRealRoles prims D) D A noFunctionality state
          (treeSimCheckWaiting K D live kind (fun i => openRep K (ctx₁ i) (v i) widths.sum >>= fun out =>
            k₁ i (treeStagesBatchDecode widths out)))
        stepRound (treeSimRealRoles prims D) D A noFunctionality p.1 p.2.1).run a)
      ((do
        let p ← stepRound (treeSimIdealRoles prims D) D A noFunctionality state
          (treeSimCheckWaiting K D live kind (fun i => treeStagesSimBatchResume K circuits settings D
            parameter seeds openings (ctx₂ i) batch jobs widths
            (treeSimHeldShift D i widths.sum (treeStagesCorrection openings batch clear) (v i)) (st i) (k₂ i)))
        stepRound (treeSimIdealRoles prims D) D A noFunctionality p.1 p.2.1).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∀ i, (u.1.2.1 i = .done none ∧ z.1.2.1 i = .done none) ∨
          ∃ out result, (next i (treeStagesBatchDecode widths out) result).rel K δ (u.1.2.1 i) (z.1.2.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  simp only [StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeStages_simBatch_resume_check_round prims K circuits settings D A state live kind
      ctx₁ ctx₂ self₁ self₂ parameter seeds openings batch jobs widths clear v st
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).real K)
      (fun i out => oracleStep (tweakable (pubCode i out)) >>= fun x => (next i out x).ideal K)
      δ a b related covered prfCovered clearEq))
  intro u z hu
  obtain ⟨sent, ds, same, _, _, steps₁, steps₂, hc, _⟩ := hu.1
  have support := hu.2.1
  simp only [← simulateQ_stepRound, treeSimRealRoles] at support
  have grows' := grows.trans (treeSim_logged_grows prims D _ a u support)
  rw [steps₁, steps₂, ← same]
  exact treeStages_openPublicBatch_round prims K D A u.1.1 _ widths.sum v ds base δ visible
    (fun i out => pubCode i (treeStagesBatchDecode widths out))
    (fun i out => next i (treeStagesBatchDecode widths out)) u.2 z.2 hc grows'

/-- The shared dealer/start prefix factors every bounded real execution,
not just the final distinguisher call. -/
theorem treeStages_ghost_phase_prefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux) (fuel : ℕ) :
    treeSimGhostRun prims D
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
      (realExecution D A noFunctionality fuel
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
        (dealtKeys parameter seeds pairs) z) =
      (do
        let p ← treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z
        (fun r => (p.1, r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
          (executePhase worldRoles D A noFunctionality fuel p.2.1
            (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree))).run p.2.2) := by
  unfold treeSimCommonPrefix treeSimGhostRun
  simp only [StateT.run'_eq, StateT.run_bind, onHash, StateT.run_mk, bind_map_left,
    StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind, Functor.map_map]
  apply bind_congr
  intro d
  have h := congrArg (fun p => (fun r => (d.1, r.1, r.2.2)) <$> p)
    (treeSimLoggedWorld_run prims D
      (realExecution D A noFunctionality fuel
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
        (dealtKeys parameter seeds pairs) z) (d.2, ∅) [])
  simpa only [realExecution, simulateQ_bind, StateT.run_bind, bind_assoc, map_bind,
    Functor.map_map, List.nil_append, bind_pure_comp] using h.symm

/-- Ghost padding preserves the exact output and query log of any bounded
real phase. Its queries do not enter the ceremony transcript. -/
theorem treeStages_phase_padding (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec TreeOutput)
    (padding : OracleComp (LocalSpec C) Unit) (s : TreeSimState C) :
    𝒟[do
      let r ← (simulateQ (localAnswer prims) padding).run s.1.1
      (fun u : (A.State × (C.Party → Option TreeOutput)) × TreeSimState C => (u.1, u.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state program)).run ((r.2, s.1.2), s.2)] =
    𝒟[(fun u : (A.State × (C.Party → Option TreeOutput)) × TreeSimState C => (u.1, u.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run s] := by
  have h := treeSim_logged_padding prims D padding
    (treeSimLocalFinish D A fuel state program (fun out => pure out)) s
  simpa only [treeSimLocalFinish_eq, worldRoles, liftComp_pure, counted_pure, bind_pure] using h

/-- Every supported padded bounded phase yields a replay certificate for
that very output and log. This discharges the witness part of core output
evidence once the invariant retains bounded real-prefix reachability. -/
theorem treeStages_outputWitness_padded (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (fuel : ℕ) (bound : fuel ≤ ceremonyFuel circuits settings)
    (u : (A.State × (C.Party → Option TreeOutput)) × TreeSimState C)
    (hu : u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel p.2.1
        (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree))).run
          ((r.2, p.2.2.1.2), p.2.2.2))) :
    TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z p.1 u.1 u.2.2 := by
  have padded : (u.1, u.2.2) ∈ support (do
      let r ← (simulateQ (localAnswer prims) padding).run p.2.2.1.1
      (fun v : (A.State × (C.Party → Option TreeOutput)) × TreeSimState C => (v.1, v.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel p.2.1
          (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree))).run
            ((r.2, p.2.2.1.2), p.2.2.2)) := by
    simp only [support_bind, Set.mem_iUnion, support_map]
    exact ⟨r, hr, u, hu, rfl⟩
  have unpadded := (mem_support_evalDist_iff _ _).2 padded
  rw [treeStages_phase_padding prims D A fuel p.2.1 _ padding p.2.2] at unpadded
  have replay := (mem_support_evalDist_iff _ _).1 unpadded
  refine ⟨fuel, u.2.2, bound, List.prefix_refl _, ?_⟩
  rw [treeStages_ghost_phase_prefix prims K circuits settings top tree D A parameter seeds pairs z fuel]
  simp only [support_bind, Set.mem_iUnion, support_map] at replay ⊢
  obtain ⟨v, hv, he⟩ := replay
  exact ⟨p, hp, v, hv, by rw [← he]⟩

/-- The actual real run after the common three-round setup, retaining every
pending program instead of projecting it to an optional output. -/
def treeStagesTrace (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (fuel : ℕ) : StateT (TreeSimState C) ProbComp
      (A.State × (C.Party → Step C E RealSpec TreeOutput)) := do
  let p ← executePhase (treeSimRealRoles prims D) D A noFunctionality 3 state
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
  let next ← simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.2)
  executeSteps (treeSimRealRoles prims D) D A noFunctionality fuel p.1 next

/-- Projecting the retained trace is exactly a bounded ceremony execution;
the three setup rounds are included in the bound. -/
theorem treeStages_trace_output (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (fuel : ℕ) :
    executePhase (treeSimRealRoles prims D) D A noFunctionality (fuel + 3) state
      (fun i => ceremony K circuits settings i (x i) top tree) =
    (fun p => (p.1, fun i => (p.2 i).output)) <$>
      treeStagesTrace prims K circuits settings top tree D A x state fuel := by
  change executePhase (treeSimRealRoles prims D) D A noFunctionality (fuel + 3) state
    (fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree x i) = _
  rw [treeSimRealRoles, treeSim_prssSetup_split]
  simp only [treeStagesTrace, treeSimRealRoles, map_bind]
  apply bind_congr
  intro p
  apply bind_congr
  intro next
  exact executeRounds_eq_executeSteps _ D A noFunctionality fuel p.1 next

/-- Retained prefixes compose before any output is discarded. -/
theorem treeStages_trace_add (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (a b : ℕ) :
    treeStagesTrace prims K circuits settings top tree D A x state (a + b) =
      (do let p ← treeStagesTrace prims K circuits settings top tree D A x state a
          executeSteps (treeSimRealRoles prims D) D A noFunctionality b p.1 p.2) := by
  simp only [treeStagesTrace, executeSteps_add, bind_assoc]

/-- Reachability records the exact padded real configuration and its used
round budget. It contains the honest continuations and the classified log. -/
def TreeStagesReach (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (fuel : ℕ)
    (a : TreeSimConfig A (TreeSimState C)) : Prop :=
  a ∈ support ((treeStagesTrace prims K circuits settings top tree D A x state fuel).run s)

/-- Every actual post-setup continuation enters the retained reachability
predicate, with no extra replay or coupling premise. -/
theorem treeStages_reach_entry (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s))
    (a : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (ha : a ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2)).run p.2)) :
    TreeStagesReach prims K circuits settings top tree D A x state s 0 ((p.1.1, a.1), a.2) := by
  simp only [TreeStagesReach, treeStagesTrace, executeSteps, StateT.run_bind,
    StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  exact ⟨p, hp, a, ha, rfl⟩

/-- A supported real rushing round extends the very same retained trace.
The nonterminal premise matches the runner's stopping test exactly. -/
theorem treeStages_reach_step (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (fuel : ℕ)
    (a : TreeSimConfig A (TreeSimState C))
    (ha : TreeStagesReach prims K circuits settings top tree D A x state s fuel a)
    (active : ¬ AllDone D a.1.2)
    (u : (A.State × (C.Party → Step C E RealSpec TreeOutput) × (C.Party → Mail C E)) × TreeSimState C)
    (hu : u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)) :
    TreeStagesReach prims K circuits settings top tree D A x state s (fuel + 1)
      ((u.1.1, u.1.2.1), u.2) := by
  unfold TreeStagesReach at ha ⊢
  rw [treeStages_trace_add]
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion]
  refine ⟨a, ha, ?_⟩
  simp only [executeSteps, AllDone] at active ⊢
  simp only [if_neg active, StateT.run_bind, StateT.run_pure,
    support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  exact ⟨u, hu, rfl⟩

/-- Bounded retained reachability supplies the core's same-execution witness,
including the actual dealer cache and arbitrary ghost padding. -/
theorem treeStages_reach_outputWitness (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (fuel : ℕ) (bound : fuel + 3 ≤ ceremonyFuel circuits settings)
    (a : TreeSimConfig A (TreeSimState C))
    (ha : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) fuel a) :
    TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z p.1
      (a.1.1, fun i => (a.1.2 i).output) a.2.2 := by
  apply treeStages_outputWitness_padded prims K circuits settings top tree D A parameter seeds pairs z
    p hp padding r hr (fuel + 3) bound ((a.1.1, fun i => (a.1.2 i).output), a.2)
  rw [simulateQ_executePhase]
  change _ ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality _ _ _).run _)
  rw [treeStages_trace_output]
  simp only [StateT.run_map, support_map]
  exact ⟨a, ha, rfl⟩

private theorem treeStages_sequenceFin_values {α σ : Type} {n : ℕ}
    (f : Fin n → StateT σ ProbComp α) (P : Fin n → α → Prop)
    (hf : ∀ i s r, r ∈ support ((f i).run s) → P i r.1)
    (s : σ) (r : (Fin n → α) × σ)
    (hr : r ∈ support ((Concrete.sequenceFin f).run s)) : ∀ i, P i (r.1 i) := by
  induction n generalizing s with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    intro i
    cases i using Fin.cases with
    | zero => exact hf 0 s u hu
    | succ i =>
      exact ih (fun i => f i.succ) (fun i => P i.succ)
        (fun i => hf i.succ) u.2 v hv i

/-- Corrupt slots remain empty in the actual driver, independently of the
adversary's outgoing messages and of the honest local computations. -/
theorem treeStages_round_corrupt {α σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (empty : ∀ i, i ∈ D.1 → steps i = .done none)
    (s : σ) (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × σ)
    (hr : r ∈ support ((stepRound (simRoles impl worldRoles) D A noFunctionality state steps).run s)) :
    ∀ i, i ∈ D.1 → r.1.2.1 i = .done none := by
  rw [← simulateQ_stepRound, stepRound_real] at hr
  simp only [simulateQ_bind, simulateQ_pure, free_sequenceFin, simulateQ_sequenceFin,
    StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, v, hv, rfl⟩ := hr
  apply treeStages_sequenceFin_values _ (fun i step => i ∈ D.1 → step = .done none) _ u.2 v hv
  intro i t out hout hi
  simp only [roundLocal, empty i hi, free_pure, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hout
  exact congrArg Prod.fst hout

/-- The retained runner never manufactures a corrupt output. -/
theorem treeStages_steps_corrupt {α σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (empty : ∀ i, i ∈ D.1 → steps i = .done none)
    (s : σ) (r : (A.State × (C.Party → Step C E RealSpec α)) × σ)
    (hr : r ∈ support ((executeSteps (simRoles impl worldRoles) D A noFunctionality fuel state steps).run s)) :
    ∀ i, i ∈ D.1 → r.1.2 i = .done none := by
  induction fuel generalizing state steps s with
  | zero =>
    simp only [executeSteps, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact empty
  | succ fuel ih =>
    simp only [executeSteps] at hr
    split_ifs at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact empty
    · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hr
      obtain ⟨u, hu, hr⟩ := hr
      exact ih u.1.1 u.1.2.1 (treeStages_round_corrupt impl D A state steps empty s u hu) u.2 hr

/-- The output projection of every real phase has empty corrupt slots,
including prefixes that stop because they exhausted their fuel. -/
theorem treeStages_phase_corrupt {α σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) (s : σ)
    (r : (A.State × (C.Party → Option α)) × σ)
    (hr : r ∈ support ((executePhase (simRoles impl worldRoles) D A noFunctionality fuel state program).run s)) :
    ∀ i, i ∈ D.1 → r.1.2 i = none := by
  simp only [executePhase, executeRounds_eq_executeSteps, StateT.run_bind,
    StateT.run_map, support_bind, Set.mem_iUnion, support_map] at hr
  obtain ⟨u, hu, v, hv, rfl⟩ := hr
  have empty : ∀ i, i ∈ D.1 → u.1 i = .done none := by
    apply treeStages_sequenceFin_values _ (fun i step => i ∈ D.1 → step = .done none) _ s u hu
    intro i t out hout hi
    simp only [if_pos hi, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
    exact congrArg Prod.fst hout
  intro i hi
  have h := treeStages_steps_corrupt impl D A fuel state u.1 empty u.2 v hv i hi
  simp only [h, Step.output]

/-- Reachable configurations automatically satisfy the corrupt-output field
of the core. No gadget invariant has to assume this separately. -/
theorem treeStages_reach_corrupt (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (fuel : ℕ)
    (a : TreeSimConfig A (TreeSimState C))
    (ha : TreeStagesReach prims K circuits settings top tree D A x state s fuel a) :
    ∀ i, i ∈ D.1 → (a.1.2 i).output = none := by
  apply treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A (fuel + 3) state
    (fun i => ceremony K circuits settings i (x i) top tree) s
    ((a.1.1, fun i => (a.1.2 i).output), a.2)
  change _ ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality _ _ _).run _)
  rw [treeStages_trace_output]
  simp only [StateT.run_map, support_map]
  exact ⟨a, ha, rfl⟩

/-- Construct the frozen core from a round-indexed gadget relation. Actual
reachability, the replay certificate and empty corrupt outputs are supplied by
the driver lemmas above. The progress premise rules out a nonterminal state
at the ceremony's round limit; it is not an extra round of allowed fuel. -/
def treeStages_core_of_reachable_relation (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (padding : OracleComp (LocalSpec C) Unit) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1))
    (R : ℕ → TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (entry : ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
      RelTriple
        ((simulateQ (treeSimLoggedWorld prims D)
          (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
        ((simulateQ (streamWorld prims D)
          (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
            (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
        (fun a b => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
          R 0 ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2)))
    (agree : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      a.1.1 = b.1.1 ∧ a.2.1.1 = b.2.1 ∧
      (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
      (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome))
    (progress : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 → n + 1 + 3 ≤ ceremonyFuel circuits settings)
    (next : ∀ n a b, R n a b →
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 →
      RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
        (fun u v => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2 ∨
          R (n + 1) ((u.1.1, u.1.2.1), u.2) ((v.1.1, v.1.2.1), v.2))) :
    TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z p.1 p.2.1
      ((r.2, p.2.2.1.2), p.2.2.2)
      (fun t => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2) where
  Inv a b := ∃ n, n + 3 ≤ ceremonyFuel circuits settings ∧
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a ∧ R n a b
  stage _ := .ceremony
  entry u hu := by
    apply relTriple_post_mono (treeSim_relTriple_support (entry u hu))
    intro a b hab
    rcases hab.1 with bad | rel
    · exact Or.inl bad
    · refine Or.inr ⟨0, ?_, ?_, rel⟩
      · unfold ceremonyFuel setupRounds
        omega
      · exact treeStages_reach_entry prims K circuits settings top tree D A _ _ _ u hu a hab.2.1
  noSetup _ _ _ _ := by intro h; cases h
  done a b hab good := by
    obtain ⟨n, _, reach, rel⟩ := hab
    exact (agree n a b rel reach good).2.2.1
  outputEvidence a b hab good := by
    obtain ⟨n, bound, reach, rel⟩ := hab
    obtain ⟨state, cache, _, success⟩ := agree n a b rel reach good
    exact ⟨treeStages_reach_outputWitness prims K circuits settings top tree D A parameter seeds pairs z
      p hp padding r hr n bound a reach, state, cache,
      treeStages_reach_corrupt prims K circuits settings top tree D A _ _ _ n a reach, success⟩
  peerBoundary _ _ h := by cases h
  collectorBoundary _ _ h := by cases h
  collectorNextBoundary _ _ h := by cases h
  rerandBoundary _ _ h := by cases h
  coinBoundary _ _ h := by cases h
  extendMultBoundary _ _ h := by cases h
  checkBoundary _ _ h := by cases h
  openingBoundary _ _ h := by cases h
  emptyOpeningBoundary _ _ h := by cases h
  ceremony a b _ hab good active := by
    obtain ⟨n, bound, reach, rel⟩ := hab
    apply relTriple_post_mono (treeSim_relTriple_support (next n a b rel reach bound good active))
    intro u v huv
    rcases huv.1 with bad | rel'
    · exact Or.inl bad
    · exact Or.inr ⟨n + 1, progress n a b rel reach bound good active,
        treeStages_reach_step prims K circuits settings top tree D A _ _ _ n a reach active u huv.2.1, rel'⟩

/-- Start all actual next-batch programs in driver order. This includes the
input PRF queries before either kind of reshare and shares one public cache. -/
theorem treeStages_batch_start (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) (grows : base ≤ a.1.1) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => (d i).real K))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => (d i).ideal K))).run b)
      (fun u z => (∀ i, if i ∈ D.1 then u.1 i = .done none ∧ z.1 i = .done none
          else (d i).rel K δ (u.1 i) (z.1 i)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  simp only [startSteps, simulateQ_sequenceFin]
  apply treeStages_sequenceFin_rel _ _ (fun a b => TreeSimStreamRel δ a b ∧ base ≤ a.1.1)
    (fun i u z => if i ∈ D.1 then u = .done none ∧ z = .done none else (d i).rel K δ u z) _ a b ⟨related, grows⟩
  intro i a b h
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, h⟩
  · simp only [if_neg hi, worldRoles]
    exact (d i).entry prims K D δ visible a b h.1 h.2

def TreeStagesBatchData.input₁ {base : HashCache C} (d : TreeStagesBatchData C E base) :=
  d.jobs.map (treeStagesCachedInputs base d.ctx₁)

def TreeStagesBatchData.input₂ {base : HashCache C} (d : TreeStagesBatchData C E base) :=
  d.jobs.map (treeStagesCachedInputs base d.ctx₂)

/-- Actual batch inputs and collector PRSS establish the adapted GS20 mask
relation for the whole vector. The shift is chosen once before any party draws;
input replay ensures it uses the values of those actual input queries. -/
theorem treeStages_batch_collector_start (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (T₀ : C.Term) (ρ idx count : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .collector)
    (index : ∀ i, i ∉ D.1 → (d i).idx = idx)
    (size : ∀ i, i ∉ D.1 → (d i).count = count)
    (self₁ : ∀ i, i ∉ D.1 → (d i).ctx₁.self = i)
    (self₂ : ∀ i, i ∉ D.1 → (d i).ctx₂.self = i)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count
      ((fun i => (d i).value₁ (d i).input₁) - (fun i => (d i).value₂ (d i).input₂)) x = 0) :
    let v₁ := fun i => (d i).value₁ (d i).input₁
    let v₂ := fun i => (d i).value₂ (d i).input₂
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => (d i).real K))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => (d i).ideal K))).run b)
      (fun u z => (∃ rnd₁ rnd₂ : C.Party → PrssOutput C Bit,
        (∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
          (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) ∧
        u.1 = treeSimCollectorWaiting K D count rnd₁ v₁ (fun i => (d i).st₁) (fun i => (d i).k₁ (d i).input₁) ∧
        z.1 = treeSimCollectorWaiting K D count rnd₂ v₂ (fun i => (d i).st₂) (fun i => (d i).k₂ (d i).input₂)) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  intro v₁ v₂ δ
  have visible' : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  apply relTriple_post_mono (treeStages_batch_start prims K D base d δ visible' a b
    ⟨related.1, treeSim_hiddenRel_extend past _ related.2 fresh⟩ grows)
  intro u z h
  have witnesses : ∀ i, ∃ r₁ r₂ : PrssOutput C Bit,
      (i ∉ D.1 → r₂ = r₁ + frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
        (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) ∧
      u.1 i = (if i ∈ D.1 then .done none else treeSimCollectorStep K (localContext i) r₁
        (v₁ i) count (d i).st₁ ((d i).k₁ (d i).input₁)) ∧
      z.1 i = (if i ∈ D.1 then .done none else treeSimCollectorStep K (localContext i) r₂
        (v₂ i) count (d i).st₂ ((d i).k₂ (d i).input₂)) := by
    intro i
    have hiRel := h.1 i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi] at hiRel ⊢
      exact ⟨0, 0, fun hn => (hn hi).elim, hiRel⟩
    · simp only [if_neg hi, TreeStagesBatchData.rel, mode i hi, TreeStagesReshareEntryRel] at hiRel
      obtain ⟨r₁, r₂, hm₁, hm₂, hu, hz⟩ := hiRel
      have shift : treeSimPrssShift δ (d i).ctx₁ (d i).st₁.label (d i).idx (d i).count =
          frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
            (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i := by
        rw [label i hi, index i hi, size i hi]
        dsimp only [δ]
        rw [treeSim_prssShift_add, treeSim_prssShift_zero past (d i).ctx₁ ρ idx count block, zero_add]
        unfold treeSimCollectorShift
        rw [treeSim_prssShift_block D (d i).ctx₁ (by simpa [self₁ i hi] using hi), self₁ i hi]
      rw [shift] at hm₁ hm₂
      refine ⟨r₁, r₂, fun _ => Prod.ext hm₁ hm₂, ?_, ?_⟩
      · simpa only [if_neg hi, treeSimCollectorStep, localContext, self₁ i hi, size i hi, v₁, TreeStagesBatchData.input₁] using hu
      · simpa only [if_neg hi, treeSimCollectorStep, localContext, self₂ i hi, size i hi, v₂, TreeStagesBatchData.input₂] using hz
  choose rnd₁ rnd₂ masks realStep idealStep using witnesses
  exact ⟨⟨rnd₁, rnd₂, masks, funext realStep, funext idealStep⟩, h.2⟩

/-- The input phase followed by collector PRSS writes only the entry label.
This is a support statement, so it needs no cache coverage or coupling premise. -/
theorem treeStages_batch_collector_entry_frame (D : C.Coalition) (ctx : Context C)
    (jobs : List Job) (idx count : ℕ) (value : List (C.Term → List Bit) → ℕ → Bit)
    (st : RunState C)
    (k : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (s : HashCache C × HiddenCache C)
    (r : Step C E RealSpec TreeOutput × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((treeStagesBatchProgram K ctx .collector jobs idx count value st k).run)))).run s)) :
    TreeSimCacheFrame st.label s.2 r.2.2 := by
  unfold treeStagesBatchProgram at hr
  simp only [inputShares_fun, mapM_oracleStep, worldRoles, advance_oracleStep_bind,
    free_bind, simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hr
  obtain ⟨u, hu, hr⟩ := hr
  rw [treeStages_inputQueries_onHash] at hu
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact treeSim_collector_entry_frame prims K D ctx idx count (value v.1) st (k v.1) (v.2, s.2) r hr

/-- Starting all collector batch programs preserves every other hidden label,
including when earlier parties have extended the shared public cache. -/
theorem treeStages_batch_collector_start_frame (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (ρ : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .collector)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (s : HashCache C × HiddenCache C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (startSteps worldRoles D (fun i => (d i).real K))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  simp only [startSteps, simulateQ_sequenceFin] at hr
  intro x hx
  apply treeStages_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 x) _ _ s r hr
  intro i a b hb
  by_cases hi : i ∈ D.1
  · simp [hi] at hb
    subst b
    rfl
  · simp only [if_neg hi, TreeStagesBatchData.real, mode i hi] at hb
    have frame := treeStages_batch_collector_entry_frame prims K D (d i).ctx₁ (d i).jobs
      (d i).idx (d i).count (d i).value₁ (d i).st₁ (d i).k₁ a b hb
    rw [label i hi] at frame
    exact frame x hx

/-- Erasing only the log transfers the exact collector batch footprint. -/
theorem treeStages_batch_collector_start_logged_frame (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (ρ : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .collector)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => (d i).real K))).run s)) :
    TreeSimCacheFrame ρ s.1.2 r.2.1.2 := by
  apply treeStages_batch_collector_start_frame prims K D base d ρ mode label s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- The real batch input phase now enters the frozen collector boundary,
with its history relation and actual saved `runJobs` continuations. -/
theorem treeStages_batch_collector_boundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀)
    (ρ idx count : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .collector)
    (index : ∀ i, i ∉ D.1 → (d i).idx = idx)
    (size : ∀ i, i ∉ D.1 → (d i).count = count)
    (self₁ : ∀ i, i ∉ D.1 → (d i).ctx₁.self = i)
    (self₂ : ∀ i, i ∉ D.1 → (d i).ctx₂.self = i)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (history : List Bit)
    (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (d i).st₁ (d i).st₂)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count
      ((fun i => (d i).value₁ (d i).input₁) - (fun i => (d i).value₂ (d i).input₂)) x = 0) :
    let v₁ := fun i => (d i).value₁ (d i).input₁
    let v₂ := fun i => (d i).value₂ (d i).input₂
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => (d i).real K))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => (d i).ideal K))).run b)
      (fun u z => ∃ rnd₁ rnd₂, ∃ masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i +
        frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
          (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i,
        TreeSimCollectorBoundary K D A
          ⟨count, T₀, lacked, δ, rnd₁, rnd₂, v₁, v₂,
            (fun i => (d i).st₁), (fun i => (d i).st₂),
            (fun i => (d i).k₁ (d i).input₁), (fun i => (d i).k₂ (d i).input₂), history, masks, states⟩
          ((state, u.1), u.2) ((state, z.1), z.2) ∧ base ≤ u.2.1.1) := by
  dsimp only
  apply relTriple_post_mono (treeStages_batch_collector_start prims K D base d T₀ ρ idx count
    mode index size self₁ self₂ label past visible block a b related grows fresh)
  intro u z h
  obtain ⟨⟨rnd₁, rnd₂, masks, realSteps, idealSteps⟩, caches, grows'⟩ := h
  exact ⟨rnd₁, rnd₂, masks, ⟨rfl, caches, Or.inl ⟨realSteps, idealSteps⟩⟩, grows'⟩

/-- The whole next-batch input/PRSS phase and its first actual collector
round couple with the real rushing adversary. The result is the forwarding
boundary, retaining the same masks and the complete saved continuations. -/
theorem treeStages_batch_collector_first_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀)
    (ρ idx count : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .collector)
    (index : ∀ i, i ∉ D.1 → (d i).idx = idx)
    (size : ∀ i, i ∉ D.1 → (d i).count = count)
    (self₁ : ∀ i, i ∉ D.1 → (d i).ctx₁.self = i)
    (self₂ : ∀ i, i ∉ D.1 → (d i).ctx₂.self = i)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (history : List Bit)
    (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (d i).st₁ (d i).st₂)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count
      ((fun i => (d i).value₁ (d i).input₁) - (fun i => (d i).value₂ (d i).input₂)) x = 0) :
    let v₁ := fun i => (d i).value₁ (d i).input₁
    let v₂ := fun i => (d i).value₂ (d i).input₂
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => (d i).real K))
        stepRound (treeSimRealRoles prims D) D A noFunctionality state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => (d i).ideal K))
        stepRound (treeSimIdealRoles prims D) D A noFunctionality state steps).run b)
      (fun u z => u.1.2.2 = z.1.2.2 ∧ ∃ rnd₁ rnd₂, ∃ masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i +
        frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
          (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i,
        TreeSimCollectorBoundary K D A
          ⟨count, T₀, lacked, δ, rnd₁, rnd₂, v₁, v₂,
            (fun i => (d i).st₁), (fun i => (d i).st₂),
            (fun i => (d i).k₁ (d i).input₁), (fun i => (d i).k₂ (d i).input₂), history, masks, states⟩
          ((u.1.1, u.1.2.1), u.2) ((z.1.1, z.1.2.1), z.2) ∧ base ≤ u.2.1.1) := by
  intro v₁ v₂ δ
  simp only [StateT.run_bind]
  apply relTriple_bind (treeStages_batch_collector_start prims K D base d T₀ ρ idx count
    mode index size self₁ self₂ label past visible block a b related grows fresh)
  intro u z h
  obtain ⟨⟨rnd₁, rnd₂, masks, realSteps, idealSteps⟩, caches, grows'⟩ := h
  rw [realSteps, idealSteps]
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  have view := (treeSim_collector_transcript_exit K D count T₀ lacked rnd₁ rnd₂ v₁ v₂ masks
    history (fun i => (d i).st₁) (fun i => (d i).st₂) states).1
  apply relTriple_post_mono (treeSim_relTriple_support (treeSim_collector_first_mixed prims K D A state δ count
    rnd₁ rnd₂ v₁ v₂ (fun i => (d i).st₁) (fun i => (d i).st₂)
    (fun i => (d i).k₁ (d i).input₁) (fun i => (d i).k₂ (d i).input₂) view u.2 z.2 caches))
  intro u' z' h'
  obtain ⟨sameState, sameSent, realNext, idealNext, nextCaches, _, _⟩ := h'.1
  exact ⟨sameSent, rnd₁, rnd₂, masks,
    ⟨sameState, nextCaches, Or.inr (Or.inl ⟨u'.1.2.2, realNext, idealNext⟩)⟩,
    grows'.trans (treeSim_logged_grows prims D _ u.2 u' h'.2.1)⟩

/-- The actual remaining layer fold, including Rerand, the check, opening
and the caller's stateful continuation. -/
def treeStagesLayers (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (layers : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    PartyM C E RealSpec TreeOutput :=
  ((layers.foldlM (layerBody K gadgets circs) p >>= tailBody K gadgets circs).run st) >>= finish

/-- Save the actual wires and multiplication tuple after this layer, then
resume the remaining circuit and ceremony code. -/
def treeStagesAfterLayer (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (layer : ℕ) (rest : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C))
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C Bit × RunState C) : PartyM C E RealSpec TreeOutput :=
  treeStagesLayers K gadgets circs rest
    (appendLayer circs layer p.1 out.1,
      p.2 ++ [⟨layerX K circs layer p.1, layerY K circs layer p.1,
        out.1, (gatesAt circs layer).length, gadgets.mode⟩]) out.2 finish

/-- No probability or continuation hypothesis is needed to identify the next
real multiplication inside the saved layer fold. -/
theorem treeStages_layers_cons (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (layer : ℕ) (rest : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesLayers K gadgets circs (layer :: rest) p st finish =
      (gadgets.mult (layerX K circs layer p.1) (layerY K circs layer p.1)
        (gatesAt circs layer).length).run st >>= treeStagesAfterLayer K gadgets circs layer rest p finish := by
  simp only [treeStagesLayers, treeStagesAfterLayer, List.foldlM_cons, layerBody,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro out
  simp only [treeStagesAfterLayer, treeStagesLayers, StateT.run_bind, bind_assoc]

/-- A concrete collector layer factors with its whole saved continuation. -/
theorem treeStages_layers_collector (ctx : Context C) (gadgets : RunGadgets C E RealSpec)
    (mult : ∀ x y count, gadgets.mult x y count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshareCollector K ctx rnd (mulRep K ctx x y) count))
    (circs : List Circuit) (layer : ℕ) (rest : List ℕ)
    (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesLayers K gadgets circs (layer :: rest) p st finish =
      treeSimCollectorProgram K ctx 0 (gatesAt circs layer).length
        (mulRep K ctx (layerX K circs layer p.1) (layerY K circs layer p.1)) st >>=
      treeStagesAfterLayer K gadgets circs layer rest p finish := by
  rw [treeStages_layers_cons, mult]
  rfl

/-- Totalize an aborted collector output only for its unused certificate
fields. No dummy output is inserted into the actual execution. -/
def treeStagesCollectorValue (count : ℕ) (st : RunState C) (i : C.Party) (z : Shares C Bit) :
    Shares C Bit × RunState C :=
  (z, ⟨recordMode K .collector i st.history z count, st.label + 1, st.tag⟩)

/-- Every actual collector exit has a common live mask and related concrete
values. Even the unused values of aborted parties have well-formed labels and
histories, so they can populate the frozen next-collector certificate. -/
theorem treeStages_collector_exit_values (D : C.Coalition) (count : ℕ) (T₀ : C.Term)
    (lacked : lackedTerm D.1 = some T₀)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i)
    (history : List Bit) (st₁ st₂ : C.Party → RunState C)
    (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (sent sent' : C.Party → Mail C E) :
    let difference := fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g
    let out₁ := fun i => treeSimCollectorRecorded K count st₁ i (colOuts K D count rnd₁ v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K count st₂ i (colOuts K D count rnd₂ v₂ sent sent' i)
    ∃ (live : C.Party → Bool) (x₁ x₂ : C.Party → Shares C Bit × RunState C),
      (∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none) ∧
      (∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none) ∧
      (∀ i, i ∉ D.1 → TreeSimCollectorExitRel K D T₀ count history difference st₁ st₂ i (x₁ i) (x₂ i)) := by
  intro difference out₁ out₂
  have related := (treeSim_collector_transcript_exit K D count T₀ lacked rnd₁ rnd₂ v₁ v₂
    masks history st₁ st₂ states).2.2 sent sent'
  let fallback₁ := fun i => treeStagesCollectorValue K count (st₁ i) i 0
  let fallback₂ := fun i => treeStagesCollectorValue K count (st₂ i) i (treeSimHeldShift D i count difference 0)
  have fallback : ∀ i, i ∉ D.1 → TreeSimCollectorExitRel K D T₀ count history difference st₁ st₂ i
      (fallback₁ i) (fallback₂ i) := by
    intro i hi
    refine ⟨⟨rfl, ?_⟩, rfl, rfl⟩
    refine ⟨congrArg (· + 1) (states i hi).1, (states i hi).2.1, ?_⟩
    exact treeSim_recordMode_shift K D .collector T₀ lacked i count history difference
      (st₁ i).history (st₂ i).history (states i hi).2.2 0 _ rfl
  refine ⟨fun i => (out₁ i).isSome, fun i => (out₁ i).getD (fallback₁ i),
    fun i => (out₂ i).getD (fallback₂ i), ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₁, treeSimCollectorRecorded, colOuts, hi]
    · simp only [if_neg hi]
      cases out₁ i <;> rfl
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₂, treeSimCollectorRecorded, colOuts, hi]
    · simp only [if_neg hi]
      have h : Option.Rel _ (out₁ i) (out₂ i) := related i
      generalize ho₁ : out₁ i = left at h ⊢
      generalize ho₂ : out₂ i = right at h ⊢
      cases h <;> rfl
  · intro i hi
    change TreeSimCollectorExitRel K D T₀ count history difference st₁ st₂ i
      ((out₁ i).getD (fallback₁ i)) ((out₂ i).getD (fallback₂ i))
    have h : Option.Rel _ (out₁ i) (out₂ i) := related i
    generalize ho₁ : out₁ i = left at h ⊢
    generalize ho₂ : out₂ i = right at h ⊢
    cases h with
    | none => exact fallback i hi
    | some h => exact h

/-- The concrete saved program at a collector layer with another AND layer
remaining. These are code equations and state facts, not a coupling premise. -/
structure TreeStagesCollectorLayer (D : C.Coalition) (d : TreeSimCollectorData K D) where
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  gadgets₁ : C.Party → RunGadgets C E RealSpec
  gadgets₂ : C.Party → RunGadgets C E RealSpec
  mult₁ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₁ i).mult x y count = (do
    let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
    reshareCollector K (ctx₁ i) rnd (mulRep K (ctx₁ i) x y) count)
  mult₂ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₂ i).mult x y count = (do
    let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
    reshareCollector K (ctx₂ i) rnd (mulRep K (ctx₂ i) x y) count)
  circs : List Circuit
  layer : ℕ
  nextLayer : ℕ
  rest : List ℕ
  p₁ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  finish₁ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → d.k₁ i =
    treeStagesAfterLayer K (gadgets₁ i) circs layer (nextLayer :: rest) (p₁ i) (finish₁ i)
  program₂ : ∀ i, i ∉ D.1 → d.k₂ i =
    treeStagesAfterLayer K (gadgets₂ i) circs layer (nextLayer :: rest) (p₂ i) (finish₂ i)
  ρ : ℕ
  labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ
  visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0
  zero : TreeSimFutureZero (ρ + 1) d.δ

/-- A successful collector layer resumes the next actual collector layer.
Its certificate is constructed from the real recorded outputs, including
selective abort, rather than assuming a coupling of the continuation. -/
theorem treeStages_collector_next_layer (D : C.Coalition) (d : TreeSimCollectorData K D)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (gadgets₁ gadgets₂ : C.Party → RunGadgets C E RealSpec)
    (mult₁ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₁ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
      reshareCollector K (ctx₁ i) rnd (mulRep K (ctx₁ i) x y) count))
    (mult₂ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₂ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
      reshareCollector K (ctx₂ i) rnd (mulRep K (ctx₂ i) x y) count))
    (circs : List Circuit) (layer nextLayer : ℕ) (rest : List ℕ)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, i ∉ D.1 → d.k₁ i =
      treeStagesAfterLayer K (gadgets₁ i) circs layer (nextLayer :: rest) (p₁ i) (finish₁ i))
    (program₂ : ∀ i, i ∉ D.1 → d.k₂ i =
      treeStagesAfterLayer K (gadgets₂ i) circs layer (nextLayer :: rest) (p₂ i) (finish₂ i))
    (ρ : ℕ) (labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ)
    (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0)
    (zero : TreeSimFutureZero (ρ + 1) d.δ) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (ρ + 1) initial) (sent sent' : C.Party → Mail C E) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeSimCollectorNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt circs nextLayer).length ∧
      ∀ later tail, rest = later :: tail → ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesCollectorLayer K D (n.data K rnd₁ rnd₂ masks),
          successor.ρ = n.ρ ∧ successor.circs = circs ∧ successor.layer = nextLayer ∧
          successor.nextLayer = later ∧ successor.rest = tail := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  let nextP₁ := fun i => (appendLayer circs layer (p₁ i).1 (x₁ i).1,
    (p₁ i).2 ++ [⟨layerX K circs layer (p₁ i).1, layerY K circs layer (p₁ i).1,
      (x₁ i).1, (gatesAt circs layer).length, (gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer circs layer (p₂ i).1 (x₂ i).1,
    (p₂ i).2 ++ [⟨layerX K circs layer (p₂ i).1, layerY K circs layer (p₂ i).1,
      (x₂ i).1, (gatesAt circs layer).length, (gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := d.T₀, lacked := d.lacked, ctx₁ := ctx₁, ctx₂ := ctx₂
    self₁ := self₁, self₂ := self₂, keys := keys
    ρ := ρ + 1, idx := 0, count := (gatesAt circs nextLayer).length
    v₁ := fun i => mulRep K (ctx₁ i) (layerX K circs nextLayer (nextP₁ i).1) (layerY K circs nextLayer (nextP₁ i).1)
    v₂ := fun i => mulRep K (ctx₂ i) (layerX K circs nextLayer (nextP₂ i).1) (layerY K circs nextLayer (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (labels i hi)))
    next₁ := fun i => treeStagesAfterLayer K (gadgets₁ i) circs nextLayer rest (nextP₁ i) (finish₁ i)
    next₂ := fun i => treeStagesAfterLayer K (gadgets₂ i) circs nextLayer rest (nextP₂ i) (finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := visible, futureZero := zero, futureEmpty := fresh
  }, rfl, rfl, rfl, ?_⟩
  · intro i hi _
    rw [program₁ i hi]
    exact treeStages_layers_collector K (ctx₁ i) (gadgets₁ i) (mult₁ i hi)
      circs nextLayer rest (nextP₁ i) (x₁ i).2 (finish₁ i)
  · intro i hi _
    rw [program₂ i hi]
    exact treeStages_layers_collector K (ctx₂ i) (gadgets₂ i) (mult₂ i hi)
      circs nextLayer rest (nextP₂ i) (x₂ i).2 (finish₂ i)

  · intro later tail rest_eq rnd₁ rnd₂ masks zeroNext
    refine ⟨{
      ctx₁ := ctx₁, ctx₂ := ctx₂, self₁ := self₁, self₂ := self₂, keys := keys
      gadgets₁ := gadgets₁, gadgets₂ := gadgets₂, mult₁ := mult₁, mult₂ := mult₂
      circs := circs, layer := nextLayer, nextLayer := later, rest := tail
      p₁ := nextP₁, p₂ := nextP₂, finish₁ := finish₁, finish₂ := finish₂
      program₁ := ?_, program₂ := ?_
      ρ := ρ + 1
      labels := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (labels i hi))
      visible := ?_, zero := zeroNext
    }, rfl, rfl, rfl, rfl, rfl⟩
    · intro i hi
      change treeStagesAfterLayer K (gadgets₁ i) circs nextLayer rest (nextP₁ i) (finish₁ i) = _
      rw [rest_eq]
    · intro i hi
      change treeStagesAfterLayer K (gadgets₂ i) circs nextLayer rest (nextP₂ i) (finish₂ i) = _
      rw [rest_eq]
    · intro x hx
      change (d.δ + treeSimCollectorShift K D d.T₀ (ρ + 1) 0 (gatesAt circs nextLayer).length _) x = 0
      simp only [Pi.add_apply, visible x hx, treeSimCollectorShift,
        treeSim_blockShift_visible D (ρ + 1) 0 (gatesAt circs nextLayer).length _ _ x hx, add_zero]

theorem TreeStagesCollectorLayer.next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (layer : TreeStagesCollectorLayer K D d) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (layer.ρ + 1) initial) (sent sent' : C.Party → Mail C E) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeSimCollectorNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = layer.ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt layer.circs layer.nextLayer).length ∧
      ∀ later tail, layer.rest = later :: tail → ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesCollectorLayer K D (n.data K rnd₁ rnd₂ masks),
          successor.ρ = n.ρ ∧ successor.circs = layer.circs ∧ successor.layer = layer.nextLayer ∧
          successor.nextLayer = later ∧ successor.rest = tail :=
  treeStages_collector_next_layer K D d layer.ctx₁ layer.ctx₂ layer.self₁ layer.self₂ layer.keys
    layer.gadgets₁ layer.gadgets₂ layer.mult₁ layer.mult₂ layer.circs layer.layer layer.nextLayer layer.rest
    layer.p₁ layer.p₂ layer.finish₁ layer.finish₂ layer.program₁ layer.program₂ layer.ρ layer.labels
    layer.visible layer.zero initial fresh sent sent'

/-- The second actual collector round and the next layer's PRSS entry.
This includes the adaptive rushing call and all successful or aborted local
resumptions; no continuation-coupling hypothesis remains. -/
theorem TreeStagesCollectorLayer.round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (layer : TreeStagesCollectorLayer K D d)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (layer.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ n : TreeSimCollectorNext K D d.δ a.1.2 d.k₁ d.k₂
          (fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent u.1.2.2 i))
          (fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent u.1.2.2 i)),
        n.ρ = layer.ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt layer.circs layer.nextLayer).length ∧
        TreeSimFutureEmpty (layer.ρ + 2) u.2.1.2 ∧ TreeSimFutureEmpty (layer.ρ + 2) z.2.2 ∧
        ∃ rnd₁ rnd₂, ∃ masks : n.Masks K rnd₁ rnd₂,
          TreeSimFutureZero (layer.ρ + 2) (n.data K rnd₁ rnd₂ masks).δ ∧
          u.1.2.1 = treeSimCollectorPartial K D n.live n.count rnd₁ n.v₁ n.st₁ n.next₁ ∧
          z.1.2.1 = treeSimCollectorPartial K D n.live n.count rnd₂ n.v₂ n.st₂ n.next₂ ∧
          TreeSimCollectorBoundary K D A (n.data K rnd₁ rnd₂ masks)
            ((u.1.1, u.1.2.1), u.2) ((z.1.1, z.1.2.1), z.2) ∧
          ∀ later tail, layer.rest = later :: tail →
            ∃ successor : TreeStagesCollectorLayer K D (n.data K rnd₁ rnd₂ masks),
              successor.ρ = layer.ρ + 1 ∧ successor.circs = layer.circs ∧
              successor.layer = layer.nextLayer ∧ successor.nextLayer = later ∧ successor.rest = tail) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, index, size, successor⟩ := layer.next K D d a.1.2 fresh sent u.1.2
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D A u.1.1 d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  obtain ⟨_, _, fresh₁, fresh₂, zero, rnd₁, rnd₂, masks, steps₁, steps₂, boundary⟩ := h'
  refine ⟨rfl, rfl, n, label, index, size, ?_, ?_, rnd₁, rnd₂, masks, ?_, steps₁, steps₂, boundary, ?_⟩
  · simpa only [label, Nat.add_assoc] using fresh₁
  · simpa only [label, Nat.add_assoc] using fresh₂
  · simpa only [TreeSimCollectorNext.data, label, Nat.add_assoc] using zero

  · intro later tail rest_eq
    obtain ⟨succ, label', info⟩ := successor later tail rest_eq rnd₁ rnd₂ masks zero
    exact ⟨succ, label'.trans label, info⟩

/-- Instantiate the collector-layer recipe with the actual real gadgets
and the simulator's output override. Only the saved program equations and
reachable state facts remain inputs. -/
def TreeStagesCollectorLayer.actual (D : C.Coalition) (d : TreeSimCollectorData K D)
    (mode : settings.mode = .collector) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (layer nextLayer : ℕ) (rest : List ℕ)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, i ∉ D.1 → d.k₁ i =
      treeStagesAfterLayer K (realRunGadgets K (ctx₁ i) settings.mode)
        (jobs.map (circuits parameter ·.kind)) layer (nextLayer :: rest) (p₁ i) (finish₁ i))
    (program₂ : ∀ i, i ∉ D.1 → d.k₂ i =
      treeStagesAfterLayer K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
        (jobs.map (circuits parameter ·.kind)) layer (nextLayer :: rest) (p₂ i) (finish₂ i))
    (ρ : ℕ) (labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ)
    (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0)
    (zero : TreeSimFutureZero (ρ + 1) d.δ) : TreeStagesCollectorLayer K D d where
  ctx₁ := ctx₁
  ctx₂ := ctx₂
  self₁ := self₁
  self₂ := self₂
  keys := keys
  gadgets₁ i := realRunGadgets K (ctx₁ i) settings.mode
  gadgets₂ i := treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  mult₁ := by intro i hi x y count; rw [mode]; rfl
  mult₂ := by
    intro i hi x y count
    change (prssRandomness (ctx₂ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₂ i) settings.mode rnd (mulRep K (ctx₂ i) x y) count) = _
    rw [mode]
    rfl
  circs := jobs.map (circuits parameter ·.kind)
  layer := layer
  nextLayer := nextLayer
  rest := rest
  p₁ := p₁
  p₂ := p₂
  finish₁ := finish₁
  finish₂ := finish₂
  program₁ := by exact program₁
  program₂ := by exact program₂
  ρ := ρ
  labels := labels
  visible := visible
  zero := zero

/-- Every boundary of a collector layer has its actual next transition:
the first exchange retains this recipe, forwarding enters the next concrete
layer, and a prior abort propagates to all honest operators. -/
theorem TreeStagesCollectorLayer.boundary_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimCollectorData K D)
    (layer : TreeStagesCollectorLayer K D d)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (boundary : TreeSimCollectorBoundary K D A d a b)
    (fresh : TreeSimFutureEmpty (layer.ρ + 1) a.2.1.2)
    (later : ℕ) (tail : List ℕ) (rest_eq : layer.rest = later :: tail) :
    RelTriple ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ((u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
            TreeSimStreamRel d.δ u.2 z.2) ∨
          (TreeSimCollectorBoundary K D A d ((u.1.1, u.1.2.1), u.2) ((z.1.1, z.1.2.1), z.2) ∧
            TreeSimFutureEmpty (layer.ρ + 1) u.2.1.2) ∨
          ∃ (nextData : TreeSimCollectorData K D) (successor : TreeStagesCollectorLayer K D nextData),
            successor.ρ = layer.ρ + 1 ∧ successor.circs = layer.circs ∧ successor.layer = layer.nextLayer ∧
            successor.nextLayer = later ∧ successor.rest = tail ∧
            TreeSimFutureEmpty (successor.ρ + 1) u.2.1.2 ∧
            TreeSimCollectorBoundary K D A nextData ((u.1.1, u.1.2.1), u.2) ((z.1.1, z.1.2.1), z.2))) := by
  obtain ⟨same, caches, initial | ⟨sent, forwarding⟩ | ⟨live, stopped, partialSteps⟩⟩ := boundary
  · rw [initial.1, initial.2, ← same]
    simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
    apply relTriple_post_mono (treeSim_collector_first_mixed prims K D A a.1.1 d.δ d.count
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a.2 b.2 caches)
    intro u z h
    obtain ⟨sameState, sameSent, next₁, next₂, nextCaches, private₁, _⟩ := h
    exact ⟨sameState, sameSent, Or.inr (Or.inl
      ⟨⟨sameState, nextCaches, Or.inr (Or.inl ⟨u.1.2.2, next₁, next₂⟩)⟩, by simpa only [private₁] using fresh⟩)⟩
  · rw [forwarding.1, forwarding.2, ← same]
    apply relTriple_post_mono (layer.round prims K D A a.1.1 d sent a.2 b.2 caches fresh)
    intro u z h
    obtain ⟨sameState, sameSent, n, label, _, _, fresh₁, _, rnd₁, rnd₂, masks, _, _, _, nextBoundary, successor⟩ := h
    obtain ⟨next, nextLabel, info⟩ := successor later tail rest_eq
    refine ⟨sameState, sameSent, Or.inr (Or.inr ⟨n.data K rnd₁ rnd₂ masks, next, nextLabel,
      info.1, info.2.1, info.2.2.1, info.2.2.2, ?_, nextBoundary⟩)⟩
    simpa only [nextLabel, Nat.add_assoc] using fresh₁
  · rw [partialSteps.1, partialSteps.2, ← same]
    simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
    apply relTriple_post_mono (treeSim_collector_partial_mixed prims K D A a.1.1 live stopped d.δ d.count
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a.2 b.2 caches)
    intro u z h
    exact ⟨h.1, h.2.1, Or.inl ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩⟩

/-- The next peer exchange after an optional gadget return. Stopped parties
remain stopped, while live parties retain their actual translated masks. -/
def TreeStagesPeerResumeRel (D : C.Coalition) (live : C.Party → Bool) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (x y : C.Party → Step C E RealSpec TreeOutput) : Prop :=
  ∀ i, if i ∈ D.1 then x i = .done none ∧ y i = .done none else
    if live i then TreeSimPeerRel K δ (ctx₁ i) (ctx₂ i) idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (k₁ i) (k₂ i) (x i) (y i)
    else x i = .done none ∧ y i = .done none

/-- Actual optional resumptions into a peer PRSS draw, in the driver's order. -/
theorem treeStages_peer_resume_entry (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (live : C.Party → Bool)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (label : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (k₁ k₂ next₁ next₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (x₁ x₂ : C.Party → Shares C Bit × RunState C)
    (shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none)
    (shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none)
    (program₁ : ∀ i, i ∉ D.1 → live i = true → k₁ i (x₁ i) =
      treeSimPeerProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) (next₁ i))
    (program₂ : ∀ i, i ∉ D.1 → live i = true → k₂ i (x₂ i) =
      treeSimPeerProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) (next₂ i))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeStagesPeerResumeRel K D live δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ next₁ next₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  apply treeSim_resumeAll_rel prims D k₁ k₂ out₁ out₂ (TreeSimStreamRel δ)
    (fun i u z => if i ∈ D.1 then u = .done none ∧ z = .done none else
      if live i then TreeSimPeerRel K δ (ctx₁ i) (ctx₂ i) idx count (v₁ i) (v₂ i)
        (st₁ i) (st₂ i) (next₁ i) (next₂ i) u z else u = .done none ∧ z = .done none) _ a b related
  intro i a b h
  rw [shape₁ i, shape₂ i]
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, h⟩
  · simp only [if_neg hi]
    by_cases hl : live i = true
    · simp only [if_pos hl, treeSimResume, program₁ i hi hl, program₂ i hi hl]
      exact treeSim_peer_start_mixed prims K D δ visible (ctx₁ i) (ctx₂ i) (self i hi) (keys i hi)
        idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (label i hi) (next₁ i) (next₂ i) a b h
    · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, h⟩

/-- The actual check and opening after Rerand, retaining the preceding layer
records and the real caller. -/
def treeStagesAfterRerand (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (p : List (C.Term → List Bit) × List (Tuple C))
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C Bit × RunState C) : PartyM C E RealSpec TreeOutput :=
  ((do
    gadgets.verify (p.2 ++ [⟨outputShares K circs p.1, one K, out.1, (outputsOf circs).length, .peer⟩])
    let opened ← gadgets.output out.1 (outputsOf circs).length
    pure (assemble circs opened) : RunM C E RealSpec (List (List Bit))).run out.2) >>= finish

/-- With no AND layers remaining, the actual next gadget is peer Rerand in
either reshare mode; its complete check/output suffix remains suspended. -/
theorem treeStages_layers_rerand (ctx : Context C) (gadgets : RunGadgets C E RealSpec)
    (rerand : ∀ v count, gadgets.rerand v count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count))
    (circs : List Circuit) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesLayers K gadgets circs [] p st finish =
      treeSimPeerProgram K ctx 0 (outputsOf circs).length (ownerSum K ctx (outputShares K circs p.1)) st
        (treeStagesAfterRerand K gadgets circs p finish) := by
  simp only [treeStagesLayers, List.foldlM_nil, pure_bind, tailBody,
    StateT.run_bind, rerand, treeSimPeerProgram, bind_assoc]
  apply bind_congr
  intro out
  apply bind_congr
  intro shared
  simp only [treeStagesAfterRerand, StateT.run_bind, bind_assoc]

/-- Peer PRSS entry writes only the current label in the hidden cache. -/
theorem treeStages_peer_entry_frame {α : Type} (D : C.Coalition) (ctx : Context C)
    (idx count : ℕ) (v : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s : HashCache C × HiddenCache C) (r : Step C E RealSpec α × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((treeSimPeerProgram K ctx idx count v st k).run)))).run s)) :
    TreeSimCacheFrame st.label s.2 r.2.2 := by
  unfold treeSimPeerProgram at hr
  rw [treeSim_peer_entry] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact treeSim_prssBits_frame (E := E) prims D ctx st.label idx count s u hu

/-- The input phase followed by peer PRSS writes only the entry label.
This is a support statement, so it needs no cache coverage or coupling premise. -/
theorem treeStages_batch_peer_entry_frame (D : C.Coalition) (ctx : Context C)
    (jobs : List Job) (idx count : ℕ) (value : List (C.Term → List Bit) → ℕ → Bit)
    (st : RunState C)
    (k : List (C.Term → List Bit) → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (s : HashCache C × HiddenCache C)
    (r : Step C E RealSpec TreeOutput × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((treeStagesBatchProgram K ctx .peer jobs idx count value st k).run)))).run s)) :
    TreeSimCacheFrame st.label s.2 r.2.2 := by
  unfold treeStagesBatchProgram at hr
  simp only [inputShares_fun, mapM_oracleStep, worldRoles, advance_oracleStep_bind,
    free_bind, simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hr
  obtain ⟨u, hu, hr⟩ := hr
  rw [treeStages_inputQueries_onHash] at hu
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact treeStages_peer_entry_frame prims K D ctx idx count (value v.1) st (k v.1) (v.2, s.2) r hr

/-- Starting all peer batch programs preserves every other hidden label,
including when earlier parties have extended the shared public cache. -/
theorem treeStages_batch_peer_start_frame (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (ρ : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .peer)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (s : HashCache C × HiddenCache C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (startSteps worldRoles D (fun i => (d i).real K))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  simp only [startSteps, simulateQ_sequenceFin] at hr
  intro x hx
  apply treeStages_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 x) _ _ s r hr
  intro i a b hb
  by_cases hi : i ∈ D.1
  · simp [hi] at hb
    subst b
    rfl
  · simp only [if_neg hi, TreeStagesBatchData.real, mode i hi] at hb
    have frame := treeStages_batch_peer_entry_frame prims K D (d i).ctx₁ (d i).jobs
      (d i).idx (d i).count (d i).value₁ (d i).st₁ (d i).k₁ a b hb
    rw [label i hi] at frame
    exact frame x hx

/-- Erasing only the log transfers the exact peer batch footprint. -/
theorem treeStages_batch_peer_start_logged_frame (D : C.Coalition) (base : HashCache C)
    (d : C.Party → TreeStagesBatchData C E base) (ρ : ℕ)
    (mode : ∀ i, i ∉ D.1 → (d i).mode = .peer)
    (label : ∀ i, i ∉ D.1 → (d i).st₁.label = ρ)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => (d i).real K))).run s)) :
    TreeSimCacheFrame ρ s.1.2 r.2.1.2 := by
  apply treeStages_batch_peer_start_frame prims K D base d ρ mode label s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- A selectively aborted vector resumes only its live programs. No local
entry can touch another label, even after earlier holders populate this one. -/
theorem treeStages_peer_resume_frame {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (ρ idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = ρ)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = treeSimPeerProgram K (ctx i) idx count (v i) (st i) (next i))
    (s : HashCache C × HiddenCache C) (r : (C.Party → Step C E RealSpec α) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  unfold treeSimResumeAll at hr
  rw [free_sequenceFin, simulateQ_sequenceFin] at hr
  intro y hy
  apply treeStages_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 y) _ _ s r hr
  intro i a b hb
  rw [shape i] at hb
  by_cases hi : i ∈ D.1
  · simp [hi, treeSimResume, free_pure] at hb
    subst b
    rfl
  · simp only [if_neg hi] at hb
    by_cases hl : live i = true
    · simp only [if_pos hl, treeSimResume, program i hi hl] at hb
      have h := treeStages_peer_entry_frame prims K D (ctx i) idx count (v i) (st i) (next i) a b hb
      rw [lab i hi hl] at h
      exact h y hy
    · simp [hl, treeSimResume, free_pure] at hb
      subst b
      rfl

/-- The logged resumption has exactly the same private-cache footprint. -/
theorem treeStages_peer_resume_logged_frame {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (ρ idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = ρ)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = treeSimPeerProgram K (ctx i) idx count (v i) (st i) (next i))
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame ρ s.1.2 r.2.1.2 := by
  apply treeStages_peer_resume_frame prims K D ctx ρ idx count v st k next out x live lab shape program
    s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- Export actual peer masks from a selectively aborted resumption. Dummy
masks for stopped parties occur only in the certificate, never in the run. -/
theorem treeStages_peer_resume_masks (D : C.Coalition) (live : C.Party → Bool) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (x y : C.Party → Step C E RealSpec TreeOutput)
    (related : TreeStagesPeerResumeRel K D live δ ctx₁ ctx₂ 0 count v₁ v₂ st₁ st₂ k₁ k₂ x y) :
    ∃ rnd₁ rnd₂ : C.Party → PrssOutput C Bit,
      (∀ i, i ∉ D.1 →
        (rnd₂ i).1 = (rnd₁ i).1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1 ∧
        (rnd₂ i).2 = (rnd₁ i).2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2) ∧
      x = treeSimPeerPartial K D ctx₁ live count rnd₁ v₁ st₁ k₁ ∧
      y = treeSimPeerPartial K D ctx₂ live count rnd₂ v₂ st₂ k₂ := by
  have witnesses : ∀ i, ∃ r₁ r₂ : PrssOutput C Bit,
      (i ∉ D.1 → r₂.1 = r₁.1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1 ∧
        r₂.2 = r₁.2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2) ∧
      x i = (if live i then if i ∈ D.1 then .done none else treeSimPeerStep K (ctx₁ i) bitCodec r₁ (v₁ i) count (st₁ i) (k₁ i) else .done none) ∧
      y i = (if live i then if i ∈ D.1 then .done none else treeSimPeerStep K (ctx₂ i) bitCodec r₂ (v₂ i) count (st₂ i) (k₂ i) else .done none) := by
    intro i
    have h := related i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi] at h ⊢
      exact ⟨0, 0, fun hn => (hn hi).elim, by simpa using h⟩
    · simp only [if_neg hi] at h ⊢
      by_cases hl : live i = true
      · simp only [if_pos hl] at h ⊢
        obtain ⟨r₁, r₂, hm₁, hm₂, hx, hy⟩ := h
        exact ⟨r₁, r₂, fun _ => ⟨hm₁, hm₂⟩, hx, hy⟩
      · simp only [if_neg hl] at h ⊢
        exact ⟨0, treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count,
          fun _ => ⟨by simp, by simp⟩, h⟩
  choose rnd₁ rnd₂ masks hx hy using witnesses
  exact ⟨rnd₁, rnd₂, masks, funext hx, funext hy⟩

/-- Concrete next-peer certificate for a saved gadget continuation. The
whole vector chooses its fresh GS20 translation before the first live draw. -/
structure TreeStagesPeerNext (D : C.Coalition) (past : HiddenAddress C → Bit) (initial : HiddenCache C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C)) where
  T₀ : C.Term
  pivotParty : C.Party
  pivot : Pivot K D T₀ pivotParty
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  ρ : ℕ
  count : ℕ
  v₁ : C.Party → ℕ → Bit
  v₂ : C.Party → ℕ → Bit
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ
  next₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  next₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  x₁ : C.Party → Shares C Bit × RunState C
  x₂ : C.Party → Shares C Bit × RunState C
  live : C.Party → Bool
  shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none
  shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none
  program₁ : ∀ i, i ∉ D.1 → live i = true → k₁ i (x₁ i) =
    treeSimPeerProgram K (ctx₁ i) 0 count (v₁ i) (st₁ i) (next₁ i)
  program₂ : ∀ i, i ∉ D.1 → live i = true → k₂ i (x₂ i) =
    treeSimPeerProgram K (ctx₂ i) 0 count (v₂ i) (st₂ i) (next₂ i)
  history : List Bit
  states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i)
  visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0
  futureZero : TreeSimFutureZero ρ past
  futureEmpty : TreeSimFutureEmpty ρ initial

def TreeStagesPeerNext.δ {D : C.Coalition} {past : HiddenAddress C → Bit} {initial : HiddenCache C} {k₁ k₂ out₁ out₂}
    (n : TreeStagesPeerNext K D past initial k₁ k₂ out₁ out₂) : HiddenAddress C → Bit :=
  past + treeSimPeerShift K D n.T₀ n.pivotParty n.ρ 0 n.count (n.v₁ - n.v₂) 0

theorem TreeStagesPeerNext.block {D : C.Coalition} {past : HiddenAddress C → Bit} {initial : HiddenCache C} {k₁ k₂ out₁ out₂}
    (n : TreeStagesPeerNext K D past initial k₁ k₂ out₁ out₂) (i : C.Party) (hi : i ∉ D.1) :
    treeSimPrssShift (n.δ K) (n.ctx₁ i) (n.st₁ i).label 0 n.count =
      frandShare D n.count 0 0 (termShift K D n.T₀ n.pivotParty (n.v₁ - n.v₂) (0 : C.Term → Fin n.count → Bit))
        (pairShift n.pivotParty (pairDelta K D n.T₀ n.pivotParty (n.v₁ - n.v₂) (0 : C.Term → Fin n.count → Bit))) i := by
  rw [n.lab₁ i hi, TreeStagesPeerNext.δ, treeSim_prssShift_add,
    treeSim_prssShift_zero past (n.ctx₁ i) n.ρ 0 n.count (fun _ _ _ _ => n.futureZero _ (by rfl)), zero_add]
  unfold treeSimPeerShift
  rw [treeSim_prssShift_block D (n.ctx₁ i) (by simpa only [n.self₁ i hi] using hi), n.self₁ i hi]

def TreeStagesPeerNext.Masks {D : C.Coalition} {past : HiddenAddress C → Bit} {initial : HiddenCache C} {k₁ k₂ out₁ out₂}
    (n : TreeStagesPeerNext K D past initial k₁ k₂ out₁ out₂) (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) : Prop :=
  ∀ i, i ∉ D.1 →
    (rnd₂ i).1 = (rnd₁ i).1 + (treeSimPrssShift (n.δ K) (n.ctx₁ i) (n.st₁ i).label 0 n.count).1 ∧
    (rnd₂ i).2 = (rnd₁ i).2 + (treeSimPrssShift (n.δ K) (n.ctx₁ i) (n.st₁ i).label 0 n.count).2

def TreeStagesPeerNext.data {D : C.Coalition} {past : HiddenAddress C → Bit} {initial : HiddenCache C} {k₁ k₂ out₁ out₂}
    (n : TreeStagesPeerNext K D past initial k₁ k₂ out₁ out₂) (rnd₁ rnd₂ : C.Party → PrssOutput C Bit)
    (masks : n.Masks K rnd₁ rnd₂) : TreeSimPeerData K D :=
  ⟨n.δ K, n.count, n.ctx₁, n.ctx₂, rnd₁, rnd₂, n.v₁, n.v₂, n.st₁, n.st₂, n.next₁, n.next₂, masks,
    n.T₀, n.pivotParty, n.pivot, n.self₁, n.self₂, n.history, n.states, n.block K⟩

/-- Actual next-peer resumption exports the frozen peer data and freshness
for the following check, without assuming a continuation coupling. -/
theorem TreeStagesPeerNext.coupling (D : C.Coalition)
    (past : HiddenAddress C → Bit) (initial : HiddenCache C) (k₁ k₂ out₁ out₂)
    (n : TreeStagesPeerNext K D past initial k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (related : TreeSimStreamRel past a b)
    (ha : a.1.2 = initial) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeSimStreamRel (n.δ K) u.2 z.2 ∧
        TreeSimFutureEmpty (n.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (n.ρ + 1) z.2.2 ∧
        TreeSimFutureZero (n.ρ + 1) (n.δ K) ∧
        ∃ rnd₁ rnd₂, ∃ masks : n.Masks K rnd₁ rnd₂,
          u.1 = treeSimPeerPartial K D n.ctx₁ n.live n.count rnd₁ n.v₁ n.st₁ n.next₁ ∧
          z.1 = treeSimPeerPartial K D n.ctx₂ n.live n.count rnd₂ n.v₂ n.st₂ n.next₂) := by
  have visible : ∀ x, ¬ Hidden D x.1.1 → n.δ K x = 0 := by
    intro x hx
    simp only [TreeStagesPeerNext.δ, Pi.add_apply, n.visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D n.ρ 0 n.count _ _ x hx, add_zero]
  have fresh : ∀ x, (a.1.2 x).isSome →
      treeSimPeerShift K D n.T₀ n.pivotParty n.ρ 0 n.count (n.v₁ - n.v₂) 0 x = 0 := by
    rw [ha]
    exact treeSim_futureEmpty_block D n.ρ 0 n.count _ _ initial n.futureEmpty
  apply relTriple_post_mono (treeSim_relTriple_support (treeStages_peer_resume_entry prims K D (n.δ K) visible
    n.live n.ctx₁ n.ctx₂ (fun i hi => (n.self₁ i hi).trans (n.self₂ i hi).symm) n.keys 0 n.count
    n.v₁ n.v₂ n.st₁ n.st₂ (fun i hi => (n.lab₁ i hi).trans (n.lab₂ i hi).symm)
    k₁ k₂ n.next₁ n.next₂ out₁ out₂ n.x₁ n.x₂ n.shape₁ n.shape₂ n.program₁ n.program₂ a b
    ⟨related.1, treeSim_hiddenRel_extend past _ related.2 fresh⟩))
  intro u z h
  have frame₁ := treeStages_peer_resume_logged_frame prims K D n.ctx₁ n.ρ 0 n.count n.v₁ n.st₁
    k₁ n.next₁ out₁ n.x₁ n.live (fun i hi _ => n.lab₁ i hi) n.shape₁ n.program₁ a u h.2.1
  have frame₂ := treeStages_peer_resume_frame prims K D n.ctx₂ n.ρ 0 n.count n.v₂ n.st₂
    k₂ n.next₂ out₂ n.x₂ n.live (fun i hi _ => n.lab₂ i hi) n.shape₂ n.program₂ b z h.2.2
  have empty : TreeSimFutureEmpty n.ρ a.1.2 := by simpa only [ha] using n.futureEmpty
  obtain ⟨rnd₁, rnd₂, masks, realSteps, idealSteps⟩ := treeStages_peer_resume_masks K D n.live (n.δ K)
    n.ctx₁ n.ctx₂ n.count n.v₁ n.v₂ n.st₁ n.st₂ n.next₁ n.next₂ u.1 z.1 h.1.1
  exact ⟨h.1.2, treeSim_futureEmpty_after empty frame₁,
    treeSim_futureEmpty_after (treeSim_futureEmpty_related empty related.2) frame₂,
    treeSim_futureZero_extend D n.ρ 0 n.count _ _ past n.futureZero,
    rnd₁, rnd₂, masks, realSteps, idealSteps⟩

/-- The actual check/output code saved at a Rerand boundary. -/
structure TreeStagesRerandTail (D : C.Coalition) (d : TreeSimPeerData K D) where
  gadgets₁ : C.Party → RunGadgets C E RealSpec
  gadgets₂ : C.Party → RunGadgets C E RealSpec
  circs : List Circuit
  count : d.count = (outputsOf circs).length
  p₁ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  finish₁ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → d.k₁ i = treeStagesAfterRerand K (gadgets₁ i) circs (p₁ i) (finish₁ i)
  program₂ : ∀ i, i ∉ D.1 → d.k₂ i = treeStagesAfterRerand K (gadgets₂ i) circs (p₂ i) (finish₂ i)
  ρ : ℕ
  labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ

  keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss
  verify₁ : ∀ i, i ∉ D.1 → (gadgets₁ i).verify = check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i))
  verify₂ : ∀ i, i ∉ D.1 → (gadgets₂ i).verify = check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i))
  visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0

/-- A final collector layer retains the real peer Rerand and the entire
check/output suffix, even though preceding multiplications used collectors. -/
structure TreeStagesCollectorTail (D : C.Coalition) (d : TreeSimCollectorData K D) where
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  gadgets₁ : C.Party → RunGadgets C E RealSpec
  gadgets₂ : C.Party → RunGadgets C E RealSpec
  rerand₁ : ∀ i, i ∉ D.1 → ∀ v count, (gadgets₁ i).rerand v count = (do
    let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
    reshare K (ctx₁ i) bitCodec rnd (ownerSum K (ctx₁ i) v) count)
  rerand₂ : ∀ i, i ∉ D.1 → ∀ v count, (gadgets₂ i).rerand v count = (do
    let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
    reshare K (ctx₂ i) bitCodec rnd (ownerSum K (ctx₂ i) v) count)
  circs : List Circuit
  layer : ℕ
  p₁ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  finish₁ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → d.k₁ i = treeStagesAfterLayer K (gadgets₁ i) circs layer [] (p₁ i) (finish₁ i)
  program₂ : ∀ i, i ∉ D.1 → d.k₂ i = treeStagesAfterLayer K (gadgets₂ i) circs layer [] (p₂ i) (finish₂ i)
  ρ : ℕ
  labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ
  visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0
  zero : TreeSimFutureZero (ρ + 1) d.δ

  verify₁ : ∀ i, i ∉ D.1 → (gadgets₁ i).verify = check K (ctx₁ i) (realCheckGadgets K (ctx₁ i))
  verify₂ : ∀ i, i ∉ D.1 → (gadgets₂ i).verify = check K (ctx₂ i) (realCheckGadgets K (ctx₂ i))

/-- Construct the next Rerand certificate directly from the final collector
outputs, keeping aborts and the real recorded state. -/
theorem TreeStagesCollectorTail.next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (tail : TreeStagesCollectorTail K D d) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (tail.ρ + 1) initial) (sent sent' : C.Party → Mail C E) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeStagesPeerNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = tail.ρ + 1 ∧ n.count = (outputsOf tail.circs).length ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        ∃ rest : TreeStagesRerandTail K D (n.data K rnd₁ rnd₂ masks), rest.ρ = n.ρ ∧ rest.circs = tail.circs := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let nextP₁ := fun i => (appendLayer tail.circs tail.layer (tail.p₁ i).1 (x₁ i).1,
    (tail.p₁ i).2 ++ [⟨layerX K tail.circs tail.layer (tail.p₁ i).1, layerY K tail.circs tail.layer (tail.p₁ i).1,
      (x₁ i).1, (gatesAt tail.circs tail.layer).length, (tail.gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer tail.circs tail.layer (tail.p₂ i).1 (x₂ i).1,
    (tail.p₂ i).2 ++ [⟨layerX K tail.circs tail.layer (tail.p₂ i).1, layerY K tail.circs tail.layer (tail.p₂ i).1,
      (x₂ i).1, (gatesAt tail.circs tail.layer).length, (tail.gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := T₀, pivotParty := pivotParty, pivot := pivot
    ctx₁ := tail.ctx₁, ctx₂ := tail.ctx₂, self₁ := tail.self₁, self₂ := tail.self₂, keys := tail.keys
    ρ := tail.ρ + 1, count := (outputsOf tail.circs).length
    v₁ := fun i => ownerSum K (tail.ctx₁ i) (outputShares K tail.circs (nextP₁ i).1)
    v₂ := fun i => ownerSum K (tail.ctx₂ i) (outputShares K tail.circs (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (tail.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (tail.labels i hi)))
    next₁ := fun i => treeStagesAfterRerand K (tail.gadgets₁ i) tail.circs (nextP₁ i) (tail.finish₁ i)
    next₂ := fun i => treeStagesAfterRerand K (tail.gadgets₂ i) tail.circs (nextP₂ i) (tail.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := tail.visible, futureZero := tail.zero, futureEmpty := fresh
  }, rfl, rfl, ?_⟩
  · intro i hi _
    rw [tail.program₁ i hi]
    exact treeStages_layers_rerand K (tail.ctx₁ i) (tail.gadgets₁ i) (tail.rerand₁ i hi)
      tail.circs (nextP₁ i) (x₁ i).2 (tail.finish₁ i)
  · intro i hi _
    rw [tail.program₂ i hi]
    exact treeStages_layers_rerand K (tail.ctx₂ i) (tail.gadgets₂ i) (tail.rerand₂ i hi)
      tail.circs (nextP₂ i) (x₂ i).2 (tail.finish₂ i)
  · intro rnd₁ rnd₂ masks
    refine ⟨⟨tail.gadgets₁, tail.gadgets₂, tail.circs, rfl, nextP₁, nextP₂, tail.finish₁, tail.finish₂,
      (by intros; rfl), (by intros; rfl), tail.ρ + 1,
      (fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (tail.labels i hi))),
      tail.keys, tail.verify₁, tail.verify₂, ?_⟩, rfl, rfl⟩
    intro x hx
    simp only [TreeStagesPeerNext.data, TreeStagesPeerNext.δ, Pi.add_apply, tail.visible x hx,
      treeSimPeerShift, treeSim_blockShift_visible D (tail.ρ + 1) 0 _ _ _ x hx, add_zero]

/-- The complete final collector forwarding round reaches the actual Rerand
boundary with balanced GS20 masks, fresh later labels and saved check code. -/
theorem TreeStagesCollectorTail.round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
          rest.ρ = tail.ρ + 1 ∧ rest.circs = tail.circs ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (rest.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (rest.ρ + 1) z.2.2 ∧
          TreeSimFutureZero (rest.ρ + 1) next.δ ∧
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, after⟩ := tail.next K D d a.1.2 fresh sent u.1.2
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨caches, empty₁, empty₂, zero, rnd₁, rnd₂, masks, next₁, next₂⟩ := h'
  obtain ⟨rest, restLabel, restCircs⟩ := after rnd₁ rnd₂ masks
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, rest, n.live, restLabel.trans label, restCircs, caches, ?_, ?_, ?_, next₁, next₂⟩
  · simpa only [restLabel] using empty₁
  · simpa only [restLabel] using empty₂
  · simpa only [restLabel, TreeStagesPeerNext.data] using zero

/-- The actual check suffix after its first Coin, retaining the pre-Coin
hash label and all subsequent slice, halving, digest and final tests. -/
def treeStagesCheckAfterCoin {α : Type} (ctx : Context C) (tuples : List (Tuple C))
    (tag label : ℕ) (finish : Unit × RunState C → PartyM C E RealSpec α)
    (out : List E × RunState C) : PartyM C E RealSpec α := (do
  let key ← StateT.lift (oracleStep (hashQuery (.coinKey tag label
    (out.1.flatMap fun v => List.ofFn (K.encode v)))))
  let count := (tuples.map (·.count)).sum
  let τ ← expand K key (coins count)
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  let p ← (List.range sliceBits).foldlM (sliceStep K ctx (realCheckGadgets K ctx) τ count)
    ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k : Shares C E), liftedPart tuples (·.y),
      conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)
  let p' ← (List.range (halvings count - sliceBits)).foldlM
    (halvingStep K ctx (realCheckGadgets K ctx) (sliceWidth count))
    (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
  finalStep K ctx (realCheckGadgets K ctx) p' : RunM C E RealSpec Unit).run out.2 >>= finish

theorem treeStages_check_coin_entry {α : Type} (ctx : Context C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec α) :
    (check K ctx (realCheckGadgets K ctx) tuples).run st >>= finish =
      ((realCheckGadgets K ctx).coin 1).run st >>=
        treeStagesCheckAfterCoin K ctx tuples st.tag st.label finish := by
  rw [check_eq K ctx (realCheckGadgets K ctx) tuples nonzero]
  simp only [coinKey, treeStagesCheckAfterCoin, StateT.run_bind,
    StateT.run_get, StateT.run_lift, pure_bind, bind_assoc]
  apply bind_congr
  intro out
  simp only [treeStagesCheckAfterCoin, StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]

/-- The Rerand tuple checked together with every recorded multiplication. -/
def treeStagesRerandTuples (circs : List Circuit)
    (p : List (C.Term → List Bit) × List (Tuple C)) (v : Shares C Bit) : List (Tuple C) :=
  p.2 ++ [⟨outputShares K circs p.1, one K, v, (outputsOf circs).length, .peer⟩]

/-- Successful verification resumes the actual output gadget and batch caller. -/
def treeStagesAfterVerify (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (v : Shares C Bit) (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Unit × RunState C) : PartyM C E RealSpec TreeOutput :=
  ((do
    let opened ← gadgets.output v (outputsOf circs).length
    pure (assemble circs opened) : RunM C E RealSpec (List (List Bit))).run out.2) >>= finish

/-- The nonempty actual Rerand check enters its first Coin, without changing
its tuples, recorded state, output correction or saved batch caller. -/
theorem treeStages_rerand_coin_entry (ctx : Context C) (gadgets : RunGadgets C E RealSpec)
    (verify : gadgets.verify = check K ctx (realCheckGadgets K ctx))
    (circs : List Circuit) (p : List (C.Term → List Bit) × List (Tuple C))
    (nonzero : (p.2.map (·.count)).sum + (outputsOf circs).length ≠ 0)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C Bit × RunState C) :
    treeStagesAfterRerand K gadgets circs p finish out =
      ((realCheckGadgets K ctx).coin 1).run out.2 >>=
        treeStagesCheckAfterCoin K ctx (treeStagesRerandTuples K circs p out.1) out.2.tag out.2.label
          (treeStagesAfterVerify gadgets circs out.1 finish) := by
  have hcount : ((treeStagesRerandTuples K circs p out.1).map (·.count)).sum ≠ 0 := by
    simpa [treeStagesRerandTuples] using nonzero
  rw [← treeStages_check_coin_entry K ctx _ hcount out.2]
  simp only [treeStagesAfterRerand, treeStagesRerandTuples, StateT.run_bind, verify, bind_assoc]
  apply bind_congr
  intro checked
  simp only [treeStagesAfterVerify, StateT.run_bind, bind_assoc]

/-- Inactive peer returns are defaulted only in the certificate. Their label
is still the next absolute label, just as for a successful recorded output. -/
theorem treeStages_peer_recorded_label {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    ((treeSimPeerOutputs K D ctx count rnd v st k sent i).getD (0, nextLabel (st i))).2.label =
      (st i).label + 1 := by
  unfold treeSimPeerOutputs treeSimPeerReturn
  split_ifs <;> rfl

/-- The actual optional peer returns determine both saved Coin continuations.
Honest histories may differ by T₀; only success and labels are synchronized. -/
def treeStages_peer_coinNext (D : C.Coalition) (d : TreeSimPeerData K D)
    (sent : C.Party → Mail C E) (label count : ℕ)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (lab₁ : ∀ i, i ∉ D.1 → (d.st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (d.st₂ i).label = label)
    (next₁ next₂ : C.Party → (Shares C Bit × RunState C) → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, i ∉ D.1 → ∀ x, d.k₁ i x = ((realCheckGadgets K (d.ctx₁ i)).coin count).run x.2 >>= next₁ i x)
    (program₂ : ∀ i, i ∉ D.1 → ∀ x, d.k₂ i x = ((realCheckGadgets K (d.ctx₂ i)).coin count).run x.2 >>= next₂ i x) :
    TreeStagesCoinNext K D d.k₁ d.k₂
      (treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)
      (treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent) := by
  let out₁ := treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
  let out₂ := treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
  let x₁ := fun i => (out₁ i).getD (0, nextLabel (d.st₁ i))
  let x₂ := fun i => (out₂ i).getD (0, nextLabel (d.st₂ i))
  have live : ∀ i, (out₁ i).isSome = (out₂ i).isSome := by
    intro i
    have h := d.outputs K D sent i
    change Option.Rel _ (out₁ i) (out₂ i) at h
    generalize out₁ i = left at h ⊢
    generalize out₂ i = right at h ⊢
    cases h <;> rfl
  refine {
    label := label + 1, count := count
    ctx₁ := d.ctx₁, ctx₂ := d.ctx₂, self₁ := d.self₁, self₂ := d.self₂, keys := keys
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := ?_, lab₂ := ?_
    live := fun i => (out₁ i).isSome, x₁ := x₁, x₂ := x₂
    shape₁ := ?_, shape₂ := ?_
    next₁ := fun i => next₁ i (x₁ i), next₂ := fun i => next₂ i (x₂ i)
    program₁ := fun i hi _ => program₁ i hi (x₁ i)
    program₂ := fun i hi _ => program₂ i hi (x₂ i) }
  · intro i hi
    exact (treeStages_peer_recorded_label K D _ _ _ _ _ _ sent i).trans (congrArg (· + 1) (lab₁ i hi))
  · intro i hi
    exact (treeStages_peer_recorded_label K D _ _ _ _ _ _ sent i).trans (congrArg (· + 1) (lab₂ i hi))
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₁, treeSimPeerOutputs, hi]
    · rw [if_neg hi]
      exact treeStages_option_shape (out₁ i) _
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₂, treeSimPeerOutputs, hi]
    · rw [if_neg hi, live i]
      exact treeStages_option_shape (out₂ i) _

/-- Peer exchange and the next actual Coin entry, including its field PRSS
and fresh-label frame. No future continuation coupling is assumed. -/
theorem treeStages_peer_coin_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (label count : ℕ) (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0)
    (future : TreeSimFutureZero (label + 1) d.δ)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (lab₁ : ∀ i, i ∉ D.1 → (d.st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (d.st₂ i).label = label)
    (next₁ next₂ : C.Party → (Shares C Bit × RunState C) → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, i ∉ D.1 → ∀ x, d.k₁ i x = ((realCheckGadgets K (d.ctx₁ i)).coin count).run x.2 >>= next₁ i x)
    (program₂ : ∀ i, i ∉ D.1 → ∀ x, d.k₂ i x = ((realCheckGadgets K (d.ctx₂ i)).coin count).run x.2 >>= next₂ i x)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => ∃ sent rnd,
        let n := treeStages_peer_coinNext K D d sent label count keys lab₁ lab₂ next₁ next₂ program₁ program₂
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
        z.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ TreeSimFutureZero (label + 2) d.δ ∧
        TreeSimFutureEmpty (label + 2) u.2.1.2 ∧ TreeSimFutureEmpty (label + 2) z.2.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_peer_resume_factor, treeSim_peer_resume_factor, d.view K D]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b h)
  intro r₁ r₂ hr
  rw [hr.1]
  let n := treeStages_peer_coinNext K D d r₂.1.2 label count keys lab₁ lab₂ next₁ next₂ program₁ program₂
  have fresh' : TreeSimFutureEmpty n.label r₁.2.1.2 := by
    rw [hr.2.2.1]
    exact fresh
  apply relTriple_bind (n.coupling_fresh prims K D d.k₁ d.k₂ _ _ d.δ visible future r₁.2 r₂.2 hr.2.1 fresh')
  intro u z hz
  obtain ⟨_, _, hf₁, hf₂, hδ, ⟨rnd, hu, hz⟩, hc⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨r₂.1.2, rnd, rfl, rfl, rfl, hu, hz, hc, hδ, hf₁, hf₂⟩

/-- The first check Coin retains the entire actual Rerand suffix. -/
def TreeStagesRerandTail.coinNext (D : C.Coalition) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (verify₁ : ∀ i, i ∉ D.1 → (tail.gadgets₁ i).verify = check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i)))
    (verify₂ : ∀ i, i ∉ D.1 → (tail.gadgets₂ i).verify = check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i)))
    (nonzero₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (sent : C.Party → Mail C E) :
    TreeStagesCoinNext K D d.k₁ d.k₂
      (treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)
      (treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent) :=
  treeStages_peer_coinNext K D d sent tail.ρ 1 keys tail.labels
    (fun i hi => (d.states i hi).1.symm.trans (tail.labels i hi))
    (fun i out => treeStagesCheckAfterCoin K (d.ctx₁ i) (treeStagesRerandTuples K tail.circs (tail.p₁ i) out.1)
      out.2.tag out.2.label (treeStagesAfterVerify (tail.gadgets₁ i) tail.circs out.1 (tail.finish₁ i)))
    (fun i out => treeStagesCheckAfterCoin K (d.ctx₂ i) (treeStagesRerandTuples K tail.circs (tail.p₂ i) out.1)
      out.2.tag out.2.label (treeStagesAfterVerify (tail.gadgets₂ i) tail.circs out.1 (tail.finish₂ i)))
    (by intro i hi out; rw [tail.program₁ i hi]
        exact treeStages_rerand_coin_entry K _ _ (verify₁ i hi) _ _ (nonzero₁ i hi) _ _)
    (by intro i hi out; rw [tail.program₂ i hi]
        exact treeStages_rerand_coin_entry K _ _ (verify₂ i hi) _ _ (nonzero₂ i hi) _ _)

/-- The real Rerand round reaches the check's first Coin with its actual
recorded tuples, different honest histories, and unchanged adaptive shift. -/
theorem TreeStagesRerandTail.coin_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (verify₁ : ∀ i, i ∉ D.1 → (tail.gadgets₁ i).verify = check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i)))
    (verify₂ : ∀ i, i ∉ D.1 → (tail.gadgets₂ i).verify = check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i)))
    (nonzero₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) (future : TreeSimFutureZero (tail.ρ + 1) d.δ)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => ∃ sent rnd,
        let n := tail.coinNext K D d keys verify₁ verify₂ nonzero₁ nonzero₂ sent
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
        z.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ TreeSimFutureZero (tail.ρ + 2) d.δ ∧
        TreeSimFutureEmpty (tail.ρ + 2) u.2.1.2 ∧ TreeSimFutureEmpty (tail.ρ + 2) z.2.2) := by
  exact treeStages_peer_coin_round prims K D A d tail.ρ 1 visible future keys tail.labels
    (fun i hi => (d.states i hi).1.symm.trans (tail.labels i hi)) _ _
    (by intro i hi out; rw [tail.program₁ i hi]
        exact treeStages_rerand_coin_entry K _ _ (verify₁ i hi) _ _ (nonzero₁ i hi) _ _)
    (by intro i hi out; rw [tail.program₂ i hi]
        exact treeStages_rerand_coin_entry K _ _ (verify₂ i hi) _ _ (nonzero₂ i hi) _ _)
    state a b related fresh

/-- A stopped honest party makes the actual peer exchange abort on both
sides, while retaining the complete rushing view and shared cache. -/
theorem treeStages_peer_partial_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel d.δ a b) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_peer_partial_factor K D A _ _ live stopped,
    treeSim_peer_partial_factor K D A _ _ live stopped,
    d.partial_view K D live]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b h)
  intro u z hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨by rw [hz.1], by rw [hz.1], rfl, rfl, hz.2⟩

/-- Rerand preservation from the exact optional boundary left by the final
multiplication. Prior honest aborts propagate; otherwise the first check Coin
uses the real tuples and continuation. -/
theorem TreeStagesRerandTail.coin_boundary_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (verify₁ : ∀ i, i ∉ D.1 → (tail.gadgets₁ i).verify = check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i)))
    (verify₂ : ∀ i, i ∉ D.1 → (tail.gadgets₂ i).verify = check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i)))
    (nonzero₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) (future : TreeSimFutureZero (tail.ρ + 1) d.δ)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧ TreeSimStreamRel d.δ u.2 z.2 ∧
        TreeSimFutureZero (tail.ρ + 2) d.δ ∧ TreeSimFutureEmpty (tail.ρ + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (tail.ρ + 2) z.2.2 ∧
        ((u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none)) ∨
          ∃ sent rnd,
            let n := tail.coinNext K D d keys verify₁ verify₂ nonzero₁ nonzero₂ sent
            u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
            u.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
            z.1.2.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂)) := by
  by_cases active : ∀ i, i ∉ D.1 → live i = true
  · have steps₁ : treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ =
        treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp only [treeSimPeerPartial, active i hi, if_true]
    have steps₂ : treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ =
        treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp only [treeSimPeerPartial, active i hi, if_true]
    rw [steps₁, steps₂]
    apply relTriple_post_mono (tail.coin_round prims K D A d keys verify₁ verify₂ nonzero₁ nonzero₂
      visible future state a b related fresh)
    intro u z h
    obtain ⟨sent, rnd, stateEq, sent₁, sent₂, steps₁, steps₂, caches, zero, empty₁, empty₂⟩ := h
    exact ⟨stateEq, sent₁.trans sent₂.symm, caches, zero, empty₁, empty₂,
      Or.inr ⟨sent, rnd, sent₁, sent₂, steps₁, steps₂⟩⟩
  · push_neg at active
    apply relTriple_post_mono (treeStages_peer_partial_round prims K D A d live active state a b related)
    intro u z h
    obtain ⟨stateEq, sentEq, steps₁, steps₂, caches, frame₁, frame₂⟩ := h
    refine ⟨stateEq, sentEq, caches, (fun x hx => future x (by omega)), ?_, ?_, Or.inl ⟨steps₁, steps₂⟩⟩
    · rw [frame₁]
      exact fun x hx => fresh x (by omega)
    · rw [frame₂]
      exact fun x hx => treeSim_futureEmpty_related fresh related.2 x (by omega)

/-- The final collector recipe for the frozen real gadgets and simulator. -/
def TreeStagesCollectorTail.actual (D : C.Coalition) (d : TreeSimCollectorData K D)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (layer : ℕ)
    (p₁ p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i, i ∉ D.1 → d.k₁ i =
      treeStagesAfterLayer K (realRunGadgets K (ctx₁ i) settings.mode)
        (jobs.map (circuits parameter ·.kind)) layer [] (p₁ i) (finish₁ i))
    (program₂ : ∀ i, i ∉ D.1 → d.k₂ i =
      treeStagesAfterLayer K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
        (jobs.map (circuits parameter ·.kind)) layer [] (p₂ i) (finish₂ i))
    (ρ : ℕ) (labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ)
    (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0)
    (zero : TreeSimFutureZero (ρ + 1) d.δ) : TreeStagesCollectorTail K D d where
  ctx₁ := ctx₁
  ctx₂ := ctx₂
  self₁ := self₁
  self₂ := self₂
  keys := keys
  gadgets₁ i := realRunGadgets K (ctx₁ i) settings.mode
  gadgets₂ i := treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  rerand₁ := by intros; rfl
  rerand₂ := by intros; rfl
  circs := jobs.map (circuits parameter ·.kind)
  layer := layer
  p₁ := p₁
  p₂ := p₂
  finish₁ := finish₁
  finish₂ := finish₂
  program₁ := by exact program₁
  program₂ := by exact program₂
  ρ := ρ
  labels := labels
  visible := visible
  zero := zero

  verify₁ := by intros; rfl
  verify₂ := by intros; rfl

/-- A concrete first-Coin boundary of the actual Rerand check, or a common
abort. The certificate retains its tuples and saved output continuation. -/
def TreeStagesCheckStart (D : C.Coalition) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (left right : C.Party → Step C E RealSpec TreeOutput) : Prop :=
  (left = (fun _ => .done none) ∧ right = (fun _ => .done none)) ∨
    ∃ (nonzero₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
      (nonzero₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
      (sent : C.Party → Mail C E) (rnd : C.Party → PrssOutput C E),
      let n := tail.coinNext K D d tail.keys tail.verify₁ tail.verify₂ nonzero₁ nonzero₂ sent
      left = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
      right = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂

/-- One actual driver step at Rerand, including its early stopping test.
An already aborted configuration makes no additional adversarial call. -/
theorem TreeStagesRerandTail.execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (nonzero : (outputsOf tail.circs).length ≠ 0)
    (future : TreeSimFutureZero (tail.ρ + 1) d.δ)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 1 state
        (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 1 state
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ TreeSimStreamRel d.δ u.2 z.2 ∧
        TreeSimFutureZero (tail.ρ + 2) d.δ ∧ TreeSimFutureEmpty (tail.ρ + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (tail.ρ + 2) z.2.2 ∧ TreeStagesCheckStart K D d tail u.1.2 z.1.2) := by
  by_cases stopped : ∀ i, i ∉ D.1 → live i ≠ true
  · have none₁ : treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp [treeSimPeerPartial, stopped i hi]
    have none₂ : treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp [treeSimPeerPartial, stopped i hi]
    rw [none₁, none₂]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, related, (fun x hx => future x (by omega)),
      (fun x hx => fresh x (by omega)),
      (fun x hx => treeSim_futureEmpty_related fresh related.2 x (by omega)), Or.inl ⟨rfl, rfl⟩⟩
  · push_neg at stopped
    obtain ⟨i, hi, hl⟩ := stopped
    have active₁ : ¬ AllDone D (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) := by
      intro done
      have h := done i hi
      simpa [treeSimPeerPartial, treeSimPeerWaiting, treeSimPeerStep, hi, hl] using h
    have active₂ : ¬ AllDone D (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
      intro done
      have h := done i hi
      simpa [treeSimPeerPartial, treeSimPeerWaiting, treeSimPeerStep, hi, hl] using h
    have nz₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0 := by
      intros; omega
    have nz₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0 := by
      intros; omega
    simp only [AllDone] at active₁ active₂
    simp only [executeSteps, if_neg active₁, if_neg active₂, StateT.run_bind]
    apply relTriple_bind (tail.coin_boundary_round prims K D A d tail.keys tail.verify₁ tail.verify₂
      nz₁ nz₂ tail.visible future live state a b related fresh)
    intro u z h
    obtain ⟨stateEq, _, caches, zero, fresh₁, fresh₂, aborted | ⟨sent, rnd, _, _, steps₁, steps₂⟩⟩ := h
    · exact relTriple_pure_pure ⟨stateEq, caches, zero, fresh₁, fresh₂, Or.inl aborted⟩
    · exact relTriple_pure_pure ⟨stateEq, caches, zero, fresh₁, fresh₂,
        Or.inr ⟨nz₁, nz₂, sent, rnd, steps₁, steps₂⟩⟩

/-- Two actual driver steps compose final collector forwarding, Rerand and
entry to the check. Both early stopping and selective aborts are retained;
there is no assumed coupling for either saved continuation. -/
theorem TreeStagesCollectorTail.execute_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (nonzero : (outputsOf tail.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2)
    (active : ¬ AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧
        ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next),
          rest.ρ = tail.ρ + 1 ∧ rest.circs = tail.circs ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureZero (tail.ρ + 3) next.δ ∧ TreeSimFutureEmpty (tail.ρ + 3) u.2.1.2 ∧
          TreeSimFutureEmpty (tail.ρ + 3) z.2.2 ∧ TreeStagesCheckStart K D next rest u.1.2 z.1.2) := by
  have active₂ : ¬ AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent) := by
    intro done
    apply active
    intro i hi
    rw [treeSim_collector_afterFirst_done K D d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ sent]
    exact done i hi
  simp only [AllDone] at active active₂
  rw [executeSteps, if_neg active, executeSteps, if_neg active₂]
  simp only [StateT.run_bind]
  apply relTriple_bind (tail.round prims K D A state d sent a b related fresh)
  intro u z h
  obtain ⟨same, _, next, rest, live, label, circs, caches, empty₁, _, zero, steps₁, steps₂⟩ := h
  rw [← same, steps₁, steps₂]
  have nz : (outputsOf rest.circs).length ≠ 0 := by simpa only [circs] using nonzero
  apply relTriple_post_mono (rest.execute prims K D A next nz zero live u.1.1 u.2 z.2 caches empty₁)
  intro u' z' h'
  obtain ⟨same', caches', zero', empty₁', empty₂', nextSteps⟩ := h'
  refine ⟨same', next, rest, label, circs, caches', ?_, ?_, ?_, nextSteps⟩
  · simpa only [label, Nat.add_assoc] using zero'
  · simpa only [label, Nat.add_assoc] using empty₁'
  · simpa only [label, Nat.add_assoc] using empty₂'

/-- At a stopped forwarding boundary, every actual collector step is an
abort; no successful ceremony output is hidden by the driver's stopping test. -/
theorem treeStages_collector_done_none (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (sent : C.Party → Mail C E) (done : AllDone D (treeSimCollectorAfterFirst K D count rnd v st k sent)) :
    treeSimCollectorAfterFirst K D count rnd v st k sent = fun _ => .done none := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCollectorAfterFirst, hi]
  · have h := done i hi
    by_cases hab : anyAbort (colInbox K D count rnd v sent i) = true <;>
      simp [treeSimCollectorAfterFirst, hi, hab] at h ⊢

/-- Final collector completion is either common abort or the actual first
check Coin after peer Rerand, with all later labels fresh. -/
def TreeStagesCollectorCheckResult (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  a.1.1 = b.1.1 ∧
    ((a.1.2 = (fun _ => .done none) ∧ b.1.2 = (fun _ => .done none) ∧ TreeSimStreamRel d.δ a.2 b.2) ∨
      ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next),
        rest.ρ = tail.ρ + 1 ∧ rest.circs = tail.circs ∧ TreeSimStreamRel next.δ a.2 b.2 ∧
        TreeSimFutureZero (tail.ρ + 3) next.δ ∧ TreeSimFutureEmpty (tail.ρ + 3) a.2.1.2 ∧
        TreeSimFutureEmpty (tail.ρ + 3) b.2.2 ∧ TreeStagesCheckStart K D next rest a.1.2 b.1.2)

/-- Forwarding-to-check simulation also covers the early-stop branch. -/
theorem TreeStagesCollectorTail.execute_check_all (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (nonzero : (outputsOf tail.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (TreeStagesCollectorCheckResult K D A d tail) := by
  by_cases done : AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)
  · have done₂ : AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent) := by
      intro i hi
      rw [← treeSim_collector_afterFirst_done K D d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ sent]
      exact done i hi
    rw [treeStages_collector_done_none K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent done,
      treeStages_collector_done_none K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent done₂]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, Or.inl ⟨rfl, rfl, related⟩⟩
  · apply relTriple_post_mono (tail.execute_check prims K D A state d nonzero sent a b related fresh done)
    intro u z h
    exact ⟨h.1, Or.inr h.2⟩

/-- The entire actual final collector gadget and Rerand reach the first
check Coin in three driver rounds, including all early and selective aborts. -/
theorem TreeStagesCollectorTail.execute_three (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (tail : TreeStagesCollectorTail K D d)
    (nonzero : (outputsOf tail.circs).length ≠ 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 3 state
        (treeSimCollectorWaiting K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 3 state
        (treeSimCollectorWaiting K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (TreeStagesCollectorCheckResult K D A d tail) := by
  have active : ∀ rnd v st k, ¬ AllDone D (treeSimCollectorWaiting (α := TreeOutput) K D d.count rnd v st k) := by
    intro rnd v st k done
    obtain ⟨i, hi⟩ := exists_honest D
    have h := done i hi
    simp [treeSimCollectorWaiting, treeSimCollectorStep, hi] at h
  have active₁ := active d.rnd₁ d.v₁ d.st₁ d.k₁
  have active₂ := active d.rnd₂ d.v₂ d.st₂ d.k₂
  simp only [AllDone] at active₁ active₂
  rw [executeSteps, if_neg active₁, executeSteps, if_neg active₂]
  simp only [StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
  have coupled := treeSim_collector_first_mixed prims K D A state d.δ d.count
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a b related
  simp only [simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles] at coupled
  apply relTriple_bind coupled
  intro u z h
  obtain ⟨same, sentEq, steps₁, steps₂, caches, frame₁, _⟩ := h
  rw [← same, steps₁, steps₂]
  apply tail.execute_check_all prims K D A u.1.1 d nonzero u.1.2.2 u.2 z.2 caches
  simpa only [frame₁] using fresh

/-- The actual remaining collector layer schedule and its complete Rerand,
check and output continuation. No transition coupling is a field. -/
structure TreeStagesCollectorSchedule (D : C.Coalition) (d : TreeSimCollectorData K D) where
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  gadgets₁ : C.Party → RunGadgets C E RealSpec
  gadgets₂ : C.Party → RunGadgets C E RealSpec
  mult₁ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₁ i).mult x y count = (do
    let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
    reshareCollector K (ctx₁ i) rnd (mulRep K (ctx₁ i) x y) count)
  mult₂ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₂ i).mult x y count = (do
    let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
    reshareCollector K (ctx₂ i) rnd (mulRep K (ctx₂ i) x y) count)
  circs : List Circuit
  layer : ℕ
  rest : List ℕ
  p₁ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  finish₁ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → d.k₁ i =
    treeStagesAfterLayer K (gadgets₁ i) circs layer rest (p₁ i) (finish₁ i)
  program₂ : ∀ i, i ∉ D.1 → d.k₂ i =
    treeStagesAfterLayer K (gadgets₂ i) circs layer rest (p₂ i) (finish₂ i)
  ρ : ℕ
  labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ
  visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0
  zero : TreeSimFutureZero (ρ + 1) d.δ

  rerand₁ : ∀ i, i ∉ D.1 → ∀ v count, (gadgets₁ i).rerand v count = (do
    let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
    reshare K (ctx₁ i) bitCodec rnd (ownerSum K (ctx₁ i) v) count)
  rerand₂ : ∀ i, i ∉ D.1 → ∀ v count, (gadgets₂ i).rerand v count = (do
    let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
    reshare K (ctx₂ i) bitCodec rnd (ownerSum K (ctx₂ i) v) count)
  verify₁ : ∀ i, i ∉ D.1 → (gadgets₁ i).verify = check K (ctx₁ i) (realCheckGadgets K (ctx₁ i))
  verify₂ : ∀ i, i ∉ D.1 → (gadgets₂ i).verify = check K (ctx₂ i) (realCheckGadgets K (ctx₂ i))

/-- The empty remaining schedule is exactly the final collector recipe. -/
def TreeStagesCollectorSchedule.last (D : C.Coalition) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (empty : s.rest = []) : TreeStagesCollectorTail K D d where
  ctx₁ := s.ctx₁
  ctx₂ := s.ctx₂
  self₁ := s.self₁
  self₂ := s.self₂
  keys := s.keys
  gadgets₁ := s.gadgets₁
  gadgets₂ := s.gadgets₂
  rerand₁ := s.rerand₁
  rerand₂ := s.rerand₂
  circs := s.circs
  layer := s.layer
  p₁ := s.p₁
  p₂ := s.p₂
  finish₁ := s.finish₁
  finish₂ := s.finish₂
  program₁ := by intro i hi; simpa only [empty] using s.program₁ i hi
  program₂ := by intro i hi; simpa only [empty] using s.program₂ i hi
  ρ := s.ρ
  labels := s.labels
  visible := s.visible
  zero := s.zero
  verify₁ := s.verify₁
  verify₂ := s.verify₂

/-- Advance the saved layer schedule using the actual optional collector
outputs. The successor is available even when it is the final layer. -/
theorem TreeStagesCollectorSchedule.next (D : C.Coalition) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (nextLayer : ℕ) (remaining : List ℕ)
    (rest_eq : s.rest = nextLayer :: remaining) (initial : HiddenCache C)
    (fresh : TreeSimFutureEmpty (s.ρ + 1) initial) (sent sent' : C.Party → Mail C E) :
    let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
    let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
    ∃ n : TreeSimCollectorNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = s.ρ + 1 ∧ n.idx = 0 ∧ n.count = (gatesAt s.circs nextLayer).length ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesCollectorSchedule K D (n.data K rnd₁ rnd₂ masks),
          successor.ρ = n.ρ ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_collector_exit_values K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states sent sent'
  let nextP₁ := fun i => (appendLayer s.circs s.layer (s.p₁ i).1 (x₁ i).1,
    (s.p₁ i).2 ++ [⟨layerX K s.circs s.layer (s.p₁ i).1, layerY K s.circs s.layer (s.p₁ i).1,
      (x₁ i).1, (gatesAt s.circs s.layer).length, (s.gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer s.circs s.layer (s.p₂ i).1 (x₂ i).1,
    (s.p₂ i).2 ++ [⟨layerX K s.circs s.layer (s.p₂ i).1, layerY K s.circs s.layer (s.p₂ i).1,
      (x₂ i).1, (gatesAt s.circs s.layer).length, (s.gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := d.T₀, lacked := d.lacked, ctx₁ := s.ctx₁, ctx₂ := s.ctx₂
    self₁ := s.self₁, self₂ := s.self₂, keys := s.keys
    ρ := s.ρ + 1, idx := 0, count := (gatesAt s.circs nextLayer).length
    v₁ := fun i => mulRep K (s.ctx₁ i) (layerX K s.circs nextLayer (nextP₁ i).1) (layerY K s.circs nextLayer (nextP₁ i).1)
    v₂ := fun i => mulRep K (s.ctx₂ i) (layerX K s.circs nextLayer (nextP₂ i).1) (layerY K s.circs nextLayer (nextP₂ i).1)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (s.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (s.labels i hi)))
    next₁ := fun i => treeStagesAfterLayer K (s.gadgets₁ i) s.circs nextLayer remaining (nextP₁ i) (s.finish₁ i)
    next₂ := fun i => treeStagesAfterLayer K (s.gadgets₂ i) s.circs nextLayer remaining (nextP₂ i) (s.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppendMode K .collector d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).1.2
    visible := s.visible, futureZero := s.zero, futureEmpty := fresh
  }, rfl, rfl, rfl, ?_⟩
  · intro i hi _
    rw [s.program₁ i hi, rest_eq]
    exact treeStages_layers_collector K (s.ctx₁ i) (s.gadgets₁ i) (s.mult₁ i hi)
      s.circs nextLayer remaining (nextP₁ i) (x₁ i).2 (s.finish₁ i)
  · intro i hi _
    rw [s.program₂ i hi, rest_eq]
    exact treeStages_layers_collector K (s.ctx₂ i) (s.gadgets₂ i) (s.mult₂ i hi)
      s.circs nextLayer remaining (nextP₂ i) (x₂ i).2 (s.finish₂ i)

  · intro rnd₁ rnd₂ masks zeroNext
    refine ⟨{
      ctx₁ := s.ctx₁, ctx₂ := s.ctx₂, self₁ := s.self₁, self₂ := s.self₂, keys := s.keys
      gadgets₁ := s.gadgets₁, gadgets₂ := s.gadgets₂, mult₁ := s.mult₁, mult₂ := s.mult₂
      circs := s.circs, layer := nextLayer, rest := remaining
      p₁ := nextP₁, p₂ := nextP₂, finish₁ := s.finish₁, finish₂ := s.finish₂
      program₁ := by intros; rfl
      program₂ := by intros; rfl
      ρ := s.ρ + 1
      labels := fun i hi => (exits i hi).2.1.trans (congrArg (· + 1) (s.labels i hi))
      visible := ?_, zero := zeroNext
      rerand₁ := s.rerand₁, rerand₂ := s.rerand₂, verify₁ := s.verify₁, verify₂ := s.verify₂
    }, rfl, rfl, rfl, rfl⟩
    intro x hx
    change (d.δ + treeSimCollectorShift K D d.T₀ (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _) x = 0
    simp only [Pi.add_apply, s.visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D (s.ρ + 1) 0 (gatesAt s.circs nextLayer).length _ _ x hx, add_zero]

/-- Collector forwarding preserves the entire remaining layer schedule,
including the last layer's Rerand and check code. -/
theorem TreeStagesCollectorSchedule.round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d)
    (nextLayer : ℕ) (remaining : List ℕ) (rest_eq : s.rest = nextLayer :: remaining)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimCollectorData K D) (successor : TreeStagesCollectorSchedule K D next)
          (live : C.Party → Bool),
          successor.ρ = s.ρ + 1 ∧ successor.circs = s.circs ∧ successor.layer = nextLayer ∧
          successor.rest = remaining ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (successor.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (successor.ρ + 1) z.2.2 ∧
          u.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimCollectorPartial K D live next.count next.rnd₂ next.v₂ next.st₂ next.k₂) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles,
    treeSim_collector_second_factor, simulateQ_bind, StateT.run_bind]
  have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).2.1 sent
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, _, _, after⟩ := s.next K D d nextLayer remaining rest_eq a.1.2 fresh sent u.1.2
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D A u.1.1 d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨_, _, empty₁, empty₂, zero, rnd₁, rnd₂, masks, steps₁, steps₂, boundary⟩ := h'
  obtain ⟨successor, nextLabel, info⟩ := after rnd₁ rnd₂ masks zero
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, successor, n.live, nextLabel.trans label,
    info.1, info.2.1, info.2.2, boundary.2.1, ?_, ?_, steps₁, steps₂⟩
  · simpa only [nextLabel] using empty₁
  · simpa only [nextLabel] using empty₂

/-- A stopped party at collector entry either stops the driver immediately
or propagates its abort in one real round. All remaining fuel is inert. -/
theorem treeStages_collector_partial_execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimCollectorData K D)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true)
    (fuel : ℕ) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none) ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  by_cases inactive : ∀ i, i ∉ D.1 → live i ≠ true
  · have none₁ : treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
      · simp [treeSimCollectorPartial, inactive i hi]
    have none₂ : treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
      · simp [treeSimCollectorPartial, inactive i hi]
    rw [none₁, none₂]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, rfl, related, rfl, rfl⟩
  · push_neg at inactive
    obtain ⟨i, hi, hl⟩ := inactive
    have active₁ : ¬ AllDone D (treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) := by
      intro done
      have h := done i hi
      simp [treeSimCollectorPartial, treeSimCollectorWaiting, treeSimCollectorStep, hi, hl] at h
    have active₂ : ¬ AllDone D (treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
      intro done
      have h := done i hi
      simp [treeSimCollectorPartial, treeSimCollectorWaiting, treeSimCollectorStep, hi, hl] at h
    simp only [AllDone] at active₁ active₂
    rw [executeSteps, if_neg active₁, executeSteps, if_neg active₂]
    simp only [StateT.run_bind]
    have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
    have coupled := treeSim_collector_partial_mixed prims K D A state live stopped d.δ d.count
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a b related
    simp only [simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles] at coupled
    apply relTriple_bind coupled
    intro u z h
    obtain ⟨same, _, steps₁, steps₂, caches, frame₁, frame₂⟩ := h
    rw [steps₁, steps₂, executeSteps_done _ D A noFunctionality fuel _ _ (by intros; trivial),
      executeSteps_done _ D A noFunctionality fuel _ _ (by intros; trivial)]
    exact relTriple_pure_pure ⟨same, rfl, rfl, caches, frame₁, frame₂⟩

/-- A finished collector schedule retains the actual first check Coin or
common abort, together with the adaptive cache relation and saved caller. -/
def TreeStagesCheckReached (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (circs : List Circuit) (label : ℕ)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  a.1.1 = b.1.1 ∧ ∃ δ, TreeSimStreamRel δ a.2 b.2 ∧
    (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
    ((a.1.2 = (fun _ => .done none) ∧ b.1.2 = (fun _ => .done none)) ∨
      ∃ (d : TreeSimPeerData K D) (tail : TreeStagesRerandTail K D d),
        d.δ = δ ∧ tail.ρ = label ∧ tail.circs = circs ∧ TreeSimFutureZero (label + 2) δ ∧
        TreeSimFutureEmpty (label + 2) a.2.1.2 ∧ TreeSimFutureEmpty (label + 2) b.2.2 ∧
        TreeStagesCheckStart K D d tail a.1.2 b.1.2)

theorem treeStages_collector_partial_live (D : C.Coalition) (live : C.Party → Bool)
    (active : ∀ i, i ∉ D.1 → live i = true) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeSimCollectorPartial K D live count rnd v st k = treeSimCollectorWaiting K D count rnd v st k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
  · simp only [treeSimCollectorPartial, active i hi, if_true]

/-- A prior abort closes any remaining collector schedule in its actual
fuel budget; the adapted hidden-cache translation is retained. -/
theorem TreeStagesCollectorSchedule.abort (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (fuel label : ℕ)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (TreeStagesCheckReached K D A s.circs label) := by
  apply relTriple_post_mono (treeStages_collector_partial_execute prims K D A d live stopped fuel state a b related)
  intro u z h
  exact ⟨h.1, d.δ, h.2.2.2.1, s.visible, Or.inl ⟨h.2.1, h.2.2.1⟩⟩

/-- The empty remaining layer schedule executes its real final collector,
Rerand and first check Coin, also when an earlier party already aborted. -/
theorem TreeStagesCollectorSchedule.execute_last (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimCollectorData K D)
    (s : TreeStagesCollectorSchedule K D d) (empty : s.rest = [])
    (nonzero : (outputsOf s.circs).length ≠ 0)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 3 state
        (treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 3 state
        (treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (TreeStagesCheckReached K D A s.circs (s.ρ + 1)) := by
  by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
  · exact s.abort prims K D A d live stopped 2 (s.ρ + 1) state a b related
  · have active : ∀ i, i ∉ D.1 → live i = true := by
      intro i hi
      by_contra hl
      exact stopped ⟨i, hi, hl⟩
    rw [treeStages_collector_partial_live K D live active, treeStages_collector_partial_live K D live active]
    apply relTriple_post_mono ((s.last K D d empty).execute_three prims K D A state d nonzero a b related fresh)
    intro u z h
    obtain ⟨same, aborted | ⟨next, tail, label, circs, caches, zero, empty₁, empty₂, start⟩⟩ := h
    · exact ⟨same, d.δ, aborted.2.2, s.visible, Or.inl ⟨aborted.1, aborted.2.1⟩⟩
    · refine ⟨same, next.δ, caches, tail.visible, Or.inr ⟨next, tail, rfl, label, circs, ?_, ?_, ?_, start⟩⟩
      · simpa only [TreeStagesCollectorSchedule.last, Nat.add_assoc, Nat.reduceAdd] using zero
      · simpa only [TreeStagesCollectorSchedule.last, Nat.add_assoc, Nat.reduceAdd] using empty₁
      · simpa only [TreeStagesCollectorSchedule.last, Nat.add_assoc, Nat.reduceAdd] using empty₂

/-- All actual collector layers, their two exchanges and fresh PRSS masks,
followed by peer Rerand and the check's first Coin. The exact driver consumes
at most two rounds per layer plus Rerand, and preserves its early-stop test. -/
theorem TreeStagesCollectorSchedule.execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (layers : List ℕ)
    (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d)
    (scheduled : s.rest = layers) (nonzero : (outputsOf s.circs).length ≠ 0)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * layers.length + 3) state
        (treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * layers.length + 3) state
        (treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (TreeStagesCheckReached K D A s.circs (s.ρ + layers.length + 1)) := by
  induction layers generalizing d state a b live with
  | nil => exact s.execute_last prims K D A d scheduled nonzero live state a b related fresh
  | cons nextLayer remaining ih =>
    by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
    · exact s.abort prims K D A d live stopped (2 * (nextLayer :: remaining).length + 2)
        (s.ρ + (nextLayer :: remaining).length + 1) state a b related
    · have active : ∀ i, i ∉ D.1 → live i = true := by
        intro i hi
        by_contra hl
        exact stopped ⟨i, hi, hl⟩
      rw [treeStages_collector_partial_live K D live active, treeStages_collector_partial_live K D live active]
      have ready : ∀ rnd v st k, ¬ AllDone D (treeSimCollectorWaiting (α := TreeOutput) K D d.count rnd v st k) := by
        intro rnd v st k done
        obtain ⟨i, hi⟩ := exists_honest D
        have h := done i hi
        simp [treeSimCollectorWaiting, treeSimCollectorStep, hi] at h
      have ready₁ := ready d.rnd₁ d.v₁ d.st₁ d.k₁
      have ready₂ := ready d.rnd₂ d.v₂ d.st₂ d.k₂
      have fuel : 2 * (nextLayer :: remaining).length + 3 = (2 * remaining.length + 3) + 1 + 1 := by
        simp only [List.length_cons]; omega
      simp only [AllDone] at ready₁ ready₂
      rw [fuel, executeSteps, if_neg ready₁, executeSteps, if_neg ready₂]
      simp only [StateT.run_bind]
      have view := (treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
        d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states).1
      have coupled := treeSim_collector_first_mixed prims K D A state d.δ d.count
        d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ view a b related
      simp only [simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles] at coupled
      apply relTriple_bind coupled
      intro u z h
      obtain ⟨same, _, steps₁, steps₂, caches, frame₁, _⟩ := h
      rw [← same, steps₁, steps₂]
      have fresh' : TreeSimFutureEmpty (s.ρ + 1) u.2.1.2 := by simpa only [frame₁] using fresh
      by_cases done : AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ u.1.2.2)
      · have done₂ : AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ u.1.2.2) := by
          intro i hi
          rw [← treeSim_collector_afterFirst_done K D d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂]
          exact done i hi
        rw [treeStages_collector_done_none K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ _ done,
          treeStages_collector_done_none K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ _ done₂]
        simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
        exact relTriple_pure_pure ⟨rfl, d.δ, caches, s.visible, Or.inl ⟨rfl, rfl⟩⟩
      · have active₂ : ¬ AllDone D (treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ u.1.2.2) := by
          intro h
          apply done
          intro i hi
          rw [treeSim_collector_afterFirst_done K D d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂]
          exact h i hi
        simp only [AllDone] at done active₂
        rw [executeSteps, if_neg done, executeSteps, if_neg active₂]
        simp only [StateT.run_bind]
        apply relTriple_bind (s.round prims K D A u.1.1 d nextLayer remaining scheduled u.1.2.2 u.2 z.2 caches fresh')
        intro u' z' h'
        obtain ⟨same', _, next, successor, nextLive, label, circs, _, rest, caches', empty₁, _, next₁, next₂⟩ := h'
        rw [← same', next₁, next₂]
        have nz : (outputsOf successor.circs).length ≠ 0 := by simpa only [circs] using nonzero
        have labels : successor.ρ + remaining.length + 1 = s.ρ + (nextLayer :: remaining).length + 1 := by
          rw [label]; simp only [List.length_cons]; omega
        apply relTriple_post_mono (ih next successor rest nz nextLive u'.1.1 u'.2 z'.2 caches' empty₁)
        intro u'' z'' h''
        simpa only [circs, labels] using h''

/-- The actual batch program is the retained layer fold with no prior tuples. -/
theorem treeStages_runJobs_layers (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (inputs : List (C.Term → List Bit)) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    (runJobs K gadgets circs inputs).run st >>= finish =
      treeStagesLayers K gadgets circs (List.range (depth circs)) (inputs, []) st finish := by
  rw [runJobs_eq]
  rfl

/-- For the real collector-mode gadgets and simulator override, the entire
nonempty AND-layer fold starts with actual PRSS draws and reaches the check.
The saved batch caller and both honest input vectors are retained exactly. -/
theorem treeStages_collector_runJobs (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (mode : settings.mode = .collector) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (layer : ℕ) (remaining : List ℕ)
    (schedule : List.range (depth (jobs.map (circuits parameter ·.kind))) = layer :: remaining)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (inputs₁ inputs₂ : C.Party → List (C.Term → List Bit)) (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs (inputs₁ i)).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * remaining.length + 3) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs (inputs₂ i)).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * remaining.length + 3) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + remaining.length + 1)) := by
  intro circs
  let gadgets₁ : C.Party → RunGadgets C E RealSpec := fun i => realRunGadgets K (ctx₁ i) settings.mode
  let gadgets₂ := fun i => treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  have mult₁ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₁ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
      reshareCollector K (ctx₁ i) rnd (mulRep K (ctx₁ i) x y) count) := by
    intro i hi x y count
    change (prssRandomness (ctx₁ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₁ i) settings.mode rnd (mulRep K (ctx₁ i) x y) count) = _
    rw [mode]; rfl
  have mult₂ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₂ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
      reshareCollector K (ctx₂ i) rnd (mulRep K (ctx₂ i) x y) count) := by
    intro i hi x y count
    change (prssRandomness (ctx₂ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₂ i) settings.mode rnd (mulRep K (ctx₂ i) x y) count) = _
    rw [mode]; rfl
  let k₁ := fun i (_ : Shares C Bit × RunState C) =>
    treeStagesLayers K (gadgets₁ i) circs (layer :: remaining) (inputs₁ i, []) (st₁ i) (finish₁ i)
  let k₂ := fun i (_ : Shares C Bit × RunState C) =>
    treeStagesLayers K (gadgets₂ i) circs (layer :: remaining) (inputs₂ i, []) (st₂ i) (finish₂ i)
  let x₁ := fun i => ((0, st₁ i) : Shares C Bit × RunState C)
  let x₂ := fun i => ((0, st₂ i) : Shares C Bit × RunState C)
  let out₁ := fun i => if i ∈ D.1 then none else some (x₁ i)
  let out₂ := fun i => if i ∈ D.1 then none else some (x₂ i)
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let n : TreeSimCollectorNext K D past a.1.2 k₁ k₂ out₁ out₂ := {
    T₀ := T₀, lacked := pivot.1
    ctx₁ := ctx₁, ctx₂ := ctx₂, self₁ := self₁, self₂ := self₂, keys := keys
    ρ := ρ, idx := 0, count := (gatesAt circs layer).length
    v₁ := fun i => mulRep K (ctx₁ i) (layerX K circs layer (inputs₁ i)) (layerY K circs layer (inputs₁ i))
    v₂ := fun i => mulRep K (ctx₂ i) (layerX K circs layer (inputs₂ i)) (layerY K circs layer (inputs₂ i))
    st₁ := st₁, st₂ := st₂, lab₁ := labels
    lab₂ := fun i hi => (states i hi).1.symm.trans (labels i hi)
    next₁ := fun i => treeStagesAfterLayer K (gadgets₁ i) circs layer remaining (inputs₁ i, []) (finish₁ i)
    next₂ := fun i => treeStagesAfterLayer K (gadgets₂ i) circs layer remaining (inputs₂ i, []) (finish₂ i)
    x₁ := x₁, x₂ := x₂, live := fun _ => true
    shape₁ := by intros; rfl
    shape₂ := by intros; rfl
    program₁ := by intro i hi _; exact treeStages_layers_collector K _ _ (mult₁ i hi) _ _ _ _ _ _
    program₂ := by intro i hi _; exact treeStages_layers_collector K _ _ (mult₂ i hi) _ _ _ _ _ _
    history := history, states := states, visible := visible, futureZero := zero, futureEmpty := fresh }
  have starts₁ := treeSim_resumeAll_start (C := C) (E := E) D k₁ out₁ x₁
    (by intro i hi; simp [out₁, hi]) (by intro i hi; simp [out₁, hi])
  have starts₂ := treeSim_resumeAll_start (C := C) (E := E) D k₂ out₂ x₂
    (by intro i hi; simp [out₂, hi]) (by intro i hi; simp [out₂, hi])
  have schedule' : List.range (depth circs) = layer :: remaining := schedule
  simp only [treeStages_runJobs_layers, schedule', StateT.run_bind]
  change RelTriple
    (((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => k₁ i (x₁ i)))).run a) >>= _) 
    (((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => k₂ i (x₂ i)))).run b) >>= _) _
  rw [← starts₁, ← starts₂]
  apply relTriple_bind (n.coupling prims K D A state past a.1.2 k₁ k₂ out₁ out₂ a b related rfl)
  intro u z h
  obtain ⟨_, _, empty₁, _, zeroNext, rnd₁, rnd₂, masks, steps₁, steps₂, boundary⟩ := h
  let d := n.data K rnd₁ rnd₂ masks
  let s : TreeStagesCollectorSchedule K D d := {
    ctx₁ := ctx₁, ctx₂ := ctx₂, self₁ := self₁, self₂ := self₂, keys := keys
    gadgets₁ := gadgets₁, gadgets₂ := gadgets₂, mult₁ := mult₁, mult₂ := mult₂
    circs := circs, layer := layer, rest := remaining
    p₁ := fun i => (inputs₁ i, []), p₂ := fun i => (inputs₂ i, [])
    finish₁ := finish₁, finish₂ := finish₂
    program₁ := by intros; rfl
    program₂ := by intros; rfl
    ρ := ρ, labels := labels, zero := zeroNext
    visible := by
      intro x hx
      change (past + treeSimCollectorShift K D T₀ ρ 0 (gatesAt circs layer).length _) x = 0
      simp only [Pi.add_apply, visible x hx, treeSimCollectorShift,
        treeSim_blockShift_visible D ρ 0 (gatesAt circs layer).length _ _ x hx, add_zero]
    rerand₁ := by intros; rfl
    rerand₂ := by intros; rfl
    verify₁ := by intros; rfl
    verify₂ := by intros; rfl }
  rw [steps₁, steps₂]
  exact s.execute prims K D A remaining d rfl nonzero n.live state u.2 z.2 boundary.2.1 empty₁

/-- A batch without AND layers still performs its actual peer Rerand and
check in either mode, retaining the simulator output override and caller. -/
theorem treeStages_zeroDepth_runJobs (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (schedule : List.range (depth (jobs.map (circuits parameter ·.kind))) = [])
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (inputs₁ inputs₂ : C.Party → List (C.Term → List Bit)) (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs (inputs₁ i)).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality 1 state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs (inputs₂ i)).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality 1 state steps).run b)
      (TreeStagesCheckReached K D A circs ρ) := by
  intro circs
  let gadgets₁ : C.Party → RunGadgets C E RealSpec := fun i => realRunGadgets K (ctx₁ i) settings.mode
  let gadgets₂ := fun i => treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  let k₁ := fun i (_ : Shares C Bit × RunState C) =>
    treeStagesLayers K (gadgets₁ i) circs [] (inputs₁ i, []) (st₁ i) (finish₁ i)
  let k₂ := fun i (_ : Shares C Bit × RunState C) =>
    treeStagesLayers K (gadgets₂ i) circs [] (inputs₂ i, []) (st₂ i) (finish₂ i)
  let x₁ := fun i => ((0, st₁ i) : Shares C Bit × RunState C)
  let x₂ := fun i => ((0, st₂ i) : Shares C Bit × RunState C)
  let out₁ := fun i => if i ∈ D.1 then none else some (x₁ i)
  let out₂ := fun i => if i ∈ D.1 then none else some (x₂ i)
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let n : TreeStagesPeerNext K D past a.1.2 k₁ k₂ out₁ out₂ := {
    T₀ := T₀, pivotParty := pivotParty, pivot := pivot
    ctx₁ := ctx₁, ctx₂ := ctx₂, self₁ := self₁, self₂ := self₂, keys := keys
    ρ := ρ, count := (outputsOf circs).length
    v₁ := fun i => ownerSum K (ctx₁ i) (outputShares K circs (inputs₁ i))
    v₂ := fun i => ownerSum K (ctx₂ i) (outputShares K circs (inputs₂ i))
    st₁ := st₁, st₂ := st₂, lab₁ := labels
    lab₂ := fun i hi => (states i hi).1.symm.trans (labels i hi)
    next₁ := fun i => treeStagesAfterRerand K (gadgets₁ i) circs (inputs₁ i, []) (finish₁ i)
    next₂ := fun i => treeStagesAfterRerand K (gadgets₂ i) circs (inputs₂ i, []) (finish₂ i)
    x₁ := x₁, x₂ := x₂, live := fun _ => true
    shape₁ := by intros; rfl
    shape₂ := by intros; rfl
    program₁ := by intro i hi _; exact treeStages_layers_rerand K _ _ (by intros; rfl) _ _ _ _
    program₂ := by intro i hi _; exact treeStages_layers_rerand K _ _ (by intros; rfl) _ _ _ _
    history := history, states := states, visible := visible, futureZero := zero, futureEmpty := fresh }
  have starts₁ := treeSim_resumeAll_start (C := C) (E := E) D k₁ out₁ x₁
    (by intro i hi; simp [out₁, hi]) (by intro i hi; simp [out₁, hi])
  have starts₂ := treeSim_resumeAll_start (C := C) (E := E) D k₂ out₂ x₂
    (by intro i hi; simp [out₂, hi]) (by intro i hi; simp [out₂, hi])
  have schedule' : List.range (depth circs) = [] := schedule
  simp only [treeStages_runJobs_layers, schedule', StateT.run_bind]
  change RelTriple
    (((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => k₁ i (x₁ i)))).run a) >>= _)
    (((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => k₂ i (x₂ i)))).run b) >>= _) _
  rw [← starts₁, ← starts₂]
  apply relTriple_bind (n.coupling prims K D past a.1.2 k₁ k₂ out₁ out₂ a b related rfl)
  intro u z h
  obtain ⟨caches, empty₁, _, zeroNext, rnd₁, rnd₂, masks, steps₁, steps₂⟩ := h
  let d := n.data K rnd₁ rnd₂ masks
  let tail : TreeStagesRerandTail K D d := {
    gadgets₁ := gadgets₁, gadgets₂ := gadgets₂, circs := circs, count := rfl
    p₁ := fun i => (inputs₁ i, []), p₂ := fun i => (inputs₂ i, [])
    finish₁ := finish₁, finish₂ := finish₂
    program₁ := by intros; rfl
    program₂ := by intros; rfl
    ρ := ρ, labels := labels, keys := keys
    verify₁ := by intros; rfl
    verify₂ := by intros; rfl
    visible := by
      intro x hx
      change (past + treeSimPeerShift K D T₀ pivotParty ρ 0 (outputsOf circs).length _ 0) x = 0
      simp only [Pi.add_apply, visible x hx, treeSimPeerShift,
        treeSim_blockShift_visible D ρ 0 (outputsOf circs).length _ _ x hx, add_zero] }
  rw [steps₁, steps₂]
  apply relTriple_post_mono (tail.execute prims K D A d nonzero zeroNext n.live state u.2 z.2 caches empty₁)
  intro u' z' h'
  obtain ⟨same, caches', zero', empty₁', empty₂', start⟩ := h'
  exact ⟨same, d.δ, caches', tail.visible,
    Or.inr ⟨d, tail, rfl, rfl, rfl, zero', empty₁', empty₂', start⟩⟩

/-- Every actual collector-mode batch with a nonempty output vector reaches
its first check Coin or common abort after at most `2 * depth + 1` rounds.
This includes zero-depth batches and preserves the real saved ceremony code. -/
theorem treeStages_collector_runJobs_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (mode : settings.mode = .collector) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (inputs₁ inputs₂ : C.Party → List (C.Term → List Bit)) (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs (inputs₁ i)).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * depth circs + 1) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs (inputs₂ i)).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * depth circs + 1) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + depth circs)) := by
  intro circs
  generalize schedule : List.range (depth circs) = layers
  cases layers with
  | nil =>
    have size : depth circs = 0 := by
      have h := congrArg List.length schedule
      simpa only [List.length_range, List.length_nil] using h
    rw [size]
    simpa only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
      treeStages_zeroDepth_runJobs prims K circuits settings D A state ctx₁ ctx₂ self₁ self₂ keys
        parameter openings batch jobs schedule nonzero inputs₁ inputs₂ st₁ st₂ finish₁ finish₂
        ρ labels history states past visible zero a b related fresh
  | cons layer remaining =>
    have size : depth circs = remaining.length + 1 := by
      have h := congrArg List.length schedule
      simpa only [List.length_range, List.length_cons] using h
    have fuel : 2 * depth circs + 1 = 2 * remaining.length + 3 := by omega
    have label : ρ + depth circs = ρ + remaining.length + 1 := by omega
    rw [fuel, label]
    exact treeStages_collector_runJobs prims K circuits settings D A state mode ctx₁ ctx₂ self₁ self₂ keys
      parameter openings batch jobs layer remaining schedule nonzero inputs₁ inputs₂ st₁ st₂ finish₁ finish₂
      ρ labels history states past visible zero a b related fresh

/-- Once the fixed event is logged, the actual setup and every continuation
retain it. This constructs a full round core without any invariant premise. -/
def treeStages_badCore (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (bad : TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z s.2) :
    TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z dealt state s
      (fun t => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2) where
  Inv _ _ := False
  stage _ := .ceremony
  entry p hp := by
    have hpref : s.2 <+: p.2.2 := by
      apply treeSimLoggedWorld_prefix prims D
        (executePhase worldRoles D A noFunctionality 3 state
          (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))) s p
      simpa only [simulateQ_executePhase, treeSimRealRoles] using hp
    apply relTriple_of_support_left
    intro a ha b
    apply Or.inl
    exact treeSimBad_mono prims K circuits settings top tree D A _ z
      (hpref.trans (treeSimLoggedWorld_prefix prims D _ p.2 a ha)) bad
  noSetup _ _ h := h.elim
  done _ _ h := h.elim
  outputEvidence _ _ h := h.elim
  peerBoundary _ _ _ h := h.elim
  collectorBoundary _ _ _ h := h.elim
  collectorNextBoundary _ _ _ h := h.elim
  rerandBoundary _ _ _ h := h.elim
  coinBoundary _ _ _ h := h.elim
  extendMultBoundary _ _ _ h := h.elim
  checkBoundary _ _ _ h := h.elim
  openingBoundary _ _ _ h := h.elim
  emptyOpeningBoundary _ _ _ h := h.elim
  ceremony _ _ _ h := h.elim

/-- The actual input PRF calls, every collector layer, and Rerand reach the
first check Coin. Input queries retain their real log; the saved caller includes
the simulator's opening correction. Coverage permits cache hits from the dealer. -/
theorem treeStages_collector_input_runJobs (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (mode : settings.mode = .collector) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, (ctx₁ i).self = i) (self₂ : ∀ i, (ctx₂ i).self = i)
    (keys : ∀ i, (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (layer : ℕ) (remaining : List ℕ)
    (schedule : List.range (depth (jobs.map (circuits parameter ·.kind))) = layer :: remaining)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels₁ : ∀ i, (st₁ i).label = ρ) (labels₂ : ∀ i, (st₂ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (base : HashCache C)
    (covered₁ : ∀ i, TreeStagesPrfCovered base (ctx₁ i).keys.seed jobs)
    (covered₂ : ∀ i, TreeStagesPrfCovered base (ctx₂ i).keys.seed jobs)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * remaining.length + 3) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs inputs).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * remaining.length + 3) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + remaining.length + 1)) := by
  intro circs
  let gadgets₁ : C.Party → RunGadgets C E RealSpec := fun i => realRunGadgets K (ctx₁ i) settings.mode
  let gadgets₂ := fun i => treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  have mult₁ : ∀ i x y count, (gadgets₁ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
      reshareCollector K (ctx₁ i) rnd (mulRep K (ctx₁ i) x y) count) := by
    intro i x y count
    change (prssRandomness (ctx₁ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₁ i) settings.mode rnd (mulRep K (ctx₁ i) x y) count) = _
    rw [mode]; rfl
  have mult₂ : ∀ i x y count, (gadgets₂ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
      reshareCollector K (ctx₂ i) rnd (mulRep K (ctx₂ i) x y) count) := by
    intro i x y count
    change (prssRandomness (ctx₂ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₂ i) settings.mode rnd (mulRep K (ctx₂ i) x y) count) = _
    rw [mode]; rfl
  let entries : C.Party → TreeStagesBatchData C E base := fun i => {
    ctx₁ := ctx₁ i, ctx₂ := ctx₂ i, self := (self₁ i).trans (self₂ i).symm, keys := keys i
    jobs := jobs, idx := 0, count := (gatesAt circs layer).length
    covered₁ := covered₁ i, covered₂ := covered₂ i
    value₁ := fun inputs => mulRep K (ctx₁ i) (layerX K circs layer inputs) (layerY K circs layer inputs)
    value₂ := fun inputs => mulRep K (ctx₂ i) (layerX K circs layer inputs) (layerY K circs layer inputs)
    st₁ := st₁ i, st₂ := st₂ i, label := (labels₁ i).trans (labels₂ i).symm
    k₁ := fun inputs => treeStagesAfterLayer K (gadgets₁ i) circs layer remaining (inputs, []) (finish₁ i)
    k₂ := fun inputs => treeStagesAfterLayer K (gadgets₂ i) circs layer remaining (inputs, []) (finish₂ i)
    mode := .collector }
  have schedule' : List.range (depth circs) = layer :: remaining := schedule
  have entry₁ (i) : (do
      let inputs ← jobs.mapM (inputShares (ctx₁ i))
      (runJobs K (gadgets₁ i) circs inputs).run (st₁ i) >>= finish₁ i) = (entries i).real K := by
    unfold TreeStagesBatchData.real treeStagesBatchProgram
    apply bind_congr
    intro inputs
    rw [treeStages_runJobs_layers, schedule']
    exact treeStages_layers_collector K _ _ (mult₁ i) _ _ _ _ _ _
  have entry₂ (i) : (do
      let inputs ← jobs.mapM (inputShares (ctx₂ i))
      (runJobs K (gadgets₂ i) circs inputs).run (st₂ i) >>= finish₂ i) = (entries i).ideal K := by
    unfold TreeStagesBatchData.ideal treeStagesBatchProgram
    apply bind_congr
    intro inputs
    rw [treeStages_runJobs_layers, schedule']
    exact treeStages_layers_collector K _ _ (mult₂ i) _ _ _ _ _ _
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  change RelTriple
    (((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
      (do let inputs ← jobs.mapM (inputShares (ctx₁ i));
          (runJobs K (gadgets₁ i) circs inputs).run (st₁ i) >>= finish₁ i)))).run a) >>= _)
    (((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
      (do let inputs ← jobs.mapM (inputShares (ctx₂ i));
          (runJobs K (gadgets₂ i) circs inputs).run (st₂ i) >>= finish₂ i)))).run b) >>= _) _
  simp only [entry₁, entry₂]
  apply relTriple_bind (treeSim_relTriple_support (treeStages_batch_collector_start prims K D base entries T₀ ρ 0
    (gatesAt circs layer).length (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun i _ => self₁ i) (fun i _ => self₂ i) (fun i _ => labels₁ i) past visible
    (fun name key g _ => zero ((name, key), ρ, 0, g) (by rfl)) a b related grows
    (treeSim_futureEmpty_block D ρ 0 _ _ _ a.1.2 fresh)))
  intro u z h
  obtain ⟨⟨⟨rnd₁, rnd₂, masks, steps₁, steps₂⟩, caches, _⟩, hu, _⟩ := h
  let d : TreeSimCollectorData K D := {
    count := (gatesAt circs layer).length, T₀ := T₀, lacked := pivot.1
    δ := past + treeSimCollectorShift K D T₀ ρ 0 (gatesAt circs layer).length
      ((fun i => (entries i).value₁ (entries i).input₁) - (fun i => (entries i).value₂ (entries i).input₂))
    rnd₁ := rnd₁, rnd₂ := rnd₂
    v₁ := fun i => (entries i).value₁ (entries i).input₁
    v₂ := fun i => (entries i).value₂ (entries i).input₂
    st₁ := st₁, st₂ := st₂
    k₁ := fun i => (entries i).k₁ (entries i).input₁
    k₂ := fun i => (entries i).k₂ (entries i).input₂
    history := history, masks := masks, states := states }
  let s : TreeStagesCollectorSchedule K D d := {
    ctx₁ := ctx₁, ctx₂ := ctx₂, self₁ := fun i _ => self₁ i, self₂ := fun i _ => self₂ i
    keys := fun i _ => keys i, gadgets₁ := gadgets₁, gadgets₂ := gadgets₂
    mult₁ := fun i _ => mult₁ i, mult₂ := fun i _ => mult₂ i
    circs := circs, layer := layer, rest := remaining
    p₁ := fun i => ((entries i).input₁, []), p₂ := fun i => ((entries i).input₂, [])
    finish₁ := finish₁, finish₂ := finish₂
    program₁ := by intros; rfl
    program₂ := by intros; rfl
    ρ := ρ, labels := fun i _ => labels₁ i
    visible := by
      intro x hx
      change (past + treeSimCollectorShift K D T₀ ρ 0 (gatesAt circs layer).length _) x = 0
      simp only [Pi.add_apply, visible x hx, treeSimCollectorShift,
        treeSim_blockShift_visible D ρ 0 (gatesAt circs layer).length _ _ x hx, add_zero]
    zero := treeSim_futureZero_extend D ρ 0 _ _ _ past zero
    rerand₁ := by intros; rfl
    rerand₂ := by intros; rfl
    verify₁ := by intros; rfl
    verify₂ := by intros; rfl }
  have empty := treeSim_futureEmpty_after fresh
    (treeStages_batch_collector_start_logged_frame prims K D base entries ρ
      (by intros; rfl) (fun i _ => labels₁ i) a u hu)
  rw [steps₁, steps₂]
  change RelTriple
    ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * remaining.length + 3) state
      (treeSimCollectorWaiting K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run u.2)
    ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * remaining.length + 3) state
      (treeSimCollectorWaiting K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run z.2)
    (TreeStagesCheckReached K D A s.circs (s.ρ + remaining.length + 1))
  simpa only [treeStages_collector_partial_live K D (fun _ => true) (by intros; rfl), d, s] using
    s.execute prims K D A remaining d rfl nonzero (fun _ => true) state u.2 z.2 caches empty

/-- Actual input queries also compose with a zero-depth batch in either
mode, including Rerand's adapted masks and its saved check continuation. -/
theorem treeStages_zeroDepth_input_runJobs (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, (ctx₁ i).self = i) (self₂ : ∀ i, (ctx₂ i).self = i)
    (keys : ∀ i, (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (schedule : List.range (depth (jobs.map (circuits parameter ·.kind))) = [])
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels₁ : ∀ i, (st₁ i).label = ρ) (labels₂ : ∀ i, (st₂ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (base : HashCache C)
    (covered₁ : ∀ i, TreeStagesPrfCovered base (ctx₁ i).keys.seed jobs)
    (covered₂ : ∀ i, TreeStagesPrfCovered base (ctx₂ i).keys.seed jobs)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality 1 state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs inputs).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality 1 state steps).run b)
      (TreeStagesCheckReached K D A circs ρ) := by
  intro circs
  let gadgets₁ : C.Party → RunGadgets C E RealSpec := fun i => realRunGadgets K (ctx₁ i) settings.mode
  let gadgets₂ := fun i => treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  let entries : C.Party → TreeStagesBatchData C E base := fun i => {
    ctx₁ := ctx₁ i, ctx₂ := ctx₂ i, self := (self₁ i).trans (self₂ i).symm, keys := keys i
    jobs := jobs, idx := 0, count := (outputsOf circs).length
    covered₁ := covered₁ i, covered₂ := covered₂ i
    value₁ := fun inputs => ownerSum K (ctx₁ i) (outputShares K circs inputs)
    value₂ := fun inputs => ownerSum K (ctx₂ i) (outputShares K circs inputs)
    st₁ := st₁ i, st₂ := st₂ i, label := (labels₁ i).trans (labels₂ i).symm
    k₁ := fun inputs => treeStagesAfterRerand K (gadgets₁ i) circs (inputs, []) (finish₁ i)
    k₂ := fun inputs => treeStagesAfterRerand K (gadgets₂ i) circs (inputs, []) (finish₂ i)
    mode := .peer }
  have schedule' : List.range (depth circs) = [] := schedule
  have entry₁ (i) : (do
      let inputs ← jobs.mapM (inputShares (ctx₁ i))
      (runJobs K (gadgets₁ i) circs inputs).run (st₁ i) >>= finish₁ i) = (entries i).real K := by
    unfold TreeStagesBatchData.real treeStagesBatchProgram
    apply bind_congr
    intro inputs
    rw [treeStages_runJobs_layers, schedule']
    exact treeStages_layers_rerand K _ _ (by intros; rfl) _ _ _ _
  have entry₂ (i) : (do
      let inputs ← jobs.mapM (inputShares (ctx₂ i))
      (runJobs K (gadgets₂ i) circs inputs).run (st₂ i) >>= finish₂ i) = (entries i).ideal K := by
    unfold TreeStagesBatchData.ideal treeStagesBatchProgram
    apply bind_congr
    intro inputs
    rw [treeStages_runJobs_layers, schedule']
    exact treeStages_layers_rerand K _ _ (by intros; rfl) _ _ _ _
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let v₁ := fun i => (entries i).value₁ (entries i).input₁
  let v₂ := fun i => (entries i).value₂ (entries i).input₂
  let k₁ := fun i => (entries i).k₁ (entries i).input₁
  let k₂ := fun i => (entries i).k₂ (entries i).input₂
  let δ := past + treeSimPeerShift K D T₀ pivotParty ρ 0 (outputsOf circs).length (v₁ - v₂) 0
  have visible' : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D ρ 0 (outputsOf circs).length _ _ x hx, add_zero]
  have zero' : TreeSimFutureZero (ρ + 1) δ := treeSim_futureZero_extend D ρ 0 _ _ _ past zero
  have adapted : ∀ x, (a.1.2 x).isSome →
      treeSimPeerShift K D T₀ pivotParty ρ 0 (outputsOf circs).length (v₁ - v₂) 0 x = 0 :=
    treeSim_futureEmpty_block D ρ 0 _ _ _ a.1.2 fresh
  change RelTriple
    (((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
      (do let inputs ← jobs.mapM (inputShares (ctx₁ i));
          (runJobs K (gadgets₁ i) circs inputs).run (st₁ i) >>= finish₁ i)))).run a) >>= _)
    (((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
      (do let inputs ← jobs.mapM (inputShares (ctx₂ i));
          (runJobs K (gadgets₂ i) circs inputs).run (st₂ i) >>= finish₂ i)))).run b) >>= _) _
  simp only [entry₁, entry₂]
  apply relTriple_bind (treeSim_relTriple_support (treeStages_batch_start prims K D base entries δ visible'
    a b ⟨related.1, treeSim_hiddenRel_extend past _ related.2 adapted⟩ grows))
  intro u z h
  have masksRel : TreeStagesPeerResumeRel K D (fun _ => true) δ ctx₁ ctx₂ 0 (outputsOf circs).length
      v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 := by
    intro i
    have hi := h.1.1 i
    simpa only [TreeStagesBatchData.rel, TreeStagesReshareEntryRel,
      TreeStagesPeerResumeRel, if_true, entries, v₁, v₂, k₁, k₂, TreeStagesBatchData.input₁,
      TreeStagesBatchData.input₂] using hi
  obtain ⟨rnd₁, rnd₂, masks, steps₁, steps₂⟩ := treeStages_peer_resume_masks K D (fun _ => true) δ
    ctx₁ ctx₂ _ v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 masksRel
  let d : TreeSimPeerData K D := {
    δ := δ, count := (outputsOf circs).length, ctx₁ := ctx₁, ctx₂ := ctx₂
    rnd₁ := rnd₁, rnd₂ := rnd₂, v₁ := v₁, v₂ := v₂, st₁ := st₁, st₂ := st₂, k₁ := k₁, k₂ := k₂
    masks := masks, T₀ := T₀, pivotParty := pivotParty, pivot := pivot
    self₁ := fun i _ => self₁ i, self₂ := fun i _ => self₂ i, history := history, states := states
    block := by
      intro i hi
      rw [labels₁ i, treeSim_prssShift_add,
        treeSim_prssShift_zero past (ctx₁ i) ρ 0 _ (fun _ _ _ _ => zero _ (by rfl)), zero_add]
      unfold treeSimPeerShift
      rw [treeSim_prssShift_block D (ctx₁ i) (by simpa only [self₁ i] using hi), self₁ i] }
  let tail : TreeStagesRerandTail K D d := {
    gadgets₁ := gadgets₁, gadgets₂ := gadgets₂, circs := circs, count := rfl
    p₁ := fun i => ((entries i).input₁, []), p₂ := fun i => ((entries i).input₂, [])
    finish₁ := finish₁, finish₂ := finish₂
    program₁ := by intros; rfl
    program₂ := by intros; rfl
    ρ := ρ, labels := fun i _ => labels₁ i, keys := fun i _ => keys i
    verify₁ := by intros; rfl
    verify₂ := by intros; rfl
    visible := visible' }
  have empty := treeSim_futureEmpty_after fresh
    (treeStages_batch_peer_start_logged_frame prims K D base entries ρ
      (by intros; rfl) (fun i _ => labels₁ i) a u h.2.1)
  rw [steps₁, steps₂]
  apply relTriple_post_mono (tail.execute prims K D A d nonzero zero' (fun _ => true)
    state u.2 z.2 h.1.2.1 empty)
  intro u' z' h'
  obtain ⟨same, caches', zeroNext, empty₁', empty₂', start⟩ := h'
  exact ⟨same, d.δ, caches', tail.visible,
    Or.inr ⟨d, tail, rfl, rfl, rfl, zeroNext, empty₁', empty₂', start⟩⟩

/-- Every collector-mode batch with nonempty outputs reaches its first
check Coin or common abort after the actual input calls and `2 * depth + 1`
rounds. All shared-cache queries and the saved ceremony callers are retained. -/
theorem treeStages_collector_input_runJobs_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (mode : settings.mode = .collector) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, (ctx₁ i).self = i) (self₂ : ∀ i, (ctx₂ i).self = i)
    (keys : ∀ i, (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels₁ : ∀ i, (st₁ i).label = ρ) (labels₂ : ∀ i, (st₂ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (base : HashCache C)
    (covered₁ : ∀ i, TreeStagesPrfCovered base (ctx₁ i).keys.seed jobs)
    (covered₂ : ∀ i, TreeStagesPrfCovered base (ctx₂ i).keys.seed jobs)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * depth circs + 1) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs inputs).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * depth circs + 1) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + depth circs)) := by
  intro circs
  generalize schedule : List.range (depth circs) = layers
  cases layers with
  | nil =>
    have size : depth circs = 0 := by
      have h := congrArg List.length schedule
      simpa only [List.length_range, List.length_nil] using h
    rw [size]
    simpa only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
      treeStages_zeroDepth_input_runJobs prims K circuits settings D A state ctx₁ ctx₂ self₁ self₂ keys
        parameter openings batch jobs schedule nonzero st₁ st₂ finish₁ finish₂
        ρ labels₁ labels₂ history states base covered₁ covered₂ past visible zero a b related grows fresh
  | cons layer remaining =>
    have size : depth circs = remaining.length + 1 := by
      have h := congrArg List.length schedule
      simpa only [List.length_range, List.length_cons] using h
    have fuel : 2 * depth circs + 1 = 2 * remaining.length + 3 := by omega
    have label : ρ + depth circs = ρ + remaining.length + 1 := by omega
    rw [fuel, label]
    exact treeStages_collector_input_runJobs prims K circuits settings D A state mode ctx₁ ctx₂ self₁ self₂ keys
      parameter openings batch jobs layer remaining schedule nonzero st₁ st₂ finish₁ finish₂
      ρ labels₁ labels₂ history states base covered₁ covered₂ past visible zero a b related grows fresh

/-- Instantiate the input-to-check composition at an actual ceremony batch:
dealt real keys, dummy hidden seeds, common PRSS keys, empty histories, and
one finite padding result covering every later choice of jobs. The incoming
shared cache may contain arbitrary dealer and adversarial answers. -/
theorem treeStages_collector_ceremonyBatch_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (mode : settings.mode = .collector) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (prss : C.Party → PrssKeys C)
    (openings : List (List (List Bit))) (batch ρ : ℕ) (jobs : List Job)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (cache : HashCache C) (padded : Unit × HashCache C)
    (padding : padded ∈ support ((simulateQ (localAnswer prims)
      (treeStagesCeremonyPrfPadding seeds)).run cache))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : padded.2 ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let dummy := fun T => if KnownTo D.1 T then seeds T else 0
    let ctx₁ := fun i => (⟨i, dealtKeys parameter seeds pairs i, prss i⟩ : Context C)
    let ctx₂ := fun i => (⟨i, ⟨parameter, dummy, fun _ => 0⟩, prss i⟩ : Context C)
    let st : RunState C := ⟨fun _ => [], ρ, batch⟩
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run st >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (2 * depth circs + 1) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter dummy openings (ctx₂ i) batch jobs)
            circs inputs).run st >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (2 * depth circs + 1) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + depth circs)) := by
  intro dummy ctx₁ ctx₂ st circs
  obtain ⟨_, covered⟩ := treeStages_seedPadding_covered prims (0 :: C.terms.map seeds) cache padded padding
  have realCovered : ∀ i, TreeStagesPrfCovered padded.2 (ctx₁ i).keys.seed jobs := by
    intro i
    apply treeStages_seedsCovered_jobs padded.2 _ covered _ _ jobs
    intro T
    change (if i ∈ C.holders T then seeds T else 0) ∈ 0 :: C.terms.map seeds
    split_ifs <;> simp [Committee.terms]
  have idealCovered : ∀ i, TreeStagesPrfCovered padded.2 (ctx₂ i).keys.seed jobs := by
    intro i
    apply treeStages_seedsCovered_jobs padded.2 _ covered _ _ jobs
    intro T
    change (if KnownTo D.1 T then seeds T else 0) ∈ 0 :: C.terms.map seeds
    split_ifs <;> simp [Committee.terms]
  exact treeStages_collector_input_runJobs_check prims K circuits settings D A state mode ctx₁ ctx₂
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    parameter openings batch jobs nonzero (fun _ => st) (fun _ => st) finish₁ finish₂
    ρ (by intros; rfl) (by intros; rfl) [] (fun i _ => ⟨rfl, rfl, treeSimHistoryRel_empty D i⟩)
    padded.2 realCovered idealCovered past visible zero a b related grows fresh

/-- First-Coin entry needs a nonempty checked tuple vector, even when the
batch's output vector is empty. Prior multiplication tuples suffice. -/
theorem TreeStagesRerandTail.execute_nonempty (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (nz₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (nz₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (future : TreeSimFutureZero (tail.ρ + 1) d.δ)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (tail.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 1 state
        (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 1 state
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ TreeSimStreamRel d.δ u.2 z.2 ∧
        TreeSimFutureZero (tail.ρ + 2) d.δ ∧ TreeSimFutureEmpty (tail.ρ + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (tail.ρ + 2) z.2.2 ∧ TreeStagesCheckStart K D d tail u.1.2 z.1.2) := by
  by_cases stopped : ∀ i, i ∉ D.1 → live i ≠ true
  · have none₁ : treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp [treeSimPeerPartial, stopped i hi]
    have none₂ : treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp [treeSimPeerPartial, stopped i hi]
    rw [none₁, none₂]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, related, (fun x hx => future x (by omega)),
      (fun x hx => fresh x (by omega)),
      (fun x hx => treeSim_futureEmpty_related fresh related.2 x (by omega)), Or.inl ⟨rfl, rfl⟩⟩
  · push_neg at stopped
    obtain ⟨i, hi, hl⟩ := stopped
    have active₁ : ¬ AllDone D (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) := by
      intro done
      have h := done i hi
      simpa [treeSimPeerPartial, treeSimPeerWaiting, treeSimPeerStep, hi, hl] using h
    have active₂ : ¬ AllDone D (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
      intro done
      have h := done i hi
      simpa [treeSimPeerPartial, treeSimPeerWaiting, treeSimPeerStep, hi, hl] using h
    simp only [AllDone] at active₁ active₂
    simp only [executeSteps, if_neg active₁, if_neg active₂, StateT.run_bind]
    apply relTriple_bind (tail.coin_boundary_round prims K D A d tail.keys tail.verify₁ tail.verify₂
      nz₁ nz₂ tail.visible future live state a b related fresh)
    intro u z h
    obtain ⟨stateEq, _, caches, zero, fresh₁, fresh₂, aborted | ⟨sent, rnd, _, _, steps₁, steps₂⟩⟩ := h
    · exact relTriple_pure_pure ⟨stateEq, caches, zero, fresh₁, fresh₂, Or.inl aborted⟩
    · exact relTriple_pure_pure ⟨stateEq, caches, zero, fresh₁, fresh₂,
        Or.inr ⟨nz₁, nz₂, sent, rnd, steps₁, steps₂⟩⟩

/-- Select the next actual peer gadget: an AND layer, or the final Rerand. -/
def treeStagesPeerLayerCount (circs : List Circuit) : List ℕ → ℕ
  | [] => (outputsOf circs).length
  | layer :: _ => (gatesAt circs layer).length

def treeStagesPeerLayerValue (ctx : Context C) (circs : List Circuit) (layers : List ℕ)
    (p : List (C.Term → List Bit) × List (Tuple C)) : ℕ → Bit :=
  match layers with
  | [] => ownerSum K ctx (outputShares K circs p.1)
  | layer :: _ => mulRep K ctx (layerX K circs layer p.1) (layerY K circs layer p.1)

def treeStagesPeerLayerCont (gadgets : RunGadgets C E RealSpec) (circs : List Circuit)
    (layers : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C))
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :=
  match layers with
  | [] => treeStagesAfterRerand K gadgets circs p finish
  | layer :: rest => treeStagesAfterLayer K gadgets circs layer rest p finish

/-- The peer layer fold retains exactly its real PRSS, saved tuple and caller. -/
theorem treeStages_layers_peer (ctx : Context C) (gadgets : RunGadgets C E RealSpec)
    (mult : ∀ x y count, gadgets.mult x y count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshare K ctx bitCodec rnd (mulRep K ctx x y) count))
    (rerand : ∀ v count, gadgets.rerand v count = (do
      let rnd ← prssRandomness ctx bitCodec 0 count
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count))
    (circs : List Circuit) (layers : List ℕ)
    (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C)
    (finish : List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesLayers K gadgets circs layers p st finish =
      treeSimPeerProgram K ctx 0 (treeStagesPeerLayerCount circs layers)
        (treeStagesPeerLayerValue K ctx circs layers p) st
        (treeStagesPeerLayerCont K gadgets circs layers p finish) := by
  cases layers with
  | nil => exact treeStages_layers_rerand K ctx gadgets rerand circs p st finish
  | cons layer rest =>
    rw [treeStages_layers_cons, mult]
    rfl

/-- Aborted peer outputs are totalized only for certificates. Their unused
states retain the same next label and the exact history-translation relation. -/
theorem treeStages_peer_exit_values (D : C.Coalition) (d : TreeSimPeerData K D)
    (sent : C.Party → Mail C E) :
    let out₁ := treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
    let out₂ := treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
    ∃ (live : C.Party → Bool) (x₁ x₂ : C.Party → Shares C Bit × RunState C),
      (∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none) ∧
      (∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none) ∧
      (∀ i, i ∉ D.1 → TreeSimPeerExitRel K D d i (x₁ i) (x₂ i)) := by
  intro out₁ out₂
  let difference := fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g
  let fallback₁ := fun i => ((0, ⟨recordMode K .peer i (d.st₁ i).history 0 d.count,
    (d.st₁ i).label + 1, (d.st₁ i).tag⟩) : Shares C Bit × RunState C)
  let fallback₂ := fun i => ((treeSimHeldShift D i d.count difference 0,
    ⟨recordMode K .peer i (d.st₂ i).history (treeSimHeldShift D i d.count difference 0) d.count,
      (d.st₂ i).label + 1, (d.st₂ i).tag⟩) : Shares C Bit × RunState C)
  have fallback : ∀ i, i ∉ D.1 → TreeSimPeerExitRel K D d i (fallback₁ i) (fallback₂ i) := by
    intro i hi
    refine ⟨rfl, ?_, rfl, rfl⟩
    refine ⟨congrArg (· + 1) (d.states i hi).1, (d.states i hi).2.1, ?_⟩
    exact treeSim_recordMode_shift K D .peer d.T₀ d.pivot.lacked i d.count d.history difference
      (d.st₁ i).history (d.st₂ i).history (d.states i hi).2.2 0 _ rfl
  refine ⟨fun i => (out₁ i).isSome, fun i => (out₁ i).getD (fallback₁ i),
    fun i => (out₂ i).getD (fallback₂ i), ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₁, treeSimPeerOutputs, hi]
    · simp only [if_neg hi]
      cases out₁ i <;> rfl
  · intro i
    by_cases hi : i ∈ D.1
    · simp [out₂, treeSimPeerOutputs, hi]
    · simp only [if_neg hi]
      have h : Option.Rel _ (out₁ i) (out₂ i) := d.outputs K D sent i
      generalize out₁ i = left at h ⊢
      generalize out₂ i = right at h ⊢
      cases h <;> rfl
  · intro i hi
    change TreeSimPeerExitRel K D d i ((out₁ i).getD (fallback₁ i)) ((out₂ i).getD (fallback₂ i))
    have h : Option.Rel _ (out₁ i) (out₂ i) := d.outputs K D sent i
    generalize out₁ i = left at h ⊢
    generalize out₂ i = right at h ⊢
    cases h with
    | none => exact fallback i hi
    | some h => exact h

/-- A peer schedule records the remaining actual AND layers. Its empty case
is Rerand, whose continuation includes the complete check and batch caller. -/
structure TreeStagesPeerSchedule (D : C.Coalition) (d : TreeSimPeerData K D) (layers : List ℕ) where
  gadgets₁ : C.Party → RunGadgets C E RealSpec
  gadgets₂ : C.Party → RunGadgets C E RealSpec
  mult₁ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₁ i).mult x y count = (do
    let rnd ← prssRandomness (d.ctx₁ i) bitCodec 0 count
    reshare K (d.ctx₁ i) bitCodec rnd (mulRep K (d.ctx₁ i) x y) count)
  mult₂ : ∀ i, i ∉ D.1 → ∀ x y count, (gadgets₂ i).mult x y count = (do
    let rnd ← prssRandomness (d.ctx₂ i) bitCodec 0 count
    reshare K (d.ctx₂ i) bitCodec rnd (mulRep K (d.ctx₂ i) x y) count)
  rerand₁ : ∀ i, i ∉ D.1 → ∀ v count, (gadgets₁ i).rerand v count = (do
    let rnd ← prssRandomness (d.ctx₁ i) bitCodec 0 count
    reshare K (d.ctx₁ i) bitCodec rnd (ownerSum K (d.ctx₁ i) v) count)
  rerand₂ : ∀ i, i ∉ D.1 → ∀ v count, (gadgets₂ i).rerand v count = (do
    let rnd ← prssRandomness (d.ctx₂ i) bitCodec 0 count
    reshare K (d.ctx₂ i) bitCodec rnd (ownerSum K (d.ctx₂ i) v) count)
  verify₁ : ∀ i, i ∉ D.1 → (gadgets₁ i).verify = check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i))
  verify₂ : ∀ i, i ∉ D.1 → (gadgets₂ i).verify = check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i))
  keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss
  circs : List Circuit
  count : d.count = treeStagesPeerLayerCount circs layers
  p₁ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  p₂ : C.Party → List (C.Term → List Bit) × List (Tuple C)
  finish₁ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → d.k₁ i = treeStagesPeerLayerCont K (gadgets₁ i) circs layers (p₁ i) (finish₁ i)
  program₂ : ∀ i, i ∉ D.1 → d.k₂ i = treeStagesPeerLayerCont K (gadgets₂ i) circs layers (p₂ i) (finish₂ i)
  checked₁ : ∀ i, i ∉ D.1 →
    ((p₁ i).2.map (·.count)).sum + (layers.map (fun l => (gatesAt circs l).length)).sum +
      (outputsOf circs).length ≠ 0
  checked₂ : ∀ i, i ∉ D.1 →
    ((p₂ i).2.map (·.count)).sum + (layers.map (fun l => (gatesAt circs l).length)).sum +
      (outputsOf circs).length ≠ 0
  ρ : ℕ
  labels : ∀ i, i ∉ D.1 → (d.st₁ i).label = ρ
  visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0
  zero : TreeSimFutureZero (ρ + 1) d.δ

def TreeStagesPeerSchedule.last (D : C.Coalition) (d : TreeSimPeerData K D)
    (s : TreeStagesPeerSchedule K D d []) : TreeStagesRerandTail K D d where
  gadgets₁ := s.gadgets₁
  gadgets₂ := s.gadgets₂
  circs := s.circs
  count := s.count
  p₁ := s.p₁
  p₂ := s.p₂
  finish₁ := s.finish₁
  finish₂ := s.finish₂
  program₁ := s.program₁
  program₂ := s.program₂
  ρ := s.ρ
  labels := s.labels
  keys := s.keys
  verify₁ := s.verify₁
  verify₂ := s.verify₂
  visible := s.visible

/-- A successful or aborted peer exit fixes the next saved layer program
and its fresh adapted PRSS block. No future coupling is an assumption. -/
theorem TreeStagesPeerSchedule.next (D : C.Coalition) (d : TreeSimPeerData K D)
    (layer : ℕ) (rest : List ℕ) (s : TreeStagesPeerSchedule K D d (layer :: rest))
    (initial : HiddenCache C) (fresh : TreeSimFutureEmpty (s.ρ + 1) initial)
    (sent : C.Party → Mail C E) :
    let out₁ := treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
    let out₂ := treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
    ∃ n : TreeStagesPeerNext K D d.δ initial d.k₁ d.k₂ out₁ out₂,
      n.ρ = s.ρ + 1 ∧
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        ∃ successor : TreeStagesPeerSchedule K D (n.data K rnd₁ rnd₂ masks) rest,
          successor.ρ = n.ρ ∧ successor.circs = s.circs := by
  intro out₁ out₂
  obtain ⟨live, x₁, x₂, shape₁, shape₂, exits⟩ := treeStages_peer_exit_values K D d sent
  let nextP₁ := fun i => (appendLayer s.circs layer (s.p₁ i).1 (x₁ i).1,
    (s.p₁ i).2 ++ [⟨layerX K s.circs layer (s.p₁ i).1, layerY K s.circs layer (s.p₁ i).1,
      (x₁ i).1, (gatesAt s.circs layer).length, (s.gadgets₁ i).mode⟩])
  let nextP₂ := fun i => (appendLayer s.circs layer (s.p₂ i).1 (x₂ i).1,
    (s.p₂ i).2 ++ [⟨layerX K s.circs layer (s.p₂ i).1, layerY K s.circs layer (s.p₂ i).1,
      (x₂ i).1, (gatesAt s.circs layer).length, (s.gadgets₂ i).mode⟩])
  refine ⟨{
    T₀ := d.T₀, pivotParty := d.pivotParty, pivot := d.pivot
    ctx₁ := d.ctx₁, ctx₂ := d.ctx₂, self₁ := d.self₁, self₂ := d.self₂, keys := s.keys
    ρ := s.ρ + 1, count := treeStagesPeerLayerCount s.circs rest
    v₁ := fun i => treeStagesPeerLayerValue K (d.ctx₁ i) s.circs rest (nextP₁ i)
    v₂ := fun i => treeStagesPeerLayerValue K (d.ctx₂ i) s.circs rest (nextP₂ i)
    st₁ := fun i => (x₁ i).2, st₂ := fun i => (x₂ i).2
    lab₁ := fun i hi => (exits i hi).2.2.1.trans (congrArg (· + 1) (s.labels i hi))
    lab₂ := fun i hi => (exits i hi).2.2.2.trans (congrArg (· + 1) ((d.states i hi).1.symm.trans (s.labels i hi)))
    next₁ := fun i => treeStagesPeerLayerCont K (s.gadgets₁ i) s.circs rest (nextP₁ i) (s.finish₁ i)
    next₂ := fun i => treeStagesPeerLayerCont K (s.gadgets₂ i) s.circs rest (nextP₂ i) (s.finish₂ i)
    x₁ := x₁, x₂ := x₂, live := live, shape₁ := shape₁, shape₂ := shape₂
    program₁ := ?_, program₂ := ?_
    history := treeSimHistoryAppend K d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g)
    states := fun i hi => (exits i hi).2.1
    visible := s.visible, futureZero := s.zero, futureEmpty := fresh
  }, rfl, ?_⟩
  · intro i hi _
    rw [s.program₁ i hi]
    exact treeStages_layers_peer K (d.ctx₁ i) (s.gadgets₁ i) (s.mult₁ i hi) (s.rerand₁ i hi)
      s.circs rest (nextP₁ i) (x₁ i).2 (s.finish₁ i)
  · intro i hi _
    rw [s.program₂ i hi]
    exact treeStages_layers_peer K (d.ctx₂ i) (s.gadgets₂ i) (s.mult₂ i hi) (s.rerand₂ i hi)
      s.circs rest (nextP₂ i) (x₂ i).2 (s.finish₂ i)
  · intro rnd₁ rnd₂ masks zeroNext
    refine ⟨{
      gadgets₁ := s.gadgets₁, gadgets₂ := s.gadgets₂, mult₁ := s.mult₁, mult₂ := s.mult₂
      rerand₁ := s.rerand₁, rerand₂ := s.rerand₂, verify₁ := s.verify₁, verify₂ := s.verify₂, keys := s.keys
      circs := s.circs, count := rfl, p₁ := nextP₁, p₂ := nextP₂, finish₁ := s.finish₁, finish₂ := s.finish₂
      program₁ := by intros; rfl
      program₂ := by intros; rfl
      checked₁ := by
        intro i hi
        have h := s.checked₁ i hi
        simpa only [nextP₁, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using h
      checked₂ := by
        intro i hi
        have h := s.checked₂ i hi
        simpa only [nextP₂, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using h
      ρ := s.ρ + 1
      labels := fun i hi => (exits i hi).2.2.1.trans (congrArg (· + 1) (s.labels i hi))
      visible := ?_, zero := zeroNext
    }, rfl, rfl⟩
    intro x hx
    change (d.δ + treeSimPeerShift K D d.T₀ d.pivotParty (s.ρ + 1) 0 (treeStagesPeerLayerCount s.circs rest) _ 0) x = 0
    simp only [Pi.add_apply, s.visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D (s.ρ + 1) 0 (treeStagesPeerLayerCount s.circs rest) _ _ x hx, add_zero]

/-- One actual rushing peer round enters the next AND layer or Rerand with
its full saved program, exact masks, history relation and fresh later labels. -/
theorem TreeStagesPeerSchedule.round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (d : TreeSimPeerData K D)
    (layer : ℕ) (rest : List ℕ) (s : TreeStagesPeerSchedule K D d (layer :: rest))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        ∃ (next : TreeSimPeerData K D) (successor : TreeStagesPeerSchedule K D next rest)
          (live : C.Party → Bool),
          successor.ρ = s.ρ + 1 ∧ successor.circs = s.circs ∧ TreeSimStreamRel next.δ u.2 z.2 ∧
          TreeSimFutureEmpty (successor.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (successor.ρ + 1) z.2.2 ∧
          u.1.2.1 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
          z.1.2.1 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_peer_resume_factor, treeSim_peer_resume_factor, d.view K D]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
  intro u z h
  obtain ⟨n, label, after⟩ := s.next K D d layer rest a.1.2 fresh u.1.2
  rw [← h.1]
  apply relTriple_bind (n.coupling prims K D d.δ a.1.2 d.k₁ d.k₂ _ _ u.2 z.2 h.2.1 h.2.2.1)
  intro u' z' h'
  simp only [simulateQ_pure, StateT.run_pure]
  obtain ⟨caches, empty₁, empty₂, zeroNext, rnd₁, rnd₂, masks, steps₁, steps₂⟩ := h'
  obtain ⟨successor, nextLabel, circs⟩ := after rnd₁ rnd₂ masks zeroNext
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, n.data K rnd₁ rnd₂ masks, successor, n.live,
    nextLabel.trans label, circs, caches, ?_, ?_, steps₁, steps₂⟩
  · simpa only [nextLabel] using empty₁
  · simpa only [nextLabel] using empty₂

/-- Any stopped peer propagates its abort in at most one real round;
all remaining scheduled rounds are then inert. -/
theorem treeStages_peer_partial_execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimPeerData K D)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true)
    (fuel : ℕ) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none) ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  by_cases inactive : ∀ i, i ∉ D.1 → live i ≠ true
  · have none₁ : treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp [treeSimPeerPartial, inactive i hi]
    have none₂ : treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
      · simp [treeSimPeerPartial, inactive i hi]
    rw [none₁, none₂]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, rfl, related, rfl, rfl⟩
  · push_neg at inactive
    obtain ⟨i, hi, hl⟩ := inactive
    have active₁ : ¬ AllDone D (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) := by
      intro done
      have h := done i hi
      simp [treeSimPeerPartial, treeSimPeerWaiting, treeSimPeerStep, hi, hl] at h
    have active₂ : ¬ AllDone D (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
      intro done
      have h := done i hi
      simp [treeSimPeerPartial, treeSimPeerWaiting, treeSimPeerStep, hi, hl] at h
    simp only [AllDone] at active₁ active₂
    rw [executeSteps, if_neg active₁, executeSteps, if_neg active₂]
    simp only [StateT.run_bind]
    simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    rw [treeSim_peer_partial_factor K D A _ _ live stopped,
      treeSim_peer_partial_factor K D A _ _ live stopped, d.partial_view K D live]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a b related)
    intro u z h
    rw [executeSteps_done _ D A noFunctionality fuel _ _ (by intros; trivial),
      executeSteps_done _ D A noFunctionality fuel _ _ (by intros; trivial)]
    have same : u.1.1 = z.1.1 := congrArg Prod.fst h.1
    exact relTriple_pure_pure ⟨same, rfl, rfl, h.2⟩

theorem treeStages_peer_partial_live (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (active : ∀ i, i ∉ D.1 → live i = true) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeSimPeerPartial K D ctx live count rnd v st k = treeSimPeerWaiting K D ctx count rnd v st k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimPeerPartial, treeSimPeerWaiting, hi]
  · simp only [treeSimPeerPartial, active i hi, if_true]

/-- Execute the entire peer-mode layer schedule and Rerand. Each AND layer
uses one real rushing exchange, and the result retains the first check Coin,
or a common abort, together with the exact saved check/output continuation. -/
theorem TreeStagesPeerSchedule.execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (layers : List ℕ)
    (d : TreeSimPeerData K D) (s : TreeStagesPeerSchedule K D d layers)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (s.ρ + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (layers.length + 1) state
        (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (layers.length + 1) state
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (TreeStagesCheckReached K D A s.circs (s.ρ + layers.length)) := by
  induction layers generalizing d state a b live with
  | nil =>
    let tail := s.last K D d
    have nz₁ : ∀ i, i ∉ D.1 → ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0 := by
      simpa only [tail, TreeStagesPeerSchedule.last, List.map_nil, List.sum_nil, Nat.add_zero] using s.checked₁
    have nz₂ : ∀ i, i ∉ D.1 → ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0 := by
      simpa only [tail, TreeStagesPeerSchedule.last, List.map_nil, List.sum_nil, Nat.add_zero] using s.checked₂
    apply relTriple_post_mono (tail.execute_nonempty prims K D A d nz₁ nz₂ s.zero live state a b related fresh)
    intro u z h
    obtain ⟨same, caches, zeroNext, empty₁, empty₂, start⟩ := h
    exact ⟨same, d.δ, caches, s.visible,
      Or.inr ⟨d, tail, rfl, rfl, rfl, zeroNext, empty₁, empty₂, start⟩⟩
  | cons layer rest ih =>
    by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
    · apply relTriple_post_mono (treeStages_peer_partial_execute prims K D A d live stopped
        (layer :: rest).length state a b related)
      intro u z h
      exact ⟨h.1, d.δ, h.2.2.2.1, s.visible, Or.inl ⟨h.2.1, h.2.2.1⟩⟩
    · have active : ∀ i, i ∉ D.1 → live i = true := by
        intro i hi
        by_contra hl
        exact stopped ⟨i, hi, hl⟩
      rw [treeStages_peer_partial_live K D d.ctx₁ live active,
        treeStages_peer_partial_live K D d.ctx₂ live active]
      have ready : ∀ ctx rnd v st k,
          ¬ AllDone D (treeSimPeerWaiting (α := TreeOutput) K D ctx d.count rnd v st k) := by
        intro ctx rnd v st k done
        obtain ⟨i, hi⟩ := exists_honest D
        have h := done i hi
        simp [treeSimPeerWaiting, treeSimPeerStep, hi] at h
      have ready₁ := ready d.ctx₁ d.rnd₁ d.v₁ d.st₁ d.k₁
      have ready₂ := ready d.ctx₂ d.rnd₂ d.v₂ d.st₂ d.k₂
      simp only [AllDone] at ready₁ ready₂
      rw [List.length_cons, executeSteps, if_neg ready₁, executeSteps, if_neg ready₂]
      simp only [StateT.run_bind]
      apply relTriple_bind (s.round prims K D A state d layer rest a b related fresh)
      intro u z h
      obtain ⟨same, _, next, successor, nextLive, label, circs, caches, empty₁, _, steps₁, steps₂⟩ := h
      rw [← same, steps₁, steps₂]
      have labels : successor.ρ + rest.length = s.ρ + (rest.length + 1) := by rw [label]; omega
      apply relTriple_post_mono (ih next successor nextLive u.1.1 u.2 z.2 caches empty₁)
      intro u' z' h'
      simpa only [circs, labels] using h'

/-- The actual input queries, all peer AND layers, and Rerand reach the
first check Coin or common abort in `depth + 1` driver rounds. The real logs,
adapted T₀ masks and saved simulator correction remain in the execution. -/
theorem treeStages_peer_input_runJobs_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (mode : settings.mode = .peer) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, (ctx₁ i).self = i) (self₂ : ∀ i, (ctx₂ i).self = i)
    (keys : ∀ i, (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (nonzero :
      ((List.range (depth (jobs.map (circuits parameter ·.kind)))).map
        (fun l => (gatesAt (jobs.map (circuits parameter ·.kind)) l).length)).sum +
        (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels₁ : ∀ i, (st₁ i).label = ρ) (labels₂ : ∀ i, (st₂ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (base : HashCache C)
    (covered₁ : ∀ i, TreeStagesPrfCovered base (ctx₁ i).keys.seed jobs)
    (covered₂ : ∀ i, TreeStagesPrfCovered base (ctx₂ i).keys.seed jobs)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (depth circs + 1) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs inputs).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (depth circs + 1) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + depth circs)) := by
  intro circs
  let gadgets₁ : C.Party → RunGadgets C E RealSpec := fun i => realRunGadgets K (ctx₁ i) settings.mode
  let gadgets₂ := fun i => treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs
  let layers := List.range (depth circs)
  have mult₁ : ∀ i x y count, (gadgets₁ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₁ i) bitCodec 0 count
      reshare K (ctx₁ i) bitCodec rnd (mulRep K (ctx₁ i) x y) count) := by
    intro i x y count
    change (prssRandomness (ctx₁ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₁ i) settings.mode rnd (mulRep K (ctx₁ i) x y) count) = _
    rw [mode]; rfl
  have mult₂ : ∀ i x y count, (gadgets₂ i).mult x y count = (do
      let rnd ← prssRandomness (ctx₂ i) bitCodec 0 count
      reshare K (ctx₂ i) bitCodec rnd (mulRep K (ctx₂ i) x y) count) := by
    intro i x y count
    change (prssRandomness (ctx₂ i) bitCodec 0 count >>= fun rnd =>
      reshareWith K (ctx₂ i) settings.mode rnd (mulRep K (ctx₂ i) x y) count) = _
    rw [mode]; rfl
  let entries : C.Party → TreeStagesBatchData C E base := fun i => {
    ctx₁ := ctx₁ i, ctx₂ := ctx₂ i, self := (self₁ i).trans (self₂ i).symm, keys := keys i
    jobs := jobs, idx := 0, count := (treeStagesPeerLayerCount circs layers)
    covered₁ := covered₁ i, covered₂ := covered₂ i
    value₁ := fun inputs => treeStagesPeerLayerValue K (ctx₁ i) circs layers (inputs, [])
    value₂ := fun inputs => treeStagesPeerLayerValue K (ctx₂ i) circs layers (inputs, [])
    st₁ := st₁ i, st₂ := st₂ i, label := (labels₁ i).trans (labels₂ i).symm
    k₁ := fun inputs => treeStagesPeerLayerCont K (gadgets₁ i) circs layers (inputs, []) (finish₁ i)
    k₂ := fun inputs => treeStagesPeerLayerCont K (gadgets₂ i) circs layers (inputs, []) (finish₂ i)
    mode := .peer }
  have entry₁ (i) : (do
      let inputs ← jobs.mapM (inputShares (ctx₁ i))
      (runJobs K (gadgets₁ i) circs inputs).run (st₁ i) >>= finish₁ i) = (entries i).real K := by
    unfold TreeStagesBatchData.real treeStagesBatchProgram
    apply bind_congr
    intro inputs
    rw [treeStages_runJobs_layers]
    exact treeStages_layers_peer K _ _ (mult₁ i) (by intros; rfl) _ _ _ _ _
  have entry₂ (i) : (do
      let inputs ← jobs.mapM (inputShares (ctx₂ i))
      (runJobs K (gadgets₂ i) circs inputs).run (st₂ i) >>= finish₂ i) = (entries i).ideal K := by
    unfold TreeStagesBatchData.ideal treeStagesBatchProgram
    apply bind_congr
    intro inputs
    rw [treeStages_runJobs_layers]
    exact treeStages_layers_peer K _ _ (mult₂ i) (by intros; rfl) _ _ _ _ _
  obtain ⟨T₀, pivotParty, pivot⟩ := exists_pivot K D
  let v₁ := fun i => (entries i).value₁ (entries i).input₁
  let v₂ := fun i => (entries i).value₂ (entries i).input₂
  let k₁ := fun i => (entries i).k₁ (entries i).input₁
  let k₂ := fun i => (entries i).k₂ (entries i).input₂
  let δ := past + treeSimPeerShift K D T₀ pivotParty ρ 0 (treeStagesPeerLayerCount circs layers) (v₁ - v₂) 0
  have visible' : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D ρ 0 (treeStagesPeerLayerCount circs layers) _ _ x hx, add_zero]
  have zero' : TreeSimFutureZero (ρ + 1) δ := treeSim_futureZero_extend D ρ 0 _ _ _ past zero
  have adapted : ∀ x, (a.1.2 x).isSome →
      treeSimPeerShift K D T₀ pivotParty ρ 0 (treeStagesPeerLayerCount circs layers) (v₁ - v₂) 0 x = 0 :=
    treeSim_futureEmpty_block D ρ 0 _ _ _ a.1.2 fresh
  change RelTriple
    (((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i =>
      (do let inputs ← jobs.mapM (inputShares (ctx₁ i));
          (runJobs K (gadgets₁ i) circs inputs).run (st₁ i) >>= finish₁ i)))).run a) >>= _)
    (((simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i =>
      (do let inputs ← jobs.mapM (inputShares (ctx₂ i));
          (runJobs K (gadgets₂ i) circs inputs).run (st₂ i) >>= finish₂ i)))).run b) >>= _) _
  simp only [entry₁, entry₂]
  apply relTriple_bind (treeSim_relTriple_support (treeStages_batch_start prims K D base entries δ visible'
    a b ⟨related.1, treeSim_hiddenRel_extend past _ related.2 adapted⟩ grows))
  intro u z h
  have masksRel : TreeStagesPeerResumeRel K D (fun _ => true) δ ctx₁ ctx₂ 0 (treeStagesPeerLayerCount circs layers)
      v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 := by
    intro i
    have hi := h.1.1 i
    simpa only [TreeStagesBatchData.rel, TreeStagesReshareEntryRel,
      TreeStagesPeerResumeRel, if_true, entries, v₁, v₂, k₁, k₂, TreeStagesBatchData.input₁,
      TreeStagesBatchData.input₂] using hi
  obtain ⟨rnd₁, rnd₂, masks, steps₁, steps₂⟩ := treeStages_peer_resume_masks K D (fun _ => true) δ
    ctx₁ ctx₂ _ v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 masksRel
  let d : TreeSimPeerData K D := {
    δ := δ, count := (treeStagesPeerLayerCount circs layers), ctx₁ := ctx₁, ctx₂ := ctx₂
    rnd₁ := rnd₁, rnd₂ := rnd₂, v₁ := v₁, v₂ := v₂, st₁ := st₁, st₂ := st₂, k₁ := k₁, k₂ := k₂
    masks := masks, T₀ := T₀, pivotParty := pivotParty, pivot := pivot
    self₁ := fun i _ => self₁ i, self₂ := fun i _ => self₂ i, history := history, states := states
    block := by
      intro i hi
      rw [labels₁ i, treeSim_prssShift_add,
        treeSim_prssShift_zero past (ctx₁ i) ρ 0 _ (fun _ _ _ _ => zero _ (by rfl)), zero_add]
      unfold treeSimPeerShift
      rw [treeSim_prssShift_block D (ctx₁ i) (by simpa only [self₁ i] using hi), self₁ i] }
  let sched : TreeStagesPeerSchedule K D d layers := {
    mult₁ := fun i _ => mult₁ i, mult₂ := fun i _ => mult₂ i
    rerand₁ := by intros; rfl
    rerand₂ := by intros; rfl
    gadgets₁ := gadgets₁, gadgets₂ := gadgets₂, circs := circs, count := rfl
    p₁ := fun i => ((entries i).input₁, []), p₂ := fun i => ((entries i).input₂, [])
    finish₁ := finish₁, finish₂ := finish₂
    program₁ := by intros; rfl
    program₂ := by intros; rfl
    checked₁ := by intro i hi; simpa only [List.map_nil, List.sum_nil, Nat.zero_add] using nonzero
    checked₂ := by intro i hi; simpa only [List.map_nil, List.sum_nil, Nat.zero_add] using nonzero
    ρ := ρ, labels := fun i _ => labels₁ i, keys := fun i _ => keys i
    verify₁ := by intros; rfl
    verify₂ := by intros; rfl
    visible := visible', zero := zero' }
  have empty := treeSim_futureEmpty_after fresh
    (treeStages_batch_peer_start_logged_frame prims K D base entries ρ
      (by intros; rfl) (fun i _ => labels₁ i) a u h.2.1)
  rw [steps₁, steps₂]
  change RelTriple
    ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (depth circs + 1) state
      (treeSimPeerPartial K D d.ctx₁ (fun _ => true) d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run u.2)
    ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (depth circs + 1) state
      (treeSimPeerPartial K D d.ctx₂ (fun _ => true) d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run z.2)
    (TreeStagesCheckReached K D A sched.circs (sched.ρ + depth circs))
  simpa only [layers, List.length_range] using
    sched.execute prims K D A layers d (fun _ => true) state u.2 z.2 h.1.2.1 empty

/-- The complete input-to-first-Coin segment for either configured mode,
using the protocol's actual per-layer round count. -/
theorem treeStages_input_runJobs_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, (ctx₁ i).self = i) (self₂ : ∀ i, (ctx₂ i).self = i)
    (keys : ∀ i, (ctx₁ i).prss = (ctx₂ i).prss)
    (parameter : PublicParameter) (openings : List (List (List Bit))) (batch : ℕ) (jobs : List Job)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (st₁ st₂ : C.Party → RunState C)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (ρ : ℕ) (labels₁ : ∀ i, (st₁ i).label = ρ) (labels₂ : ∀ i, (st₂ i).label = ρ)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (base : HashCache C)
    (covered₁ : ∀ i, TreeStagesPrfCovered base (ctx₁ i).keys.seed jobs)
    (covered₂ : ∀ i, TreeStagesPrfCovered base (ctx₂ i).keys.seed jobs)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : base ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run (st₁ i) >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (settings.mode.rounds * depth circs + 1) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter (ctx₂ i).keys.seed openings (ctx₂ i) batch jobs)
            circs inputs).run (st₂ i) >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (settings.mode.rounds * depth circs + 1) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + depth circs)) := by
  cases mode : settings.mode with
  | peer =>
    simpa only [mode, ReshareMode.rounds, Nat.one_mul] using
      treeStages_peer_input_runJobs_check prims K circuits settings D A state mode ctx₁ ctx₂ self₁ self₂ keys
        parameter openings batch jobs (by omega) st₁ st₂ finish₁ finish₂ ρ labels₁ labels₂ history states
        base covered₁ covered₂ past visible zero a b related grows fresh
  | collector =>
    simpa only [mode, ReshareMode.rounds] using
      treeStages_collector_input_runJobs_check prims K circuits settings D A state mode ctx₁ ctx₂ self₁ self₂ keys
        parameter openings batch jobs nonzero st₁ st₂ finish₁ finish₂ ρ labels₁ labels₂ history states
        base covered₁ covered₂ past visible zero a b related grows fresh

/-- For either reshare mode, an actual ceremony batch with dealt real keys,
dummy hidden seeds, common PRSS keys and reset histories reaches its first
check Coin. One finite padding result supplies all input coverage, even after
the dealer and adversary have populated the shared public cache. -/
theorem treeStages_ceremonyBatch_check (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (prss : C.Party → PrssKeys C)
    (openings : List (List (List Bit))) (batch ρ : ℕ) (jobs : List Job)
    (nonzero : (outputsOf (jobs.map (circuits parameter ·.kind))).length ≠ 0)
    (finish₁ finish₂ : C.Party → List (List Bit) × RunState C → PartyM C E RealSpec TreeOutput)
    (cache : HashCache C) (padded : Unit × HashCache C)
    (padding : padded ∈ support ((simulateQ (localAnswer prims)
      (treeStagesCeremonyPrfPadding seeds)).run cache))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (zero : TreeSimFutureZero ρ past) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel past a b) (grows : padded.2 ≤ a.1.1) (fresh : TreeSimFutureEmpty ρ a.1.2) :
    let dummy := fun T => if KnownTo D.1 T then seeds T else 0
    let ctx₁ := fun i => (⟨i, dealtKeys parameter seeds pairs i, prss i⟩ : Context C)
    let ctx₂ := fun i => (⟨i, ⟨parameter, dummy, fun _ => 0⟩, prss i⟩ : Context C)
    let st : RunState C := ⟨fun _ => [], ρ, batch⟩
    let circs := jobs.map (circuits parameter ·.kind)
    RelTriple
      ((do
        let steps ← simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₁ i))
          (runJobs K (realRunGadgets K (ctx₁ i) settings.mode) circs inputs).run st >>= finish₁ i))
        executeSteps (treeSimRealRoles prims D) D A noFunctionality (settings.mode.rounds * depth circs + 1) state steps).run a)
      ((do
        let steps ← simulateQ (streamWorld prims D) (startSteps worldRoles D (fun i => do
          let inputs ← jobs.mapM (inputShares (ctx₂ i))
          (runJobs K (treeSimGadgets K circuits settings D parameter dummy openings (ctx₂ i) batch jobs)
            circs inputs).run st >>= finish₂ i))
        executeSteps (treeSimIdealRoles prims D) D A noFunctionality (settings.mode.rounds * depth circs + 1) state steps).run b)
      (TreeStagesCheckReached K D A circs (ρ + depth circs)) := by
  intro dummy ctx₁ ctx₂ st circs
  obtain ⟨_, covered⟩ := treeStages_seedPadding_covered prims (0 :: C.terms.map seeds) cache padded padding
  have realCovered : ∀ i, TreeStagesPrfCovered padded.2 (ctx₁ i).keys.seed jobs := by
    intro i
    apply treeStages_seedsCovered_jobs padded.2 _ covered _ _ jobs
    intro T
    change (if i ∈ C.holders T then seeds T else 0) ∈ 0 :: C.terms.map seeds
    split_ifs <;> simp [Committee.terms]
  have idealCovered : ∀ i, TreeStagesPrfCovered padded.2 (ctx₂ i).keys.seed jobs := by
    intro i
    apply treeStages_seedsCovered_jobs padded.2 _ covered _ _ jobs
    intro T
    change (if KnownTo D.1 T then seeds T else 0) ∈ 0 :: C.terms.map seeds
    split_ifs <;> simp [Committee.terms]
  exact treeStages_input_runJobs_check prims K circuits settings D A state ctx₁ ctx₂
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    parameter openings batch jobs nonzero (fun _ => st) (fun _ => st) finish₁ finish₂
    ρ (by intros; rfl) (by intros; rfl) [] (fun i _ => ⟨rfl, rfl, treeSimHistoryRel_empty D i⟩)
    padded.2 realCovered idealCovered past visible zero a b related grows fresh

/-- The actual first-Coin hash and expansion queries of the check. -/
def treeStagesCheckExpansionQuery (tag label : ℕ) (values : List E) (count : ℕ) :
    OracleComp (RoSpec C) (List E) := do
  let key ← hashQuery (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v)))
  (List.range (coins count)).mapM fun k => elementOfHash K <$> hashQuery (.expand key k)

/-- Coverage is local to the actual Coin value and its resulting hash key. -/
def TreeStagesExpansionCovered (cache : HashCache C) (tag label : ℕ) (values : List E) (count : ℕ) : Prop :=
  ∃ key : HashOutput, cache (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))) = some key ∧
    ∀ k < coins count, ∃ h, cache (.expand key k) = some h

def treeStagesCachedExpansion (cache : HashCache C) (tag label : ℕ) (values : List E) (count : ℕ) : List E :=
  let key := (cache (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v)))).getD 0
  (List.range (coins count)).map fun k => elementOfHash K ((cache (.expand key k)).getD 0)

theorem treeStages_expansionCovered_mono {a b : HashCache C} (h : a ≤ b)
    (tag label : ℕ) (values : List E) (count : ℕ)
    (covered : TreeStagesExpansionCovered K a tag label values count) :
    TreeStagesExpansionCovered K b tag label values count := by
  obtain ⟨key, hk, expansions⟩ := covered
  refine ⟨key, h hk, ?_⟩
  intro k hk'
  obtain ⟨v, hv⟩ := expansions k hk'
  exact ⟨v, h hv⟩

theorem treeStages_cachedExpansion_mono {a b : HashCache C} (h : a ≤ b)
    (tag label : ℕ) (values : List E) (count : ℕ)
    (covered : TreeStagesExpansionCovered K a tag label values count) :
    treeStagesCachedExpansion K a tag label values count = treeStagesCachedExpansion K b tag label values count := by
  obtain ⟨key, hk, expansions⟩ := covered
  simp only [treeStagesCachedExpansion]
  rw [hk, h hk]
  simp only [Option.getD_some]
  apply List.map_congr_left
  intro k hk'
  obtain ⟨v, hv⟩ := expansions k (List.mem_range.mp hk')
  rw [hv, h hv]

/-- Replay of the actual check expansion preserves both caches. The logged
execution still records every original hash query. -/
theorem treeStages_checkExpansion_replay (D : C.Coalition) (tag label : ℕ) (values : List E) (count : ℕ)
    (cache : HashCache C × HiddenCache C)
    (covered : TreeStagesExpansionCovered K cache.1 tag label values count) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (treeStagesCheckExpansionQuery K tag label values count) (LocalSpec C)))).run cache =
      pure (treeStagesCachedExpansion K cache.1 tag label values count, cache) := by
  obtain ⟨key, hk, expansions⟩ := covered
  have queryEq (q : Query C) : simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C))) = onHash (hashAnswer prims q) := by
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  have cached (q : Query C) (random : ¬ IsFixed q) (v : HashOutput) (hv : cache.1 q = some v) :
      (simulateQ (streamWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C)))).run cache =
        pure (v, cache) := by
    rw [queryEq]
    simp [onHash, hashAnswer_run_cached prims random hv]
  unfold treeStagesCheckExpansionQuery
  simp only [liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind]
  rw [cached _ (by rintro ⟨_, heq, _⟩; cases heq) key hk, pure_bind]
  simp only [treeStagesCachedExpansion]
  rw [hk]
  simp only [Option.getD_some]
  apply treeStages_ro_mapM_replay prims D _ _ _ cache
  intro k hk'
  obtain ⟨v, hv⟩ := expansions k (List.mem_range.mp hk')
  apply treeStages_ro_map_replay prims D _ (elementOfHash K) _ cache
  simpa only [hv, Option.getD_some] using cached (.expand key k) (by rintro ⟨_, heq, _⟩; cases heq) v hv

/-- The complete remaining slice/halving/final-check program. -/
def treeStagesCheckFold (ctx : Context C) (τ : List E) (count : ℕ) (layers : List ℕ)
    (p : Shares C E × Shares C E × E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) : PartyM C E RealSpec TreeOutput :=
  ((do
    let p ← layers.foldlM (sliceStep K ctx (realCheckGadgets K ctx) τ count) p
    let p' ← (List.range (halvings count - sliceBits)).foldlM
      (halvingStep K ctx (realCheckGadgets K ctx) (sliceWidth count))
      (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
    finalStep K ctx (realCheckGadgets K ctx) p' : RunM C E RealSpec Unit).run st) >>= finish

def treeStagesCheckInitial (ctx : Context C) (tuples : List (Tuple C)) (τ : List E) :
    Shares C E × Shares C E × E :=
  let count := (tuples.map (·.count)).sum
  ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k),
    liftedPart tuples (·.y), conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)

/-- Separate the public expansion from the real private slice program,
retaining the original guard, absolute label and final saved caller. -/
theorem treeStages_check_expansion_factor (ctx : Context C) (tuples : List (Tuple C))
    (tag label : ℕ) (values : List E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesCheckAfterCoin K ctx tuples tag label finish (values, st) = (do
      let τ ← oracleStep (treeStagesCheckExpansionQuery K tag label values (tuples.map (·.count)).sum)
      require (∀ b < sliceBits, τ.getD b 0 ≠ 0)
      treeStagesCheckFold K ctx τ (tuples.map (·.count)).sum (List.range sliceBits)
        (treeStagesCheckInitial K ctx tuples τ) st finish) := by
  simp only [treeStagesCheckAfterCoin, treeStagesCheckExpansionQuery, treeStagesCheckFold,
    treeStagesCheckInitial, expand, StateT.run_bind, StateT.run_lift, oracleStep_bind,
    bind_assoc, pure_bind]

def treeStagesSliceProducts (τ : List E) (count j : ℕ) (p : Shares C E × Shares C E × E) :
    List (Product C E) :=
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  let rest := fun k => coinProduct τ 0 (sliceBits - 1 - j) (k / sliceWidth count)
  [.replicated (fun T k => rest k * p.1 T k) p.2.1 half,
    .replicated (fun T k => rest k * (p.1 T k + p.1 T (k + half)))
      (fun T k => p.2.1 T k + p.2.1 T (k + half)) half]

def treeStagesAfterSlice (ctx : Context C) (τ : List E) (count j : ℕ) (remaining : List ℕ)
    (p : Shares C E × Shares C E × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput := do
  let r ← (challenge K (realCheckGadgets K ctx)).run out.2
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  let t₀ := conv K ctx out.1 0
  let tInf := conv K ctx out.1 1
  let t₁ := (p.2.2 + t₀) / τ.getD (sliceBits - 1 - j) 0
  let fold := fun (v : Shares C E) T k => v T k + r.1 * (v T k + v T (k + half))
  treeStagesCheckFold K ctx τ count remaining
    (fold p.1, fold p.2.1, (1 + r.1) * t₀ + r.1 * t₁ + r.1 * (1 + r.1) * tInf) r.2 finish

/-- Every slice has the actual two-product ExtendMult followed by the
actual challenge and all remaining check code. -/
theorem treeStages_checkFold_cons (ctx : Context C) (τ : List E) (count j : ℕ) (remaining : List ℕ)
    (p : Shares C E × Shares C E × E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesCheckFold K ctx τ count (j :: remaining) p st finish =
      ((realCheckGadgets K ctx).extendMult (treeStagesSliceProducts τ count j p)).run st >>=
        treeStagesAfterSlice K ctx τ count j remaining p finish := by
  simp only [treeStagesCheckFold, List.foldlM_cons, sliceStep, treeStagesSliceProducts,
    StateT.run_bind, StateT.run_pure, treeStagesAfterSlice, bind_assoc, pure_bind]
  apply bind_congr
  intro out
  simp only [treeStagesAfterSlice, treeStagesCheckFold, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]

/-- Field draws preserve any previously covered public-cache prefix. This
lets later honest parties replay the same check expansion after earlier
parties have already drawn their field masks. -/
theorem treeStages_fieldDraws_base (D : C.Coalition) (label idx count : ℕ)
    (delta : KeyName C → Fin count → E)
    (visible : ∀ name, ¬ Hidden D name → delta name = 0)
    (base₁ base₂ : HiddenCache C) (base : HashCache C) :
    TreeStagesFieldDraws prims K D label idx count delta
      (fun a b => TreeStagesFieldRel K D label idx count delta base₁ base₂ a b ∧ base ≤ a.1.1) := by
  intro name key a b h
  apply relTriple_post_mono (treeSim_relTriple_support
    (treeStages_fieldDraws_closed prims K D label idx count delta visible base₁ base₂ name key a b h.1))
  intro u z hu
  exact ⟨hu.1.1, hu.1.2, h.2.trans (treeSim_logged_grows prims D _ a u hu.2.1)⟩

/-- The actual public expansion and rejection, followed by the field draw
and peer exchange. Values and continuations may depend on the expansion. -/
def treeStagesExpansionPeerProgram (ctx : Context C) (tag hashLabel : ℕ)
    (values : List E) (tupleCount idx count : ℕ) (v : List E → ℕ → E)
    (st : RunState C) (k : List E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput) :
    PartyM C E RealSpec TreeOutput := do
  let τ ← oracleStep (treeStagesCheckExpansionQuery K tag hashLabel values tupleCount)
  require (∀ b < sliceBits, τ.getD b 0 ≠ 0)
  ((prssRandomness ctx (elementCodec K) idx count >>= fun rnd =>
    reshare K ctx (elementCodec K) rnd (v τ) count).run st) >>= k τ

/-- Replay the real expansion before entering the field gadget. The
rejected branch stops both parties; the accepted branch retains the original
saved check continuation and the coherent field-cache invariant. -/
theorem treeStages_expansion_field_entry (D : C.Coalition)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (tag hashLabel tupleCount label idx count : ℕ) (values : List E)
    (v₁ v₂ : List E → ℕ → E) (st₁ st₂ : RunState C)
    (lab₁ : st₁.label = label) (lab₂ : st₂.label = label)
    (k₁ k₂ : List E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (delta : KeyName C → Fin count → E)
    (visible : ∀ name, ¬ Hidden D name → delta name = 0)
    (base₁ base₂ : HiddenCache C) (base : HashCache C)
    (covered : TreeStagesExpansionCovered K base tag hashLabel values tupleCount)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeStagesFieldRel K D label idx count delta base₁ base₂ a b) (base_le : base ≤ a.1.1) :
    let τ := treeStagesCachedExpansion K base tag hashLabel values tupleCount
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        (treeStagesExpansionPeerProgram K ctx₁ tag hashLabel values tupleCount idx count v₁ st₁ k₁).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        (treeStagesExpansionPeerProgram K ctx₂ tag hashLabel values tupleCount idx count v₂ st₂ k₂).run))).run b)
      (fun u z => (∃ rnd,
        u.1 = (if ∀ j < sliceBits, τ.getD j 0 ≠ 0 then
          treeSimPeerStep K ctx₁ (elementCodec K) rnd (v₁ τ) count st₁ (k₁ τ) else .done none) ∧
        z.1 = (if ∀ j < sliceBits, τ.getD j 0 ≠ 0 then
          treeSimPeerStep K ctx₂ (elementCodec K)
            (rnd + treeStagesPrssFieldShift ctx₁ count delta) (v₂ τ) count st₂ (k₂ τ) else .done none)) ∧
        TreeStagesFieldRel K D label idx count delta base₁ base₂ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  have base_le₂ : base ≤ b.1 := by rw [← h.1]; exact base_le
  have replay₁ := treeStages_checkExpansion_replay prims K D tag hashLabel values tupleCount a.1
    (treeStages_expansionCovered_mono K base_le _ _ _ _ covered)
  have replay₂ := treeStages_checkExpansion_replay prims K D tag hashLabel values tupleCount b
    (treeStages_expansionCovered_mono K base_le₂ _ _ _ _ covered)
  rw [← treeStages_cachedExpansion_mono K base_le _ _ _ _ covered] at replay₁
  rw [← treeStages_cachedExpansion_mono K base_le₂ _ _ _ _ covered] at replay₂
  unfold treeStagesExpansionPeerProgram
  simp only [advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeStages_readOnly_pair prims D _ _ a b _ _ replay₁ replay₂)
  intro u z hu
  rw [hu.1, hu.2.1]
  have h' : TreeStagesFieldRel K D label idx count delta base₁ base₂ u.2 z.2 := by
    simpa only [TreeStagesFieldRel, hu.2.2.1, hu.2.2.2] using h
  have le' : base ≤ u.2.1.1 := by rw [hu.2.2.1]; exact base_le
  rw [advance_require_bind, advance_require_bind]
  split_ifs with good
  · exact treeStages_field_peer_entry prims K D ctx₁ ctx₂ self keys label idx count _ _ st₁ st₂
      lab₁ lab₂ _ _ delta _ (treeStages_fieldDraws_base prims K D label idx count delta visible base₁ base₂ base)
      u.2 z.2 ⟨h', le'⟩
  · simp only [free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨⟨0, rfl, rfl⟩, h', le'⟩

/-- Honest parties rejected by the expansion guard join the existing
aborted parties before the first slice exchange. -/
def treeStagesExpansionLive (base : HashCache C) (tag hashLabel tupleCount : C.Party → ℕ)
    (values : C.Party → List E) (out : C.Party → Option Unit) (i : C.Party) : Bool :=
  (out i).isSome && decide (∀ j < sliceBits,
    (treeStagesCachedExpansion K base (tag i) (hashLabel i) (values i) (tupleCount i)).getD j 0 ≠ 0)

/-- Compose the actual expansions, guards and field PRSS entries in driver
order. Each later holder replays the same covered hash values, while encoded
field blocks remain coherent across all earlier holders. -/
theorem treeStages_expansion_field_partial (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (out : C.Party → Option Unit) (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (tag hashLabel tupleCount : C.Party → ℕ) (values : C.Party → List E)
    (label idx count : ℕ) (v₁ v₂ : C.Party → List E → ℕ → E)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → List E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E)
    (base₁ base₂ : HiddenCache C) (base : HashCache C)
    (covered : ∀ i, out i = some () → TreeStagesExpansionCovered K base (tag i) (hashLabel i) (values i) (tupleCount i))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeStagesFieldRel K D label idx count (treeStagesMaskDelta D count dt dp) base₁ base₂ a b)
    (base_le : base ≤ a.1.1) :
    let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) (values i) (tupleCount i)
    let live := treeStagesExpansionLive K base tag hashLabel tupleCount values out
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        treeStagesExpansionPeerProgram K (ctx₁ i) (tag i) (hashLabel i) (values i) (tupleCount i)
          idx count (v₁ i) (st₁ i) (k₁ i)) out)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        treeStagesExpansionPeerProgram K (ctx₂ i) (tag i) (hashLabel i) (values i) (tupleCount i)
          idx count (v₂ i) (st₂ i) (k₂ i)) out)).run b)
      (fun u z => (∃ rnd,
        u.1 = treeSimExtendMultPartial K D ctx₁ live count rnd (fun i => v₁ i (τ i)) st₁ (fun i => k₁ i (τ i)) ∧
        z.1 = treeSimExtendMultPartial K D ctx₂ live count
          (fun i => rnd i + frandShare D count 0 0 dt dp i) (fun i => v₂ i (τ i)) st₂ (fun i => k₂ i (τ i))) ∧
        TreeStagesFieldRel K D label idx count (treeStagesMaskDelta D count dt dp) base₁ base₂ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) (values i) (tupleCount i)
  let live := treeStagesExpansionLive K base tag hashLabel tupleCount values out
  let J := fun a b => TreeStagesFieldRel K D label idx count (treeStagesMaskDelta D count dt dp) base₁ base₂ a b ∧ base ≤ a.1.1
  let Q := fun i x y => ∃ rnd : PrssOutput C E,
    x = treeSimExtendMultPartial K D ctx₁ live count (fun _ => rnd) (fun i => v₁ i (τ i)) st₁ (fun i => k₁ i (τ i)) i ∧
    y = treeSimExtendMultPartial K D ctx₂ live count
      (fun j => rnd + frandShare D count 0 0 dt dp j) (fun i => v₂ i (τ i)) st₂ (fun i => k₂ i (τ i)) i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ out out J Q ?_ a b ⟨h, base_le⟩)
  · intro u z hu
    choose rnd h₁ h₂ using hu.1
    exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩
  · intro i s t hst
    cases ho : out i with
    | none =>
      simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨0, ?_, ?_⟩, hst⟩ <;>
        simp [treeSimExtendMultPartial, live, treeStagesExpansionLive, ho]
    | some x =>
      cases x
      have hi : i ∉ D.1 := fun hi => by simpa [ho] using corrupt i hi
      simp only [treeSimResume]
      apply relTriple_post_mono (treeStages_expansion_field_entry prims K D (ctx₁ i) (ctx₂ i)
        ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi)
        (tag i) (hashLabel i) (tupleCount i) label idx count (values i) (v₁ i) (v₂ i) (st₁ i) (st₂ i)
        (lab₁ i hi) (lab₂ i hi) (k₁ i) (k₂ i) (treeStagesMaskDelta D count dt dp)
        (treeStagesMaskDelta_visible D count dt dp) base₁ base₂ base (covered i ho) s t hst.1 hst.2)
      intro u z hu
      obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
      have hs : treeStagesPrssFieldShift (ctx₁ i) count (treeStagesMaskDelta D count dt dp) =
          frandShare D count 0 0 dt dp i := by
        rw [treeStages_prssFieldShift_mask D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
      refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
      · simpa [treeSimExtendMultPartial, live, treeStagesExpansionLive, ho, treeSimExtendMultWaiting, hi, τ] using hu
      · simpa [treeSimExtendMultPartial, live, treeStagesExpansionLive, ho, treeSimExtendMultWaiting, hi, τ, hs] using hz

/-- The first slice has exactly two actual products, regardless of the
number of checked tuples. -/
def treeStagesCheckFirstValue (ctx : Context C) (tuples : List (Tuple C)) (τ : List E) : ℕ → E :=
  contextProductValues K ctx (treeStagesSliceProducts τ (tuples.map (·.count)).sum 0
    (treeStagesCheckInitial K ctx tuples τ))

def treeStagesCheckFirstCont (ctx : Context C) (tuples : List (Tuple C))
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) (τ : List E) :
    Shares C E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesAfterSlice K ctx τ (tuples.map (·.count)).sum 0 ((List.range sliceBits).drop 1)
    (treeStagesCheckInitial K ctx tuples τ) finish

/-- Exact entry to the first slice of the frozen check, including all
expansion queries and the zero-coefficient rejection. -/
theorem treeStages_check_firstSlice_program (ctx : Context C) (tuples : List (Tuple C))
    (tag hashLabel : ℕ) (values : List E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesCheckAfterCoin K ctx tuples tag hashLabel finish (values, st) =
      treeStagesExpansionPeerProgram K ctx tag hashLabel values (tuples.map (·.count)).sum 0 2
        (treeStagesCheckFirstValue K ctx tuples) st (treeStagesCheckFirstCont K ctx tuples finish) := by
  rw [treeStages_check_expansion_factor]
  unfold treeStagesExpansionPeerProgram
  apply bind_congr
  intro τ
  apply bind_congr
  intro _
  have range : List.range sliceBits = 0 :: (List.range sliceBits).drop 1 := rfl
  rw [range, treeStages_checkFold_cons, treeStages_extendMult_program K _ _ 2 (by rfl)]
  rfl

/-- Keep optional outputs exactly, while totalizing their saved values for
the subsequent boundary data. Aborted outputs execute no continuation. -/
theorem treeStages_resumeAll_getD {α β : Type} (k : C.Party → β → PartyM C E RealSpec α)
    (out : C.Party → Option β) (fallback : C.Party → β) :
    treeSimResumeAll k out = treeSimResumeAll
      (fun i (_ : Unit) => k i ((out i).getD (fallback i))) (fun i => (out i).map fun _ => ()) := by
  unfold treeSimResumeAll
  congr 2
  funext i
  cases ho : out i <;> simp [treeSimResume, ho]

/-- The actual first check slice constructs its full adaptive GS20 boundary
from encoded PRSS masks. Coin failures and zero expansion coefficients are
retained as stopped parties. The continuation is the remaining real check. -/
theorem treeStages_check_firstSlice_start (D : C.Coalition)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (tuples₁ tuples₂ : C.Party → List (Tuple C))
    (counts : ∀ i, ((tuples₁ i).map (·.count)).sum = ((tuples₂ i).map (·.count)).sum)
    (tag hashLabel : C.Party → ℕ) (out : C.Party → Option (List E))
    (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (label : ℕ) (future : TreeSimFutureZero (label + 1) old)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (base : HashCache C)
    (covered : ∀ i values, out i = some values →
      TreeStagesExpansionCovered K base (tag i) (hashLabel i) values ((tuples₁ i).map (·.count)).sum)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty label a.1.2) (base_le : base ≤ a.1.1) :
    let values := fun i => (out i).getD []
    let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) (values i) ((tuples₁ i).map (·.count)).sum
    let live := treeStagesExpansionLive K base tag hashLabel (fun i => ((tuples₁ i).map (·.count)).sum)
      values (fun i => (out i).map fun _ => ())
    let v₁ := fun i => treeStagesCheckFirstValue K (ctx₁ i) (tuples₁ i) (τ i)
    let v₂ := fun i => treeStagesCheckFirstValue K (ctx₂ i) (tuples₂ i) (τ i)
    let k₁ := fun i => treeStagesCheckFirstCont K (ctx₁ i) (tuples₁ i) (finish₁ i) (τ i)
    let k₂ := fun i => treeStagesCheckFirstCont K (ctx₂ i) (tuples₂ i) (finish₂ i) (τ i)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i values =>
        treeStagesCheckAfterCoin K (ctx₁ i) (tuples₁ i) (tag i) (hashLabel i) (finish₁ i) (values, st₁ i)) out)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i values =>
        treeStagesCheckAfterCoin K (ctx₂ i) (tuples₂ i) (tag i) (hashLabel i) (finish₂ i) (values, st₂ i)) out)).run b)
      (fun u z => ∃ rnd δ,
        let d := treeStagesExtendMultData K D T₀ pivotParty pivot δ 2 ctx₁ ctx₂ self₁ self₂ rnd v₁ v₂ st₁ st₂ k₁ k₂
        u.1 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        z.1 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) ∧
        TreeSimFutureZero (label + 1) d.δ ∧ TreeSimFutureEmpty (label + 1) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 1) z.2.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  let values := fun i => (out i).getD []
  let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) (values i) ((tuples₁ i).map (·.count)).sum
  let v₁ := fun i => treeStagesCheckFirstValue K (ctx₁ i) (tuples₁ i) (τ i)
  let v₂ := fun i => treeStagesCheckFirstValue K (ctx₂ i) (tuples₂ i) (τ i)
  let dt := termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin 2 → E)
  let dp := pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin 2 → E))
  let delta := treeStagesMaskDelta D 2 dt dp
  have fresh₂ := treeSim_futureEmpty_related fresh h.2
  have initial : TreeStagesFieldRel K D label 0 2 delta a.1.2 b.2 a b :=
    ⟨h.1, treeStages_fieldCaches_initial K D label 0 2 delta _ _ fresh fresh₂⟩
  rw [treeStages_resumeAll_getD _ out (fun _ => []), treeStages_resumeAll_getD _ out (fun _ => [])]
  simp only [treeStages_check_firstSlice_program, ← counts]
  apply relTriple_post_mono (treeStages_expansion_field_partial prims K D ctx₁ ctx₂ self₁ self₂ keys
    (fun i => (out i).map fun _ => ()) (by intro i hi; simp [corrupt i hi]) tag hashLabel
    (fun i => ((tuples₁ i).map (·.count)).sum) values label 0 2
    (fun i => treeStagesCheckFirstValue K (ctx₁ i) (tuples₁ i))
    (fun i => treeStagesCheckFirstValue K (ctx₂ i) (tuples₂ i)) st₁ st₂ lab₁ lab₂
    (fun i => treeStagesCheckFirstCont K (ctx₁ i) (tuples₁ i) (finish₁ i))
    (fun i => treeStagesCheckFirstCont K (ctx₂ i) (tuples₂ i) (finish₂ i))
    dt dp a.1.2 b.2 base ?_ a b initial base_le)
  · intro u z hu
    obtain ⟨⟨rnd, hu, hz⟩, hc, le⟩ := hu
    let δ := treeStagesFieldCacheDelta D label 0 2 old u.2.1.2 z.2.2
    refine ⟨rnd, δ, hu, hz, ⟨hc.1, ?_⟩, ?_, ?_, ?_, ?_, le⟩
    · exact treeStages_fieldCaches_related K D label 0 2 delta old _ _ _ _ hc.2 h.2
    · exact treeStages_fieldCacheDelta_visible D label 0 2 old _ _ visible
    · exact treeStages_fieldCacheDelta_future D label 0 2 old _ _ future
    · exact (treeStages_fieldCaches_future K D label 0 2 delta _ _ _ _ hc.2 fresh fresh₂).1
    · exact (treeStages_fieldCaches_future K D label 0 2 delta _ _ _ _ hc.2 fresh fresh₂).2
  · intro i hi
    cases ho : out i with
    | none => simp [ho] at hi
    | some vs => simpa [values, ho] using covered i vs ho

/-- Finite padding for the check Coin and expansion hashes. It includes
all possible opened field vectors and hash outputs at the supplied schedule;
existing dealer cache entries are retained. -/
def treeStagesCheckPaddingQueries (tagLabels : List (ℕ × ℕ)) (tupleCounts : List ℕ) (coinCount : ℕ) : List (Query C) :=
  (tagLabels.flatMap fun tl => (Finset.univ : Finset (Fin coinCount → E)).toList.map fun vs =>
    Query.coinKey tl.1 tl.2 ((List.ofFn vs).flatMap fun v => List.ofFn (K.encode v))) ++
  ((Finset.univ : Finset HashOutput).toList.flatMap fun key => tupleCounts.flatMap fun count =>
    (List.range (coins count)).map (Query.expand key))

def treeStagesCheckPadding (tagLabels : List (ℕ × ℕ)) (tupleCounts : List ℕ) (coinCount : ℕ) :
    OracleComp (LocalSpec C) Unit := do
  let _ ← (treeStagesCheckPaddingQueries K tagLabels tupleCounts coinCount).mapM fun q =>
    liftComp (hashQuery q) (LocalSpec C)
  pure ()

theorem treeStages_checkPadding_covered (tagLabels : List (ℕ × ℕ)) (tupleCounts : List ℕ) (coinCount : ℕ)
    (cache : HashCache C) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (treeStagesCheckPadding K tagLabels tupleCounts coinCount)).run cache)) :
    cache ≤ r.2 ∧ ∀ tag label, (tag, label) ∈ tagLabels → ∀ count ∈ tupleCounts,
      ∀ values : List E, values.length = coinCount → TreeStagesExpansionCovered K r.2 tag label values count := by
  simp only [treeStagesCheckPadding, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  obtain ⟨grows, covered⟩ := treeStages_prefetch_queries prims _ (by
    intro q hq
    simp only [treeStagesCheckPaddingQueries, List.mem_append, List.mem_flatMap, List.mem_map] at hq
    rcases hq with ⟨tl, _, vs, _, rfl⟩ | ⟨key, _, count, _, k, _, rfl⟩ <;>
      rintro ⟨_, heq, _⟩ <;> cases heq) cache u hu
  refine ⟨grows, ?_⟩
  intro tag label htl count hcount values hlen
  have hvalues : List.ofFn (fun i : Fin coinCount => values[i.val]'(by omega)) = values := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp
  obtain ⟨key, hkey⟩ := covered (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))) (by
    apply List.mem_append_left
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨(tag, label), htl, (fun i : Fin coinCount => values[i.val]'(by omega)), ?_, ?_⟩
    · simp
    · rw [hvalues])
  refine ⟨key, hkey, ?_⟩
  intro k hk
  apply covered
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨key, by simp, count, hcount, k, List.mem_range.mpr hk, rfl⟩

/-- Successful real Coin openings have the requested length, including
malformed adversarial replies that pass the actual decoder. -/
theorem treeStages_coinOutput_length (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E) (i : C.Party)
    (values : List E) (h : treeSimCoinOutput K D count rnd sent i = some values) : values.length = count := by
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinOutput, hi] at h
  · simp only [treeSimCoinOutput, if_neg hi] at h
    unfold coinRes at h
    split_ifs at h
    obtain ⟨v, _, hv⟩ := Option.map_eq_some_iff.mp h
    subst values
    simp [vector]

/-- Mapping the recorded Coin state into its continuation does not change
the actual optional-output traversal. -/
theorem treeStages_resumeAll_map {α β γ : Type}
    (k : C.Party → γ → PartyM C E RealSpec α) (f : C.Party → β → γ) (out : C.Party → Option β) :
    treeSimResumeAll k (fun i => (out i).map (f i)) = treeSimResumeAll (fun i x => k i (f i x)) out := by
  unfold treeSimResumeAll
  congr 2
  funext i
  cases ho : out i <;> simp [treeSimResume, ho]

/-- One complete rushing Coin round through the actual expansion hashes,
zero guard and first slice field masks. The resulting boundary keeps the
original products and the entire remaining check continuation. -/
theorem treeStages_check_coin_firstSlice_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (tuples₁ tuples₂ : C.Party → List (Tuple C))
    (counts : ∀ i, ((tuples₁ i).map (·.count)).sum = ((tuples₂ i).map (·.count)).sum)
    (tag hashLabel : C.Party → ℕ) (label : ℕ) (future : TreeSimFutureZero (label + 2) old)
    (coinRnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      TreeStagesExpansionCovered K base (tag i) (hashLabel i) values ((tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCoinWaiting K D 1 coinRnd st₁ (fun i =>
          treeStagesCheckAfterCoin K (ctx₁ i) (tuples₁ i) (tag i) (hashLabel i) (finish₁ i)))).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCoinWaiting K D 1 coinRnd st₂ (fun i =>
          treeStagesCheckAfterCoin K (ctx₂ i) (tuples₂ i) (tag i) (hashLabel i) (finish₂ i)))).run b)
      (fun u z => ∃ sent rnd δ,
        let out := treeSimCoinOutput K D 1 coinRnd sent
        let values := fun i => (out i).getD []
        let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) (values i) ((tuples₁ i).map (·.count)).sum
        let live := treeStagesExpansionLive K base tag hashLabel (fun i => ((tuples₁ i).map (·.count)).sum)
          values (fun i => (out i).map fun _ => ())
        let d := treeStagesExtendMultData K D T₀ pivotParty pivot δ 2 ctx₁ ctx₂ self₁ self₂ rnd
          (fun i => treeStagesCheckFirstValue K (ctx₁ i) (tuples₁ i) (τ i))
          (fun i => treeStagesCheckFirstValue K (ctx₂ i) (tuples₂ i) (τ i))
          (fun i => nextLabel (st₁ i)) (fun i => nextLabel (st₂ i))
          (fun i => treeStagesCheckFirstCont K (ctx₁ i) (tuples₁ i) (finish₁ i) (τ i))
          (fun i => treeStagesCheckFirstCont K (ctx₂ i) (tuples₂ i) (finish₂ i) (τ i))
        u.1.1 = z.1.1 ∧ u.1.2.2 = sent ∧ z.1.2.2 = sent ∧
        u.1.2.1 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        z.1.2.1 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) ∧
        TreeSimFutureZero (label + 2) d.δ ∧ TreeSimFutureEmpty (label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 2) z.2.2 ∧ base ≤ u.2.1.1) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [treeSim_coin_round_factor, treeSim_coin_round_factor]
  simp only [treeStages_resumeAll_map, simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D old _ a b h))
  intro r₁ r₂ hr
  rw [hr.1.1]
  have fresh' : TreeSimFutureEmpty (label + 1) r₁.2.1.2 := by
    rw [hr.1.2.2.1]
    exact fresh
  have le' : base ≤ r₁.2.1.1 := base_le.trans (treeSim_logged_grows prims D _ a r₁ hr.2.1)
  apply relTriple_bind (treeStages_check_firstSlice_start prims K D T₀ pivotParty pivot old visible
    ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ counts tag hashLabel
    (treeSimCoinOutput K D 1 coinRnd r₂.1.2) (by intro i hi; simp [treeSimCoinOutput, hi])
    (label + 1) future (fun i => nextLabel (st₁ i)) (fun i => nextLabel (st₂ i))
    (by intro i hi; change (st₁ i).label + 1 = label + 1; rw [lab₁ i hi])
    (by intro i hi; change (st₂ i).label + 1 = label + 1; rw [lab₂ i hi])
    finish₁ finish₂ base (by
      intro i values ho
      exact covered i values (treeStages_coinOutput_length K D 1 coinRnd r₂.1.2 i values ho))
    r₁.2 r₂.2 hr.1.2.1 fresh' le')
  intro u z hu
  obtain ⟨rnd, δ, hu, hz, caches, visible', future', fresh₁, fresh₂, le⟩ := hu
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨r₂.1.2, rnd, δ, rfl, rfl, rfl, hu, hz, caches, visible', future', fresh₁, fresh₂, le⟩

/-- A partially active field exchange executes its actual next driver
step, including early termination, propagation of earlier aborts, and entry
to the saved Coin. No continuation-coupling hypothesis is used. -/
theorem treeStages_extendMult_coin_execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimExtendMultData K D)
    (label count : ℕ) (visible : ∀ x, ¬ Hidden D x.1.1 → d.δ x = 0)
    (future : TreeSimFutureZero (label + 1) d.δ)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (lab₁ : ∀ i, i ∉ D.1 → (d.st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (d.st₂ i).label = label)
    (next₁ next₂ : C.Party → (Shares C E × RunState C) → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (program₁ : ∀ i x, d.k₁ i x = ((realCheckGadgets K (d.ctx₁ i)).coin count).run x.2 >>= next₁ i x)
    (program₂ : ∀ i x, d.k₂ i x = ((realCheckGadgets K (d.ctx₂ i)).coin count).run x.2 >>= next₂ i x)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel d.δ a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 1 state
        (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 1 state
        (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ TreeSimStreamRel d.δ u.2 z.2 ∧
        TreeSimFutureZero (label + 2) d.δ ∧ TreeSimFutureEmpty (label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 2) z.2.2 ∧
        ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
          ∃ sent rnd,
            let n := treeStages_extendMult_coinNext K D d sent label count keys lab₁ lab₂ next₁ next₂ program₁ program₂
            u.1.2 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
            z.1.2 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂)) := by
  by_cases noneLive : ∀ i, i ∉ D.1 → live i ≠ true
  · have left : treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
      · simp [treeSimExtendMultPartial, noneLive i hi]
    have right : treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
      · simp [treeSimExtendMultPartial, noneLive i hi]
    rw [left, right]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, h, (fun x hx => future x (by omega)),
      (fun x hx => fresh x (by omega)),
      (fun x hx => treeSim_futureEmpty_related fresh h.2 x (by omega)), Or.inl ⟨rfl, rfl⟩⟩
  · push_neg at noneLive
    obtain ⟨i, hi, hl⟩ := noneLive
    have active₁ : ¬ AllDone D (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) := by
      intro done
      have hh := done i hi
      simpa [treeSimExtendMultPartial, treeSimExtendMultWaiting, treeSimPeerStep, hi, hl] using hh
    have active₂ : ¬ AllDone D (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
      intro done
      have hh := done i hi
      simpa [treeSimExtendMultPartial, treeSimExtendMultWaiting, treeSimPeerStep, hi, hl] using hh
    simp only [AllDone] at active₁ active₂
    simp only [executeSteps, if_neg active₁, if_neg active₂, StateT.run_bind]
    by_cases allLive : ∀ i, i ∉ D.1 → live i = true
    · have left : treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ =
          treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ := by
        funext i
        by_cases hi : i ∈ D.1
        · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
        · simp [treeSimExtendMultPartial, allLive i hi]
      have right : treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ =
          treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ := by
        funext i
        by_cases hi : i ∈ D.1
        · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
        · simp [treeSimExtendMultPartial, allLive i hi]
      rw [left, right]
      apply relTriple_bind (treeStages_extendMult_coin_round prims K D A d label count visible future keys
        lab₁ lab₂ next₁ next₂ program₁ program₂ state a b h fresh)
      intro u z hu
      obtain ⟨sent, rnd, same, _, _, left, right, caches, zero, fresh₁, fresh₂⟩ := hu
      exact relTriple_pure_pure ⟨same, caches, zero, fresh₁, fresh₂, Or.inr ⟨sent, rnd, left, right⟩⟩
    · push_neg at allLive
      apply relTriple_bind (treeStages_extendMult_partial_round prims K D A d live allLive state a b h)
      intro u z hu
      obtain ⟨same, left, right, caches, frame₁, frame₂⟩ := hu
      exact relTriple_pure_pure ⟨same, caches, (fun x hx => future x (by omega)),
        (by rw [frame₁]; exact fun x hx => fresh x (by omega)),
        (by rw [frame₂]; exact fun x hx => treeSim_futureEmpty_related fresh h.2 x (by omega)), Or.inl ⟨left, right⟩⟩

/-- Deterministic slice fold after its challenge. The full halving and
final-check suffix is retained by `treeStagesCheckFold`. -/
def treeStagesSliceBody (ctx : Context C) (τ : List E) (count j : ℕ) (remaining : List ℕ)
    (p : Shares C E × Shares C E × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E × RunState C) : PartyM C E RealSpec TreeOutput :=
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  let t₀ := conv K ctx out.1 0
  let tInf := conv K ctx out.1 1
  let t₁ := (p.2.2 + t₀) / τ.getD (sliceBits - 1 - j) 0
  let fold := fun (v : Shares C E) T k => v T k + r.1 * (v T k + v T (k + half))
  treeStagesCheckFold K ctx τ count remaining
    (fold p.1, fold p.2.1, (1 + r.1) * t₀ + r.1 * t₁ + r.1 * (1 + r.1) * tInf) r.2 finish

theorem treeStages_afterSlice_coin (ctx : Context C) (τ : List E) (count j : ℕ) (remaining : List ℕ)
    (p : Shares C E × Shares C E × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) (out : Shares C E × RunState C) :
    treeStagesAfterSlice K ctx τ count j remaining p finish out =
      ((realCheckGadgets K ctx).coin 1).run out.2 >>=
        treeStagesChallengeTail K out.2.tag out.2.label (treeStagesSliceBody K ctx τ count j remaining p finish out) :=
  treeStages_challenge_prefix K ctx out.2 (treeStagesSliceBody K ctx τ count j remaining p finish out)

/-- The real first-slice products and saved fold instantiate the generic
ExtendMult/challenge transition without any algebraic or coupling premise. -/
def treeStagesFirstSliceChallenge (D : C.Coalition)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (tuples₁ tuples₂ : C.Party → List (Tuple C)) (τ : C.Party → List E)
    (label : ℕ) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    TreeStagesExtendMultChallenge K D where
  T₀ := T₀
  pivotParty := pivotParty
  pivot := pivot
  label := label + 1
  count := 2
  ctx₁ := ctx₁
  ctx₂ := ctx₂
  self₁ := self₁
  self₂ := self₂
  keys := keys
  products₁ := fun i => treeStagesSliceProducts (τ i) ((tuples₁ i).map (·.count)).sum 0
    (treeStagesCheckInitial K (ctx₁ i) (tuples₁ i) (τ i))
  products₂ := fun i => treeStagesSliceProducts (τ i) ((tuples₂ i).map (·.count)).sum 0
    (treeStagesCheckInitial K (ctx₂ i) (tuples₂ i) (τ i))
  len₁ := by intros; rfl
  len₂ := by intros; rfl
  st₁ := fun i => nextLabel (st₁ i)
  st₂ := fun i => nextLabel (st₂ i)
  lab₁ := by intro i hi; change (st₁ i).label + 1 = label + 1; rw [lab₁ i hi]
  lab₂ := by intro i hi; change (st₂ i).label + 1 = label + 1; rw [lab₂ i hi]
  body₁ := fun i => treeStagesSliceBody K (ctx₁ i) (τ i) ((tuples₁ i).map (·.count)).sum 0
    ((List.range sliceBits).drop 1) (treeStagesCheckInitial K (ctx₁ i) (tuples₁ i) (τ i)) (finish₁ i)
  body₂ := fun i => treeStagesSliceBody K (ctx₂ i) (τ i) ((tuples₂ i).map (·.count)).sum 0
    ((List.range sliceBits).drop 1) (treeStagesCheckInitial K (ctx₂ i) (tuples₂ i) (τ i)) (finish₂ i)

/-- Execute the actual partial ExtendMult boundary of a reduction step.
Its successor records the precise optional outputs and next challenge Coin. -/
theorem TreeStagesExtendMultChallenge.execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesExtendMultChallenge K D)
    (rnd : C.Party → PrssOutput C E) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (future : TreeSimFutureZero (p.label + 1) δ)
    (live : C.Party → Bool) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel δ a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2) :
    let d := p.data K D rnd δ
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 1 state
        (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 1 state
        (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧
        TreeSimFutureZero (p.label + 2) δ ∧ TreeSimFutureEmpty (p.label + 2) u.2.1.2 ∧
        TreeSimFutureEmpty (p.label + 2) z.2.2 ∧
        ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
          ∃ sent coinRnd,
            let n := p.coinNext K D rnd δ sent
            u.1.2 = treeSimCoinPartial K D n.live n.count coinRnd n.st₁ n.next₁ ∧
            z.1.2 = treeSimCoinPartial K D n.live n.count coinRnd n.st₂ n.next₂)) :=
  treeStages_extendMult_coin_execute prims K D A (p.data K D rnd δ) p.label 1 visible future p.keys p.lab₁ p.lab₂
    (p.next₁ K D) (p.next₂ K D)
    (fun i x => treeStages_challenge_prefix K (p.ctx₁ i) x.2 (p.body₁ i x))
    (fun i x => treeStages_challenge_prefix K (p.ctx₂ i) x.2 (p.body₂ i x)) live state a b h fresh

/-- Two actual ceremony-driver rounds, from the first check Coin through
the first slice exchange into its challenge Coin. Abort propagation and early
termination are included, with the exact remaining real check retained. -/
theorem treeStages_firstCheck_two_rounds (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (tuples₁ tuples₂ : C.Party → List (Tuple C))
    (counts : ∀ i, ((tuples₁ i).map (·.count)).sum = ((tuples₂ i).map (·.count)).sum)
    (tag hashLabel : C.Party → ℕ) (label : ℕ) (future : TreeSimFutureZero (label + 2) old)
    (coinRnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      TreeStagesExpansionCovered K base (tag i) (hashLabel i) values ((tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinWaiting K D 1 coinRnd st₁ (fun i =>
          treeStagesCheckAfterCoin K (ctx₁ i) (tuples₁ i) (tag i) (hashLabel i) (finish₁ i)))).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinWaiting K D 1 coinRnd st₂ (fun i =>
          treeStagesCheckAfterCoin K (ctx₂ i) (tuples₂ i) (tag i) (hashLabel i) (finish₂ i)))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ ∃ sent rnd δ,
        let out := treeSimCoinOutput K D 1 coinRnd sent
        let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) ((out i).getD []) ((tuples₁ i).map (·.count)).sum
        let p := treeStagesFirstSliceChallenge K D T₀ pivotParty pivot ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ τ
          label st₁ st₂ lab₁ lab₂ finish₁ finish₂
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (label + 3) δ ∧ TreeSimFutureEmpty (label + 3) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 3) z.2.2 ∧
        ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
          ∃ sent' challengeRnd,
            let n := p.coinNext K D rnd δ sent'
            u.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₁ n.next₁ ∧
            z.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₂ n.next₂)) := by
  have active₁ : ¬ AllDone D (treeSimCoinWaiting K D 1 coinRnd st₁ (fun i =>
      treeStagesCheckAfterCoin K (ctx₁ i) (tuples₁ i) (tag i) (hashLabel i) (finish₁ i))) := by
    intro done
    have hh := done pivotParty pivot.honest
    simpa [treeSimCoinWaiting, treeSimCoinStep, pivot.honest] using hh
  have active₂ : ¬ AllDone D (treeSimCoinWaiting K D 1 coinRnd st₂ (fun i =>
      treeStagesCheckAfterCoin K (ctx₂ i) (tuples₂ i) (tag i) (hashLabel i) (finish₂ i))) := by
    intro done
    have hh := done pivotParty pivot.honest
    simpa [treeSimCoinWaiting, treeSimCoinStep, pivot.honest] using hh
  simp only [AllDone] at active₁ active₂
  rw [executeSteps, if_neg active₁, executeSteps, if_neg active₂]
  simp only [StateT.run_bind]
  apply relTriple_bind (treeStages_check_coin_firstSlice_round prims K D A T₀ pivotParty pivot old visible
    ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ counts tag hashLabel label future coinRnd st₁ st₂ lab₁ lab₂
    finish₁ finish₂ base covered state a b h fresh base_le)
  intro u z hu
  obtain ⟨sent, rnd, δ, same, _, _, left, right, caches, visible', future', fresh₁, _, _⟩ := hu
  rw [← same, left, right]
  let out := treeSimCoinOutput K D 1 coinRnd sent
  let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) ((out i).getD []) ((tuples₁ i).map (·.count)).sum
  let p := treeStagesFirstSliceChallenge K D T₀ pivotParty pivot ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ τ
    label st₁ st₂ lab₁ lab₂ finish₁ finish₂
  let live := treeStagesExpansionLive K base tag hashLabel (fun i => ((tuples₁ i).map (·.count)).sum)
    (fun i => (out i).getD []) (fun i => (out i).map fun _ => ())
  apply relTriple_post_mono (p.execute prims K D A rnd δ visible' future' live u.1.1 u.2 z.2 caches fresh₁)
  intro r t hr
  obtain ⟨same', caches', future'', empty₁, empty₂, next⟩ := hr
  exact ⟨same', sent, rnd, δ, caches', visible', future'', empty₁, empty₂, next⟩

/-- A prior honest abort closes any remaining Coin schedule in one actual
round; an already stopped driver performs no additional adversarial call. -/
theorem treeStages_coin_partial_execute (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (δ : HiddenAddress C → Bit)
    (live : C.Party → Bool) (stopped : ∃ i, i ∉ D.1 ∧ live i ≠ true)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (fuel : ℕ) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (related : TreeSimStreamRel δ a b) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCoinPartial K D live count rnd st₁ k₁)).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality (fuel + 1) state
        (treeSimCoinPartial K D live count rnd st₂ k₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  by_cases inactive : ∀ i, i ∉ D.1 → live i ≠ true
  · have none₁ : treeSimCoinPartial K D live count rnd st₁ k₁ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCoinPartial, treeSimCoinWaiting, hi]
      · simp [treeSimCoinPartial, inactive i hi]
    have none₂ : treeSimCoinPartial K D live count rnd st₂ k₂ = fun _ => .done none := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCoinPartial, treeSimCoinWaiting, hi]
      · simp [treeSimCoinPartial, inactive i hi]
    rw [none₁, none₂]
    simp only [executeSteps, Step.isDone, implies_true, if_true, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, rfl, related, rfl, rfl⟩
  · push_neg at inactive
    obtain ⟨i, hi, hl⟩ := inactive
    have active₁ : ¬ AllDone D (treeSimCoinPartial K D live count rnd st₁ k₁) := by
      intro done
      have hh := done i hi
      simp [treeSimCoinPartial, treeSimCoinWaiting, treeSimCoinStep, hi, hl] at hh
    have active₂ : ¬ AllDone D (treeSimCoinPartial K D live count rnd st₂ k₂) := by
      intro done
      have hh := done i hi
      simp [treeSimCoinPartial, treeSimCoinWaiting, treeSimCoinStep, hi, hl] at hh
    simp only [AllDone] at active₁ active₂
    rw [executeSteps, if_neg active₁, executeSteps, if_neg active₂]
    simp only [StateT.run_bind, ← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    rw [treeSim_coin_partial_factor K D A _ live stopped, treeSim_coin_partial_factor K D A _ live stopped]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b related)
    intro u z h
    rw [executeSteps_done _ D A noFunctionality fuel _ _ (by intros; trivial),
      executeSteps_done _ D A noFunctionality fuel _ _ (by intros; trivial)]
    have same : u.1.1 = z.1.1 := congrArg Prod.fst h.1
    exact relTriple_pure_pure ⟨same, rfl, rfl, h.2⟩

theorem treeStages_coin_partial_live (D : C.Coalition)
    (live : C.Party → Bool) (active : ∀ i, i ∉ D.1 → live i = true) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput) :
    treeSimCoinPartial K D live count rnd st k = treeSimCoinWaiting K D count rnd st k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinPartial, treeSimCoinWaiting, hi]
  · simp only [treeSimCoinPartial, active i hi, if_true]

/-- The first two check rounds apply directly to a partially active
ceremony boundary, including aborts inherited from Rerand. -/
theorem treeStages_firstCheck_partial_two_rounds (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (tuples₁ tuples₂ : C.Party → List (Tuple C))
    (counts : ∀ i, ((tuples₁ i).map (·.count)).sum = ((tuples₂ i).map (·.count)).sum)
    (tag hashLabel : C.Party → ℕ) (label : ℕ) (future : TreeSimFutureZero (label + 2) old)
    (live : C.Party → Bool) (coinRnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (base : HashCache C)
    (covered : ∀ i values, values.length = 1 →
      TreeStagesExpansionCovered K base (tag i) (hashLabel i) values ((tuples₁ i).map (·.count)).sum)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd st₁ (fun i =>
          treeStagesCheckAfterCoin K (ctx₁ i) (tuples₁ i) (tag i) (hashLabel i) (finish₁ i)))).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd st₂ (fun i =>
          treeStagesCheckAfterCoin K (ctx₂ i) (tuples₂ i) (tag i) (hashLabel i) (finish₂ i)))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ ∃ sent rnd δ,
        let out := treeSimCoinOutput K D 1 coinRnd sent
        let τ := fun i => treeStagesCachedExpansion K base (tag i) (hashLabel i) ((out i).getD []) ((tuples₁ i).map (·.count)).sum
        let p := treeStagesFirstSliceChallenge K D T₀ pivotParty pivot ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ τ
          label st₁ st₂ lab₁ lab₂ finish₁ finish₂
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (label + 3) δ ∧ TreeSimFutureEmpty (label + 3) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 3) z.2.2 ∧
        ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
          ∃ sent' challengeRnd,
            let n := p.coinNext K D rnd δ sent'
            u.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₁ n.next₁ ∧
            z.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₂ n.next₂)) := by
  by_cases active : ∀ i, i ∉ D.1 → live i = true
  · rw [treeStages_coin_partial_live K D live active, treeStages_coin_partial_live K D live active]
    exact treeStages_firstCheck_two_rounds prims K D A T₀ pivotParty pivot old visible ctx₁ ctx₂ self₁ self₂ keys
      tuples₁ tuples₂ counts tag hashLabel label future coinRnd st₁ st₂ lab₁ lab₂ finish₁ finish₂ base covered state a b h fresh base_le
  · push_neg at active
    apply relTriple_post_mono (treeStages_coin_partial_execute prims K D A old live active 1 coinRnd st₁ st₂
      _ _ 1 state a b h)
    intro u z hu
    obtain ⟨same, left, right, caches, frame₁, frame₂⟩ := hu
    refine ⟨same, (fun _ _ => none), 0, old, caches, visible, ?_, ?_, ?_, Or.inl ⟨left, right⟩⟩
    · exact fun x hx => future x (by omega)
    · rw [frame₁]; exact fun x hx => fresh x (by omega)
    · rw [frame₂]; exact fun x hx => treeSim_futureEmpty_related fresh h.2 x (by omega)

set_option maxHeartbeats 400000 in
/-- Concrete padding discharges all first-check hash coverage for every
possible rushing Coin reply. The two real driver rounds start from the padded
dealer cache, retain the original log, and perform the original check queries. -/
theorem treeStages_firstCheck_padded_two_rounds (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (tuples₁ tuples₂ : C.Party → List (Tuple C))
    (counts : ∀ i, ((tuples₁ i).map (·.count)).sum = ((tuples₂ i).map (·.count)).sum)
    (tag hashLabel : C.Party → ℕ) (label : ℕ) (future : TreeSimFutureZero (label + 2) old)
    (live : C.Party → Bool) (coinRnd : C.Party → PrssOutput C E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (label + 1) a.1.2) 
    (r : Unit × HashCache C)
    (padded : r ∈ support ((simulateQ (localAnswer prims) (treeStagesCheckPadding K
      (C.parties.map fun i => (tag i, hashLabel i)) (C.parties.map fun i => ((tuples₁ i).map (·.count)).sum) 1)).run a.1.1)) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd st₁ (fun i =>
          treeStagesCheckAfterCoin K (ctx₁ i) (tuples₁ i) (tag i) (hashLabel i) (finish₁ i)))).run ((r.2, a.1.2), a.2))
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd st₂ (fun i =>
          treeStagesCheckAfterCoin K (ctx₂ i) (tuples₂ i) (tag i) (hashLabel i) (finish₂ i)))).run (r.2, b.2))
      (fun u z => u.1.1 = z.1.1 ∧ ∃ sent rnd δ,
        let out := treeSimCoinOutput K D 1 coinRnd sent
        let τ := fun i => treeStagesCachedExpansion K r.2 (tag i) (hashLabel i) ((out i).getD []) ((tuples₁ i).map (·.count)).sum
        let p := treeStagesFirstSliceChallenge K D T₀ pivotParty pivot ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ τ
          label st₁ st₂ lab₁ lab₂ finish₁ finish₂
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (label + 3) δ ∧ TreeSimFutureEmpty (label + 3) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 3) z.2.2 ∧
        ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
          ∃ sent' challengeRnd,
            let n := p.coinNext K D rnd δ sent'
            u.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₁ n.next₁ ∧
            z.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₂ n.next₂)) := by
  have cover := (treeStages_checkPadding_covered prims K
    (C.parties.map fun i => (tag i, hashLabel i)) (C.parties.map fun i => ((tuples₁ i).map (·.count)).sum)
    1 a.1.1 r (by exact padded)).2
  have covered : ∀ i values, values.length = 1 →
      TreeStagesExpansionCovered K r.2 (tag i) (hashLabel i) values ((tuples₁ i).map (·.count)).sum := by
    intro i values hlen
    exact cover (tag i) (hashLabel i) (List.mem_map.mpr ⟨i, by simp [Committee.parties], rfl⟩)
      _ (List.mem_map.mpr ⟨i, by simp [Committee.parties], rfl⟩) values hlen
  exact treeStages_firstCheck_partial_two_rounds prims K D A T₀ pivotParty pivot old visible
    ctx₁ ctx₂ self₁ self₂ keys tuples₁ tuples₂ counts tag hashLabel label future live coinRnd
    st₁ st₂ lab₁ lab₂ finish₁ finish₂ r.2 covered state ((r.2, a.1.2), a.2) (r.2, b.2) ⟨rfl, h.2⟩ fresh le_rfl

/-- Read the bounded rejection sampler from the covered public cache. -/
def treeStagesCachedFindChallenge (cache : HashCache C) (key : HashOutput) : ℕ → ℕ → Option E
  | 0, _ => none
  | tries + 1, index =>
    let r := elementOfHash K ((cache (.expand key index)).getD 0)
    if r ≠ 0 ∧ r ≠ 1 then some r else treeStagesCachedFindChallenge cache key tries (index + 1)

def TreeStagesChallengeCovered (cache : HashCache C) (tag label : ℕ) (values : List E) : Prop :=
  ∃ key : HashOutput, cache (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))) = some key ∧
    ∀ k < challengeTries, ∃ h, cache (.expand key k) = some h

def treeStagesCachedChallenge (cache : HashCache C) (tag label : ℕ) (values : List E) : Option E :=
  let key := (cache (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v)))).getD 0
  treeStagesCachedFindChallenge K cache key challengeTries 0

theorem treeStages_challengeCovered_mono {a b : HashCache C} (h : a ≤ b)
    (tag label : ℕ) (values : List E) (covered : TreeStagesChallengeCovered K a tag label values) :
    TreeStagesChallengeCovered K b tag label values := by
  obtain ⟨key, hk, expansions⟩ := covered
  exact ⟨key, h hk, fun k hk' => (expansions k hk').imp (fun _ hv => h hv)⟩

theorem treeStages_cachedFindChallenge_mono {a b : HashCache C} (h : a ≤ b)
    (key : HashOutput) (tries index : ℕ)
    (covered : ∀ k, index ≤ k → k < index + tries → ∃ v, a (.expand key k) = some v) :
    treeStagesCachedFindChallenge K a key tries index = treeStagesCachedFindChallenge K b key tries index := by
  induction tries generalizing index with
  | zero => rfl
  | succ tries ih =>
    obtain ⟨v, hv⟩ := covered index le_rfl (by omega)
    simp only [treeStagesCachedFindChallenge]
    rw [hv, h hv]
    simp only [Option.getD_some]
    split_ifs with good
    · rfl
    · exact ih (index + 1) (fun k hk hk' => covered k (by omega) (by omega))

theorem treeStages_cachedChallenge_mono {a b : HashCache C} (h : a ≤ b)
    (tag label : ℕ) (values : List E) (covered : TreeStagesChallengeCovered K a tag label values) :
    treeStagesCachedChallenge K a tag label values = treeStagesCachedChallenge K b tag label values := by
  obtain ⟨key, hk, expansions⟩ := covered
  simp only [treeStagesCachedChallenge]
  rw [hk, h hk]
  simp only [Option.getD_some]
  exact treeStages_cachedFindChallenge_mono K h key challengeTries 0 (fun k _ hk' => expansions k (by omega))

theorem treeStages_hashQuery_replay (D : C.Coalition) (q : Query C) (random : ¬ IsFixed q)
    (cache : HashCache C × HiddenCache C) (v : HashOutput) (hit : cache.1 q = some v) :
    (simulateQ (streamWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C)))).run cache = pure (v, cache) := by
  have queryEq : simulateQ (streamWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C))) =
      onHash (hashAnswer prims q) := by
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  rw [queryEq]
  simp [onHash, hashAnswer_run_cached prims random hit]

/-- Every actually attempted challenge query is retained; cached rejection
and exhaustion execute the same branches as the frozen rejection sampler. -/
theorem treeStages_findChallenge_replay (D : C.Coalition) (key : HashOutput) (tries index : ℕ)
    (cache : HashCache C × HiddenCache C)
    (covered : ∀ k, index ≤ k → k < index + tries → ∃ v, cache.1 (.expand key k) = some v) :
    (simulateQ (streamWorld prims D) (free (liftComp (findChallenge K key tries index) (LocalSpec C)))).run cache =
      pure (treeStagesCachedFindChallenge K cache.1 key tries index, cache) := by
  induction tries generalizing index with
  | zero => simp [findChallenge, treeStagesCachedFindChallenge, free_pure]
  | succ tries ih =>
    obtain ⟨v, hv⟩ := covered index le_rfl (by omega)
    simp only [findChallenge, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind]
    rw [treeStages_hashQuery_replay prims D (.expand key index) (by rintro ⟨_, heq, _⟩; cases heq) cache v hv, pure_bind]
    simp only [treeStagesCachedFindChallenge]
    rw [hv]
    simp only [Option.getD_some]
    cases hd : Classical.propDecidable (elementOfHash K v ≠ 0 ∧ elementOfHash K v ≠ 1) with
    | isTrue good => simp [good, free_pure]
    | isFalse bad =>
      simpa only [if_neg bad] using ih (index + 1)
        (fun k hk hk' => covered k (by omega) (by omega))

theorem treeStages_challengeQuery_replay (D : C.Coalition) (tag label : ℕ) (values : List E)
    (cache : HashCache C × HiddenCache C) (covered : TreeStagesChallengeCovered K cache.1 tag label values) :
    (simulateQ (streamWorld prims D) (free (liftComp (challengeQuery K tag label values) (LocalSpec C)))).run cache =
      pure (treeStagesCachedChallenge K cache.1 tag label values, cache) := by
  obtain ⟨key, hk, expansions⟩ := covered
  simp only [challengeQuery, liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind]
  rw [treeStages_hashQuery_replay prims D _ (by rintro ⟨_, heq, _⟩; cases heq) cache key hk, pure_bind]
  simp only [treeStagesCachedChallenge]
  rw [hk]
  simp only [Option.getD_some]
  exact treeStages_findChallenge_replay prims K D key challengeTries 0 cache (fun k _ hk' => expansions k (by omega))

/-- The actual challenge hashing/rejection followed by field PRSS and
reshare, with the challenge-dependent check continuation retained. -/
def treeStagesChallengePeerProgram (ctx : Context C) (tag hashLabel : ℕ)
    (values : List E) (idx count : ℕ) (v : E → ℕ → E) (st : RunState C)
    (k : E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput) : PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K tag hashLabel (fun r =>
    ((prssRandomness ctx (elementCodec K) idx count >>= fun rnd =>
      reshare K ctx (elementCodec K) rnd (v r.1) count).run r.2) >>= k r.1) (values, st)

/-- Cached challenge replay can precede a shifted field draw even after
previous holders have filled the same field block. Exhaustion stops both runs. -/
theorem treeStages_challenge_field_entry (D : C.Coalition)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (tag hashLabel label idx count : ℕ) (values : List E)
    (v₁ v₂ : E → ℕ → E) (st₁ st₂ : RunState C) (lab₁ : st₁.label = label) (lab₂ : st₂.label = label)
    (k₁ k₂ : E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (delta : KeyName C → Fin count → E) (visible : ∀ name, ¬ Hidden D name → delta name = 0)
    (base₁ base₂ : HiddenCache C) (base : HashCache C)
    (covered : TreeStagesChallengeCovered K base tag hashLabel values)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeStagesFieldRel K D label idx count delta base₁ base₂ a b) (base_le : base ≤ a.1.1) :
    let r := treeStagesCachedChallenge K base tag hashLabel values
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (advance
        (treeStagesChallengePeerProgram K ctx₁ tag hashLabel values idx count v₁ st₁ k₁).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance
        (treeStagesChallengePeerProgram K ctx₂ tag hashLabel values idx count v₂ st₂ k₂).run))).run b)
      (fun u z => (∃ rnd,
        u.1 = (if r.isSome then treeSimPeerStep K ctx₁ (elementCodec K) rnd (v₁ (r.getD 0)) count st₁ (k₁ (r.getD 0)) else .done none) ∧
        z.1 = (if r.isSome then treeSimPeerStep K ctx₂ (elementCodec K)
          (rnd + treeStagesPrssFieldShift ctx₁ count delta) (v₂ (r.getD 0)) count st₂ (k₂ (r.getD 0)) else .done none)) ∧
        TreeStagesFieldRel K D label idx count delta base₁ base₂ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  have le₂ : base ≤ b.1 := by rw [← h.1]; exact base_le
  have replay₁ := treeStages_challengeQuery_replay prims K D tag hashLabel values a.1
    (treeStages_challengeCovered_mono K base_le _ _ _ covered)
  have replay₂ := treeStages_challengeQuery_replay prims K D tag hashLabel values b
    (treeStages_challengeCovered_mono K le₂ _ _ _ covered)
  rw [← treeStages_cachedChallenge_mono K base_le _ _ _ covered] at replay₁
  rw [← treeStages_cachedChallenge_mono K le₂ _ _ _ covered] at replay₂
  unfold treeStagesChallengePeerProgram
  rw [treeStages_challenge_tail_factor, treeStages_challenge_tail_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeStages_readOnly_pair prims D _ _ a b _ _ replay₁ replay₂)
  intro u z hu
  rw [hu.1, hu.2.1]
  have h' : TreeStagesFieldRel K D label idx count delta base₁ base₂ u.2 z.2 := by
    simpa only [TreeStagesFieldRel, hu.2.2.1, hu.2.2.2] using h
  have le' : base ≤ u.2.1.1 := by rw [hu.2.2.1]; exact base_le
  cases hr : treeStagesCachedChallenge K base tag hashLabel values with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure, Option.isSome_none, Bool.false_eq_true, if_false]
    exact relTriple_pure_pure ⟨⟨0, rfl, rfl⟩, h', le'⟩
  | some r =>
    simp only [treeSimResume, Option.isSome_some, if_true, Option.getD_some]
    exact treeStages_field_peer_entry prims K D ctx₁ ctx₂ self keys label idx count _ _ st₁ st₂ lab₁ lab₂
      _ _ delta _ (treeStages_fieldDraws_base prims K D label idx count delta visible base₁ base₂ base) u.2 z.2 ⟨h', le'⟩

def treeStagesChallengeLive (base : HashCache C) (tag hashLabel : C.Party → ℕ)
    (values : C.Party → List E) (out : C.Party → Option Unit) (i : C.Party) : Bool :=
  (out i).isSome && (treeStagesCachedChallenge K base (tag i) (hashLabel i) (values i)).isSome

/-- All honest holders execute the original challenge queries and field
entries in driver order, sharing the same coherent encoded field block. -/
theorem treeStages_challenge_field_partial (D : C.Coalition)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (out : C.Party → Option Unit) (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (tag hashLabel : C.Party → ℕ) (values : C.Party → List E)
    (label idx count : ℕ) (v₁ v₂ : C.Party → E → ℕ → E) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label) (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E)
    (base₁ base₂ : HiddenCache C) (base : HashCache C)
    (covered : ∀ i, out i = some () → TreeStagesChallengeCovered K base (tag i) (hashLabel i) (values i))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeStagesFieldRel K D label idx count (treeStagesMaskDelta D count dt dp) base₁ base₂ a b)
    (base_le : base ≤ a.1.1) :
    let r := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) (values i)).getD 0
    let live := treeStagesChallengeLive K base tag hashLabel values out
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        treeStagesChallengePeerProgram K (ctx₁ i) (tag i) (hashLabel i) (values i) idx count (v₁ i) (st₁ i) (k₁ i)) out)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i (_ : Unit) =>
        treeStagesChallengePeerProgram K (ctx₂ i) (tag i) (hashLabel i) (values i) idx count (v₂ i) (st₂ i) (k₂ i)) out)).run b)
      (fun u z => (∃ rnd,
        u.1 = treeSimExtendMultPartial K D ctx₁ live count rnd (fun i => v₁ i (r i)) st₁ (fun i => k₁ i (r i)) ∧
        z.1 = treeSimExtendMultPartial K D ctx₂ live count
          (fun i => rnd i + frandShare D count 0 0 dt dp i) (fun i => v₂ i (r i)) st₂ (fun i => k₂ i (r i))) ∧
        TreeStagesFieldRel K D label idx count (treeStagesMaskDelta D count dt dp) base₁ base₂ u.2 z.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  let r := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) (values i)).getD 0
  let live := treeStagesChallengeLive K base tag hashLabel values out
  let J := fun a b => TreeStagesFieldRel K D label idx count (treeStagesMaskDelta D count dt dp) base₁ base₂ a b ∧ base ≤ a.1.1
  let Q := fun i x y => ∃ rnd : PrssOutput C E,
    x = treeSimExtendMultPartial K D ctx₁ live count (fun _ => rnd) (fun i => v₁ i (r i)) st₁ (fun i => k₁ i (r i)) i ∧
    y = treeSimExtendMultPartial K D ctx₂ live count
      (fun j => rnd + frandShare D count 0 0 dt dp j) (fun i => v₂ i (r i)) st₂ (fun i => k₂ i (r i)) i
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D _ _ out out J Q ?_ a b ⟨h, base_le⟩)
  · intro u z hu
    choose rnd h₁ h₂ using hu.1
    exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩
  · intro i s t hst
    cases ho : out i with
    | none =>
      simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨0, ?_, ?_⟩, hst⟩ <;> simp [treeSimExtendMultPartial, live, treeStagesChallengeLive, ho]
    | some x =>
      cases x
      have hi : i ∉ D.1 := fun hi => by simpa [ho] using corrupt i hi
      simp only [treeSimResume]
      apply relTriple_post_mono (treeStages_challenge_field_entry prims K D (ctx₁ i) (ctx₂ i)
        ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi) (tag i) (hashLabel i) label idx count (values i)
        (v₁ i) (v₂ i) (st₁ i) (st₂ i) (lab₁ i hi) (lab₂ i hi) (k₁ i) (k₂ i)
        (treeStagesMaskDelta D count dt dp) (treeStagesMaskDelta_visible D count dt dp)
        base₁ base₂ base (covered i ho) s t hst.1 hst.2)
      intro u z hu
      obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
      have hs : treeStagesPrssFieldShift (ctx₁ i) count (treeStagesMaskDelta D count dt dp) =
          frandShare D count 0 0 dt dp i := by
        rw [treeStages_prssFieldShift_mask D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
      refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
      · simpa [treeSimExtendMultPartial, live, treeStagesChallengeLive, ho, treeSimExtendMultWaiting, hi, r] using hu
      · simpa [treeSimExtendMultPartial, live, treeStagesChallengeLive, ho, treeSimExtendMultWaiting, hi, r, hs] using hz

/-- Normalize only the field gadget following the actual challenge. -/
theorem treeStages_challenge_extendMult_program (ctx : Context C) (tag hashLabel count : ℕ)
    (products : E → List (Product C E)) (len : ∀ r, (products r).length = count)
    (k : E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput) (values : List E) (st : RunState C) :
    treeStagesChallengeTail K tag hashLabel (fun r =>
      ((realCheckGadgets K ctx).extendMult (products r.1)).run r.2 >>= k r.1) (values, st) =
      treeStagesChallengePeerProgram K ctx tag hashLabel values 0 count
        (fun r => contextProductValues K ctx (products r)) st k := by
  have program (r : E) := treeStages_extendMult_program K ctx (products r) count (len r)
  simp only [treeStagesChallengePeerProgram, program]

/-- Construct a new coherent field-mask translation after the actual
challenge and rejection sampler, including optional earlier Coin failures.
The exact challenge-dependent products and continuations remain in the data. -/
theorem treeStages_challenge_extendMult_start (D : C.Coalition)
    (T₀ : C.Term) (pivotParty : C.Party) (pivot : Pivot K D T₀ pivotParty)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i) (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (count : ℕ) (products₁ products₂ : C.Party → E → List (Product C E))
    (len₁ : ∀ i r, (products₁ i r).length = count) (len₂ : ∀ i r, (products₂ i r).length = count)
    (tag hashLabel : C.Party → ℕ) (out : C.Party → Option (List E))
    (corrupt : ∀ i, i ∈ D.1 → out i = none) (label : ℕ) (future : TreeSimFutureZero (label + 1) old)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label) (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label)
    (k₁ k₂ : C.Party → E → Shares C E × RunState C → PartyM C E RealSpec TreeOutput)
    (base : HashCache C)
    (covered : ∀ i values, out i = some values → TreeStagesChallengeCovered K base (tag i) (hashLabel i) values)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty label a.1.2) (base_le : base ≤ a.1.1) :
    let values := fun i => (out i).getD []
    let r := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) (values i)).getD 0
    let live := treeStagesChallengeLive K base tag hashLabel values (fun i => (out i).map fun _ => ())
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll (fun i values =>
        treeStagesChallengeTail K (tag i) (hashLabel i) (fun r =>
          ((realCheckGadgets K (ctx₁ i)).extendMult (products₁ i r.1)).run r.2 >>= k₁ i r.1) (values, st₁ i)) out)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll (fun i values =>
        treeStagesChallengeTail K (tag i) (hashLabel i) (fun r =>
          ((realCheckGadgets K (ctx₂ i)).extendMult (products₂ i r.1)).run r.2 >>= k₂ i r.1) (values, st₂ i)) out)).run b)
      (fun u z => ∃ rnd δ,
        let d := treeStagesExtendMultData K D T₀ pivotParty pivot δ count ctx₁ ctx₂ self₁ self₂ rnd
          (fun i => contextProductValues K (ctx₁ i) (products₁ i (r i)))
          (fun i => contextProductValues K (ctx₂ i) (products₂ i (r i))) st₁ st₂ (fun i => k₁ i (r i)) (fun i => k₂ i (r i))
        u.1 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
        z.1 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
        TreeSimStreamRel d.δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → d.δ x = 0) ∧
        TreeSimFutureZero (label + 1) d.δ ∧ TreeSimFutureEmpty (label + 1) u.2.1.2 ∧
        TreeSimFutureEmpty (label + 1) z.2.2 ∧ base ≤ u.2.1.1) := by
  dsimp only
  let values := fun i => (out i).getD []
  let r := fun i => (treeStagesCachedChallenge K base (tag i) (hashLabel i) (values i)).getD 0
  let v₁ := fun i => contextProductValues K (ctx₁ i) (products₁ i (r i))
  let v₂ := fun i => contextProductValues K (ctx₂ i) (products₂ i (r i))
  let dt := termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E)
  let dp := pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))
  let delta := treeStagesMaskDelta D count dt dp
  have fresh₂ := treeSim_futureEmpty_related fresh h.2
  have initial : TreeStagesFieldRel K D label 0 count delta a.1.2 b.2 a b :=
    ⟨h.1, treeStages_fieldCaches_initial K D label 0 count delta _ _ fresh fresh₂⟩
  have program₁ (i : C.Party) (vs : List E) :=
    treeStages_challenge_extendMult_program K (ctx₁ i) (tag i) (hashLabel i) count (products₁ i) (len₁ i) (k₁ i) vs (st₁ i)
  have program₂ (i : C.Party) (vs : List E) :=
    treeStages_challenge_extendMult_program K (ctx₂ i) (tag i) (hashLabel i) count (products₂ i) (len₂ i) (k₂ i) vs (st₂ i)
  rw [treeStages_resumeAll_getD _ out (fun _ => []), treeStages_resumeAll_getD _ out (fun _ => [])]
  simp only [program₁, program₂]
  apply relTriple_post_mono (treeStages_challenge_field_partial prims K D ctx₁ ctx₂ self₁ self₂ keys
    (fun i => (out i).map fun _ => ()) (by intro i hi; simp [corrupt i hi]) tag hashLabel values label 0 count
    (fun i r => contextProductValues K (ctx₁ i) (products₁ i r))
    (fun i r => contextProductValues K (ctx₂ i) (products₂ i r)) st₁ st₂ lab₁ lab₂ k₁ k₂ dt dp a.1.2 b.2 base ?_
    a b initial base_le)
  · intro u z hu
    obtain ⟨⟨rnd, hu, hz⟩, hc, le⟩ := hu
    let δ := treeStagesFieldCacheDelta D label 0 count old u.2.1.2 z.2.2
    refine ⟨rnd, δ, hu, hz, ⟨hc.1, ?_⟩, ?_, ?_, ?_, ?_, le⟩
    · exact treeStages_fieldCaches_related K D label 0 count delta old _ _ _ _ hc.2 h.2
    · exact treeStages_fieldCacheDelta_visible D label 0 count old _ _ visible
    · exact treeStages_fieldCacheDelta_future D label 0 count old _ _ future
    · exact (treeStages_fieldCaches_future K D label 0 count delta _ _ _ _ hc.2 fresh fresh₂).1
    · exact (treeStages_fieldCaches_future K D label 0 count delta _ _ _ _ hc.2 fresh fresh₂).2
  · intro i hi
    cases ho : out i with
    | none => simp [ho] at hi
    | some vs => simpa [values, ho] using covered i vs ho

/-- An actual check reduction after a challenge Coin. Products may depend
on the common challenge, and the saved body contains the rest of the check. -/
structure TreeStagesReductionContext (D : C.Coalition) where
  T₀ : C.Term
  pivotParty : C.Party
  pivot : Pivot K D T₀ pivotParty
  label : ℕ
  tag : C.Party → ℕ
  hashLabel : C.Party → ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = label
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = label
structure TreeStagesChallengeReduction (D : C.Coalition) extends TreeStagesReductionContext K D where
  count : ℕ
  products₁ : C.Party → E → List (Product C E)
  products₂ : C.Party → E → List (Product C E)
  len₁ : ∀ i r, (products₁ i r).length = count
  len₂ : ∀ i r, (products₂ i r).length = count
  body₁ : C.Party → E → (Shares C E × RunState C) → E × RunState C → PartyM C E RealSpec TreeOutput
  body₂ : C.Party → E → (Shares C E × RunState C) → E × RunState C → PartyM C E RealSpec TreeOutput

def TreeStagesChallengeReduction.afterField₁ (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (i : C.Party) (r : E) (out : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K (p.ctx₁ i))).run out.2 >>= p.body₁ i r out

def TreeStagesChallengeReduction.afterField₂ (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (i : C.Party) (r : E) (out : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K (p.ctx₂ i))).run out.2 >>= p.body₂ i r out

def TreeStagesChallengeReduction.afterCoin₁ (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (i : C.Party) : List E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K (p.tag i) (p.hashLabel i) (fun r =>
    ((realCheckGadgets K (p.ctx₁ i)).extendMult (p.products₁ i r.1)).run r.2 >>= p.afterField₁ K D i r.1)

def TreeStagesChallengeReduction.afterCoin₂ (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (i : C.Party) : List E × RunState C → PartyM C E RealSpec TreeOutput :=
  treeStagesChallengeTail K (p.tag i) (p.hashLabel i) (fun r =>
    ((realCheckGadgets K (p.ctx₂ i)).extendMult (p.products₂ i r.1)).run r.2 >>= p.afterField₂ K D i r.1)

def TreeStagesChallengeReduction.step (D : C.Coalition) (p : TreeStagesChallengeReduction K D)
    (r : C.Party → E) : TreeStagesExtendMultChallenge K D where
  T₀ := p.T₀
  pivotParty := p.pivotParty
  pivot := p.pivot
  label := p.label + 1
  count := p.count
  ctx₁ := p.ctx₁
  ctx₂ := p.ctx₂
  self₁ := p.self₁
  self₂ := p.self₂
  keys := p.keys
  st₁ := fun i => nextLabel (p.st₁ i)
  st₂ := fun i => nextLabel (p.st₂ i)
  lab₁ := by intro i hi; change (p.st₁ i).label + 1 = p.label + 1; rw [p.lab₁ i hi]
  lab₂ := by intro i hi; change (p.st₂ i).label + 1 = p.label + 1; rw [p.lab₂ i hi]
  products₁ := fun i => p.products₁ i (r i)
  products₂ := fun i => p.products₂ i (r i)
  len₁ := fun i => p.len₁ i (r i)
  len₂ := fun i => p.len₂ i (r i)
  body₁ := fun i => p.body₁ i (r i)
  body₂ := fun i => p.body₂ i (r i)

/-- Two complete driver rounds: actual challenge Coin, bounded rejection,
coherent adapted field masks, rushing ExtendMult, and the next challenge Coin.
Earlier aborts and sampler exhaustion are included. -/
theorem TreeStagesChallengeReduction.coupling (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesChallengeReduction K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 → TreeStagesChallengeCovered K base (p.tag i) (p.hashLabel i) values)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd p.st₁ (p.afterCoin₁ K D))).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd p.st₂ (p.afterCoin₂ K D))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ ∃ sent rnd δ,
        let out := treeSimCoinOutput K D 1 coinRnd sent
        let r := fun i => (treeStagesCachedChallenge K base (p.tag i) (p.hashLabel i) ((out i).getD [])).getD 0
        let step := p.step K D r
        TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
        TreeSimFutureZero (p.label + 3) δ ∧ TreeSimFutureEmpty (p.label + 3) u.2.1.2 ∧ TreeSimFutureEmpty (p.label + 3) z.2.2 ∧
        ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
          ∃ sent' challengeRnd,
            let n := step.coinNext K D rnd δ sent'
            u.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₁ n.next₁ ∧
            z.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₂ n.next₂)) := by
  by_cases allLive : ∀ i, i ∉ D.1 → live i = true
  · rw [treeStages_coin_partial_live K D live allLive, treeStages_coin_partial_live K D live allLive]
    have active₁ : ¬ AllDone D (treeSimCoinWaiting K D 1 coinRnd p.st₁ (p.afterCoin₁ K D)) := by
      intro done
      have hh := done p.pivotParty p.pivot.honest
      simpa [treeSimCoinWaiting, treeSimCoinStep, p.pivot.honest] using hh
    have active₂ : ¬ AllDone D (treeSimCoinWaiting K D 1 coinRnd p.st₂ (p.afterCoin₂ K D)) := by
      intro done
      have hh := done p.pivotParty p.pivot.honest
      simpa [treeSimCoinWaiting, treeSimCoinStep, p.pivot.honest] using hh
    simp only [AllDone] at active₁ active₂
    rw [executeSteps, if_neg active₁, executeSteps, if_neg active₂]
    simp only [StateT.run_bind, ← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
    rw [treeSim_coin_round_factor, treeSim_coin_round_factor]
    simp only [treeStages_resumeAll_map, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure, bind_assoc, pure_bind]
    apply relTriple_bind (treeSim_relTriple_support (treeSim_local_streamRel_fixed prims D old _ a b h))
    intro u z hu
    rw [hu.1.1]
    have fresh' : TreeSimFutureEmpty (p.label + 1) u.2.1.2 := by rw [hu.1.2.2.1]; exact fresh
    have le' : base ≤ u.2.1.1 := base_le.trans (treeSim_logged_grows prims D _ a u hu.2.1)
    apply relTriple_bind (treeStages_challenge_extendMult_start prims K D p.T₀ p.pivotParty p.pivot old visible
      p.ctx₁ p.ctx₂ p.self₁ p.self₂ p.keys p.count p.products₁ p.products₂ p.len₁ p.len₂ p.tag p.hashLabel
      (treeSimCoinOutput K D 1 coinRnd z.1.2) (by intro i hi; simp [treeSimCoinOutput, hi])
      (p.label + 1) future (fun i => nextLabel (p.st₁ i)) (fun i => nextLabel (p.st₂ i))
      (by intro i hi; change (p.st₁ i).label + 1 = p.label + 1; rw [p.lab₁ i hi])
      (by intro i hi; change (p.st₂ i).label + 1 = p.label + 1; rw [p.lab₂ i hi])
      (p.afterField₁ K D) (p.afterField₂ K D) base (by
        intro i values hout
        exact covered i values (treeStages_coinOutput_length K D 1 coinRnd z.1.2 i values hout))
      u.2 z.2 hu.1.2.1 fresh' le')
    intro u' z' h'
    obtain ⟨rnd, δ, left, right, caches, visible', future', fresh₁, _, _⟩ := h'
    rw [left, right]
    let out := treeSimCoinOutput K D 1 coinRnd z.1.2
    let r := fun i => (treeStagesCachedChallenge K base (p.tag i) (p.hashLabel i) ((out i).getD [])).getD 0
    let live' := treeStagesChallengeLive K base p.tag p.hashLabel (fun i => (out i).getD []) (fun i => (out i).map fun _ => ())
    apply relTriple_post_mono ((p.step K D r).execute prims K D A rnd δ visible' future' live' z.1.1 u'.2 z'.2 caches fresh₁)
    intro v w hv
    obtain ⟨same, caches', zero, empty₁, empty₂, next⟩ := hv
    exact ⟨same, z.1.2, rnd, δ, caches', visible', zero, empty₁, empty₂, next⟩
  · push_neg at allLive
    apply relTriple_post_mono (treeStages_coin_partial_execute prims K D A old live allLive 1 coinRnd p.st₁ p.st₂
      _ _ 1 state a b h)
    intro u z hu
    obtain ⟨same, left, right, caches, frame₁, frame₂⟩ := hu
    refine ⟨same, (fun _ _ => none), 0, old, caches, visible, ?_, ?_, ?_, Or.inl ⟨left, right⟩⟩
    · exact fun x hx => future x (by omega)
    · rw [frame₁]; exact fun x hx => fresh x (by omega)
    · rw [frame₂]; exact fun x hx => treeSim_futureEmpty_related fresh h.2 x (by omega)

/-- The exact successor of two check-reduction rounds. The cached
challenge fixes the actual products and both saved remaining programs. -/
def TreeStagesChallengeReduction.Result (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesChallengeReduction K D)
    (base : HashCache C) (coinRnd : C.Party → PrssOutput C E)
    (u : TreeSimConfig A (TreeSimState C)) (z : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  u.1.1 = z.1.1 ∧ ∃ sent rnd δ,
    let out := treeSimCoinOutput K D 1 coinRnd sent
    let r := fun i => (treeStagesCachedChallenge K base (p.tag i) (p.hashLabel i) ((out i).getD [])).getD 0
    let step := p.step K D r
    TreeSimStreamRel δ u.2 z.2 ∧ (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
    TreeSimFutureZero (p.label + 3) δ ∧ TreeSimFutureEmpty (p.label + 3) u.2.1.2 ∧ TreeSimFutureEmpty (p.label + 3) z.2.2 ∧
    ((u.1.2 = (fun _ => .done none) ∧ z.1.2 = (fun _ => .done none)) ∨
      ∃ sent' challengeRnd,
        let n := step.coinNext K D rnd δ sent'
        u.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₁ n.next₁ ∧
        z.1.2 = treeSimCoinPartial K D n.live n.count challengeRnd n.st₂ n.next₂)

/-- The actual deterministic slice update, before entering the next slice. -/
def treeStagesSliceUpdate (ctx : Context C) (τ : List E) (count j : ℕ)
    (p : Shares C E × Shares C E × E) (out : Shares C E) (r : E) : Shares C E × Shares C E × E :=
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  let t₀ := conv K ctx out 0
  let tInf := conv K ctx out 1
  let t₁ := (p.2.2 + t₀) / τ.getD (sliceBits - 1 - j) 0
  let fold := fun (v : Shares C E) T k => v T k + r * (v T k + v T (k + half))
  (fold p.1, fold p.2.1, (1 + r) * t₀ + r * t₁ + r * (1 + r) * tInf)

theorem treeStages_sliceBody_next (ctx : Context C) (τ : List E) (count j next : ℕ) (remaining : List ℕ)
    (p : Shares C E × Shares C E × E) (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E × RunState C) :
    treeStagesSliceBody K ctx τ count j (next :: remaining) p finish out r =
      ((realCheckGadgets K ctx).extendMult
        (treeStagesSliceProducts τ count next (treeStagesSliceUpdate K ctx τ count j p out.1 r.1))).run r.2 >>=
        treeStagesAfterSlice K ctx τ count next remaining (treeStagesSliceUpdate K ctx τ count j p out.1 r.1) finish := by
  change treeStagesCheckFold K ctx τ count (next :: remaining) (treeStagesSliceUpdate K ctx τ count j p out.1 r.1) r.2 finish = _
  exact treeStages_checkFold_cons K ctx τ count next remaining _ r.2 finish

/-- Concrete next-slice products and fold, retaining both private tuples
and the complete halving/final-check suffix. -/
def treeStagesSliceReduction (D : C.Coalition) (q : TreeStagesReductionContext K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → Shares C E × Shares C E × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) : TreeStagesChallengeReduction K D where
  toTreeStagesReductionContext := q
  count := 2
  products₁ := fun i r => treeStagesSliceProducts (τ₁ i) (count₁ i) next (treeStagesSliceUpdate K (q.ctx₁ i) (τ₁ i) (count₁ i) j (p₁ i) (out₁ i) r)
  products₂ := fun i r => treeStagesSliceProducts (τ₂ i) (count₂ i) next (treeStagesSliceUpdate K (q.ctx₂ i) (τ₂ i) (count₂ i) j (p₂ i) (out₂ i) r)
  len₁ := by intros; rfl
  len₂ := by intros; rfl
  body₁ := fun i r => treeStagesSliceBody K (q.ctx₁ i) (τ₁ i) (count₁ i) next remaining
    (treeStagesSliceUpdate K (q.ctx₁ i) (τ₁ i) (count₁ i) j (p₁ i) (out₁ i) r) (finish₁ i)
  body₂ := fun i r => treeStagesSliceBody K (q.ctx₂ i) (τ₂ i) (count₂ i) next remaining
    (treeStagesSliceUpdate K (q.ctx₂ i) (τ₂ i) (count₂ i) j (p₂ i) (out₂ i) r) (finish₂ i)

theorem treeStages_sliceReduction_afterCoin₁ (D : C.Coalition) (q : TreeStagesReductionContext K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → Shares C E × Shares C E × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    (treeStagesSliceReduction K D q τ₁ τ₂ count₁ count₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).afterCoin₁ K D =
      fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
        (treeStagesSliceBody K (q.ctx₁ i) (τ₁ i) (count₁ i) j (next :: remaining) (p₁ i) (finish₁ i) (out₁ i, q.st₁ i)) := by
  funext i values
  unfold TreeStagesChallengeReduction.afterCoin₁
  congr 1
  funext r
  rw [treeStages_sliceBody_next]
  rfl

theorem treeStages_sliceReduction_afterCoin₂ (D : C.Coalition) (q : TreeStagesReductionContext K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → Shares C E × Shares C E × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    (treeStagesSliceReduction K D q τ₁ τ₂ count₁ count₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).afterCoin₂ K D =
      fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
        (treeStagesSliceBody K (q.ctx₂ i) (τ₂ i) (count₂ i) j (next :: remaining) (p₂ i) (finish₂ i) (out₂ i, q.st₂ i)) := by
  funext i values
  unfold TreeStagesChallengeReduction.afterCoin₂
  congr 1
  funext r
  rw [treeStages_sliceBody_next]
  rfl

/-- Two actual driver rounds between successive slice challenges. The
field masks, hashing and rushing calls are all discharged by the proof. -/
theorem treeStages_slice_two_rounds (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (q : TreeStagesReductionContext K D)
    (τ₁ τ₂ : C.Party → List E) (count₁ count₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → Shares C E × Shares C E × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (q.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 → TreeStagesChallengeCovered K base (q.tag i) (q.hashLabel i) values)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (q.label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd q.st₁ (fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
          (treeStagesSliceBody K (q.ctx₁ i) (τ₁ i) (count₁ i) j (next :: remaining) (p₁ i) (finish₁ i) (out₁ i, q.st₁ i))))).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd q.st₂ (fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
          (treeStagesSliceBody K (q.ctx₂ i) (τ₂ i) (count₂ i) j (next :: remaining) (p₂ i) (finish₂ i) (out₂ i, q.st₂ i))))).run b)
      ((treeStagesSliceReduction K D q τ₁ τ₂ count₁ count₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).Result K D A base coinRnd) := by
  have coupled := (treeStagesSliceReduction K D q τ₁ τ₂ count₁ count₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).coupling
    prims K D A old visible future live coinRnd base covered state a b h fresh base_le
  simp only [treeStages_sliceReduction_afterCoin₁, treeStages_sliceReduction_afterCoin₂] at coupled
  exact coupled

/-- Finite coverage for every attempt of a bounded challenge rejection
sampler. The existing public cache, including dealer hits, is extended. -/
def treeStagesChallengePaddingQueries (tagLabels : List (ℕ × ℕ)) (coinCount : ℕ) : List (Query C) :=
  (tagLabels.flatMap fun tl => (Finset.univ : Finset (Fin coinCount → E)).toList.map fun vs =>
    Query.coinKey tl.1 tl.2 ((List.ofFn vs).flatMap fun v => List.ofFn (K.encode v))) ++
  ((Finset.univ : Finset HashOutput).toList.flatMap fun key => (List.range challengeTries).map (Query.expand key))

def treeStagesChallengePadding (tagLabels : List (ℕ × ℕ)) (coinCount : ℕ) : OracleComp (LocalSpec C) Unit := do
  let _ ← (treeStagesChallengePaddingQueries K tagLabels coinCount).mapM fun q => liftComp (hashQuery q) (LocalSpec C)
  pure ()

theorem treeStages_challengePadding_covered (tagLabels : List (ℕ × ℕ)) (coinCount : ℕ)
    (cache : HashCache C) (r : Unit × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (treeStagesChallengePadding K tagLabels coinCount)).run cache)) :
    cache ≤ r.2 ∧ ∀ tag label, (tag, label) ∈ tagLabels → ∀ values : List E, values.length = coinCount →
      TreeStagesChallengeCovered K r.2 tag label values := by
  simp only [treeStagesChallengePadding, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  obtain ⟨grows, covered⟩ := treeStages_prefetch_queries prims _ (by
    intro q hq
    simp only [treeStagesChallengePaddingQueries, List.mem_append, List.mem_flatMap, List.mem_map] at hq
    rcases hq with ⟨tl, _, vs, _, rfl⟩ | ⟨key, _, k, _, rfl⟩ <;>
      rintro ⟨_, heq, _⟩ <;> cases heq) cache u hu
  refine ⟨grows, ?_⟩
  intro tag label htl values hlen
  have hvalues : List.ofFn (fun i : Fin coinCount => values[i.val]'(by omega)) = values := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj; simp
  obtain ⟨key, hkey⟩ := covered (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))) (by
    apply List.mem_append_left
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨(tag, label), htl, (fun i : Fin coinCount => values[i.val]'(by omega)), ?_, ?_⟩
    · simp
    · rw [hvalues])
  refine ⟨key, hkey, ?_⟩
  intro k hk
  apply covered
  apply List.mem_append_right
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨key, by simp, k, List.mem_range.mpr hk, rfl⟩

/-- The actual driver never removes public cache entries. This carries
one initial padding choice through later gadgets and later batches. -/
theorem treeStages_executeSteps_grows (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec TreeOutput) (a : TreeSimState C)
    (u : TreeSimConfig A (TreeSimState C))
    (hu : u ∈ support ((executeSteps (treeSimRealRoles prims D) D A noFunctionality fuel state steps).run a)) :
    a.1.1 ≤ u.2.1.1 := by
  induction fuel generalizing state steps a u with
  | zero =>
    simp only [executeSteps, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst u
    exact le_rfl
  | succ fuel ih =>
    rw [executeSteps] at hu
    split_ifs at hu with done
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
      subst u
      exact le_rfl
    · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hu
      obtain ⟨v, hv, hu⟩ := hu
      have grows : a.1.1 ≤ v.2.1.1 := by
        apply treeSim_logged_grows prims D (stepRound worldRoles D A noFunctionality state steps) a v
        simpa only [simulateQ_stepRound, treeSimRealRoles] using hv
      exact grows.trans (ih _ _ _ _ hu)

/-- The two-round reduction also retains the initial padding prefix for
subsequent challenges. -/
theorem TreeStagesChallengeReduction.coupling_base (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesChallengeReduction K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 → TreeStagesChallengeCovered K base (p.tag i) (p.hashLabel i) values)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd p.st₁ (p.afterCoin₁ K D))).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd p.st₂ (p.afterCoin₂ K D))).run b)
      (fun u z => p.Result K D A base coinRnd u z ∧ base ≤ u.2.1.1) := by
  apply relTriple_post_mono (treeSim_relTriple_support
    (p.coupling prims K D A old visible future live coinRnd base covered state a b h fresh base_le))
  intro u z hu
  exact ⟨hu.1, base_le.trans (treeStages_executeSteps_grows prims D A 2 state _ a u hu.2.1)⟩

/-- Concrete finite padding discharges the entire challenge-reduction
transition without an assumed hash or field-draw coupling. -/
theorem TreeStagesChallengeReduction.padded (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (p : TreeStagesChallengeReduction K D)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (p.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (p.label + 1) a.1.2)
    (r : Unit × HashCache C)
    (padded : r ∈ support ((simulateQ (localAnswer prims)
      (treeStagesChallengePadding K (C.parties.map fun i => (p.tag i, p.hashLabel i)) 1)).run a.1.1)) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd p.st₁ (p.afterCoin₁ K D))).run ((r.2, a.1.2), a.2))
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd p.st₂ (p.afterCoin₂ K D))).run (r.2, b.2))
      (fun u z => p.Result K D A r.2 coinRnd u z ∧ r.2 ≤ u.2.1.1) := by
  have cover := (treeStages_challengePadding_covered prims K
    (C.parties.map fun i => (p.tag i, p.hashLabel i)) 1 a.1.1 r (by exact padded)).2
  apply p.coupling_base prims K D A old visible future live coinRnd r.2 ?_ state
    ((r.2, a.1.2), a.2) (r.2, b.2) ⟨rfl, h.2⟩ fresh le_rfl
  intro i values hlen
  exact cover (p.tag i) (p.hashLabel i) (List.mem_map.mpr ⟨i, by simp [Committee.parties], rfl⟩) values hlen

/-- Remaining actual Shamir halvings and final masked check. -/
def treeStagesHalvingFold (ctx : Context C) (width : ℕ) (remaining : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) : PartyM C E RealSpec TreeOutput :=
  ((do
    let p ← remaining.foldlM (halvingStep K ctx (realCheckGadgets K ctx) width) p
    finalStep K ctx (realCheckGadgets K ctx) p : RunM C E RealSpec Unit).run st) >>= finish

def treeStagesHalvingProducts (width j : ℕ) (p : (ℕ → E) × (ℕ → E) × E) : List (Product C E) :=
  let length := halvedLength^[j] width
  let half := halvedLength length
  let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
  let sum := fun (v : ℕ → E) k => v k + hi v k
  [.shamir p.1 p.2.1 half, .shamir (sum p.1) (sum p.2.1) half]

def treeStagesHalvingUpdate (ctx : Context C) (width j : ℕ) (p : (ℕ → E) × (ℕ → E) × E)
    (out : Shares C E) (r : E) : (ℕ → E) × (ℕ → E) × E :=
  let length := halvedLength^[j] width
  let half := halvedLength length
  let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
  let fold := fun (v : ℕ → E) k => v k + r * (v k + hi v k)
  (fold p.1, fold p.2.1, conv K ctx out 0 + (p.2.2 + conv K ctx out 1) * r + conv K ctx out 1 * r ^ 2)

def treeStagesHalvingBody (ctx : Context C) (width j : ℕ) (remaining : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E × RunState C) : PartyM C E RealSpec TreeOutput :=
  treeStagesHalvingFold K ctx width remaining (treeStagesHalvingUpdate K ctx width j p out.1 r.1) r.2 finish

def treeStagesAfterHalving (ctx : Context C) (width j : ℕ) (remaining : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput :=
  (challenge K (realCheckGadgets K ctx)).run out.2 >>= treeStagesHalvingBody K ctx width j remaining p finish out

/-- Enter the next real Shamir product, retaining its challenge, every
remaining halving and the final masked check. -/
theorem treeStages_halvingFold_cons (ctx : Context C) (width j : ℕ) (remaining : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesHalvingFold K ctx width (j :: remaining) p st finish =
      ((realCheckGadgets K ctx).extendMult (treeStagesHalvingProducts width j p)).run st >>=
        treeStagesAfterHalving K ctx width j remaining p finish := by
  simp only [treeStagesHalvingFold, List.foldlM_cons, halvingStep, treeStagesHalvingProducts,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  congr 1
  funext out
  simp only [treeStagesAfterHalving, treeStagesHalvingBody, treeStagesHalvingFold, treeStagesHalvingUpdate,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  congr 1
  funext r
  simp only [treeStagesHalvingBody, treeStagesHalvingFold, treeStagesHalvingUpdate, StateT.run_bind, bind_assoc]

theorem treeStages_halvingBody_next (ctx : Context C) (width j next : ℕ) (remaining : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E × RunState C) :
    treeStagesHalvingBody K ctx width j (next :: remaining) p finish out r =
      ((realCheckGadgets K ctx).extendMult
        (treeStagesHalvingProducts width next (treeStagesHalvingUpdate K ctx width j p out.1 r.1))).run r.2 >>=
        treeStagesAfterHalving K ctx width next remaining (treeStagesHalvingUpdate K ctx width j p out.1 r.1) finish :=
  treeStages_halvingFold_cons K ctx width next remaining _ r.2 finish

/-- The slice fold enters exactly the frozen halving schedule. -/
theorem treeStages_checkFold_nil (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    treeStagesCheckFold K ctx τ count [] p st finish =
      treeStagesHalvingFold K ctx (sliceWidth count) (List.range (halvings count - sliceBits))
        (conv K ctx p.1, conv K ctx p.2.1, p.2.2) st finish := by
  simp only [treeStagesCheckFold, treeStagesHalvingFold, List.foldlM_nil, pure_bind]

/-- Concrete next-halving products and the remaining real check. -/
def treeStagesHalvingReduction (D : C.Coalition) (q : TreeStagesReductionContext K D)
    (width₁ width₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → (ℕ → E) × (ℕ → E) × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) : TreeStagesChallengeReduction K D where
  toTreeStagesReductionContext := q
  count := 2
  products₁ := fun i r => treeStagesHalvingProducts (width₁ i) next (treeStagesHalvingUpdate K (q.ctx₁ i) (width₁ i) j (p₁ i) (out₁ i) r)
  products₂ := fun i r => treeStagesHalvingProducts (width₂ i) next (treeStagesHalvingUpdate K (q.ctx₂ i) (width₂ i) j (p₂ i) (out₂ i) r)
  len₁ := by intros; rfl
  len₂ := by intros; rfl
  body₁ := fun i r => treeStagesHalvingBody K (q.ctx₁ i) (width₁ i) next remaining
    (treeStagesHalvingUpdate K (q.ctx₁ i) (width₁ i) j (p₁ i) (out₁ i) r) (finish₁ i)
  body₂ := fun i r => treeStagesHalvingBody K (q.ctx₂ i) (width₂ i) next remaining
    (treeStagesHalvingUpdate K (q.ctx₂ i) (width₂ i) j (p₂ i) (out₂ i) r) (finish₂ i)

theorem treeStages_halvingReduction_afterCoin₁ (D : C.Coalition) (q : TreeStagesReductionContext K D)
    (width₁ width₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → (ℕ → E) × (ℕ → E) × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    (treeStagesHalvingReduction K D q width₁ width₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).afterCoin₁ K D =
      fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
        (treeStagesHalvingBody K (q.ctx₁ i) (width₁ i) j (next :: remaining) (p₁ i) (finish₁ i) (out₁ i, q.st₁ i)) := by
  funext i values
  unfold TreeStagesChallengeReduction.afterCoin₁
  congr 1
  funext r
  rw [treeStages_halvingBody_next]
  rfl

theorem treeStages_halvingReduction_afterCoin₂ (D : C.Coalition) (q : TreeStagesReductionContext K D)
    (width₁ width₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → (ℕ → E) × (ℕ → E) × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    (treeStagesHalvingReduction K D q width₁ width₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).afterCoin₂ K D =
      fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
        (treeStagesHalvingBody K (q.ctx₂ i) (width₂ i) j (next :: remaining) (p₂ i) (finish₂ i) (out₂ i, q.st₂ i)) := by
  funext i values
  unfold TreeStagesChallengeReduction.afterCoin₂
  congr 1
  funext r
  rw [treeStages_halvingBody_next]
  rfl

/-- Two real driver rounds between successive halving challenges, with
actual Shamir products, bounded challenge rejection and selective abort. -/
theorem treeStages_halving_two_rounds (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (q : TreeStagesReductionContext K D) (width₁ width₂ : C.Party → ℕ) (j next : ℕ) (remaining : List ℕ)
    (p₁ p₂ : C.Party → (ℕ → E) × (ℕ → E) × E) (out₁ out₂ : C.Party → Shares C E)
    (finish₁ finish₂ : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (old : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0)
    (future : TreeSimFutureZero (q.label + 2) old) (live : C.Party → Bool)
    (coinRnd : C.Party → PrssOutput C E) (base : HashCache C)
    (covered : ∀ i values, values.length = 1 → TreeStagesChallengeCovered K base (q.tag i) (q.hashLabel i) values)
    (state : A.State) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h : TreeSimStreamRel old a b) (fresh : TreeSimFutureEmpty (q.label + 1) a.1.2) (base_le : base ≤ a.1.1) :
    RelTriple
      ((executeSteps (treeSimRealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd q.st₁ (fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
          (treeStagesHalvingBody K (q.ctx₁ i) (width₁ i) j (next :: remaining) (p₁ i) (finish₁ i) (out₁ i, q.st₁ i))))).run a)
      ((executeSteps (treeSimIdealRoles prims D) D A noFunctionality 2 state
        (treeSimCoinPartial K D live 1 coinRnd q.st₂ (fun i => treeStagesChallengeTail K (q.tag i) (q.hashLabel i)
          (treeStagesHalvingBody K (q.ctx₂ i) (width₂ i) j (next :: remaining) (p₂ i) (finish₂ i) (out₂ i, q.st₂ i))))).run b)
      (fun u z => (treeStagesHalvingReduction K D q width₁ width₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).Result K D A base coinRnd u z ∧ base ≤ u.2.1.1) := by
  have coupled := (treeStagesHalvingReduction K D q width₁ width₂ j next remaining p₁ p₂ out₁ out₂ finish₁ finish₂).coupling_base
    prims K D A old visible future live coinRnd base covered state a b h fresh base_le
  simp only [treeStages_halvingReduction_afterCoin₁, treeStages_halvingReduction_afterCoin₂] at coupled
  exact coupled

/-- Remaining reachable-core construction only on good common-prefix logs.
The bad-prefix case is proved above. The shared-cache dealer and padding are
retained exactly as in the frozen assembly theorem. Reduction transitions can
use `treeStages_extendMult_challenge_preserves` and
`treeStages_digest_challenge_preserves`. Salt sampling and the entire digest
transition are proved by `treeStages_saltedDigest_challenge` for equal held
histories. The remaining construction must still identify reachable boundaries,
compose the unequal-history digest transports, meet the core's public-cache
equality requirement for those transports, and close the invariant across
the actual ceremony batches. `treeStages_finalMask_simBatch_finish` proves the
actual final-check/output suffix, including the simulator's clear queries and
unbounded correction. `treeStagesOutputPadding` supplies its cache coverage.
Reachability must still supply its Shamir/residual and internal-share equations,
justify the late translation, and assemble the whole-ceremony invariant.
`treeStages_simBatch_next_rounds` proves the nonterminal check/OpenRep/
public-computation/next-batch transition in either mode, including actual next
input and PRSS queries. The `runJobs` entry is identified by
`treeStages_actualBatchData`. `treeStages_batch_collector_first_round` proves
actual input replay, adapted collector masks and the first rushing exchange.
`TreeStagesCollectorLayer.boundary_round` proves the following actual layer
transitions, with concrete successor recipes and selective abort.
`treeStages_collector_ceremonyBatch_check` composes actual input queries,
all collector layers and Rerand up to the first check Coin, using the exact
real/dummy keys and padding coverage. `treeStages_ceremonyBatch_check` now
handles either mode. `treeStages_peer_input_runJobs_check` additionally covers
zero-output batches with nonempty AND tuples. Zero-output collector batches,
empty checks, the complete check invariant and the whole-ceremony relation remain.
`treeStages_firstCheck_padded_two_rounds` proves the actual first check Coin,
expansion/rejection and first slice exchange up to its next challenge Coin,
including inherited aborts and early driver stopping. Its finite padding
preserves the existing dealer cache and discharges coverage for all possible
rushing replies. The stage retains exact tuples, products and saved check
continuations. Connecting it to the earlier layer certificates still requires
the equality of accumulated tuple counts; subsequent slice/halving iterations
must carry the check's algebraic invariant through the final masked opening.
`treeStages_core_of_reachable_relation` discharges replay and corrupt outputs
from the exact bounded trace; its relation, progress and transition premises
still need to be instantiated for the complete ceremony.
`treeStagesCeremonyPrfPadding` establishes PRF coverage for all later jobs. `treeStages_split_digest_round` discharges
the rejected check exchange from logged split histories under a digest transport;
it assumes neither probability bound nor any later continuation coupling.
`treeStages_saltedDigest_split_finish` closes the complete split-history suffix
from salt generation, deriving the certificates rather than assuming them.
`treeStages_split_digest_finish` closes final observation under a digest swap. -/
def TreeSimStagesGoodCoreGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    Nonempty (TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z p.1 p.2.1
      ((r.2, p.2.2.1.2), p.2.2.2)
      (fun t => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2))

/-- Assembly only; the reachable-core premise remains to be discharged. -/
theorem treeSimStagesGoalClosed (cores : TreeSimStagesGoodCoreGoal prims K circuits settings) :
    TreeSimStagesGoal prims K circuits settings := by
  apply treeSimStagesGoal_of_cores prims K circuits settings
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  by_cases bad : TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2
  · refine ⟨pure (), fun r hr => ?_⟩
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨treeStages_badCore prims K circuits settings top tree D A parameter seeds pairs z p.1 p.2.1 p.2.2 bad⟩
  · exact cores hb top tree D A parameter seeds pairs z Z q hq hsmall p hp bad

/-- info: 'ThresholdLeanXmssSecurity.treeStages_fieldDraws_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_fieldDraws_closed

/-- info: 'ThresholdLeanXmssSecurity.treeStages_extendMult_real_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_extendMult_real_start

/-- info: 'ThresholdLeanXmssSecurity.treeStages_extendMult_aborted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_extendMult_aborted

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesExtendMultChallenge.coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesExtendMultChallenge.coupling

/-- info: 'ThresholdLeanXmssSecurity.treeStages_extendMult_challenge_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_extendMult_challenge_preserves

/-- info: 'ThresholdLeanXmssSecurity.treeStages_challenge_coinClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_challenge_coinClosure

/-- info: 'ThresholdLeanXmssSecurity.treeStages_saltedDigest_challenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_saltedDigest_challenge

/-- info: 'ThresholdLeanXmssSecurity.treeStages_digest_challenge_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_digest_challenge_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimExtendMultExitRel.history_unfilled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeSimExtendMultExitRel.history_unfilled

/-- info: 'ThresholdLeanXmssSecurity.treeStages_local_digestSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_local_digestSwap

/-- info: 'ThresholdLeanXmssSecurity.treeStages_hiddenDigest_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_hiddenDigest_fresh

/-- info: 'ThresholdLeanXmssSecurity.treeStages_split_digest_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_split_digest_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_observe_digestSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_observe_digestSwap

/-- info: 'ThresholdLeanXmssSecurity.treeStages_split_digest_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_split_digest_finish

/-- info: 'ThresholdLeanXmssSecurity.treeStages_saltedDigest_partial_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_saltedDigest_partial_log

/-- info: 'ThresholdLeanXmssSecurity.treeStages_saltedDigest_split_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_saltedDigest_split_finish

/-- info: 'ThresholdLeanXmssSecurity.treeStages_copyPadding_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_copyPadding_covered

/-- info: 'ThresholdLeanXmssSecurity.treeStages_open_entry_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_open_entry_padded

/-- info: 'ThresholdLeanXmssSecurity.treeStages_finalMask_open_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_finalMask_open_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_check_open_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_check_open_finish

/-- info: 'ThresholdLeanXmssSecurity.treeStages_openRep_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_openRep_prefix

/-- info: 'ThresholdLeanXmssSecurity.treeStages_check_shift_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_check_shift_finish

/-- info: 'ThresholdLeanXmssSecurity.treeStages_evalJobs_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_evalJobs_replay

/-- info: 'ThresholdLeanXmssSecurity.treeStages_simOutput_advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_simOutput_advance

/-- info: 'ThresholdLeanXmssSecurity.treeStages_outputPadding_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_outputPadding_covered

/-- info: 'ThresholdLeanXmssSecurity.treeStages_simBatch_check_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_simBatch_check_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_simBatch_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_simBatch_finish

/-- info: 'ThresholdLeanXmssSecurity.treeStages_finalMask_simBatch_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_finalMask_simBatch_finish

/-- info: 'ThresholdLeanXmssSecurity.treeStages_inputQueries_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_inputQueries_replay

/-- info: 'ThresholdLeanXmssSecurity.treeStages_batchPeer_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_batchPeer_entry

/-- info: 'ThresholdLeanXmssSecurity.treeStages_actualPeerBatchData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_actualPeerBatchData

/-- info: 'ThresholdLeanXmssSecurity.treeStages_openBatchPeer_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_openBatchPeer_boundary

/-- info: 'ThresholdLeanXmssSecurity.treeStages_openPublicBatchPeer_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_openPublicBatchPeer_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_ceremonyPrfPadding_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_ceremonyPrfPadding_covered

/-- info: 'ThresholdLeanXmssSecurity.treeStages_simBatch_resume_check_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_simBatch_resume_check_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_simBatch_nextPeer_rounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_simBatch_nextPeer_rounds

/-- info: 'ThresholdLeanXmssSecurity.treeStages_reshare_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_reshare_entry

/-- info: 'ThresholdLeanXmssSecurity.treeStages_batch_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_batch_entry

/-- info: 'ThresholdLeanXmssSecurity.treeStages_actualBatchData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_actualBatchData

/-- info: 'ThresholdLeanXmssSecurity.treeStages_simBatch_next_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_simBatch_next_rounds

/-- info: 'ThresholdLeanXmssSecurity.treeStages_outputWitness_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_outputWitness_padded

/-- info: 'ThresholdLeanXmssSecurity.treeStages_reach_outputWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_reach_outputWitness

/-- info: 'ThresholdLeanXmssSecurity.treeStages_reach_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_reach_corrupt

/-- info: 'ThresholdLeanXmssSecurity.treeStages_core_of_reachable_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_core_of_reachable_relation

/-- info: 'ThresholdLeanXmssSecurity.treeStages_batch_collector_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_batch_collector_boundary

/-- info: 'ThresholdLeanXmssSecurity.treeStages_batch_collector_first_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_batch_collector_first_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_exit_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_exit_values

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_next_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_next_layer

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorLayer.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorLayer.round

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorLayer.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorLayer.actual

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorLayer.boundary_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorLayer.boundary_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_peer_resume_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_peer_resume_entry

/-- info: 'ThresholdLeanXmssSecurity.treeStages_layers_rerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_layers_rerand

/-- info: 'ThresholdLeanXmssSecurity.treeStages_peer_resume_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_peer_resume_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesPeerNext.coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesPeerNext.coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorTail.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorTail.round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_check_coin_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_check_coin_entry

/-- info: 'ThresholdLeanXmssSecurity.treeStages_rerand_coin_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_rerand_coin_entry

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesRerandTail.coin_boundary_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesRerandTail.coin_boundary_round

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesRerandTail.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesRerandTail.execute

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorTail.execute_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorTail.execute_check

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorTail.execute_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorTail.execute_three

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorSchedule.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorSchedule.next

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorSchedule.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorSchedule.round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_partial_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_partial_execute

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesCollectorSchedule.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesCollectorSchedule.execute

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_runJobs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_runJobs

/-- info: 'ThresholdLeanXmssSecurity.treeStages_zeroDepth_runJobs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_zeroDepth_runJobs

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_runJobs_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_runJobs_check

/-- info: 'ThresholdLeanXmssSecurity.treeStages_inputQueries_onHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_inputQueries_onHash

/-- info: 'ThresholdLeanXmssSecurity.treeStages_batch_collector_start_logged_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_batch_collector_start_logged_frame

/-- info: 'ThresholdLeanXmssSecurity.treeStages_batch_peer_start_logged_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_batch_peer_start_logged_frame

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_input_runJobs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_input_runJobs

/-- info: 'ThresholdLeanXmssSecurity.treeStages_zeroDepth_input_runJobs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_zeroDepth_input_runJobs

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_input_runJobs_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_input_runJobs_check

/-- info: 'ThresholdLeanXmssSecurity.treeStages_collector_ceremonyBatch_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_collector_ceremonyBatch_check

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesRerandTail.execute_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesRerandTail.execute_nonempty

/-- info: 'ThresholdLeanXmssSecurity.treeStages_peer_exit_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_peer_exit_values

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesPeerSchedule.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesPeerSchedule.round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_peer_partial_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_peer_partial_execute

/-- info: 'ThresholdLeanXmssSecurity.TreeStagesPeerSchedule.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeStagesPeerSchedule.execute

/-- info: 'ThresholdLeanXmssSecurity.treeStages_peer_input_runJobs_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_peer_input_runJobs_check

/-- info: 'ThresholdLeanXmssSecurity.treeStages_input_runJobs_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_input_runJobs_check

/-- info: 'ThresholdLeanXmssSecurity.treeStages_ceremonyBatch_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_ceremonyBatch_check

/-- info: 'ThresholdLeanXmssSecurity.treeStages_checkExpansion_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_checkExpansion_replay

/-- info: 'ThresholdLeanXmssSecurity.treeStages_check_firstSlice_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_check_firstSlice_start

/-- info: 'ThresholdLeanXmssSecurity.treeStages_checkPadding_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_checkPadding_covered

/-- info: 'ThresholdLeanXmssSecurity.treeStages_check_coin_firstSlice_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_check_coin_firstSlice_round

/-- info: 'ThresholdLeanXmssSecurity.treeStages_firstCheck_two_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStages_firstCheck_two_rounds

/-- info: 'ThresholdLeanXmssSecurity.treeStages_firstCheck_partial_two_rounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_firstCheck_partial_two_rounds

/-- info: 'ThresholdLeanXmssSecurity.treeStages_firstCheck_padded_two_rounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeStages_firstCheck_padded_two_rounds

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoalClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimStagesGoalClosed

end ThresholdLeanXmssSecurity
