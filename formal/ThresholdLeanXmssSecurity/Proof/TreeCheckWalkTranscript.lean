import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkConsistent
import ThresholdLeanXmssSecurity.Proof.TreeCheckMaskExtraction
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoupling

/-!
# Transcript agreement of the fixed source walk

This file concerns `WalkTranscript` of `TreeCheckWalkConsistent` for the fixed
family `family` of `TreeCheckWalkRecipe`. The family, its decoder and its
witness are not changed.

## Scheduler lemmas

These lemmas read one replay of the real scheduler with a coalition `D`. The
replay keeps the corrupt messages and the honest outboxes of each round.

* `rounds_done_none` and `phase_stop` show that an operator that stops keeps
  the output `none`.
* `phase_local` takes the local draws at the head of a phase. Each honest
  operator gets one value, and the phase goes on with these values.
* `phase_exchange` takes one exchange round. Honest operator `i` gets
  `sent k i` from a corrupt `k` and the outbox of an honest `k`. An abort frame
  stops `i`, so a phase with all honest outputs has no abort frame.
* `phase_pure` reads the outputs of programs that return at once.

## Agreement lemmas

* `term_mask` reads a term mask of a PRSS draw as the stream answer of its
  key, label, index and position. `streamAnswer_unique` shows that this answer
  is unique in one cache. So `draw_masks` gives equal term masks to honest
  holders with equal term keys at a common label.
* `peer_agree` uses `treeSim_reshareZ_value`. An honest filler sends one value
  to all holders, and a term with no filler keeps its mask.
* `collector_agree` uses `collector_value`. An honest collector forwards one
  sum to all holders of its term.
* `gadget_agree`, `layer_agree` and `layers_agree` carry `SavedAgree` through
  the real layers. The products of earlier layers do not enter the agreement,
  because the filler value and the masks do not depend on them.

## Boundary and walk lemmas

* `boundary_inputs` gives equal term inputs from equal term seeds. The input
  shares are PRF values that the final hash cache fixes.
* `boundary_products` gives `SavedAgree` for the checkpoint rows of a tail
  boundary. All honest rows are present, so the pending tails and the input
  queries return, and the layers and the final peer `rerand` follow.
* `transcript_of_keys` gives `Transcript` of a walk from common term seeds and
  from common term keys at its live checkpoints.
* `walkTranscript` gives `WalkTranscript`. `DealtInputs` gives the common
  seeds. `TreeCheckWalkCoupling.checkpointFacts` gives the setup rows and the
  common term keys. `walkConsistent` then gives `WalkConsistent` by
  `walkConsistent_of_transcript`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkTranscript

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

section Scheduler

variable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)

-- The private `treeSimCheck_sequence_allowed` of `TreeSimCheck.lean`, kept with its original proof.
theorem sequence_allowed {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (allowed : (t : spec.Domain) → spec.Range t → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α) (x : Fin n → α),
    TreeSimCheckAllowed allowed (Concrete.sequenceFin f) x →
      ∀ i, TreeSimCheckAllowed allowed (f i) (x i)
  | 0, _, _, _, i => i.elim0
  | n + 1, f, x, hx, i => by
    simp only [Concrete.sequenceFin] at hx
    obtain ⟨a, ha, hrest⟩ := hx.bind_inv
    obtain ⟨t, htail, he⟩ := hrest.bind_inv
    have he := he.pure_inv
    subst x
    cases i using Fin.cases with
    | zero => exact ha
    | succ i => exact sequence_allowed allowed (fun i : Fin n => f i.succ) t htail i

/-- A stopped operator keeps the output `none` in every later round. -/
theorem rounds_done_none {α : Type} (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executeRounds worldRoles D A noFunctionality fuel state steps) r)
    (i : C.Party) (stopped : steps i = .done none) : r.2 i = none := by
  induction fuel generalizing state steps r with
  | zero =>
    rw [run.pure_inv]
    simp [stopped, Step.output]
  | succ fuel ih =>
    unfold executeRounds at run
    split_ifs at run with hd
    · rw [run.pure_inv]
      simp [stopped, Step.output]
    · obtain ⟨next, hn, rest⟩ := run.bind_inv
      rw [stepRound_real] at hn
      obtain ⟨b, -, hn⟩ := hn.bind_inv
      obtain ⟨nexts, hs, he⟩ := hn.bind_inv
      have he := he.pure_inv
      subst next
      rw [free_sequenceFin] at hs
      have hi := TreeCheckMaskExtraction.allowed_free allowed _ _
        (sequence_allowed allowed _ _ hs i)
      simp only [roundLocal, stopped] at hi
      exact ih _ _ _ rest hi.pure_inv

/-- The local draws at the head of a phase give one value to each honest
operator. The phase goes on with these values. -/
theorem phase_local {α β : Type} [Inhabited β] (fuel : ℕ) (state : A.State)
    (draw : C.Party → OracleComp (LocalSpec C) β) (next : C.Party → β → PartyM C E RealSpec α)
    (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state
      (fun i => localStep (draw i) >>= next i)) r) :
    ∃ values : C.Party → β,
      (∀ i, i ∉ D.1 → TreeSimCheckAllowed (fun t u => allowed (.inr t) u) (draw i) (values i)) ∧
      TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state
        (fun i => next i (values i))) r := by
  unfold executePhase at run ⊢
  obtain ⟨steps, hs, hr⟩ := run.bind_inv
  have split : (fun i => if i ∈ D.1 then pure (Step.done none) else
      worldRoles.honest (advance (localStep (draw i) >>= next i).run) :
        C.Party → OracleComp (WorldSpec C) (Step C E RealSpec α)) =
      fun i => (if i ∈ D.1 then pure default else free (draw i)) >>= fun b =>
        if i ∈ D.1 then pure (Step.done none) else free (advance (next i b).run) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp only [if_neg hi, advance_localStep_bind]
      exact free_bind _ _
  unfold startSteps at hs
  rw [split] at hs
  obtain ⟨values, each, rest⟩ :=
    TreeCheckMaskExtraction.allowed_sequence_bind allowed _ _ steps hs
  refine ⟨values, fun i hi => ?_, rest.bind hr⟩
  have hv := each i
  simp only [if_neg hi] at hv
  exact TreeCheckMaskExtraction.allowed_free allowed _ _ hv

/-- An operator whose program stops at once has no output. -/
theorem phase_stop {α : Type} (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state
      program) r)
    (i : C.Party) (stopped : advance (program i).run = pure (.done none)) : r.2 i = none := by
  unfold executePhase at run
  obtain ⟨steps, hs, hr⟩ := run.bind_inv
  have hi := sequence_allowed allowed _ _ hs i
  apply rounds_done_none D A allowed fuel state steps r hr i
  by_cases hD : i ∈ D.1
  · simp only [if_pos hD] at hi
    exact hi.pure_inv
  · simp only [if_neg hD] at hi
    change TreeSimCheckAllowed allowed (free (advance (program i).run)) (steps i) at hi
    rw [stopped, free_pure] at hi
    exact hi.pure_inv

/-- A phase whose programs return at once gives these values to the honest
operators. -/
theorem phase_pure {α : Type} (fuel : ℕ) (state : A.State) (value : C.Party → α)
    (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state
      (fun i => pure (value i))) r)
    (i : C.Party) (hi : i ∉ D.1) : r.2 i = some (value i) := by
  unfold executePhase at run
  obtain ⟨steps, hs, hr⟩ := run.bind_inv
  have each : ∀ k, steps k = if k ∈ D.1 then .done none else .done (some (value k)) := by
    intro k
    have hk := sequence_allowed allowed _ _ hs k
    by_cases hD : k ∈ D.1
    · simp only [if_pos hD] at hk ⊢
      exact hk.pure_inv
    · simp only [if_neg hD] at hk ⊢
      change TreeSimCheckAllowed allowed (free (advance (pure (value k) : PartyM C E RealSpec α).run))
        (steps k) at hk
      rw [advance_run_pure, free_pure] at hk
      exact hk.pure_inv
  cases fuel with
  | zero =>
    rw [hr.pure_inv]
    simp [each i, hi, Step.output]
  | succ fuel =>
    unfold executeRounds at hr
    rw [if_pos (fun k hk => by simp [each k, hk, Step.isDone])] at hr
    rw [hr.pure_inv]
    simp [each i, hi, Step.output]

/-- One exchange round of a phase. Each honest operator gets the corrupt
messages and the honest outboxes. If an honest operator gets an abort frame,
it has no output, so a phase with all honest outputs has no abort frame. -/
theorem phase_exchange {α : Type} (fuel : ℕ) (state : A.State)
    (out : C.Party → Mail C E) (f : C.Party → Mail C E → PartyM C E RealSpec α)
    (honest : ∃ i, i ∉ D.1)
    (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality (fuel + 1) state
      (fun i => exchange (out i) >>= f i)) r)
    (present : ∀ i, i ∉ D.1 → (r.2 i).isSome) :
    ∃ (state' : A.State) (sent : C.Party → Mail C E),
      TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state'
        (fun i => f i (fun k => if k ∈ D.1 then sent k i else out k i))) r := by
  unfold executePhase at run ⊢
  obtain ⟨steps, hs, hr⟩ := run.bind_inv
  have each : ∀ k, steps k =
      if k ∈ D.1 then .done none else .wait (out k) (exchangeResume (f k)) := by
    intro k
    have hk := sequence_allowed allowed _ _ hs k
    by_cases hD : k ∈ D.1
    · simp only [if_pos hD] at hk ⊢
      exact hk.pure_inv
    · simp only [if_neg hD] at hk ⊢
      change TreeSimCheckAllowed allowed (free (advance (exchange (out k) >>= f k).run))
        (steps k) at hk
      rw [advance_exchange_bind, free_pure] at hk
      exact hk.pure_inv
  obtain ⟨i₀, hi₀⟩ := honest
  unfold executeRounds at hr
  rw [if_neg (fun h => by simpa [each i₀, hi₀, Step.isDone] using h i₀ hi₀)] at hr
  obtain ⟨next, hn, rest⟩ := hr.bind_inv
  rw [stepRound_real] at hn
  obtain ⟨b, -, hn⟩ := hn.bind_inv
  obtain ⟨nexts, hns, he⟩ := hn.bind_inv
  have he := he.pure_inv
  subst next
  rw [free_sequenceFin] at hns
  have local_eq : ∀ i, roundLocal D steps b.2 i =
      if i ∈ D.1 then pure (.done none) else
        advance (exchangeResume (f i) (fun k => if k ∈ D.1 then b.2 k i else out k i)) := by
    intro i
    have inbox : (fun k => if k ∈ D.1 then b.2 k i else (steps k).delivered i) =
        fun k => if k ∈ D.1 then b.2 k i else out k i := by
      funext k
      by_cases hk : k ∈ D.1 <;> simp [hk, each k]
    unfold roundLocal
    by_cases hD : i ∈ D.1
    · simp [each i, hD]
    · simp only [each i, if_neg hD]
      rw [inbox]
  have clear : ∀ i, i ∉ D.1 → (C.parties.any fun k => Msg.isAbort
      (if k ∈ D.1 then b.2 k i else out k i)) = false := by
    intro i hi
    by_contra hab
    simp only [Bool.not_eq_false] at hab
    have hc := TreeCheckMaskExtraction.allowed_free allowed _ _
      (sequence_allowed allowed _ _ hns i)
    rw [local_eq i, if_neg hi, exchangeResume, if_pos hab, advance_pure] at hc
    have stopped := rounds_done_none D A allowed fuel b.1 nexts r rest i hc.pure_inv
    simpa [stopped] using present i hi
  have programs : (fun i => free (roundLocal D steps b.2 i)) =
      fun i => if i ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (f i (fun k => if k ∈ D.1 then b.2 k i else out k i)).run) := by
    funext i
    rw [local_eq i]
    by_cases hD : i ∈ D.1
    · simp [hD]
    · simp only [if_neg hD, exchangeResume, clear i hD]
      rfl
  rw [programs] at hns
  exact ⟨b.1, b.2, hns.bind rest⟩

end Scheduler

section Masks

variable [Field E] [Algebra Bit E]

theorem streamAnswer_unique (prims : Primitives) (D : C.Coalition)
    {s : HashCache C × HiddenCache C} {x : PrgInput C} {u u' : Bit}
    (h : TreeLockstepStreamAnswer prims D s x u) (h' : TreeLockstepStreamAnswer prims D s x u') :
    u = u' := by
  unfold TreeLockstepStreamAnswer at h h'
  split_ifs at h h'
  · exact Option.some.inj (h.symm.trans h')
  · obtain ⟨d, hd, rfl⟩ := h
    obtain ⟨d', hd', rfl⟩ := h'
    rw [Option.some.inj (hd.symm.trans hd')]

-- The private `treeLockstep_allowed_mapM_get` of `TreeLockstepOpenedFinal.lean`, without its length clause.
theorem allowed_mapM_get {ι α β : Type} {S : OracleSpec.{0, 0} ι}
    (allowed : (t : S.Domain) → S.Range t → Prop) (f : α → OracleComp S β) :
    ∀ (xs : List α) (ys : List β), TreeSimCheckAllowed allowed (xs.mapM f) ys →
      ∀ (n : ℕ) x, xs[n]? = some x → ∃ y, ys[n]? = some y ∧ TreeSimCheckAllowed allowed (f x) y
  | [], ys, _, n, x, hx => by simp at hx
  | a :: xs, ys, h, n, x, hx => by
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, ht⟩ := h.bind_inv
    obtain ⟨tail, htail, he⟩ := ht.bind_inv
    have he : ys = y :: tail := he.pure_inv
    subst ys
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst x
      exact ⟨y, rfl, hy⟩
    | succ n => exact allowed_mapM_get allowed f xs tail htail n x (by simpa using hx)

/-- The term `T` mask of a PRSS draw is the stream answer of its term key,
label, index and position. -/
theorem term_mask (prims : Primitives) (D : C.Coalition) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u → TreeLockstepStreamAnswer prims D cache x u)
    (ctx : Context C) (label idx count : ℕ) (rnd : PrssOutput C Bit)
    (run : TreeSimCheckAllowed allowed (prssDraw ctx (bitCodec (E := E)) label idx count) rnd)
    (T : C.Term) (held : ctx.self ∈ C.holders T) (g : ℕ) (hg : g < count) :
    TreeLockstepStreamAnswer prims D cache (.term T, ctx.prss.term T, label, idx, g) (rnd.1 T g) := by
  unfold prssDraw termDraws at run
  obtain ⟨rr, hrr, rest⟩ := run.bind_inv
  obtain ⟨zz, -, result⟩ := rest.bind_inv
  rw [result.pure_inv]
  have mem : C.terms[C.terms.idxOf T]? = some T := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (by simp [Committee.terms]))]
    simp [List.getElem_idxOf]
  obtain ⟨y, hy, hdraw⟩ := allowed_mapM_get allowed _ C.terms rr hrr _ T mem
  simp only [if_pos held] at hdraw
  have answers := (treeLockstep_prg_stream_answers prims D cache allowed streams (.term T)
    (ctx.prss.term T) label idx count y hdraw).1 g hg
  simpa only [List.getD_eq_getElem?_getD, hy, Option.getD_some] using answers

end Masks

section Agreement

variable [Field E] [Algebra Bit E] (K : Constants C E) (D : C.Coalition)

/-- No corrupt operator fills position `g` of term `T`. -/
def Unfilled (mode : ReshareMode) (T : C.Term) (g : ℕ) : Prop :=
  ¬ ∃ j ∈ D.1, filler K mode T g = some j

/-- Two honest holders of a term have equal term masks below `count`. -/
def MaskAgree (count : ℕ) (rnd : C.Party → PrssOutput C Bit) : Prop :=
  ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
    ∀ g < count, (rnd i).1 T g = (rnd k).1 T g

/-- Two honest holders of a term have equal products below `count` at each
position that no corrupt operator fills. -/
def ZAgree (mode : ReshareMode) (count : ℕ) (z : C.Party → Shares C Bit) : Prop :=
  ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
    ∀ g < count, Unfilled K D mode T g → z i T g = z k T g

theorem peer_filler (T : C.Term) (g : ℕ) (j : C.Party) (filled : K.filled j = T) :
    filler K .peer T g = some j := by
  unfold filler
  obtain ⟨j', hj', hf⟩ : ∃ j', C.parties.find? (K.filled · = T) = some j' ∧ K.filled j' = T := by
    have some : (C.parties.find? (K.filled · = T)).isSome := by
      rw [List.find?_isSome]
      exact ⟨j, by simp [Committee.parties], by simp [filled]⟩
    obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp some
    exact ⟨j', hj', by simpa using List.find?_some hj'⟩
  change List.find? (fun x => decide (K.filled x = T)) C.parties = some j
  rw [hj', K.filled.injective (hf.trans filled.symm)]

/-- An honest filler sends one value to all holders of its term, and a term
with no filler keeps its common mask. -/
theorem peer_agree (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (count : ℕ)
    (sent : C.Party → Mail C E) (masks : MaskAgree D count rnd) :
    ZAgree K D .peer count (fun i => reshareZ K (ctx i) (bitCodec (E := E)) (rnd i).1 (rnd i).2
      (v i) count (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) bitCodec (rnd j).1 (rnd j).2 (v j) count i)) := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  intro T i k hiT hkT hi hk g hg unfilled
  dsimp only
  rw [treeSim_reshareZ_value K D ctx self rnd v count sent i hi T g,
    treeSim_reshareZ_value K D ctx self rnd v count sent k hk T g]
  simp only [hiT, hkT, not_true_eq_false, false_or, show ¬ count ≤ g by omega, if_false]
  unfold treeSimPeerValue
  split_ifs with hT
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjD : j ∉ D.1 := fun hjD => unfilled
      ⟨j, hjD, peer_filler K T g j (Finset.mem_filter.mp hj).2⟩
    simp only [if_neg hjD]
  · exact masks T i k hiT hkT hi hk g hg

/-- The products of an honest holder at a position of an honest collector are
the sum that the collector forms. -/
theorem collector_value (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (count : ℕ)
    (sent₁ sent₂ : C.Party → Mail C E) (T : C.Term) (g : ℕ) (hg : g < count)
    (star : T = (K.collector g).1) (honestCollector : (K.collector g).2 ∉ D.1)
    (h : C.Party) (hh : h ∉ D.1) (held : h ∈ C.holders T) :
    colZ K (ctx h).self (rnd h).1 (rnd h).2 (v h) count
        (fun k => if k ∈ D.1 then sent₁ k h else
          colOut1 K (ctx k).self (rnd k).1 (rnd k).2 (v k) count h)
        (fun k => if k ∈ D.1 then sent₂ k h else
          colOut2 K (ctx k).self (rnd k).1 (rnd k).2 (v k) count
            (fun k' => if k' ∈ D.1 then sent₁ k' k else
              colOut1 K (ctx k').self (rnd k').1 (rnd k').2 (v k') count k) h) T g =
      colSum K (K.collector g).2 (rnd (K.collector g).2).1 (rnd (K.collector g).2).2
        (v (K.collector g).2) count
        (fun k' => if k' ∈ D.1 then sent₁ k' (K.collector g).2 else
          colOut1 K (ctx k').self (rnd k').1 (rnd k').2 (v k') count (K.collector g).2) g := by
  unfold colZ
  rw [self h hh, if_neg (by simp [held]; omega), if_pos star]
  by_cases hκ : (K.collector g).2 = h
  · rw [if_pos hκ]
    subst hκ
    rfl
  · rw [if_neg hκ]
    dsimp only
    rw [if_neg honestCollector]
    have hmem : g ∈ forwardedTo K count (K.collector g).2 h :=
      List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_range.2 hg, by simp⟩,
        by simpa [← star] using held⟩
    simp only [colOut2, self _ honestCollector, ne_eq, Ne.symm hκ, not_false_eq_true, if_true,
      Msg.bitAt]
    exact getD_map_idxOf' hmem _

/-- An honest collector forwards one sum to all holders of its term, and a
term with no filler keeps its common mask. -/
theorem collector_agree (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (count : ℕ)
    (sent₁ sent₂ : C.Party → Mail C E) (masks : MaskAgree D count rnd) :
    ZAgree K D .collector count (fun i => colZ K (ctx i).self (rnd i).1 (rnd i).2 (v i) count
        (fun k => if k ∈ D.1 then sent₁ k i else
          colOut1 K (ctx k).self (rnd k).1 (rnd k).2 (v k) count i)
        (fun k => if k ∈ D.1 then sent₂ k i else
          colOut2 K (ctx k).self (rnd k).1 (rnd k).2 (v k) count
            (fun k' => if k' ∈ D.1 then sent₁ k' k else
              colOut1 K (ctx k').self (rnd k').1 (rnd k').2 (v k') count k) i)) := by
  intro T i k hiT hkT hi hk g hg unfilled
  dsimp only
  by_cases star : T = (K.collector g).1
  · have honestCollector : (K.collector g).2 ∉ D.1 := fun hD =>
      unfilled ⟨_, hD, by simp [filler, star]⟩
    rw [collector_value K D ctx self rnd v count sent₁ sent₂ T g hg star honestCollector i hi hiT,
      collector_value K D ctx self rnd v count sent₁ sent₂ T g hg star honestCollector k hk hkT]
  · unfold colZ
    have hi' : ¬ (i ∉ C.holders T ∨ count ≤ g) := by simp [hiT]; omega
    have hk' : ¬ (k ∉ C.holders T ∨ count ≤ g) := by simp [hkT]; omega
    rw [self i hi, self k hk, if_neg hi', if_neg hk', if_neg star, if_neg star]
    exact masks T i k hiT hkT hi hk g hg

end Agreement

section Layers

variable [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty) (cache : HashCache C × HiddenCache C)
variable (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
variable (streams : ∀ x u, allowed (.inr (.inr (.inr x))) u →
  TreeLockstepStreamAnswer prims D cache x u)
variable (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
variable (keys : ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
  (ctx i).prss.term T = (ctx k).prss.term T)

/-- Two honest holders of a term have equal unfilled products in each saved
tuple. -/
def SavedAgree (q : C.Party → List (Tuple C)) : Prop :=
  ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
    (q i).map (TreeCheckWalkConsistent.unfilledView K D T) =
      (q k).map (TreeCheckWalkConsistent.unfilledView K D T)

theorem savedAgree_nil : SavedAgree K D (fun _ => []) := fun _ _ _ _ _ _ _ => rfl

theorem savedAgree_append (q : C.Party → List (Tuple C)) (saved : SavedAgree K D q)
    (mode : ReshareMode) (count : ℕ) (x y z : C.Party → Shares C Bit)
    (agree : ZAgree K D mode count z) :
    SavedAgree K D (fun i => q i ++ [⟨x i, y i, z i, count, mode⟩]) := by
  intro T i k hiT hkT hi hk
  simp only [List.map_append, List.map_cons, List.map_nil, saved T i k hiT hkT hi hk]
  congr 2
  unfold TreeCheckWalkConsistent.unfilledView
  apply vector_congr
  intro g hg
  split_ifs with filled
  · rfl
  · exact agree T i k hiT hkT hi hk g hg filled

include streams self keys in
/-- The masks of one PRSS draw at a common label agree for honest holders. -/
theorem draw_masks (label count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (each : ∀ i, i ∉ D.1 → TreeSimCheckAllowed (fun t u => allowed (.inr t) u)
      (liftComp (prssDraw (ctx i) (bitCodec (E := E)) label 0 count) (LocalSpec C)) (rnd i)) :
    MaskAgree D count rnd := by
  have answer : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count,
      TreeLockstepStreamAnswer prims D cache (.term T, (ctx i).prss.term T, label, 0, g)
        ((rnd i).1 T g) := by
    intro i hi T held g hg
    have ro : TreeSimCheckAllowed (fun t u => allowed (.inr (.inr t)) u)
        (prssDraw (ctx i) (bitCodec (E := E)) label 0 count) (rnd i) :=
      TreeSimCheckAllowed.simulate_inv
        (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (Sum.inr t)))
        (fun t u => allowed (.inr t) u) _
        (fun t u hu => TreeSimCheckAllowed.query_inv
          (allowed := fun t u => allowed (.inr t) u) (Sum.inr t) u hu) _ _ (each i hi)
    exact term_mask prims D cache _ (fun x u h => streams x u h) (ctx i) label 0 count (rnd i) ro
      T (by rw [self i hi]; exact held) g hg
  intro T i k hiT hkT hi hk g hg
  have ai := answer i hi T hiT g hg
  have ak := answer k hk T hkT g hg
  rw [keys T i k hiT hkT hi hk] at ai
  exact streamAnswer_unique prims D ai ak

include streams self keys in
/-- A real multiplication gadget is a PRSS draw at a common label and a peer
or collector reshare. Its products agree for honest holders at each position
that no corrupt operator fills. -/
theorem gadget_agree {α : Type} (honest : ∃ i, i ∉ D.1) (mode : ReshareMode)
    (v : C.Party → ℕ → Bit) (count label : ℕ) (st : C.Party → RunState C)
    (labels : ∀ i, (st i).label = label)
    (next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (fuel : ℕ) (state : A.State) (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality
      (fuel + mode.rounds) state (fun i =>
        oracleStep (prssDraw (ctx i) (bitCodec (E := E)) (st i).label 0 count) >>= fun o =>
          (reshareWith K (ctx i) mode o (v i) count).run (nextLabel (st i)) >>= next i)) r)
    (present : ∀ i, i ∉ D.1 → (r.2 i).isSome) :
    ∃ (state' : A.State) (z : C.Party → Shares C Bit) (history : C.Party → C.Term → List Bit),
      ZAgree K D mode count z ∧
      TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state'
        (fun i => next i (z i, ⟨history i, label + 1, (st i).tag⟩))) r := by
  obtain ⟨rnd, each, rest⟩ := phase_local D A allowed (fuel + mode.rounds) state
    (fun i => liftComp (prssDraw (ctx i) (bitCodec (E := E)) (st i).label 0 count) (LocalSpec C))
    (fun i o => (reshareWith K (ctx i) mode o (v i) count).run (nextLabel (st i)) >>= next i) r run
  have masks := draw_masks prims D cache allowed streams ctx self keys label count rnd
    (fun i hi => by simpa only [labels i] using each i hi)
  cases mode with
  | peer =>
    have form : ∀ i, (reshareWith K (ctx i) .peer (rnd i) (v i) count).run (nextLabel (st i)) >>=
        next i = exchange (reshareOut K (ctx i) bitCodec (rnd i).1 (rnd i).2 (v i) count) >>=
          fun inbox => next i (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2 (v i) count inbox,
            ⟨recordPeer K bitCodec (ctx i).self (st i).history
              (reshareZ K (ctx i) bitCodec (rnd i).1 (rnd i).2 (v i) count inbox) count,
              label + 1, (st i).tag⟩) := by
      intro i
      rw [show reshareWith K (ctx i) .peer (rnd i) (v i) count =
        reshare K (ctx i) bitCodec ((rnd i).1, (rnd i).2) (v i) count from rfl, reshare_run]
      simp only [bind_assoc, pure_bind, nextLabel, labels i]
    simp only [form, ReshareMode.rounds] at rest
    obtain ⟨state', sent, last⟩ := phase_exchange D A allowed fuel state _ _ honest r rest present
    exact ⟨state', _, _, peer_agree K D ctx self rnd v count sent masks, last⟩
  | collector =>
    have form : ∀ i, (reshareWith K (ctx i) .collector (rnd i) (v i) count).run
        (nextLabel (st i)) >>= next i =
        exchange (colOut1 K (ctx i).self (rnd i).1 (rnd i).2 (v i) count) >>= fun inbox =>
          exchange (colOut2 K (ctx i).self (rnd i).1 (rnd i).2 (v i) count inbox) >>= fun forward =>
            next i (colZ K (ctx i).self (rnd i).1 (rnd i).2 (v i) count inbox forward,
              ⟨recordMode K .collector (ctx i).self (st i).history
                (colZ K (ctx i).self (rnd i).1 (rnd i).2 (v i) count inbox forward) count,
                label + 1, (st i).tag⟩) := by
      intro i
      rw [show reshareWith K (ctx i) .collector (rnd i) (v i) count =
        reshareCollector K (ctx i) ((rnd i).1, (rnd i).2) (v i) count from rfl,
        reshareCollector_run]
      simp only [bind_assoc, pure_bind, nextLabel, labels i]
    simp only [form, ReshareMode.rounds] at rest
    obtain ⟨state₁, sent₁, mid⟩ := phase_exchange D A allowed (fuel + 1) state _ _ honest r rest
      present
    obtain ⟨state₂, sent₂, last⟩ := phase_exchange D A allowed fuel state₁ _ _ honest r mid present
    exact ⟨state₂, _, _, collector_agree K D ctx self rnd v count sent₁ sent₂ masks, last⟩

include streams self keys in
/-- One real multiplication layer keeps the agreement of the saved tuples. -/
theorem layer_agree {α : Type} (honest : ∃ i, i ∉ D.1) (mode : ReshareMode)
    (jobs : List Circuit) (l label : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (saved : SavedAgree K D (fun i => (p i).2))
    (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (next : C.Party → (MainInput C × List (Tuple C)) × RunState C → PartyM C E RealSpec α)
    (fuel : ℕ) (state : A.State) (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality
      (fuel + mode.rounds) state (fun i =>
        (layerBody K (realRunGadgets K (ctx i) mode) jobs (p i) l).run (st i) >>= next i)) r)
    (present : ∀ i, i ∉ D.1 → (r.2 i).isSome) :
    ∃ (state' : A.State) (p' : C.Party → MainInput C × List (Tuple C))
      (st' : C.Party → RunState C),
      SavedAgree K D (fun i => (p' i).2) ∧ (∀ i, (st' i).label = label + 1) ∧
      TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state'
        (fun i => next i (p' i, st' i))) r := by
  have gadgetMode : ∀ i, (realRunGadgets (G := RealSpec) K (ctx i) mode).mode = mode :=
    fun _ => rfl
  simp only [layerBody, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind,
    realMult_run, gadgetMode] at run
  have key := gadget_agree prims K D A cache allowed streams ctx self keys honest mode
    (fun i => mulRep K (ctx i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1))
    (gatesAt jobs l).length label st labels
    (fun i a => next i ((appendLayer jobs l (p i).1 a.1, (p i).2 ++
      [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1, a.1, (gatesAt jobs l).length, mode⟩]),
        a.2)) fuel state r
  obtain ⟨state', z, history, agree, last⟩ := key run present
  refine ⟨state', fun i => (appendLayer jobs l (p i).1 (z i), (p i).2 ++
      [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1, z i, (gatesAt jobs l).length, mode⟩]),
    fun i => ⟨history i, label + 1, (st i).tag⟩, ?_, fun i => rfl, last⟩
  exact savedAgree_append K D (fun i => (p i).2) saved mode (gatesAt jobs l).length
    (fun i => layerX K jobs l (p i).1) (fun i => layerY K jobs l (p i).1) z agree

include streams self keys in
/-- The ordered fold of real multiplication layers keeps the agreement of the
saved tuples. -/
theorem layers_agree {α : Type} (honest : ∃ i, i ∉ D.1) (mode : ReshareMode)
    (jobs : List Circuit) (count l label : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (saved : SavedAgree K D (fun i => (p i).2))
    (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (next : C.Party → (MainInput C × List (Tuple C)) × RunState C → PartyM C E RealSpec α)
    (fuel : ℕ) (state : A.State) (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality
      (fuel + count * mode.rounds) state (fun i =>
        ((List.range' l count).foldlM (layerBody K (realRunGadgets K (ctx i) mode) jobs)
          (p i)).run (st i) >>= next i)) r)
    (present : ∀ i, i ∉ D.1 → (r.2 i).isSome) :
    ∃ (state' : A.State) (p' : C.Party → MainInput C × List (Tuple C))
      (st' : C.Party → RunState C),
      SavedAgree K D (fun i => (p' i).2) ∧ (∀ i, (st' i).label = label + count) ∧
      TreeSimCheckAllowed allowed (executePhase worldRoles D A noFunctionality fuel state'
        (fun i => next i (p' i, st' i))) r := by
  induction count generalizing l label p st state with
  | zero =>
    refine ⟨state, p, st, saved, labels, ?_⟩
    simpa only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind,
      Nat.zero_mul, Nat.add_zero] using run
  | succ count ih =>
    simp only [List.range'_succ, List.foldlM_cons, StateT.run_bind, bind_assoc] at run
    have cost : fuel + (count + 1) * mode.rounds = (fuel + count * mode.rounds) + mode.rounds := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [cost] at run
    obtain ⟨state', p', st', saved', labels', rest⟩ := layer_agree prims K D A cache allowed
      streams ctx self keys honest mode jobs l label p saved st labels _
      (fuel + count * mode.rounds) state r run present
    obtain ⟨state'', p'', st'', saved'', labels'', last⟩ := ih (l + 1) (label + 1) p' saved'
      st' labels' state' rest
    exact ⟨state'', p'', st'', saved'',
      fun i => by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using labels'' i, last⟩

end Layers

section Boundary

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) {A : Adversary C E (Keys C) PEmpty PEmpty}

theorem executePhase_congr {α : Type} (fuel : ℕ) (state : A.State)
    (p q : C.Party → PartyM C E RealSpec α) (h : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D A noFunctionality fuel state p =
      executePhase worldRoles D A noFunctionality fuel state q := by
  have steps : (fun i => if i ∈ D.1 then pure (Step.done none) else
      worldRoles.honest (advance (p i).run) : C.Party → OracleComp (WorldSpec C) _) =
      fun i => if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (q i).run) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi, h i hi]
  unfold executePhase startSteps
  rw [steps]

/-- Honest holders of a term with checkpoint rows have equal term inputs. The
input shares are PRF values of the term seed, read from the final hash cache. -/
theorem boundary_inputs (b : TreeCheckTailBoundary A) (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings D))
    (self : ∀ i, i ∉ D.1 → (b.batch.ctx i).self = i)
    (seeds : ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
      (b.batch.ctx i).keys.seed T = (b.batch.ctx k).keys.seed T)
    (T : C.Term) (i k : C.Party) di dk (hiT : i ∈ C.holders T) (hkT : k ∈ C.holders T)
    (hi : i ∉ D.1) (hk : k ∉ D.1) (hdi : o.1.2 i = some di) (hdk : o.1.2 k = some dk) :
    TreeCheckWalkConsistent.wiresAt T di.1 = TreeCheckWalkConsistent.wiresAt T dk.1 := by
  unfold TreeCheckTailBoundary.pre at run
  have allowed := TreeCheckMaskExtraction.logged_hash_replay prims D _ _ o run
  have data : ∀ j, j ∉ D.1 → ∀ d, o.1.2 j = some d → d.1 = b.batch.jobs.map (fun job T =>
      if j ∈ C.holders T then inputBits (hashOf prims o.2.1.1) (b.batch.ctx j).keys.seed job T
      else []) := by
    intro j hj d hd
    have localRun := treeSimCheck_phase_replay D A noFunctionality _ _ b.batch.state _ o.1
      allowed j hj d hd
    obtain ⟨_, _, localRun⟩ := localRun.option_bind_inv _ _ _
    unfold treeSimCheckBatchPrefix at localRun
    obtain ⟨inputs, hp, ht⟩ := localRun.option_bind_inv _ _ _
    obtain ⟨rest, _, he⟩ := ht.option_bind_inv _ _ _
    have he : d = (inputs, rest) := Option.some.inj he.pure_inv
    subst d
    rw [treeCheck_inputShares_replay prims _ _ (fun q u h => h) _ _ inputs hp, self j hj]
  rw [data i hi di hdi, data k hk dk hdk]
  unfold TreeCheckWalkConsistent.wiresAt
  simp only [List.map_map]
  apply List.map_congr_left
  intro job _
  simp only [Function.comp_apply, if_pos hiT, if_pos hkT, inputBits,
    seeds T i k hiT hkT hi hk]

/-- Honest holders of a term with checkpoint rows have equal products in each
saved tuple at each position that no corrupt operator fills. -/
theorem boundary_products (b : TreeCheckTailBoundary A) (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings D))
    (self : ∀ i, i ∉ D.1 → (b.batch.ctx i).self = i)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (keys : ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
      (b.batch.ctx i).prss.term T = (b.batch.ctx k).prss.term T)
    (present : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (T : C.Term) (i k : C.Party) di dk (hiT : i ∈ C.holders T) (hkT : k ∈ C.holders T)
    (hi : i ∉ D.1) (hk : k ∉ D.1) (hdi : o.1.2 i = some di) (hdk : o.1.2 k = some dk) :
    di.2.1.2.map (TreeCheckWalkConsistent.unfilledView K D T) =
      dk.2.1.2.map (TreeCheckWalkConsistent.unfilledView K D T) := by
  unfold TreeCheckTailBoundary.pre at run
  have replay := treeLockstep_logged_run_allowed prims D _ b.batch.world o run
  have streams : ∀ x u, TreeLockstepWorldStreams prims D o.2.1 (.inr (.inr (.inr x))) u →
      TreeLockstepStreamAnswer prims D o.2.1 x u := fun _ _ h => h
  have honest : ∃ j, j ∉ D.1 := ⟨i, hi⟩
  unfold treeLockstepLocalPrelude at replay
  simp only [bind_assoc] at replay
  obtain ⟨outs, -, replay⟩ := phase_local D A _ _ _ _ _ _ replay
  have accepted : ∀ j, j ∉ D.1 → ∃ u, outs j = some u := by
    intro j hj
    cases hout : outs j with
    | some u => exact ⟨u, rfl⟩
    | none =>
      have stopped := phase_stop D A _ _ _ _ _ replay j (by
        simp only [hout, failure_bind]
        exact advance_run_failure)
      simpa [stopped] using present j hj
  rw [executePhase_congr D _ _ _ (fun j => treeSimCheckBatchPrefix K circuits settings
    (b.batch.ctx j) b.batch.jobs b.batch.initial) (fun j hj => by
      obtain ⟨u, hu⟩ := accepted j hj
      simp only [hu, pure_bind])] at replay
  unfold treeSimCheckBatchPrefix at replay
  simp only [inputShares_fun, mapM_oracleStep, parameter] at replay
  obtain ⟨inputs, -, replay⟩ := phase_local D A _ _ _ _ _ _ replay
  unfold treeSimCheckBeforeVerify at replay
  simp only [StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, List.range_eq_range'] at replay
  rw [TreeCheckBatchBoundary.rounds, Nat.add_comm] at replay
  have layers := layers_agree prims K D A o.2.1 _ streams b.batch.ctx self keys honest settings.mode
    (b.batch.jobs.map (circuits b.batch.parameter ·.kind))
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind))) 0 b.batch.initial.1
    (fun j => (inputs j, [])) (savedAgree_nil K D)
    (fun _ => ⟨fun _ => [], b.batch.initial.1, b.batch.initial.2⟩) (fun _ => rfl)
    (fun j x => ((realRunGadgets K (b.batch.ctx j) settings.mode).rerand
      (outputShares K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) x.1.1)
      (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length).run x.2 >>=
        fun y => pure (inputs j, (y.1, x.1.2 ++
          [⟨outputShares K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) x.1.1, one K, y.1,
            (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length, .peer⟩]),
          y.2)) 1 b.batch.state o.1
  obtain ⟨state', p', st', saved', labels', rest⟩ := layers replay present
  simp only [realRerand_run] at rest
  have rerand := gadget_agree prims K D A o.2.1 _ streams b.batch.ctx self keys honest .peer
    (fun j => ownerSum K (b.batch.ctx j)
      (outputShares K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) (p' j).1))
    (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length
    (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind))) st' labels'
    (fun j y => pure (inputs j, (y.1, (p' j).2 ++
      [⟨outputShares K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) (p' j).1, one K, y.1,
        (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length, .peer⟩]),
      y.2)) 0 state' o.1
  obtain ⟨state'', z, history, agree, last⟩ := rerand rest present
  have row := fun j hj => phase_pure D A _ 0 state'' _ o.1 last j hj
  rw [row i hi, Option.some.injEq] at hdi
  rw [row k hk, Option.some.injEq] at hdk
  subst di dk
  exact savedAgree_append K D (fun j => (p' j).2) saved' .peer _
    (fun j => outputShares K (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) (p' j).1)
    (fun _ => one K) z agree T i k hiT hkT hi hk

end Boundary

section Walk

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}

/-- `Transcript` of a walk follows from common term seeds and from common term
keys at its supported live checkpoints. -/
theorem transcript_of_keys {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    (self : ∀ c i, ((W.boundary c).batch.ctx i).self = i)
    (parameter : ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter)
    (seeds : ∀ c T l m, l ∈ C.holders T → m ∈ C.holders T → l ∉ D.1 → m ∉ D.1 →
      ((W.boundary c).batch.ctx l).keys.seed T = ((W.boundary c).batch.ctx m).keys.seed T)
    (keys : ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
        (.inl (c, o)) →
      ∀ T l m, l ∈ C.holders T → m ∈ C.holders T → l ∉ D.1 → m ∉ D.1 →
        ((W.boundary c).batch.ctx l).prss.term T = ((W.boundary c).batch.ctx m).prss.term T) :
    TreeCheckWalkConsistent.Transcript prims K circuits settings D top tree x z Z j W := by
  intro c o hs live T i k di dk hiT hkT hi hk hdi hdk
  have pre := TreeCheckTailWalk.mem_support_cut_pre hs
  obtain ⟨r, hr, hbad, _⟩ := id live
  obtain ⟨_, _, _, _, i₀, value, records, _, _, _, _, _, _, hout, _⟩ := hbad.2
  have counted := (W.boundary c).counts prims K circuits settings D Z (self c) (parameter c)
    o pre r hr ⟨i₀, (value, records), hout⟩
  have present : ∀ l, l ∉ D.1 → (o.1.2 l).isSome := fun l hl => by
    obtain ⟨d, hd, -⟩ := counted l hl
    simp [hd]
  exact ⟨boundary_inputs prims K circuits settings D _ o pre (fun l _ => self c l) (seeds c)
    T i k di dk hiT hkT hi hk hdi hdk,
    boundary_products prims K circuits settings D _ o pre (fun l _ => self c l) (parameter c)
    (keys c o hs live) present T i k di dk hiT hkT hi hk hdi hdk⟩

open TreeCheckWalkRecipe

set_option maxRecDepth 2000 in
set_option linter.constructorNameAsVariable false in
/-- `WalkTranscript` holds for the fixed family. -/
theorem walkTranscript : TreeCheckWalkConsistent.WalkTranscript prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨⟨-, parameter⟩, -, self⟩ :=
    walkSplit prims K circuits settings hb top tree D A x z Z q dealt bounded small j p hp
  have checkpoint := TreeCheckWalkCoupling.checkpointFacts prims K circuits settings hb top tree D A
    x z Z q dealt bounded small j p hp
  obtain ⟨parameter', seeds, pairKeys, hx⟩ := id dealt
  refine transcript_of_keys prims K circuits settings self parameter ?_ ?_
  · intro c T l m hl hm _ _
    change (x l).seed T = (x m).seed T
    rw [hx l, hx m]
    simp [dealtKeys, hl, hm]
  · intro c o hs live T l m hl hm hlD hmD
    have facts : TreeCheckWalkCoupling.CheckpointFacts D p.1.2 o.2.1.1 := by
      with_reducible exact (checkpoint c o hs live)
    exact facts.agree l m hlD hmD T hl hm

/-- `WalkConsistent` holds for the fixed family. -/
theorem walkConsistent : TreeCheckWalkCoverage.WalkConsistent prims K circuits settings :=
  TreeCheckWalkConsistent.walkConsistent_of_transcript prims K circuits settings
    (walkTranscript prims K circuits settings)

end Walk

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.phase_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_exchange

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.gadget_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gadget_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.layers_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms layers_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.boundary_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_inputs

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.boundary_products' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_products

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.walkTranscript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkTranscript

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkTranscript.walkConsistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkConsistent

end TreeCheckWalkTranscript
end ThresholdLeanXmssSecurity
