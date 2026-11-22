import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.PhaseAbort

/-!
# The lemma of one ceremony from its parts

`ceremonyBad_of_parts` proves `CeremonyBad` from its thirteen parts, `ceremonySupport_of_parts` proves
`CeremonySupport` from its seven parts, and `provenanceTreeRun_of_parts` proves `ProvenanceTreeRun`
from its two parts. `cutDead` proves `CutDead`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The ghost run with its records dropped -/

/-- With its record dropped, `recCeremony` is `ceremonyProgram`. -/
theorem dropRec_recCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    dropRec (recCeremony K circuits settings i c) = ceremonyProgram K circuits settings i c := by
  have hfail : ∀ {α : Type}, dropRec (failure : RecM C E α) = failure := fun {α} =>
    OptionT.ext (by
      change dropLog.toFun _ (pure none) = pure none
      exact dropLog.toFun_pure' _)
  unfold recCeremony ceremonyProgram
  rcases c.keys i with _ | keys
  · exact hfail
  · rw [MonadHom.mmap_bind]
    have hrun : dropRec ((recRun K circuits settings i keys c.jobs).run c.counters) =
        (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys
          c.jobs).run c.counters := by
      rw [← dropRecS_recRun]
      rfl
    rw [hrun]
    refine bind_congr fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · exact hfail
    · exact MonadHom.mmap_pure _ _

/-- The ghost run of one ceremony with the records dropped is `ceremonyPhase`. -/
theorem ghostCeremony_erase (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) :
    (ceremonyPhase prims K circuits settings D net rounds c).run world =
      (fun w => ((w.1.1, ceremonyOutputs w.1.2), w.2)) <$>
        (ghostCeremony prims K circuits settings D net rounds c).run world := by
  have hprog : (fun i => ceremonyProgram K circuits settings i c) =
      fun i => dropRecord (recCeremony K circuits settings i c).run.run := by
    funext i
    rw [← dropRec_recCeremony]
    rfl
  unfold ceremonyPhase ghostCeremony
  rw [hprog, executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
    ([] : Record C E), simulateQ_map, StateT.run_map]
  rfl

/-! ## The bound of one check -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem jointStop_eq {α : Type} {D : C.Coalition} {σ : Type} {r : σ × (C.Party → Option (CutOf C E α))}
    {world : StreamState C} {start : CheckStart C σ} (h : jointStop D r world = some start) :
    start.world = world ∧ start.st = r.1 := by
  unfold jointStop at h
  split_ifs at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

omit [DecidableEq E] in
/-- A bad check of batch `k` of one ceremony has probability at most `checkErrorMax`. A bad check with
agreeing copies is a sound case of the pilot (`checkHop_of_pilot`). A bad check with split copies
leaves a collision of two history and digest cells (`splitAcceptCollides_of_evidence`), which the
event excludes. Disagreeing PRSS keys leave an echo collision, which the event excludes too. -/
theorem ceremonyCheckBad_le (budget : CeremonyBudget prims K circuits settings runLimit)
    (zero : ZeroCheck (C := C) (E := E)) (agree : CeremonyKeysAgree prims K circuits settings)
    (inputs : CeremonyTupleInputs prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step rounds : ℕ)
    (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step)
    (ℓ : StartBudget) (c : CeremonyStart C net.State) (world : StreamState C)
    (hjobs : AdmissibleJobs circuits settings c.jobs) (hready : CeremonyReady D ℓ c world)
    (hroom : LedgerRoom circuits settings runLimit C q step
      (ledgerStep circuits settings C step rounds (chunks settings.batchSize c.jobs).length ℓ))
    (hpad : (rounds + 2) * step ≤ q)
    (hfuel : CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds)
    (k : ℕ) (hk : k < (chunks settings.batchSize c.jobs).length) :
    (Pr{let r ← ceremonyCheckAt prims K circuits settings D net rounds k c world}[CheckBad D r]).toReal ≤
      checkErrorMax (E := E) circuits settings runLimit C q := by
  let : SampleableType E := SampleableType.ofFintype E
  have split := splitAcceptCollides_of_evidence prims K (splitAcceptEvidence prims K)
  have checkHop := checkHop_of_pilot prims K circuits settings runLimit D net q step hstep
  have hsound : ∀ r ∈ support (ceremonyCheckAt prims K circuits settings D net rounds k c world), CheckBad D r →
      SoundAt K circuits settings runLimit D q step r := by
    intro r hr ⟨start, out, hrc, hacc, hcase, hfresh, hglobal, hsplit⟩
    unfold ceremonyCheckAt at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨z, hz, hr⟩ := hr
    cases hj : jointStop D z.1 z.2 with
    | none =>
      rw [hj] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      rw [hr] at hrc
      cases hrc
    | some start' =>
      rw [hj] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨out', hout', rfl⟩ := hr
      simp only [Prod.mk.injEq, Option.some.injEq] at hrc
      obtain ⟨rfl, rfl⟩ := hrc
      obtain ⟨hworld, -⟩ := jointStop_eq hj
      have hglobal' : ¬ GlobalEvent z.2 := hworld ▸ hglobal
      have hpositive : start'.counts.sum ≠ 0 := fun hzero => by
        obtain ⟨hright, hsame⟩ := zero D z.1 z.2 start' hj hzero
        rcases hcase with hwrong | hsplit'
        · exact hright hwrong
        · exact hsplit' hsame
      have hbudget := budget D net q step rounds hstep ℓ c world hjobs hready hroom hpad hfuel k hk z hz start' hj
        hglobal' hpositive
      have hagree : PrssKeysAgree D start'.prss :=
        (agree D net rounds c world k hk z hz start' hj).resolve_right fun h => hglobal' (Or.inl h)
      have htuple := inputs D net rounds ℓ c world hready k hk z hz start' hj hglobal' hagree
      by_cases hmv : MultVerifyAgree D (honestTuples D start'.x)
      · rcases hcase with hwrong | hsplit'
        · exact ⟨start', out', rfl, hacc, htuple, hwrong, hmv, hagree, hfresh, hbudget⟩
        · exact absurd hmv hsplit'
      · obtain ⟨seen, expansionKeys, salts, splitCells, hcache, -⟩ := hbudget
        exact absurd (split D net step hstep start'.keys start'.prss start'.counts start'.x start'.L start'.tg
          start'.st start'.world.1 start'.world.2 seen expansionKeys salts splitCells htuple hmv hagree hfresh hcache
          out' hout' hacc) hsplit
  refine (prReal_mono _ _ _ hsound).trans ?_
  have hmax := checkErrorMax_nonneg (E := E) circuits settings runLimit (C := C) q
  refine (ENNReal.toReal_le_of_le_ofReal hmax ?_)
  unfold ceremonyCheckAt
  refine prEvent_bind_le_of_forall_le _ _ _ fun z => ?_
  cases hj : jointStop D z.1 z.2 with
  | none =>
    dsimp only
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_]
    · exact bot_le
    · rintro ⟨start, out, hrc, -⟩
      simp only [support_pure, Set.mem_singleton_iff] at hr
      rw [hr] at hrc
      cases hrc
  | some start =>
    dsimp only
    rw [prEvent_map]
    by_cases hcase : SoundCase K circuits settings runLimit D q step start
    · have hmem : start.counts.sum ∈ batchCounts circuits settings := by
        obtain ⟨-, -, -, -, -, _, _, _, _, -, -, -, -, -, hmem⟩ := hcase
        exact hmem
      refine le_trans (prEvent_mono_of_support _ _ (fun out => ∃ i, i ∉ D.1 ∧ out.1.2 i = some ()) ?_) ?_
      · rintro out - ⟨start', out', hrc, hacc, -⟩
        simp only [Prod.mk.injEq, Option.some.injEq] at hrc
        obtain ⟨-, rfl⟩ := hrc
        exact hacc
      · exact (ENNReal.le_ofReal_iff_toReal_le (prEvent_ne_top _) hmax).2
          ((checkHop start hcase).trans (batchCheckError_le_max circuits settings runLimit hmem))
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun out _ => ?_]
      · exact bot_le
      · rintro ⟨start', out', hrc, -, hs⟩
        simp only [Prod.mk.injEq, Option.some.injEq] at hrc
        obtain ⟨rfl, -⟩ := hrc
        exact hcase hs

/-! ## The fresh part, the union over the old keys -/

omit [Fintype E] [DecidableEq E] in
/-- A reused key in one ceremony with no global event has probability at most
`prssKeyCount C * ℓ.hiddenKeys / 2^256`. The old keys under the hidden names with a stream cell at the
start are a finite set `S` of at most `prssKeyCount C * ℓ.hiddenKeys` pairs, by `HiddenNames` and
`HiddenKeyBound`. Each pair of `S` has a derive cell at the start by `HiddenProvenance`, so `FreshOne`
bounds its event by `2^-256`. A reused key is the event of one pair of `S`, so the bound is the sum
over `S`. -/
theorem reusedKey_le (names : HiddenNames C) (fresh : FreshOne prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C) (hready : CeremonyReady D ℓ c world) :
    (Pr{let ω ← (ghostCeremony prims K circuits settings D net rounds c).run world}[
        ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2]).toReal ≤ ceremonyFresh C ℓ.hiddenKeys := by
  obtain ⟨hidden, hcard, hmem⟩ := names D
  have hbound : HiddenKeyBound world.2 ℓ.hiddenKeys := hready.2.1.2.2.2
  have hprov : HiddenProvenance D world := hready.2.2
  choose keysOf hkeysCard hkeysMem using hbound
  let S : Finset (KeyName C × HashOutput) :=
    (hidden.biUnion fun name => (keysOf name).image fun key => (name, key)).filter fun p =>
      Hidden D p.1 ∧ ∃ ρ idx position, world.2 ((p.1, p.2), ρ, idx, position) ≠ none
  have hS : S.card ≤ prssKeyCount C * ℓ.hiddenKeys := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ ℓ.hiddenKeys fun name _ =>
      Finset.card_image_le.trans (hkeysCard name)).trans ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hcard
  have hone : ∀ p ∈ S, Pr{let ω ← (ghostCeremony prims K circuits settings D net rounds c).run world}[
      UsesKey D p.1 p.2 ω.1.2 ∧ ¬ GlobalEvent ω.2] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    intro p hp
    obtain ⟨-, hhidden, ρ, idx, position, hcell⟩ := Finset.mem_filter.1 hp
    exact fresh D net rounds c world p.1 p.2 hhidden (hprov p.1 p.2 ρ idx position hhidden hcell)
  have hunion := prEvent_exists_finset_le_card_mul S
    ((ghostCeremony prims K circuits settings D net rounds c).run world)
    (fun p ω => UsesKey D p.1 p.2 ω.1.2 ∧ ¬ GlobalEvent ω.2) hone
  have hcover : Pr{let ω ← (ghostCeremony prims K circuits settings D net rounds c).run world}[
      ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2] ≤
      Pr{let ω ← (ghostCeremony prims K circuits settings D net rounds c).run world}[
        ∃ p ∈ S, UsesKey D p.1 p.2 ω.1.2 ∧ ¬ GlobalEvent ω.2] := by
    refine prEvent_mono_of_support _ _ _ ?_
    rintro ω - ⟨⟨name, key, hhidden, huses, ρ, idx, position, hcell⟩, hglobal⟩
    refine ⟨(name, key), Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨name, hmem name hhidden,
      Finset.mem_image.2 ⟨key, hkeysMem name key ρ idx position hcell, rfl⟩⟩, hhidden, ρ, idx, position, hcell⟩,
      huses, hglobal⟩
  have htop : (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.2 (by positivity))
  have hreal := ENNReal.toReal_mono htop (hcover.trans hunion)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at hreal
  refine hreal.trans ?_
  unfold ceremonyFresh
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)

/-! ## `CeremonyBad` -/

omit [DecidableEq E] in
/-- `CeremonyBad` from its sub-statements. Wrong opened outputs with no
global event give a wrong batch `k` (`CeremonyMonitor`), which has a bad check `k` in the records
(`CeremonyBatch`, with `CeremonyAbort` for the case of an operator that did not start it). The event
is then a reused key or, for some batch `k`, a bad check `k` with no reused key. The first has the
bound of `reusedKey_le`. The second is at most a bad check of the cut (`CeremonyCoupling`), which has
the bound of `ceremonyCheckBad_le`. The sum over the batches is the union bound. -/
theorem ceremonyBad_of_parts (monitor : CeremonyMonitor prims K circuits settings)
    (batch : CeremonyBatch prims K circuits settings) (abort : CeremonyAbort prims K circuits settings)
    (fresh : FreshOne prims K circuits settings) (names : HiddenNames C)
    (sync : CeremonySync prims K circuits settings) (interval : CeremonyInterval prims K circuits settings)
    (coupling : CeremonyCoupling prims K circuits settings)
    (agree : CeremonyKeysAgree prims K circuits settings)
    (budget : CeremonyBudget prims K circuits settings runLimit) (zero : ZeroCheck (C := C) (E := E))
    (short : ShortFuel prims K circuits settings)
    (inputs : CeremonyTupleInputs prims K circuits settings) :
    CeremonyBad prims K circuits settings runLimit := by
  intro hsize D net q step rounds hstep ℓ c world hjobs hready hroom hpad
  by_cases hfuel : CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds
  swap
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun r hr h => by
      obtain ⟨⟨i, hi, o, ho, -⟩, -⟩ := h
      rw [short D net rounds ℓ c world hready (not_le.1 hfuel) r hr i hi] at ho
      exact absurd ho (by simp)]
    rw [ENNReal.toReal_zero]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (checkErrorMax_nonneg circuits settings runLimit q))
      (by positivity)
  rw [ghostCeremony_erase, prEvent_map]
  obtain ⟨mx, hmx⟩ : ∃ mx, (ghostCeremony prims K circuits settings D net rounds c).run world = mx := ⟨_, rfl⟩
  have hcover := prReal_mono mx
    (fun ω => (WrongCeremony prims circuits D c ∘ fun w => ((w.1.1, ceremonyOutputs w.1.2), w.2)) ω ∧
      ¬ GlobalEvent ((fun w : (net.State × CeremonySteps C E) × StreamState C =>
        ((w.1.1, ceremonyOutputs w.1.2), w.2)) ω).2)
    (fun ω => (ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2) ∨
      ∃ k ∈ Finset.range (chunks settings.batchSize c.jobs).length, BadCheckAt K D k ω.1.2 ∧
        ¬ ReusedKey D world.2 ω.1.2 ∧ HonestOutput D (ceremonyOutputs ω.1.2) ∧ ¬ GlobalEvent ω.2) (by
    rintro ω hω ⟨hwrong, hglobal⟩
    rw [← hmx] at hω
    obtain ⟨k, hk, hwb⟩ := monitor hsize D net rounds ℓ c world hready ω hω hwrong hglobal
    obtain ⟨i, hi, hout, -⟩ := id hwb
    have hhonest : HonestOutput D (ceremonyOutputs ω.1.2) := ⟨i, hi, hout⟩
    rcases batch D net rounds ℓ c world hready ω hω hglobal k hk hwb with hbad | hmissing
    · by_cases hreused : ReusedKey D world.2 ω.1.2
      · exact Or.inl ⟨hreused, hglobal⟩
      · exact Or.inr ⟨k, Finset.mem_range.2 hk, hbad, hreused, hhonest, hglobal⟩
    · have hnone := abort D net rounds ℓ c world hready ω hω hglobal k hk hmissing i hi
      rw [hnone] at hout
      exact absurd hout (by simp))
  have hunion := prReal_or_le mx (fun ω => ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2)
    (fun ω => ∃ k ∈ Finset.range (chunks settings.batchSize c.jobs).length, BadCheckAt K D k ω.1.2 ∧
      ¬ ReusedKey D world.2 ω.1.2 ∧ HonestOutput D (ceremonyOutputs ω.1.2) ∧ ¬ GlobalEvent ω.2)
  have hsum := prReal_exists_finset_le mx (Finset.range (chunks settings.batchSize c.jobs).length) fun k ω =>
    BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧ HonestOutput D (ceremonyOutputs ω.1.2) ∧
      ¬ GlobalEvent ω.2
  have hcheck : ∑ k ∈ Finset.range (chunks settings.batchSize c.jobs).length,
      (Pr{let ω ← mx}[BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧
        HonestOutput D (ceremonyOutputs ω.1.2) ∧ ¬ GlobalEvent ω.2]).toReal ≤
      ∑ _k ∈ Finset.range (chunks settings.batchSize c.jobs).length,
        checkErrorMax (E := E) circuits settings runLimit C q :=
    Finset.sum_le_sum fun k hk => by
      rw [← hmx]
      exact (coupling sync interval D net rounds ℓ c world hready hfuel k (Finset.mem_range.1 hk)).trans
        (ceremonyCheckBad_le prims K circuits settings runLimit budget zero agree inputs D net q step rounds hstep
          ℓ c world hjobs hready hroom hpad hfuel k (Finset.mem_range.1 hk))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hcheck
  have hfresh := reusedKey_le prims K circuits settings names fresh D net rounds ℓ c world hready
  rw [hmx] at hfresh
  unfold ceremonyFresh at hfresh
  rw [hmx]
  exact hcover.trans (hunion.trans (by linarith))

/-! ## `CeremonySupport` -/

omit [Fintype E] [DecidableEq E] in
/-- The program of one ceremony starts with a round, the first exchange of its PRSS setup, or it
aborts at once. -/
theorem startsWithRound_ceremonyProgram (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    StartsWithRound (ceremonyProgram K circuits settings i c) := by
  cases hk : c.keys i with
  | none =>
    simp only [ceremonyProgram, hk]
    exact startsWithRound_failure
  | some keys =>
    simp only [ceremonyProgram, hk]
    rw [CheckTiming.ceremonyRun_run_keys]
    exact startsWithRound_bind _ _ (startsWithRound_bind _ _ (startsWithRound_prssSetup i))

omit [Fintype E] [DecidableEq E] in
/-- The clause on an operator that is not alive at the start of one ceremony, with a proof. Each
living operator meets its abort frame in the first exchange of the PRSS setup. -/
theorem ceremonyDead (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (r : (net.State × (C.Party → Option CeremonyResult)) × StreamState C)
    (hr : r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world))
    (hdead : ∃ i, i ∉ D.1 ∧ c.keys i = none) : ∀ i, i ∉ D.1 → r.1.2 i = none := by
  obtain ⟨i₀, hi₀, hnone⟩ := hdead
  refine phase_dead_noOutput prims D net rounds c.adversary _ i₀ hi₀ ?_
    (fun i _ => startsWithRound_ceremonyProgram K circuits settings i c) world r hr
  simp only [ceremonyProgram, hnone]

omit [Fintype E] [DecidableEq E] in
/-- `CeremonySupport` from its sub-statements. The ledger clause is the
ledger of each class. The agreement of the results is the agreement of the opened outputs and the
end counters, which are one function of the job list. The clause on an operator that is not alive at
the start is `ceremonyDead`. -/
theorem ceremonySupport_of_parts (counters : CeremonyCounters prims K circuits settings)
    (outputs : CeremonyOutputsAgree prims K circuits settings)
    (split : LedgerSplit prims K circuits settings) (sound : LedgerSound prims K circuits settings)
    (salts : LedgerSalts prims K circuits settings) (hidden : LedgerHidden prims K circuits settings)
    (provenance : CeremonyProvenance prims K circuits settings) :
    CeremonySupport prims K circuits settings := by
  intro D net step rounds hstep ℓ c world hjobs hready r hr
  obtain ⟨-, ⟨hsplit, hsound, hsalts, hhidden⟩, hprov⟩ := id hready
  refine ⟨counters D net rounds ℓ c world hready r hr,
    ceremonyDead prims K circuits settings D net rounds c world r hr,
    ⟨⟨split D net step rounds hstep _ c world hsplit r hr,
      sound D net step rounds hstep _ _ c world hjobs hsound r hr,
      salts D net step rounds hstep _ c world hsalts r hr,
      hidden D net rounds _ c world hhidden r hr⟩,
      provenance D net rounds c world hprov r hr⟩, fun hglobal i j oi oj hi hj hoi hoj => ?_⟩
  exact Prod.ext (outputs D net rounds ℓ c world hready r hr hglobal i j oi oj hi hj hoi hoj)
    ((counters D net rounds ℓ c world hready r hr i oi hi hoi).trans
      (counters D net rounds ℓ c world hready r hr j oj hj hoj).symm)

/-! ## `ProvenanceTreeRun` -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The outcomes of a computation and then a test of its result. -/
theorem support_then_test {α β : Type} (D : C.Coalition) (X : OracleComp (WorldSpec C) α)
    (W : α → OracleComp (WorldSpec C) β) (w : StreamState C) (y : (α × β) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (do
      let r ← X
      let bad ← W r
      pure (r, bad))).run w)) :
    ∃ r ∈ support ((simulateQ (streamWorld prims D) X).run w),
      ∃ v ∈ support ((simulateQ (streamWorld prims D) (W r.1)).run r.2), y.2 = v.2 := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨r, hr, v, hv, rfl⟩ := hy
  exact ⟨r, hr, v, hv, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- `ProvenanceTreeRun` from the phase of a run of a tree and its monitor. -/
theorem provenanceTreeRun_of_parts (phase : TreePhaseProvenance prims K circuits settings)
    (monitor : MonitorProvenance prims (C := C)) : ProvenanceTreeRun prims K circuits settings := by
  intro D net tree s world hprov r hr
  obtain ⟨W, hW⟩ : ∃ W : (C.Party → Option TreeOutput) → OracleComp (WorldSpec C) Bool,
      ∀ outputs, wrongOutput D (fun i => (s.operators i).keys) tree outputs = W outputs := ⟨_, fun _ => rfl⟩
  have hmonitor : ∀ outputs, KeepsProvenance prims D (W outputs) := fun outputs => by
    rw [← hW]
    exact monitor D _ tree outputs
  unfold streamTreeRun at hr
  simp only [hW] at hr
  obtain ⟨a, ha, v, hv, hrv⟩ := support_then_test prims D
    (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary fun i =>
      treeProgram K circuits settings i (s.operators i) tree)
    (fun a => W a.2) world r hr
  rw [hrv]
  exact hmonitor a.1.2 a.2 (phase D net tree s world hprov a ha) v hv

/-! ## The cut of the program of one ceremony -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The comparison of the monitor is `false` when no honest operator has an output. -/
theorem compare_noOutput (D : C.Coalition) (outputs : C.Party → Option TreeOutput)
    (hno : ∀ i, i ∉ D.1 → outputs i = none) (reference : Option TreeOutput) :
    decide (∃ i, i ∉ D.1 ∧ (outputs i).isSome ∧ outputs i ≠ reference) = false := by
  refine decide_eq_false fun h => ?_
  obtain ⟨i, hi, hsome, -⟩ := h
  rw [hno i hi] at hsome
  exact absurd hsome (by simp)

omit [Fintype E] [DecidableEq E] in
/-- `CutDead`, with a proof. An honest operator with no head result sends
abort frames from the first round of the rest, each living operator starts the rest with the first
exchange of the second PRSS setup, so no honest operator has an output, and the monitor gives
`false`. -/
theorem cutDead : CutDead prims K circuits settings := by
  intro D net b s st heads m w hdead y hy
  obtain ⟨reference, href⟩ : ∃ reference : OracleComp (WorldSpec C) (Option TreeOutput),
      ∀ outputs : C.Party → Option TreeOutput,
        wrongOutput D (fun i => (s.operators i).keys) (.bottom b) outputs = reference >>= fun reference =>
          pure (decide (∃ i, i ∉ D.1 ∧ (outputs i).isSome ∧ outputs i ≠ reference)) := ⟨_, fun _ => rfl⟩
  unfold bottomRest at hy
  simp only [href, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨r, hr, v, hv, hy⟩ := hy
  obtain ⟨ref, -, hv⟩ := hv
  rw [hy, hv]
  refine compare_noOutput D _ (phase_dead_noOutput prims D net m st _ hdead.choose hdead.choose_spec.1
    (by simp [hdead.choose_spec.2]) (fun i _ => ?_) w r hr) ref.1
  cases heads i with
  | none => exact startsWithRound_failure
  | some x => exact startsWithRound_bottomTail K circuits settings i (s.operators i) b x

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyBad_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyBad_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonySupport_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonySupport_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.provenanceTreeRun_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.provenanceTreeRun_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutDead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutDead
