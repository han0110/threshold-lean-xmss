import ThresholdLeanXmssSecurity.Proof.SigningOwnLedger
import ThresholdLeanXmssSecurity.Proof.SigningCompilerPotential

/-!
# The own potential of the compiler run with the ledger

`ownPotential` is the compensated lane 2 sum of leanVM on the view of the backend, with the ledger
of `SigningOwnLedger` as the count. `OwnInv` is the count invariant of leanVM with the ledger.

* `viewSum_closed` states that a fresh input that the lane 2 key does not decode keeps the sum.
* `ownInv_step` and `ownPotential_step` state that each backend call keeps the invariant, and that
  the potential rises by at most `2^-128` at a charged call only.
* `ownPotential_event` states that the lane 2 event gives a potential of at least one.
* `ownRun_cap` bounds the cap flag or the lane 2 event of `ownRun` by `B / 2^128`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

namespace SigningOwnCapPotential

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerO1Coupling
open SigningCompilerCouplingProof SigningCompilerO1Release
open SigningLedgerExpect SigningCompilerO1Clean SigningOwnLedger

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The own potential. It is the compensated lane 2 sum of leanVM on the view of the backend, with
the ledger as the count and `B` as the budget. It is zero on a stale or dirty state and above the
budget. -/
def ownPotential (P : PublicParameter) (B : ℕ) (st : (CompilerBackend C × ℕ) × OwnGhost) : ℝ≥0∞ :=
  if st.1.1.trace.2 = true ∨ st.2.dirty = true ∨ B < st.2.ledger then 0 else
    SigningCompilerPotential.viewSum P B (compilerView st.1.1, st.2.ledger) *
      ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹

/-- The invariant of the potential step. The backend is reachable. On a state that is not stale
and not dirty, the count invariant of leanVM holds with the ledger. -/
def OwnInv (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : (CompilerBackend C × ℕ) × OwnGhost) : Prop :=
  CompilerReachable P seeds st.1 ∧
    (st.1.1.trace.2 = true ∨ st.2.dirty = true ∨
      XmssSecurity.Ghost.Inv (SigningLane2FlatProof.laneKey P) (compilerView st.1.1, st.2.ledger))

set_option linter.unusedVariables false in
/-- A fresh hash input that the lane 2 key does not decode keeps the four terms of the
compensated sum, at each count. It covers each top digest input. -/
theorem viewSum_closed (P : PublicParameter) (B : ℕ) (cache : XmssSecurity.HashSpec.QueryCache)
    (trace : XmssSecurity.SigningCacheTrace) (k : ℕ) (input : HashInput) (u : HashOutput)
    (hfresh : cache input = none)
    (hdec : XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey P).parameter input = none) :
    SigningCompilerPotential.viewSum P B ((cache.cacheQuery input u, trace), k) =
      SigningCompilerPotential.viewSum P B ((cache, trace), k) := by
  have hne := XmssSecurity.Ghost.dec_eq_none _ hdec
  have hq : ∀ e y, (cache.cacheQuery input u)
      (XmssSecurity.Partner.input (SigningLane2FlatProof.laneKey P).parameter e y) =
        cache (XmssSecurity.Partner.input (SigningLane2FlatProof.laneKey P).parameter e y) :=
    fun e y => QueryCache.cacheQuery_of_ne _ _ (hne e y).symm
  have hΦ : XmssSecurity.Ghost.openΦ (SigningLane2FlatProof.laneKey P).parameter
      (cache.cacheQuery input u) trace =
        XmssSecurity.Ghost.openΦ (SigningLane2FlatProof.laneKey P).parameter cache trace :=
    Finset.sum_congr rfl fun e _ => by
      rw [(XmssSecurity.Partner.potentials_cacheQuery_of_not_input (hne e) u).1]
  have hhv : XmssSecurity.Ghost.hvSum (SigningLane2FlatProof.laneKey P).parameter
      (cache.cacheQuery input u) trace =
        XmssSecurity.Ghost.hvSum (SigningLane2FlatProof.laneKey P).parameter cache trace :=
    Finset.sum_congr rfl fun e _ => by
      rw [XmssSecurity.Partner.V_congr (XmssSecurity.Ghost.frozen_agree_of_none hdec u e),
        XmssSecurity.Partner.H_congr (XmssSecurity.Ghost.frozen_agree_of_none hdec u e)]
  have hcount := XmssSecurity.Ghost.counts_fresh_closed (cache := cache) (trace := trace)
    (fun p hp => by rw [hdec] at hp; cases hp) u
  have hpost : XmssSecurity.Ghost.PostBad (SigningLane2FlatProof.laneKey P).parameter trace
      (cache.cacheQuery input u) ↔
        XmssSecurity.Ghost.PostBad (SigningLane2FlatProof.laneKey P).parameter trace cache := by
    simp only [XmssSecurity.Ghost.PostBad, hq]
  simp only [SigningCompilerPotential.viewSum, SigningLane2Proof.lane2Sum, XmssSecurity.Ghost.f1,
    XmssSecurity.Ghost.f2, XmssSecurity.Ghost.f3, XmssSecurity.Ghost.f4, XmssSecurity.Ghost.postPot,
    hΦ, hhv, hcount.1, hcount.2, hpost]

/-- A message digest call keeps the trace. It keeps the view, or it adds one fresh entry to the
view. -/
theorem message_view (P : PublicParameter) (seeds : C.Term → HashOutput) (input : HashInput)
    (hmsg : IsMsg input) (st : CompilerBackend C)
    (r : DeferredSpec C (.hash (.hash input)) × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds (.hash (.hash input))).run st)) :
    r.2.trace = st.trace ∧ (compilerView r.2 = compilerView st ∨
      (st.data.cache (.hash input) = none ∧
        ∃ u, compilerView r.2 = ((compilerView st).1.cacheQuery input u, (compilerView st).2))) := by
  rw [SigningCompilerPotential.compiler_hash_message P seeds input hmsg st] at run
  erw [support_map (m := ProbComp)] at run
  obtain ⟨a, ha, rfl⟩ := run
  refine ⟨rfl, ?_⟩
  change (SigningLane2BridgeProof.keptView IsMsg a.2, st.trace.1) =
      (SigningLane2BridgeProof.keptView IsMsg st.data.cache, st.trace.1) ∨
    (st.data.cache (.hash input) = none ∧ ∃ u, (SigningLane2BridgeProof.keptView IsMsg a.2,
      st.trace.1) = ((SigningLane2BridgeProof.keptView IsMsg st.data.cache).cacheQuery input u,
        st.trace.1))
  cases cached : st.data.cache (.hash input) with
  | some value =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ cached,
      mem_support_pure_iff] at ha
    subst a
    exact Or.inl rfl
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ cached] at ha
    simp only [support_map, Set.mem_image] at ha
    obtain ⟨u, _, rfl⟩ := ha
    exact Or.inr ⟨rfl, u, by rw [SigningLane2BridgeProof.keptView_cacheQuery_of_kept hmsg]⟩

/-- A call that the ledger does not charge does not raise the count of leanVM on a backend that
stays live. A charged call raises it by at most one. -/
theorem own_count_le (prims : Primitives) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C × ℕ) (reachable : CompilerReachable P seeds st)
    (live : st.1.trace.2 = false) (stored : HiddenKey → Option Digest) (g : OwnGhost)
    (clean : g.dirty = false) (single : ¬SecondOpening P seeds st.1.data)
    (r : DeferredSpec C t × CompilerBackend C)
    (run : r ∈ support ((compilerImpl P seeds t).run st.1)) (nextLive : r.2.trace.2 = false) :
    XmssSecurity.Ghost.nCount P (compilerView r.2).1 (compilerView r.2).2 ≤
      XmssSecurity.Ghost.nCount P (compilerView st.1).1 (compilerView st.1).2 +
        if ownCharged P seeds t (st, stored) g then 1 else 0 := by
  have bases := (CompilerReachable.entryBases P seeds st reachable).1
  have trials := SigningCompilerPotential.reachable_entryTrials P seeds st reachable
  by_cases charged : ownCharged P seeds t (st, stored) g
  · have bound := SigningCompilerPotential.compiler_count_le prims P seeds st.1 bases trials t r
      run nextLive
    rw [if_pos charged]
    split_ifs at bound <;> omega
  rw [if_neg charged, Nat.add_zero]
  have same : compilerView r.2 = compilerView st.1 →
      XmssSecurity.Ghost.nCount P (compilerView r.2).1 (compilerView r.2).2 ≤
        XmssSecurity.Ghost.nCount P (compilerView st.1).1 (compilerView st.1).2 := by
    intro eq
    rw [eq]
  by_cases counted : deferredCounted t
  swap
  · exact same (compilerImpl_view_uncounted P seeds t counted st.1 r run).1
  cases t with
  | hash q =>
    by_cases hhash : ∃ input, q = .hash input
    swap
    · exact same (compilerImpl_view_not_hash P seeds (.hash q)
        ⟨q, rfl, fun input eq => hhash ⟨input, eq⟩⟩ st.1 r run).1
    obtain ⟨input, rfl⟩ := hhash
    by_cases hmsg : IsMsg input
    · rcases (message_view P seeds input hmsg st.1 r run).2 with view | ⟨fresh, u, view⟩
      · exact same view
      cases hdec : XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey P).parameter input with
      | some p =>
        exact absurd ⟨input, rfl, Or.inr ⟨hmsg, by rw [hdec]; rfl, fresh, live, clean, single⟩⟩
          charged
      | none =>
        rw [view]
        exact (XmssSecurity.Ghost.counts_fresh_closed
          (fun p hp => absurd (hp.symm.trans hdec) (Option.some_ne_none p)) u).1.le
    by_cases trigger : ∃ e, SigningGuessProof.RandomizerCached seeds st.1.data.cache e ∧
      SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e)
        (compilerSigning st.1) (.inr (.inr (.inl (.hash input))))
    · obtain ⟨e, hprf, hcall⟩ := trigger
      obtain ⟨message, bound, canonical⟩ := SigningCompilerPotential.base_call_query P
        (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (compilerSigning st.1)
        (.hash input) e hcall
      cases cached : st.1.data.cache (.hash (randomizerInput P bottomLayer e
          (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (bytesLE 32 message))) with
      | none =>
        rw [SigningCompilerPotential.compiler_fresh_base_count prims P seeds st.1 e message hprf
          bound cached _ canonical r run]
      | some answer =>
        by_cases recorded : e ∈ st.1.trace.1.leafIndices
        · exact same (SigningCompilerPotential.compiler_traced_base_view P seeds st.1 bases trials
            e message hprf bound recorded _ canonical r run)
        · have stop := SigningCompilerPotential.compiler_stale_base P seeds st.1 e message hprf
            bound answer cached recorded _ canonical r run
          simp [nextLive] at stop
    · exact same (SigningCompilerPotential.compiler_hash_other_view P seeds input hmsg st.1
        trigger r run)
  | pending p => exact same (compilerImpl_view_pending P seeds p st.1 r run).1
  | virtual T p => exact same (compilerImpl_view_virtual P seeds T p st.1 r run).1
  | _ => simp [deferredCounted] at counted

/-- Each step keeps the invariant of the potential. -/
theorem ownInv_step (prims : Primitives) (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C × ℕ) (stored : HiddenKey → Option Digest)
    (g : OwnGhost) (h : OwnInv P seeds (st, g)) :
    ∀ r ∈ support ((countImpl (compilerImpl P seeds) deferredCounted t).run st),
      OwnInv P seeds (r.2, ownAux P seeds t (st, stored) g) := by
  intro r hr
  refine ⟨CompilerReachable.step t st r h.1 hr, ?_⟩
  simp only [countImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  cases nextLive : a.2.trace.2 with
  | true => exact Or.inl rfl
  | false =>
  by_cases dirty : g.dirty = true ∨ SecondOpening P seeds st.1.data
  · refine Or.inr (Or.inl ?_)
    rcases dirty with dirty | dirty <;> simp [ownAux, dirty]
  simp only [not_or, Bool.not_eq_true] at dirty
  obtain ⟨clean, single⟩ := dirty
  have live : st.1.trace.2 = false := by
    cases hs : st.1.trace.2 with
    | false => rfl
    | true => simpa [nextLive] using compilerImpl_stale P seeds t st.1 hs a ha
  have old : XmssSecurity.Ghost.nCount P (compilerView st.1).1 (compilerView st.1).2 ≤ g.ledger := by
    rcases h.2 with h | h | h
    · simp [live] at h
    · simp [clean] at h
    · exact h
  have bound := own_count_le prims P seeds t st h.1 live stored g clean single a ha nextLive
  refine Or.inr (Or.inr ?_)
  change XmssSecurity.Ghost.nCount P (compilerView a.2).1 (compilerView a.2).2 ≤
    g.ledger + if ownCharged P seeds t (st, stored) g then 1 else 0
  omega

/-- The counted run with a function of the state is the run of the backend. -/
theorem tsum_countImpl (P : PublicParameter) (seeds : C.Term → HashOutput) (t : DeferredQuery C)
    (st : CompilerBackend C × ℕ) (F : CompilerBackend C × ℕ → ℝ≥0∞) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] * F r.2 =
      ∑' r, Pr[= r | (compilerImpl P seeds t).run st.1] *
        F (r.2, st.2 + if deferredCounted t then 1 else 0) := by
  simp only [countImpl, StateT.run_mk]
  rw [tsum_probOutput_map_mul]

/-- A tick of the count within the budget lowers the compensated sum. -/
theorem viewSum_tick (P : PublicParameter) (B : ℕ)
    (v : XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace) (k : ℕ)
    (hk : k + 1 ≤ B) :
    SigningCompilerPotential.viewSum P B (v, k + 1) ≤ SigningCompilerPotential.viewSum P B (v, k) := by
  simp only [SigningCompilerPotential.viewSum, SigningLane2Proof.lane2Sum]
  have h3 : XmssSecurity.Ghost.f3 (SigningLane2FlatProof.laneKey P) B (v, k + 1) ≤
      XmssSecurity.Ghost.f3 (SigningLane2FlatProof.laneKey P) B (v, k) :=
    XmssSecurity.Partner.F3_budget (by omega)
  refine add_le_add ?_ le_rfl
  refine add_le_add le_rfl ?_
  exact tsub_le_tsub_right h3 _

/-- The own potential at a ledger of `k` or `k + 1` is at most the scaled sum at `k`. -/
theorem ownPotential_le (P : PublicParameter) (B : ℕ) (s : CompilerBackend C × ℕ) (g : OwnGhost)
    (k : ℕ) (hk : k ≤ g.ledger) (hk' : g.ledger ≤ k + 1) :
    ownPotential P B (s, g) ≤ SigningCompilerPotential.viewSum P B (compilerView s.1, k) *
      ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
  unfold ownPotential
  split_ifs with h
  · exact zero_le
  simp only [not_or, not_lt] at h
  refine mul_le_mul' ?_ le_rfl
  rcases (by omega : g.ledger = k ∨ g.ledger = k + 1) with e | e
  · rw [e]
  · rw [e]
    exact viewSum_tick P B _ k (by omega)

/-- The step of the own potential. It rises by at most `2^-128` at a charged call below the budget
that carries no candidate at an unrevealed key. It does not rise at another call. -/
theorem ownPotential_step (prims : Primitives) (x : Keys3 C) (B : ℕ) (hB : B < 2 ^ 127)
    (t : DeferredQuery C) (st : CompilerBackend C × ℕ) (stored : HiddenKey → Option Digest)
    (g : OwnGhost) (h : OwnInv x.1 x.2.1 (st, g)) :
    ∑' r, Pr[= r | (countImpl (compilerImpl x.1 x.2.1) deferredCounted t).run st] *
        ownPotential x.1 B (r.2, ownAux x.1 x.2.1 t (st, stored) g) ≤
      ownPotential x.1 B (st, g) +
        if ownCharged x.1 x.2.1 t (st, stored) g ∧ g.ledger < B ∧
            ¬(deferredInputSide x.1 t ∧ stored (deferredKey x.1 t) = none) then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  generalize hg' : ownAux x.1 x.2.1 t (st, stored) g = g'
  have hledger : g'.ledger = g.ledger + if ownCharged x.1 x.2.1 t (st, stored) g then 1 else 0 := by
    rw [← hg']
    rfl
  have hstep : g.ledger ≤ g'.ledger ∧ g'.ledger ≤ g.ledger + 1 := by
    rw [hledger]
    split_ifs <;> omega
  by_cases zero : st.1.trace.2 = true ∨ g'.dirty = true ∨ B < g'.ledger
  · refine (XmssSecurity.Ghost.tsum_le_of_support _ _ 0 fun r hr => ?_).trans (zero_le)
    simp only [countImpl, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    simp only [ownPotential]
    rw [if_pos]
    rcases zero with zero | zero | zero
    · exact Or.inl (compilerImpl_stale x.1 x.2.1 t st.1 zero a ha)
    · exact Or.inr (Or.inl zero)
    · exact Or.inr (Or.inr zero)
  simp only [not_or, Bool.not_eq_true, not_lt] at zero
  obtain ⟨live, clean', room'⟩ := zero
  have clean : g.dirty = false ∧ ¬SecondOpening x.1 x.2.1 st.1.data := by
    rw [← hg'] at clean'
    simpa [ownAux] using clean'
  obtain ⟨clean, single⟩ := clean
  have within : g.ledger ≤ B := by omega
  have pre : ownPotential x.1 B (st, g) =
      SigningCompilerPotential.viewSum x.1 B (compilerView st.1, g.ledger) *
        ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
    have hz : ¬(st.1.trace.2 = true ∨ g.dirty = true ∨ B < g.ledger) := by
      simp only [live, clean, Bool.false_eq_true, false_or, not_lt]
      exact within
    rw [ownPotential, if_neg hz]
  have inv : XmssSecurity.Ghost.Inv (SigningLane2FlatProof.laneKey x.1)
      (compilerView st.1, g.ledger) := by
    rcases h.2 with h' | h' | h'
    · simp [live] at h'
    · simp [clean] at h'
    · exact h'
  refine (tsum_countImpl x.1 x.2.1 t st (fun s => ownPotential x.1 B (s, g'))).le.trans ?_
  have pointwise : (∀ r ∈ support ((compilerImpl x.1 x.2.1 t).run st.1), r.2.trace.2 = false →
      SigningCompilerPotential.viewSum x.1 B (compilerView r.2, g.ledger) ≤
        SigningCompilerPotential.viewSum x.1 B (compilerView st.1, g.ledger)) →
      ∑' r, Pr[= r | (compilerImpl x.1 x.2.1 t).run st.1] *
        ownPotential x.1 B ((r.2, st.2 + if deferredCounted t then 1 else 0), g') ≤
          ownPotential x.1 B (st, g) := by
    intro hp
    refine XmssSecurity.Ghost.tsum_le_of_support _ _ _ fun r hr => ?_
    cases nl : r.2.trace.2 with
    | true => simp only [ownPotential, nl, true_or, if_true]; exact zero_le
    | false =>
      rw [pre]
      exact (ownPotential_le x.1 B (r.2, st.2 + if deferredCounted t then 1 else 0) g' g.ledger
        hstep.1 hstep.2).trans
        (mul_le_mul' (hp r hr nl) le_rfl)
  have expect : ∑' r, Pr[= r | (compilerImpl x.1 x.2.1 t).run st.1] *
        SigningCompilerPotential.viewSum x.1 B (compilerView r.2, g.ledger) ≤
        SigningCompilerPotential.viewSum x.1 B (compilerView st.1, g.ledger) →
      ∑' r, Pr[= r | (compilerImpl x.1 x.2.1 t).run st.1] *
        ownPotential x.1 B ((r.2, st.2 + if deferredCounted t then 1 else 0), g') ≤
          ownPotential x.1 B (st, g) := by
    intro he
    rw [pre]
    calc _ ≤ ∑' r, Pr[= r | (compilerImpl x.1 x.2.1 t).run st.1] *
          (SigningCompilerPotential.viewSum x.1 B (compilerView r.2, g.ledger) *
            ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹) :=
          ENNReal.tsum_le_tsum fun r =>
            mul_le_mul_right (ownPotential_le x.1 B (r.2, st.2 + if deferredCounted t then 1 else 0)
              g' g.ledger hstep.1 hstep.2) _
      _ = (∑' r, Pr[= r | (compilerImpl x.1 x.2.1 t).run st.1] *
          SigningCompilerPotential.viewSum x.1 B (compilerView r.2, g.ledger)) *
            ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
        rw [← ENNReal.tsum_mul_right]
        simp only [mul_assoc]
      _ ≤ _ := mul_le_mul' he le_rfl
  by_cases counted : deferredCounted t
  swap
  · exact (pointwise fun r hr _ => by
      rw [(compilerImpl_view_uncounted x.1 x.2.1 t counted st.1 r hr).1]).trans le_self_add
  cases t with
  | hash q =>
    by_cases hhash : ∃ input, q = .hash input
    swap
    · exact (pointwise fun r hr _ => by
        rw [(compilerImpl_view_not_hash x.1 x.2.1 (.hash q)
          ⟨q, rfl, fun input eq => hhash ⟨input, eq⟩⟩ st.1 r hr).1]).trans le_self_add
    obtain ⟨input, rfl⟩ := hhash
    by_cases hmsg : IsMsg input
    · by_cases fresh : (XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey x.1).parameter
          input).isSome ∧ st.1.data.cache (.hash input) = none
      · have hc : ownCharged x.1 x.2.1 (.hash (.hash input)) (st, stored) g :=
          ⟨input, rfl, Or.inr ⟨hmsg, fresh.1, fresh.2, live, clean, single⟩⟩
        have room : g.ledger < B := by
          rw [hledger, if_pos hc] at room'
          omega
        have side : ¬(deferredInputSide x.1 (C := C) (.hash (.hash input)) ∧
            stored (deferredKey x.1 (C := C) (.hash (.hash input))) = none) := by
          rintro ⟨hs, -⟩
          simp [deferredInputSide, deferredCandidate,
            hiddenCandidate_none_of_isMsg x.1 input hmsg] at hs
        rw [if_pos (And.intro hc (And.intro room side))]
        have sum := (tsum_countImpl x.1 x.2.1 _ (st.1, g.ledger)
          (fun s => SigningCompilerPotential.viewSum x.1 B (compilerView s.1, s.2))).symm.le.trans
          (SigningCompilerPotential.compiler_message_sum_le prims ⟨0, x.1⟩ x.1 x.2.1 B hB input
            hmsg (st.1, g.ledger) inv room)
        simp only [deferredCounted, if_true] at sum
        rw [pre]
        calc _ ≤ ∑' r, Pr[= r | (compilerImpl x.1 x.2.1 (.hash (.hash input))).run st.1] *
              (SigningCompilerPotential.viewSum x.1 B (compilerView r.2, g.ledger + 1) *
                ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹) :=
              ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ownPotential_le x.1 B
                (r.2, st.2 + if deferredCounted (C := C) (.hash (.hash input)) then 1 else 0) g'
                (g.ledger + 1) (by rw [hledger, if_pos hc]) (by omega)) _
          _ = (∑' r, Pr[= r | (compilerImpl x.1 x.2.1 (.hash (.hash input))).run st.1] *
              SigningCompilerPotential.viewSum x.1 B (compilerView r.2, g.ledger + 1)) *
                ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := by
            rw [← ENNReal.tsum_mul_right]
            simp only [mul_assoc]
          _ ≤ (SigningCompilerPotential.viewSum x.1 B (compilerView st.1, g.ledger) + 2 ^ 128) *
                ((2 ^ 128 : ℝ≥0∞) * 2 ^ 128)⁻¹ := mul_le_mul' sum le_rfl
          _ = _ := by
            have hzero : (2 ^ 128 : ℝ≥0∞) ≠ 0 := by norm_num
            have htop : (2 ^ 128 : ℝ≥0∞) ≠ ⊤ := by norm_num
            rw [add_mul, ENNReal.mul_inv (Or.inl hzero) (Or.inl htop), ← mul_assoc (2 ^ 128 : ℝ≥0∞),
              ENNReal.mul_inv_cancel hzero htop, one_mul]
      · refine (pointwise fun r hr _ => ?_).trans le_self_add
        rcases (message_view x.1 x.2.1 input hmsg st.1 r hr).2 with view | ⟨cached, u, view⟩
        · rw [view]
        have hdec : XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey x.1).parameter input =
            none := by
          cases hd : XmssSecurity.Ghost.dec (SigningLane2FlatProof.laneKey x.1).parameter input with
          | none => rfl
          | some p => exact absurd ⟨by rw [hd]; rfl, cached⟩ fresh
        rw [view]
        exact (viewSum_closed x.1 B _ _ _ input u
          (by simp only [compilerView, SigningLane2BridgeProof.keptView, if_pos hmsg]; exact cached)
          hdec).le
    by_cases trigger : ∃ e, SigningGuessProof.RandomizerCached x.2.1 st.1.data.cache e ∧
        SigningFlatProof.BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 st.1.data.cache e)
          (compilerSigning st.1) (.inr (.inr (.inl (.hash input))))
    · obtain ⟨e, hprf, base⟩ := trigger
      obtain ⟨m, bound, canonical⟩ := SigningCompilerPotential.base_call_query x.1
        (SigningGuessProof.cachedRandomizer x.2.1 st.1.data.cache e)
        (compilerSigning st.1) (.hash input) e base
      cases cached : st.1.data.cache (.hash (randomizerInput x.1 bottomLayer e
          (SigningGuessProof.cachedRandomizer x.2.1 st.1.data.cache e) (bytesLE 32 m))) with
      | none =>
        exact (expect (SigningCompilerPotential.fresh_base_sum_le prims ⟨0, x.1⟩ x.1 x.2.1 B hB
          (st.1, g.ledger) inv e m hprf bound cached (.hash input) canonical)).trans le_self_add
      | some answer =>
        refine (pointwise fun r hr nextLive => ?_).trans le_self_add
        by_cases recorded : e ∈ st.1.trace.1.leafIndices
        · rw [SigningCompilerPotential.compiler_traced_base_view x.1 x.2.1 st.1
            (CompilerReachable.entryBases x.1 x.2.1 st h.1).1
            (SigningCompilerPotential.reachable_entryTrials x.1 x.2.1 st h.1) e m hprf bound
            recorded (.hash input) canonical r hr]
        · have stale := SigningCompilerPotential.compiler_stale_base x.1 x.2.1 st.1 e m hprf bound
            answer cached recorded (.hash input) canonical r hr
          exact False.elim (Bool.false_ne_true (nextLive.symm.trans stale))
    · exact (pointwise fun r hr _ => by
        rw [SigningCompilerPotential.compiler_hash_other_view x.1 x.2.1 input hmsg st.1 trigger r
          hr]).trans le_self_add
  | pending p =>
    exact (pointwise fun r hr _ => by
      rw [(compilerImpl_view_pending x.1 x.2.1 p st.1 r hr).1]).trans le_self_add
  | virtual T p =>
    exact (pointwise fun r hr _ => by
      rw [(compilerImpl_view_virtual x.1 x.2.1 T p st.1 r hr).1]).trans le_self_add
  | _ => simp [deferredCounted] at counted

/-- The lane 2 event on a state that is not dirty and within the budget gives a potential of at
least one. -/
theorem ownPotential_event (P : PublicParameter) (Q B : ℕ) (st : CompilerBackend C × ℕ)
    (g : OwnGhost) (hE : compilerEvent P Q st) (hd : g.dirty = false) (hB : g.ledger ≤ B) :
    1 ≤ ownPotential P B (st, g) := by
  obtain ⟨hs, he, -⟩ := hE
  have hN : (((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞)) = (2 ^ 128 : ℝ≥0∞) := by
    norm_num [XmssSecurity.digestBits]
  have hbad : (2 ^ 128 : ℝ≥0∞) * 2 ^ 128 ≤
      XmssSecurity.Ghost.f1 (SigningLane2FlatProof.laneKey P) (compilerView st.1, g.ledger) +
        XmssSecurity.Ghost.f4 (SigningLane2FlatProof.laneKey P) (compilerView st.1, g.ledger) := by
    rcases he with he | he
    · refine le_trans ?_ le_self_add
      unfold XmssSecurity.Ghost.f1
      rw [if_pos he, mul_one, hN]
      exact le_self_add
    · refine le_trans ?_ le_add_self
      unfold XmssSecurity.Ghost.f4 XmssSecurity.Ghost.postPot
      rw [if_pos he, mul_one, hN]
  rw [ownPotential, if_neg (by simp only [hs, hd, Bool.false_eq_true, false_or, not_lt]; exact hB),
    SigningCompilerPotential.viewSum, SigningLane2Proof.lane2Sum]
  calc (1 : ℝ≥0∞) = (2 ^ 128 * 2 ^ 128) * (2 ^ 128 * 2 ^ 128)⁻¹ :=
      (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm
    _ ≤ _ := by
      refine mul_le_mul' (hbad.trans ?_) le_rfl
      rw [add_right_comm]
      exact le_self_add

/-- A query with a candidate is a hash call on an input with that candidate. -/
theorem deferredCandidate_some (P : PublicParameter) {t : DeferredQuery C}
    {c : HiddenKey × Digest} (h : deferredCandidate P t = some c) :
    ∃ input, t = .hash (.hash input) ∧ hiddenCandidate P input = some c := by
  unfold deferredCandidate at h
  split at h
  · exact ⟨_, rfl, h⟩
  · cases h

/-- A call that can raise the cap flag is charged. -/
theorem ownCharged_of_inputSide (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C × ℕ) (stored : HiddenKey → Option Digest)
    (g : OwnGhost) (side : deferredInputSide P t) (unrevealed : stored (deferredKey P t) = none) :
    ownCharged P seeds t (st, stored) g := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp side
  have hkey : deferredKey P t = c.1 := by
    change ((deferredCandidate P t).getD (default, 0)).1 = c.1
    rw [hc, Option.getD_some]
  rw [hkey] at unrevealed
  obtain ⟨input, rfl, hcandidate⟩ := deferredCandidate_some P hc
  exact ⟨input, rfl, Or.inl ⟨c, hcandidate, unrevealed⟩⟩

attribute [local irreducible] sourceProgramO1 in
set_option maxRecDepth 100000 in
/-- The cap of the run with the ledger. The cap flag, or the lane 2 event on a state that is not
dirty, with the ledger within `B`, has probability at most `B / 2^128`. -/
theorem ownRun_cap (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (Q B : ℕ)
    (hB : B < 2 ^ 127) :
    Pr[fun r => (r.1.2.2.2 = true ∨ (compilerEvent x.1 Q r.1.2.1 ∧ r.2.dirty = false)) ∧
        r.2.ledger ≤ B | ownRun prims A x Q] ≤ (B : ℝ≥0∞) / 2 ^ 128 := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by
    unfold Digest digestBits
    exact card_bitVec 128
  have live : (compilerInit (C := C)).trace.2 = false := by simp [compilerInit]
  have hinit : OwnInv x.1 x.2.1 ((compilerInit, 0), ⟨0, false⟩) :=
    ⟨CompilerReachable.initial, Or.inr (Or.inr (SigningCompilerPotential.reachable_ghostInv prims
      x.1 x.2.1 (compilerInit, 0) CompilerReachable.initial live))⟩
  have hf₀ : ownPotential x.1 B ((compilerInit (C := C), 0), ⟨0, false⟩) = 0 := by
    have h0 := compilerPotential_initial (C := C) x.1 B
    rw [SigningCompilerPotential.compilerPotential_eq_sum x.1 B _ live (Nat.zero_le _)] at h0
    rw [ownPotential, if_neg (by simp [live])]
    exact h0
  have main := probEvent_ledger_expect_le (impl := countImpl (compilerImpl x.1 x.2.1) deferredCounted)
    (counted := cappedCall deferredCounted Q) (inputSide := deferredInputSide x.1)
    (keyOf := deferredKey x.1) (point := deferredPoint x.1) (aux := ownAux x.1 x.2.1)
    (ownCharged x.1 x.2.1) OwnGhost.ledger B (OwnInv x.1 x.2.1) (ownPotential x.1 B)
    (fun _ _ _ => rfl)
    (fun t st stored g _ side unrevealed =>
      ownCharged_of_inputSide x.1 x.2.1 t st stored g side unrevealed)
    (fun t st stored g hs r hr => ownInv_step prims x.1 x.2.1 t st stored g hs r hr)
    (fun t st stored g hs => by
      simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using
        ownPotential_step prims x B hB t st stored g hs)
    (fun st => compilerEvent x.1 Q st.1 ∧ st.2.dirty = false)
    (fun st g hE hl => ownPotential_event x.1 Q B st g hE.1 hE.2 hl)
    (sourceProgramO1 prims A x) (compilerInit, 0) ⟨0, false⟩ hinit hf₀ rfl
  have hrun : ownRun prims A x Q = (fun r => ((r.1, r.2.1), r.2.2)) <$>
      ($ᵗ (HiddenKey → Digest) >>= fun s =>
        (simulateQ (ownHybrid x.1 x.2.1 Q s) (sourceProgramO1 prims A x)).run ownInit) := by
    rw [map_bind]
    rfl
  rw [hrun, probEvent_map]
  refine main.trans (le_of_eq ?_)
  rw [hcard, div_eq_mul_inv]
  norm_num

end SigningOwnCapPotential

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.viewSum_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.viewSum_closed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.message_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.message_view

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.own_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.own_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownInv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownInv_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.tsum_countImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.tsum_countImpl

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.viewSum_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.viewSum_tick

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownPotential_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownPotential_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownPotential_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownPotential_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownPotential_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownPotential_event

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.deferredCandidate_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.deferredCandidate_some

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownCharged_of_inputSide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownCharged_of_inputSide

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownRun_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCapPotential.ownRun_cap
