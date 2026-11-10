import ThresholdLeanXmssSecurity.Proof.SigningHitLane

set_option pp.deepTerms false
set_option pp.maxSteps 2000

noncomputable section

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
open SigningHitLaneProof SigningCostProof

namespace SigningHitProof

variable {C : Committee} (prims : Primitives)

/-- Consume one entry of a complete raw-query transcript. -/
def transcriptNext {α : Type} (oa : OracleComp (WorldSpec C) α)
    (entry : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) :
    Option (OracleComp (WorldSpec C) α) :=
  open Classical in
  match oa with
  | .pure _ => none
  | .queryBind t k => if h : entry.1 = t then some (k (h ▸ entry.2)) else none

/-- The residual computation is absent after the transcript deviates from the program. -/
def transcriptResidual {α : Type} (oa : OracleComp (WorldSpec C) α)
    (log : QueryLog (WorldSpec C)) : Option (OracleComp (WorldSpec C) α) :=
  log.foldl (fun residual entry => residual.bind (fun c => transcriptNext c entry)) (some oa)

theorem transcriptResidual_append {α : Type} (oa : OracleComp (WorldSpec C) α)
    (log : QueryLog (WorldSpec C)) (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) :
    transcriptResidual oa (log.logQuery t u) =
      (transcriptResidual oa log).bind (fun c => transcriptNext c ⟨t, u⟩) := by
  simp [transcriptResidual, QueryLog.logQuery, QueryLog.singleton, List.foldl_append]

/-- The continuation reserve uses the full cache, including private honest values. -/
def continuationReserve {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (s : LoggedState C) : ℝ≥0∞ :=
  match transcriptResidual oa s.2 with
  | none => 0
  | some c => Pr[event | (simulateQ (loggedImpl prims) c).run s]

theorem continuationReserve_step {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (t : (WorldSpec C).Domain) (s : LoggedState C) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] *
      continuationReserve prims oa event r.2 ≤ continuationReserve prims oa event s := by
  classical
  unfold continuationReserve
  cases hres : transcriptResidual oa s.2 with
  | none =>
      apply le_of_eq
      apply ENNReal.tsum_eq_zero.mpr
      intro r
      by_cases hr : r ∈ support ((loggedImpl prims t).run s)
      · simp [loggedImpl_log prims t s r hr, transcriptResidual_append, hres]
      · simp [probOutput_eq_zero_of_not_mem_support hr]
  | some c =>
      cases c with
      | pure a =>
          have hz : (∑' r, Pr[= r | (loggedImpl prims t).run s] *
              (match transcriptResidual oa r.2.2 with
              | none => 0
              | some c => Pr[event | (simulateQ (loggedImpl prims) c).run r.2])) = 0 := by
            apply ENNReal.tsum_eq_zero.mpr
            intro r
            by_cases hr : r ∈ support ((loggedImpl prims t).run s)
            · simp [loggedImpl_log prims t s r hr, transcriptResidual_append, hres, transcriptNext]
            · simp [probOutput_eq_zero_of_not_mem_support hr]
          rw [hz]
          exact zero_le
      | queryBind t' k =>
          by_cases ht : t = t'
          · subst t'
            apply le_of_eq
            change _ = Pr[event | (simulateQ (loggedImpl prims) (query t >>= k)).run s]
            simp only [simulateQ_bind, StateT.run_bind]
            rw [probEvent_bind_eq_tsum]
            apply tsum_congr
            intro r
            by_cases hr : r ∈ support ((loggedImpl prims t).run s)
            · simp [loggedImpl_log prims t s r hr, transcriptResidual_append, hres, transcriptNext]
            · simp [probOutput_eq_zero_of_not_mem_support hr]
          · have hz : (∑' r, Pr[= r | (loggedImpl prims t).run s] *
                (match transcriptResidual oa r.2.2 with
                | none => 0
                | some c => Pr[event | (simulateQ (loggedImpl prims) c).run r.2])) = 0 := by
              apply ENNReal.tsum_eq_zero.mpr
              intro r
              by_cases hr : r ∈ support ((loggedImpl prims t).run s)
              · simp [loggedImpl_log prims t s r hr, transcriptResidual_append, hres, transcriptNext, ht]
              · simp [probOutput_eq_zero_of_not_mem_support hr]
            rw [hz]
            exact zero_le

/-- A supported execution consumes its transcript and leaves its return value. -/
theorem transcriptResidual_run {α : Type} (main oa : OracleComp (WorldSpec C) α) :
    ∀ s : LoggedState C, transcriptResidual main s.2 = some oa →
    ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s),
      transcriptResidual main z.2.2 = some (pure z.1) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact hs
  | query_bind t k ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, hr, hz⟩ := hz
      apply ih r.1 r.2 _ z hz
      rw [loggedImpl_log prims t s r hr, transcriptResidual_append, hs]
      change transcriptNext (queryBind t k) ⟨t, r.1⟩ = some (k r.1)
      simp [transcriptNext]

theorem continuationReserve_terminal {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (z : α × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run loggedInit))
    (he : event z) : continuationReserve prims oa event z.2 = 1 := by
  classical
  have hres := transcriptResidual_run prims oa oa loggedInit rfl z hz
  simp [continuationReserve, hres, he]

/-- A reserve paid at the first query and carried without further charges. -/
def fundedContinuation {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (s : LoggedState C) : ℝ≥0∞ :=
  open Classical in if s.2 = [] then 0 else continuationReserve prims oa event s

theorem loggedImpl_log_nonempty (t : (WorldSpec C).Domain) (s : LoggedState C)
    (r : (WorldSpec C).Range t × LoggedState C)
    (hr : r ∈ support ((loggedImpl prims t).run s)) : r.2.2 ≠ [] := by
  rw [loggedImpl_log prims t s r hr]
  simp [QueryLog.logQuery, QueryLog.singleton]

theorem initialLogInvariant_step (t : (WorldSpec C).Domain) (s : LoggedState C)
    (r : (WorldSpec C).Range t × LoggedState C)
    (hr : r ∈ support ((loggedImpl prims t).run s)) :
    r.2.2 = [] → r.2 = loggedInit := by
  intro hnil
  exact (loggedImpl_log_nonempty prims t s r hr hnil).elim

theorem fundedContinuation_next {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (t : (WorldSpec C).Domain) (s : LoggedState C) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] * fundedContinuation prims oa event r.2) =
      ∑' r, Pr[= r | (loggedImpl prims t).run s] * continuationReserve prims oa event r.2 := by
  apply tsum_congr
  intro r
  by_cases hr : r ∈ support ((loggedImpl prims t).run s)
  · simp [fundedContinuation, loggedImpl_log_nonempty prims t s r hr]
  · simp [probOutput_eq_zero_of_not_mem_support hr]

open Classical in
/-- Only the initial, matching query pays for this reserve. A small event bound
therefore suffices even for the universal raw-query condition of IsHitPotential. -/
theorem fundedContinuation_step {α : Type} (first : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range first → OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (ε : ℝ≥0∞)
    (hprob : Pr[event | (simulateQ (loggedImpl prims) (query first >>= k)).run loggedInit] ≤ ε)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : s.2 = [] → s = loggedInit) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] *
      fundedContinuation prims (query first >>= k) event r.2) ≤
      fundedContinuation prims (query first >>= k) event s +
        @ite ℝ≥0∞ (s.2 = [] ∧ t = first) (Classical.propDecidable _) ε 0 := by
  classical
  letI : DecidableEq ((WorldSpec C).Range t × LoggedState C) := Classical.decEq _
  rw [fundedContinuation_next]
  by_cases hnil : s.2 = []
  · have hstate := hs hnil
    subst s
    by_cases ht : t = first
    · subst t
      simpa [fundedContinuation, continuationReserve, transcriptResidual, loggedInit] using
        (continuationReserve_step prims (query first >>= k) event first loggedInit).trans hprob
    · have hz : (∑' r, Pr[= r | (loggedImpl prims t).run loggedInit] *
          continuationReserve prims (query first >>= k) event r.2) = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        intro r
        by_cases hr : r ∈ support ((loggedImpl prims t).run loggedInit)
        · change Pr[= r | (loggedImpl prims t).run loggedInit] *
            continuationReserve prims (queryBind first k) event r.2 = 0
          simp [continuationReserve, loggedImpl_log prims t loggedInit r hr,
            transcriptResidual, loggedInit, transcriptNext,
            QueryLog.logQuery, QueryLog.singleton, ht]
        · simp [probOutput_eq_zero_of_not_mem_support hr]
      rw [hz]
      simp [fundedContinuation, loggedInit, ht]
  · simpa [fundedContinuation, hnil] using
      continuationReserve_step prims (query first >>= k) event t s

theorem fundedContinuation_terminal {α : Type} (first : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range first → OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (z : α × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) (query first >>= k)).run loggedInit))
    (he : event z) : fundedContinuation prims (query first >>= k) event z.2 = 1 := by
  classical
  have hres := transcriptResidual_run prims (query first >>= k) (query first >>= k) loggedInit rfl z hz
  have hnil : z.2.2 ≠ [] := by
    intro hn
    simp only [hn, transcriptResidual, List.foldl_nil, Option.some.injEq] at hres
    cases hres
  rw [fundedContinuation, if_neg hnil]
  exact continuationReserve_terminal prims _ event z hz he

/-- Preservation of the absence of programming queries from any initial log. -/
def NoProgramming {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  ∀ s : LoggedState C, ¬Programmed s.2 →
    ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s), ¬Programmed z.2.2

theorem noProgramming_pure {α : Type} (a : α) :
    NoProgramming prims (pure a : OracleComp (WorldSpec C) α) := by
  intro s hs z hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst z
  exact hs

theorem noProgramming_bind {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (k : α → OracleComp (WorldSpec C) β) (ha : NoProgramming prims oa)
    (hk : ∀ a, NoProgramming prims (k a)) : NoProgramming prims (oa >>= k) := by
  intro s hs z hz
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨r, hr, hz⟩ := hz
  exact hk r.1 r.2 (ha s hs r hr) z hz

theorem noProgramming_map {α β : Type} (f : α → β) (oa : OracleComp (WorldSpec C) α)
    (ha : NoProgramming prims oa) : NoProgramming prims (f <$> oa) := by
  rw [← bind_pure_comp]
  exact noProgramming_bind prims oa _ ha (fun _ => noProgramming_pure prims _)

theorem noProgramming_query (t : (WorldSpec C).Domain) (ht : ¬IsProgram t) :
    NoProgramming (C := C) prims (query t) := by
  intro s hs z hz
  simp at hz
  rw [loggedImpl_log prims t s z hz, programmed_logQuery]
  exact not_or.mpr ⟨hs, ht⟩

/-- Structural induction through an oracle handler that preserves the log invariant. -/
theorem noProgramming_simulate {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (OracleComp (WorldSpec C)))
    (h : ∀ t, NoProgramming prims (impl t)) (oa : OracleComp spec α) :
    NoProgramming prims (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using noProgramming_pure (C := C) prims a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact noProgramming_bind prims _ _ (h t) ih

theorem noProgramming_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    NoProgramming prims (free oa) := by
  apply noProgramming_simulate
  intro t
  exact noProgramming_query prims (.inr t) (by simp [IsProgram])

theorem noProgramming_liftFree {α : Type} (oa : OracleComp (RoSpec C) α) :
    NoProgramming prims (SigningSecurityProof.liftFree oa) :=
  noProgramming_free prims _

/-- The adversary's local calls cannot access the programming summand. -/
theorem noProgramming_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    NoProgramming prims (worldRoles.adversary oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [worldRoles, liftComp_pure, counted]
    exact noProgramming_pure prims a
  | query_bind t k ih =>
    simp only [worldRoles, liftComp_bind, counted_bind] at ih ⊢
    apply noProgramming_bind prims _ _ ?_ ih
    rcases t with t | (t | t) <;>
      exact noProgramming_query prims _ (by change ¬False; exact not_false)

/-- Structural induction also allows an auxiliary oracle state. -/
theorem noProgramming_simulateState {ι α σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (h : ∀ t s, NoProgramming prims ((impl t).run s)) (oa : OracleComp spec α) (s : σ) :
    NoProgramming prims ((simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simpa using noProgramming_pure (C := C) prims (a, s)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact noProgramming_bind prims _ _ (h t s) (fun r => ih r.1 r.2)

set_option maxRecDepth 100000 in
/-- The honest signing handler is the free lift of a local computation. -/
theorem tsigOracles_free (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (q : (TsigSpec C).Domain) (s : TsigState C) :
    (tsigOracles (fun oa => SigningCoreProof.honestLift oa)
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) q).run s =
    SigningSecurityProof.liftFree ((tsigOracles (fun oa => oa)
      (dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1)) q).run s) := by
  rw [show SigningSecurityProof.liftFree
      ((tsigOracles (fun oa => oa)
        (dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1)) q).run s) = _ from
    SeedHitProof.hom_tsigOracles SigningCacheProof.freeHom (fun oa => oa) _ q s]
  apply congrArg (fun dealt => (tsigOracles (fun oa => SigningSecurityProof.liftFree oa) dealt q).run s)
  simp only [SeedHitProof.Dealt.hmap, dealtWith, SigningCacheProof.freeHom,
    referenceTree_φ, φ_map]


/-- Neither branch of the flagged handler can program the random oracle. -/
theorem noProgramming_flaggedOracles (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TsigState C × Bool) :
    NoProgramming prims ((SigningCoreProof.flaggedOracles x
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) t).run s) := by
  cases t with
  | inl t =>
    apply noProgramming_map
    exact noProgramming_adversary prims _
  | inr q =>
    apply noProgramming_map
    rw [tsigOracles_free]
    exact noProgramming_liftFree prims _

set_option maxRecDepth 100000 in
theorem noProgramming_finish (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (r : Forgery × TsigState C) :
    NoProgramming prims (SigningCoreProof.tsigFinish
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) r) := by
  rcases r with ⟨forgery, st⟩
  unfold SigningCoreProof.tsigFinish
  apply noProgramming_bind prims _ _ (noProgramming_liftFree prims _)
  intro verified
  dsimp only
  split_ifs
  · simpa using noProgramming_pure (C := C) prims (verified && true, st, forgery)
  · apply noProgramming_bind
    · erw [SigningCacheProof.liftFree_honestSignature]
      exact noProgramming_liftFree prims _
    · intro honest
      simpa using noProgramming_pure (C := C) prims
        (verified && decide (honest ≠ some forgery.signature), st, forgery)

set_option maxRecDepth 100000 in
theorem noProgramming_finalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    NoProgramming prims (SigningDescentProof.finalRun A x) := by
  unfold SigningDescentProof.finalRun
  dsimp only
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  apply noProgramming_bind prims _ _ (noProgramming_liftFree prims _)
  intro output
  rcases output with _ | (top | tree)
  · exact noProgramming_pure prims _
  · apply noProgramming_bind
    · exact noProgramming_simulateState prims _ (noProgramming_flaggedOracles prims x top) _ _
    · intro r
      exact noProgramming_map prims _ _ (noProgramming_finish prims x top _)
  · exact noProgramming_pure prims _

/-- A fixed target costs one unit when the fresh oracle answer is sampled. -/
theorem fixedTargetCharge (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output = target | $ᵗ HashOutput] =
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  change Pr[fun output : XmssSecurity.HashOutput => XmssSecurity.truncateHash output = target |
    $ᵗ XmssSecurity.HashOutput] = _
  simpa only [XmssSecurity.digestBits, Nat.cast_pow, Nat.cast_ofNat] using
    XmssSecurity.Rom.uniform_truncate_probability target

/-- When the honest target arrives after the candidate inputs, charge each earlier
candidate once. This only bounds the sampling step; target stability is separate. -/
theorem lateTargetCharge {ι : Type} (candidates : Finset ι) (output : ι → Digest) :
    Pr[fun fresh : HashOutput => ∃ i ∈ candidates, truncateHash fresh = output i | $ᵗ HashOutput] ≤
      (candidates.card : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ∑ i ∈ candidates,
        Pr[fun fresh : HashOutput => truncateHash fresh = output i | $ᵗ HashOutput] :=
      probEvent_exists_finset_le_sum candidates _ _
    _ = _ := by simp only [fixedTargetCharge, Finset.sum_const, nsmul_eq_mul]

/-- The deferred charge applies to a fresh honest hash call in the actual logged world. -/
theorem lateTarget_loggedStep {ι : Type} (candidates : Finset ι) (output : ι → Digest)
    (q : Query C) (s : LoggedState C) (hfresh : s.1.1 q = none) :
    Pr[fun z => ∃ i ∈ candidates, truncateHash z.1 = output i |
      (loggedImpl prims (.inr (.inr (.inl q)))).run s] ≤
        (candidates.card : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    probEvent_map]
  change Pr[fun z => ∃ i ∈ candidates, truncateHash z.1 = output i |
    ((Query C →ₒ HashOutput).randomOracle q).run s.1.1] ≤ _
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hfresh, probEvent_map]
  exact lateTargetCharge candidates output

/-- A hit against targets fixed before this part of the run. Entries already in
the initial cache are excluded, including the honest target entries themselves. -/
def FixedHit (initial : HashCache C) (relevant : Query C → Prop)
    (target : Query C → Digest) (cache : HashCache C) : Prop :=
  ∃ input output, cache input = some output ∧ initial input = none ∧
    relevant input ∧ truncateHash output = target input

theorem fixedHit_initial (initial : HashCache C) (relevant : Query C → Prop)
    (target : Query C → Digest) : ¬FixedHit initial relevant target initial := by
  rintro ⟨input, output, hsome, hnone, _⟩
  simp [hnone] at hsome

theorem fixedHit_cacheQuery (initial cache : HashCache C) (relevant : Query C → Prop)
    (target : Query C → Digest) (input : Query C) (output : HashOutput)
    (hnot : ¬FixedHit initial relevant target cache)
    (hnew : FixedHit initial relevant target (cache.cacheQuery input output)) :
    initial input = none ∧ relevant input ∧ truncateHash output = target input := by
  obtain ⟨other, value, hvalue, hnone, hrel, htarget⟩ := hnew
  by_cases heq : other = input
  · subst other
    simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hvalue
    subst value
    exact ⟨hnone, hrel, htarget⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hvalue
    exact False.elim (hnot ⟨other, value, hvalue, hnone, hrel, htarget⟩)

open Classical in
/-- The cache hit indicator has a one-query increment bound, including cache hits. -/
theorem fixedHit_randomOracle_step (initial cache : HashCache C)
    (relevant : Query C → Prop) (target : Query C → Digest) (input : Query C) :
    Pr[fun z => FixedHit initial relevant target z.2 |
      ((Query C →ₒ HashOutput).randomOracle input).run cache] ≤
        (if FixedHit initial relevant target cache then 1 else 0) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  by_cases hbad : FixedHit initial relevant target cache
  · simp only [if_pos hbad]
    exact le_trans probEvent_le_one (le_add_right le_rfl)
  · simp only [if_neg hbad, zero_add]
    cases hc : cache input with
    | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, probEvent_map]
      calc
        _ ≤ Pr[fun output : HashOutput => truncateHash output = target input | $ᵗ HashOutput] :=
          probEvent_mono fun output _ hh =>
            (fixedHit_cacheQuery initial cache relevant target input output hbad hh).2.2
        _ = _ := fixedTargetCharge (target input)
    | some output =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc]
      simp [hbad]

open Classical in
/-- The fixed-target indicator on the logged signing state. -/
def fixedHitPotential (initial : HashCache C) (relevant : Query C → Prop)
    (target : Query C → Digest) (s : LoggedState C) : ℝ≥0∞ :=
  if FixedHit initial relevant target s.1.1 then 1 else 0

open Classical in
theorem fixedHit_loggedStep (initial : HashCache C) (relevant : Query C → Prop)
    (target : Query C → Digest) (t : (WorldSpec C).Domain) (s : LoggedState C)
    (ht : ¬IsProgram t) :
    Pr[fun z => FixedHit initial relevant target z.2.1.1 | (loggedImpl prims t).run s] ≤
      fixedHitPotential initial relevant target s +
        (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    probEvent_map, fixedHitPotential]
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change Pr[fun z => FixedHit initial relevant target z.2 |
        (unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1] ≤ _
    by_cases h : FixedHit initial relevant target s.1.1 <;>
      simp [unifFwdImpl, h, SeedHitProof.signCost]
  · change Pr[fun z => FixedHit initial relevant target z.2 |
        ((Query C →ₒ HashOutput).randomOracle q).run s.1.1] ≤ _
    simpa only [SeedHitProof.signCost, Nat.cast_one, one_mul] using
      fixedHit_randomOracle_step initial s.1.1 relevant target q
  · change Pr[fun z => FixedHit initial relevant target z.2 |
        (prgAnswer prims p).run s.1.1] ≤ _
    simpa [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, bind_pure_comp,
      probEvent_map, SeedHitProof.signCost, Function.comp_def] using
      fixedHit_randomOracle_step initial s.1.1 relevant target (.streamKey p.2.1)
  · exact False.elim (ht (by trivial))
  · change Pr[fun z => FixedHit initial relevant target z.2 |
        (unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1] ≤ _
    by_cases h : FixedHit initial relevant target s.1.1 <;>
      simp [unifFwdImpl, h, SeedHitProof.signCost]
  · change Pr[fun z => FixedHit initial relevant target z.2 |
        ((Query C →ₒ HashOutput).randomOracle q).run s.1.1] ≤ _
    simpa only [SeedHitProof.signCost, Nat.cast_one, one_mul] using
      fixedHit_randomOracle_step initial s.1.1 relevant target q
  · change Pr[fun z => FixedHit initial relevant target z.2 |
        (prgAnswer prims p).run s.1.1] ≤ _
    simpa [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, bind_pure_comp,
      probEvent_map, SeedHitProof.signCost, Function.comp_def] using
      fixedHit_randomOracle_step initial s.1.1 relevant target (.streamKey p.2.1)

open Classical in
theorem fixedHitPotential_step (initial : HashCache C) (relevant : Query C → Prop)
    (target : Query C → Digest) (t : (WorldSpec C).Domain) (s : LoggedState C)
    (ht : ¬IsProgram t) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] *
        fixedHitPotential initial relevant target r.2 ≤
      fixedHitPotential initial relevant target s +
        (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite, fixedHitPotential, mul_ite, mul_one, mul_zero] using
    fixedHit_loggedStep prims initial relevant target t s ht

/-- Fixed targets admit the expected-cost bound over the entire mixed signing
world, including the PRG's internal cache lookup. -/
theorem fixedHit_le_expectedCost {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hnoprog : NoProgramming prims oa) (initial : HashCache C)
    (relevant : Query C → Prop) (target : Query C → Digest) :
    Pr[fun z => FixedHit initial relevant target z.2.1.1 |
      (simulateQ (loggedImpl prims) oa).run ((initial, 0), [])] ≤
      XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹)
        oa ((initial, 0), []) := by
  classical
  let f := fixedHitPotential initial relevant target
  let s : LoggedState C := ((initial, 0), [])
  have hs : ¬Programmed s.2 := by simp [s, Programmed]
  have hzero : guarded f s = 0 := by
    simp [guarded, hs, f, fixedHitPotential, s, fixedHit_initial]
  calc
    _ = XmssSecurity.expectedFinal (loggedImpl prims) (guarded f) oa s := by
      rw [probEvent_eq_tsum_ite, XmssSecurity.expectedFinal]
      apply tsum_congr
      intro z
      by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run s)
      · simp [guarded, hnoprog s hs z hz, f, fixedHitPotential, mul_ite, s]
      · simp [probOutput_eq_zero_of_not_mem_support hz, s]
    _ ≤ guarded f s + XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) oa s := by
      refine XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := fun _ => True)
        (fun _ _ _ _ _ => trivial) _ _ ?_ oa s trivial
      intro t state _
      exact guarded_step prims (fun _ => True) f
        (fun t state _ _ ht => fixedHitPotential_step prims initial relevant target t state ht)
        t state (fun _ => trivial)
    _ = _ := by rw [hzero, zero_add]

/-- Inputs and digests supplied by an honest completion, indexed by candidate. -/
abbrev CompletionTargets (C : Committee) := Query C → Query C × Digest

def CompletedHit (relevant : Query C → Prop) (target : CompletionTargets C)
    (cache : HashCache C) : Prop :=
  ∃ input output, cache input = some output ∧ relevant input ∧
    input ≠ (target input).1 ∧ truncateHash output = (target input).2

theorem completedHit_cacheQuery (relevant : Query C → Prop) (target : CompletionTargets C)
    (cache : HashCache C) (input : Query C) (output : HashOutput)
    (hnot : ¬CompletedHit relevant target cache)
    (hnew : CompletedHit relevant target (cache.cacheQuery input output)) :
    relevant input ∧ input ≠ (target input).1 ∧ truncateHash output = (target input).2 := by
  obtain ⟨other, value, hvalue, hrel, hne, heq⟩ := hnew
  by_cases hi : other = input
  · subst other
    simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hvalue
    subst value
    exact ⟨hrel, hne, heq⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hi] at hvalue
    exact (hnot ⟨other, value, hvalue, hrel, hne, heq⟩).elim

/-- Complete the honest targets without adding its queries to the candidates. -/
def completionPotential (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (cache : HashCache C) : ℝ≥0∞ :=
  Pr[fun z => CompletedHit relevant z.1 cache |
    (simulateQ (Query C →ₒ HashOutput).randomOracle completion).run cache]

theorem completionPotential_empty (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C)) :
    completionPotential relevant completion ∅ = 0 := by
  simp [completionPotential, CompletedHit]

open Classical in
/-- After the completion, a previously uncached candidate either is the honest
input or receives a fresh answer. The completion may choose its targets adaptively. -/
theorem completedHit_afterCompletion (relevant : Query C → Prop) (target : CompletionTargets C)
    (cache completed : HashCache C) (input : Query C)
    (hvisited : relevant input → (completed input).isSome → input = (target input).1) :
    Pr[fun z => CompletedHit relevant target (cache.cacheQuery input z.1) |
      ((Query C →ₒ HashOutput).randomOracle input).run completed] ≤
      (if CompletedHit relevant target cache then 1 else 0) +
        if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hbad : CompletedHit relevant target cache
  · simp only [if_pos hbad]
    exact le_trans probEvent_le_one (le_add_right le_rfl)
  · simp only [if_neg hbad, zero_add]
    by_cases hrel : relevant input
    swap
    · rw [if_neg hrel]
      calc
        _ ≤ Pr[fun _ => False | ((Query C →ₒ HashOutput).randomOracle input).run completed] := by
          apply probEvent_mono
          intro z _ hh
          exact hrel (completedHit_cacheQuery relevant target cache input z.1 hbad hh).1
        _ = 0 := by simp
    rw [if_pos hrel]
    cases hc : completed input with
    | none =>
        rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, probEvent_map]
        calc
          _ ≤ Pr[fun output : HashOutput => truncateHash output = (target input).2 | $ᵗ HashOutput] :=
            probEvent_mono fun output _ hh =>
              (completedHit_cacheQuery relevant target cache input output hbad hh).2.2
          _ = _ := fixedTargetCharge (target input).2
    | some output =>
        rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc]
        have hn : ¬CompletedHit relevant target (cache.cacheQuery input output) := by
          intro hh
          obtain ⟨hrel, hne, _⟩ := completedHit_cacheQuery relevant target cache input output hbad hh
          exact hne (hvisited hrel (by simp [hc]))
        simp [hn]

/-- The completion only reads the distinguished honest input at each relevant
position. This condition allows its target inputs to depend on earlier answers. -/
def CompletionReadsTargets (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C)) : Prop :=
  ∀ cache z, z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle completion).run cache) →
    ∀ input, cache input = none → relevant input → (z.2 input).isSome → input = (z.1 input).1

theorem randomOracle_result_cache (input : Query C) (cache : HashCache C)
    (r : HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle input).run cache)) :
    r.2 = cache.cacheQuery input r.1 := by
  have h := randomOracle_support input cache r hr
  apply funext
  intro q
  by_cases hq : q = input
  · subst q
    simpa using h.2.1
  · simpa [QueryCache.cacheQuery_of_ne _ _ hq] using h.2.2 q hq

open Classical in
/-- Averaging over an honest completion pays each fresh candidate once, even
when the honest input is selected only after the candidate was cached. -/
theorem completionPotential_fresh_step (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (hreads : CompletionReadsTargets relevant completion) (input : Query C) (cache : HashCache C)
    (hfresh : cache input = none) :
    (∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle input).run cache] *
      completionPotential relevant completion r.2) ≤
      completionPotential relevant completion cache +
        if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  classical
  let Q := (Query C →ₒ HashOutput).randomOracle input
  let F := simulateQ (Query C →ₒ HashOutput).randomOracle completion
  let event : (HashOutput × CompletionTargets C) × HashCache C → Prop :=
    fun z => CompletedHit relevant z.1.2 (cache.cacheQuery input z.1.1)
  have hcomm : Commutes Q F := by
    simpa [Q, F] using commutes_simulateQ (Query C →ₒ HashOutput).randomOracle
      commutes_randomOracle_randomOracle
      (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input)) completion
  have hforward : (∑' r, Pr[= r | Q.run cache] * completionPotential relevant completion r.2) =
      Pr[event | (do let u ← Q; let targets ← F; pure (u, targets)).run cache] := by
    simp only [StateT.run_bind, StateT.run_pure, bind_pure_comp,
      probEvent_bind_eq_tsum, probEvent_map]
    apply tsum_congr
    intro r
    by_cases hr : r ∈ support (Q.run cache)
    · have hc := randomOracle_result_cache input cache r hr
      simp only [completionPotential, F, event, hc, StateT.run_map, probEvent_map, Function.comp_def]
    · simp [probOutput_eq_zero_of_not_mem_support hr]
  rw [hforward, probEvent_congr' (fun _ _ => Iff.rfl) (hcomm cache)]
  simp only [StateT.run_bind, StateT.run_pure, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map]
  calc
    _ ≤ ∑' r, Pr[= r | F.run cache] *
        ((if CompletedHit relevant r.1 cache then 1 else 0) +
          if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) := by
      apply ENNReal.tsum_le_tsum
      intro r
      by_cases hr : r ∈ support (F.run cache)
      · apply mul_le_mul_left'
        simp only [StateT.run_map, probEvent_map]
        change Pr[fun z => CompletedHit relevant r.1 (cache.cacheQuery input z.1) | Q.run r.2] ≤ _
        exact completedHit_afterCompletion relevant r.1 cache r.2 input
          (hreads cache r hr input hfresh)
      · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ = completionPotential relevant completion cache +
        (∑' r, Pr[= r | F.run cache]) *
          (if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      congr 1
      simp [completionPotential, F, probEvent_eq_tsum_ite, mul_ite]
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [one_mul] using
        mul_le_mul_right' (tsum_probOutput_le_one (mx := F.run cache))
          (if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0)

open Classical in
theorem completionPotential_randomOracle_step (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (hreads : CompletionReadsTargets relevant completion) (input : Query C) (cache : HashCache C) :
    (∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle input).run cache] *
      completionPotential relevant completion r.2) ≤
      completionPotential relevant completion cache +
        if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  cases hc : cache input with
  | none => exact completionPotential_fresh_step relevant completion hreads input cache hc
  | some output =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, tsum_probOutput_pure_mul]
      exact le_add_right le_rfl

/-- One candidate's reserve before the honest query, and its collision indicator
afterwards. The candidate pays once, whichever input is queried first. -/
def pairPotential (honest candidate : Query C) (cache : HashCache C) : ℝ≥0∞ :=
  match cache candidate with
  | none => 0
  | some output => match cache honest with
    | none => (2 ^ 128 : ℝ≥0∞)⁻¹
    | some value => if truncateHash output = truncateHash value then 1 else 0

theorem pairPotential_freshStep (honest candidate input : Query C)
    (hne : candidate ≠ honest) (cache : HashCache C) (hfresh : cache input = none) :
    ∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
        pairPotential honest candidate (cache.cacheQuery input output) =
      pairPotential honest candidate cache +
        (if input = candidate then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) := by
  classical
  by_cases hcandidate : input = candidate
  · subst input
    cases hh : cache honest with
    | none =>
      simp only [pairPotential, QueryCache.cacheQuery_self,
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne), hh, hfresh, ↓reduceIte, zero_add]
      exact tsum_probOutput_mul_of_const_on_support _ (fun _ _ => rfl) (by simp)
    | some value =>
      simp only [pairPotential, QueryCache.cacheQuery_self,
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne), hh, hfresh, ↓reduceIte, zero_add,
        mul_ite, mul_one, mul_zero]
      rw [← probEvent_eq_tsum_ite]
      exact fixedTargetCharge (truncateHash value)
  · by_cases hhonest : input = honest
    · subst input
      cases hc : cache candidate with
      | none =>
        simp [pairPotential, QueryCache.cacheQuery_of_ne _ _ hne, hc, hcandidate]
      | some value =>
        simp only [pairPotential, QueryCache.cacheQuery_self,
          QueryCache.cacheQuery_of_ne _ _ hne, hc, hfresh, if_neg hcandidate, add_zero,
          mul_ite, mul_one, mul_zero]
        rw [← probEvent_eq_tsum_ite]
        simpa only [eq_comm] using fixedTargetCharge (truncateHash value)
    · simp only [pairPotential, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hcandidate),
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm hhonest), if_neg hcandidate, add_zero]
      exact tsum_probOutput_mul_of_const_on_support _ (fun _ _ => rfl) (by simp)

theorem pairPotential_randomOracle_step (honest candidate input : Query C)
    (hne : candidate ≠ honest) (cache : HashCache C) :
    ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle input).run cache] *
        pairPotential honest candidate r.2 =
      pairPotential honest candidate cache +
        (if cache input = none ∧ input = candidate then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) := by
  classical
  cases hc : cache input with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc,
      tsum_probOutput_map_mul]
    change (∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
      pairPotential honest candidate (cache.cacheQuery input output)) = _
    simpa only [hc, true_and] using pairPotential_freshStep honest candidate input hne cache hc
  | some output =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc,
      tsum_probOutput_pure_mul]
    simp

/-- A finite family of pairs, indexed by candidate input so no query pays twice. -/
def fixedPairPotential (candidates : Finset (Query C)) (honest : Query C → Query C)
    (cache : HashCache C) : ℝ≥0∞ :=
  ∑ candidate ∈ candidates, pairPotential (honest candidate) candidate cache

theorem fixedPairPotential_randomOracle_step (candidates : Finset (Query C))
    (honest : Query C → Query C) (hne : ∀ c ∈ candidates, c ≠ honest c)
    (input : Query C) (cache : HashCache C) :
    ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle input).run cache] *
        fixedPairPotential candidates honest r.2 =
      fixedPairPotential candidates honest cache +
        (if cache input = none ∧ input ∈ candidates then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) := by
  classical
  simp only [fixedPairPotential, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  trans ∑ c ∈ candidates, (pairPotential (honest c) c cache +
    if cache input = none ∧ input = c then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0)
  · apply Finset.sum_congr rfl
    intro c hc
    exact pairPotential_randomOracle_step (honest c) c input (hne c hc) cache
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases hc : cache input = none
  · simp [hc]
  · simp [hc]

theorem fixedPairPotential_empty (candidates : Finset (Query C))
    (honest : Query C → Query C) : fixedPairPotential candidates honest ∅ = 0 := by
  simp [fixedPairPotential, pairPotential]

theorem fixedPairPotential_of_hit (candidates : Finset (Query C))
    (honest : Query C → Query C) (cache : HashCache C) (candidate : Query C)
    (hc : candidate ∈ candidates) (output value : HashOutput)
    (houtput : cache candidate = some output) (hvalue : cache (honest candidate) = some value)
    (heq : truncateHash output = truncateHash value) :
    1 ≤ fixedPairPotential candidates honest cache := by
  have hpair : pairPotential (honest candidate) candidate cache = 1 := by
    simp [pairPotential, houtput, hvalue, heq]
  rw [← hpair]
  exact Finset.single_le_sum (f := fun c => pairPotential (honest c) c cache)
    (fun _ _ => zero_le) hc

/-- Lift a cache potential through both copies of the local signing oracle. -/
theorem cachePotential_loggedStep (f : HashCache C → ℝ≥0∞)
    (hhash : ∀ input cache,
      ∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle input).run cache] * f r.2 ≤
        f cache + (2 ^ 128 : ℝ≥0∞)⁻¹)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ht : ¬IsProgram t) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] * f r.2.1.1 ≤
      f s.1.1 + (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    tsum_probOutput_map_mul]
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change (∑' r, Pr[= r | (unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1] * f r.2) ≤ _
    simp [unifFwdImpl, SeedHitProof.signCost, tsum_probOutput_map_mul, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]
  · change (∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle q).run s.1.1] * f r.2) ≤ _
    simpa only [SeedHitProof.signCost, Nat.cast_one, one_mul] using hhash q s.1.1
  · change (∑' r, Pr[= r | (prgAnswer prims p).run s.1.1] * f r.2) ≤ _
    simpa [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, bind_pure_comp,
      tsum_probOutput_map_mul, SeedHitProof.signCost] using hhash (.streamKey p.2.1) s.1.1
  · exact False.elim (ht (by trivial))
  · change (∑' r, Pr[= r | (unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1] * f r.2) ≤ _
    simp [unifFwdImpl, SeedHitProof.signCost, tsum_probOutput_map_mul, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]
  · change (∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle q).run s.1.1] * f r.2) ≤ _
    simpa only [SeedHitProof.signCost, Nat.cast_one, one_mul] using hhash q s.1.1
  · change (∑' r, Pr[= r | (prgAnswer prims p).run s.1.1] * f r.2) ≤ _
    simpa [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, bind_pure_comp,
      tsum_probOutput_map_mul, SeedHitProof.signCost] using hhash (.streamKey p.2.1) s.1.1

theorem completionPotential_loggedStep (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (hreads : CompletionReadsTargets relevant completion)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ht : ¬IsProgram t) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] *
      completionPotential relevant completion r.2.1.1) ≤
      completionPotential relevant completion s.1.1 +
        (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  apply cachePotential_loggedStep prims (completionPotential relevant completion) _ t s ht
  intro input cache
  apply (completionPotential_randomOracle_step relevant completion hreads input cache).trans
  split_ifs <;> simp

open Classical in
theorem completionPotential_freeHash_step (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (hreads : CompletionReadsTargets relevant completion) (input : Query C) (s : LoggedState C) :
    (∑' r, Pr[= r | (loggedImpl prims (.inr (.inr (.inl input)))).run s] *
      completionPotential relevant completion r.2.1.1) ≤
      completionPotential relevant completion s.1.1 +
        if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    tsum_probOutput_map_mul]
  change (∑' r, Pr[= r | ((Query C →ₒ HashOutput).randomOracle input).run s.1.1] *
    completionPotential relevant completion r.2) ≤ _
  exact completionPotential_randomOracle_step relevant completion hreads input s.1.1

theorem completionPotential_terminal (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C)) (cache : HashCache C)
    (hstable : ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle completion).run cache),
      CompletedHit relevant z.1 cache) : completionPotential relevant completion cache = 1 := by
  exact probEvent_eq_one ⟨by simp, hstable⟩

theorem fixedPairPotential_loggedStep (candidates : Finset (Query C))
    (honest : Query C → Query C) (hne : ∀ c ∈ candidates, c ≠ honest c)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ht : ¬IsProgram t) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] *
        fixedPairPotential candidates honest r.2.1.1 ≤
      fixedPairPotential candidates honest s.1.1 +
        (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply cachePotential_loggedStep prims (fixedPairPotential candidates honest) _ t s ht
  intro input cache
  rw [fixedPairPotential_randomOracle_step candidates honest hne input cache]
  split_ifs
  · exact le_rfl
  · gcongr
    exact zero_le

/-- Expected-cost accounting for fixed input pairs in either query order. -/
theorem fixedPairHits_le_expectedCost {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hnoprog : NoProgramming prims oa) (candidates : Finset (Query C))
    (honest : Query C → Query C) (hne : ∀ c ∈ candidates, c ≠ honest c) :
    Pr[fun z => ∃ c ∈ candidates, ∃ output value,
      z.2.1.1 c = some output ∧ z.2.1.1 (honest c) = some value ∧
        truncateHash output = truncateHash value |
      (simulateQ (loggedImpl prims) oa).run loggedInit] ≤
      XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹)
        oa loggedInit := by
  classical
  let f : LoggedState C → ℝ≥0∞ := fun s => fixedPairPotential candidates honest s.1.1
  have hs : ¬Programmed (loggedInit (C := C)).2 := by simp [loggedInit, Programmed]
  have hzero : guarded f loggedInit = 0 := by
    simp [guarded, f, loggedInit, fixedPairPotential_empty]
  calc
    _ ≤ XmssSecurity.expectedFinal (loggedImpl prims) (guarded f) oa loggedInit := by
      rw [probEvent_eq_tsum_ite, XmssSecurity.expectedFinal]
      apply ENNReal.tsum_le_tsum
      intro z
      split_ifs with hhit
      · by_cases hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run loggedInit)
        · rw [guarded, if_neg (hnoprog loggedInit hs z hz)]
          obtain ⟨c, hc, output, value, houtput, hvalue, heq⟩ := hhit
          calc
            _ = Pr[= z | (simulateQ (loggedImpl prims) oa).run loggedInit] * 1 := (mul_one _).symm
            _ ≤ _ := by
              gcongr
              exact fixedPairPotential_of_hit candidates honest z.2.1.1 c hc
                output value houtput hvalue heq
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul]
      · exact zero_le
    _ ≤ guarded f loggedInit + XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) oa loggedInit := by
      refine XmssSecurity.expectedFinal_le (loggedImpl prims) (Inv := fun _ => True)
        (fun _ _ _ _ _ => trivial) _ _ ?_ oa loggedInit trivial
      intro t state _
      exact guarded_step prims (fun _ => True) f
        (fun t state _ _ ht => fixedPairPotential_loggedStep prims candidates honest hne t state ht)
        t state (fun _ => trivial)
    _ = _ := by rw [hzero, zero_add]

/-- A valid codeword needs at least 23 chain values strictly below the public
endpoint. This is the quantitative form needed for an unopened top key. -/
theorem valid_encoding_short_chains (encoding : XmssSecurity.Encoding)
    (hvalid : XmssSecurity.TargetSum.Valid encoding) :
    23 ≤ (Finset.univ.filter fun l => (encoding l).val < 3).card := by
  classical
  have hle (l : XmssSecurity.ChainIndex) : (encoding l).val ≤ 3 := by
    have h := (encoding l).isLt
    norm_num [XmssSecurity.chainLength, XmssSecurity.winternitzBits] at h
    omega
  have hsum : (∑ l, (encoding l).val) = 106 := by
    simpa only [XmssSecurity.TargetSum.Valid, XmssSecurity.TargetSum.sum,
      XmssSecurity.targetSum] using hvalid
  have hdeficit : (∑ l, (3 - (encoding l).val)) = 68 := by
    have htotal : (∑ l, (3 - (encoding l).val)) + (∑ l, (encoding l).val) = 174 := by
      rw [← Finset.sum_add_distrib]
      simp [Nat.sub_add_cancel (hle _), XmssSecurity.numChains]
    omega
  have hbound : (∑ l, (3 - (encoding l).val)) ≤
      ∑ l : XmssSecurity.ChainIndex, if (encoding l).val < 3 then 3 else 0 := by
    apply Finset.sum_le_sum
    intro l _
    split_ifs with hl <;> omega
  have hcount : (∑ l : XmssSecurity.ChainIndex, if (encoding l).val < 3 then 3 else 0) =
      (Finset.univ.filter fun l => (encoding l).val < 3).card * 3 := by
    rw [← Finset.sum_filter]
    simp
  rw [hdeficit, hcount] at hbound
  omega

open SigningDescentProof in
/-- Root agreement without an output hit requires authentic values at at least
23 distinct chain indices below their endpoints. Hiddenness is a separate condition. -/
theorem fresh_layer_many_guesses
    (step : XmssSecurity.ChainIndex → ℕ → XmssSecurity.Digest → XmssSecurity.Digest)
    (leafHash : (XmssSecurity.ChainIndex → XmssSecurity.Digest) → XmssSecurity.Digest)
    (nodeHash : ℕ → XmssSecurity.Digest → XmssSecurity.Digest → XmssSecurity.Digest)
    (secret : XmssSecurity.ChainIndex → XmssSecurity.Digest) (path : ℕ → XmssSecurity.Digest)
    (stepCached : XmssSecurity.ChainIndex → ℕ → XmssSecurity.Digest → Prop)
    (leafCached : (XmssSecurity.ChainIndex → XmssSecurity.Digest) → Prop)
    (nodeCached : ℕ → XmssSecurity.Digest → XmssSecurity.Digest → Prop)
    (encoding : XmssSecurity.Encoding) (hvalid : XmssSecurity.TargetSum.Valid encoding)
    (value : XmssSecurity.ChainIndex → XmssSecurity.Digest) (forgedPath : ℕ → XmssSecurity.Digest)
    (hroot : XmssSecurity.Merkle.ascend nodeHash forgedPath 0 XmssSecurity.treeHeight
        (leafHash (XmssSecurity.recoveredEndpoints step encoding value)) =
      XmssSecurity.Merkle.ascend nodeHash path 0 XmssSecurity.treeHeight
        (leafHash (honestEnds step secret)))
    (hcached : LayerCached step leafHash nodeHash stepCached leafCached nodeCached encoding value forgedPath) :
    LayerHit step leafHash nodeHash secret path stepCached leafCached nodeCached ∨
      ∃ chains : Finset XmssSecurity.ChainIndex, 23 ≤ chains.card ∧
        ∀ l ∈ chains, (encoding l).val < 3 ∧ value l = honestValue step secret l (encoding l).val := by
  classical
  by_cases hhit : LayerHit step leafHash nodeHash secret path stepCached leafCached nodeCached
  · exact Or.inl hhit
  apply Or.inr
  have hends : XmssSecurity.recoveredEndpoints step encoding value = honestEnds step secret := by
    rcases XmssSecurity.Merkle.sameXmssPath_or_hasCollision nodeHash forgedPath path _ _ hroot with
      ⟨hleaf, -⟩ | ⟨level, hne, heq⟩
    · rcases XmssSecurity.Wots.eq_or_hasLeafCollision leafHash _ _ hleaf with h | ⟨hne, heq⟩
      · exact h
      · exact False.elim (hhit (Or.inr (Or.inl ⟨_, hcached.2.1, hne, heq⟩)))
    · exact False.elim (hhit (Or.inr (Or.inr
        ⟨level.val, level.isLt, _, _, hcached.2.2 _ level.isLt, hne, heq⟩)))
  refine ⟨Finset.univ.filter (fun l => (encoding l).val < 3),
    valid_encoding_short_chains encoding hvalid, ?_⟩
  intro l hl
  refine ⟨(Finset.mem_filter.mp hl).2, ?_⟩
  exact (guess_or_hit_of_end step leafHash nodeHash secret path stepCached leafCached nodeCached l
    (encoding l) (value l) (congrFun hends l) (hcached.1 l)).resolve_right hhit

set_option maxRecDepth 100000 in
/-- Assembly of a completion potential and a rare-event reserve. The hypotheses
separate the concrete forest proof from the unopened-key probability bound. -/
theorem isHitPotential_of_completion (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (hreads : CompletionReadsTargets relevant completion) (firstInput : Query C)
    (hirrelevant : ¬relevant firstInput)
    (k : HashOutput → OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)))
    (hfirst : SigningDescentProof.finalRun A x =
      query (spec := WorldSpec C) (.inr (.inr (.inl firstInput))) >>= k)
    (exception : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C) → Prop)
    (hrare : Pr[exception | loggedRun prims A x] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹)
    (hcover : ∀ z ∈ support (loggedRun prims A x), WinHit prims x (z.1, z.2.1) →
      (∀ r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle completion).run z.2.1.1),
        CompletedHit relevant r.1 z.2.1.1) ∨ exception z) :
    ∃ Inv f, IsHitPotential prims A x Inv f := by
  classical
  let first : (WorldSpec C).Domain := .inr (.inr (.inl firstInput))
  let main : OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) :=
    query first >>= k
  let g := completionPotential relevant completion
  let f : LoggedState C → ℝ≥0∞ := fun s => g s.1.1 + fundedContinuation prims main exception s
  refine ⟨fun s => s.2 = [] → s = loggedInit, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rfl
  · simp [f, g, fundedContinuation, loggedInit, completionPotential_empty]
  · intro t s _ _ r hr
    exact initialLogInvariant_step prims t s r hr
  · intro t s hs _ ht
    change (∑' r, Pr[= r | (loggedImpl prims t).run s] *
      (g r.2.1.1 + fundedContinuation prims main exception r.2)) ≤ _
    simp_rw [mul_add]
    rw [ENNReal.tsum_add]
    have hfund := fundedContinuation_step prims first k exception (2 ^ 128 : ℝ≥0∞)⁻¹
      (by simpa only [loggedRun, hfirst, first, loggedInit] using hrare) t s hs
    have hg := completionPotential_loggedStep prims relevant completion hreads t s ht
    letI : Decidable (s.2 = [] ∧ t = first) := Classical.propDecidable _
    by_cases hspecial : s.2 = [] ∧ t = first
    · obtain ⟨hnil, rfl⟩ := hspecial
      have hgzero := completionPotential_freeHash_step prims relevant completion hreads firstInput s
      simp only [if_neg hirrelevant, add_zero] at hgzero
      have hf : (∑' r, Pr[= r | (loggedImpl prims first).run s] *
          fundedContinuation prims main exception r.2) ≤
          fundedContinuation prims main exception s + (2 ^ 128 : ℝ≥0∞)⁻¹ := by
        simpa only [hnil, and_self, if_pos, main] using hfund
      calc
        _ ≤ g s.1.1 + (fundedContinuation prims main exception s + (2 ^ 128 : ℝ≥0∞)⁻¹) :=
          add_le_add hgzero hf
        _ = _ := by simp [f, first, SeedHitProof.signCost, add_assoc]
    · have hf : (∑' r, Pr[= r | (loggedImpl prims t).run s] *
          fundedContinuation prims main exception r.2) ≤ fundedContinuation prims main exception s := by
        simpa only [if_neg hspecial, add_zero, main] using hfund
      calc
        _ ≤ (g s.1.1 + (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) +
            fundedContinuation prims main exception s := add_le_add hg hf
        _ = _ := by dsimp [f]; ac_rfl
  · intro z hz hwin
    rcases hcover z hz hwin with hstable | hexception
    · have hg := completionPotential_terminal relevant completion z.2.1.1 hstable
      change 1 ≤ completionPotential relevant completion z.2.1.1 + _
      rw [hg]
      exact le_add_right le_rfl
    · have hf := fundedContinuation_terminal prims first k exception z
        (by simpa only [loggedRun, hfirst, first, loggedInit] using hz) hexception
      change 1 ≤ g z.2.1.1 + fundedContinuation prims main exception z.2
      rw [hf]
      exact le_add_left le_rfl

end SigningHitProof

set_option maxRecDepth 100000 in
/-- No outcome of the signing run logs a programming query. -/
theorem noProgramQuery (prims : Primitives) (C : Committee) : NoProgramQuery prims C := by
  intro A x z hz
  exact SigningHitProof.noProgramming_finalRun prims A x loggedInit
    (by simp [loggedInit, Programmed]) z hz

/-
Remaining obligation: SigningHitLaneProof.HitPotential prims C.
For every admissible A, q and x, construct Inv and f with:
  Inv loggedInit; f loggedInit = 0;
  preservation under every non-programming loggedImpl step;
  expected increment at most signCost t / 2^128;
  1 ≤ f z.2 for every supported terminal WinHit outcome.

Routes checked, without a complete invariant:
* A hit indicator alone does not account for the default-zero answers of uncached
  honest inputs. The terminal condition must use WinHit.
* fixedHit_le_expectedCost proves the fixed-target bound for the complete mixed
  signing oracle. Extracting the top targets from the key-generation prefix and
  proving their stability still has to be connected to this bound.
* fixedPairHits_le_expectedCost charges fixed input pairs once, in either query
  order. Its target-input map must be fixed before the run. Substituting the final
  cache-dependent honest-input map is not justified by that theorem.
* Eager completion could average the pair potential over the unqueried honest
  inputs. Its terminal condition still needs a win-aware argument: a default-zero
  bottom hit can disappear on completion, while a rare top guess authenticates
  the forgery. A bound for genuine completed-tree hits alone is insufficient.
* Counting all pairs at a position gives a quadratic bound, which does not imply
  the required one-unit-per-query bound.
* fundedContinuation_step now discharges the universal raw-query condition for
  a continuation reserve. The complete log determines the residual computation;
  mismatching queries leave it forever. An exceptional-event probability at most
  2^-128 can be paid by the first counted query, with no later charge. The
  actual-game exceptional-event bound and its combination with a collision
  potential that leaves this first charge unused remain open.
* fresh_layer_many_guesses proves the quantitative descent needed for unopened
  top keys: no output hit forces authentic values at at least 23 short chains.
  It does not assert that those values are hidden. An accounting proof must track
  disclosure, and must preserve the reserve for prequeries when a tree is opened.
  A fractional count of guesses and hits does not establish this transition.

No counterexample to HitLaneBound is established here. The hypothesis below is
explicitly open; the conditional theorem is not a closure of the hit lane.
-/

/-- The final assembly, conditional on the remaining hit-potential obligation. -/
theorem hitLaneBoundClosed (prims : Primitives) (C : Committee)
    (hitPotential : HitPotential prims C) : HitLaneBound prims C :=
  hitLaneBound prims C hitPotential (noProgramQuery prims C)

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fixedHit_le_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fixedHit_le_expectedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fundedContinuation_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fundedContinuation_step

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fundedContinuation_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fundedContinuation_terminal

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fixedPairHits_le_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fixedPairHits_le_expectedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fresh_layer_many_guesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fresh_layer_many_guesses

/-- info: 'ThresholdLeanXmssSecurity.noProgramQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noProgramQuery

/-- info: 'ThresholdLeanXmssSecurity.hitLaneBoundClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hitLaneBoundClosed

end ThresholdLeanXmssSecurity
