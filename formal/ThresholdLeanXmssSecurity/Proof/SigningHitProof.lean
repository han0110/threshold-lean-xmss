import ThresholdLeanXmssSecurity.Proof.SigningHitLane
import ThresholdLeanXmssSecurity.Proof.Tree
import XmssSecurity.Proof.TopKeygenQueryBound
import XmssSecurity.Proof.MerkleQueryBound
import XmssSecurity.Proof.TopStructural

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

/-- A raw query different from the next program query kills the residual. -/
theorem transcriptResidual_wrongQuery {α : Type} (oa : OracleComp (WorldSpec C) α)
    (log : QueryLog (WorldSpec C)) (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t)
    (h : ¬∃ k, transcriptResidual oa log = some (OracleComp.queryBind t k)) :
    transcriptResidual oa (log.logQuery t u) = none := by
  classical
  rw [transcriptResidual_append]
  cases hp : transcriptResidual oa log with
  | none => rfl
  | some rest =>
    cases rest with
    | pure a => rfl
    | queryBind t' k =>
      have ht : t ≠ t' := by
        intro he
        subst t'
        exact h ⟨k, hp⟩
      simp [transcriptNext, ht]

theorem continuationReserve_wrongQuery {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (t : (WorldSpec C).Domain) (s : LoggedState C)
    (h : ¬∃ k, transcriptResidual oa s.2 = some (OracleComp.queryBind t k)) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] * continuationReserve prims oa event r.2) = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support ((loggedImpl prims t).run s)
  · simp [continuationReserve, loggedImpl_log prims t s r hr,
      transcriptResidual_wrongQuery oa s.2 t r.1 h]
  · simp [probOutput_eq_zero_of_not_mem_support hr]

/-- At a matching gate the reserve's next expectation is exactly the
conditional event probability from that actual residual program. -/
theorem continuationReserve_matchingQuery {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (t : (WorldSpec C).Domain) (s : LoggedState C)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α)
    (h : transcriptResidual oa s.2 = some (OracleComp.queryBind t k)) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] * continuationReserve prims oa event r.2) =
      Pr[event | (simulateQ (loggedImpl prims) (OracleComp.queryBind t k)).run s] := by
  classical
  change _ = Pr[event | (simulateQ (loggedImpl prims) (query t >>= k)).run s]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro r
  by_cases hr : r ∈ support ((loggedImpl prims t).run s)
  · simp [continuationReserve, loggedImpl_log prims t s r hr,
      transcriptResidual_append, h, transcriptNext]
  · simp [probOutput_eq_zero_of_not_mem_support hr]

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

/-- Reachability includes arbitrary supported nonprogramming calls. In
particular, a matching program prefix cannot hide extra unlogged cache entries. -/
inductive RawReachable : LoggedState C → Prop
  | initial : RawReachable loggedInit
  | step (t : (WorldSpec C).Domain) (s : LoggedState C)
      (hs : RawReachable s) (ht : ¬IsProgram t)
      (r : (WorldSpec C).Range t × LoggedState C)
      (hr : r ∈ support ((loggedImpl prims t).run s)) : RawReachable r.2

/-- Execute at most `n` queries, returning the unexecuted program. -/
def prefixRun {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ℕ → OracleComp (WorldSpec C) (OracleComp (WorldSpec C) α)
  | 0 => pure oa
  | n + 1 => match oa with
    | .pure a => pure (pure a)
    | .queryBind t k => query t >>= fun answer => prefixRun (k answer) n

theorem prefixRun_succ {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ) :
    prefixRun oa (n + 1) = prefixRun oa n >>= fun rest => prefixRun rest 1 := by
  induction n generalizing oa with
  | zero => simp [prefixRun]
  | succ n ih =>
    cases oa with
    | pure a => rfl
    | queryBind t k => simp only [prefixRun, ih, bind_assoc]

theorem prefixRun_resume {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ) :
    (prefixRun oa n >>= id) = oa := by
  induction n generalizing oa with
  | zero => simp [prefixRun]
  | succ n ih =>
    cases oa with
    | pure a => rfl
    | queryBind t k => simpa only [prefixRun, bind_assoc, ih] using
        (show (query t >>= k) = OracleComp.queryBind t k from rfl)

/-- Prefix execution commutes with changing only the final return value. -/
theorem prefixRun_map {α β : Type} (f : α → β) (oa : OracleComp (WorldSpec C) α) (n : ℕ) :
    prefixRun (f <$> oa) n = (fun rest => f <$> rest) <$> prefixRun oa n := by
  induction n generalizing oa with
  | zero => simp [prefixRun]
  | succ n ih =>
    cases oa with
    | pure a =>
      rfl
    | queryBind t k =>
      change prefixRun (OracleComp.queryBind t (fun u => f <$> k u)) (n + 1) = _
      simp [prefixRun, map_bind, ih]

/-- Every continuation of a supported prefix is a supported full execution.
The game's worst-case count bound therefore also applies after conditioning. -/
theorem prefixRun_support_resume {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (rest : OracleComp (WorldSpec C) α) (s : LoggedState C)
    (hp : (rest, s) ∈ support ((simulateQ (loggedImpl prims) (prefixRun oa n)).run loggedInit))
    (z : α × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) rest).run s)) :
    z ∈ support ((simulateQ (loggedImpl prims) oa).run loggedInit) := by
  rw [← prefixRun_resume oa n, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨(rest, s), hp, hz⟩

/-- A raw transcript that still matches the program is a supported actual
prefix. Thus its cache cannot contain extra data absent from that prefix. -/
theorem rawReachable_prefix {α : Type} (s : LoggedState C) (hs : RawReachable prims s) :
    ∀ (oa rest : OracleComp (WorldSpec C) α), transcriptResidual oa s.2 = some rest →
      ∃ n, (rest, s) ∈ support ((simulateQ (loggedImpl prims) (prefixRun oa n)).run loggedInit) := by
  induction hs with
  | initial =>
    intro oa rest h
    have he : oa = rest := Option.some.inj h
    subst rest
    exact ⟨0, by simp [prefixRun]⟩
  | step t s hs ht r hr ih =>
    intro oa rest h
    rw [loggedImpl_log prims t s r hr, transcriptResidual_append] at h
    cases hp : transcriptResidual oa s.2 with
    | none => simp [hp] at h
    | some prev =>
      rw [hp, Option.bind_some] at h
      obtain ⟨n, hn⟩ := ih oa prev hp
      cases prev with
      | pure a => simp [transcriptNext] at h
      | queryBind u k =>
        by_cases he : t = u
        · subst u
          simp only [transcriptNext, ↓reduceDIte, Option.some.injEq] at h
          subst rest
          refine ⟨n + 1, ?_⟩
          rw [prefixRun_succ, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
          refine ⟨(OracleComp.queryBind t k, s), hn, ?_⟩
          simp only [prefixRun, query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            mem_support_bind_iff]
          exact ⟨r, hr, by simp⟩
        · simp [transcriptNext, he] at h

/-- A gate is one concrete oracle input, independent of the final forgery. -/
def GateSeen (gate : (WorldSpec C).Domain) (log : QueryLog (WorldSpec C)) : Prop :=
  ∃ entry ∈ log, entry.1 = gate

theorem gateSeen_logQuery (gate t : (WorldSpec C).Domain)
    (u : (WorldSpec C).Range t) (log : QueryLog (WorldSpec C)) :
    GateSeen gate (log.logQuery t u) ↔ GateSeen gate log ∨ t = gate := by
  simp [GateSeen, QueryLog.logQuery, QueryLog.singleton, or_and_right, exists_or]

/-- Pay a key's reserve at its first designated PRF query. After activation it
is a continuation probability; a transcript mismatch makes it zero. -/
def gatedContinuation {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (gate : (WorldSpec C).Domain)
    (s : LoggedState C) : ℝ≥0∞ :=
  open Classical in if GateSeen gate s.2 then continuationReserve prims oa event s else 0

open Classical in
theorem gatedContinuation_next {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (gate t : (WorldSpec C).Domain)
    (s : LoggedState C) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] * gatedContinuation prims oa event gate r.2) =
      if GateSeen gate s.2 ∨ t = gate then
        ∑' r, Pr[= r | (loggedImpl prims t).run s] * continuationReserve prims oa event r.2
      else 0 := by
  classical
  split_ifs with h
  · apply tsum_congr
    intro r
    by_cases hr : r ∈ support ((loggedImpl prims t).run s)
    · simp [gatedContinuation, loggedImpl_log prims t s r hr, gateSeen_logQuery, h]
    · simp [probOutput_eq_zero_of_not_mem_support hr]
  · apply ENNReal.tsum_eq_zero.mpr
    intro r
    by_cases hr : r ∈ support ((loggedImpl prims t).run s)
    · simp [gatedContinuation, loggedImpl_log prims t s r hr, gateSeen_logQuery, h]
    · simp [probOutput_eq_zero_of_not_mem_support hr]

open Classical in
/-- A conditional bound is needed only immediately before the gate opens. -/
theorem gatedContinuation_step {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (gate t : (WorldSpec C).Domain)
    (s : LoggedState C) (ε : ℝ≥0∞)
    (hgate : ¬GateSeen gate s.2 → t = gate →
      (∑' r, Pr[= r | (loggedImpl prims t).run s] * continuationReserve prims oa event r.2) ≤ ε) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] * gatedContinuation prims oa event gate r.2) ≤
      gatedContinuation prims oa event gate s +
        if ¬GateSeen gate s.2 ∧ t = gate then ε else 0 := by
  classical
  rw [gatedContinuation_next]
  by_cases hseen : GateSeen gate s.2
  · simpa [gatedContinuation, hseen] using continuationReserve_step prims oa event t s
  · by_cases ht : t = gate
    · simpa [gatedContinuation, hseen, ht] using hgate hseen ht
    · simp [gatedContinuation, hseen, ht]

theorem gatedContinuation_terminal {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (gate : (WorldSpec C).Domain)
    (z : α × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run loggedInit))
    (he : event z) (hseen : GateSeen gate z.2.2) :
    gatedContinuation prims oa event gate z.2 = 1 := by
  classical
  rw [gatedContinuation, if_pos hseen]
  exact continuationReserve_terminal prims oa event z hz he

open Classical in
/-- Injective gates activate at most one key's reserve per oracle call. -/
theorem gatedContinuation_sum_step {ι α : Type} [Fintype ι]
    (oa : OracleComp (WorldSpec C) α) (event : ι → α × LoggedState C → Prop)
    (gate : ι → (WorldSpec C).Domain) (hinj : Function.Injective gate)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ε : ℝ≥0∞)
    (hgate : ∀ i, ¬GateSeen (gate i) s.2 → t = gate i →
      (∑' r, Pr[= r | (loggedImpl prims t).run s] * continuationReserve prims oa (event i) r.2) ≤ ε) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] *
      ∑ i, gatedContinuation prims oa (event i) (gate i) r.2) ≤
      (∑ i, gatedContinuation prims oa (event i) (gate i) s) +
        if ∃ i, t = gate i then ε else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc
    _ ≤ ∑ i, (gatedContinuation prims oa (event i) (gate i) s +
        if ¬GateSeen (gate i) s.2 ∧ t = gate i then ε else 0) :=
      Finset.sum_le_sum fun i _ => gatedContinuation_step prims oa (event i) (gate i) t s ε (hgate i)
    _ = _ + ∑ i, if ¬GateSeen (gate i) s.2 ∧ t = gate i then ε else 0 := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add le_rfl
      by_cases hex : ∃ i, t = gate i
      · obtain ⟨i, hi⟩ := hex
        rw [if_pos ⟨i, hi⟩, Finset.sum_eq_single i]
        · split_ifs <;> simp
        · intro j _ hji
          have hne : t ≠ gate j := fun h => hji (hinj (h.symm.trans hi))
          simp [hne]
        · simp
      · have hn : ∀ i, t ≠ gate i := by simpa using hex
        simp [hex, hn]

/-- Universal raw-state gate bounds reduce to supported matching prefixes.
Mismatched raw queries contribute exactly zero. -/
theorem gate_bound_of_prefix {α : Type} (oa : OracleComp (WorldSpec C) α)
    (event : α × LoggedState C → Prop) (gate : (WorldSpec C).Domain) (ε : ℝ≥0∞)
    (hprefix : ∀ (n : ℕ) (s : LoggedState C)
      (k : (WorldSpec C).Range gate → OracleComp (WorldSpec C) α),
      (OracleComp.queryBind gate k, s) ∈
        support ((simulateQ (loggedImpl prims) (prefixRun oa n)).run loggedInit) →
      ¬GateSeen gate s.2 →
      Pr[event | (simulateQ (loggedImpl prims) (OracleComp.queryBind gate k)).run s] ≤ ε)
    (s : LoggedState C) (hs : RawReachable prims s) (hseen : ¬GateSeen gate s.2) :
    (∑' r, Pr[= r | (loggedImpl prims gate).run s] * continuationReserve prims oa event r.2) ≤ ε := by
  classical
  letI : Decidable (∃ k, transcriptResidual oa s.2 = some (OracleComp.queryBind gate k)) :=
    Classical.propDecidable _
  by_cases h : ∃ k, transcriptResidual oa s.2 = some (OracleComp.queryBind gate k)
  · obtain ⟨k, hk⟩ := h
    obtain ⟨n, hn⟩ := rawReachable_prefix prims s hs oa _ hk
    rw [continuationReserve_matchingQuery prims oa event gate s k hk]
    exact hprefix n s k hn hseen
  · rw [continuationReserve_wrongQuery prims oa event gate s h]
    exact zero_le

theorem gateSeen_run {α : Type} (gate : (WorldSpec C).Domain)
    (oa : OracleComp (WorldSpec C) α) :
    ∀ s, GateSeen gate s.2 → ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s),
      GateSeen gate z.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs z hz
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    exact hz ▸ hs
  | query_bind t k ih =>
    intro s hs z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    apply ih r.1 r.2 _ z hz
    rw [loggedImpl_log prims t s r hr, gateSeen_logQuery]
    exact Or.inl hs

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
open Classical in
/-- A supported prefix poised at an unseen gate is exactly a completed
execution of the preceding gate-avoiding block. -/
theorem first_gate_residual {α β : Type} (gate : (WorldSpec C).Domain)
    (before : OracleComp (WorldSpec C) β)
    (next : β → (WorldSpec C).Range gate → OracleComp (WorldSpec C) α)
    (havoid : before.IsQueryBoundP (· = gate) 0)
    (n : ℕ) (initial s : LoggedState C)
    (k : (WorldSpec C).Range gate → OracleComp (WorldSpec C) α)
    (hp : (OracleComp.queryBind gate k, s) ∈ support ((simulateQ (loggedImpl prims)
      (prefixRun (before >>= fun value => query gate >>= next value) n)).run initial))
    (hseen : ¬GateSeen gate s.2) :
    ∃ value, (value, s) ∈ support ((simulateQ (loggedImpl prims) before).run initial) ∧
      OracleComp.queryBind gate k = (query gate >>= next value) := by
  classical
  induction before using OracleComp.inductionOn generalizing initial n with
  | pure value =>
    simp only [pure_bind] at hp
    cases n with
    | zero =>
      simp only [prefixRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hp
      have hs : s = initial := congrArg Prod.snd hp
      subst s
      exact ⟨value, by simp, congrArg Prod.fst hp⟩
    | succ n =>
      change (OracleComp.queryBind gate k, s) ∈ support ((simulateQ (loggedImpl prims)
        (query gate >>= fun u => prefixRun (next value u) n)).run initial) at hp
      simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
        mem_support_bind_iff] at hp
      obtain ⟨v, hv, hp⟩ := hp
      have hg : GateSeen gate v.2.2 := by
        rw [loggedImpl_log prims gate initial v hv, gateSeen_logQuery]
        exact Or.inr rfl
      exact (hseen (gateSeen_run prims gate _ v.2 hg _ hp)).elim
  | query_bind input cont ih =>
    have hb := (isQueryBoundP_query_bind_iff (· = gate) input cont 0).mp havoid
    have hi : input ≠ gate := by simpa using hb.1
    have hc : ∀ u, (cont u).IsQueryBoundP (· = gate) 0 := by simpa [hi] using hb.2
    cases n with
    | zero =>
      simp only [prefixRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hp
      have he := congrArg (fun oa : OracleComp (WorldSpec C) α =>
        match oa with | .pure _ => none | .queryBind t _ => some t) (congrArg Prod.fst hp)
      have he' : gate = input := Option.some.inj he
      exact (hi he'.symm).elim
    | succ n =>
      change (OracleComp.queryBind gate k, s) ∈ support ((simulateQ (loggedImpl prims)
        (query input >>= fun u => prefixRun
          (cont u >>= fun value => query gate >>= next value) n)).run initial) at hp
      simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
        mem_support_bind_iff] at hp
      obtain ⟨v, hv, hp⟩ := hp
      obtain ⟨value, hvalue, hnext⟩ := ih v.1 (hc v.1) n v.2 hp
      refine ⟨value, ?_, hnext⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff]
      exact ⟨v, hv, hvalue⟩

open Classical in
theorem first_gate_prefix {α β : Type} (gate : (WorldSpec C).Domain)
    (before : OracleComp (WorldSpec C) β)
    (next : β → (WorldSpec C).Range gate → OracleComp (WorldSpec C) α)
    (havoid : before.IsQueryBoundP (· = gate) 0)
    (n : ℕ) (initial s : LoggedState C)
    (k : (WorldSpec C).Range gate → OracleComp (WorldSpec C) α)
    (hp : (OracleComp.queryBind gate k, s) ∈ support ((simulateQ (loggedImpl prims)
      (prefixRun (before >>= fun value => query gate >>= next value) n)).run initial))
    (hseen : ¬GateSeen gate s.2) :
    ∃ value, (value, s) ∈ support ((simulateQ (loggedImpl prims) before).run initial) := by
  obtain ⟨value, hv, _⟩ := first_gate_residual prims gate before next havoid n initial s k hp hseen
  exact ⟨value, hv⟩

/-- Every supported execution asks a fixed gate, regardless of initial state. -/
def EnsuresGate {α : Type} (gate : (WorldSpec C).Domain)
    (oa : OracleComp (WorldSpec C) α) : Prop :=
  ∀ s, ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run s), GateSeen gate z.2.2

theorem ensuresGate_query (gate : (WorldSpec C).Domain) :
    EnsuresGate prims gate (query gate) := by
  intro s z hz
  simp only [query, simulateQ_spec_query] at hz
  rw [loggedImpl_log prims gate s z hz, gateSeen_logQuery]
  exact Or.inr rfl

theorem ensuresGate_bind_left {α β : Type} (gate : (WorldSpec C).Domain)
    (oa : OracleComp (WorldSpec C) α) (k : α → OracleComp (WorldSpec C) β)
    (h : EnsuresGate prims gate oa) : EnsuresGate prims gate (oa >>= k) := by
  intro s z hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨r, hr, hz⟩ := hz
  exact gateSeen_run prims gate (k r.1) r.2 (h s r hr) z hz

theorem ensuresGate_bind_right {α β : Type} (gate : (WorldSpec C).Domain)
    (oa : OracleComp (WorldSpec C) α) (k : α → OracleComp (WorldSpec C) β)
    (h : ∀ a, EnsuresGate prims gate (k a)) : EnsuresGate prims gate (oa >>= k) := by
  intro s z hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨r, _, hz⟩ := hz
  exact h r.1 r.2 z hz

theorem ensuresGate_map {α β : Type} (gate : (WorldSpec C).Domain)
    (oa : OracleComp (WorldSpec C) α) (f : α → β)
    (h : EnsuresGate prims gate oa) : EnsuresGate prims gate (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact ensuresGate_bind_left prims gate oa _ h

theorem ensuresGate_mapM {α β : Type} (gate : (WorldSpec C).Domain)
    (f : α → OracleComp (WorldSpec C) β) (a : α)
    (ha : EnsuresGate prims gate (f a)) :
    ∀ xs : List α, a ∈ xs → EnsuresGate prims gate (xs.mapM f) := by
  intro xs
  induction xs with
  | nil => simp
  | cons b xs ih =>
    intro hmem
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ensuresGate_bind_left prims gate _ _ ha
    · apply ensuresGate_bind_right prims gate
      intro b'
      exact ensuresGate_bind_left prims gate _ _ (ih hmem)

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


set_option maxRecDepth 100000 in
/-- A tree-opening handler begins with the actual free bottom ceremony. -/
theorem flagged_tree_prefix (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (s : TsigState C × Bool) :
    ∃ k, (SigningCoreProof.flaggedOracles x
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) (.inr (.tree b))).run s =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b)) >>= k := by
  simp only [SigningCoreProof.flaggedOracles, StateT.run_mk]
  rw [tsigOracles_free]
  simp [tsigOracles, dealtWith, liftM, SigningSecurityProof.liftFree, map_bind]

set_option maxRecDepth 100000 in
/-- A permitted second-round handler starts with the selected bottom ceremony. -/
theorem flagged_round2_prefix (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest)
    (s : TsigState C × Bool)
    (hguard : ¬(i ∈ s.1.corrupt ∨ i ∉ J.1 ∨ s.1.bound e ≠ some message)) :
    ∃ k, (SigningCoreProof.flaggedOracles x
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) (.inr (.round2 i J e message parts))).run s =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom (treeOf e))) >>= k := by
  simp only [SigningCoreProof.flaggedOracles, StateT.run_mk]
  rw [tsigOracles_free]
  simp [tsigOracles, dealtWith, liftM, SigningSecurityProof.liftFree, map_bind, hguard]

set_option maxRecDepth 100000 in
/-- The freshness comparison's honest signature also begins with a bottom call. -/
theorem honestSignature_prefix (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (e : KeyIndex) (message : Message) :
    ∃ k, honestSignature (fun oa => SigningCoreProof.honestLift oa)
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) e message =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom (treeOf e))) >>= k := by
  simp only [honestSignature, dealtWith, referenceTree_φ, bind_map_left]
  exact ⟨_, rfl⟩

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

open Classical in
/-- Syntactic absence of programming, including every possible response
branch. This permits oracle replacement before distributional reasoning. -/
def ProgramFree {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  oa.IsQueryBoundP IsProgram 0

theorem programFree_pure {α : Type} (a : α) :
    ProgramFree (pure a : OracleComp (WorldSpec C) α) := by
  classical
  exact isQueryBoundP_pure _ _ _

theorem programFree_bind {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (k : α → OracleComp (WorldSpec C) β) (ha : ProgramFree oa)
    (hk : ∀ a, ProgramFree (k a)) : ProgramFree (oa >>= k) := by
  classical
  exact isQueryBoundP_bind ha (fun a _ => hk a)

theorem programFree_map {α β : Type} (f : α → β) (oa : OracleComp (WorldSpec C) α)
    (ha : ProgramFree oa) : ProgramFree (f <$> oa) := by
  rw [← bind_pure_comp]
  exact programFree_bind oa _ ha (fun _ => programFree_pure _)

theorem programFree_query (t : (WorldSpec C).Domain) (ht : ¬IsProgram t) :
    ProgramFree (C := C) (query t) := by
  classical
  change (liftM (OracleSpec.query t) : OracleComp (WorldSpec C) _).IsQueryBoundP IsProgram 0
  exact (isQueryBoundP_query_iff _ _ _).mpr (fun h => (ht h).elim)

/-- Structural induction through an oracle handler that preserves the log invariant. -/
theorem programFree_simulate {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (OracleComp (WorldSpec C)))
    (h : ∀ t, ProgramFree (impl t)) (oa : OracleComp spec α) :
    ProgramFree (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using programFree_pure (C := C) a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact programFree_bind _ _ (h t) ih

theorem programFree_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ProgramFree (free oa) := by
  apply programFree_simulate
  intro t
  exact programFree_query (.inr t) (by simp [IsProgram])

theorem programFree_liftFree {α : Type} (oa : OracleComp (RoSpec C) α) :
    ProgramFree (SigningSecurityProof.liftFree oa) :=
  programFree_free _

/-- The adversary's local calls cannot access the programming summand. -/
theorem programFree_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ProgramFree (worldRoles.adversary oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [worldRoles, liftComp_pure, counted]
    exact programFree_pure a
  | query_bind t k ih =>
    simp only [worldRoles, liftComp_bind, counted_bind] at ih ⊢
    apply programFree_bind _ _ ?_ ih
    rcases t with t | (t | t) <;>
      exact programFree_query _ (by change ¬False; exact not_false)

/-- Structural induction also allows an auxiliary oracle state. -/
theorem programFree_simulateState {ι α σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (h : ∀ t s, ProgramFree ((impl t).run s)) (oa : OracleComp spec α) (s : σ) :
    ProgramFree ((simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simpa using programFree_pure (C := C) (a, s)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact programFree_bind _ _ (h t s) (fun r => ih r.1 r.2)

/-- Neither branch of the flagged handler can program the random oracle. -/
theorem programFree_flaggedOracles (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TsigState C × Bool) :
    ProgramFree ((SigningCoreProof.flaggedOracles x
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) t).run s) := by
  cases t with
  | inl t =>
    apply programFree_map
    exact programFree_adversary _
  | inr q =>
    apply programFree_map
    rw [tsigOracles_free]
    exact programFree_liftFree _

set_option maxRecDepth 100000 in
theorem programFree_finish (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (r : Forgery × TsigState C) :
    ProgramFree (SigningCoreProof.tsigFinish
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) r) := by
  rcases r with ⟨forgery, st⟩
  unfold SigningCoreProof.tsigFinish
  apply programFree_bind _ _ (programFree_liftFree _)
  intro verified
  dsimp only
  split_ifs
  · simpa using programFree_pure (C := C) (verified && true, st, forgery)
  · apply programFree_bind
    · erw [SigningCacheProof.liftFree_honestSignature]
      exact programFree_liftFree _
    · intro honest
      simpa using programFree_pure (C := C)
        (verified && decide (honest ≠ some forgery.signature), st, forgery)

set_option maxRecDepth 100000 in
theorem programFree_finalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProgramFree (SigningDescentProof.finalRun A x) := by
  unfold SigningDescentProof.finalRun
  dsimp only
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  apply programFree_bind _ _ (programFree_liftFree _)
  intro output
  rcases output with _ | (top | tree)
  · exact programFree_pure _
  · apply programFree_bind
    · exact programFree_simulateState _ (programFree_flaggedOracles x top) _ _
    · intro r
      exact programFree_map _ _ (programFree_finish x top _)
  · exact programFree_pure _

theorem programFree_queryBind_iff {α : Type} (t : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α) :
    ProgramFree (.queryBind t k) ↔ ¬IsProgram t ∧ ∀ u, ProgramFree (k u) := by
  classical
  change (query t >>= k).IsQueryBoundP IsProgram 0 ↔ _
  simp only [HasQuery.instOfMonadLift_query, isQueryBoundP_query_bind_iff,
    Nat.lt_irrefl, or_false, Nat.sub_zero, ite_self, ProgramFree]

theorem programFree_prefix {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hfree : ProgramFree oa) (n : ℕ) : ProgramFree (prefixRun oa n) := by
  induction n generalizing oa with
  | zero => simpa only [prefixRun] using programFree_pure oa
  | succ n ih =>
    cases oa with
    | pure a => exact programFree_pure _
    | queryBind t k =>
      obtain ⟨ht, hk⟩ := (programFree_queryBind_iff t k).mp hfree
      exact programFree_bind _ _ (programFree_query t ht) (fun u => ih (k u) (hk u))

/-- Every supported residual inherits syntactic absence of programming.
This includes the residual selected by a matching gate prefix. -/
theorem programFree_residual {α σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (oa : OracleComp (WorldSpec C) α) (hfree : ProgramFree oa) (n : ℕ) (s : σ)
    (r : OracleComp (WorldSpec C) α × σ)
    (hr : r ∈ support ((simulateQ impl (prefixRun oa n)).run s)) : ProgramFree r.1 := by
  induction n generalizing oa s r with
  | zero =>
    simp only [prefixRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hfree
  | succ n ih =>
    cases oa with
    | pure a =>
      simp only [prefixRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      exact programFree_pure _
    | queryBind t k =>
      obtain ⟨ht, hk⟩ := (programFree_queryBind_iff t k).mp hfree
      simp only [prefixRun, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind,
        mem_support_bind_iff] at hr
      obtain ⟨v, _, hr⟩ := hr
      exact ih (k v.1) (hk v.1) v.2 r hr

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

/-- Record the answers read by a completion, including answers already cached by
the signing run. The record starts empty and is separate from the oracle cache. -/
def recordReads {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (record : HashCache C) : OracleComp (Query C →ₒ HashOutput) (α × HashCache C) :=
  match oa with
  | .pure a => pure (a, record)
  | .queryBind input k => do
      let answer ← OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input)
      recordReads (k answer) (record.cacheQuery input answer)

theorem recordReads_preserves_unrecorded {α : Type}
    (oa : OracleComp (Query C →ₒ HashOutput) α) (base : HashCache C) :
    ∀ record cache, (∀ input, record input = none → cache input = base input) →
    ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads oa record)).run cache),
      ∀ input, z.1.2 input = none → z.2 input = base input := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro record cache h z hz
      change z ∈ ({((a, record), cache)} : Set _) at hz
      rcases hz with rfl
      exact h
  | query_bind input k ih =>
      intro record cache h z hz
      change z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input) >>=
          fun answer => recordReads (k answer)
          (record.cacheQuery input answer))).run cache) at hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, hr, hz⟩ := hz
      apply ih r.1 (record.cacheQuery input r.1) r.2 _ z hz
      intro other hnone
      have hne : other ≠ input := by
        intro heq
        subst other
        simp at hnone
      rw [randomOracle_result_cache input cache r hr,
        QueryCache.cacheQuery_of_ne _ _ hne]
      exact h other (by simpa [QueryCache.cacheQuery_of_ne _ _ hne] using hnone)

/-- The completion's record resolves its entire execution. It stays coherent
with the oracle cache, even when that cache was populated before completion. -/
theorem recordReads_resolves {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) :
    ∀ record cache, record ≤ cache →
    ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads oa record)).run cache),
      cache ≤ z.2 ∧ record ≤ z.1.2 ∧ z.1.2 ≤ z.2 ∧
        DeterministicSigning.Resolves z.1.2 oa z.1.1 := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro record cache hle z hz
      change z ∈ ({((a, record), cache)} : Set _) at hz
      rcases hz with rfl
      exact ⟨le_rfl, le_rfl, hle, .pure a⟩
  | query_bind input k ih =>
      intro record cache hle z hz
      change z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input) >>=
          fun answer => recordReads (k answer) (record.cacheQuery input answer))).run cache) at hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, hr, hz⟩ := hz
      have hro := randomOracle_support input cache r hr
      have hnew : record.cacheQuery input r.1 ≤ r.2 := by
        intro other value hv
        by_cases he : other = input
        · subst other
          simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
          subst value
          exact hro.2.1
        · rw [QueryCache.cacheQuery_of_ne _ _ he] at hv
          exact hro.1 (hle hv)
      have hrecord : record ≤ record.cacheQuery input r.1 := by
        intro other value hv
        by_cases he : other = input
        · subst other
          have heq := (hro.1 (hle hv)).symm.trans hro.2.1
          have heq' := Option.some.inj heq
          simpa only [QueryCache.cacheQuery_self, heq']
        · simpa only [QueryCache.cacheQuery_of_ne _ _ he] using hv
      obtain ⟨hgrow, hrec, hcoherent, hresolve⟩ := ih r.1 _ _ hnew z hz
      exact ⟨hro.1.trans hgrow, hrecord.trans hrec, hcoherent,
        .query input r.1 (hrec (QueryCache.cacheQuery_self _ _ _)) k z.1.1 hresolve⟩

/-- A predicate-free computation leaves the record unchanged on that predicate. -/
theorem recordReads_bound_zero {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (p : Query C → Prop) [DecidablePred p] (hb : oa.IsQueryBoundP p 0) :
    ∀ record cache z, z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads oa record)).run cache) →
      ∀ input, p input → z.1.2 input = record input := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro record cache z hz
      change z ∈ ({((a, record), cache)} : Set _) at hz
      rcases hz with rfl
      exact fun _ _ => rfl
  | query_bind input k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      have hp : ¬p input := by simpa using hb.1
      intro record cache z hz
      change z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input) >>=
          fun answer => recordReads (k answer) (record.cacheQuery input answer))).run cache) at hz
      simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, _, hz⟩ := hz
      intro other hother
      have hne : other ≠ input := fun heq => hp (heq ▸ hother)
      have hk : (k r.1).IsQueryBoundP p 0 := by simpa [hp] using hb.2 r.1
      exact (ih r.1 hk _ _ z hz other hother).trans
        (QueryCache.cacheQuery_of_ne _ _ hne)

/-- A single predicate query can record only one input in that predicate. This
holds even when the underlying oracle already has an adversarial cache. -/
theorem recordReads_bound_one {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (p : Query C → Prop) [DecidablePred p] (hb : oa.IsQueryBoundP p 1) :
    ∀ record cache, (∀ input, p input → record input = none) →
    ∀ z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads oa record)).run cache),
      ∀ left right lv rv, p left → p right →
        z.1.2 left = some lv → z.1.2 right = some rv → left = right := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro record cache hrecord z hz left right lv rv hl hr hleft hright
      change z ∈ ({((a, record), cache)} : Set _) at hz
      rcases hz with rfl
      simpa [hrecord left hl] using hleft
  | query_bind input k ih =>
      rw [isQueryBoundP_query_bind_iff] at hb
      intro record cache hrecord z hz
      change z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashOutput) input) >>=
          fun answer => recordReads (k answer) (record.cacheQuery input answer))).run cache) at hz
      simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨r, _, hz⟩ := hz
      by_cases hp : p input
      · have hk : (k r.1).IsQueryBoundP p 0 := by simpa [hp] using hb.2 r.1
        have hzero := recordReads_bound_zero (k r.1) p hk _ _ z hz
        have honly : ∀ other value, p other → z.1.2 other = some value → other = input := by
          intro other value hother hvalue
          by_contra hne
          rw [hzero other hother, QueryCache.cacheQuery_of_ne _ _ hne,
            hrecord other hother] at hvalue
          cases hvalue
        intro left right lv rv hl hr hleft hright
        exact (honly left lv hl hleft).trans (honly right rv hr hright).symm
      · have hk : (k r.1).IsQueryBoundP p 1 := by simpa [hp] using hb.2 r.1
        apply ih r.1 hk _ _ _ z hz
        intro other hother
        have hne : other ≠ input := fun heq => hp (heq ▸ hother)
        rw [QueryCache.cacheQuery_of_ne _ _ hne]
        exact hrecord other hother

open Classical in
/-- A completion's own reads cannot count as alternative inputs. -/
def recordedTargets (target : CompletionTargets C) (record : HashCache C) : CompletionTargets C :=
  fun input => if (record input).isSome then (input, 0) else target input

/-- Generate targets from an honest computation and exclude every input it read. -/
def recordedCompletion {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (target : α → HashCache C → CompletionTargets C) :
    OracleComp (Query C →ₒ HashOutput) (CompletionTargets C) :=
  (fun r => recordedTargets (target r.1 r.2) r.2) <$> recordReads oa ∅

/-- Recording the completion proves its read condition without any assumption
on the program's adaptive queries. Structural uniqueness is needed only later,
to show that a genuine alternative input survives the exclusion. -/
theorem recordedCompletion_reads {α : Type} (relevant : Query C → Prop)
    (oa : OracleComp (Query C →ₒ HashOutput) α)
    (target : α → HashCache C → CompletionTargets C) :
    CompletionReadsTargets relevant (recordedCompletion oa target) := by
  intro cache z hz
  simp only [recordedCompletion, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  intro input hnone _ hsome
  have hrecord : (r.1.2 input).isSome := by
    by_contra hn
    have heq : r.1.2 input = none := by
      cases hi : r.1.2 input <;> simp_all
    have hpres := recordReads_preserves_unrecorded oa cache ∅ cache
      (fun _ _ => rfl) r hr input heq
    simpa only [hpres, hnone, Option.isSome_none, Bool.false_eq_true] using hsome
  simp [recordedTargets, hrecord]

theorem completedHit_recordedTargets (relevant : Query C → Prop)
    (target : CompletionTargets C) (record cache : HashCache C) :
    CompletedHit relevant (recordedTargets target record) cache ↔
      ∃ input output, cache input = some output ∧ record input = none ∧
        relevant input ∧ input ≠ (target input).1 ∧ truncateHash output = (target input).2 := by
  classical
  constructor
  · rintro ⟨input, output, hc, hr, hn, he⟩
    cases hm : record input with
    | none => exact ⟨input, output, hc, hm, hr,
        by simpa [recordedTargets, hm] using hn,
        by simpa [recordedTargets, hm] using he⟩
    | some value => simp [recordedTargets, hm] at hn
  · rintro ⟨input, output, hc, hm, hr, hn, he⟩
    refine ⟨input, output, hc, hr, ?_, ?_⟩
    · simpa [recordedTargets, hm] using hn
    · simpa [recordedTargets, hm] using he

/-- The structural domains exclude the two codeword hashes. -/
def StructuralDomain : XmssSecurity.HashDomain → Prop
  | .encoding _ | .topEncoding _ => False
  | _ => True

/-- Two inputs address the same structural hash position. -/
def SameStructuralPosition (P : PublicParameter) (input honest : Query C) : Prop :=
  ∃ domain payload honestPayload, StructuralDomain domain ∧
    input = .hash (XmssSecurity.tweakableHashInput P domain payload) ∧
    honest = .hash (XmssSecurity.tweakableHashInput P domain honestPayload)

def forestRelevant (P : PublicParameter) (input : Query C) : Prop :=
  SameStructuralPosition P input input

theorem forestRelevant_prf (P : PublicParameter) (seed : HashOutput) (p : Point) :
    ¬forestRelevant (C := C) P (.prf seed p) := by
  rintro ⟨domain, payload, honestPayload, _, h, _⟩
  cases h

/-- The ordinary hash lift used by the total forest computation. -/
def forestHash {α : Type} (oa : OracleComp HashSpec α) :
    OracleComp (Query C →ₒ HashOutput) α :=
  simulateQ (fun input => OracleComp.lift
    (OracleSpec.query (spec := Query C →ₒ HashOutput) (.hash input))) oa

theorem resolves_forestHash {α : Type} (record : HashCache C)
    (oa : OracleComp XmssSecurity.HashSpec α) :
    ∀ value, DeterministicSigning.Resolves record (forestHash oa) value →
      DeterministicSigning.Resolves (SigningDescentProof.thView record) oa value := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro value h
      simp only [forestHash, simulateQ_pure] at h
      have hv := h.pure_inv
      subst value
      exact .pure a
  | query_bind input k ih =>
      intro value h
      simp only [forestHash, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map] at h
      obtain ⟨answer, hanswer, htail⟩ := h.query_inv
      exact .query input answer hanswer k value (ih answer value htail)

/-- The threshold PRF evaluated directly over the completion's hash oracle. -/
def forestValue (seeds : C.Term → HashOutput) (p : Point) :
    OracleComp (Query C →ₒ HashOutput) Digest := do
  let values ← C.terms.mapM fun T => truncateHash <$> OracleComp.lift
    (OracleSpec.query (spec := Query C →ₒ HashOutput) (.prf (seeds T) p))
  pure (values.foldl (· ^^^ ·) 0)

/-- Embed the completion's hash-only computations in the signing oracle. -/
def hashEmbed {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) :
    OracleComp (RoSpec C) α := simulateQ (fun q => hashQuery q) oa

theorem hashEmbed_forestHash {α : Type} (oa : OracleComp HashSpec α) :
    hashEmbed (forestHash (C := C) oa) = tweakable oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [hashEmbed, forestHash, tweakable]
  | query_bind input k ih =>
    simp only [hashEmbed, forestHash, tweakable, simulateQ_bind, simulateQ_spec_query]
    congr 1
    funext answer
    exact ih answer

theorem hashEmbed_forestValue (seeds : C.Term → HashOutput) (p : Point) :
    hashEmbed (forestValue seeds p) = prfValue seeds p := by
  simp only [hashEmbed, forestValue, prfValue, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_map, simulateQ_spec_query, simulateQ_pure, prf]

theorem eval_hashEmbed {α : Type} (h : Query C → HashOutput)
    (oa : OracleComp (Query C →ₒ HashOutput) α) :
    D prims h (hashEmbed oa) = evalWithAnswerFn h oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [hashEmbed, D_pure]
  | query_bind input k ih =>
    simp only [hashEmbed, simulateQ_bind, simulateQ_spec_query, D_bind, D_hashQuery,
      evalWithAnswerFn_bind, DeterministicSigning.eval_liftM_query]
    exact ih _

theorem hashEmbed_referenceTree (seeds : C.Term → HashOutput) (P : PublicParameter)
    (top : TopTree) (tree : Tree) :
    hashEmbed (referenceTree forestHash (forestValue seeds) P top tree) =
      referenceTree tweakable (prfValue seeds) P top tree := by
  let hom : OracleComp (Query C →ₒ HashOutput) →ᵐ OracleComp (RoSpec C) :=
    simulateQ' (fun q => hashQuery q)
  have h := SeedHitProof.hom_referenceTree hom forestHash (forestValue seeds) P top tree
  change hashEmbed _ = referenceTree (fun oa => hashEmbed (forestHash oa))
    (fun p => hashEmbed (forestValue seeds p)) P top tree at h
  simpa only [hashEmbed_forestHash, hashEmbed_forestValue] using h

theorem hashEmbed_referenceJob (seeds : C.Term → HashOutput) (P : PublicParameter)
    (job : Job) :
    hashEmbed (referenceJob forestHash (forestValue seeds) P job) =
      referenceJob tweakable (prfValue seeds) P job := by
  let hom : OracleComp (Query C →ₒ HashOutput) →ᵐ OracleComp (RoSpec C) :=
    simulateQ' (fun q => hashQuery q)
  have h := SeedHitProof.hom_referenceJob hom forestHash (forestValue seeds) P job
  change hashEmbed _ = referenceJob (fun oa => hashEmbed (forestHash oa))
    (fun p => hashEmbed (forestValue seeds p)) P job at h
  simpa only [hashEmbed_forestHash, hashEmbed_forestValue] using h

/-- Every hash read of a supported honest computation is resolved by its final
cache. This includes threshold PRF inputs, not just the structural hash view. -/
theorem run_hashEmbed_resolves {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) :
    ∀ initial, ∀ z ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (hashEmbed oa))).run initial),
      DeterministicSigning.Resolves z.2.1 oa z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro initial z hz
    simp [SigningSecurityProof.liftFree, free, hashEmbed] at hz
    subst hz
    exact .pure _
  | query_bind input k ih =>
    intro initial z hz
    have he : hashEmbed (OracleComp.lift (OracleSpec.query input) >>= k) =
        hashQuery input >>= fun answer => hashEmbed (k answer) := by
      simp [hashEmbed, simulateQ_bind]
    rw [he, SigningSecurityProof.liftFree, liftComp_bind, free_bind] at hz
    obtain ⟨p, hp, hz⟩ := SigningCacheProof.run_bind_support prims _ _ initial z hz
    have hgrow := SigningCacheProof.countRun_grows prims _ _ z hz
    exact .query input p.1 (hgrow (SigningCacheProof.run_hashQuery prims input initial p hp))
      k z.1 (ih p.1 p.2 z hz)

/-- The actual dealt object, shared by the semantic opening instrumentation. -/
abbrev actualDealt (x : SigningSecurityProof.Keys3 C) (top : TopTree) :
    Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
    (dealtKeys x.1 x.2.1 x.2.2) top (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))

/-- Only semantic calls that pass their guards count as bottom openings. -/
def Opens (b : Fin (2 ^ layerHeight)) (s : TsigState C) : (LocalSpec C + TsigSpec C).Domain → Prop
  | .inr (.tree b') => b' = b
  | .inr (.round2 i J e message _) => treeOf e = b ∧ ¬(i ∈ s.corrupt ∨ i ∉ J.1 ∨ s.bound e ≠ some message)
  | _ => False

set_option maxRecDepth 100000 in
theorem opens_prefix (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (s : TsigState C × Bool)
    (t : (LocalSpec C + TsigSpec C).Domain) (h : Opens b s.1 t) :
    ∃ k, (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run s =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b)) >>= k := by
  rcases t with t | q
  · cases h
  · cases q with
    | corrupt _ | round1 _ _ _ _ => cases h
    | tree b' =>
      change b' = b at h
      subst b'
      exact flagged_tree_prefix x top b s
    | round2 i J e message parts =>
      obtain ⟨rfl, hguard⟩ := h
      exact flagged_round2_prefix x top i J e message parts s hguard

/-- A ghost opening bit, separate from hiddenHit. All real calls are unchanged. -/
def openedOracles (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : QueryImpl (LocalSpec C + TsigSpec C)
      (StateT ((TsigState C × Bool) × Bool) (OracleComp (WorldSpec C))) :=
  open Classical in
  fun t => StateT.mk fun p =>
    (fun z => (z.1, (z.2, p.2 || decide (Opens b p.1.1 t)))) <$>
      (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p.1

set_option maxRecDepth 100000 in
/-- Forgetting the ghost bit gives exactly the original flagged computation. -/
theorem openedRun_forget {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : TsigState C × Bool) (opened : Bool) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (openedOracles x top b) oa).run (s, opened) =
      (simulateQ (SigningCoreProof.flaggedOracles x (actualDealt x top)) oa).run s :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun t s opened => by simp [openedOracles, Functor.map_map]) oa s opened

def BottomResolved (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (cache : HashCache C) : Prop :=
  ∃ output, DeterministicSigning.Resolves cache
    (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output

theorem bottomResolved_mono (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) {cache larger : HashCache C} (hle : cache ≤ larger)
    (h : BottomResolved x top b cache) : BottomResolved x top b larger :=
  h.imp (fun _ h => h.mono hle)

set_option maxRecDepth 100000 in
/-- A set opening bit certifies an actual completed bottom call in the cache. -/
theorem openedOracles_resolves (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (t : (LocalSpec C + TsigSpec C).Domain)
    (p : (TsigState C × Bool) × Bool) (initial : HashCache C × ℕ)
    (hp : p.2 = true → BottomResolved x top b initial.1)
    (r : ((LocalSpec C + TsigSpec C).Range t × ((TsigState C × Bool) × Bool)) × (HashCache C × ℕ))
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((openedOracles x top b t).run p)).run initial)) :
    r.1.2.2 = true → BottomResolved x top b r.2.1 := by
  classical
  simp only [openedOracles, StateT.run_mk, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rintro (hprevious | hopen)
  · exact bottomResolved_mono x top b (SigningCacheProof.countRun_grows prims _ _ v hv) (hp hprevious)
  · obtain ⟨k, he⟩ := opens_prefix x top b p.1 t hopen
    rw [he] at hv
    obtain ⟨call, hc, htail⟩ := SigningCacheProof.run_bind_support prims _ _ initial v hv
    rw [← hashEmbed_referenceTree] at hc
    exact ⟨call.1, (run_hashEmbed_resolves prims _ initial call hc).mono
      (SigningCacheProof.countRun_grows prims _ _ v htail)⟩

set_option maxRecDepth 100000 in
/-- Structural induction carries the opening certificate through an adaptive
adversary, including later corruptions and repeated calls. -/
theorem openedRun_resolves {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ (p : (TsigState C × Bool) × Bool) (initial : HashCache C × ℕ),
      (p.2 = true → BottomResolved x top b initial.1) →
      ∀ r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((simulateQ (openedOracles x top b) oa).run p)).run initial),
        r.1.2.2 = true → BottomResolved x top b r.2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro p initial hp r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hp
  | query_bind t k ih =>
    intro p initial hp r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    exact ih v.1.1 v.1.2 v.2 (openedOracles_resolves prims x top b t p initial hp v hv) r hr

/-- Stop before executing a semantic opening. The surviving branches execute
exactly the original handlers, including all local queries and corruptions. -/
def unopenedRun {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (p : TsigState C × Bool) : OracleComp (WorldSpec C) (Option (α × (TsigState C × Bool))) :=
  open Classical in
  match oa with
  | .pure a => pure (some (a, p))
  | .queryBind t k =>
      if Opens b p.1 t then pure none else
        (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p >>= fun r =>
          unopenedRun x top b (k r.1) r.2

set_option maxRecDepth 100000 in
theorem programFree_unopenedRun {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (p : TsigState C × Bool) : ProgramFree (unopenedRun x top b oa p) := by
  classical
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a => exact programFree_pure _
  | query_bind t k ih =>
    change ProgramFree (if Opens b p.1 t then pure none else
      (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p >>= fun r =>
        unopenedRun x top b (k r.1) r.2)
    split_ifs
    · exact programFree_pure _
    · exact programFree_bind _ _ (programFree_flaggedOracles x top t p) (fun r => ih r.1 r.2)

set_option maxRecDepth 100000 in
/-- Once set, the ghost bit remains set through every subsequent real call. -/
theorem openedRun_mono {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ (p : TsigState C × Bool) (s : LoggedState C),
      ∀ r ∈ support ((simulateQ (loggedImpl prims)
        ((simulateQ (openedOracles x top b) oa).run (p, true))).run s),
        r.1.2.2 = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro p s r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    rfl
  | query_bind t k ih =>
    intro p s r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, openedOracles, StateT.run_mk,
      Bool.true_or, simulateQ_map, StateT.run_map, bind_map_left] at hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    exact ih v.1.1 v.1.2 v.2 r hr

set_option maxRecDepth 100000 in
/-- Stopping before an opening preserves the full distribution on unopened
outcomes, including the final cache, count, and raw transcript. -/
theorem unopenedRun_probability {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ (p : TsigState C × Bool) (s : LoggedState C)
      (event : (α × (TsigState C × Bool)) × LoggedState C → Prop),
    Pr[fun r => ∃ v, r.1 = some v ∧ event (v, r.2) |
      (simulateQ (loggedImpl prims) (unopenedRun x top b oa p)).run s] =
    Pr[fun r => event ((r.1.1, r.1.2.1), r.2) ∧ r.1.2.2 = false |
      (simulateQ (loggedImpl prims)
        ((simulateQ (openedOracles x top b) oa).run (p, false))).run s] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro p s event
    rw [show unopenedRun x top b (pure a) p = pure (some (a, p)) from rfl]
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, Option.some.injEq,
      exists_eq_left', and_true]
  | query_bind t k ih =>
    intro p s event
    rw [show unopenedRun x top b (liftM (OracleSpec.query t) >>= k) p =
      (if Opens b p.1 t then pure none else
        (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p >>= fun r =>
          unopenedRun x top b (k r.1) r.2) from rfl]
    by_cases ho : Opens b p.1 t
    · rw [if_pos ho]
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, reduceCtorEq,
        false_and, exists_false, not_false_eq_true, ↓reduceIte]
      symm
      apply probEvent_eq_zero
      intro r hr he
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, openedOracles, StateT.run_mk,
        Bool.false_or, decide_eq_true ho, simulateQ_map, StateT.run_map, bind_map_left] at hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨v, hv, hr⟩ := hr
      simp only [ho, decide_true] at hr
      have htrue := openedRun_mono prims x top b (k v.1.1) v.1.2 v.2 r hr
      simp [htrue] at he
    · rw [if_neg ho]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, openedOracles, StateT.run_mk,
        Bool.false_or, decide_eq_false ho, simulateQ_map, StateT.run_map, bind_map_left,
        probEvent_bind_eq_tsum]
      apply tsum_congr
      intro r
      rw [ih r.1.1 r.1.2 r.2 event]
      simp only [ho, decide_false]

set_option maxRecDepth 100000 in
theorem unopenedRun_probOutput {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (p p' : TsigState C × Bool) (s s' : LoggedState C) (a : α) :
    Pr[= (some (a, p'), s') | (simulateQ (loggedImpl prims) (unopenedRun x top b oa p)).run s] =
    Pr[= ((a, (p', false)), s') | (simulateQ (loggedImpl prims)
      ((simulateQ (openedOracles x top b) oa).run (p, false))).run s] := by
  have h := unopenedRun_probability prims x top b oa p s (fun r => r = ((a, p'), s'))
  convert h using 1
  · rw [← probEvent_eq_eq_probOutput]
    apply probEvent_congr' _ rfl
    intro r _
    constructor
    · rintro rfl
      exact ⟨(a, p'), rfl, rfl⟩
    · rintro ⟨v, hv, he⟩
      cases r
      cases Prod.mk.inj he
      simp_all
  · rw [← probEvent_eq_eq_probOutput]
    apply probEvent_congr' _ rfl
    intro r _
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨he, hb⟩
      rcases r with ⟨⟨a', p'', bit⟩, s''⟩
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj he |>.imp_left Prod.mk.inj
      cases hb
      rfl

set_option maxRecDepth 100000 in
/-- The stopping identity extends to any nonnegative continuation weight. -/
theorem unopenedRun_expectation {α : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (p : TsigState C × Bool) (s : LoggedState C)
    (weight : (α × (TsigState C × Bool)) × LoggedState C → ℝ≥0∞) :
    (∑' r, Pr[= r | (simulateQ (loggedImpl prims) (unopenedRun x top b oa p)).run s] *
      r.1.elim 0 (fun v => weight (v, r.2))) =
    ∑' r, Pr[= r | (simulateQ (loggedImpl prims)
      ((simulateQ (openedOracles x top b) oa).run (p, false))).run s] *
      if r.1.2.2 then 0 else weight ((r.1.1, r.1.2.1), r.2) := by
  classical
  simp only [ENNReal.tsum_prod', tsum_option _ ENNReal.summable, Option.elim_none, Option.elim_some,
    mul_zero, tsum_zero, zero_add]
  simp only [tsum_fintype (β := Bool), Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte, mul_zero, tsum_zero, add_zero, zero_add]
  simp_rw [unopenedRun_probOutput prims]

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Stopping is compatible with any real continuation whose abort result
cannot satisfy the terminal event. -/
theorem unopenedRun_bind_probability {α β : Type} (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (p : TsigState C × Bool) (s : LoggedState C)
    (cont : α × (TsigState C × Bool) → OracleComp (WorldSpec C) β)
    (abort : β) (event : β × LoggedState C → Prop) (habort : ∀ s, ¬event (abort, s)) :
    Pr[event | (simulateQ (loggedImpl prims)
      (unopenedRun x top b oa p >>= fun r => r.elim (pure abort) cont)).run s] =
    Pr[fun r => event (r.1.1, r.2) ∧ r.1.2 = false |
      (simulateQ (loggedImpl prims)
        (((simulateQ (openedOracles x top b) oa).run (p, false)) >>= fun r =>
          (fun v => (v, r.2.2)) <$> cont (r.1, r.2.1))).run s] := by
  classical
  simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  let weight := fun r : (α × (TsigState C × Bool)) × LoggedState C =>
    Pr[event | (simulateQ (loggedImpl prims) (cont r.1)).run r.2]
  calc
    _ = ∑' r, Pr[= r | (simulateQ (loggedImpl prims) (unopenedRun x top b oa p)).run s] *
        r.1.elim 0 (fun v => weight (v, r.2)) := by
      apply tsum_congr
      intro r
      cases hr : r.1 with
      | none => simp [weight, hr, habort]
      | some v => rfl
    _ = ∑' r, Pr[= r | (simulateQ (loggedImpl prims)
        ((simulateQ (openedOracles x top b) oa).run (p, false))).run s] *
        if r.1.2.2 then 0 else weight ((r.1.1, r.1.2.1), r.2) :=
      unopenedRun_expectation prims x top b oa p s weight
    _ = _ := by
      apply tsum_congr
      intro r
      simp only [simulateQ_map, StateT.run_map, probEvent_map]
      cases hb : r.1.2.2 <;> simp [hb, weight, Function.comp_def]

/-- The real final run with one additional semantic-opening bit. -/
def openedFinalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    OracleComp (WorldSpec C) (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × Bool) := do
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top
    | pure (((false, false), none), false)
  let r ← (simulateQ (openedOracles x top b) (A ⟨top.root, x.1⟩ top)).run
    ((SigningCoreProof.tsigInit, false), false)
  (fun w => (((w.1, r.2.1.2), some (top, w.2.1, w.2.2)), r.2.2)) <$>
    SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1.1)

/-- The actual final program stopped before opening the selected bottom tree. -/
def unopenedFinalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) := do
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top
    | pure ((false, false), none)
  let some r ← unopenedRun x top b (A ⟨top.root, x.1⟩ top) (SigningCoreProof.tsigInit, false)
    | pure ((false, false), none)
  (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
    SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1)

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The stopped final program has exactly the unopened event mass, from any
initial raw state, with the original verification continuation. -/
theorem unopenedFinalRun_probability (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) (s : LoggedState C)
    (event : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C) → Prop)
    (hnone : ∀ flags s, ¬event ((flags, none), s)) :
    Pr[event | (simulateQ (loggedImpl prims) (unopenedFinalRun A x b)).run s] =
    Pr[fun r => event (r.1.1, r.2) ∧ r.1.2 = false |
      (simulateQ (loggedImpl prims) (openedFinalRun A x b)).run s] := by
  classical
  unfold unopenedFinalRun openedFinalRun
  simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro r
  congr 1
  rcases hr : r.1 with _ | (top | bottom)
  · simp [hnone]
  · simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
    have h := unopenedRun_bind_probability prims x top b (A ⟨top.root, x.1⟩ top)
        (SigningCoreProof.tsigInit, false) r.2
        (fun r => (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
          SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1))
        ((false, false), none) event (hnone (false, false))
    simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum, Functor.map_map] at h
    refine Eq.trans ?_ h
    apply tsum_congr
    intro v
    cases v.1 <;> rfl
  · simp [hnone]

set_option maxRecDepth 100000 in
/-- Instrumentation changes neither real calls nor the returned game outcome. -/
theorem openedFinalRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    Prod.fst <$> openedFinalRun A x b = SigningDescentProof.finalRun A x := by
  unfold openedFinalRun SigningDescentProof.finalRun
  rw [map_bind]
  apply bind_congr
  intro output
  rcases output with _ | (top | bottom)
  · simp
  · simp only [map_bind, Functor.map_map]
    erw [← openedRun_forget x top b (A ⟨top.root, x.1⟩ top) (SigningCoreProof.tsigInit, false) false,
      bind_map_left]
  · simp

set_option maxRecDepth 100000 in
open SigningCacheProof in
/-- A set bit in the actual instrumented final run supplies the resolved
bottom ceremony in its final cache, after verification and freshness checking. -/
theorem openedFinalRun_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) (initial : HashCache C × ℕ)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × Bool) × (HashCache C × ℕ))
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (openedFinalRun A x b)).run initial))
    (hopen : r.1.2 = true) :
    ∃ top state forgery, r.1.1.2 = some (top, state, forgery) ∧ BottomResolved x top b r.2.1 := by
  unfold openedFinalRun at hr
  obtain ⟨p, hp, hr⟩ := run_bind_support prims _ _ initial r hr
  rcases hp1 : p.1 with _ | (top | bottom)
  · rw [hp1] at hr
    simp at hr
    subst hr
    cases hopen
  swap
  · rw [hp1] at hr
    simp at hr
    subst hr
    cases hopen
  rw [hp1] at hr
  obtain ⟨q, hq, hr⟩ := run_bind_support prims _ _ p.2 r hr
  have hresolved := openedRun_resolves prims x top b (A ⟨top.root, x.1⟩ top)
    ((SigningCoreProof.tsigInit, false), false) p.2 (by simp) q hq
  have hgrow := countRun_grows prims _ _ r hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact ⟨top, w.1.2.1, w.1.2.2, rfl, bottomResolved_mono x top b hgrow (hresolved hopen)⟩

/-- Logged instrumentation preserves precisely the raw-query transcript. -/
def openedLoggedRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :=
  (simulateQ (loggedImpl prims) (openedFinalRun A x b)).run loggedInit

set_option maxRecDepth 100000 in
theorem openedLoggedRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    (fun r => (r.1.1, r.2)) <$> openedLoggedRun prims A x b = loggedRun prims A x := by
  rw [openedLoggedRun, loggedRun, ← openedFinalRun_forget A x b, simulateQ_map, StateT.run_map]
  rfl

set_option maxRecDepth 100000 in
/-- Each real supported prefix lifts to an instrumented prefix with the exact
same raw state. Thus the opening instrumentation remains valid at a PRF gate. -/
theorem prefixRun_opened_lift (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) (n : ℕ)
    (rest : OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)))
    (s : LoggedState C)
    (hp : (rest, s) ∈ support ((simulateQ (loggedImpl prims)
      (prefixRun (SigningDescentProof.finalRun A x) n)).run loggedInit)) :
    ∃ instrumented,
      (instrumented, s) ∈ support ((simulateQ (loggedImpl prims)
        (prefixRun (openedFinalRun A x b) n)).run loggedInit) ∧ Prod.fst <$> instrumented = rest := by
  rw [← openedFinalRun_forget A x b, prefixRun_map, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at hp
  obtain ⟨⟨instrumented, state⟩, hi, he⟩ := hp
  have hs : state = s := congrArg Prod.snd he
  subst state
  exact ⟨instrumented, hi, congrArg Prod.fst he⟩

theorem eval_mapM {α β : Type} (h : Query C → HashOutput)
    (f : α → OracleComp (Query C →ₒ HashOutput) β) (xs : List α) :
    evalWithAnswerFn h (xs.mapM f) = xs.map (fun a => evalWithAnswerFn h (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih, List.map_cons]

/-- The completion uses exactly the threshold PRF value of the signing code. -/
theorem eval_forestValue (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (p : Point) :
    evalWithAnswerFn h (forestValue seeds p) = D prims h (prfValue seeds p) := by
  simp only [forestValue, evalWithAnswerFn_bind, eval_mapM, evalWithAnswerFn_pure,
    evalWithAnswerFn_map, DeterministicSigning.eval_liftM_query, prfValue, D_bind, D_mapM, D_pure,
    prf, D_map, D_hashQuery]

theorem resolves_forestValue (record larger : HashCache C) (hle : record ≤ larger)
    (seeds : C.Term → HashOutput) (p : Point) (value : Digest)
    (h : DeterministicSigning.Resolves record (forestValue seeds p) value) :
    D prims (SigningCacheProof.answersOf larger) (prfValue seeds p) = value := by
  rw [← eval_forestValue prims]
  exact h.eval _ (fun input output ho => by simp [SigningCacheProof.answersOf, hle ho])

/-- leanVM's structural forest visits each structural address at most once. -/
theorem modelForest_bound (P : PublicParameter)
    (secret : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → Digest)
    (topSecret : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → Digest)
    (domain : XmssSecurity.HashDomain) (hs : StructuralDomain domain) :
    (XmssSecurity.Concrete.honestKeygen P secret topSecret (fun _ _ => pure 0) :
      OracleComp XmssSecurity.HashSpec _).IsQueryBoundP (XmssSecurity.AtHashAddress P domain) 1 := by
  cases domain with
  | chain e l k =>
      exact XmssSecurity.Concrete.rootTree_queryBound_chainAddress P secret topSecret (fun _ => 0) e l k
  | leaf e =>
      exact XmssSecurity.Concrete.rootTree_queryBound_leafAddress P secret topSecret (fun _ => 0) e
  | merkle level node =>
      exact XmssSecurity.Concrete.rootTree_queryBound_merkleAddress P secret topSecret (fun _ => 0) level node
  | topChain e l k =>
      exact XmssSecurity.Concrete.honestKeygen_queryBound_topChainAddress P secret topSecret (fun _ => 0) e l k
  | topLeaf e =>
      exact XmssSecurity.Concrete.honestKeygen_queryBound_topLeafAddress P secret topSecret (fun _ => 0) e
  | topMerkle level node =>
      exact XmssSecurity.Concrete.honestKeygen_queryBound_topMerkleAddress P secret topSecret (fun _ => 0) level node
  | encoding _ => exact hs.elim
  | topEncoding _ => exact hs.elim

def forestAddress (P : PublicParameter) (domain : XmssSecurity.HashDomain) : Query C → Prop
  | .hash input => XmssSecurity.AtHashAddress P domain input
  | _ => False

local instance (P : PublicParameter) (domain : XmssSecurity.HashDomain) :
    DecidablePred (forestAddress (C := C) P domain) := Classical.decPred _

theorem forestHash_bound {α : Type} (oa : OracleComp HashSpec α)
    (P : PublicParameter) (domain : XmssSecurity.HashDomain) (n : ℕ)
    (h : oa.IsQueryBoundP (XmssSecurity.AtHashAddress P domain) n) :
    (forestHash (C := C) oa).IsQueryBoundP (forestAddress P domain) n := by
  classical
  letI : (Query C →ₒ HashOutput).IsUniformSpec := OracleSpec.IsUniformSpec.ofFintypeInhabited _
  apply h.simulateQ_of_step
  · intro input _
    simp only [isQueryBoundP_query_iff]
    omega
  · intro input hn
    simp only [isQueryBoundP_query_iff, forestAddress]
    exact fun hp => (hn hp).elim

theorem mapM_bound_zero {α β : Type} (xs : List α)
    (f : α → OracleComp (Query C →ₒ HashOutput) β) (p : Query C → Prop) [DecidablePred p]
    (hf : ∀ a, (f a).IsQueryBoundP p 0) : (xs.mapM f).IsQueryBoundP p 0 := by
  classical
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.mapM_cons]
      exact isQueryBoundP_bind (n := 0) (m := 0) (hf a) (fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0) ih (fun _ _ => by simp))

theorem sequenceFin_bound_zero {α : Type} {n : ℕ}
    (f : Fin n → OracleComp (Query C →ₒ HashOutput) α) (p : Query C → Prop) [DecidablePred p]
    (hf : ∀ a, (f a).IsQueryBoundP p 0) :
    (XmssSecurity.Concrete.sequenceFin f).IsQueryBoundP p 0 := by
  classical
  induction n with
  | zero => simp [XmssSecurity.Concrete.sequenceFin]
  | succ n ih =>
      rw [XmssSecurity.Concrete.sequenceFin]
      exact isQueryBoundP_bind (n := 0) (m := 0) (hf 0) (fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0)
          (ih (fun a => f a.succ) (fun a => hf a.succ)) (fun _ _ => by simp))

theorem forestValue_bound (seeds : C.Term → HashOutput) (p : Point)
    (P : PublicParameter) (domain : XmssSecurity.HashDomain) :
    (forestValue seeds p).IsQueryBoundP (forestAddress P domain) 0 := by
  classical
  unfold forestValue
  apply isQueryBoundP_bind (m := 0)
  · apply mapM_bound_zero
    intro T
    simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, forestAddress]
    exact False.elim
  · intro _ _
    simp

/-- Complete the structural forest using leanVM's once-per-address traversal.
Threshold PRFs supply the starts of both layers. The auxiliary top grinding has
base zero and touches only encoding domains, which are irrelevant to this lane. -/
def forestRun (x : SigningSecurityProof.Keys3 C) : OracleComp (Query C →ₒ HashOutput) Unit := do
  let secret ← XmssSecurity.Concrete.sequenceFin fun e : XmssSecurity.LeafIndex =>
    XmssSecurity.Concrete.sequenceFin fun l : XmssSecurity.ChainIndex =>
      forestValue x.2.1 (.chain bottomLayer e l (digit 0))
  let topSecret ← XmssSecurity.Concrete.sequenceFin fun b : XmssSecurity.TopIndex =>
    XmssSecurity.Concrete.sequenceFin fun l : XmssSecurity.ChainIndex =>
      forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))
  let _ ← forestHash (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret
    (fun _ _ => pure 0) : OracleComp XmssSecurity.HashSpec _)
  pure ()

/-- A supported completion resolves each threshold chain start and the entire
model forest in its own record, not merely in the larger oracle cache. -/
theorem forestRun_resolves (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache)) :
    ∃ secret topSecret result,
      (∀ e l, DeterministicSigning.Resolves z.1.2
        (forestValue x.2.1 (.chain bottomLayer e l (digit 0))) (secret e l)) ∧
      (∀ b l, DeterministicSigning.Resolves z.1.2
        (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) (topSecret b l)) ∧
      DeterministicSigning.Resolves (SigningDescentProof.thView z.1.2)
        (XmssSecurity.Concrete.honestKeygen x.1 secret topSecret (fun _ _ => pure 0) :
          OracleComp XmssSecurity.HashSpec _) result := by
  have h := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.2
  unfold forestRun at h
  obtain ⟨secret, hsecret, h⟩ := h.of_bind
  obtain ⟨topSecret, htopSecret, h⟩ := h.of_bind
  obtain ⟨result, hforest, _⟩ := h.of_bind
  exact ⟨secret, topSecret, result,
    fun e l => (hsecret.of_sequenceFin e).of_sequenceFin l,
    fun b l => (htopSecret.of_sequenceFin b).of_sequenceFin l,
    resolves_forestHash _ _ _ hforest⟩

/-- Chain starts replayed from a threshold hash cache. -/
def replayStarts (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (layer : Layer) (key : KeyIndex) (chain : ChainIndex) : Digest :=
  D prims (SigningCacheProof.answersOf cache) (prfValue x.2.1 (.chain layer key chain (digit 0)))

/-- Each job of a resolved list has itself been resolved. -/
theorem resolves_mapM_member {α β : Type} {cache : HashCache C}
    (f : α → OracleComp (Query C →ₒ HashOutput) β) (xs : List α) (ys : List β)
    (h : DeterministicSigning.Resolves cache (xs.mapM f) ys) :
    ∀ a ∈ xs, ∃ b, DeterministicSigning.Resolves cache (f a) b := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := h.of_bind
    obtain ⟨bs, hbs, _⟩ := h.of_bind
    intro a' ha'
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨b, hb⟩
    · exact ih bs hbs a' ha'

/-- A resolved top ceremony has read every top chain start and its full chain. -/
theorem resolves_referenceTop_chains (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    ∃ start finish,
      DeterministicSigning.Resolves cache
        (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) start ∧
      DeterministicSigning.Resolves (SigningDescentProof.thView cache)
        (XmssSecurity.Concrete.topChainWalk x.1 b l 0 3 start :
          OracleComp XmssSecurity.HashSpec _) finish := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, _⟩ := h.of_bind
  obtain ⟨values, hvalues, _⟩ := houtputs.of_map
  let job : Job := ⟨.chainEnd (topKey b) l, [.chain topLayer (topKey b) l (digit 0)]⟩
  have hmem : job ∈ topJobs := by
    simp only [topJobs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨b, l, rfl⟩
  obtain ⟨bits, hjob⟩ := resolves_mapM_member _ _ values hvalues job hmem
  simp only [referenceJob, job, List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc] at hjob
  obtain ⟨start, hstart, htail⟩ := hjob.of_bind
  obtain ⟨finish, hfinish, _⟩ := htail.of_map
  refine ⟨start, finish, hstart, ?_⟩
  have hm := resolves_forestHash _ _ _ hfinish
  erw [XmssSecurity.Bridge.chainWalk_top] at hm
  exact hm

/-- All starts in an actually resolved top ceremony are stable under extension. -/
theorem resolves_referenceTop_starts (x : SigningSecurityProof.Keys3 C)
    (cache larger : HashCache C) (hle : cache ≤ larger) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    replayStarts prims x larger topLayer (topKey b) l =
      replayStarts prims x cache topLayer (topKey b) l := by
  obtain ⟨start, _, hs, _⟩ := resolves_referenceTop_chains x cache top h b l
  exact (resolves_forestValue prims cache larger hle _ _ _ hs).trans
    (resolves_forestValue prims cache cache le_rfl _ _ _ hs).symm

set_option maxRecDepth 100000 in
/-- The top ceremony also resolves the Merkle computation, with its actual
chain ends and root. -/
theorem resolves_referenceTop_merkle (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top))) :
    DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (merkleNode x.1 topLayer top.chainEnd layerHeight 0) top.root := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, htail⟩ := h.of_bind
  obtain ⟨values, _, rfl⟩ := houtputs.of_map
  obtain ⟨root, hroot, hfinal⟩ := htail.of_bind
  have he := hfinal.pure_inv
  have ht := TreeOutput.top.inj (Option.some.inj he)
  have hchain := congrArg TopTree.chainEnd ht
  have hr := congrArg TopTree.root ht
  rw [← hchain, ← hr]
  exact resolves_forestHash _ _ _ hroot

/-- Replaying a resolved ceremony returns the original top tree in every
extension, without imposing any distributional assumption on that extension. -/
theorem resolves_referenceTop_eval (x : SigningSecurityProof.Keys3 C)
    (cache larger : HashCache C) (hle : cache ≤ larger) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top))) :
    D prims (SigningCacheProof.answersOf larger)
      (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) = some (.top top) := by
  rw [← hashEmbed_referenceTree, eval_hashEmbed]
  exact h.eval _ (fun input output ho => by simp [SigningCacheProof.answersOf, hle ho])

set_option maxRecDepth 100000 in
/-- The public chain ends are the ends of these resolved chains, including the
indexing through the ceremony's flattened job list. -/
theorem resolves_referenceTop_chainEnds (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    top.chainEnd (topKey b) l =
      XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
        0 3 (replayStarts prims x cache topLayer (topKey b) l) := by
  have href := resolves_referenceTop_eval prims x cache cache le_rfl top h
  obtain ⟨top', href', hends, _⟩ :=
    D_refTop (prims := prims) (h := SigningCacheProof.answersOf cache) x.1 x.2.1 emptyTop
  have ht : top' = top := TreeOutput.top.inj (Option.some.inj (href'.symm.trans href))
  subst top'
  rw [hends b l]
  exact SigningCacheProof.E_chainWalk_top prims cache x.1 b l 0 3 _

/-- The endpoint in the resolution certificate is exactly the endpoint handed
to the adversary in the real top tree. -/
theorem resolves_referenceTop_modelChains (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (XmssSecurity.Concrete.topChainWalk x.1 b l 0 3
        (replayStarts prims x cache topLayer (topKey b) l) : OracleComp XmssSecurity.HashSpec _)
      (top.chainEnd (topKey b) l) := by
  obtain ⟨start, finish, hs, hw⟩ := resolves_referenceTop_chains x cache top h b l
  have he := resolves_forestValue prims cache cache le_rfl _ _ _ hs
  change replayStarts prims x cache topLayer (topKey b) l = start at he
  rw [he]
  have hv := SigningCacheProof.resolves_value hw
  rw [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk] at hv
  have hend := resolves_referenceTop_chainEnds prims x cache top h b l
  rw [he] at hend
  exact (hv.symm.trans hend.symm) ▸ hw

theorem resolves_topChainWalk_prefix (cache : QueryCache XmssSecurity.HashSpec)
    (P : XmssSecurity.PublicParameter) (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex)
    (start : Digest) : ∀ n finish,
      DeterministicSigning.Resolves cache
        (XmssSecurity.Concrete.topChainWalk P b l 0 n start : OracleComp XmssSecurity.HashSpec _) finish →
      ∀ k ≤ n, ∃ value, DeterministicSigning.Resolves cache
        (XmssSecurity.Concrete.topChainWalk P b l 0 k start : OracleComp XmssSecurity.HashSpec _) value := by
  intro n
  induction n with
  | zero =>
    intro finish h k hk
    have he : k = 0 := by omega
    subst k
    exact ⟨finish, h⟩
  | succ n ih =>
    intro finish h k hk
    by_cases hkn : k ≤ n
    · rw [XmssSecurity.Concrete.topChainWalk] at h
      obtain ⟨prev, hp, _⟩ := h.of_bind
      exact ih prev hp k hkn
    · have he : k = n + 1 := by omega
      subst k
      exact ⟨finish, h⟩

/-- Every intermediate top-chain value is stable, not just its endpoint. -/
theorem resolves_referenceTop_walks (x : SigningSecurityProof.Keys3 C)
    (cache larger : HashCache C) (hle : cache ≤ larger) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) (k : ℕ) (hk : k ≤ 3) :
    XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView larger) x.1 b l)
      0 k (replayStarts prims x larger topLayer (topKey b) l) =
    XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
      0 k (replayStarts prims x cache topLayer (topKey b) l) := by
  obtain ⟨value, hv⟩ := resolves_topChainWalk_prefix _ _ _ _ _ 3 _
    (resolves_referenceTop_modelChains prims x cache top h b l) k hk
  have hsmall := SigningCacheProof.resolves_value hv
  have hlarge := SigningCacheProof.resolves_value (hv.mono (SigningCacheProof.thView_mono hle))
  rw [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk] at hsmall hlarge
  rw [resolves_referenceTop_starts prims x cache larger hle top h b l]
  exact hlarge.trans hsmall.symm

set_option maxRecDepth 100000 in
/-- A bottom ceremony resolves all its chain starts and complete chains even
if its later grinding step returns `none`. -/
theorem resolves_referenceBottom_chains (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (b k : Fin (2 ^ layerHeight))
    (output : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output)
    (l : ChainIndex) :
    ∃ start finish,
      DeterministicSigning.Resolves cache
        (forestValue x.2.1 (.chain bottomLayer (bottomKey b k) l (digit 0))) start ∧
      DeterministicSigning.Resolves (SigningDescentProof.thView cache)
        (XmssSecurity.Concrete.chainWalk x.1 (bottomKey b k) l 0 3 start :
          OracleComp XmssSecurity.HashSpec _) finish := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, _⟩ := h.of_bind
  obtain ⟨values, hvalues, _⟩ := houtputs.of_map
  let job : Job := ⟨.chainRow (bottomKey b k) l,
    [.chain bottomLayer (bottomKey b k) l (digit 0),
      .chain bottomLayer (bottomKey b k) l (digit 1),
      .chain bottomLayer (bottomKey b k) l (digit 2)]⟩
  have hmem : job ∈ bottomJobs b := by
    simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact Or.inl (Or.inl ⟨k, l, rfl⟩)
  obtain ⟨bits, hjob⟩ := resolves_mapM_member _ _ values hvalues job hmem
  dsimp only [referenceJob, job] at hjob
  obtain ⟨starts, hstarts, htail⟩ := hjob.of_bind
  obtain ⟨start, hs⟩ := resolves_mapM_member (forestValue x.2.1) _ starts hstarts
    (.chain bottomLayer (bottomKey b k) l (digit 0)) (by simp)
  have hvs := hstarts.eval (SigningCacheProof.answersOf cache)
    (fun input output ho => by simp [SigningCacheProof.answersOf, ho])
  rw [eval_mapM] at hvs
  have hhead : starts.getD 0 0 = start := by
    rw [← hvs]
    exact hs.eval _ (fun input output ho => by simp [SigningCacheProof.answersOf, ho])
  obtain ⟨y₁, _, htail⟩ := htail.of_bind
  obtain ⟨y₂, _, htail⟩ := htail.of_bind
  obtain ⟨finish, hfinish, _⟩ := htail.of_bind
  refine ⟨start, finish, hs, ?_⟩
  have hm := resolves_forestHash _ _ _ hfinish
  rw [hhead] at hm
  erw [XmssSecurity.Bridge.chainWalk_bottom] at hm
  exact hm

theorem resolves_chainWalk_prefix (cache : QueryCache XmssSecurity.HashSpec)
    (P : XmssSecurity.PublicParameter) (b : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex)
    (start : Digest) : ∀ n finish,
      DeterministicSigning.Resolves cache
        (XmssSecurity.Concrete.chainWalk P b l 0 n start : OracleComp XmssSecurity.HashSpec _) finish →
      ∀ k ≤ n, ∃ value, DeterministicSigning.Resolves cache
        (XmssSecurity.Concrete.chainWalk P b l 0 k start : OracleComp XmssSecurity.HashSpec _) value := by
  intro n
  induction n with
  | zero =>
    intro finish h k hk
    have he : k = 0 := by omega
    subst k
    exact ⟨finish, h⟩
  | succ n ih =>
    intro finish h k hk
    by_cases hkn : k ≤ n
    · rw [XmssSecurity.Concrete.chainWalk] at h
      obtain ⟨prev, hp, _⟩ := h.of_bind
      exact ih prev hp k hkn
    · have he : k = n + 1 := by omega
      subst k
      exact ⟨finish, h⟩

/-- The structural bottom prefix fixes every intermediate chain value, also
when the ceremony later fails its grinding step. -/
theorem resolves_referenceBottom_walks (x : SigningSecurityProof.Keys3 C)
    (cache larger : HashCache C) (hle : cache ≤ larger) (top : TopTree)
    (b k : Fin (2 ^ layerHeight)) (output : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output)
    (l : ChainIndex) (n : ℕ) (hn : n ≤ 3) :
    XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView larger) x.1 (bottomKey b k) l)
      0 n (replayStarts prims x larger bottomLayer (bottomKey b k) l) =
    XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView cache) x.1 (bottomKey b k) l)
      0 n (replayStarts prims x cache bottomLayer (bottomKey b k) l) := by
  obtain ⟨start, finish, hs, hw⟩ := resolves_referenceBottom_chains x cache top b k output h l
  have hsmallStart := resolves_forestValue prims cache cache le_rfl _ _ _ hs
  have hlargeStart := resolves_forestValue prims cache larger hle _ _ _ hs
  change replayStarts prims x cache bottomLayer (bottomKey b k) l = start at hsmallStart
  change replayStarts prims x larger bottomLayer (bottomKey b k) l = start at hlargeStart
  obtain ⟨value, hv⟩ := resolves_chainWalk_prefix _ _ _ _ _ 3 finish hw n hn
  have hsmall := SigningCacheProof.resolves_value hv
  have hlarge := SigningCacheProof.resolves_value (hv.mono (SigningCacheProof.thView_mono hle))
  rw [XmssSecurity.Concrete.CacheReplay.eval_chainWalk] at hsmall hlarge
  rw [hsmallStart, hlargeStart]
  exact hlarge.trans hsmall.symm

set_option maxRecDepth 100000 in
/-- The bottom structural prefix resolves its complete Merkle tree before any
grinding or top-signature failure. Its leaves use the canonical chain ends. -/
theorem resolves_referenceBottom_merkle (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (output : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output) :
    ∃ ends root,
      DeterministicSigning.Resolves (SigningDescentProof.thView cache)
        (merkleNode x.1 bottomLayer ends layerHeight b.val) root ∧
      ∀ (k : Fin (2 ^ layerHeight)) (l : ChainIndex),
        ends (bottomKey b k) l =
          XmssSecurity.Wots.walk
            (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView cache) x.1
              (bottomKey b k) l) 0 3
            (replayStarts prims x cache bottomLayer (bottomKey b k) l) := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, htail⟩ := h.of_bind
  obtain ⟨values, hvalues, rfl⟩ := houtputs.of_map
  obtain ⟨root, hroot, _⟩ := htail.of_bind
  let ends : KeyIndex → ChainIndex → Digest := fun e l =>
    digestAt (values.getD ((bottomKeys b).idxOf (e, l)) []) 2
  have hmerkle : DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (merkleNode x.1 bottomLayer ends layerHeight b.val) root :=
    resolves_forestHash _ _ _ hroot
  refine ⟨ends, root, hmerkle, ?_⟩
  intro k l
  have hvs := hvalues.eval (SigningCacheProof.answersOf cache)
    (fun input output ho => by simp [SigningCacheProof.answersOf, ho])
  rw [eval_mapM] at hvs
  simp_rw [← eval_hashEmbed prims, hashEmbed_referenceJob] at hvs
  change bottomOutputs prims (SigningCacheProof.answersOf cache) x.2.1 x.1 b = values at hvs
  dsimp only [ends]
  rw [← hvs]
  exact (bottomOutputs_cpk (prims := prims) (h := SigningCacheProof.answersOf cache)
    x.2.1 x.1 b k l).2.2.trans (SigningCacheProof.E_chainWalk_bottom prims cache x.1
      (bottomKey b k) l 0 3 _)

/-- Resolving a Merkle root resolves every descendant computation, including
the leaves. The statement keeps the actual root index for a bottom subtree. -/
theorem resolves_merkleNode_descendant (cache : QueryCache HashSpec) (P : PublicParameter)
    (layer : Layer) (ends : KeyIndex → ChainIndex → Digest) (height node : ℕ) (root : Digest)
    (h : DeterministicSigning.Resolves cache (merkleNode P layer ends height node) root) :
    ∀ depth ≤ height, ∀ offset < 2 ^ depth, ∃ value,
      DeterministicSigning.Resolves cache
        (merkleNode P layer ends (height - depth) (node * 2 ^ depth + offset)) value := by
  intro depth
  induction depth with
  | zero =>
    intro _ offset hoff
    have he : offset = 0 := by simpa using hoff
    subst offset
    exact ⟨root, by simpa using h⟩
  | succ depth ih =>
    intro hd offset hoff
    have hp : offset / 2 < 2 ^ depth :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using hoff)
    obtain ⟨parent, hparent⟩ := ih (by omega) (offset / 2) hp
    have hl : height - depth = (height - (depth + 1)) + 1 := by omega
    rw [hl, merkleNode] at hparent
    obtain ⟨left, hleft, htail⟩ := hparent.of_bind
    obtain ⟨right, hright, _⟩ := htail.of_bind
    have hbase : node * 2 ^ (depth + 1) = 2 * (node * 2 ^ depth) := by rw [pow_succ]; ring
    by_cases heven : offset % 2 = 0
    · have hi : 2 * (node * 2 ^ depth + offset / 2) = node * 2 ^ (depth + 1) + offset := by
        rw [hbase]
        omega
      exact ⟨left, hi ▸ hleft⟩
    · have hi : 2 * (node * 2 ^ depth + offset / 2) + 1 = node * 2 ^ (depth + 1) + offset := by
        rw [hbase]
        omega
      exact ⟨right, hi ▸ hright⟩

/-- Fixed bottom endpoints remain canonical in every cache extension. -/
theorem resolves_referenceBottom_fixedEnds (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (output : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output) :
    ∃ ends root, DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (merkleNode x.1 bottomLayer ends 16 b.val) root ∧
      ∀ larger : HashCache C, cache ≤ larger → ∀ e : XmssSecurity.LeafIndex,
        e.val / 2 ^ 16 = b.val → ∀ l, ends e l =
          XmssSecurity.Wots.walk
            (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView larger) x.1 e l)
            0 3 (replayStarts prims x larger bottomLayer e l) := by
  obtain ⟨ends, root, hroot, hends⟩ := resolves_referenceBottom_merkle prims x cache top b output h
  refine ⟨ends, root, hroot, ?_⟩
  intro larger hle e he l
  let k : Fin (2 ^ layerHeight) := ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
  have hek : bottomKey b k = e := by
    apply Fin.ext
    simp only [bottomKey, k, ← he, layerHeight]
    exact Nat.div_add_mod _ _
  rw [← hek]
  exact (hends k l).trans (resolves_referenceBottom_walks prims x cache larger hle top b k output h l 3 le_rfl).symm

/-- Every index below a bottom root has the expected canonical replay. -/
theorem eval_merkleNode_in_bottom (cache : HashCache C) (P : PublicParameter)
    (ends : KeyIndex → ChainIndex → Digest)
    (starts : XmssSecurity.LeafIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (b : Fin (2 ^ layerHeight))
    (hends : ∀ e : XmssSecurity.LeafIndex, e.val / 2 ^ 16 = b.val → ∀ l,
      ends e l = XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView cache) P e l) 0 3 (starts e l))
    (level j : ℕ) (hl : level ≤ 16) (hj : j / 2 ^ (16 - level) = b.val) :
    evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn (SigningDescentProof.thView cache))
      (merkleNode P bottomLayer ends level j) =
    XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView cache) P starts level
      (XmssSecurity.Concrete.merkleNodeOfNat j) := by
  apply SigningCacheProof.eval_merkleNode_bottom _ _ _ _ level hl j
  · have hb : j / 2 ^ (16 - level) < 2 ^ 16 := by rw [hj]; exact b.isLt
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show 16 + (16 - level) = 32 - level by omega] at hb
    exact hb
  · intro e he l
    apply hends e _ l
    rw [show 16 = level + (16 - level) by omega, pow_add,
      ← Nat.div_div_eq_div_mul, he]
    simpa only [show level + (16 - level) - level = 16 - level by omega] using hj

/-- The completed forest's starts agree with replay from every larger cache.
The model-tree transcript itself is resolved by the smaller honest record. -/
theorem forestRun_replay (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger) :
    ∃ result, DeterministicSigning.Resolves (SigningDescentProof.thView z.1.2)
      (XmssSecurity.Concrete.honestKeygen x.1
        (replayStarts prims x larger bottomLayer)
        (fun b => replayStarts prims x larger topLayer (topKey b))
        (fun _ _ => pure 0) : OracleComp XmssSecurity.HashSpec _) result := by
  obtain ⟨secret, topSecret, result, hsecret, htopSecret, hmodel⟩ := forestRun_resolves x cache z hz
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have hs : secret = replayStarts prims x larger bottomLayer := by
    funext e l
    exact (resolves_forestValue prims _ _ (hrecord.trans hle) _ _ _ (hsecret e l)).symm
  have ht : topSecret = fun b => replayStarts prims x larger topLayer (topKey b) := by
    funext b l
    exact (resolves_forestValue prims _ _ (hrecord.trans hle) _ _ _ (htopSecret b l)).symm
  rw [hs, ht] at hmodel
  exact ⟨result, hmodel⟩

/-- The recorded model forest is itself a supported replay from that record. -/
theorem forestRun_honestRun (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger) :
    ∃ result, (result, SigningDescentProof.thView z.1.2) ∈ support
      ((simulateQ XmssSecurity.HashSpec.randomOracle
        (XmssSecurity.Concrete.honestKeygen x.1
          (replayStarts prims x larger bottomLayer)
          (fun b => replayStarts prims x larger topLayer (topKey b))
          (fun _ _ => pure 0) : OracleComp XmssSecurity.HashSpec _)).run
        (SigningDescentProof.thView z.1.2)) := by
  obtain ⟨result, hmodel⟩ := forestRun_replay prims x cache z hz larger hle
  refine ⟨result, ?_⟩
  rw [hmodel.run_eq_pure]
  simp

/-- Every bottom chain input of the completed replay was actually read by the
completion, even if the oracle cache already contained adversarial queries. -/
theorem forestRun_chainInput (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (step : XmssSecurity.ChainStep) :
    ∃ output, SigningDescentProof.thView z.1.2
      (XmssSecurity.Concrete.CacheView.chainInput x.1 e l step
        (XmssSecurity.Wots.walk
          (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView larger) x.1 e l)
          0 step.val (replayStarts prims x larger bottomLayer e l))) = some output := by
  obtain ⟨result, hmem⟩ := forestRun_honestRun prims x cache z hz larger hle
  have hwalk := XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_chainWalk
    hmem e l (step.val + 1) (by have := step.isLt; omega)
  have hprefix := XmssSecurity.Concrete.CacheReplay.RunsBelow.chainWalk_prefix
    x.1 e l 0 (replayStarts prims x larger bottomLayer e l) _
    (step.val + 1) step.val (by omega) hwalk
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have heval := hprefix.eval_eq (SigningDescentProof.thView larger)
    (SigningCacheProof.thView_mono (hrecord.trans hle))
  rw [XmssSecurity.Concrete.CacheReplay.eval_chainWalk,
    XmssSecurity.Concrete.CacheReplay.eval_chainWalk] at heval
  rw [← heval]
  exact XmssSecurity.Concrete.CacheReplay.RunsBelow.chainInput_cached step hwalk

/-- The same record guarantee for the top chains. -/
theorem forestRun_topChainInput (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) (step : XmssSecurity.ChainStep) :
    ∃ output, SigningDescentProof.thView z.1.2
      (XmssSecurity.Concrete.CacheView.topChainInput x.1 b l step
        (XmssSecurity.Wots.walk
          (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView larger) x.1 b l)
          0 step.val (replayStarts prims x larger topLayer (topKey b) l))) = some output := by
  obtain ⟨result, hmem⟩ := forestRun_honestRun prims x cache z hz larger hle
  have hwalk := XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk
    hmem b l (step.val + 1) (by have := step.isLt; omega)
  have hprefix := XmssSecurity.Concrete.CacheReplay.RunsBelow.topChainWalk_prefix
    x.1 b l 0 (replayStarts prims x larger topLayer (topKey b) l) _
    (step.val + 1) step.val (by omega) hwalk
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have heval := hprefix.eval_eq (SigningDescentProof.thView larger)
    (SigningCacheProof.thView_mono (hrecord.trans hle))
  rw [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk,
    XmssSecurity.Concrete.CacheReplay.eval_topChainWalk] at heval
  rw [← heval]
  obtain ⟨before, after, value, hrun, hafter⟩ := hwalk
  obtain ⟨output, hcached⟩ :=
    XmssSecurity.Concrete.CacheReplay.topChainWalk_query_cached_in_largerCache
      x.1 b l 0 (step.val + 1) (replayStarts prims x larger topLayer (topKey b) l)
      step.val (by omega) (by have := step.isLt; omega) before after
      (SigningDescentProof.thView z.1.2) value hrun hafter
  have hstep : (⟨0 + step.val, by have := step.isLt; omega⟩ : XmssSecurity.ChainStep) = step :=
    Fin.ext (Nat.zero_add _)
  rw [hstep] at hcached
  exact ⟨output, hcached⟩

/-- Resolve a subtree from the honest completion record. -/
theorem forestRun_treeResolved (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (levels : ℕ) (node : XmssSecurity.MerkleNode) (hlevels : levels ≤ XmssSecurity.treeHeight)
    (hvalid : XmssSecurity.TreeSubtreeValid levels node) :
    ∃ value, DeterministicSigning.Resolves (SigningDescentProof.thView z.1.2)
      (XmssSecurity.Concrete.treeNode x.1 (replayStarts prims x larger bottomLayer)
        levels node : OracleComp XmssSecurity.HashSpec _) value := by
  obtain ⟨result, hmem⟩ := forestRun_honestRun prims x cache z hz larger hle
  obtain ⟨before, after, value, hrun, hafter⟩ :=
    XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_treeNode
      hmem levels node hlevels hvalid
  exact ⟨value, (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter⟩

/-- Resolve a top subtree from the same record. -/
theorem forestRun_topTreeResolved (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (levels : ℕ) (node : XmssSecurity.TopNode) (hlevels : levels ≤ XmssSecurity.treeHeight)
    (hvalid : node.val < 2 ^ (XmssSecurity.treeHeight - levels)) :
    ∃ value, DeterministicSigning.Resolves (SigningDescentProof.thView z.1.2)
      (XmssSecurity.Concrete.topTreeNode x.1
        (fun b => replayStarts prims x larger topLayer (topKey b))
        levels node : OracleComp XmssSecurity.HashSpec _) value := by
  obtain ⟨result, hmem⟩ := forestRun_honestRun prims x cache z hz larger hle
  obtain ⟨before, after, value, hrun, hafter⟩ :=
    XmssSecurity.Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode
      hmem levels node hlevels hvalid
  exact ⟨value, (DeterministicSigning.resolves_of_run _ before (value, after) hrun).mono hafter⟩

/-- Every completed bottom leaf input occurs in the honest record. -/
theorem forestRun_leafInput (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger) (e : XmssSecurity.LeafIndex) :
    (SigningDescentProof.thView z.1.2 (XmssSecurity.Concrete.CacheView.leafInput x.1 e
      (XmssSecurity.Concrete.CacheReplay.oneTimePublicKey (SigningDescentProof.thView larger)
        x.1 (replayStarts prims x larger bottomLayer) e))).isSome := by
  obtain ⟨value, hleaf⟩ := forestRun_treeResolved prims x cache z hz larger hle 0 e
    (by omega) (by simpa [XmssSecurity.TreeSubtreeValid] using e.isLt)
  rw [XmssSecurity.Concrete.treeNode_zero_eq, XmssSecurity.Concrete.leafAt] at hleaf
  obtain ⟨ends, hends, hhash⟩ := hleaf.of_bind
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have heval := SigningCacheProof.resolves_value
    (hends.mono (SigningCacheProof.thView_mono (hrecord.trans hle)))
  rw [XmssSecurity.Concrete.CacheReplay.eval_oneTimePublicKey] at heval
  rw [heval]
  exact SigningCacheProof.resolves_tweakableHash hhash

/-- Every completed top leaf input occurs in the honest record. -/
theorem forestRun_topLeafInput (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger) (b : XmssSecurity.TopIndex) :
    (SigningDescentProof.thView z.1.2 (XmssSecurity.Concrete.CacheView.topLeafInput x.1 b
      (XmssSecurity.Concrete.CacheReplay.topOneTimePublicKey (SigningDescentProof.thView larger)
        x.1 (fun k => replayStarts prims x larger topLayer (topKey k)) b))).isSome := by
  obtain ⟨value, hleaf⟩ := forestRun_topTreeResolved prims x cache z hz larger hle 0 b
    (by omega) (by simpa [XmssSecurity.topLifetime, XmssSecurity.treeHeight] using b.isLt)
  rw [XmssSecurity.Concrete.topTreeNode, XmssSecurity.Concrete.topLeafAt] at hleaf
  obtain ⟨ends, hends, hhash⟩ := hleaf.of_bind
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have heval := SigningCacheProof.resolves_value
    (hends.mono (SigningCacheProof.thView_mono (hrecord.trans hle)))
  have heval' : XmssSecurity.Concrete.CacheReplay.topOneTimePublicKey
      (SigningDescentProof.thView larger) x.1
      (fun k => replayStarts prims x larger topLayer (topKey k)) b = ends := by
    unfold XmssSecurity.Concrete.CacheReplay.topOneTimePublicKey
    simpa [XmssSecurity.Concrete.topOneTimePublicKey] using heval
  rw [heval']
  exact SigningCacheProof.resolves_tweakableHash hhash

/-- A completed bottom Merkle node records its actual pair of children. -/
theorem forestRun_merkleInput (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (level : XmssSecurity.MerkleLevel) (node : XmssSecurity.MerkleNode)
    (hvalid : XmssSecurity.TreeSubtreeValid (level.val + 1) node) :
    (SigningDescentProof.thView z.1.2
      (XmssSecurity.Concrete.CacheView.merkleInput x.1 level node
        (XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView larger) x.1
          (replayStarts prims x larger bottomLayer) level.val (XmssSecurity.Concrete.childNode node false))
        (XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView larger) x.1
          (replayStarts prims x larger bottomLayer) level.val (XmssSecurity.Concrete.childNode node true)))).isSome := by
  obtain ⟨value, hnode⟩ := forestRun_treeResolved prims x cache z hz larger hle
    (level.val + 1) node level.isLt hvalid
  rw [XmssSecurity.Concrete.treeNode_succ_eq] at hnode
  obtain ⟨left, hleft, hrest⟩ := hnode.of_bind
  obtain ⟨right, hright, hhash⟩ := hrest.of_bind
  simp only [level.isLt, ↓reduceDIte] at hhash
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have hview := SigningCacheProof.thView_mono (hrecord.trans hle)
  have hl := SigningCacheProof.resolves_value (hleft.mono hview)
  have hr := SigningCacheProof.resolves_value (hright.mono hview)
  rw [XmssSecurity.Concrete.CacheReplay.eval_treeNode] at hl hr
  rw [hl, hr]
  exact SigningCacheProof.resolves_tweakableHash hhash

/-- A completed top Merkle node records its actual pair of children. -/
theorem forestRun_topMerkleInput (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (level : XmssSecurity.MerkleLevel) (node : XmssSecurity.TopNode)
    (hvalid : node.val < 2 ^ (XmssSecurity.treeHeight - (level.val + 1))) :
    (SigningDescentProof.thView z.1.2
      (XmssSecurity.Concrete.CacheView.topMerkleInput x.1 level node
        (XmssSecurity.Concrete.CacheReplay.topTreeNode (SigningDescentProof.thView larger) x.1
          (fun b => replayStarts prims x larger topLayer (topKey b)) level.val
          (XmssSecurity.Concrete.topChildNode node false))
        (XmssSecurity.Concrete.CacheReplay.topTreeNode (SigningDescentProof.thView larger) x.1
          (fun b => replayStarts prims x larger topLayer (topKey b)) level.val
          (XmssSecurity.Concrete.topChildNode node true)))).isSome := by
  obtain ⟨value, hnode⟩ := forestRun_topTreeResolved prims x cache z hz larger hle
    (level.val + 1) node level.isLt hvalid
  rw [XmssSecurity.Concrete.topTreeNode] at hnode
  obtain ⟨left, hleft, hrest⟩ := hnode.of_bind
  obtain ⟨right, hright, hhash⟩ := hrest.of_bind
  simp only [level.isLt, ↓reduceDIte] at hhash
  have hrecord := (recordReads_resolves (forestRun x) ∅ cache
    (by intro input output hh; cases hh) z hz).2.2.1
  have hview := SigningCacheProof.thView_mono (hrecord.trans hle)
  have hl := SigningCacheProof.resolves_value (hleft.mono hview)
  have hr := SigningCacheProof.resolves_value (hright.mono hview)
  rw [XmssSecurity.Concrete.CacheReplay.eval_topTreeNode] at hl hr
  rw [hl, hr]
  exact SigningCacheProof.resolves_tweakableHash hhash

/-- The structural addresses that occur in the finite honest forest. -/
def ForestDomain : XmssSecurity.HashDomain → Prop
  | .chain _ _ _ | .leaf _ | .topChain _ _ _ | .topLeaf _ => True
  | .merkle level node => XmssSecurity.TreeSubtreeValid (level.val + 1) node
  | .topMerkle level node => node.val < 2 ^ (XmssSecurity.treeHeight - (level.val + 1))
  | .encoding _ | .topEncoding _ => False

/-- The payload at a structural address in the deterministic forest replay. -/
def forestPayload (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) :
    XmssSecurity.HashDomain → XmssSecurity.HashInput
  | .chain e l step => XmssSecurity.Concrete.digestBytes
      (XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.chainStep (SigningDescentProof.thView cache) x.1 e l)
        0 step.val (replayStarts prims x cache bottomLayer e l))
  | .leaf e => XmssSecurity.Concrete.leafPayload
      (XmssSecurity.Concrete.CacheReplay.oneTimePublicKey (SigningDescentProof.thView cache)
        x.1 (replayStarts prims x cache bottomLayer) e)
  | .merkle level node => XmssSecurity.Concrete.nodePayload
      (XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView cache) x.1
        (replayStarts prims x cache bottomLayer) level.val (XmssSecurity.Concrete.childNode node false))
      (XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView cache) x.1
        (replayStarts prims x cache bottomLayer) level.val (XmssSecurity.Concrete.childNode node true))
  | .topChain b l step => XmssSecurity.Concrete.digestBytes
      (XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
        0 step.val (replayStarts prims x cache topLayer (topKey b) l))
  | .topLeaf b => XmssSecurity.Concrete.leafPayload
      (XmssSecurity.Concrete.CacheReplay.topOneTimePublicKey (SigningDescentProof.thView cache)
        x.1 (fun k => replayStarts prims x cache topLayer (topKey k)) b)
  | .topMerkle level node => XmssSecurity.Concrete.nodePayload
      (XmssSecurity.Concrete.CacheReplay.topTreeNode (SigningDescentProof.thView cache) x.1
        (fun b => replayStarts prims x cache topLayer (topKey b)) level.val
        (XmssSecurity.Concrete.topChildNode node false))
      (XmssSecurity.Concrete.CacheReplay.topTreeNode (SigningDescentProof.thView cache) x.1
        (fun b => replayStarts prims x cache topLayer (topKey b)) level.val
        (XmssSecurity.Concrete.topChildNode node true))
  | .encoding _ | .topEncoding _ => []

/-- Structural positions inside one bottom tree, including its root. -/
def BottomDomain (b : Fin (2 ^ layerHeight)) : XmssSecurity.HashDomain → Prop
  | .chain e _ _ | .leaf e => e.val / 2 ^ 16 = b.val
  | .merkle level node => node.val / 2 ^ (16 - (level.val + 1)) = b.val
  | _ => False

/-- A target was actually read and its payload is unchanged by any extension. -/
def StableForestTarget (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (domain : XmssSecurity.HashDomain) : Prop :=
  (cache (.hash (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x cache domain)))).isSome ∧
  ∀ larger : HashCache C, cache ≤ larger →
    forestPayload prims x larger domain = forestPayload prims x cache domain

theorem bottom_child_index (b j level bit : ℕ) (hl : level < 16) (hbit : bit < 2)
    (hj : j / 2 ^ (16 - (level + 1)) = b) :
    (2 * j + bit) / 2 ^ (16 - level) = b := by
  have hc : (2 * j + bit) / 2 = j := by omega
  rw [show 16 - level = 1 + (16 - (level + 1)) by omega, pow_add,
    ← Nat.div_div_eq_div_mul]
  simpa only [pow_one, hc] using hj

set_option maxRecDepth 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every target in a completed bottom ceremony is stable, even if its output
is `none`. This uses the actual structural reads before grinding. -/
theorem resolves_referenceBottom_targets (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (output : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom b)) output)
    (domain : XmssSecurity.HashDomain) (hd : BottomDomain b domain) :
    StableForestTarget prims x cache domain := by
  cases domain with
  | chain e l step =>
    change e.val / 2 ^ 16 = b.val at hd
    let k : Fin (2 ^ layerHeight) := ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
    have hek : bottomKey b k = e := by
      apply Fin.ext
      simp only [bottomKey, k, ← hd, layerHeight]
      exact Nat.div_add_mod _ _
    obtain ⟨start, finish, hs, hw⟩ := resolves_referenceBottom_chains x cache top b k output h l
    have hstart := resolves_forestValue prims cache cache le_rfl _ _ _ hs
    change replayStarts prims x cache bottomLayer (bottomKey b k) l = start at hstart
    rw [hek] at hstart hw
    constructor
    · have hc := SigningCacheProof.resolves_chainWalk 0 start 3 finish hw step.val
        (Nat.zero_le _) step.isLt step.isLt
      rw [← hstart] at hc
      simpa only [Nat.sub_zero, SigningDescentProof.thView, XmssSecurity.Concrete.CacheView.chainInput,
        forestPayload] using hc
    · intro larger hle
      have he := resolves_referenceBottom_walks prims x cache larger hle top b k output h l
        step.val (Nat.le_of_lt step.isLt)
      rw [hek] at he
      exact congrArg XmssSecurity.Concrete.digestBytes he
  | leaf e =>
    change e.val / 2 ^ 16 = b.val at hd
    obtain ⟨ends, root, hroot, hends⟩ := resolves_referenceBottom_fixedEnds prims x cache top b output h
    obtain ⟨value, hv⟩ := resolves_merkleNode_descendant _ _ _ _ 16 b.val root hroot
      16 le_rfl (e.val % 2 ^ 16) (Nat.mod_lt _ (by decide))
    have hi : b.val * 2 ^ 16 + e.val % 2 ^ 16 = e.val := by
      rw [← hd]
      simpa only [Nat.mul_comm] using Nat.div_add_mod e.val (2 ^ 16)
    rw [Nat.sub_self, hi, merkleNode, SigningCacheProof.leafKey_bottom] at hv
    have he : XmssSecurity.Concrete.merkleNodeOfNat e.val = e := Fin.ext (Nat.mod_eq_of_lt e.isLt)
    rw [he, XmssSecurity.Bridge.leafHash_bottom] at hv
    have hp : ∀ larger : HashCache C, cache ≤ larger →
        forestPayload prims x larger (.leaf e) = XmssSecurity.Concrete.leafPayload (ends e) := by
      intro larger hle
      exact congrArg XmssSecurity.Concrete.leafPayload
        (funext (fun l => (hends larger hle e hd l).symm))
    constructor
    · rw [hp cache le_rfl]
      exact SigningCacheProof.resolves_tweakableHash hv
    · intro larger hle
      exact (hp larger hle).trans (hp cache le_rfl).symm
  | merkle level node =>
    change node.val / 2 ^ (16 - (level.val + 1)) = b.val at hd
    obtain ⟨ends, root, hroot, hends⟩ := resolves_referenceBottom_fixedEnds prims x cache top b output h
    obtain ⟨value, hv⟩ := resolves_merkleNode_descendant _ _ _ _ 16 b.val root hroot
      (16 - (level.val + 1)) (by omega) (node.val % 2 ^ (16 - (level.val + 1)))
      (Nat.mod_lt _ (by positivity))
    have hl : level.val < 16 := level.isLt
    have hi : b.val * 2 ^ (16 - (level.val + 1)) + node.val % 2 ^ (16 - (level.val + 1)) = node.val := by
      rw [← hd]
      simpa only [Nat.mul_comm] using Nat.div_add_mod node.val (2 ^ (16 - (level.val + 1)))
    rw [show 16 - (16 - (level.val + 1)) = level.val + 1 by omega, hi, merkleNode] at hv
    obtain ⟨left, hleft, hv⟩ := hv.of_bind
    obtain ⟨right, hright, hv⟩ := hv.of_bind
    rw [XmssSecurity.Bridge.nodeHash_bottom x.1 level node] at hv
    have hp : ∀ larger : HashCache C, cache ≤ larger →
        forestPayload prims x larger (.merkle level node) = XmssSecurity.Concrete.nodePayload left right := by
      intro larger hle
      have hleftv := SigningCacheProof.resolves_value (hleft.mono (SigningCacheProof.thView_mono hle))
      have hrightv := SigningCacheProof.resolves_value (hright.mono (SigningCacheProof.thView_mono hle))
      rw [eval_merkleNode_in_bottom larger x.1 ends _ b (hends larger hle) level.val (2 * node.val)
        (by omega) (by simpa using bottom_child_index b.val node.val level.val 0 hl (by decide) hd)] at hleftv
      rw [eval_merkleNode_in_bottom larger x.1 ends _ b (hends larger hle) level.val (2 * node.val + 1)
        (by omega) (bottom_child_index b.val node.val level.val 1 hl (by decide) hd)] at hrightv
      change XmssSecurity.Concrete.nodePayload
        (XmssSecurity.Concrete.CacheReplay.treeNode _ _ _ _ (XmssSecurity.Concrete.childNode node false))
        (XmssSecurity.Concrete.CacheReplay.treeNode _ _ _ _ (XmssSecurity.Concrete.childNode node true)) = _
      exact congrArg₂ XmssSecurity.Concrete.nodePayload hleftv hrightv
    constructor
    · rw [hp cache le_rfl]
      exact SigningCacheProof.resolves_tweakableHash hv
    · intro larger hle
      exact (hp larger hle).trans (hp cache le_rfl).symm
  | topChain _ _ _ | topLeaf _ | topMerkle _ _ | encoding _ | topEncoding _ => cases hd

def TopDomain : XmssSecurity.HashDomain → Prop
  | .topChain _ _ _ | .topLeaf _ => True
  | .topMerkle level node => node.val < 2 ^ (16 - (level.val + 1))
  | _ => False

set_option maxRecDepth 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- All top structural addresses are fixed by the key-generation prefix. -/
theorem resolves_referenceTop_targets (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (domain : XmssSecurity.HashDomain)
    (hd : TopDomain domain) : StableForestTarget prims x cache domain := by
  have hends : ∀ larger : HashCache C, cache ≤ larger → ∀ b l,
      top.chainEnd (topKey b) l = XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView larger) x.1 b l)
        0 3 (replayStarts prims x larger topLayer (topKey b) l) :=
    fun larger hle => resolves_referenceTop_chainEnds prims x larger top (h.mono hle)
  cases domain with
  | topChain b l step =>
    have hw := resolves_referenceTop_modelChains prims x cache top h b l
    constructor
    · exact SigningCacheProof.resolves_topChainWalk 0 _ 3 _ hw step.val
        (Nat.zero_le _) step.isLt step.isLt
    · intro larger hle
      exact congrArg XmssSecurity.Concrete.digestBytes
        (resolves_referenceTop_walks prims x cache larger hle top h b l step.val (Nat.le_of_lt step.isLt))
  | topLeaf b =>
    have hroot := resolves_referenceTop_merkle x cache top h
    obtain ⟨value, hv⟩ := resolves_merkleNode_descendant _ _ _ _ 16 0 top.root hroot
      16 le_rfl b.val b.isLt
    simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add, merkleNode] at hv
    have he : (⟨b.val % lifetime, Nat.mod_lt _ (by decide)⟩ : KeyIndex) = topKey b := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le b.isLt (by decide))
    rw [he] at hv
    erw [XmssSecurity.Bridge.leafHash_top] at hv
    have hp : ∀ larger : HashCache C, cache ≤ larger →
        forestPayload prims x larger (.topLeaf b) = XmssSecurity.Concrete.leafPayload (top.chainEnd (topKey b)) :=
      fun larger hle => congrArg XmssSecurity.Concrete.leafPayload (funext (fun l => (hends larger hle b l).symm))
    constructor
    · rw [hp cache le_rfl]
      exact SigningCacheProof.resolves_tweakableHash hv
    · intro larger hle
      exact (hp larger hle).trans (hp cache le_rfl).symm
  | topMerkle level node =>
    change node.val < 2 ^ (16 - (level.val + 1)) at hd
    have hroot := resolves_referenceTop_merkle x cache top h
    obtain ⟨value, hv⟩ := resolves_merkleNode_descendant _ _ _ _ 16 0 top.root hroot
      (16 - (level.val + 1)) (by omega) node.val hd
    have hl : level.val < 16 := level.isLt
    simp only [Nat.zero_mul, Nat.zero_add, show 16 - (16 - (level.val + 1)) = level.val + 1 by omega,
      merkleNode] at hv
    obtain ⟨left, hleft, hv⟩ := hv.of_bind
    obtain ⟨right, hright, hv⟩ := hv.of_bind
    rw [XmssSecurity.Bridge.nodeHash_top x.1 level node] at hv
    have hrightlt : 2 * node.val + 1 < 2 ^ (16 - level.val) := by
      rw [show 16 - level.val = (16 - (level.val + 1)) + 1 by omega, pow_succ]
      omega
    have hp : ∀ larger : HashCache C, cache ≤ larger →
        forestPayload prims x larger (.topMerkle level node) = XmssSecurity.Concrete.nodePayload left right := by
      intro larger hle
      have hleftv := SigningCacheProof.resolves_value (hleft.mono (SigningCacheProof.thView_mono hle))
      have hrightv := SigningCacheProof.resolves_value (hright.mono (SigningCacheProof.thView_mono hle))
      rw [SigningCacheProof.eval_merkleNode_top _ _ _ _ (hends larger hle) level.val (by omega)
        (2 * node.val) (by omega)] at hleftv
      rw [SigningCacheProof.eval_merkleNode_top _ _ _ _ (hends larger hle) level.val (by omega)
        (2 * node.val + 1) hrightlt] at hrightv
      exact congrArg₂ XmssSecurity.Concrete.nodePayload hleftv hrightv
    constructor
    · rw [hp cache le_rfl]
      exact SigningCacheProof.resolves_tweakableHash hv
    · intro larger hle
      exact (hp larger hle).trans (hp cache le_rfl).symm
  | chain _ _ _ | leaf _ | merkle _ _ | encoding _ | topEncoding _ => cases hd

/-- All six kinds of honest structural input are in the completion record. -/
theorem forestRun_payload (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (larger : HashCache C) (hle : z.2 ≤ larger)
    (domain : XmssSecurity.HashDomain) (hdomain : ForestDomain domain) :
    (z.1.2 (.hash (XmssSecurity.tweakableHashInput x.1 domain
      (forestPayload prims x larger domain)))).isSome := by
  cases domain with
  | chain e l step =>
      obtain ⟨output, ho⟩ := forestRun_chainInput prims x cache z hz larger hle e l step
      exact congrArg Option.isSome ho
  | leaf e => exact forestRun_leafInput prims x cache z hz larger hle e
  | merkle level node => exact forestRun_merkleInput prims x cache z hz larger hle level node hdomain
  | encoding _ => exact hdomain.elim
  | topChain b l step =>
      obtain ⟨output, ho⟩ := forestRun_topChainInput prims x cache z hz larger hle b l step
      exact congrArg Option.isSome ho
  | topLeaf b => exact forestRun_topLeafInput prims x cache z hz larger hle b
  | topMerkle level node => exact forestRun_topMerkleInput prims x cache z hz larger hle level node hdomain
  | topEncoding _ => exact hdomain.elim

/-- The complete threshold forest makes at most one query per structural
address, even though its chain starts are chosen by earlier oracle answers. -/
theorem forestRun_bound (x : SigningSecurityProof.Keys3 C)
    (domain : XmssSecurity.HashDomain) (hs : StructuralDomain domain) :
    (forestRun x).IsQueryBoundP (forestAddress x.1 domain) 1 := by
  classical
  unfold forestRun
  apply isQueryBoundP_bind (n := 0) (m := 1)
  · apply sequenceFin_bound_zero
    intro e
    exact sequenceFin_bound_zero _ _ (fun l => forestValue_bound _ _ _ _)
  · intro secret _
    apply isQueryBoundP_bind (n := 0) (m := 1)
    · apply sequenceFin_bound_zero
      intro b
      exact sequenceFin_bound_zero _ _ (fun l => forestValue_bound _ _ _ _)
    · intro topSecret _
      exact isQueryBoundP_bind (n := 1) (m := 0) (forestHash_bound _ _ _ 1
        (modelForest_bound x.1 secret topSecret domain hs)) (fun _ _ => by simp)

theorem sameStructuralPosition_atAddress (P : PublicParameter) (domain : XmssSecurity.HashDomain)
    (input honest : Query C) (hpos : SameStructuralPosition P input honest)
    (ha : forestAddress P domain input) : forestAddress P domain honest := by
  obtain ⟨otherDomain, payload, honestPayload, _, rfl, rfl⟩ := hpos
  simp only [forestAddress, XmssSecurity.atHashAddress_tweakableHashInput_iff] at ha ⊢
  exact ha

theorem sameStructuralPosition_relevant (P : PublicParameter) (input honest : Query C)
    (hpos : SameStructuralPosition P input honest) : forestRelevant P input := by
  obtain ⟨domain, payload, honestPayload, hs, hi, hh⟩ := hpos
  exact ⟨domain, payload, payload, hs, hi, hi⟩

/-- Even when started on an adversarial cache, the completion records at most
one input at every structural position. Chain suffixes are included in the address. -/
theorem forestRun_unique (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (input left right : Query C) (lv rv : HashOutput)
    (hl : SameStructuralPosition x.1 input left) (hr : SameStructuralPosition x.1 input right)
    (hleft : z.1.2 left = some lv) (hright : z.1.2 right = some rv) : left = right := by
  obtain ⟨domain, payload, leftPayload, hs, rfl, rfl⟩ := hl
  have ha : forestAddress x.1 domain (.hash (XmssSecurity.tweakableHashInput x.1 domain payload) : Query C) := by
    simp [forestAddress]
  have har := sameStructuralPosition_atAddress x.1 domain _ right hr ha
  exact recordReads_bound_one (forestRun x) (forestAddress x.1 domain)
    (forestRun_bound x domain hs) ∅ cache (fun _ _ => rfl) z hz _ right lv rv
    (by simp [forestAddress]) har hleft hright

open Classical in
/-- Select a target from the completion's record at the input's structural
position. The record contains only reads of the honest forest computation. -/
def forestTargets (P : PublicParameter) (record : HashCache C) : CompletionTargets C :=
  fun input => if h : ∃ r : Query C × HashOutput,
      SameStructuralPosition P input r.1 ∧ record r.1 = some r.2 then
    let r := Classical.choose h
    (r.1, truncateHash r.2)
  else (input, 0)

/-- A unique honest read at a position is exactly the target selected there. -/
theorem forestTargets_eq (P : PublicParameter) (record : HashCache C)
    (input honest : Query C) (output : HashOutput)
    (hpos : SameStructuralPosition P input honest) (hread : record honest = some output)
    (hunique : ∀ other value, SameStructuralPosition P input other →
      record other = some value → other = honest) :
    forestTargets P record input = (honest, truncateHash output) := by
  classical
  have hex : ∃ r : Query C × HashOutput,
      SameStructuralPosition P input r.1 ∧ record r.1 = some r.2 :=
    ⟨(honest, output), hpos, hread⟩
  rw [forestTargets, dif_pos hex]
  have hc := Classical.choose_spec hex
  have hi := hunique _ _ hc.1 hc.2
  have ho : (Classical.choose hex).2 = output := by
    rw [hi, hread] at hc
    exact Option.some.inj hc.2.symm
  simp only [hi, ho]

/-- A cached alternative colliding with an honest forest read survives the
recording filter and reaches the completion potential's terminal event. -/
theorem completedHit_forest_of_collision (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (input honest : Query C) (output honestOutput : HashOutput)
    (hc : cache input = some output) (hr : z.1.2 honest = some honestOutput)
    (hpos : SameStructuralPosition x.1 input honest) (hne : input ≠ honest)
    (heq : truncateHash output = truncateHash honestOutput) :
    CompletedHit (forestRelevant x.1) (recordedTargets (forestTargets x.1 z.1.2) z.1.2) cache := by
  have hrel := sameStructuralPosition_relevant x.1 input honest hpos
  have hunique : ∀ other value, SameStructuralPosition x.1 input other →
      z.1.2 other = some value → other = honest := by
    intro other value hp hv
    exact forestRun_unique x cache z hz input other honest value honestOutput hp hpos hv hr
  have hnone : z.1.2 input = none := by
    cases hi : z.1.2 input with
    | none => rfl
    | some value => exact (hne (hunique input value hrel hi)).elim
  have ht := forestTargets_eq x.1 z.1.2 input honest honestOutput hpos hr hunique
  apply (completedHit_recordedTargets _ _ _ _).mpr
  refine ⟨input, output, hc, hnone, hrel, ?_, ?_⟩
  · simpa only [ht] using hne
  · simpa only [ht] using heq

/-- A collision with the completed deterministic replay reaches the terminal
completion event. This covers every structural address and both query orders. -/
theorem completedHit_forest_of_replayCollision (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (domain : XmssSecurity.HashDomain) (hdomain : ForestDomain domain)
    (input : Query C) (output : HashOutput)
    (hc : cache input = some output)
    (hpos : SameStructuralPosition x.1 input
      (.hash (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x z.2 domain))))
    (hne : input ≠ .hash (XmssSecurity.tweakableHashInput x.1 domain
      (forestPayload prims x z.2 domain)))
    (heq : truncateHash output = truncateHash (SigningCacheProof.answersOf z.2
      (.hash (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x z.2 domain))))) :
    CompletedHit (forestRelevant x.1) (recordedTargets (forestTargets x.1 z.1.2) z.1.2) cache := by
  have hread := forestRun_payload prims x cache z hz z.2 le_rfl domain hdomain
  cases hr : z.1.2 (.hash (XmssSecurity.tweakableHashInput x.1 domain
      (forestPayload prims x z.2 domain))) with
  | none => simp [hr] at hread
  | some honestOutput =>
      have hrecord := (recordReads_resolves (forestRun x) ∅ cache
        (by intro input output hh; cases hh) z hz).2.2.1
      have hh := hrecord hr
      have heq' : truncateHash output = truncateHash honestOutput := by
        simpa only [SigningCacheProof.answersOf, hh, Option.getD_some] using heq
      exact completedHit_forest_of_collision x cache z hz input _ output honestOutput
        hc hr hpos hne heq'

/-- Honest completion cannot create a new alternative at one of its own
structural addresses. A collision in its final cache was already a candidate in
the starting cache and is therefore charged by the completion potential. -/
theorem completedHit_forest_of_completedCollision (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (z : (Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (recordReads (forestRun x) ∅)).run cache))
    (domain : XmssSecurity.HashDomain) (hdomain : ForestDomain domain)
    (input : Query C) (output : HashOutput)
    (hc : z.2 input = some output)
    (hpos : SameStructuralPosition x.1 input
      (.hash (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x z.2 domain))))
    (hne : input ≠ .hash (XmssSecurity.tweakableHashInput x.1 domain
      (forestPayload prims x z.2 domain)))
    (heq : truncateHash output = truncateHash (SigningCacheProof.answersOf z.2
      (.hash (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x z.2 domain))))) :
    CompletedHit (forestRelevant x.1) (recordedTargets (forestTargets x.1 z.1.2) z.1.2) cache := by
  have hread := forestRun_payload prims x cache z hz z.2 le_rfl domain hdomain
  have hnone : z.1.2 input = none := by
    cases hi : z.1.2 input with
    | none => rfl
    | some v =>
      cases hh : z.1.2 (.hash (XmssSecurity.tweakableHashInput x.1 domain
          (forestPayload prims x z.2 domain))) with
      | none => simp [hh] at hread
      | some w =>
        exact (hne (forestRun_unique x cache z hz input input _ v w
          (sameStructuralPosition_relevant _ _ _ hpos) hpos hi hh)).elim
  have hp := recordReads_preserves_unrecorded (forestRun x) cache ∅ cache
    (fun _ _ => rfl) z hz input hnone
  exact completedHit_forest_of_replayCollision prims x cache z hz domain hdomain
    input output (hp ▸ hc) hpos hne heq

def forestCompletion (x : SigningSecurityProof.Keys3 C) :
    OracleComp (Query C →ₒ HashOutput) (CompletionTargets C) :=
  recordedCompletion (forestRun x) (fun _ record => forestTargets x.1 record)

theorem forestCompletion_reads (x : SigningSecurityProof.Keys3 C) :
    CompletionReadsTargets (forestRelevant x.1) (forestCompletion x) :=
  recordedCompletion_reads _ _ _

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

/-- The exact total depth below the public endpoints required by a valid codeword. -/
theorem valid_encoding_deficit (encoding : XmssSecurity.Encoding)
    (hvalid : XmssSecurity.TargetSum.Valid encoding) :
    (∑ l, (3 - (encoding l).val)) = 68 := by
  have hle (l : XmssSecurity.ChainIndex) : (encoding l).val ≤ 3 := by
    have h := (encoding l).isLt
    norm_num [XmssSecurity.chainLength, XmssSecurity.winternitzBits] at h
    omega
  have hsum : (∑ l, (encoding l).val) = 106 := by
    simpa only [XmssSecurity.TargetSum.Valid, XmssSecurity.TargetSum.sum,
      XmssSecurity.targetSum] using hvalid
  have htotal : (∑ l, (3 - (encoding l).val)) + (∑ l, (encoding l).val) = 174 := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (hle _), XmssSecurity.numChains]
  omega

namespace MarkedChain

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

/-- The row law of leanVM's `PartialChainEndpoint`: cached rows are fixed,
and uncached rows are uniform. That package is not on this project's import path. -/
def rowLaw : Option State → PMF State
  | none => PMF.uniformOfFintype State
  | some value => PMF.pure value

/-- Keep a transition only when no queried alternative enters its output. -/
def rowWeight (observed : State → Option State) (input endpoint : State) : ℝ≥0∞ :=
  open Classical in
  if ∀ other, observed other = some endpoint → other = input then
    rowLaw (observed input) endpoint
  else 0

/-- Marking removes the extra preimage mass: every column has mass at most one. -/
theorem rowWeight_column (observed : State → Option State) (endpoint : State) :
    ∑ input, rowWeight observed input endpoint ≤ 1 := by
  classical
  by_cases hknown : ∃ input, observed input = some endpoint
  · obtain ⟨known, hk⟩ := hknown
    have hz : ∀ input ≠ known, rowWeight observed input endpoint = 0 := by
      intro input hi
      unfold rowWeight
      rw [if_neg (by intro h; exact hi (h known hk).symm)]
    rw [Finset.sum_eq_single known (by intro i _ hi; exact hz i hi) (by simp)]
    unfold rowWeight
    split
    · exact PMF.coe_le_one _ _
    · exact bot_le
  · have hb : ∀ input, rowWeight observed input endpoint ≤ (Fintype.card State : ℝ≥0∞)⁻¹ := by
      intro input
      unfold rowWeight
      split
      · cases ho : observed input with
        | none => simp [rowLaw]
        | some value =>
          have hv : endpoint ≠ value := by
            intro he; subst value; exact hknown ⟨input, ho⟩
          simp [rowLaw, PMF.pure_apply, hv]
      · exact bot_le
    calc
      _ ≤ ∑ _input : State, (Fintype.card State : ℝ≥0∞)⁻¹ := Finset.sum_le_sum (fun i _ => hb i)
      _ = 1 := by simp [ENNReal.mul_inv_cancel, Fintype.card_ne_zero]

/-- The marked walk uses the existing independent-row completion law. -/
def law : {n : ℕ} → (Fin n → State → Option State) → State → PMF (Option State)
  | 0, _, start => PMF.pure (some start)
  | _ + 1, observed, start =>
    open Classical in
    (rowLaw (observed 0 start)).bind fun next =>
      if ∀ other, observed 0 other = some next → other = start then
        law (Fin.tail observed) next
      else PMF.pure none

/-- Its transition formula retains the actual marked mass, without normalizing. -/
theorem law_succ_apply {n : ℕ} (observed : Fin (n + 1) → State → Option State)
    (start endpoint : State) :
    law observed start (some endpoint) =
      ∑ next, rowWeight (observed 0) start next * law (Fin.tail observed) next (some endpoint) := by
  classical
  rw [law, PMF.bind_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro next _
  by_cases h : ∀ other, observed 0 other = some next → other = start
  · simp only [rowWeight, if_pos h]
  · simp only [rowWeight, if_neg h, PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_mul]

/-- The marked endpoint density is at most one for any number of layers,
including a transcript with an already known suffix. -/
theorem law_column {n : ℕ} (observed : Fin n → State → Option State) (endpoint : State) :
    ∑ start, law observed start (some endpoint) ≤ 1 := by
  classical
  induction n with
  | zero => simp [law, PMF.pure_apply]
  | succ n ih =>
    simp_rw [law_succ_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    calc
      _ ≤ ∑ next, law (Fin.tail observed) next (some endpoint) := by
        apply Finset.sum_le_sum
        intro next _
        simpa only [one_mul] using mul_le_mul_right'
          (rowWeight_column (observed 0) next) (law (Fin.tail observed) next (some endpoint))
      _ ≤ 1 := ih (Fin.tail observed)

/-- Independent marked chain columns tensorize jointly. This is a bound on
the entire endpoint vector, not a collection of marginal bounds. -/
theorem joint_law_column {Index : Type} [Fintype Index] [DecidableEq Index] {n : ℕ}
    (observed : Index → Fin n → State → Option State) (endpoint : Index → State) :
    ∑ starts : Index → State, ∏ i, law (observed i) (starts i) (some (endpoint i)) ≤ 1 := by
  classical
  rw [← Fintype.prod_sum (fun i start => law (observed i) start (some (endpoint i)))]
  calc
    _ ≤ ∏ _i : Index, (1 : ℝ≥0∞) :=
      Finset.prod_le_prod' (fun i _ => law_column (observed i) (endpoint i))
    _ = 1 := by simp

/-- A jointly uniform vector of starts has marked endpoint-vector density
at most one over the size of its whole vector space. -/
theorem joint_uniformStart_density {Index : Type} [Fintype Index] [DecidableEq Index] {n : ℕ}
    (observed : Index → Fin n → State → Option State) (endpoint : Index → State) :
    ∑ starts : Index → State, (Fintype.card (Index → State) : ℝ≥0∞)⁻¹ *
      ∏ i, law (observed i) (starts i) (some (endpoint i)) ≤
        ((Fintype.card State : ℝ≥0∞) ^ Fintype.card Index)⁻¹ := by
  rw [← Finset.mul_sum]
  have h := mul_le_mul_left' (joint_law_column observed endpoint)
    (Fintype.card (Index → State) : ℝ≥0∞)⁻¹
  simpa only [mul_one, Fintype.card_fun, Nat.cast_pow] using h

/-- Sampling a uniform start and retaining only marked paths reaches any fixed
endpoint with probability at most one digest guess. -/
theorem uniformStart_endpoint {n : ℕ} (observed : Fin n → State → Option State)
    (endpoint : State) :
    ((PMF.uniformOfFintype State).bind (law observed)) (some endpoint) ≤
      (Fintype.card State : ℝ≥0∞)⁻¹ := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_left' (law_column observed endpoint)
    (Fintype.card State : ℝ≥0∞)⁻¹

/-- Query each listed layer once, discarding a path when a previously queried
alternative enters its output. The marking table stays fixed during this walk. -/
def walk {Index : Type} (observed : Index → State → Option State) :
    List Index → State → OracleComp ((Index × State) →ₒ State) (Option State)
  | [], start => pure (some start)
  | index :: rest, start =>
    open Classical in do
    let next ← OracleComp.lift (OracleSpec.query (index, start))
    if ∀ other, observed index other = some next → other = start then
      walk observed rest next
    else pure none

set_option maxRecDepth 10000 in
/-- Layer-disjoint lazy queries realize the marked transition law. -/
theorem walk_run {Index : Type} [DecidableEq Index]
    (observed : Index → State → Option State) (indices : List Index) (hn : indices.Nodup)
    (start : State) (cache : QueryCache ((Index × State) →ₒ State))
    (hc : ∀ index ∈ indices, ∀ input, cache (index, input) = observed index input) :
    letI : Inhabited State := Classical.inhabited_of_nonempty inferInstance
    letI : SampleableType State := .ofFintype State
    letI : IsUniformSpec ((Index × State) →ₒ State) := .ofFintypeInhabited _
    𝒟[(simulateQ ((Index × State) →ₒ State).randomOracle (walk observed indices start)).run' cache] =
      law (fun k : Fin indices.length => observed indices[k]) start := by
  classical
  letI : Inhabited State := Classical.inhabited_of_nonempty inferInstance
  letI : SampleableType State := .ofFintype State
  letI : IsUniformSpec ((Index × State) →ₒ State) := .ofFintypeInhabited _
  induction indices generalizing start cache with
  | nil => simp [walk, law, StateT.run'_eq]
  | cons index rest ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hn
    have hrow := hc index (by simp) start
    have htail : ∀ input, ∀ j ∈ rest, ∀ value,
        (cache.cacheQuery (index, start) input) (j, value) = observed j value := by
      intro input j hj value
      rw [QueryCache.cacheQuery_of_ne _ _ (by
        intro h
        have he : j = index := congrArg Prod.fst h
        exact hnot (he ▸ hj))]
      exact hc j (by simp [hj]) value
    simp only [walk, simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    change _ = liftM ((rowLaw (observed index start)).bind fun next =>
      if ∀ other, observed index other = some next → other = start then
        law (fun k : Fin rest.length => observed rest[k]) next else PMF.pure none)
    cases ho : observed index start with
    | none =>
      rw [QueryImpl.withCaching_run_none _ (hrow.trans ho)]
      simp only [bind_map_left, Function.comp_def]
      rw [evalDist_bind]
      simp only [ho, rowLaw]
      rw [← PMF.monad_bind_eq_bind, liftM_bind]
      change (𝒟[($ᵗ State : ProbComp State)] >>= _) = _
      rw [evalDist_uniformSample]
      congr 1
      funext next
      by_cases h : ∀ other, observed index other = some next → other = start
      · simp only [if_pos h]
        exact ih hn next (cache.cacheQuery (index, start) next) (htail next)
      · simp only [if_neg h, simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure, SPMF.lift_pure]
    | some value =>
      rw [QueryImpl.withCaching_run_some _ (hrow.trans ho)]
      simp only [pure_bind, ho, rowLaw, PMF.pure_bind]
      by_cases h : ∀ other, observed index other = some value → other = start
      · simp only [if_pos h]
        exact ih hn value cache (fun j hj input => hc j (by simp [hj]) input)
      · simp only [if_neg h, simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure, SPMF.lift_pure]

/-- The marked-density bound holds for the actual lazy random-oracle walk,
not just for the abstract row recurrence. -/
theorem walk_density {Index : Type} [DecidableEq Index]
    (observed : Index → State → Option State) (indices : List Index) (hn : indices.Nodup)
    (cache : QueryCache ((Index × State) →ₒ State))
    (hc : ∀ index ∈ indices, ∀ input, cache (index, input) = observed index input)
    (endpoint : State) :
    letI : Inhabited State := Classical.inhabited_of_nonempty inferInstance
    letI : SampleableType State := .ofFintype State
    letI : IsUniformSpec ((Index × State) →ₒ State) := .ofFintypeInhabited _
    ∑ start, Pr[= some endpoint |
      (simulateQ ((Index × State) →ₒ State).randomOracle (walk observed indices start)).run' cache] ≤ 1 := by
  classical
  letI : Inhabited State := Classical.inhabited_of_nonempty inferInstance
  letI : SampleableType State := .ofFintype State
  letI : IsUniformSpec ((Index × State) →ₒ State) := .ofFintypeInhabited _
  calc
    _ = ∑ start, law (fun k : Fin indices.length => observed indices[k]) start (some endpoint) := by
      apply Finset.sum_congr rfl
      intro start _
      simpa only [probOutput_def, SPMF.liftM_apply] using congrArg (fun d : SPMF (Option State) =>
        d (some endpoint)) (walk_run observed indices hn start cache hc)
    _ ≤ 1 := law_column _ endpoint

end MarkedChain

/-- The three possible newly completed suffix lengths fit the pending-edge
charge. This is only the algebraic part of the graph-potential argument. -/
theorem suffixWeight_charge (r : ℕ) (hr : r ≤ 3) :
    (5 : ℝ) ^ r - 1 ≤ (124 / 3 : ℝ) * r := by
  interval_cases r <;> norm_num

/-- Weight of a suffix of depth `depth`, with `pending` eligible edges below
its head. The graph classification that supplies these arguments is separate. -/
def suffixWeight (N : ℝ) (depth pending : ℕ) : ℝ :=
  5 ^ depth * (1 + (124 / 3 : ℝ) * pending / N)

/-- A query that only adds a pending edge obeys the proposed multiplicative
one-query bound. -/
theorem suffixWeight_pending (N : ℝ) (hN : 0 < N) (depth pending : ℕ) :
    suffixWeight N depth (pending + 1) ≤
      (1 + (124 / 3 : ℝ) / N) * suffixWeight N depth pending := by
  calc
    _ ≤ suffixWeight N depth (pending + 1) +
        5 ^ depth * ((124 / 3 : ℝ) / N) * ((124 / 3 : ℝ) * pending / N) :=
      le_add_of_nonneg_right (by positivity)
    _ = _ := by unfold suffixWeight; push_cast; ring

/-- Joining an eligible prefix to the suffix: a miss removes the prefix;
a hit advances by its length plus the new edge and removes all pending edges.
The bound therefore includes reuse of an already known suffix. -/
theorem suffixWeight_join (N : ℝ) (hN : 1 ≤ N) (depth pending prefixLength : ℕ)
    (hp : prefixLength ≤ pending) (hl : prefixLength + 1 ≤ 3) :
    (1 - N⁻¹) * suffixWeight N depth (pending - prefixLength) +
      N⁻¹ * suffixWeight N (depth + prefixLength + 1) 0 ≤
        (1 + (124 / 3 : ℝ) / N) * suffixWeight N depth pending := by
  have hNpos : 0 < N := by linarith
  have hcharge := suffixWeight_charge (prefixLength + 1) hl
  have hrest : (pending : ℝ) - prefixLength = (pending - prefixLength : ℕ) :=
    (Nat.cast_sub hp).symm
  have hrestnonneg : 0 ≤ (pending : ℝ) - prefixLength := sub_nonneg.mpr (by exact_mod_cast hp)
  have hgain : 0 ≤ (124 / 3 : ℝ) * (prefixLength + 1) - ((5 : ℝ) ^ (prefixLength + 1) - 1) := by
    exact sub_nonneg.mpr (by simpa only [Nat.cast_add, Nat.cast_one] using hcharge)
  have hslack : 0 ≤ (5 : ℝ) ^ depth *
      (N⁻¹ * ((124 / 3 : ℝ) * (prefixLength + 1) - ((5 : ℝ) ^ (prefixLength + 1) - 1)) +
        (124 / 3 : ℝ) * N⁻¹ ^ 2 * ((pending : ℝ) - prefixLength + (124 / 3 : ℝ) * pending)) := by
    positivity
  apply le_of_sub_nonneg
  convert hslack using 1 <;>
    simp only [suffixWeight, Nat.cast_zero, mul_zero, zero_div, add_zero, pow_add, pow_one, ← hrest] <;> ring

/-- The first edge into an endpoint can leave other pending edges eligible.
This case keeps their reserve instead of discarding it on success. -/
theorem suffixWeight_first (N : ℝ) (hN : 0 < N) (pending : ℕ) :
    (1 - N⁻¹) * suffixWeight N 0 pending + N⁻¹ * suffixWeight N 1 pending ≤
      (1 + (124 / 3 : ℝ) / N) * suffixWeight N 0 pending := by
  have hslack : 0 ≤ (112 / 3 : ℝ) / N * (1 + (124 / 3 : ℝ) * pending / N) := by positivity
  apply le_of_sub_nonneg
  convert hslack using 1 <;> simp only [suffixWeight, pow_zero, pow_one] <;> ring

/-- Rational certificate for the exponential tail needed at total depth 68. -/
theorem authenticDepth_tail_constant :
    Real.exp (62 / 3) / (5 : ℝ) ^ 68 ≤ (2 : ℝ) ^ (-128 : ℤ) := by
  have hsmall : Real.exp (1 / 3 : ℝ) ≤ 349 / 250 := by
    have h := Real.exp_bound' (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
      (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hpow := pow_le_pow_left₀ (Real.exp_pos (1 / 3)).le hsmall 62
  have hexp : Real.exp (62 / 3 : ℝ) = Real.exp (1 / 3 : ℝ) ^ 62 := by
    convert Real.exp_nat_mul (1 / 3 : ℝ) 62 using 1 <;> norm_num
  rw [hexp]
  calc
    _ ≤ (349 / 250 : ℝ) ^ 62 / 5 ^ 68 := div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ (2 : ℝ) ^ (-128 : ℤ) := by norm_num

/-- The proposed per-query growth rate leaves enough room at the original
query cap. No probability claim is assumed in this numerical calculation. -/
theorem authenticDepth_query_cap (q : ℕ) (hq : q < 2 ^ 127) :
    (1 + 124 / (3 * (2 : ℝ) ^ 128)) ^ q / 5 ^ 68 ≤ (2 : ℝ) ^ (-128 : ℤ) := by
  have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq.le
  have hstep : (1 + 124 / (3 * (2 : ℝ) ^ 128)) ^ q ≤
      Real.exp ((q : ℝ) * (124 / (3 * (2 : ℝ) ^ 128))) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    simpa only [add_comm] using Real.add_one_le_exp (124 / (3 * (2 : ℝ) ^ 128))
  have hexponent : (q : ℝ) * (124 / (3 * (2 : ℝ) ^ 128)) ≤ 62 / 3 := by
    calc
      _ ≤ 2 ^ 127 * (124 / (3 * (2 : ℝ) ^ 128)) :=
        mul_le_mul_of_nonneg_right hq' (by positivity)
      _ = 62 / 3 := by norm_num
  exact (div_le_div_of_nonneg_right
    (hstep.trans (Real.exp_le_exp.mpr hexponent)) (by positivity)).trans authenticDepth_tail_constant

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
  have hdeficit := valid_encoding_deficit encoding hvalid
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
/-- A collision-free recovered root forces every forged chain value to be the
honest value at its digit. This is stronger than one existential guess. -/
theorem fresh_layer_authentic
    (step : XmssSecurity.ChainIndex → ℕ → XmssSecurity.Digest → XmssSecurity.Digest)
    (leafHash : (XmssSecurity.ChainIndex → XmssSecurity.Digest) → XmssSecurity.Digest)
    (nodeHash : ℕ → XmssSecurity.Digest → XmssSecurity.Digest → XmssSecurity.Digest)
    (secret : XmssSecurity.ChainIndex → XmssSecurity.Digest) (path : ℕ → XmssSecurity.Digest)
    (stepCached : XmssSecurity.ChainIndex → ℕ → XmssSecurity.Digest → Prop)
    (leafCached : (XmssSecurity.ChainIndex → XmssSecurity.Digest) → Prop)
    (nodeCached : ℕ → XmssSecurity.Digest → XmssSecurity.Digest → Prop)
    (encoding : XmssSecurity.Encoding)
    (value : XmssSecurity.ChainIndex → XmssSecurity.Digest) (forgedPath : ℕ → XmssSecurity.Digest)
    (hroot : XmssSecurity.Merkle.ascend nodeHash forgedPath 0 XmssSecurity.treeHeight
        (leafHash (XmssSecurity.recoveredEndpoints step encoding value)) =
      XmssSecurity.Merkle.ascend nodeHash path 0 XmssSecurity.treeHeight
        (leafHash (honestEnds step secret)))
    (hcached : LayerCached step leafHash nodeHash stepCached leafCached nodeCached encoding value forgedPath) :
    LayerHit step leafHash nodeHash secret path stepCached leafCached nodeCached ∨
      ∀ l, value l = honestValue step secret l (encoding l).val := by
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
  intro l
  exact (guess_or_hit_of_end step leafHash nodeHash secret path stepCached leafCached nodeCached l
    (encoding l) (value l) (congrFun hends l) (hcached.1 l)).resolve_right hhit

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
  rcases fresh_layer_authentic step leafHash nodeHash secret path stepCached leafCached nodeCached
    encoding value forgedPath hroot hcached with hhit | hauth
  · exact Or.inl hhit
  · exact Or.inr ⟨Finset.univ.filter (fun l => (encoding l).val < 3),
      valid_encoding_short_chains encoding hvalid,
      fun l hl => ⟨(Finset.mem_filter.mp hl).2, hauth l⟩⟩

/-- Every committee has a first PRF term. -/
theorem terms_cons (C : Committee) : ∃ T rest, C.terms = T :: rest := by
  classical
  have hcard : C.t - 1 ≤ (Finset.univ : Finset C.Party).card := by
    simp only [Finset.card_univ, Fintype.card_fin, Committee.n]
    omega
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  have hmem : (⟨s, hs⟩ : C.Term) ∈ C.terms := by simp [Committee.terms]
  apply List.exists_cons_of_ne_nil
  intro h
  simpa [h] using hmem

/-- The top ceremony begins with a chain-start PRF job. This avoids reducing the
concrete list of all top keys during the first-query proof. -/
theorem topJobs_cons : ∃ b l rest, topJobs =
    ⟨.chainEnd (topKey b) l, [.chain topLayer (topKey b) l (digit 0)]⟩ :: rest := by
  have hb : (List.finRange (2 ^ layerHeight)) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [layerHeight] at this
  have hl : (List.finRange numChains) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [numChains] at this
  obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hb
  obtain ⟨l, ls, hl⟩ := List.exists_cons_of_ne_nil hl
  refine ⟨b, l, ?_⟩
  simp only [topJobs, hb, List.flatMap_cons, hl, List.map_cons, List.cons_append]
  exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- The first operation of the actual top ceremony is a threshold PRF call. -/
theorem referenceTree_top_first (x : SigningSecurityProof.Keys3 C) :
    ∃ p k, referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (prfValue x.2.1 p) >>= k := by
  obtain ⟨b, l, rest, hrest⟩ := topJobs_cons
  simp only [referenceTree, ceremonyOutput, hrest, List.mapM_cons, referenceJob,
    List.mapM_nil, bind_pure_comp, bind_map_left, map_bind, bind_assoc, pure_bind]
  exact ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- A threshold PRF starts by hashing the seed of its first term. -/
theorem prfValue_first (seeds : C.Term → HashOutput) (p : Point) :
    ∃ T k, SigningSecurityProof.liftFree (prfValue seeds p) =
      query (spec := WorldSpec C) (.inr (.inr (.inl (.prf (seeds T) p)))) >>= k := by
  obtain ⟨T, rest, hrest⟩ := terms_cons C
  simp only [prfValue, hrest, List.mapM_cons, prf, bind_map_left, bind_assoc,
    SigningSecurityProof.liftFree, liftComp_bind, free_bind, liftComp_map]
  exact ⟨T, _, rfl⟩

set_option maxRecDepth 100000 in
/-- The signing run starts with a free PRF hash, before it reaches the adversary. -/
theorem finalRun_first (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ∃ T p k, SigningDescentProof.finalRun A x =
      query (spec := WorldSpec C) (.inr (.inr (.inl (.prf (x.2.1 T) p)))) >>= k := by
  obtain ⟨p, ktop, htop⟩ := referenceTree_top_first x
  obtain ⟨T, kprf, hprf⟩ := prfValue_first x.2.1 p
  unfold SigningDescentProof.finalRun
  dsimp only
  rw [htop, hprf, bind_assoc, bind_assoc]
  exact ⟨T, p, _, rfl⟩

def topGateInput (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (b : XmssSecurity.TopIndex) : Query C :=
  .prf (x.2.1 T) (.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0))

theorem topGateInput_injective (x : SigningSecurityProof.Keys3 C) (T : C.Term) :
    Function.Injective (topGateInput x T) := by
  intro b c h
  have hp := (Query.prf.inj h).2
  have hk := (Point.chain.inj hp).2.1
  exact Fin.ext (congrArg (fun k : KeyIndex => k.val) hk)

/-- The actual PRF computation asks every term, so each selected gate occurs
in the logged prefix before the adversary is invoked. -/
theorem ensuresGate_prfValue (seeds : C.Term → HashOutput) (p : Point) (T : C.Term) :
    EnsuresGate prims (.inr (.inr (.inl (.prf (seeds T) p))))
      (SigningSecurityProof.liftFree (prfValue seeds p)) := by
  change EnsuresGate prims _ (SigningCacheProof.freeHom (prfValue seeds p))
  rw [prfValue, MonadHom.mmap_bind, SeedHitProof.hom_mapM]
  apply ensuresGate_bind_left prims
  apply ensuresGate_mapM prims _ _ T
  · rw [prf, SeedHitProof.hom_map]
    apply ensuresGate_map prims
    have he : SigningCacheProof.freeHom (C := C) (hashQuery (.prf (seeds T) p)) =
        query (spec := WorldSpec C) (.inr (.inr (.inl (.prf (seeds T) p)))) := by
      simp only [SigningCacheProof.freeHom, SigningSecurityProof.liftFree, hashQuery, free,
        liftComp_query]
      exact (simulateQ_query _ _).trans (id_map _)
    rw [he]
    exact ensuresGate_query prims _
  · simp [Committee.terms]

set_option maxRecDepth 100000 in
/-- Every top key's gate is present in every supported final transcript. -/
theorem finalRun_gate (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (T : C.Term) (b : XmssSecurity.TopIndex) :
    EnsuresGate prims (.inr (.inr (.inl (topGateInput x T b))))
      (SigningDescentProof.finalRun A x) := by
  unfold SigningDescentProof.finalRun
  apply ensuresGate_bind_left prims
  unfold referenceTree ceremonyOutput
  apply ensuresGate_bind_left prims
  apply ensuresGate_map prims
  let job : Job := ⟨.chainEnd (topKey b) ⟨0, by decide⟩, [.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0)]⟩
  apply ensuresGate_mapM prims _ _ job
  · unfold referenceJob
    apply ensuresGate_bind_left prims
    apply ensuresGate_mapM prims _ _ (.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0))
    · exact ensuresGate_prfValue prims _ _ T
    · simp [job]
  · simp only [topJobs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
    exact ⟨b, ⟨0, by decide⟩, rfl⟩

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

set_option maxRecDepth 100000 in
/-- Per-key reserves use separate nonstructural PRF calls. The invariant keeps
their conditional bounds tied to caches actually generated by the transcript. -/
theorem isHitPotential_of_gated_completion {ι : Type} [Fintype ι]
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (relevant : Query C → Prop)
    (completion : OracleComp (Query C →ₒ HashOutput) (CompletionTargets C))
    (hreads : CompletionReadsTargets relevant completion)
    (input : ι → Query C) (hinj : Function.Injective input)
    (hirrelevant : ∀ i, ¬relevant (input i))
    (event : ι → (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C) → Prop)
    (hgate : ∀ i s, RawReachable prims s → ¬GateSeen (.inr (.inr (.inl (input i)))) s.2 →
      (∑' r, Pr[= r | (loggedImpl prims (.inr (.inr (.inl (input i))))).run s] *
        continuationReserve prims (SigningDescentProof.finalRun A x) (event i) r.2) ≤
          (2 ^ 128 : ℝ≥0∞)⁻¹)
    (hcover : ∀ z ∈ support (loggedRun prims A x), WinHit prims x (z.1, z.2.1) →
      (∀ r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle completion).run z.2.1.1),
        CompletedHit relevant r.1 z.2.1.1) ∨
      ∃ i, event i z ∧ GateSeen (.inr (.inr (.inl (input i)))) z.2.2) :
    ∃ Inv f, IsHitPotential prims A x Inv f := by
  classical
  let gate : ι → (WorldSpec C).Domain := fun i => .inr (.inr (.inl (input i)))
  let main := SigningDescentProof.finalRun A x
  let g := completionPotential relevant completion
  let reserves := fun s => ∑ i, gatedContinuation prims main (event i) (gate i) s
  let f := fun s : LoggedState C => g s.1.1 + reserves s
  have hginj : Function.Injective gate := by
    intro i j he
    exact hinj (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj he)))
  refine ⟨RawReachable prims, f, .initial, ?_, ?_, ?_, ?_⟩
  · have hn : ∀ i, ¬GateSeen (gate i) (loggedInit (C := C)).2 := by
      intro i h
      obtain ⟨entry, hmem, _⟩ := h
      cases hmem
    simp only [f, g, reserves, gatedContinuation, hn, if_false, Finset.sum_const_zero, add_zero]
    exact completionPotential_empty relevant completion
  · intro t s hs ht r hr
    exact .step t s hs ht r hr
  · intro t s hs _ ht
    change (∑' r, Pr[= r | (loggedImpl prims t).run s] * (g r.2.1.1 + reserves r.2)) ≤ _
    simp_rw [mul_add]
    rw [ENNReal.tsum_add]
    have hf := gatedContinuation_sum_step prims main event gate hginj t s (2 ^ 128 : ℝ≥0∞)⁻¹
      (fun i hseen he => by subst t; exact hgate i s hs hseen)
    by_cases hex : ∃ i, t = gate i
    · obtain ⟨i, rfl⟩ := hex
      have hg := completionPotential_freeHash_step prims relevant completion hreads (input i) s
      simp only [if_neg (hirrelevant i), add_zero] at hg
      simp only [if_pos (show ∃ j, gate i = gate j from ⟨i, rfl⟩)] at hf
      calc
        _ ≤ g s.1.1 + (reserves s + (2 ^ 128 : ℝ≥0∞)⁻¹) := add_le_add hg hf
        _ = _ := by simp [f, gate, SeedHitProof.signCost, add_assoc]
    · simp only [if_neg hex, add_zero] at hf
      have hg := completionPotential_loggedStep prims relevant completion hreads t s ht
      calc
        _ ≤ (g s.1.1 + (SeedHitProof.signCost t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) + reserves s :=
          add_le_add hg hf
        _ = _ := by dsimp [f]; ac_rfl
  · intro z hz hwin
    rcases hcover z hz hwin with hstable | ⟨i, he, hseen⟩
    · have hg := completionPotential_terminal relevant completion z.2.1.1 hstable
      change 1 ≤ completionPotential relevant completion z.2.1.1 + _
      rw [hg]
      exact le_add_right le_rfl
    · have hf := gatedContinuation_terminal prims main (event i) (gate i) z hz he hseen
      have hsum : gatedContinuation prims main (event i) (gate i) z.2 ≤ reserves z.2 := by
        change _ ≤ ∑ j, gatedContinuation prims main (event j) (gate j) z.2
        exact Finset.single_le_sum
          (f := fun j => gatedContinuation prims main (event j) (gate j) z.2)
          (fun _ _ => zero_le) (Finset.mem_univ i)
      exact (hf ▸ hsum).trans (le_add_left le_rfl)

/-- A winning replay hit that is not guaranteed to survive honest completion.
This includes shadow chains caused by missing upstream PRF answers, not only
hits whose replayed target digest is zero. -/
def ForestException (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C)) : Prop :=
  WinHit prims x (z.1, z.2.1) ∧
    ¬∀ r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (forestCompletion x)).run z.2.1.1), CompletedHit (forestRelevant x.1) r.1 z.2.1.1

/-- No alternative in this cache collides with a canonical forest input. -/
def NoForestCollision (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) : Prop :=
  ∀ (domain : XmssSecurity.HashDomain), ForestDomain domain →
    ∀ input output, cache input = some output →
      SameStructuralPosition x.1 input (.hash (XmssSecurity.tweakableHashInput x.1 domain
        (forestPayload prims x cache domain))) →
      input ≠ .hash (XmssSecurity.tweakableHashInput x.1 domain
        (forestPayload prims x cache domain)) →
      truncateHash output ≠ truncateHash (SigningCacheProof.answersOf cache
        (.hash (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x cache domain))))

/-- A collision can disappear under cache extension only if its canonical
payload changes or the original canonical input was not cached. -/
theorem forestCollision_changes (x : SigningSecurityProof.Keys3 C)
    (cache larger : HashCache C) (hle : cache ≤ larger)
    (hbad : ¬NoForestCollision prims x cache) (hno : NoForestCollision prims x larger) :
    ∃ domain, ForestDomain domain ∧
      (forestPayload prims x cache domain ≠ forestPayload prims x larger domain ∨
        cache (.hash (XmssSecurity.tweakableHashInput x.1 domain
          (forestPayload prims x cache domain))) = none) := by
  classical
  unfold NoForestCollision at hbad
  push_neg at hbad
  obtain ⟨domain, hd, input, output, hc, hpos, hne, heq⟩ := hbad
  refine ⟨domain, hd, ?_⟩
  by_cases hp : forestPayload prims x cache domain = forestPayload prims x larger domain
  · right
    cases ho : cache (.hash (XmssSecurity.tweakableHashInput x.1 domain
        (forestPayload prims x cache domain))) with
    | none => rfl
    | some honest =>
      exfalso
      have ho' := hle ho
      rw [hp] at hpos hne ho'
      apply hno domain hd input output (hle hc) hpos hne
      simpa only [SigningCacheProof.answersOf, ho, ho', Option.getD_some] using heq
  · exact Or.inl hp

set_option backward.isDefEq.respectTransparency false in
/-- In a cache without forest collisions, a cached payload with the canonical
output must itself be the canonical payload. -/
theorem noForestCollision_payload (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (hno : NoForestCollision prims x cache) (domain : XmssSecurity.HashDomain)
    (hd : ForestDomain domain) (hs : StructuralDomain domain) (payload : XmssSecurity.HashInput)
    (hc : (cache (.hash (XmssSecurity.tweakableHashInput x.1 domain payload))).isSome)
    (heq : XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView cache)
        (XmssSecurity.tweakableHashInput x.1 domain payload) =
      XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView cache)
        (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x cache domain))) :
    payload = forestPayload prims x cache domain := by
  classical
  by_contra hn
  cases ho : cache (.hash (XmssSecurity.tweakableHashInput x.1 domain payload)) with
  | none => simp [ho] at hc
  | some output =>
      apply hno domain hd _ output ho ⟨domain, payload, _, hs, rfl, rfl⟩
      · intro hi
        exact hn (XmssSecurity.payload_eq_of_tweakableHashInput_eq x.1 domain
          (Query.hash.inj hi))
      · cases hh : cache (.hash (XmssSecurity.tweakableHashInput x.1 domain
          (forestPayload prims x cache domain))) <;>
          simpa [XmssSecurity.Concrete.CacheView.digestAt, SigningDescentProof.thView,
            SigningCacheProof.answersOf, ho, hh, truncateHash, XmssSecurity.truncateHash,
            XmssSecurity.digestBits, LeanXmss.digestBits, XmssSecurity.Digest, LeanXmss.Digest] using heq

/-- A cached payload cannot share the canonical output unless it is canonical. -/
def PayloadRigid (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (domain : XmssSecurity.HashDomain) : Prop :=
  ∀ payload : XmssSecurity.HashInput,
    (cache (.hash (XmssSecurity.tweakableHashInput x.1 domain payload))).isSome →
    XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView cache)
        (XmssSecurity.tweakableHashInput x.1 domain payload) =
      XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView cache)
        (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x cache domain)) →
    payload = forestPayload prims x cache domain

/-- Collision exclusion transfers back at an actually read, stable target. -/
theorem stableTarget_payloadRigid (x : SigningSecurityProof.Keys3 C)
    (cache larger : HashCache C) (hle : cache ≤ larger)
    (hno : NoForestCollision prims x larger) (domain : XmssSecurity.HashDomain)
    (hd : ForestDomain domain) (hs : StructuralDomain domain)
    (hstable : StableForestTarget prims x cache domain) : PayloadRigid prims x cache domain := by
  intro payload hc heq
  have hp := hstable.2 larger hle
  have hvalue : ∀ input : XmssSecurity.HashInput, (cache (.hash input)).isSome →
      XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView larger) input =
        XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView cache) input := by
    intro input hi
    cases ho : cache (.hash input) with
    | none => simp [ho] at hi
    | some output =>
      exact (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some (hle ho)).trans
        (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ho).symm
  have hc' : (larger (.hash (XmssSecurity.tweakableHashInput x.1 domain payload))).isSome := by
    cases ho : cache (.hash (XmssSecurity.tweakableHashInput x.1 domain payload)) with
    | none => simp [ho] at hc
    | some output => simp [hle ho]
  have heq' : XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView larger)
        (XmssSecurity.tweakableHashInput x.1 domain payload) =
      XmssSecurity.Concrete.CacheView.digestAt (SigningDescentProof.thView larger)
        (XmssSecurity.tweakableHashInput x.1 domain (forestPayload prims x larger domain)) := by
    rw [hp, hvalue _ hc, hvalue _ hstable.1]
    exact heq
  exact (noForestCollision_payload prims x larger hno domain hd hs payload hc' heq').trans hp

/-- The canonical top-node payload orders the path node and sibling by the
key's path bit, exactly as verification does. -/
theorem forestPayload_topNode (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (b : XmssSecurity.TopIndex) (level : XmssSecurity.MerkleLevel) :
    forestPayload prims x cache (.topMerkle level (XmssSecurity.Concrete.topNodeIndex b level.val)) =
      XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload b level.val
        (XmssSecurity.Concrete.CacheReplay.topTreeNode (SigningDescentProof.thView cache) x.1
          (fun k => replayStarts prims x cache topLayer (topKey k)) level.val
          (SigningCacheProof.topPathNodeAt b level.val))
        (XmssSecurity.Concrete.CacheReplay.topTreeNode (SigningDescentProof.thView cache) x.1
          (fun k => replayStarts prims x cache topLayer (topKey k)) level.val
          (XmssSecurity.Concrete.topPathNode b level)) := by
  unfold forestPayload
  rw [SigningCacheProof.topNodeIndex_eq_topPathNodeAt_succ]
  have hchildren := SigningCacheProof.topPathNode_children b level.val level.isLt
  by_cases hb : b.val.testBit level.val = true
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hchildren
    simp only [hchildren.1, hchildren.2,
      XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hchildren
    simp only [hchildren.1, hchildren.2,
      XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
open SigningDescentProof in
/-- Canonical collision exclusion rules out the entire top-layer hit event. -/
theorem noTopHit_of_payload (z : FinalState C)
    (hno : ∀ domain, TopDomain domain → PayloadRigid prims z.keys z.cache domain) :
    ¬LayerHit (topStep z.cache z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.topLeafHash (thView z.cache) z.keys.1 (XmssSecurity.topKeyOf z.key))
      (XmssSecurity.Concrete.CacheView.topNodeHash (thView z.cache) z.keys.1 (XmssSecurity.topKeyOf z.key))
      (z.honestKey prims).topSecret (z.honestKey prims).topPath
      (topStepCached z.cache z.keys.1 z.key) (topLeafCached z.cache z.keys.1 z.key)
      (topNodeCached z.cache z.keys.1 z.key) := by
  rintro (⟨l, k, value, hk, ⟨_, hc⟩, hn, he⟩ | ⟨ends, hc, hn, he⟩ | ⟨level, hl, node, sibling, ⟨_, hc⟩, hn, he⟩)
  · have hp := hno
      (.topChain (XmssSecurity.topKeyOf z.key) l ⟨k, hk⟩) trivial
      (XmssSecurity.Concrete.digestBytes value) hc (by
        simp only [topStep, XmssSecurity.Concrete.CacheView.topChainStep, hk, ↓reduceDIte] at he
        exact he)
    exact hn (XmssSecurity.Concrete.digestBytes_injective hp)
  · have hp := hno
      (.topLeaf (XmssSecurity.topKeyOf z.key)) trivial
      (XmssSecurity.Concrete.leafPayload ends) hc he
    exact hn (XmssSecurity.Concrete.leafPayload_injective hp)
  · let b := XmssSecurity.topKeyOf z.key
    have hnode : honestNode (topStep z.cache z.keys.1 z.key)
        (XmssSecurity.Concrete.CacheView.topLeafHash (thView z.cache) z.keys.1 b)
        (XmssSecurity.Concrete.CacheView.topNodeHash (thView z.cache) z.keys.1 b)
        (z.honestKey prims).topSecret (z.honestKey prims).topPath level =
      XmssSecurity.Concrete.CacheReplay.topTreeNode (thView z.cache) z.keys.1
        (fun k => replayStarts prims z.keys z.cache topLayer (topKey k)) level
        (SigningCacheProof.topPathNodeAt b level) :=
      SigningCacheProof.topPath_ascends_to_topTreeNode _ _ _ b level (Nat.le_of_lt hl)
    have hpath : (z.honestKey prims).topPath level =
      XmssSecurity.Concrete.CacheReplay.topTreeNode (thView z.cache) z.keys.1
        (fun k => replayStarts prims z.keys z.cache topLayer (topKey k)) level
        (XmssSecurity.Concrete.topPathNode b ⟨level, hl⟩) := by
      simp only [FinalState.honestKey, hl, ↓reduceDIte]
      rfl
    have hpayload := forestPayload_topNode prims z.keys z.cache b ⟨level, hl⟩
    rw [← hnode, ← hpath] at hpayload
    have hp := hno
      (.topMerkle ⟨level, hl⟩ (XmssSecurity.Concrete.topNodeIndex b level))
      (XmssSecurity.CappedTop.topNodeIndex_lt b ⟨level, hl⟩)
      (XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload b level node sibling) hc (by
        simpa only [XmssSecurity.Concrete.CacheView.topNodeHash, hl, ↓reduceDIte,
          XmssSecurity.Concrete.CacheView.topNodeInput, hpayload] using he)
    rw [hpayload] at hp
    apply hn
    by_cases hb : b.val.testBit level = true
    · simp only [XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte] at hp
      have hpair := XmssSecurity.Concrete.nodePayload_injective
        (a₁ := (sibling, node)) (a₂ := (_, _)) hp
      exact Prod.ext (congrArg Prod.snd hpair) (congrArg Prod.fst hpair)
    · simp only [XmssSecurity.Concrete.CacheView.topAuthenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte] at hp
      exact XmssSecurity.Concrete.nodePayload_injective hp

open SigningDescentProof in
theorem noForestCollision_topHit (z : FinalState C)
    (hno : NoForestCollision prims z.keys z.cache) :
    ¬LayerHit (topStep z.cache z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.topLeafHash (thView z.cache) z.keys.1 (XmssSecurity.topKeyOf z.key))
      (XmssSecurity.Concrete.CacheView.topNodeHash (thView z.cache) z.keys.1 (XmssSecurity.topKeyOf z.key))
      (z.honestKey prims).topSecret (z.honestKey prims).topPath
      (topStepCached z.cache z.keys.1 z.key) (topLeafCached z.cache z.keys.1 z.key)
      (topNodeCached z.cache z.keys.1 z.key) := by
  apply noTopHit_of_payload prims z
  intro domain hd
  apply noForestCollision_payload prims z.keys z.cache hno domain
  · cases domain <;> simp_all [TopDomain, ForestDomain, XmssSecurity.treeHeight]
  · cases domain <;> simp_all [TopDomain, StructuralDomain]

/-- The canonical bottom-node payload orders the path node and sibling by the
key's path bit, exactly as verification does. -/
theorem forestPayload_bottomNode (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (b : XmssSecurity.LeafIndex) (level : XmssSecurity.MerkleLevel) :
    forestPayload prims x cache (.merkle level (XmssSecurity.Concrete.CacheView.nodeIndex b level.val)) =
      XmssSecurity.Concrete.CacheView.authenticationNodePayload b level.val
        (XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView cache) x.1
          (replayStarts prims x cache bottomLayer) level.val
          (SigningCacheProof.pathNode b level.val))
        (XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView cache) x.1
          (replayStarts prims x cache bottomLayer) level.val
          (XmssSecurity.Concrete.authenticationPathNode b level)) := by
  unfold forestPayload
  rw [SigningCacheProof.nodeIndex_eq_pathNode_succ]
  have hchildren := SigningCacheProof.pathNode_children b level.val level.isLt
  by_cases hb : b.val.testBit level.val = true
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hchildren
    simp only [hchildren.1, hchildren.2,
      XmssSecurity.Concrete.CacheView.authenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hchildren
    simp only [hchildren.1, hchildren.2,
      XmssSecurity.Concrete.CacheView.authenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte]

theorem bottomNode_valid (b : XmssSecurity.LeafIndex) (level : XmssSecurity.MerkleLevel) :
    XmssSecurity.TreeSubtreeValid (level.val + 1)
      (XmssSecurity.Concrete.CacheView.nodeIndex b level.val) := by
  have hsum : (2 * XmssSecurity.treeHeight - (level.val + 1)) + (level.val + 1) =
      2 * XmssSecurity.treeHeight := by have := level.isLt; omega
  have hlt : b.val / 2 ^ (level.val + 1) < 2 ^ (2 * XmssSecurity.treeHeight - (level.val + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (level.val + 1))).2
    rw [← Nat.pow_add, hsum]
    exact b.isLt
  change (b.val / 2 ^ (level.val + 1) + 1) * 2 ^ (level.val + 1) ≤ _
  calc
    _ ≤ 2 ^ (2 * XmssSecurity.treeHeight - (level.val + 1)) * 2 ^ (level.val + 1) :=
      Nat.mul_le_mul_right _ hlt
    _ = XmssSecurity.lifetime := by rw [← Nat.pow_add, hsum]; rfl

set_option backward.isDefEq.respectTransparency false in
open SigningDescentProof in
/-- Canonical collision exclusion rules out the entire bottom-layer hit event. -/
theorem noBottomHit_of_payload (z : FinalState C)
    (hno : ∀ domain, BottomDomain (treeOf z.key) domain → PayloadRigid prims z.keys z.cache domain) :
    ¬LayerHit (bottomStep z.cache z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.leafHash (thView z.cache) z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.nodeHash (thView z.cache) z.keys.1 z.key)
      (z.honestKey prims).secret (z.honestKey prims).path
      (bottomStepCached z.cache z.keys.1 z.key) (bottomLeafCached z.cache z.keys.1 z.key)
      (bottomNodeCached z.cache z.keys.1 z.key) := by
  rintro (⟨l, k, value, hk, ⟨_, hc⟩, hn, he⟩ | ⟨ends, hc, hn, he⟩ | ⟨level, hl, node, sibling, ⟨_, hc⟩, hn, he⟩)
  · have hp := hno
      (.chain z.key l ⟨k, hk⟩) rfl
      (XmssSecurity.Concrete.digestBytes value) hc (by
        simp only [bottomStep, XmssSecurity.Concrete.CacheView.chainStep, hk, ↓reduceDIte] at he
        exact he)
    exact hn (XmssSecurity.Concrete.digestBytes_injective hp)
  · have hp := hno
      (.leaf z.key) rfl
      (XmssSecurity.Concrete.leafPayload ends) hc he
    exact hn (XmssSecurity.Concrete.leafPayload_injective hp)
  · let b := z.key
    have hnode : honestNode (bottomStep z.cache z.keys.1 z.key)
        (XmssSecurity.Concrete.CacheView.leafHash (thView z.cache) z.keys.1 b)
        (XmssSecurity.Concrete.CacheView.nodeHash (thView z.cache) z.keys.1 b)
        (z.honestKey prims).secret (z.honestKey prims).path level =
      XmssSecurity.Concrete.CacheReplay.treeNode (thView z.cache) z.keys.1
        (replayStarts prims z.keys z.cache bottomLayer) level
        (SigningCacheProof.pathNode b level) :=
      SigningCacheProof.path_ascends_to_treeNode _ _ _ b level (Nat.le_of_lt hl)
    have hpath : (z.honestKey prims).path level =
      XmssSecurity.Concrete.CacheReplay.treeNode (thView z.cache) z.keys.1
        (replayStarts prims z.keys z.cache bottomLayer) level
        (XmssSecurity.Concrete.authenticationPathNode b ⟨level, hl⟩) := by
      simp only [FinalState.honestKey, hl, ↓reduceDIte]
      rfl
    have hpayload := forestPayload_bottomNode prims z.keys z.cache b ⟨level, hl⟩
    rw [← hnode, ← hpath] at hpayload
    have hp := hno
      (.merkle ⟨level, hl⟩ (XmssSecurity.Concrete.CacheView.nodeIndex b level))
      (by
        change (b.val / 2 ^ (level + 1)) / 2 ^ (16 - (level + 1)) = b.val / 2 ^ 16
        rw [Nat.div_div_eq_div_mul, ← pow_add, show level + 1 + (16 - (level + 1)) = 16 by
          have hh : level < 16 := hl; omega])
      (XmssSecurity.Concrete.CacheView.authenticationNodePayload b level node sibling) hc (by
        simpa only [XmssSecurity.Concrete.CacheView.nodeHash, hl, ↓reduceDIte,
          XmssSecurity.Concrete.CacheView.nodeInput, hpayload] using he)
    rw [hpayload] at hp
    apply hn
    by_cases hb : b.val.testBit level = true
    · simp only [XmssSecurity.Concrete.CacheView.authenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte] at hp
      have hpair := XmssSecurity.Concrete.nodePayload_injective
        (a₁ := (sibling, node)) (a₂ := (_, _)) hp
      exact Prod.ext (congrArg Prod.snd hpair) (congrArg Prod.fst hpair)
    · simp only [XmssSecurity.Concrete.CacheView.authenticationNodePayload, hb, Bool.false_eq_true, ↓reduceIte] at hp
      exact XmssSecurity.Concrete.nodePayload_injective hp

open SigningDescentProof in
theorem noForestCollision_bottomHit (z : FinalState C)
    (hno : NoForestCollision prims z.keys z.cache) :
    ¬LayerHit (bottomStep z.cache z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.leafHash (thView z.cache) z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.nodeHash (thView z.cache) z.keys.1 z.key)
      (z.honestKey prims).secret (z.honestKey prims).path
      (bottomStepCached z.cache z.keys.1 z.key) (bottomLeafCached z.cache z.keys.1 z.key)
      (bottomNodeCached z.cache z.keys.1 z.key) := by
  apply noBottomHit_of_payload prims z
  intro domain hd
  apply noForestCollision_payload prims z.keys z.cache hno domain
  · cases domain with
    | chain _ _ _ | leaf _ => trivial
    | merkle level node =>
      have hj : node.val / 2 ^ (16 - (level.val + 1)) < 2 ^ 16 := by
        rw [hd]; exact (treeOf z.key).isLt
      have hl : level.val < 16 := level.isLt
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add] at hj
      change (node.val + 1) * 2 ^ (level.val + 1) ≤ 2 ^ 32
      calc
        _ ≤ 2 ^ (16 + (16 - (level.val + 1))) * 2 ^ (level.val + 1) := Nat.mul_le_mul_right _ hj
        _ = _ := by rw [← pow_add, show 16 + (16 - (level.val + 1)) + (level.val + 1) = 32 by omega]
    | topChain _ _ _ | topLeaf _ | topMerkle _ _ | encoding _ | topEncoding _ => cases hd
  · cases domain <;> simp_all [BottomDomain, StructuralDomain]

open SigningDescentProof in
/-- Both layers of the completed replay are free of the original hit event. -/
theorem noForestCollision_hit (z : FinalState C)
    (hno : NoForestCollision prims z.keys z.cache) :
    ¬Hit z.cache z.keys.1 z.key (z.honestKey prims) := by
  rintro (h | h)
  · exact noForestCollision_bottomHit prims z hno h
  · exact noForestCollision_topHit prims z hno h

theorem bottomDomain_valid (b : Fin (2 ^ layerHeight)) (domain : XmssSecurity.HashDomain)
    (hd : BottomDomain b domain) : ForestDomain domain ∧ StructuralDomain domain := by
  constructor
  · cases domain with
    | chain _ _ _ | leaf _ => trivial
    | merkle level node =>
      have hj : node.val / 2 ^ (16 - (level.val + 1)) < 2 ^ 16 := by rw [hd]; exact b.isLt
      have hl : level.val < 16 := level.isLt
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add] at hj
      change (node.val + 1) * 2 ^ (level.val + 1) ≤ 2 ^ 32
      calc
        _ ≤ 2 ^ (16 + (16 - (level.val + 1))) * 2 ^ (level.val + 1) := Nat.mul_le_mul_right _ hj
        _ = _ := by rw [← pow_add, show 16 + (16 - (level.val + 1)) + (level.val + 1) = 32 by omega]
    | topChain _ _ _ | topLeaf _ | topMerkle _ _ | encoding _ | topEncoding _ => cases hd
  · cases domain <;> simp_all [BottomDomain, StructuralDomain]

theorem topDomain_valid (domain : XmssSecurity.HashDomain)
    (hd : TopDomain domain) : ForestDomain domain ∧ StructuralDomain domain := by
  cases domain <;> simp_all [TopDomain, ForestDomain, StructuralDomain, XmssSecurity.treeHeight]

open SigningDescentProof in
/-- Completing unrelated trees cannot erase a hit at a key whose own bottom
ceremony and the top ceremony are already resolved. -/
theorem resolved_ceremonies_noHit (z : FinalState C)
    (larger : HashCache C) (hle : z.cache ≤ larger)
    (hno : NoForestCollision prims z.keys larger)
    (htop : DeterministicSigning.Resolves z.cache
      (referenceTree forestHash (forestValue z.keys.2.1) z.keys.1 emptyTop .top) (some (.top z.top)))
    (output : Option TreeOutput)
    (hbottom : DeterministicSigning.Resolves z.cache
      (referenceTree forestHash (forestValue z.keys.2.1) z.keys.1 z.top (.bottom (treeOf z.key))) output) :
    ¬Hit z.cache z.keys.1 z.key (z.honestKey prims) := by
  rintro (hhit | hhit)
  · apply noBottomHit_of_payload prims z _ hhit
    intro domain hd
    have hv := bottomDomain_valid (treeOf z.key) domain hd
    exact stableTarget_payloadRigid prims z.keys z.cache larger hle hno domain hv.1 hv.2
      (resolves_referenceBottom_targets prims z.keys z.cache z.top (treeOf z.key) output hbottom domain hd)
  · apply noTopHit_of_payload prims z _ hhit
    intro domain hd
    have hv := topDomain_valid domain hd
    exact stableTarget_payloadRigid prims z.keys z.cache larger hle hno domain hv.1 hv.2
      (resolves_referenceTop_targets prims z.keys z.cache z.top htop domain hd)

/-- Every exceptional win admits a completed honest forest with no cached
alternative in its final cache colliding with a canonical structural input. This makes
the collision-free case available for the remaining authentic-value argument. -/
theorem forestException_witness (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hex : ForestException prims x z) :
    ∃ r : (Unit × HashCache C) × HashCache C,
      r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (recordReads (forestRun x) ∅)).run z.2.1.1) ∧
      NoForestCollision prims x r.2 := by
  classical
  obtain ⟨t, ht⟩ := not_forall.mp hex.2
  obtain ⟨ht, hno⟩ := Classical.not_imp.mp ht
  simp only [forestCompletion, recordedCompletion, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at ht
  obtain ⟨r, hr, rfl⟩ := ht
  refine ⟨r, hr, ?_⟩
  intro domain hdomain input output hc hpos hne heq
  exact hno (completedHit_forest_of_completedCollision prims x z.2.1.1 r hr
    domain hdomain input output hc hpos hne heq)

/-- An exceptional hit has a concrete witness to unstable or missing honest
replay data in its original cache. It cannot be dismissed as a collision created
by the completion itself. -/
theorem forestException_replayChanges (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hex : ForestException prims x z) :
    ∃ r : (Unit × HashCache C) × HashCache C,
      r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (recordReads (forestRun x) ∅)).run z.2.1.1) ∧
      NoForestCollision prims x r.2 ∧
      ∃ domain, ForestDomain domain ∧
        (forestPayload prims x z.2.1.1 domain ≠ forestPayload prims x r.2 domain ∨
          z.2.1.1 (.hash (XmssSecurity.tweakableHashInput x.1 domain
            (forestPayload prims x z.2.1.1 domain))) = none) := by
  obtain ⟨r, hr, hno⟩ := forestException_witness prims x z hex
  obtain ⟨top, state, forgery, _, hhit⟩ := hex.1.2
  have hbad : ¬NoForestCollision prims x z.2.1.1 := by
    intro hn
    exact noForestCollision_hit prims ⟨x, top, state, forgery, z.2.1.1, false⟩ hn hhit
  exact ⟨r, hr, hno, forestCollision_changes prims x z.2.1.1 r.2
    (recordReads_resolves (forestRun x) ∅ z.2.1.1 (by intro i v h; cases h) r hr).1 hbad hno⟩

set_option maxRecDepth 100000 in
/-- The actual top ceremony resolves every PRF and structural read in the
final cache. Evaluation alone would not justify stability of its targets. -/
theorem exposedRun_top_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) :
    DeterministicSigning.Resolves r.2.1
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)) := by
  obtain ⟨top', state', forgery', hsome', hfinal, _⟩ :=
    SigningCacheProof.exposedRun_facts prims A x r hr hwin
  have htop : top' = top := by
    rw [hsome] at hsome'
    exact congrArg Prod.fst (Option.some.inj hsome').symm
  subst top'
  unfold SigningDescentProof.exposedRun SigningDescentProof.finalRun at hr
  dsimp only at hr
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _] at hr
  obtain ⟨first, hp, hrest⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
  have hgrow := SigningCacheProof.countRun_grows prims _ _ r hrest
  have hf := SigningCacheProof.run_liftFree prims _ _ first hp _
    (SigningCacheProof.agrees_answersOf hgrow)
  have hv : first.1 = some (.top top) := hf.trans hfinal
  rw [← hashEmbed_referenceTree] at hp
  exact hv ▸ (run_hashEmbed_resolves prims _ _ first hp).mono hgrow

set_option maxRecDepth 100000 in
open SigningCacheProof SigningDescentProof in
/-- Actual freshness checking either uses fewer than t signers or resolves the
forgery's bottom ceremony. This follows the executed finish branch. -/
theorem exposedRun_fresh_or_bottom (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : Outcome C) (hr : r ∈ support (exposedRun prims A x)) (hwin : r.1.1 = (true, false)) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      ((signersAt state forgery.signature.leafIndex forgery.message).card < C.t ∨
        ∃ output, DeterministicSigning.Resolves r.2.1
          (referenceTree forestHash (forestValue x.2.1) x.1 top
            (.bottom (treeOf forgery.signature.leafIndex))) output) := by
  unfold exposedRun finalRun at hr
  dsimp only at hr
  obtain ⟨p, hp, hr⟩ := run_bind_support prims _ _ _ r hr
  rcases hp1 : p.1 with _ | (top | tree)
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hwin
  swap
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hwin
  rw [hp1] at hr
  obtain ⟨q, hq, hr⟩ := run_bind_support prims _ _ _ r hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  unfold SigningCoreProof.tsigFinish at hw
  obtain ⟨v, hv, hw⟩ := run_bind_support prims _ _ _ w hw
  dsimp only at hw
  split_ifs at hw with hlt
  · simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨top, q.1.2.1, q.1.1, rfl, Or.inl hlt⟩
  · obtain ⟨f, hf, hw⟩ := run_bind_support prims _ _ _ w hw
    simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨k, he⟩ := honestSignature_prefix x top q.1.1.signature.leafIndex q.1.1.message
    rw [he] at hf
    obtain ⟨call, hc, htail⟩ := run_bind_support prims _ _ _ f hf
    have hgrow := countRun_grows prims _ _ f htail
    rw [← hashEmbed_referenceTree] at hc
    exact ⟨top, q.1.2.1, q.1.1, rfl, Or.inr
      ⟨call.1, (run_hashEmbed_resolves prims _ _ call hc).mono hgrow⟩⟩

set_option maxRecDepth 100000 in
/-- An exceptional win targets a bottom tree whose structural ceremony has
never completed in the actual cache, including ceremonies returning `none`. -/
theorem forestException_unopened (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestException prims x z)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : z.1.2 = some (top, state, forgery)) (output : Option TreeOutput) :
    ¬DeterministicSigning.Resolves z.2.1.1
      (referenceTree forestHash (forestValue x.2.1) x.1 top (.bottom (treeOf forgery.signature.leafIndex))) output := by
  intro hbottom
  obtain ⟨r, hr, hno⟩ := forestException_witness prims x z hex
  have hgrow := (recordReads_resolves (forestRun x) ∅ z.2.1.1
    (by intro input value hh; cases hh) r hr).1
  have he : (z.1, z.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
    rw [← loggedRun_forget, support_map]
    exact Set.mem_image_of_mem _ hz
  have htop := exposedRun_top_resolves prims A x (z.1, z.2.1) he hex.1.1 top state forgery hsome
  obtain ⟨top', state', forgery', hsome', hhit⟩ := hex.1.2
  have htuple := Option.some.inj (hsome'.symm.trans hsome)
  cases htuple
  exact resolved_ceremonies_noHit prims ⟨x, top, state, forgery, z.2.1.1, false⟩
    r.2 hgrow hno htop output hbottom hhit

set_option maxRecDepth 100000 in
/-- Exceptional wins use a fresh signing key: the alternative freshness
comparison would itself execute the forbidden bottom ceremony. -/
theorem forestException_fresh (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestException prims x z) :
    ∃ top state forgery, z.1.2 = some (top, state, forgery) ∧
      (signersAt state forgery.signature.leafIndex forgery.message).card < C.t := by
  have he : (z.1, z.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
    rw [← loggedRun_forget, support_map]
    exact Set.mem_image_of_mem _ hz
  obtain ⟨top, state, forgery, hsome, hfresh | ⟨output, hresolved⟩⟩ :=
    exposedRun_fresh_or_bottom prims A x (z.1, z.2.1) he hex.1.1
  · exact ⟨top, state, forgery, hsome, hfresh⟩
  · exact False.elim (forestException_unopened prims A x z hz hex top state forgery hsome output hresolved)

set_option maxRecDepth 100000 in
/-- Any completed semantic bottom call excludes the exceptional event at that
key. The call may fail; only its supported execution and cache inclusion matter. -/
theorem forestException_no_bottom_call (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestException prims x z)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : z.1.2 = some (top, state, forgery))
    (initial : HashCache C × ℕ) (r : Option TreeOutput × (HashCache C × ℕ))
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree
        (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom (treeOf forgery.signature.leafIndex))))).run initial))
    (hle : r.2.1 ≤ z.2.1.1) : False := by
  rw [← hashEmbed_referenceTree] at hr
  have hresolved := run_hashEmbed_resolves prims _ initial r hr
  exact forestException_unopened prims A x z hz hex top state forgery hsome r.1 (hresolved.mono hle)

set_option maxRecDepth 100000 in
/-- An exceptional terminal trace cannot have a supported suffix beginning
with the semantic bottom call for its forged key, followed by any continuation. -/
theorem forestException_no_bottom_suffix (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestException prims x z)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : z.1.2 = some (top, state, forgery)) (initial : LoggedState C)
    (k : Option TreeOutput → OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)))
    (hsuffix : z ∈ support ((simulateQ (loggedImpl prims)
      (SigningSecurityProof.liftFree
        (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom (treeOf forgery.signature.leafIndex))) >>= k)).run initial)) :
    False := by
  let call := SigningSecurityProof.liftFree
    (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom (treeOf forgery.signature.leafIndex)))
  have hforget : (fun r => (r.1, r.2.1)) <$>
      ((simulateQ (loggedImpl prims) (call >>= k)).run initial) =
      ((simulateQ (SigningCacheProof.countImpl prims) (call >>= k)).run initial.1) :=
    SigningCoreProof.simulateQ_run_forget _ _
      (fun t s log => by simp [loggedImpl, Functor.map_map]) _ _ _
  have hc : (z.1, z.2.1) ∈ support
      ((simulateQ (SigningCacheProof.countImpl prims) (call >>= k)).run initial.1) := by
    rw [← hforget, support_map]
    exact Set.mem_image_of_mem _ hsuffix
  obtain ⟨r, hr, htail⟩ := SigningCacheProof.run_bind_support prims call k initial.1 (z.1, z.2.1) hc
  exact forestException_no_bottom_call prims A x z hz hex top state forgery hsome initial.1 r hr
    (SigningCacheProof.countRun_grows prims (k r.1) r.2 (z.1, z.2.1) htail)

set_option maxRecDepth 100000 in
/-- The actual key-generation prefix replays to the same top tree after every
cache extension, including an honest completion of unopened bottom trees. -/
theorem exposedRun_top_extension (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery))
    (larger : HashCache C) (hle : r.2.1 ≤ larger) :
    D prims (SigningCacheProof.answersOf larger)
      (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) = some (.top top) := by
  exact resolves_referenceTop_eval prims x r.2.1 larger hle top
    (exposedRun_top_resolves prims A x r hr hwin top state forgery hsome)

/-- The codeword selected by the actual verifier, retaining its bottom decode. -/
def ActualTopCodeword (cache : HashCache C) (P : XmssSecurity.PublicParameter)
    (e : XmssSecurity.LeafIndex) (message : XmssSecurity.Message)
    (σ : XmssSecurity.Signature) (topCodeword : XmssSecurity.Encoding) : Prop :=
  ∃ encoding : XmssSecurity.Encoding,
    XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView cache)
        P e (message, σ.randomness)) = some encoding ∧
    XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView cache)
        P (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot cache P e encoding σ, σ.top.randomness)) = some topCodeword

set_option maxRecDepth 100000 in
/-- Decoding in an extension selects the same recovery walks that the actual
verifier resolved in the original cache. This preserves the queried digits. -/
theorem resolves_verify_topWalks (cache larger : HashCache C) (hle : cache ≤ larger)
    (pk : XmssSecurity.PublicKey) (e : XmssSecurity.LeafIndex) (message : XmssSecurity.Message)
    (σ : XmssSecurity.Signature) (verified : Bool)
    (h : DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (XmssSecurity.Concrete.verify pk e message σ : OracleComp XmssSecurity.HashSpec _) verified)
    (encoding topCodeword : XmssSecurity.Encoding)
    (hdec : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView larger)
        pk.parameter e (message, σ.randomness)) = some encoding)
    (htop : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView larger)
        pk.parameter (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot larger pk.parameter e encoding σ, σ.top.randomness)) = some topCodeword) :
    ActualTopCodeword cache pk.parameter e message σ topCodeword ∧
    ∀ l, ∃ finish, DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (XmssSecurity.Concrete.topChainWalk pk.parameter (XmssSecurity.topKeyOf e) l
        (topCodeword l).val (XmssSecurity.chainLength - 1 - (topCodeword l).val)
        (σ.top.chainValue l) : OracleComp XmssSecurity.HashSpec _) finish := by
  have hgrow := SigningCacheProof.thView_mono hle
  unfold XmssSecurity.Concrete.verify at h
  obtain ⟨d, hd, h⟩ := h.of_bind
  have hdv := SigningCacheProof.resolves_value (hd.mono hgrow)
  rw [XmssSecurity.Concrete.CacheReplay.eval_encodingHash] at hdv
  have hdv₀ := SigningCacheProof.resolves_value hd
  rw [XmssSecurity.Concrete.CacheReplay.eval_encodingHash] at hdv₀
  have hdec₀ : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView cache)
        pk.parameter e (message, σ.randomness)) = some encoding := by
    rw [hdv₀, ← hdv]
    exact hdec
  rw [← hdv, hdec] at h
  obtain ⟨ends, hends, h⟩ := h.of_bind
  have hendsv := SigningCacheProof.resolves_value (hends.mono hgrow)
  rw [XmssSecurity.Concrete.CacheReplay.eval_recoverEndpoints] at hendsv
  obtain ⟨leaf, hleaf, h⟩ := h.of_bind
  have hleafv := SigningCacheProof.resolves_value (hleaf.mono hgrow)
  rw [XmssSecurity.Concrete.CacheReplay.eval_leafHash] at hleafv
  unfold XmssSecurity.Concrete.verifyAfterLeaf at h
  obtain ⟨root, hroot, h⟩ := h.of_bind
  have hrootv := SigningCacheProof.resolves_value (hroot.mono hgrow)
  rw [XmssSecurity.Concrete.CacheReplay.eval_authenticationRoot] at hrootv
  have hendsv₀ := SigningCacheProof.resolves_value hends
  have hleafv₀ := SigningCacheProof.resolves_value hleaf
  have hrootv₀ := SigningCacheProof.resolves_value hroot
  rw [XmssSecurity.Concrete.CacheReplay.eval_recoverEndpoints] at hendsv₀
  rw [XmssSecurity.Concrete.CacheReplay.eval_leafHash] at hleafv₀
  rw [XmssSecurity.Concrete.CacheReplay.eval_authenticationRoot, ← hleafv₀, ← hendsv₀] at hrootv₀
  change SigningDescentProof.forgedRoot cache pk.parameter e encoding σ = root at hrootv₀
  subst hendsv hleafv hrootv
  unfold XmssSecurity.Concrete.verifyTop at h
  obtain ⟨d₂, hd₂, h⟩ := h.of_bind
  have hd₂v := SigningCacheProof.resolves_value (hd₂.mono hgrow)
  have hh : evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn (SigningDescentProof.thView larger))
      (XmssSecurity.Concrete.topEncodingHash pk.parameter (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot larger pk.parameter e encoding σ) σ.top.randomness :
          OracleComp XmssSecurity.HashSpec _) =
      XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView larger)
        pk.parameter (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot larger pk.parameter e encoding σ, σ.top.randomness) := by
    simp [XmssSecurity.Concrete.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingHash,
      XmssSecurity.Concrete.CacheView.topEncodingInput, XmssSecurity.Concrete.CacheView.tweakableHash]
  have hd₂v₀ := SigningCacheProof.resolves_value hd₂
  have hh₀ : evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn (SigningDescentProof.thView cache))
      (XmssSecurity.Concrete.topEncodingHash pk.parameter (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot larger pk.parameter e encoding σ) σ.top.randomness :
          OracleComp XmssSecurity.HashSpec _) =
      XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView cache)
        pk.parameter (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot larger pk.parameter e encoding σ, σ.top.randomness) := by
    simp [XmssSecurity.Concrete.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingHash,
      XmssSecurity.Concrete.CacheView.topEncodingInput, XmssSecurity.Concrete.CacheView.tweakableHash]
  have hd₂v₀' := hh₀.symm.trans hd₂v₀
  change SigningDescentProof.forgedRoot cache pk.parameter e encoding σ =
    SigningDescentProof.forgedRoot larger pk.parameter e encoding σ at hrootv₀
  rw [← hrootv₀] at hd₂v₀'
  have hd₂v' := hh.symm.trans hd₂v
  have htop₀ : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView cache)
        pk.parameter (XmssSecurity.topKeyOf e)
        (SigningDescentProof.forgedRoot cache pk.parameter e encoding σ, σ.top.randomness)) = some topCodeword := by
    rw [hd₂v₀', ← hd₂v']
    exact htop
  rw [← hd₂v', htop] at h
  obtain ⟨ends, hends, _⟩ := h.of_bind
  exact ⟨⟨encoding, hdec₀, htop₀⟩, fun l => ⟨ends l, hends.of_sequenceFin l⟩⟩

/-- Root agreement at the top layer forces authentic forged values, unless a
structural output collision occurs in that layer. It asserts no hiddenness. -/
def TopAuthenticOrHit (verifiedCache : HashCache C) (z : SigningDescentProof.FinalState C) : Prop :=
  ∃ encoding : XmssSecurity.Encoding, XmssSecurity.TargetSum.Valid encoding ∧
    ActualTopCodeword verifiedCache z.keys.1 z.key z.forgery.message
      (XmssSecurity.Bridge.toModelSig z.forgery.signature) encoding ∧
    (∀ l, ∃ finish, DeterministicSigning.Resolves (SigningDescentProof.thView verifiedCache)
      (XmssSecurity.Concrete.topChainWalk z.keys.1 (XmssSecurity.topKeyOf z.key) l
        (encoding l).val (XmssSecurity.chainLength - 1 - (encoding l).val)
        ((XmssSecurity.Bridge.toModelSig z.forgery.signature).top.chainValue l) :
          OracleComp XmssSecurity.HashSpec _) finish) ∧
    (SigningDescentProof.LayerHit (SigningDescentProof.topStep z.cache z.keys.1 z.key)
      (XmssSecurity.Concrete.CacheView.topLeafHash (SigningDescentProof.thView z.cache)
        z.keys.1 (XmssSecurity.topKeyOf z.key))
      (XmssSecurity.Concrete.CacheView.topNodeHash (SigningDescentProof.thView z.cache)
        z.keys.1 (XmssSecurity.topKeyOf z.key))
      (z.honestKey prims).topSecret (z.honestKey prims).topPath
      (SigningDescentProof.topStepCached z.cache z.keys.1 z.key)
      (SigningDescentProof.topLeafCached z.cache z.keys.1 z.key)
      (SigningDescentProof.topNodeCached z.cache z.keys.1 z.key) ∨
    ∀ l, (XmssSecurity.Bridge.toModelSig z.forgery.signature).top.chainValue l =
      SigningDescentProof.honestValue (SigningDescentProof.topStep z.cache z.keys.1 z.key)
        (z.honestKey prims).topSecret l (encoding l).val)

set_option maxRecDepth 100000 in
/-- This descent applies to the actual signing run and every extension of its
final cache; it does not assume an eager bottom-tree key generation. -/
theorem exposedRun_top_authentic (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (larger : HashCache C) (hle : r.2.1 ≤ larger) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      TopAuthenticOrHit prims r.2.1 ⟨x, top, state, forgery, larger, false⟩ := by
  obtain ⟨top, state, forgery, hsome, _, hres, _⟩ :=
    SigningCacheProof.exposedRun_facts prims A x r hr hwin
  refine ⟨top, state, forgery, hsome, ?_⟩
  let z : SigningDescentProof.FinalState C := ⟨x, top, state, forgery, larger, false⟩
  have hres' := hres.mono (SigningCacheProof.thView_mono hle)
  have hv := (XmssSecurity.Concrete.CacheReplay.eval_verify _ _ _ _ _).symm.trans
    (SigningCacheProof.resolves_value hres')
  have hc := SigningCacheProof.verifyCached_of_resolves larger
    (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩) forgery.signature.leafIndex
    forgery.message (XmssSecurity.Bridge.toModelSig forgery.signature) true hres'
  obtain ⟨encoding, hencoding, htop⟩ :=
    (XmssSecurity.Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hv
  obtain ⟨topCodeword, htopCodeword, htopRoot⟩ :=
    (XmssSecurity.Concrete.verifyTopFromCache_eq_true_iff _ _ _ _ _).mp htop
  have hroot := SigningCacheProof.topRootReplay prims z
    (exposedRun_top_extension prims A x r hr hwin top state forgery hsome larger hle)
  have hcode := resolves_verify_topWalks r.2.1 larger hle _ _ _ _ true hres
    encoding topCodeword hencoding htopCodeword
  refine ⟨topCodeword, (XmssSecurity.TargetSum.decodeDigest_eq_some_iff.mp htopCodeword).2,
    hcode.1, hcode.2, ?_⟩
  exact fresh_layer_authentic (SigningDescentProof.topStep larger x.1 z.key)
    (XmssSecurity.Concrete.CacheView.topLeafHash (SigningDescentProof.thView larger)
      x.1 (XmssSecurity.topKeyOf z.key))
    (XmssSecurity.Concrete.CacheView.topNodeHash (SigningDescentProof.thView larger)
      x.1 (XmssSecurity.topKeyOf z.key))
    (z.honestKey prims).topSecret (z.honestKey prims).topPath _ _ _ topCodeword
    (XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue
    (XmssSecurity.Concrete.layerPath (XmssSecurity.Bridge.toModelSig forgery.signature).top)
    (htopRoot.trans hroot.symm) ((hc encoding hencoding).2 topCodeword htopCodeword)

set_option maxRecDepth 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- An exceptional winning trace has a supported collision-free completion in
which every top signature value is authentic. The valid codeword requires total
authentic depth 68 below the public endpoints. -/
theorem forestException_authentic (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestException prims x z) :
    ∃ r : (Unit × HashCache C) × HashCache C,
      r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
        (recordReads (forestRun x) ∅)).run z.2.1.1) ∧
      NoForestCollision prims x r.2 ∧
      ∃ top state forgery, z.1.2 = some (top, state, forgery) ∧
        ∃ encoding : XmssSecurity.Encoding, XmssSecurity.TargetSum.Valid encoding ∧
          (∑ l, (3 - (encoding l).val)) = 68 ∧
          (∀ l, (XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue l =
            XmssSecurity.Wots.walk
              (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView r.2) x.1
                (XmssSecurity.topKeyOf forgery.signature.leafIndex) l)
              0 (encoding l).val
              (replayStarts prims x r.2 topLayer
                (topKey (XmssSecurity.topKeyOf forgery.signature.leafIndex)) l)) ∧
          ActualTopCodeword z.2.1.1 x.1 forgery.signature.leafIndex forgery.message
            (XmssSecurity.Bridge.toModelSig forgery.signature) encoding ∧
          ∀ l, ∃ finish, DeterministicSigning.Resolves (SigningDescentProof.thView z.2.1.1)
            (XmssSecurity.Concrete.topChainWalk x.1 (XmssSecurity.topKeyOf forgery.signature.leafIndex) l
              (encoding l).val (XmssSecurity.chainLength - 1 - (encoding l).val)
              ((XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue l) :
                OracleComp XmssSecurity.HashSpec _) finish := by
  obtain ⟨r, hr, hno⟩ := forestException_witness prims x z hex
  have hgrow := (recordReads_resolves (forestRun x) ∅ z.2.1.1
    (by intro input output hh; cases hh) r hr).1
  have he : (z.1, z.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
    rw [← loggedRun_forget, support_map]
    exact Set.mem_image_of_mem _ hz
  obtain ⟨top, state, forgery, hsome, encoding, hvalid, hcode, hsuffix, hauth⟩ :=
    exposedRun_top_authentic prims A x (z.1, z.2.1) he hex.1.1 r.2 hgrow
  have hn := noForestCollision_topHit prims
    (⟨x, top, state, forgery, r.2, false⟩ : SigningDescentProof.FinalState C) hno
  exact ⟨r, hr, hno, top, state, forgery, hsome, encoding, hvalid,
    valid_encoding_deficit encoding hvalid, hauth.resolve_left hn, hcode, hsuffix⟩

set_option maxRecDepth 100000 in
/-- The authentic depth certificate is already true in the actual final
cache. It does not depend on targets chosen by the later forest completion. -/
theorem forestException_authentic_original (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C))
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestException prims x z) :
    ∃ top state forgery, z.1.2 = some (top, state, forgery) ∧
      ∃ encoding : XmssSecurity.Encoding, XmssSecurity.TargetSum.Valid encoding ∧
        (∑ l, (3 - (encoding l).val)) = 68 ∧
        (∀ l, (XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue l =
          XmssSecurity.Wots.walk
            (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView z.2.1.1) x.1
              (XmssSecurity.topKeyOf forgery.signature.leafIndex) l)
            0 (encoding l).val
            (replayStarts prims x z.2.1.1 topLayer
              (topKey (XmssSecurity.topKeyOf forgery.signature.leafIndex)) l)) ∧
          ActualTopCodeword z.2.1.1 x.1 forgery.signature.leafIndex forgery.message
            (XmssSecurity.Bridge.toModelSig forgery.signature) encoding ∧
          ∀ l, ∃ finish, DeterministicSigning.Resolves (SigningDescentProof.thView z.2.1.1)
            (XmssSecurity.Concrete.topChainWalk x.1 (XmssSecurity.topKeyOf forgery.signature.leafIndex) l
              (encoding l).val (XmssSecurity.chainLength - 1 - (encoding l).val)
              ((XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue l) :
                OracleComp XmssSecurity.HashSpec _) finish := by
  obtain ⟨r, hr, _, top, state, forgery, hsome, encoding, hvalid, hdepth, hauth, hcode, hsuffix⟩ :=
    forestException_authentic prims A x z hz hex
  have hgrow := (recordReads_resolves (forestRun x) ∅ z.2.1.1
    (by intro input output hh; cases hh) r hr).1
  have he : (z.1, z.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
    rw [← loggedRun_forget, support_map]
    exact Set.mem_image_of_mem _ hz
  have htop := exposedRun_top_resolves prims A x (z.1, z.2.1) he hex.1.1 top state forgery hsome
  refine ⟨top, state, forgery, hsome, encoding, hvalid, hdepth, fun l => ?_, hcode, hsuffix⟩
  exact (hauth l).trans (resolves_referenceTop_walks prims x z.2.1.1 r.2 hgrow top htop
    _ l (encoding l).val (by have hh : (encoding l).val < 4 := (encoding l).isLt; omega))

/-- Partition the exceptional event by the forgery's top key. The gate for
each part is fixed by that key before the adversary runs. -/
def ForestExceptionAt (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (z : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C)) : Prop :=
  ForestException prims x z ∧ ∃ top state forgery,
    z.1.2 = some (top, state, forgery) ∧ XmssSecurity.topKeyOf forgery.signature.leafIndex = b

set_option maxRecDepth 100000 in
/-- The actual instrumented adversary never opens the key of an exceptional
forgery. This connects the semantic handler bit to the final winning event. -/
theorem forestExceptionAt_no_opened (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight))
    (r : ((((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × Bool) × LoggedState C))
    (hr : r ∈ support (openedLoggedRun prims A x b))
    (hex : ForestExceptionAt prims x b (r.1.1, r.2)) : r.1.2 = false := by
  cases hopen : r.1.2 with
  | false => rfl
  | true =>
    exfalso
    have hforget : (fun z => (z.1, z.2.1)) <$> openedLoggedRun prims A x b =
        ((simulateQ (SigningCacheProof.countImpl prims) (openedFinalRun A x b)).run (∅, 0)) :=
      SigningCoreProof.simulateQ_run_forget _ _
        (fun t s log => by simp [loggedImpl, Functor.map_map]) _ _ _
    have hc : (r.1, r.2.1) ∈ support
        ((simulateQ (SigningCacheProof.countImpl prims) (openedFinalRun A x b)).run (∅, 0)) := by
      rw [← hforget, support_map]
      exact Set.mem_image_of_mem _ hr
    obtain ⟨top, state, forgery, hsome, output, hresolved⟩ :=
      openedFinalRun_resolves prims A x b (∅, 0) (r.1, r.2.1) hc hopen
    obtain ⟨top', state', forgery', hsome', hkey⟩ := hex.2
    have htuple := Option.some.inj (hsome'.symm.trans hsome)
    cases htuple
    have hz : (r.1.1, r.2) ∈ support (loggedRun prims A x) := by
      rw [← openedLoggedRun_forget prims A x b, support_map]
      exact Set.mem_image_of_mem _ hr
    have hb : treeOf forgery.signature.leafIndex = b := hkey
    rw [← hb] at hresolved
    exact forestException_unopened prims A x (r.1.1, r.2) hz hex.1 top state forgery hsome output hresolved

set_option maxRecDepth 100000 in
/-- Adding the semantic unopened condition loses no exceptional-event mass.
The real program and its complete raw transcript are preserved. -/
theorem forestExceptionAt_unopened_probability (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    Pr[ForestExceptionAt prims x b | loggedRun prims A x] =
      Pr[fun r => ForestExceptionAt prims x b (r.1.1, r.2) ∧ r.1.2 = false |
        openedLoggedRun prims A x b] := by
  rw [← openedLoggedRun_forget prims A x b, probEvent_map]
  exact probEvent_congr' (fun r hr => ⟨fun h => ⟨h, forestExceptionAt_no_opened prims A x b r hr h⟩,
    fun h => h.1⟩) rfl

set_option maxRecDepth 100000 in
/-- The exceptional event can be analyzed in a program that aborts before
opening the forged bottom key during the adversary; verification remains real. -/
theorem forestExceptionAt_stopped_probability (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) :
    Pr[ForestExceptionAt prims x b | loggedRun prims A x] =
    Pr[ForestExceptionAt prims x b |
      (simulateQ (loggedImpl prims) (unopenedFinalRun A x b)).run loggedInit] := by
  rw [forestExceptionAt_unopened_probability prims A x b]
  symm
  apply unopenedFinalRun_probability
  intro flags s hex
  obtain ⟨top, state, forgery, hsome, _⟩ := hex.2
  cases hsome

set_option maxRecDepth 100000 in
/-- The unopened-event identity also holds after conditioning on any supported
instrumented prefix; it is not merely an unconditional probability identity. -/
theorem forestExceptionAt_unopened_prefix (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) (n : ℕ)
    (rest : OracleComp (WorldSpec C) (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × Bool))
    (s : LoggedState C)
    (hp : (rest, s) ∈ support ((simulateQ (loggedImpl prims)
      (prefixRun (openedFinalRun A x b) n)).run loggedInit)) :
    Pr[fun r => ForestExceptionAt prims x b (r.1.1, r.2) |
      (simulateQ (loggedImpl prims) rest).run s] =
    Pr[fun r => ForestExceptionAt prims x b (r.1.1, r.2) ∧ r.1.2 = false |
      (simulateQ (loggedImpl prims) rest).run s] := by
  apply probEvent_congr' _ rfl
  intro r hr
  constructor
  · intro hex
    exact ⟨hex, forestExceptionAt_no_opened prims A x b r
      (prefixRun_support_resume prims (openedFinalRun A x b) n rest s hp r hr) hex⟩
  · exact And.left

set_option maxRecDepth 100000 in
/-- The original query cap remains valid on every continuation of any
supported program prefix, as required by the conditional gate analysis. -/
theorem prefixRun_count_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (n : ℕ) (rest : OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)))
    (s : LoggedState C)
    (hp : (rest, s) ∈ support ((simulateQ (loggedImpl prims)
      (prefixRun (SigningDescentProof.finalRun A x) n)).run loggedInit)) :
    ∀ z ∈ support ((simulateQ (loggedImpl prims) rest).run s), z.2.1.2 ≤ q := by
  intro z hz
  have hfull := prefixRun_support_resume prims (SigningDescentProof.finalRun A x) n rest s hp z hz
  apply exposedRun_count_le prims A x q hq (z.1, z.2.1)
  rw [← loggedRun_forget, support_map]
  exact Set.mem_image_of_mem _ hfull

set_option maxRecDepth 100000 in
/-- A matching reserve is exactly the exceptional unopened-event probability
at a supported instrumented prefix, with the same cache, count, and transcript. -/
theorem continuationReserve_unopened (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : Fin (2 ^ layerHeight)) (gate : (WorldSpec C).Domain) (s : LoggedState C)
    (k : (WorldSpec C).Range gate → OracleComp (WorldSpec C)
      ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)))
    (hs : RawReachable prims s)
    (hk : transcriptResidual (SigningDescentProof.finalRun A x) s.2 =
      some (OracleComp.queryBind gate k)) :
    ∃ n instrumented,
      (instrumented, s) ∈ support ((simulateQ (loggedImpl prims)
        (prefixRun (openedFinalRun A x b) n)).run loggedInit) ∧
      Prod.fst <$> instrumented = OracleComp.queryBind gate k ∧
      (∑' r, Pr[= r | (loggedImpl prims gate).run s] *
        continuationReserve prims (SigningDescentProof.finalRun A x) (ForestExceptionAt prims x b) r.2) =
      Pr[fun r => ForestExceptionAt prims x b (r.1.1, r.2) ∧ r.1.2 = false |
        (simulateQ (loggedImpl prims) instrumented).run s] := by
  obtain ⟨n, hp⟩ := rawReachable_prefix prims s hs (SigningDescentProof.finalRun A x) _ hk
  obtain ⟨instrumented, hi, he⟩ := prefixRun_opened_lift prims A x b n _ s hp
  refine ⟨n, instrumented, hi, he, ?_⟩
  rw [continuationReserve_matchingQuery prims _ _ gate s k hk, ← he,
    simulateQ_map, StateT.run_map, probEvent_map]
  exact forestExceptionAt_unopened_prefix prims A x b n instrumented s hi

namespace LayeredGraph

variable {State : Type} [DecidableEq State]

/-- Follow the queried rows until the first uncached vertex. Layers are
relative to the supplied suffix of the table. -/
def root : List (State → Option State) → State → ℕ × State
  | [], input => (0, input)
  | row :: rows, input => match row input with
    | none => (0, input)
    | some output => let r := root rows output; (r.1 + 1, r.2)

/-- Insert one fresh directed edge in the layer-indexed query table. -/
def insertEdge : List (State → Option State) → ℕ → State → State → List (State → Option State)
  | [], _, _, _ => []
  | row :: rows, 0, input, output => Function.update row input (some output) :: rows
  | row :: rows, layer + 1, input, output => row :: insertEdge rows layer input output

/-- The forward root is changed precisely for the component ending at the
fresh query input. No injectivity assumption on the other components is needed. -/
theorem root_insertEdge (rows : List (State → Option State)) (layer : ℕ)
    (input output start : State) (hlayer : layer < rows.length)
    (hfresh : rows[layer] input = none) :
    root (insertEdge rows layer input output) start =
      if root rows start = (layer, input) then
        let r := root (rows.drop (layer + 1)) output; (layer + 1 + r.1, r.2)
      else root rows start := by
  induction rows generalizing layer start with
  | nil => simp at hlayer
  | cons row rows ih =>
    cases layer with
    | zero =>
      change row input = none at hfresh
      by_cases hs : start = input
      · subst start
        simp [insertEdge, root, hfresh, Nat.add_comm]
      · cases hr : row start with
        | none => simp [insertEdge, root, hs, hr]
        | some next => simp [insertEdge, root, hs, hr]
    | succ layer =>
      cases hr : row start with
      | none => simp [insertEdge, root, hr]
      | some next =>
        have hl : layer < rows.length := by simpa using hlayer
        have hf : rows[layer] input = none := by simpa using hfresh
        simp only [insertEdge, root, hr, ih layer next hl hf]
        have hcond : ((root rows next).1 + 1, (root rows next).2) = (layer + 1, input) ↔
            root rows next = (layer, input) := by simp [Prod.ext_iff]
        simp only [hcond]
        by_cases h : root rows next = (layer, input)
        · simp only [h, ↓reduceIte, List.drop_succ_cons, Prod.mk.injEq, and_true]
          omega
        · simp [h]

theorem root_layer_le (rows : List (State → Option State)) (start : State) :
    (root rows start).1 ≤ rows.length := by
  induction rows generalizing start with
  | nil => simp [root]
  | cons row rows ih =>
    cases h : row start <;> simp [root, h, ih]

theorem drop_insertEdge (rows : List (State → Option State)) (skip layer : ℕ)
    (input output : State) :
    (insertEdge rows (skip + layer) input output).drop skip =
      insertEdge (rows.drop skip) layer input output := by
  induction skip generalizing rows with
  | zero => simp
  | succ skip ih =>
    cases rows with
    | nil => simp [insertEdge]
    | cons row rows => simpa [insertEdge, Nat.succ_add] using ih rows

theorem drop_insertEdge_of_lt (rows : List (State → Option State)) (skip layer : ℕ)
    (input output : State) (h : layer < skip) :
    (insertEdge rows layer input output).drop skip = rows.drop skip := by
  induction skip generalizing rows layer with
  | zero => omega
  | succ skip ih =>
    cases rows with
    | nil => simp [insertEdge]
    | cons row rows =>
      cases layer with
      | zero => simp [insertEdge]
      | succ layer => simpa [insertEdge] using ih rows layer (by omega)

/-- Absolute-layer forward root of a vertex in the finite layered table. -/
def rootFrom (rows : List (State → Option State)) (layer : ℕ) (input : State) : ℕ × State :=
  let r := root (rows.drop layer) input; (layer + r.1, r.2)

theorem rootFrom_layer (rows : List (State → Option State)) (layer : ℕ) (input : State) :
    layer ≤ (rootFrom rows layer input).1 := by simp [rootFrom]

/-- Insertion changes exactly one root fiber, for vertices at every layer. -/
theorem rootFrom_insertEdge (rows : List (State → Option State)) (layer : ℕ)
    (input output : State) (hlayer : layer < rows.length)
    (hfresh : rows[layer] input = none) (startLayer : ℕ) (start : State) :
    rootFrom (insertEdge rows layer input output) startLayer start =
      if rootFrom rows startLayer start = (layer, input) then
        rootFrom rows (layer + 1) output else rootFrom rows startLayer start := by
  by_cases hle : startLayer ≤ layer
  · have hs : startLayer + (layer - startLayer) = layer := by omega
    have hd : layer - startLayer < (rows.drop startLayer).length := by
      rw [List.length_drop]
      omega
    have hf : (rows.drop startLayer)[layer - startLayer] input = none := by
      rw [List.getElem_drop]
      apply Eq.trans (b := rows[layer] input) _ hfresh
      exact congrArg (fun i : Fin rows.length => rows[i.val] input)
        (Fin.ext hs : (⟨startLayer + (layer - startLayer), by omega⟩ : Fin rows.length) = ⟨layer, hlayer⟩)
    have hdrop : (insertEdge rows layer input output).drop startLayer =
        insertEdge (rows.drop startLayer) (layer - startLayer) input output := by
      simpa only [hs] using drop_insertEdge rows startLayer (layer - startLayer) input output
    unfold rootFrom
    rw [hdrop, root_insertEdge _ _ input output start hd hf]
    simp only [List.drop_drop]
    have he : (startLayer + (root (rows.drop startLayer) start).1,
        (root (rows.drop startLayer) start).2) = (layer, input) ↔
        root (rows.drop startLayer) start = (layer - startLayer, input) := by
      simp only [Prod.ext_iff]
      apply and_congr_left
      intro _
      calc
        (startLayer + (root (rows.drop startLayer) start).1 = layer) ↔
          startLayer + (root (rows.drop startLayer) start).1 = startLayer + (layer - startLayer) := by
            rw [hs]
        _ ↔ _ := Nat.add_left_cancel_iff
    simp only [he]
    by_cases hr : root (rows.drop startLayer) start = (layer - startLayer, input)
    · simp only [hr, ↓reduceIte, Prod.mk.injEq]
      have hsum : startLayer + (layer - startLayer + 1) = layer + 1 := by omega
      rw [hsum]
      constructor
      · omega
      · rfl
    · simp [hr]
  · have hlt : layer < startLayer := by omega
    have hn : rootFrom rows startLayer start ≠ (layer, input) := by
      intro he
      have hl := rootFrom_layer rows startLayer start
      rw [he] at hl
      omega
    rw [if_neg hn]
    simp only [rootFrom, drop_insertEdge_of_lt rows startLayer layer input output hlt]

/-- A cached edge, with absent layers treated as empty. -/
def edge (rows : List (State → Option State)) (layer : ℕ) (input : State) : Option State :=
  (rows[layer]?).bind (fun row => row input)

theorem edge_insertEdge (rows : List (State → Option State)) (layer : ℕ)
    (input output : State) (hlayer : layer < rows.length) (atLayer : ℕ) (atInput : State) :
    edge (insertEdge rows layer input output) atLayer atInput =
      if atLayer = layer ∧ atInput = input then some output else edge rows atLayer atInput := by
  induction rows generalizing layer atLayer with
  | nil => simp at hlayer
  | cons row rows ih =>
    cases layer <;> cases atLayer <;>
      simp_all [insertEdge, edge, Function.update_apply]

theorem rootFrom_insertEdge_mono (rows : List (State → Option State)) (layer : ℕ)
    (input output : State) (hlayer : layer < rows.length)
    (hfresh : rows[layer] input = none) (atLayer : ℕ) (atInput : State) :
    (rootFrom rows atLayer atInput).1 ≤
      (rootFrom (insertEdge rows layer input output) atLayer atInput).1 := by
  rw [rootFrom_insertEdge rows layer input output hlayer hfresh]
  split
  · rename_i h
    rw [h]
    exact (Nat.le_succ layer).trans (rootFrom_layer rows (layer + 1) output)
  · exact le_rfl

variable [Fintype State]

/-- Queried edges whose forward root is strictly below the current head. -/
def pending (rows : List (State → Option State)) (layers head : ℕ) : Finset (Fin layers × State) :=
  Finset.univ.filter fun v => (edge rows v.1.val v.2).isSome ∧ (rootFrom rows v.1.val v.2).1 < head

/-- Fresh insertion creates at most one pending edge. Existing pending
components can merge or disappear, but cannot acquire duplicate credit. -/
theorem pending_insertEdge_le (rows : List (State → Option State)) (layers head layer : ℕ)
    (input output : State) (hlayer : layer < rows.length) (hbound : rows.length ≤ layers)
    (hfresh : rows[layer] input = none) :
    (pending (insertEdge rows layer input output) layers head).card ≤
      (pending rows layers head).card + 1 := by
  let vertex : Fin layers × State := (⟨layer, hlayer.trans_le hbound⟩, input)
  have hsub : pending (insertEdge rows layer input output) layers head ⊆
      insert vertex (pending rows layers head) := by
    intro v hv
    by_cases he : v = vertex
    · exact Finset.mem_insert.mpr (Or.inl he)
    · apply Finset.mem_insert.mpr
      right
      simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have hne : ¬(v.1.val = layer ∧ v.2 = input) := by
        rintro ⟨hi, hx⟩
        apply he
        exact Prod.ext (Fin.ext hi) hx
      rw [edge_insertEdge rows layer input output hlayer, if_neg hne] at hv
      exact ⟨hv.1, lt_of_le_of_lt
        (rootFrom_insertEdge_mono rows layer input output hlayer hfresh v.1.val v.2) hv.2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- All already queried edges of a component, indexed by its forward root. -/
def component (rows : List (State → Option State)) (layers layer : ℕ) (input : State) :
    Finset (Fin layers × State) :=
  Finset.univ.filter fun v => (edge rows v.1.val v.2).isSome ∧ rootFrom rows v.1.val v.2 = (layer, input)

theorem component_pending (rows : List (State → Option State)) (layers layer : ℕ) (input : State) :
    component rows layers layer input ⊆ pending rows layers (layer + 1) := by
  intro v hv
  simp only [component, pending, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact ⟨hv.1, by rw [hv.2]; exact Nat.lt_succ_self layer⟩

/-- At the head boundary the entire input component leaves the pending set,
on both a hit and a miss. Branched components are counted without pruning. -/
theorem pending_insertEdge_boundary (rows : List (State → Option State)) (layers layer : ℕ)
    (input output : State) (hlayer : layer < rows.length) (hfresh : rows[layer] input = none) :
    pending (insertEdge rows layer input output) layers (layer + 1) =
      pending rows layers (layer + 1) \ component rows layers layer input := by
  ext v
  simp only [pending, component, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [edge_insertEdge rows layer input output hlayer,
    rootFrom_insertEdge rows layer input output hlayer hfresh]
  by_cases hroot : rootFrom rows v.1.val v.2 = (layer, input)
  · simp only [hroot, ↓reduceIte, Nat.lt_succ_self, and_true, and_self]
    have hge := rootFrom_layer rows (layer + 1) output
    simp only [not_lt_of_ge hge, and_false, false_iff, not_and]
    intro h hn
    exact hn h
  · have hne : ¬(v.1.val = layer ∧ v.2 = input) := by
      rintro ⟨hi, hx⟩
      apply hroot
      simp only [hi, hx, rootFrom]
      have hd : (rows.drop layer)[0]? = some rows[layer] := by
        simp [List.getElem?_drop, List.getElem?_eq_getElem hlayer]
      cases hdrop : rows.drop layer with
      | nil => simp [hdrop] at hd
      | cons row tail =>
        simp only [hdrop, List.getElem?_cons_zero, Option.some.injEq] at hd
        simp [root, hd, hfresh]
    simp [hroot, hne]

theorem pending_insertEdge_boundary_card (rows : List (State → Option State)) (layers layer : ℕ)
    (input output : State) (hlayer : layer < rows.length) (hfresh : rows[layer] input = none) :
    (pending (insertEdge rows layer input output) layers (layer + 1)).card +
        (component rows layers layer input).card = (pending rows layers (layer + 1)).card := by
  rw [pending_insertEdge_boundary rows layers layer input output hlayer hfresh]
  exact Finset.card_sdiff_add_card_eq_card (component_pending rows layers layer input)

theorem rootFrom_gt_of_edge (rows : List (State → Option State)) (layer : ℕ) (input : State)
    (h : (edge rows layer input).isSome) : layer < (rootFrom rows layer input).1 := by
  cases hr : rows[layer]? with
  | none => simp [edge, hr] at h
  | some row =>
    have hd : (rows.drop layer)[0]? = some row := by
      simpa only [List.getElem?_drop, Nat.add_zero] using hr
    cases hdrop : rows.drop layer with
    | nil => simp [hdrop] at hd
    | cons first tail =>
      simp only [hdrop, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst first
      cases hv : row input with
      | none => simp [edge, hr, hv] at h
      | some value => simp [rootFrom, hdrop, root, hv, Nat.add_assoc]

theorem pending_eq_empty_of_head_le_one (rows : List (State → Option State)) (layers head : ℕ)
    (hh : head ≤ 1) : pending rows layers head = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hgt := rootFrom_gt_of_edge rows v.1.val v.2 hv.1
  omega

theorem pending_mono (rows : List (State → Option State)) (layers head head' : ℕ)
    (hh : head ≤ head') : pending rows layers head ⊆ pending rows layers head' := by
  intro v hv
  simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact ⟨hv.1, hv.2.trans_le hh⟩

/-- An unbranched component has at most one queried vertex per preceding
layer, so at a three-layer boundary its size is at most two. -/
theorem component_card_le (rows : List (State → Option State)) (layers layer : ℕ) (input : State)
    (hinj : Set.InjOn (fun v : Fin layers × State => v.1.val) (component rows layers layer input)) :
    (component rows layers layer input).card ≤ layer := by
  classical
  calc
    _ = ((component rows layers layer input).image fun v => v.1.val).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range layer).card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      simp only [component, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hgt := rootFrom_gt_of_edge rows v.1.val v.2 hv.1
      rw [hv.2] at hgt
      exact Finset.mem_range.mpr hgt
    _ = layer := Finset.card_range layer

theorem rootFrom_fresh (rows : List (State → Option State)) (layer : ℕ) (input : State)
    (hlayer : layer < rows.length) (hfresh : rows[layer] input = none) :
    rootFrom rows layer input = (layer, input) := by
  have hd : (rows.drop layer)[0]? = some rows[layer] := by
    simp [List.getElem?_drop, List.getElem?_eq_getElem hlayer]
  cases hdrop : rows.drop layer with
  | nil => simp [hdrop] at hd
  | cons row tail =>
    simp only [hdrop, List.getElem?_cons_zero, Option.some.injEq] at hd
    simp [rootFrom, hdrop, root, hd, hfresh]

/-- A fresh query either leaves a higher endpoint's component unchanged or
joins the input component and the new edge to it. -/
theorem component_insertEdge (rows : List (State → Option State)) (layers layer targetLayer : ℕ)
    (input output target : State) (hlayer : layer < rows.length) (hbound : rows.length ≤ layers)
    (hfresh : rows[layer] input = none) (htarget : layer < targetLayer) :
    component (insertEdge rows layer input output) layers targetLayer target =
      if rootFrom rows (layer + 1) output = (targetLayer, target) then
        insert (⟨layer, hlayer.trans_le hbound⟩, input)
          (component rows layers targetLayer target ∪ component rows layers layer input)
      else component rows layers targetLayer target := by
  have hn : (layer, input) ≠ (targetLayer, target) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hf : edge rows layer input = none := by
    simp [edge, List.getElem?_eq_getElem hlayer, hfresh]
  ext v
  by_cases he : v = (⟨layer, hlayer.trans_le hbound⟩, input)
  · subst v
    by_cases ht : rootFrom rows (layer + 1) output = (targetLayer, target) <;>
      simp [ht, component, edge_insertEdge rows layer input output hlayer,
      rootFrom_insertEdge rows layer input output hlayer hfresh,
      rootFrom_fresh rows layer input hlayer hfresh, hf]
  · have hne : ¬(v.1.val = layer ∧ v.2 = input) := by
      rintro ⟨hi, hx⟩
      exact he (Prod.ext (Fin.ext hi) hx)
    simp only [component, Finset.mem_filter, Finset.mem_univ, true_and,
      edge_insertEdge rows layer input output hlayer, if_neg hne,
      rootFrom_insertEdge rows layer input output hlayer hfresh]
    by_cases hr : rootFrom rows v.1.val v.2 = (layer, input)
    · by_cases ht : rootFrom rows (layer + 1) output = (targetLayer, target) <;>
        simp [ht, hr, hn, he]
    · by_cases ht : rootFrom rows (layer + 1) output = (targetLayer, target) <;>
        simp [ht, hr, he]

/-- The two old components are disjoint because every vertex has one root. -/
theorem component_disjoint (rows : List (State → Option State)) (layers i j : ℕ)
    (x y : State) (h : (i, x) ≠ (j, y)) :
    Disjoint (component rows layers i x) (component rows layers j y) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
  exact h (hv.2.symm.trans hw.2)

theorem component_insertEdge_card (rows : List (State → Option State)) (layers layer targetLayer : ℕ)
    (input output target : State) (hlayer : layer < rows.length) (hbound : rows.length ≤ layers)
    (hfresh : rows[layer] input = none) (htarget : layer < targetLayer)
    (hhit : rootFrom rows (layer + 1) output = (targetLayer, target)) :
    (component (insertEdge rows layer input output) layers targetLayer target).card =
      (component rows layers targetLayer target).card + (component rows layers layer input).card + 1 := by
  rw [component_insertEdge rows layers layer targetLayer input output target hlayer hbound hfresh htarget,
    if_pos hhit, Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint]
    apply component_disjoint
    intro h
    have := congrArg Prod.fst h
    omega
  · simp [component, edge, List.getElem?_eq_getElem hlayer, hfresh]

/-- Old endpoint branches cannot disappear when more rows are queried. -/
theorem component_insertEdge_subset (rows : List (State → Option State)) (layers layer targetLayer : ℕ)
    (input output target : State) (hlayer : layer < rows.length) (hbound : rows.length ≤ layers)
    (hfresh : rows[layer] input = none) (htarget : layer < targetLayer) :
    component rows layers targetLayer target ⊆
      component (insertEdge rows layer input output) layers targetLayer target := by
  rw [component_insertEdge rows layers layer targetLayer input output target hlayer hbound hfresh htarget]
  split
  · exact Finset.Subset.trans Finset.subset_union_left (Finset.subset_insert _ _)
  · exact Finset.Subset.refl _

/-- Every layer traversed on the way to a root contains a queried vertex
with that same root. -/
theorem root_has_vertex (rows : List (State → Option State)) (start : State) (layer : ℕ)
    (hlayer : layer < (root rows start).1) :
    ∃ input, (edge rows layer input).isSome ∧ rootFrom rows layer input = root rows start := by
  induction rows generalizing start layer with
  | nil => simp [root] at hlayer
  | cons row rows ih =>
    cases hr : row start with
    | none => simp [root, hr] at hlayer
    | some next =>
      cases layer with
      | zero => exact ⟨start, by simp [edge, hr], by simp [rootFrom]⟩
      | succ layer =>
        have hl : layer < (root rows next).1 := by simpa [root, hr] using hlayer
        obtain ⟨input, hi, he⟩ := ih next layer hl
        refine ⟨input, by simpa [edge] using hi, ?_⟩
        have h := congrArg (fun r : ℕ × State => (r.1 + 1, r.2)) he
        simpa [rootFrom, root, hr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem rootFrom_drop (rows : List (State → Option State)) (skip layer : ℕ) (input : State) :
    let r := rootFrom (rows.drop skip) layer input
    (skip + r.1, r.2) = rootFrom rows (skip + layer) input := by
  simp [rootFrom, List.drop_drop, Nat.add_assoc]

theorem rootFrom_has_vertex (rows : List (State → Option State)) (startLayer : ℕ) (start : State)
    (layer : ℕ) (hlo : startLayer ≤ layer) (hhi : layer < (rootFrom rows startLayer start).1) :
    ∃ input, (edge rows layer input).isSome ∧
      rootFrom rows layer input = rootFrom rows startLayer start := by
  have hs : startLayer + (layer - startLayer) = layer := Nat.add_sub_of_le hlo
  have hl : layer - startLayer < (root (rows.drop startLayer) start).1 := by
    simp only [rootFrom] at hhi
    omega
  obtain ⟨input, hi, he⟩ := root_has_vertex (rows.drop startLayer) start (layer - startLayer) hl
  refine ⟨input, ?_, ?_⟩
  · simpa only [edge, List.getElem?_drop, hs] using hi
  · have hd := rootFrom_drop rows startLayer (layer - startLayer) input
    rw [hs] at hd
    rw [← hd, he]
    rfl

/-- The queried layers of a component form a final interval below its root. -/
theorem component_layer_exists (rows : List (State → Option State)) (layers targetLayer : ℕ)
    (target : State) (v : Fin layers × State) (hv : v ∈ component rows layers targetLayer target)
    (layer : ℕ) (hlo : v.1.val ≤ layer) (hhi : layer < targetLayer) (hbound : targetLayer ≤ layers) :
    ∃ w ∈ component rows layers targetLayer target, w.1.val = layer := by
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨input, hi, he⟩ := rootFrom_has_vertex rows v.1.val v.2 layer hlo (by simpa [hv.2] using hhi)
  refine ⟨(⟨layer, hhi.trans_le hbound⟩, input), ?_, rfl⟩
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hi, he.trans hv.2⟩

/-- In an unbranched component of size d, every layer at least rootLayer−d
and below the root is occupied. This supplies the internal-suffix collision test. -/
theorem component_suffix_layer (rows : List (State → Option State)) (layers targetLayer : ℕ)
    (target : State)
    (hinj : Set.InjOn (fun v : Fin layers × State => v.1.val) (component rows layers targetLayer target))
    (layer : ℕ) (hlo : targetLayer - (component rows layers targetLayer target).card ≤ layer)
    (hhi : layer < targetLayer) (hbound : targetLayer ≤ layers) :
    ∃ v ∈ component rows layers targetLayer target, v.1.val = layer := by
  classical
  by_contra hn
  have hlow : ∀ v ∈ component rows layers targetLayer target, layer < v.1.val := by
    intro v hv
    by_contra hl
    exact hn (component_layer_exists rows layers targetLayer target v hv layer (by omega) hhi hbound)
  have hcard : (component rows layers targetLayer target).card ≤ targetLayer - (layer + 1) := by
    calc
      _ = ((component rows layers targetLayer target).image fun v => v.1.val).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico (layer + 1) targetLayer).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
        have hlo' := hlow v hv
        simp only [component, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hgt := rootFrom_gt_of_edge rows v.1.val v.2 hv.1
        rw [hv.2] at hgt
        exact Finset.mem_Ico.mpr ⟨by omega, hgt⟩
      _ = _ := Nat.card_Ico _ _
  omega

theorem rootFrom_of_edge_none (rows : List (State → Option State)) (layer : ℕ) (input : State)
    (h : edge rows layer input = none) : rootFrom rows layer input = (layer, input) := by
  have he : edge rows layer input = edge (rows.drop layer) 0 input := by
    simp [edge, List.getElem?_drop]
  rw [he] at h
  cases hdrop : rows.drop layer with
  | nil => simp [rootFrom, hdrop, root]
  | cons row tail =>
    simp only [hdrop, edge, List.getElem?_cons_zero, Option.bind_some] at h
    simp [rootFrom, hdrop, root, h]

theorem edge_some_of_rootFrom_gt (rows : List (State → Option State)) (layer : ℕ) (input : State)
    (h : layer < (rootFrom rows layer input).1) : (edge rows layer input).isSome := by
  cases he : edge rows layer input with
  | none =>
    have hr := rootFrom_of_edge_none rows layer input he
    simp [hr] at h
  | some output => rfl

/-- No vertex of a component can lie below rootLayer minus its number of
queried edges. This uses its actual forward paths, not a graph assumption. -/
theorem component_layer_ge (rows : List (State → Option State)) (layers targetLayer : ℕ)
    (target : State) (hbound : targetLayer ≤ layers) (v : Fin layers × State)
    (hv : v ∈ component rows layers targetLayer target) :
    targetLayer - (component rows layers targetLayer target).card ≤ v.1.val := by
  classical
  have hsub : Finset.Ico v.1.val targetLayer ⊆
      (component rows layers targetLayer target).image (fun w => w.1.val) := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    obtain ⟨w, hw, he⟩ := component_layer_exists rows layers targetLayer target v hv i hlo hhi hbound
    exact Finset.mem_image.mpr ⟨w, hw, he⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  rw [Nat.card_Ico] at hcard
  omega

theorem pending_insertEdge_nonincrease (rows : List (State → Option State)) (layers head layer : ℕ)
    (input output : State) (hlayer : layer < rows.length) (hfresh : rows[layer] input = none)
    (hhead : head ≤ layer + 1) :
    pending (insertEdge rows layer input output) layers head ⊆ pending rows layers head := by
  intro v hv
  simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  have hne : ¬(v.1.val = layer ∧ v.2 = input) := by
    rintro ⟨hi, hx⟩
    have hr := rootFrom_insertEdge rows layer input output hlayer hfresh layer input
    simp only [rootFrom_fresh rows layer input hlayer hfresh, ↓reduceIte] at hr
    have hgt := rootFrom_layer rows (layer + 1) output
    rw [hi, hx, hr] at hv
    omega
  rw [edge_insertEdge rows layer input output hlayer, if_neg hne] at hv
  exact ⟨hv.1, lt_of_le_of_lt
    (rootFrom_insertEdge_mono rows layer input output hlayer hfresh v.1.val v.2) hv.2⟩

/-- An insertion below the suffix head cannot already connect to the endpoint. -/
theorem no_hit_below_head (rows : List (State → Option State)) (layers layer targetLayer : ℕ)
    (output target : State) (hbound : targetLayer ≤ layers)
    (hbelow : layer + 1 < targetLayer - (component rows layers targetLayer target).card) :
    rootFrom rows (layer + 1) output ≠ (targetLayer, target) := by
  intro he
  have hlt : layer + 1 < targetLayer := lt_of_lt_of_le hbelow (Nat.sub_le _ _)
  have hsome := edge_some_of_rootFrom_gt rows (layer + 1) output (by simpa [he] using hlt)
  let v : Fin layers × State := (⟨layer + 1, hlt.trans_le hbound⟩, output)
  have hv : v ∈ component rows layers targetLayer target := by
    simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hsome, he⟩
  have hge := component_layer_ge rows layers targetLayer target hbound v hv
  change _ ≤ layer + 1 at hge
  omega

/-- Joining an internal suffix node creates a second vertex at an occupied
layer. Such a branch permanently kills the marked endpoint component. -/
theorem hit_above_head_branches (rows : List (State → Option State)) (layers layer targetLayer : ℕ)
    (input output target : State) (hlayer : layer < rows.length) (hbound : rows.length ≤ layers)
    (hfresh : rows[layer] input = none) (htarget : layer < targetLayer) (hend : targetLayer ≤ layers)
    (hinj : Set.InjOn (fun v : Fin layers × State => v.1.val) (component rows layers targetLayer target))
    (hhead : targetLayer - (component rows layers targetLayer target).card ≤ layer)
    (hhit : rootFrom rows (layer + 1) output = (targetLayer, target)) :
    ¬Set.InjOn (fun v : Fin layers × State => v.1.val)
      (component (insertEdge rows layer input output) layers targetLayer target) := by
  intro hnew
  obtain ⟨v, hv, hi⟩ := component_suffix_layer rows layers targetLayer target hinj layer hhead htarget hend
  have hv' := component_insertEdge_subset rows layers layer targetLayer input output target
    hlayer hbound hfresh htarget hv
  let q : Fin layers × State := (⟨layer, hlayer.trans_le hbound⟩, input)
  have hq : q ∈ component (insertEdge rows layer input output) layers targetLayer target := by
    rw [component_insertEdge rows layers layer targetLayer input output target hlayer hbound hfresh htarget,
      if_pos hhit]
    exact Finset.mem_insert_self _ _
  have he : v = q := hnew hv' hq hi
  rw [he] at hv
  simp [q, component, edge, List.getElem?_eq_getElem hlayer, hfresh] at hv

/-- The head has exactly one value whose continuation reaches an unbranched
endpoint, including the empty-suffix case where the head is the endpoint. -/
theorem head_unique (rows : List (State → Option State)) (layers : ℕ) (target : State)
    (hlen : rows.length = layers)
    (hinj : Set.InjOn (fun v : Fin layers × State => v.1.val) (component rows layers layers target)) :
    ∃ value, ∀ input,
      rootFrom rows (layers - (component rows layers layers target).card) input = (layers, target) ↔
        input = value := by
  classical
  by_cases hz : (component rows layers layers target).card = 0
  · refine ⟨target, fun input => ?_⟩
    simp only [hz, Nat.sub_zero, rootFrom]
    simp only [← hlen, List.drop_length, root, Nat.add_zero, Prod.mk.injEq, true_and]
  · have hc := component_card_le rows layers layers target hinj
    have hhead : layers - (component rows layers layers target).card < layers := by omega
    obtain ⟨v, hv, hi⟩ := component_suffix_layer rows layers layers target hinj
      (layers - (component rows layers layers target).card) le_rfl hhead le_rfl
    refine ⟨v.2, fun input => ⟨fun he => ?_, fun he => ?_⟩⟩
    · let w : Fin layers × State := (⟨layers - (component rows layers layers target).card, hhead⟩, input)
      have hw : w ∈ component rows layers layers target := by
        simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨edge_some_of_rootFrom_gt rows
          (layers - (component rows layers layers target).card) input
          (by simpa only [he] using hhead), he⟩
      exact congrArg Prod.snd (hinj hw hv hi.symm)
    · subst input
      have hr := (Finset.mem_filter.mp hv).2.2
      simpa only [hi] using hr

/-- The concrete graph potential, killed when the endpoint component branches. -/
def weight (N : ℝ) (rows : List (State → Option State)) (target : State) : ℝ :=
  open Classical in
  let comp := component rows 3 3 target
  if Set.InjOn (fun v : Fin 3 × State => v.1.val) comp then
    suffixWeight N comp.card (pending rows 3 (3 - comp.card)).card
  else 0

theorem suffixWeight_nonneg (N : ℝ) (hN : 0 < N) (depth pending : ℕ) :
    0 ≤ suffixWeight N depth pending := by unfold suffixWeight; positivity

theorem suffixWeight_mono (N : ℝ) (hN : 0 < N) (depth m n : ℕ) (h : m ≤ n) :
    suffixWeight N depth m ≤ suffixWeight N depth n := by
  unfold suffixWeight
  gcongr

theorem weight_nonneg (N : ℝ) (hN : 0 < N) (rows : List (State → Option State)) (target : State) :
    0 ≤ weight N rows target := by
  dsimp only [weight]
  split
  · exact suffixWeight_nonneg N hN _ _
  · exact le_rfl

/-- An existing endpoint branch stays killed. -/
theorem weight_of_branched (N : ℝ) (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input output : State)
    (hfresh : rows[layer] input = none)
    (hbad : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 3 target)) :
    weight N (insertEdge rows layer input output) target = 0 := by
  have hsub := component_insertEdge_subset rows 3 layer 3 input output target hlayer hlen.le hfresh
    (by omega)
  unfold weight
  rw [if_neg]
  intro h
  exact hbad (h.mono hsub)

/-- Away from a head-boundary query the graph weight has the already-proved
one-edge drift, with branch deaths contributing zero. -/
theorem weight_below_head (N : ℝ) (hN : 0 < N) (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input output : State)
    (hfresh : rows[layer] input = none)
    (hbelow : layer + 1 < 3 - (component rows 3 3 target).card) :
    weight N (insertEdge rows layer input output) target ≤
      (1 + (124 / 3 : ℝ) / N) * weight N rows target := by
  classical
  by_cases hbad : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 3 target)
  · rw [weight_of_branched N rows target hlen layer hlayer input output hfresh hbad]
    exact mul_nonneg (by positivity) (weight_nonneg N hN rows target)
  · have hi := not_not.mp hbad
    have hn := no_hit_below_head rows 3 layer 3 output target le_rfl hbelow
    have hc := component_insertEdge rows 3 layer 3 input output target hlayer hlen.le hfresh (by omega)
    rw [if_neg hn] at hc
    simp only [weight, hc, if_pos hi]
    exact (suffixWeight_mono N hN _ _ _
      (pending_insertEdge_le rows 3 _ layer input output hlayer hlen.le hfresh)).trans
        (suffixWeight_pending N hN _ _)

theorem weight_above_head (N : ℝ) (hN : 0 < N) (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input output : State)
    (hfresh : rows[layer] input = none)
    (habove : 3 - (component rows 3 3 target).card ≤ layer) :
    weight N (insertEdge rows layer input output) target ≤ weight N rows target := by
  classical
  by_cases hbad : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 3 target)
  · rw [weight_of_branched N rows target hlen layer hlayer input output hfresh hbad]
    exact weight_nonneg N hN rows target
  · have hi := not_not.mp hbad
    by_cases hhit : rootFrom rows (layer + 1) output = (3, target)
    · have hb := hit_above_head_branches rows 3 layer 3 input output target hlayer hlen.le hfresh
        (by omega) le_rfl hi habove hhit
      simp only [weight, if_neg hb, if_pos hi]
      exact suffixWeight_nonneg N hN _ _
    · have hc := component_insertEdge rows 3 layer 3 input output target hlayer hlen.le hfresh (by omega)
      rw [if_neg hhit] at hc
      simp only [weight, hc, if_pos hi]
      apply suffixWeight_mono N hN
      exact Finset.card_le_card
        (pending_insertEdge_nonincrease rows 3 _ layer input output hlayer hfresh (by omega))

theorem weight_boundary_miss (N : ℝ) (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input output : State)
    (hfresh : rows[layer] input = none)
    (hinj : Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 3 target))
    (hhead : layer + 1 = 3 - (component rows 3 3 target).card)
    (hmiss : rootFrom rows (layer + 1) output ≠ (3, target)) :
    weight N (insertEdge rows layer input output) target =
      suffixWeight N (component rows 3 3 target).card
        ((pending rows 3 (layer + 1)).card - (component rows 3 layer input).card) := by
  have hc := component_insertEdge rows 3 layer 3 input output target hlayer hlen.le hfresh (by omega)
  rw [if_neg hmiss] at hc
  simp only [weight, hc, if_pos hinj, ← hhead]
  have hp := pending_insertEdge_boundary_card rows 3 layer input output hlayer hfresh
  congr 1
  omega

theorem weight_boundary_hit (N : ℝ) (hN : 0 < N) (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input output : State)
    (hfresh : rows[layer] input = none)
    (hhead : layer + 1 = 3 - (component rows 3 3 target).card)
    (hhit : rootFrom rows (layer + 1) output = (3, target)) :
    weight N (insertEdge rows layer input output) target ≤
      if (component rows 3 3 target).card + (component rows 3 layer input).card = 0 then
        suffixWeight N 1 (pending rows 3 (layer + 1)).card
      else suffixWeight N ((component rows 3 3 target).card + (component rows 3 layer input).card + 1) 0 := by
  classical
  have hc := component_insertEdge_card rows 3 layer 3 input output target hlayer hlen.le hfresh (by omega) hhit
  dsimp only [weight]
  split
  · rename_i hi
    rw [hc]
    split
    · rename_i hz
      rw [hz]
      simp only [Nat.zero_add, Nat.reduceSub]
      apply suffixWeight_mono N hN
      apply Finset.card_le_card
      apply Finset.Subset.trans (pending_mono _ 3 2 (layer + 1) (by omega))
      exact pending_insertEdge_nonincrease rows 3 (layer + 1) layer input output hlayer hfresh le_rfl
    · rename_i hz
      rw [pending_eq_empty_of_head_le_one _ 3 _ (by omega), Finset.card_empty]
  · split <;> exact suffixWeight_nonneg N hN _ _

theorem weight_boundary_branched (N : ℝ) (hN : 0 < N) (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input output : State)
    (hfresh : rows[layer] input = none)
    (hinj : Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 3 target))
    (hhead : layer + 1 = 3 - (component rows 3 3 target).card)
    (hbranch : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 layer input)) :
    weight N (insertEdge rows layer input output) target ≤ weight N rows target := by
  classical
  by_cases hh : rootFrom rows (layer + 1) output = (3, target)
  · have hbad : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val)
        (component (insertEdge rows layer input output) 3 3 target) := by
      intro hi
      apply hbranch
      apply hi.mono
      rw [component_insertEdge rows 3 layer 3 input output target hlayer hlen.le hfresh (by omega), if_pos hh]
      exact Finset.Subset.trans Finset.subset_union_right (Finset.subset_insert _ _)
    simp only [weight, if_neg hbad, if_pos hinj]
    exact suffixWeight_nonneg N hN _ _
  · rw [weight_boundary_miss N rows target hlen layer hlayer input output hfresh hinj hhead hh]
    simp only [weight, if_pos hinj, ← hhead]
    exact suffixWeight_mono N hN _ _ _ (Nat.sub_le _ _)

variable [Nonempty State]

theorem uniform_mean_le_const (f : State → ℝ) (c : ℝ) (h : ∀ input, f input ≤ c) :
    (∑ input, f input) / (Fintype.card State : ℝ) ≤ c := by
  have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ ∑ _input : State, c := Finset.sum_le_sum (fun input _ => h input)
    _ = _ := by simp; ring

/-- Exact single-target averaging, with arbitrary nonnegative or signed bounds. -/
theorem uniform_mean_le_two (f : State → ℝ) (chosen : State) (miss hit : ℝ)
    (hmiss : ∀ input, input ≠ chosen → f input ≤ miss) (hhit : f chosen ≤ hit) :
    (∑ input, f input) / (Fintype.card State : ℝ) ≤
      (1 - (Fintype.card State : ℝ)⁻¹) * miss + (Fintype.card State : ℝ)⁻¹ * hit := by
  classical
  have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ input, f input) ≤ (Fintype.card State : ℝ) * miss + (hit - miss) := by
    calc
      _ ≤ ∑ input : State, (miss + if input = chosen then hit - miss else 0) := by
        apply Finset.sum_le_sum
        intro input _
        by_cases hi : input = chosen
        · subst input
          simpa using hhit
        · simpa [hi] using hmiss input hi
      _ = _ := by simp [Finset.sum_add_distrib]
  apply (div_le_div_of_nonneg_right hsum hN.le).trans_eq
  field_simp
  ring

/-- Concrete one-query drift for the three-layer marked graph. The proof
covers every fresh row, branch deaths, suffix reuse, and pending-component joins. -/
theorem weight_mean_step (rows : List (State → Option State)) (target : State)
    (hlen : rows.length = 3) (layer : ℕ) (hlayer : layer < rows.length) (input : State)
    (hfresh : rows[layer] input = none) :
    (∑ output : State, weight (Fintype.card State) (insertEdge rows layer input output) target) /
        (Fintype.card State : ℝ) ≤
      (1 + (124 / 3 : ℝ) / Fintype.card State) * weight (Fintype.card State) rows target := by
  classical
  have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hN1 : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hgrow : weight (Fintype.card State) rows target ≤
      (1 + (124 / 3 : ℝ) / Fintype.card State) * weight (Fintype.card State) rows target := by
    have h := mul_nonneg (show 0 ≤ (124 / 3 : ℝ) / Fintype.card State by positivity)
      (weight_nonneg _ hN rows target)
    nlinarith
  by_cases hbad : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 3 target)
  · have hw : weight (Fintype.card State) rows target = 0 := by simp [weight, hbad]
    rw [hw, mul_zero]
    apply uniform_mean_le_const
    intro output
    rw [weight_of_branched _ rows target hlen layer hlayer input output hfresh hbad]
  have hinj := not_not.mp hbad
  by_cases hbelow : layer + 1 < 3 - (component rows 3 3 target).card
  · exact uniform_mean_le_const _ _ (fun output =>
      weight_below_head _ hN rows target hlen layer hlayer input output hfresh hbelow)
  by_cases habove : 3 - (component rows 3 3 target).card ≤ layer
  · exact (uniform_mean_le_const _ _ (fun output =>
      weight_above_head _ hN rows target hlen layer hlayer input output hfresh habove)).trans hgrow
  have hhead : layer + 1 = 3 - (component rows 3 3 target).card := by omega
  by_cases hbranch : ¬Set.InjOn (fun v : Fin 3 × State => v.1.val) (component rows 3 layer input)
  · exact (uniform_mean_le_const _ _ (fun output =>
      weight_boundary_branched _ hN rows target hlen layer hlayer input output hfresh hinj hhead hbranch)).trans hgrow
  have hsource := not_not.mp hbranch
  obtain ⟨chosen, hchosen⟩ := head_unique rows 3 target hlen hinj
  have hchoice : ∀ output, rootFrom rows (layer + 1) output = (3, target) ↔ output = chosen := by
    intro output
    simpa only [hhead] using hchosen output
  let d := (component rows 3 3 target).card
  let l := (component rows 3 layer input).card
  let m := (pending rows 3 (layer + 1)).card
  have hmean := uniform_mean_le_two
    (fun output => weight (Fintype.card State) (insertEdge rows layer input output) target) chosen
    (suffixWeight (Fintype.card State) d (m - l))
    (if d + l = 0 then suffixWeight (Fintype.card State) 1 m else
      suffixWeight (Fintype.card State) (d + l + 1) 0)
    (fun output ho => (weight_boundary_miss _ rows target hlen layer hlayer input output hfresh hinj hhead
      (fun hh => ho ((hchoice output).mp hh))).le)
    (weight_boundary_hit _ hN rows target hlen layer hlayer input chosen hfresh hhead ((hchoice chosen).mpr rfl))
  apply hmean.trans
  simp only [weight, if_pos hinj, ← hhead]
  change _ ≤ (1 + (124 / 3 : ℝ) / Fintype.card State) * suffixWeight (Fintype.card State) d m
  by_cases hz : d + l = 0
  · have hd : d = 0 := by omega
    have hl : l = 0 := by omega
    simpa only [hd, hl, Nat.add_zero, ↓reduceIte, Nat.sub_zero] using
      suffixWeight_first (Fintype.card State) hN m
  · rw [if_neg hz]
    apply suffixWeight_join _ hN1 d m l
    · exact Finset.card_le_card (component_pending rows 3 layer input)
    · have hl := component_card_le rows 3 layer input hsource
      change l ≤ layer at hl
      omega

variable {Index : Type} [Fintype Index] [DecidableEq Index]

/-- Product potential for independently addressed chains. -/
def productWeight (N : ℝ) (rows : Index → List (State → Option State)) (target : Index → State) : ℝ :=
  ∏ i, weight N (rows i) (target i)

theorem productWeight_update (N : ℝ) (rows : Index → List (State → Option State)) (target : Index → State)
    (index : Index) (newRows : List (State → Option State)) :
    productWeight N (Function.update rows index newRows) target =
      weight N newRows (target index) * ∏ i ∈ Finset.univ.erase index, weight N (rows i) (target i) := by
  classical
  unfold productWeight
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ index)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- One query changes one factor, so the same drift constant applies to the
entire product; there is no extra factor for the number of chains. -/
theorem productWeight_mean_step (rows : Index → List (State → Option State)) (target : Index → State)
    (index : Index) (hlen : (rows index).length = 3) (layer : ℕ)
    (hlayer : layer < (rows index).length) (input : State)
    (hfresh : (rows index)[layer] input = none) :
    (∑ output : State, productWeight (Fintype.card State)
      (Function.update rows index (insertEdge (rows index) layer input output)) target) /
        (Fintype.card State : ℝ) ≤
      (1 + (124 / 3 : ℝ) / Fintype.card State) * productWeight (Fintype.card State) rows target := by
  classical
  have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  let factor := ∏ i ∈ Finset.univ.erase index, weight (Fintype.card State) (rows i) (target i)
  have hf : 0 ≤ factor := Finset.prod_nonneg (fun i _ => weight_nonneg _ hN _ _)
  simp_rw [productWeight_update]
  calc
    _ = ((∑ output : State, weight (Fintype.card State) (insertEdge (rows index) layer input output)
        (target index)) / (Fintype.card State : ℝ)) * factor := by
      rw [← Finset.sum_mul]
      dsimp only [factor]
      ring
    _ ≤ ((1 + (124 / 3 : ℝ) / Fintype.card State) * weight (Fintype.card State) (rows index) (target index)) * factor :=
      mul_le_mul_of_nonneg_right (weight_mean_step (rows index) (target index) hlen layer hlayer input hfresh) hf
    _ = _ := by
      rw [mul_assoc]
      congr 1
      exact Finset.mul_prod_erase Finset.univ
        (fun i => weight (Fintype.card State) (rows i) (target i)) (Finset.mem_univ index)

/-- Live suffixes of total depth 68 force the product above the threshold
used in authenticDepth_query_cap. -/
theorem productWeight_terminal (N : ℝ) (hN : 0 < N)
    (rows : Index → List (State → Option State)) (target : Index → State)
    (hinj : ∀ i, Set.InjOn (fun v : Fin 3 × State => v.1.val) (component (rows i) 3 3 (target i)))
    (hdepth : 68 ≤ ∑ i, (component (rows i) 3 3 (target i)).card) :
    (5 : ℝ) ^ 68 ≤ productWeight N rows target := by
  have hweight (i : Index) : (5 : ℝ) ^ (component (rows i) 3 3 (target i)).card ≤
      weight N (rows i) (target i) := by
    simp only [weight, if_pos (hinj i), suffixWeight]
    have h := mul_nonneg
      (show (0 : ℝ) ≤ 5 ^ (component (rows i) 3 3 (target i)).card by positivity)
      (show (0 : ℝ) ≤ (124 / 3) * (pending (rows i) 3 (3 - (component (rows i) 3 3 (target i)).card)).card / N by positivity)
    nlinarith
  calc
    _ ≤ (5 : ℝ) ^ (∑ i, (component (rows i) 3 3 (target i)).card) := pow_le_pow_right₀ (by norm_num) hdepth
    _ = ∏ i, (5 : ℝ) ^ (component (rows i) 3 3 (target i)).card :=
      (Finset.prod_pow_eq_pow_sum ..).symm
    _ ≤ _ := Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hweight i)

theorem length_insertEdge (rows : List (State → Option State)) (layer : ℕ)
    (input output : State) : (insertEdge rows layer input output).length = rows.length := by
  induction rows generalizing layer with
  | nil => simp [insertEdge]
  | cons row rows ih => cases layer <;> simp [insertEdge, ih]

theorem productWeight_nonneg (N : ℝ) (hN : 0 < N)
    (rows : Index → List (State → Option State)) (target : Index → State) :
    0 ≤ productWeight N rows target :=
  Finset.prod_nonneg (fun i _ => weight_nonneg N hN (rows i) (target i))

/-- The graph table contains only observed queries; it starts empty even when
the marked honest computation has already produced public endpoints. -/
def emptyRows : Index → List (State → Option State) := fun _ => List.replicate 3 (fun _ => none)

theorem productWeight_empty (N : ℝ) (target : Index → State) :
    productWeight N (emptyRows (Index := Index)) target = 1 := by
  have he (layer : ℕ) (input : State) :
      edge (List.replicate 3 (fun _ : State => (none : Option State))) layer input = none := by
    unfold edge
    rw [List.getElem?_replicate]
    split <;> rfl
  have hc (value : State) :
      component (List.replicate 3 (fun _ : State => (none : Option State))) 3 3 value = ∅ := by
    ext v
    simp only [component, Finset.mem_filter, he, Option.isSome_none, Bool.false_eq_true,
      false_and, and_false, Finset.notMem_empty]
  have hp (head : ℕ) :
      pending (List.replicate 3 (fun _ : State => (none : Option State))) 3 head = ∅ := by
    ext v
    simp only [pending, Finset.mem_filter, he, Option.isSome_none, Bool.false_eq_true,
      false_and, and_false, Finset.notMem_empty]
  simp only [productWeight, emptyRows, weight, hc, hp, Finset.card_empty,
    Finset.coe_empty, Set.injOn_empty, ↓reduceIte, suffixWeight]
  simp

def potential (rows : Index → List (State → Option State)) (target : Index → State) : ℝ≥0∞ :=
  ENNReal.ofReal (productWeight (Fintype.card State) rows target)

def growth (State : Type) [Fintype State] : ℝ≥0∞ :=
  ENNReal.ofReal (1 + (124 / 3 : ℝ) / Fintype.card State)

theorem potential_mean_step [SampleableType State]
    (rows : Index → List (State → Option State)) (target : Index → State)
    (index : Index) (hlen : (rows index).length = 3) (layer : ℕ)
    (hlayer : layer < (rows index).length) (input : State)
    (hfresh : (rows index)[layer] input = none) :
    (∑' output : State, Pr[= output | $ᵗ State] *
      potential (Function.update rows index (insertEdge (rows index) layer input output)) target) ≤
      growth State * potential rows target := by
  have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hnonneg (rs : Index → List (State → Option State)) := productWeight_nonneg _ hN rs target
  have h := ENNReal.ofReal_le_ofReal
    (productWeight_mean_step rows target index hlen layer hlayer input hfresh)
  rw [ENNReal.ofReal_div_of_pos hN,
    ENNReal.ofReal_sum_of_nonneg (fun output _ => hnonneg _),
    ENNReal.ofReal_mul (by positivity)] at h
  simpa only [potential, growth, tsum_fintype, probOutput_uniformSample,
    ENNReal.ofReal_natCast, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_comm] using h

theorem growth_one_le : 1 ≤ growth State := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  exact le_add_of_nonneg_right (by positivity)

theorem growth_ne_zero : growth State ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one growth_one_le)

theorem growth_ne_top : growth State ≠ ∞ := ENNReal.ofReal_ne_top

abbrev GraphState (Index State : Type) := (Index → List (State → Option State)) × ℕ

abbrev GraphSpec (Index State : Type) := (Index × Fin 3 × State) →ₒ State

variable [SampleableType State]

/-- Lazy sampling of observed chain edges, counting cached queries too. -/
def step (t : Index × Fin 3 × State) (s : GraphState Index State) :
    ProbComp (State × GraphState Index State) :=
  match edge (s.1 t.1) t.2.1.val t.2.2 with
  | some output => pure (output, s.1, s.2 + 1)
  | none => (fun output => (output,
      Function.update s.1 t.1 (insertEdge (s.1 t.1) t.2.1.val t.2.2 output), s.2 + 1)) <$> ($ᵗ State)

def implementation : QueryImpl (GraphSpec Index State) (StateT (GraphState Index State) ProbComp) :=
  fun t s => step t s

def Valid (s : GraphState Index State) : Prop := ∀ i, (s.1 i).length = 3

theorem step_valid (t : Index × Fin 3 × State) (s : GraphState Index State) (hs : Valid s)
    (r : State × GraphState Index State) (hr : r ∈ support (step t s)) : Valid r.2 := by
  unfold step at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hs
  · simp only [support_map, Set.mem_image] at hr
    obtain ⟨output, _, rfl⟩ := hr
    intro i
    by_cases hi : i = t.1
    · subst i
      simpa only [Function.update_self, length_insertEdge] using hs t.1
    · simpa only [Function.update_of_ne hi] using hs i

theorem step_potential (t : Index × Fin 3 × State) (s : GraphState Index State)
    (hs : Valid s) (target : Index → State) :
    (∑' r, Pr[= r | step t s] * potential r.2.1 target) ≤ growth State * potential s.1 target := by
  unfold step
  split
  · rw [tsum_probOutput_pure_mul]
    exact le_mul_of_one_le_left' growth_one_le
  · rename_i hfresh
    rw [tsum_probOutput_map_mul]
    have hl : t.2.1.val < (s.1 t.1).length := by rw [hs]; exact t.2.1.isLt
    have hf : (s.1 t.1)[t.2.1.val] t.2.2 = none := by
      simpa only [edge, List.getElem?_eq_getElem hl, Option.bind_some] using hfresh
    exact potential_mean_step s.1 target t.1 (hs t.1) _ hl _ hf

def discounted (target : Index → State) (s : GraphState Index State) : ℝ≥0∞ :=
  potential s.1 target / growth State ^ s.2

theorem step_count (t : Index × Fin 3 × State) (s : GraphState Index State)
    (r : State × GraphState Index State) (hr : r ∈ support (step t s)) : r.2.2 = s.2 + 1 := by
  unfold step at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    rfl
  · simp only [support_map, Set.mem_image] at hr
    obtain ⟨output, _, rfl⟩ := hr
    rfl

theorem step_discounted (t : Index × Fin 3 × State) (s : GraphState Index State)
    (hs : Valid s) (target : Index → State) :
    (∑' r, Pr[= r | step t s] * discounted target r.2) ≤ discounted target s := by
  calc
    _ = (∑' r, Pr[= r | step t s] * potential r.2.1 target) / growth State ^ (s.2 + 1) := by
      rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro r
      by_cases hr : r ∈ support (step t s)
      · simp only [discounted, step_count t s r hr, div_eq_mul_inv, mul_assoc]
      · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
    _ ≤ (growth State * potential s.1 target) / growth State ^ (s.2 + 1) :=
      ENNReal.div_le_div_right (step_potential t s hs target) _
    _ = discounted target s := by
      rw [pow_succ, mul_comm (growth State),
        ENNReal.mul_div_mul_right _ _ growth_ne_zero growth_ne_top]
      rfl

/-- Discounting the graph potential turns its multiplicative drift into the
standard VCV-io expected-final invariant, for arbitrary adaptive programs. -/
theorem expected_discounted_le {α : Type} (oa : OracleComp (GraphSpec Index State) α)
    (target : Index → State) (s : GraphState Index State) (hs : Valid s) :
    XmssSecurity.expectedFinal implementation (discounted target) oa s ≤ discounted target s := by
  have hzero (comp : OracleComp (GraphSpec Index State) α) (state : GraphState Index State) :
      XmssSecurity.expectedSimulatedCost implementation (fun _ _ => 0) comp state = 0 := by
    induction comp using OracleComp.inductionOn generalizing state with
    | pure value => rfl
    | query_bind t next ih =>
      simp only [XmssSecurity.expectedSimulatedCost_query_bind, ih, mul_zero,
        tsum_zero, add_zero]
  have h := XmssSecurity.expectedFinal_le implementation
    (Inv := Valid) (fun t state hstate r hr => step_valid t state hstate r hr)
    (discounted target) (fun _ _ => 0)
    (fun t state hstate => by
      simpa only [add_zero, implementation, StateT.run] using step_discounted t state hstate target)
    oa s hs
  simpa only [hzero, add_zero] using h

def Terminal (target : Index → State) (q : ℕ) (s : GraphState Index State) : Prop :=
  s.2 ≤ q ∧
  (∀ i, Set.InjOn (fun v : Fin 3 × State => v.1.val) (component (s.1 i) 3 3 (target i))) ∧
  68 ≤ ∑ i, (component (s.1 i) 3 3 (target i)).card

theorem terminal_discounted (target : Index → State) (q : ℕ) (s : GraphState Index State)
    (h : Terminal target q s) :
    (5 : ℝ≥0∞) ^ 68 / growth State ^ q ≤ discounted target s := by
  apply ENNReal.div_le_div
  · have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
    simpa only [potential, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 5), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal (productWeight_terminal _ hN s.1 target h.2.1 h.2.2)
  · exact pow_le_pow_right₀ growth_one_le h.1

theorem terminal_probability_of_expected {α : Type} (run : ProbComp (α × GraphState Index State))
    (target : Index → State) (q : ℕ)
    (hmean : (∑' r, Pr[= r | run] * discounted target r.2) ≤ 1) :
    Pr[fun r => Terminal target q r.2 | run] ≤ growth State ^ q / (5 : ℝ≥0∞) ^ 68 := by
  classical
  have hmass : Pr[fun r => Terminal target q r.2 | run] *
      ((5 : ℝ≥0∞) ^ 68 / growth State ^ q) ≤ 1 := by
    calc
      _ = ∑' r, (if Terminal target q r.2 then Pr[= r | run] else 0) *
          ((5 : ℝ≥0∞) ^ 68 / growth State ^ q) := by
        rw [probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
      _ ≤ ∑' r, Pr[= r | run] * discounted target r.2 := by
        apply ENNReal.tsum_le_tsum
        intro r
        split_ifs with hr
        · exact mul_le_mul_right (terminal_discounted target q r.2 hr) _
        · simp only [zero_mul, zero_le]
      _ ≤ 1 := hmean
  rw [← mul_div_assoc] at hmass
  have hmul := (ENNReal.div_le_iff (pow_ne_zero _ growth_ne_zero)
    (ENNReal.pow_ne_top growth_ne_top)).mp hmass
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  simpa only [one_mul] using hmul

/-- The adaptive observed-graph bound, before coupling the observed table to
the marked signing run. No response-independence premise is hidden in it. -/
theorem terminal_probability {α : Type} (oa : OracleComp (GraphSpec Index State) α)
    (target : Index → State) (q : ℕ) :
    Pr[fun r => Terminal target q r.2 |
      (simulateQ implementation oa).run (emptyRows, 0)] ≤
        growth State ^ q / (5 : ℝ≥0∞) ^ 68 := by
  apply terminal_probability_of_expected
  simpa only [XmssSecurity.expectedFinal, discounted, potential, productWeight_empty, ENNReal.ofReal_one,
    pow_zero, div_one] using expected_discounted_le oa target (emptyRows, 0) (by intro i; rfl)

theorem growth_query_cap (q : ℕ) (hq : q < 2 ^ 127) (hcard : Fintype.card State = 2 ^ 128) :
    growth State ^ q / (5 : ℝ≥0∞) ^ 68 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have hg : (1 + (124 / 3 : ℝ) / Fintype.card State) = 1 + 124 / (3 * (2 : ℝ) ^ 128) := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, div_div]
  have h := ENNReal.ofReal_le_ofReal (authenticDepth_query_cap q hq)
  rw [ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num)] at h
  have hr : ENNReal.ofReal ((2 : ℝ) ^ (-128 : ℤ)) = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    rw [zpow_neg, zpow_ofNat, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  simpa only [growth, hg, hr, ENNReal.ofReal_ofNat] using h

theorem terminal_probability_digest {α : Type} (oa : OracleComp (GraphSpec Index State) α)
    (target : Index → State) (q : ℕ) (hq : q < 2 ^ 127)
    (hcard : Fintype.card State = 2 ^ 128) :
    Pr[fun r => Terminal target q r.2 |
      (simulateQ implementation oa).run (emptyRows, 0)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  (terminal_probability oa target q).trans (growth_query_cap q hq hcard)

variable {Aux : Type} {ι : Type} {auxSpec : OracleSpec ι}

/-- Auxiliary queries may carry arbitrary state and randomness. Their graph
projection is required to stay fixed; graph queries retain fresh uniform sampling. -/
def mixedImplementation
    (aux : QueryImpl auxSpec (StateT (GraphState Index State × Aux) ProbComp)) :
    QueryImpl (GraphSpec Index State + auxSpec) (StateT (GraphState Index State × Aux) ProbComp)
  | .inl t => fun s => (fun r => (r.1, r.2, s.2)) <$> step t s.1
  | .inr t => aux t

theorem mixed_expected_discounted_le {α : Type}
    (aux : QueryImpl auxSpec (StateT (GraphState Index State × Aux) ProbComp))
    (haux : ∀ t s r, r ∈ support ((aux t).run s) → r.2.1 = s.1)
    (oa : OracleComp (GraphSpec Index State + auxSpec) α)
    (target : Index → State) (s : GraphState Index State × Aux) (hs : Valid s.1) :
    XmssSecurity.expectedFinal (mixedImplementation aux) (fun r => discounted target r.1) oa s ≤
      discounted target s.1 := by
  have hzero (comp : OracleComp (GraphSpec Index State + auxSpec) α)
      (state : GraphState Index State × Aux) :
      XmssSecurity.expectedSimulatedCost (mixedImplementation aux) (fun _ _ => 0) comp state = 0 := by
    induction comp using OracleComp.inductionOn generalizing state with
    | pure value => rfl
    | query_bind t next ih =>
      simp only [XmssSecurity.expectedSimulatedCost_query_bind, ih, mul_zero, tsum_zero, add_zero]
  have hinv : ∀ t state, Valid state.1 → ∀ r ∈ support ((mixedImplementation aux t).run state), Valid r.2.1 := by
    intro t state hstate r hr
    cases t with
    | inl t =>
      simp only [mixedImplementation, StateT.run, support_map, Set.mem_image] at hr
      obtain ⟨v, hv, rfl⟩ := hr
      exact step_valid t state.1 hstate v hv
    | inr t => rw [haux t state r hr]; exact hstate
  have hstep : ∀ t state, Valid state.1 →
      (∑' r, Pr[= r | (mixedImplementation aux t).run state] * discounted target r.2.1) ≤
        discounted target state.1 := by
    intro t state hstate
    cases t with
    | inl t =>
      simp only [mixedImplementation, StateT.run, tsum_probOutput_map_mul]
      exact step_discounted t state.1 hstate target
    | inr t =>
      change (∑' r : auxSpec.Range t × GraphState Index State × Aux,
        Pr[= r | (aux t).run state] * discounted target r.2.1) ≤ discounted target state.1
      calc
        _ = (∑' r, Pr[= r | (aux t).run state]) * discounted target state.1 := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro r
          by_cases hr : r ∈ support ((aux t).run state)
          · rw [haux t state r hr]
          · simp only [mixedImplementation, probOutput_eq_zero_of_not_mem_support hr, zero_mul]
        _ ≤ _ := mul_le_of_le_one_left zero_le tsum_probOutput_le_one
  have h := XmssSecurity.expectedFinal_le (mixedImplementation aux)
    (Inv := fun r => Valid r.1) hinv (fun r => discounted target r.1) (fun _ _ => 0)
    (fun t state hstate => by simpa only [add_zero] using hstep t state hstate) oa s hs
  simpa only [hzero, add_zero] using h

/-- Arbitrary auxiliary oracle interaction consumes no extra graph drift.
The bound still uses the graph-query count recorded by the implementation. -/
theorem mixed_terminal_probability_digest {α : Type}
    (aux : QueryImpl auxSpec (StateT (GraphState Index State × Aux) ProbComp))
    (haux : ∀ t s r, r ∈ support ((aux t).run s) → r.2.1 = s.1)
    (oa : OracleComp (GraphSpec Index State + auxSpec) α) (initial : Aux)
    (target : Index → State) (q : ℕ) (hq : q < 2 ^ 127)
    (hcard : Fintype.card State = 2 ^ 128) :
    Pr[fun r => Terminal target q r.2.1 |
      (simulateQ (mixedImplementation aux) oa).run ((emptyRows, 0), initial)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  let run := (simulateQ (mixedImplementation aux) oa).run ((emptyRows, 0), initial)
  have hm := mixed_expected_discounted_le aux haux oa target ((emptyRows, 0), initial) (by intro i; rfl)
  have h := terminal_probability_of_expected ((fun r => (r.1, r.2.1)) <$> run) target q (by
    rw [tsum_probOutput_map_mul]
    simpa only [XmssSecurity.expectedFinal, discounted, potential, productWeight_empty,
      ENNReal.ofReal_one, pow_zero, div_one] using hm)
  have h' : Pr[fun r => Terminal target q r.2.1 | run] ≤ growth State ^ q / (5 : ℝ≥0∞) ^ 68 := by
    simpa only [probEvent_map, Function.comp_def] using h
  exact h'.trans (growth_query_cap q hq hcard)

/-- A canonical path with unique observed predecessors admits no branched
observed component at its endpoint. The premise is supplied by the chosen
collision-free completion, not by conditioning fresh oracle answers. -/
theorem root_canonical (rows : List (State → Option State)) (a : ℕ → State)
    (hunique : ∀ j (hj : j < rows.length) input,
      rows[j] input = some (a (j + 1)) → input = a j)
    (input : State) (hroot : root rows input = (rows.length, a rows.length)) : input = a 0 := by
  induction rows generalizing a input with
  | nil => simpa only [root, List.length_nil, Prod.mk.injEq, true_and] using hroot
  | cons row rows ih =>
    cases hr : row input with
    | none => simp [root, hr] at hroot
    | some output =>
      have htail : root rows output = (rows.length, a (rows.length + 1)) := by
        simp only [root, hr, List.length_cons, Prod.mk.injEq, Nat.add_right_cancel_iff] at hroot
        exact Prod.ext hroot.1 hroot.2
      have hout : output = a 1 := ih (fun j => a (j + 1))
        (fun j hj u hu => hunique (j + 1) (by simp; omega) u (by simpa using hu)) output htail
      exact hunique 0 (by simp) input (by simpa only [List.getElem_cons_zero, zero_add, hout] using hr)

theorem component_canonical (rows : List (State → Option State)) (a : ℕ → State)
    (hunique : ∀ j (hj : j < rows.length) input,
      rows[j] input = some (a (j + 1)) → input = a j)
    (v : Fin rows.length × State) (hv : v ∈ component rows rows.length rows.length (a rows.length)) :
    v.2 = a v.1.val := by
  have hr := (Finset.mem_filter.mp hv).2.2
  have hroot : root (rows.drop v.1.val) v.2 =
      ((rows.drop v.1.val).length, a rows.length) := by
    simp only [rootFrom, Prod.mk.injEq] at hr
    apply Prod.ext
    · simp only [List.length_drop]
      omega
    · exact hr.2
  have ha : a (v.1.val + (rows.drop v.1.val).length) = a rows.length := by
    congr 1
    simp only [List.length_drop]
    omega
  apply root_canonical (rows.drop v.1.val) (fun j => a (v.1.val + j)) ?_ v.2
    (by simpa only [ha] using hroot)
  intro j hj input hin
  apply hunique (v.1.val + j) (by simp only [List.length_drop] at hj; omega) input
  simpa only [List.getElem_drop, Nat.add_assoc] using hin

theorem component_canonical_injective (rows : List (State → Option State)) (a : ℕ → State)
    (hunique : ∀ j (hj : j < rows.length) input,
      rows[j] input = some (a (j + 1)) → input = a j) :
    Set.InjOn (fun v : Fin rows.length × State => v.1.val)
      (component rows rows.length rows.length (a rows.length)) := by
  intro v hv w hw h
  change v.1.val = w.1.val at h
  apply Prod.ext (Fin.ext h)
  rw [component_canonical rows a hunique v hv, component_canonical rows a hunique w hw, h]

theorem component_canonical_injective_of_length (rows : List (State → Option State)) (a : ℕ → State)
    (layers : ℕ) (hlen : rows.length = layers)
    (hunique : ∀ j (hj : j < rows.length) input,
      rows[j] input = some (a (j + 1)) → input = a j) :
    Set.InjOn (fun v : Fin layers × State => v.1.val)
      (component rows layers layers (a layers)) := by
  subst layers
  exact component_canonical_injective rows a hunique

theorem root_path (rows : List (State → Option State)) (a : ℕ → State)
    (hedges : ∀ j (hj : j < rows.length), rows[j] (a j) = some (a (j + 1))) :
    root rows (a 0) = (rows.length, a rows.length) := by
  induction rows generalizing a with
  | nil => rfl
  | cons row rows ih =>
    have h0 := hedges 0 (by simp)
    simp only [List.getElem_cons_zero, zero_add] at h0
    have ht := ih (fun j => a (j + 1)) (fun j hj => hedges (j + 1) (by simp; omega))
    simp only [root, h0, ht, List.length_cons]

theorem rootFrom_path (rows : List (State → Option State)) (a : ℕ → State) (start : ℕ)
    (hstart : start ≤ rows.length)
    (hedges : ∀ j (hj : j < rows.length), start ≤ j → rows[j] (a j) = some (a (j + 1))) :
    rootFrom rows start (a start) = (rows.length, a rows.length) := by
  have ht := root_path (rows.drop start) (fun j => a (start + j)) (by
    intro j hj
    simpa only [List.getElem_drop, Nat.add_assoc] using
      hedges (start + j) (by simp only [List.length_drop] at hj; omega) (by omega))
  have hn : start + (rows.drop start).length = rows.length := by
    simp only [List.length_drop]
    omega
  simpa only [rootFrom, Nat.add_zero, ht, hn] using
    congrArg (fun r : ℕ × State => (start + r.1, r.2)) ht

theorem component_depth_of_path (rows : List (State → Option State)) (a : ℕ → State)
    (start : ℕ) (hstart : start ≤ rows.length)
    (hedges : ∀ j (hj : j < rows.length), start ≤ j → rows[j] (a j) = some (a (j + 1))) :
    rows.length - start ≤ (component rows rows.length rows.length (a rows.length)).card := by
  by_cases hs : start = rows.length
  · simp [hs]
  · have hlt : start < rows.length := by omega
    have hv : (⟨start, hlt⟩, a start) ∈ component rows rows.length rows.length (a rows.length) := by
      simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simp only [edge, List.getElem?_eq_getElem hlt, Option.bind_some,
        hedges start hlt le_rfl, Option.isSome_some], rootFrom_path rows a start hstart hedges⟩
    have h := component_layer_ge rows rows.length rows.length (a rows.length) le_rfl _ hv
    change rows.length - (component rows rows.length rows.length (a rows.length)).card ≤ start at h
    omega

theorem component_depth_of_path_of_length (rows : List (State → Option State)) (a : ℕ → State)
    (layers : ℕ) (hlen : rows.length = layers) (start : ℕ) (hstart : start ≤ rows.length)
    (hedges : ∀ j (hj : j < rows.length), start ≤ j → rows[j] (a j) = some (a (j + 1))) :
    layers - start ≤ (component rows layers layers (a layers)).card := by
  subst layers
  exact component_depth_of_path rows a start hstart hedges

end LayeredGraph

/-- Projection of an observed subcache onto one public top chain. -/
def observedTopRows (P : PublicParameter) (cache : HashCache C)
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    List (XmssSecurity.Digest → Option XmssSecurity.Digest) :=
  List.ofFn fun step : XmssSecurity.ChainStep => fun input =>
    (cache (.hash (XmssSecurity.Concrete.CacheView.topChainInput P b l step input))).map truncateHash

theorem observedTopRows_length (P : PublicParameter) (cache : HashCache C)
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    (observedTopRows P cache b l).length = 3 := by
  simp [observedTopRows, XmssSecurity.chainLength, XmssSecurity.winternitzBits]

set_option backward.isDefEq.respectTransparency false in
theorem observedTopRows_depth (P : PublicParameter) (cache : HashCache C)
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex)
    (pos : ℕ) (hpos : pos ≤ 3) (input finish : XmssSecurity.Digest)
    (hres : DeterministicSigning.Resolves (SigningDescentProof.thView cache)
      (XmssSecurity.Concrete.topChainWalk P b l pos (3 - pos) input :
        OracleComp XmssSecurity.HashSpec _) finish) :
    3 - pos ≤ (LayeredGraph.component (observedTopRows P cache b l) 3 3 finish).card := by
  let a := fun j => XmssSecurity.Wots.walk
    (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) P b l)
    pos (j - pos) input
  have ha : a 3 = finish := by
    have hv := SigningCacheProof.resolves_value hres
    simpa only [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk] using hv
  have hedges : ∀ j (hj : j < (observedTopRows P cache b l).length), pos ≤ j →
      (observedTopRows P cache b l)[j] (a j) = some (a (j + 1)) := by
    intro j hj hlo
    have hj' : j < XmssSecurity.chainLength - 1 := by
      simpa only [observedTopRows, List.length_ofFn] using hj
    have hjs : j < 3 := by simpa only [observedTopRows_length] using hj
    have hc := SigningCacheProof.resolves_topChainWalk pos input (3 - pos) finish hres
      j hlo (by omega) hj'
    obtain ⟨output, hout⟩ := Option.isSome_iff_exists.mp hc
    have hv := XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout
    have hsub : j + 1 - pos = (j - pos) + 1 := by omega
    have hadd : pos + (j - pos) = j := by omega
    simp only [observedTopRows, List.getElem_ofFn, a]
    change (SigningDescentProof.thView cache
      (XmssSecurity.Concrete.CacheView.topChainInput P b l ⟨j, hj'⟩ (a j))).map truncateHash = _
    rw [hout]
    simp only [Option.map_some, Option.some.injEq]
    simpa only [a, hsub, XmssSecurity.Wots.walk, hadd,
      XmssSecurity.Concrete.CacheView.topChainStep, hj', ↓reduceDIte,
      truncateHash, XmssSecurity.truncateHash, XmssSecurity.digestBits, LeanXmss.digestBits] using hv.symm
  have h := LayeredGraph.component_depth_of_path_of_length (observedTopRows P cache b l) a
    3 (observedTopRows_length P cache b l) pos
    (by simpa only [observedTopRows_length] using hpos) hedges
  simpa only [observedTopRows_length, ha] using h

set_option backward.isDefEq.respectTransparency false in
theorem observedTopRows_unique (x : SigningSecurityProof.Keys3 C) (observed cache : HashCache C)
    (hle : observed ≤ cache) (hno : NoForestCollision prims x cache)
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex)
    (j : ℕ) (hj : j < (observedTopRows x.1 observed b l).length) (input : XmssSecurity.Digest)
    (hin : (observedTopRows x.1 observed b l)[j] input = some
      (XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
        0 (j + 1) (replayStarts prims x cache topLayer (topKey b) l))) :
    input = XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
      0 j (replayStarts prims x cache topLayer (topKey b) l) := by
  have hj' : j < XmssSecurity.chainLength - 1 := by
    simpa only [observedTopRows, List.length_ofFn] using hj
  simp only [observedTopRows, List.getElem_ofFn, Option.map_eq_some_iff] at hin
  obtain ⟨output, hout, heq⟩ := hin
  have hc := hle hout
  apply XmssSecurity.Concrete.digestBytes_injective
  apply noForestCollision_payload prims x cache hno (.topChain b l ⟨j, hj'⟩) trivial trivial
    (XmssSecurity.Concrete.digestBytes input) (by
      simpa only [XmssSecurity.Concrete.CacheView.topChainInput] using Option.isSome_iff_exists.mpr ⟨output, hc⟩)
  have hv := XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some
    (show SigningDescentProof.thView cache
      (XmssSecurity.Concrete.CacheView.topChainInput x.1 b l ⟨j, hj'⟩ input) = some output from hc)
  simp only [XmssSecurity.Concrete.CacheView.topChainInput] at hv
  rw [hv]
  simpa only [forestPayload, XmssSecurity.Wots.walk, Nat.zero_add,
    XmssSecurity.Concrete.CacheView.topChainStep, hj', ↓reduceDIte,
    XmssSecurity.Concrete.CacheView.topChainInput, truncateHash, XmssSecurity.truncateHash,
    XmssSecurity.digestBits, LeanXmss.digestBits] using heq

/-- Collision exclusion in a single completed cache makes every observed
top endpoint component live, including chains not used below depth zero. -/
theorem observedTopRows_injective (x : SigningSecurityProof.Keys3 C) (observed cache : HashCache C)
    (hle : observed ≤ cache) (hno : NoForestCollision prims x cache)
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    Set.InjOn (fun v : Fin 3 × XmssSecurity.Digest => v.1.val)
      (LayeredGraph.component (observedTopRows x.1 observed b l) 3 3
        (XmssSecurity.Wots.walk
          (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
          0 3 (replayStarts prims x cache topLayer (topKey b) l))) := by
  exact LayeredGraph.component_canonical_injective_of_length (observedTopRows x.1 observed b l)
    (fun j => XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
      0 j (replayStarts prims x cache topLayer (topKey b) l))
    3 (observedTopRows_length x.1 observed b l)
    (observedTopRows_unique prims x observed cache hle hno b l)

/-- A verification transcript resolving authentic suffixes reaches the graph
terminal event. The observed cache may omit all private key-generation reads. -/
theorem observedTopRows_terminal (x : SigningSecurityProof.Keys3 C) (observed cache : HashCache C)
    (hle : observed ≤ cache) (hno : NoForestCollision prims x cache)
    (b : XmssSecurity.TopIndex) (encoding : XmssSecurity.Encoding)
    (hvalid : XmssSecurity.TargetSum.Valid encoding)
    (values : XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (hauth : ∀ l, values l = XmssSecurity.Wots.walk
      (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
      0 (encoding l).val (replayStarts prims x cache topLayer (topKey b) l))
    (hres : ∀ l, ∃ finish, DeterministicSigning.Resolves (SigningDescentProof.thView observed)
      (XmssSecurity.Concrete.topChainWalk x.1 b l (encoding l).val (3 - (encoding l).val)
        (values l) : OracleComp XmssSecurity.HashSpec _) finish)
    (count q : ℕ) (hcount : count ≤ q) :
    LayeredGraph.Terminal
      (fun l => XmssSecurity.Wots.walk
        (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
        0 3 (replayStarts prims x cache topLayer (topKey b) l)) q
      (fun l => observedTopRows x.1 observed b l, count) := by
  refine ⟨hcount, fun l => observedTopRows_injective prims x observed cache hle hno b l, ?_⟩
  rw [← valid_encoding_deficit encoding hvalid]
  apply Finset.sum_le_sum
  intro l _
  have hd : (encoding l).val ≤ 3 := by
    have h := (encoding l).isLt
    norm_num [XmssSecurity.chainLength, XmssSecurity.winternitzBits] at h
    omega
  obtain ⟨finish, hfinish⟩ := hres l
  have hv := SigningCacheProof.resolves_value (hfinish.mono (SigningCacheProof.thView_mono hle))
  rw [XmssSecurity.Concrete.CacheReplay.eval_topChainWalk, hauth] at hv
  have hw := XmssSecurity.Wots.walk_add
    (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
    0 (encoding l).val (3 - (encoding l).val) (replayStarts prims x cache topLayer (topKey b) l)
  rw [Nat.zero_add, Nat.add_sub_of_le hd] at hw
  rw [← hw] at hv
  simpa only [hv] using observedTopRows_depth x.1 observed b l (encoding l).val hd (values l) finish hfinish

/-- All threshold slots and the selected key's finite structural chain domain.
The remaining raw hash domain stays in the auxiliary lazy oracle. -/
abbrev ProtectedSlot (C : Committee) := TprfSecurityProof.Slot C ⊕
  (XmssSecurity.ChainIndex × XmssSecurity.ChainStep × XmssSecurity.Digest)

def protectedInput (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex) :
    ProtectedSlot C → Query C
  | .inl slot => TprfSecurityProof.slotInput x.2.1 x.2.2 slot
  | .inr (l, step, input) => .hash (XmssSecurity.Concrete.CacheView.topChainInput x.1 b l step input)

set_option backward.isDefEq.respectTransparency false in
theorem protectedInput_injective (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) : Function.Injective (protectedInput x b) := by
  have hinj := TprfSecurityProof.slotInput_injective
    (not_not.mp (not_or.mp hno).1) (not_not.mp (not_or.mp hno).2)
  rintro (slot | ⟨l, step, input⟩) (slot' | ⟨l', step', input'⟩) h
  · exact congrArg Sum.inl (hinj h)
  · exact (TprfSecurityProof.slotInput_ne_hash x.2.1 x.2.2 slot _ h).elim
  · exact (TprfSecurityProof.slotInput_ne_hash x.2.1 x.2.2 slot' _ h.symm).elim
  · have he := Query.hash.inj h
    have hd := XmssSecurity.domain_eq_of_tweakableHashInput_eq x.1 he
    obtain ⟨_, rfl, rfl⟩ := XmssSecurity.HashDomain.topChain.inj hd
    have hp := XmssSecurity.payload_eq_of_tweakableHashInput_eq x.1 (.topChain b l step) he
    have hi := XmssSecurity.Concrete.digestBytes_injective hp
    cases hi
    rfl

namespace FinitePosterior

variable {D R : Type} [DecidableEq D]

/-- Deterministic execution records exactly the queried cells while retaining
the same full table. This is an interpreter, not a new security experiment. -/
def evalRecorded {α : Type} : OracleComp (D →ₒ R) α → QueryCache (D →ₒ R) → (D → R) → α × QueryCache (D →ₒ R)
  | .pure a, cache, _ => (a, cache)
  | .queryBind t k, cache, table => evalRecorded (k (table t)) (cache.cacheQuery t (table t)) table

variable [Finite D] [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)]

/-- The joint posterior identity retains the latent table. After an adaptive
execution, its unobserved entries can be sampled afresh independently. -/
theorem joint_table {α : Type} (oa : OracleComp (D →ₒ R) α) (cache : QueryCache (D →ₒ R)) :
    𝒟[(fun h => (evalRecorded oa cache (tableExtending cache h), tableExtending cache h)) <$> ($ᵗ (D → R))] =
      𝒟[do
        let r ← (simulateQ (D →ₒ R).randomOracle oa).run cache
        let h ← $ᵗ (D → R)
        pure (r, tableExtending r.2 h)] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
    simp only [evalRecorded, simulateQ_pure, StateT.run_pure, pure_bind, bind_pure_comp]
    rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map, bind_assoc]
    change 𝒟[(fun h => (evalRecorded (k (tableExtending cache h t))
      (cache.cacheQuery t (tableExtending cache h t)) (tableExtending cache h), tableExtending cache h)) <$>
      ($ᵗ (D → R))] = _
    cases hc : cache t with
    | some value =>
      rw [QueryImpl.withCaching_run_some _ hc]
      simp only [pure_bind]
      have he (h : D → R) : tableExtending cache h t = value := by simp [tableExtending, hc]
      have hu : cache.cacheQuery t value = cache := by
        ext u
        by_cases hu : u = t
        · subst u; simp [QueryCache.cacheQuery, hc]
        · simp [QueryCache.cacheQuery, hu]
      simpa only [evalRecorded, he, hu] using ih value cache
    | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      rw [map_eq_bind_pure_comp]
      simp only [Function.comp_def, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      rw [← evalDist_uniformSample_bind_update_map (R := R) t]
      rw [evalDist_bind]
      conv_rhs => rw [evalDist_bind]
      congr 1
      funext value
      have he (h : D → R) : tableExtending cache (Function.update h t value) =
          tableExtending (cache.cacheQuery t value) h := by
        rw [tableExtending_cacheQuery, tableExtending_update_of_none cache h hc]
      have hv (h : D → R) : tableExtending cache (Function.update h t value) t = value := by
        simp [tableExtending, hc]
      simpa only [Function.comp_apply, evalRecorded, hv, he, bind_pure_comp] using
        ih value (cache.cacheQuery t value)

theorem uniform_update_bind {α : Type} (t : D) (next : (D → R) → ProbComp α) :
    𝒟[do let value ← $ᵗ R; let h ← $ᵗ (D → R); next (Function.update h t value)] =
      𝒟[do let h ← $ᵗ (D → R); next h] := by
  calc
    _ = 𝒟[(do let value ← $ᵗ R; let h ← $ᵗ (D → R); pure (Function.update h t value)) >>= next] := by
      simp only [bind_assoc, pure_bind]
    _ = _ := by rw [evalDist_bind, evalDist_uniformSample_bind_update, ← evalDist_bind]

variable {Aux : Type} {ι : Type} {auxSpec : OracleSpec ι}

def eager (table : D → R)
    (aux : QueryImpl auxSpec (StateT (QueryCache (D →ₒ R) × Aux) ProbComp)) :
    QueryImpl ((D →ₒ R) + auxSpec) (StateT (QueryCache (D →ₒ R) × Aux) ProbComp)
  | .inl t => fun s => pure (table t, s.1.cacheQuery t (table t), s.2)
  | .inr t => aux t

def lazy (aux : QueryImpl auxSpec (StateT (QueryCache (D →ₒ R) × Aux) ProbComp)) :
    QueryImpl ((D →ₒ R) + auxSpec) (StateT (QueryCache (D →ₒ R) × Aux) ProbComp)
  | .inl t => fun s => (fun r => (r.1, r.2, s.2)) <$> ((D →ₒ R).randomOracle t).run s.1
  | .inr t => aux t

/-- Joint deferred sampling with an auxiliary lazy oracle. Its kernel may
inspect observed cells, but never the latent table or modify the observed cache. -/
theorem joint_table_mixed {α : Type}
    (aux : QueryImpl auxSpec (StateT (QueryCache (D →ₒ R) × Aux) ProbComp))
    (haux : ∀ t s r, r ∈ support ((aux t).run s) → r.2.1 = s.1)
    (oa : OracleComp ((D →ₒ R) + auxSpec) α) (s : QueryCache (D →ₒ R) × Aux) :
    𝒟[do
      let h ← $ᵗ (D → R)
      let table := tableExtending s.1 h
      let r ← (simulateQ (eager table aux) oa).run s
      pure (r, table)] =
    𝒟[do
      let r ← (simulateQ (lazy aux) oa).run s
      let h ← $ᵗ (D → R)
      pure (r, tableExtending r.2.1 h)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | query_bind t k ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, bind_assoc]
    cases t with
    | inl t =>
      simp only [eager, lazy, StateT.run, pure_bind, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc]
      cases hc : s.1 t with
      | some value =>
        have hro : (D →ₒ R).randomOracle t s.1 = pure (value, s.1) :=
          QueryImpl.withCaching_run_some _ hc
        rw [hro]
        simp only [pure_bind]
        have he (h : D → R) : tableExtending s.1 h t = value := by simp [tableExtending, hc]
        have hu : s.1.cacheQuery t value = s.1 := by
          ext u
          by_cases h : u = t
          · subst u; simp [QueryCache.cacheQuery, hc]
          · simp [QueryCache.cacheQuery, h]
        simpa only [he, hu, StateT.run, Prod.mk.eta] using ih value s
      | none =>
        have hro : (D →ₒ R).randomOracle t s.1 =
            (fun value => (value, s.1.cacheQuery t value)) <$> ($ᵗ R) :=
          QueryImpl.withCaching_run_none _ hc
        rw [hro]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        rw [← uniform_update_bind t]
        rw [evalDist_bind]
        conv_rhs => rw [evalDist_bind]
        congr 1
        funext value
        have he (h : D → R) : tableExtending s.1 (Function.update h t value) =
            tableExtending (s.1.cacheQuery t value) h := by
          rw [tableExtending_cacheQuery, tableExtending_update_of_none s.1 h hc]
        have hv (h : D → R) : tableExtending s.1 (Function.update h t value) t = value := by
          simp [tableExtending, hc]
        simpa only [hv, he, StateT.run] using ih value (s.1.cacheQuery t value, s.2)
    | inr t =>
      simp only [eager, lazy, StateT.run]
      rw [DeferredSampling.evalDist_bind_comm]
      apply evalDist_bind_congr
      intro r hr
      simpa only [StateT.run, haux t s r hr] using ih r.1 r.2

end FinitePosterior

namespace ProtectedRouting

open Classical

variable {D E R : Type} [DecidableEq D] [DecidableEq E] [SampleableType R]

def split (f : D → E) (cache : QueryCache (E →ₒ R)) :
    QueryCache (D →ₒ R) × QueryCache (E →ₒ R) :=
  (fun d => cache (f d), fun e => if ∃ d, f d = e then none else cache e)

def aux : QueryImpl (E →ₒ R)
    (StateT (QueryCache (D →ₒ R) × QueryCache (E →ₒ R)) ProbComp) :=
  fun e s => (fun r => (r.1, s.1, r.2)) <$> ((E →ₒ R).randomOracle e).run s.2

def route (f : D → E) : QueryImpl (E →ₒ R) (OracleComp ((D →ₒ R) + (E →ₒ R))) :=
  fun e => if h : ∃ d, f d = e then
    liftM (((D →ₒ R) + (E →ₒ R)).query (.inl h.choose))
    else liftM (((D →ₒ R) + (E →ₒ R)).query (.inr e))

theorem aux_preserves (e : E) (s : QueryCache (D →ₒ R) × QueryCache (E →ₒ R))
    (r) (hr : r ∈ support ((aux e).run s)) : r.2.1 = s.1 := by
  simp only [aux, StateT.run, support_map, Set.mem_image] at hr
  obtain ⟨v, _, rfl⟩ := hr
  rfl

theorem split_update_in (f : D → E) (hinj : Function.Injective f)
    (cache : QueryCache (E →ₒ R)) (d : D) (v : R) :
    split f (cache.cacheQuery (f d) v) = ((split f cache).1.cacheQuery d v, (split f cache).2) := by
  apply Prod.ext
  · funext d'
    by_cases h : d' = d
    · subst d'; simp [split]
    · simp [split, QueryCache.cacheQuery_of_ne _ _ h,
        QueryCache.cacheQuery_of_ne _ _ (fun he => h (hinj he))]
  · funext e
    by_cases h : ∃ d, f d = e
    · simp [split, h]
    · have he : e ≠ f d := fun he => h ⟨d, he.symm⟩
      simp [split, h, QueryCache.cacheQuery_of_ne _ _ he]

theorem split_update_out (f : D → E) (cache : QueryCache (E →ₒ R))
    (e : E) (hout : ∀ d, f d ≠ e) (v : R) :
    split f (cache.cacheQuery e v) = ((split f cache).1, (split f cache).2.cacheQuery e v) := by
  apply Prod.ext
  · funext d
    exact QueryCache.cacheQuery_of_ne _ _ (hout d)
  · funext e'
    by_cases he : e' = e
    · subst e'; simp [split, not_exists.mpr hout]
    · simp [split, QueryCache.cacheQuery_of_ne _ _ he]

set_option backward.isDefEq.respectTransparency false in
/-- The finite protected table and the remaining lazy oracle are an exact
reindexing of the original random oracle, including its cache. -/
theorem query_eq (f : D → E) (hinj : Function.Injective f) (e : E) :
    TprfSecurityProof.StateMap (split (R := R) f) ((E →ₒ R).randomOracle e)
      (simulateQ (FinitePosterior.lazy aux) (route f e)) := by
  intro cache
  by_cases h : ∃ d, f d = e
  · obtain ⟨d, rfl⟩ := h
    have he : route (R := R) f (f d) =
        liftM (((D →ₒ R) + (E →ₒ R)).query (.inl d)) := by
      unfold route
      split_ifs with h'
      · rw [hinj h'.choose_spec]
      · exact (h' ⟨d, rfl⟩).elim
    rw [he]
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      FinitePosterior.lazy, StateT.run]
    change (fun r => (r.1, r.2, (split f cache).2)) <$>
      ((D →ₒ R).randomOracle d).run (split f cache).1 =
      Prod.map id (split f) <$> ((E →ₒ R).randomOracle (f d)).run cache
    have hc : (split f cache).1 d = cache (f d) := rfl
    cases hv : cache (f d) with
    | some v =>
      simp only [QueryImpl.withCaching_run_some _ hv,
        QueryImpl.withCaching_run_some _ (hc.trans hv), map_pure, Prod.map_apply, id]
    | none =>
      simp only [QueryImpl.withCaching_run_none _ hv,
        QueryImpl.withCaching_run_none _ (hc.trans hv), Functor.map_map,
        Function.comp_def, Prod.map_apply, id, split_update_in f hinj]
      rfl
  · simp only [route, dif_neg h, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, FinitePosterior.lazy, aux, StateT.run]
    change (fun r => (r.1, (split f cache).1, r.2)) <$>
      ((E →ₒ R).randomOracle e).run (split f cache).2 =
      Prod.map id (split f) <$> ((E →ₒ R).randomOracle e).run cache
    have hc : (split f cache).2 e = cache e := by simp [split, h]
    cases hv : cache e with
    | some v =>
      simp only [QueryImpl.withCaching_run_some _ hv,
        QueryImpl.withCaching_run_some _ (hc.trans hv), map_pure, Prod.map_apply, id]
    | none =>
      simp only [QueryImpl.withCaching_run_none _ hv,
        QueryImpl.withCaching_run_none _ (hc.trans hv), Functor.map_map,
        Function.comp_def, Prod.map_apply, id, split_update_out f cache e (not_exists.mp h)]

set_option backward.isDefEq.respectTransparency false in
theorem run_eq {α : Type} (f : D → E) (hinj : Function.Injective f)
    (oa : OracleComp (E →ₒ R) α) (cache : QueryCache (E →ₒ R)) :
    (simulateQ (FinitePosterior.lazy aux) (simulateQ (route f) oa)).run (split f cache) =
      Prod.map id (split f) <$> (simulateQ (E →ₒ R).randomOracle oa).run cache := by
  have h := TprfSecurityProof.StateMap.simulateQ (query_eq f hinj) oa cache
  rw [← QueryImpl.simulateQ_compose]
  exact h

/-- The posterior identity holds for the original oracle program, with only
its finite protected cells presampled. -/
theorem joint_original [Finite D] [Finite R] [Nonempty R] [SampleableType (D → R)]
    {α : Type} (f : D → E) (hinj : Function.Injective f)
    (oa : OracleComp (E →ₒ R) α) (cache : QueryCache (E →ₒ R)) :
    𝒟[do
      let h ← $ᵗ (D → R)
      let table := tableExtending (split f cache).1 h
      let r ← (simulateQ (FinitePosterior.eager table aux) (simulateQ (route f) oa)).run (split f cache)
      pure (r, table)] =
    𝒟[do
      let r ← (simulateQ (E →ₒ R).randomOracle oa).run cache
      let h ← $ᵗ (D → R)
      pure (Prod.map id (split f) r, tableExtending (split f r.2).1 h)] := by
  rw [FinitePosterior.joint_table_mixed aux aux_preserves, run_eq f hinj]
  simp only [bind_map_left, Function.comp_def, Prod.map_snd]

def samplingAux : QueryImpl (unifSpec + (E →ₒ R))
    (StateT (QueryCache (D →ₒ R) × QueryCache (E →ₒ R)) ProbComp)
  | .inl n => fun s => (fun v => (v, s)) <$> (liftM (unifSpec.query n) : ProbComp _)
  | .inr e => aux e

def extend : QueryImpl ((D →ₒ R) + (E →ₒ R))
    (OracleComp ((D →ₒ R) + (unifSpec + (E →ₒ R))))
  | .inl d => liftM (((D →ₒ R) + (unifSpec + (E →ₒ R))).query (.inl d))
  | .inr e => liftM (((D →ₒ R) + (unifSpec + (E →ₒ R))).query (.inr (.inr e)))

set_option backward.isDefEq.respectTransparency false in
theorem extend_eq : FinitePosterior.lazy (samplingAux (D := D) (E := E) (R := R)) ∘ₛ extend =
    FinitePosterior.lazy aux := by
  funext t
  cases t <;> simp only [QueryImpl.compose, extend, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map] <;> rfl

def routeWithSampling (f : D → E) (e : E) :
    OracleComp ((D →ₒ R) + (unifSpec + (E →ₒ R))) R := simulateQ extend (route f e)

set_option backward.isDefEq.respectTransparency false in
theorem routeWithSampling_in (f : D → E) (hinj : Function.Injective f) (d : D) :
    routeWithSampling (R := R) f (f d) =
      liftM (((D →ₒ R) + (unifSpec + (E →ₒ R))).query (.inl d)) := by
  unfold routeWithSampling route
  split_ifs with h
  · rw [hinj h.choose_spec]
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, extend]
  · exact (h ⟨d, rfl⟩).elim

set_option backward.isDefEq.respectTransparency false in
theorem queryWithSampling_eq (f : D → E) (hinj : Function.Injective f) (e : E) :
    TprfSecurityProof.StateMap (split (R := R) f) ((E →ₒ R).randomOracle e)
      (simulateQ (FinitePosterior.lazy samplingAux) (routeWithSampling f e)) := by
  simpa only [routeWithSampling, ← QueryImpl.simulateQ_compose, extend_eq] using query_eq (R := R) f hinj e

theorem samplingAux_preserves (t : (unifSpec + (E →ₒ R)).Domain)
    (s : QueryCache (D →ₒ R) × QueryCache (E →ₒ R)) (r)
    (hr : r ∈ support ((samplingAux t).run s)) : r.2.1 = s.1 := by
  cases t with
  | inl n =>
    simp only [samplingAux, StateT.run, support_map, Set.mem_image] at hr
    obtain ⟨v, _, rfl⟩ := hr
    rfl
  | inr e => exact aux_preserves e s r hr

def unrecorded (table : D → R) :
    QueryImpl ((D →ₒ R) + (unifSpec + (E →ₒ R))) (StateT (QueryCache (E →ₒ R)) ProbComp)
  | .inl d => pure (table d)
  | .inr (.inl n) => fun cache => (fun v => (v, cache)) <$>
      (liftM (unifSpec.query n) : ProbComp _)
  | .inr (.inr e) => (E →ₒ R).randomOracle e

set_option backward.isDefEq.respectTransparency false in
theorem unrecorded_in (f : D → E) (hinj : Function.Injective f) (table : D → R) (d : D) :
    simulateQ (unrecorded (E := E) table) (routeWithSampling f (f d)) = pure (table d) := by
  rw [routeWithSampling_in f hinj]
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, unrecorded]

set_option backward.isDefEq.respectTransparency false in
theorem eager_forget_query (table : D → R)
    (t : ((D →ₒ R) + (unifSpec + (E →ₒ R))).Domain) :
    TprfSecurityProof.StateMap Prod.snd
      (FinitePosterior.eager table samplingAux t) (unrecorded table t) := by
  rintro ⟨record, cache⟩
  rcases t with d | n | e
  · simp [FinitePosterior.eager, unrecorded, StateT.run]
    rfl
  · simp [FinitePosterior.eager, unrecorded, samplingAux, StateT.run, Functor.map_map]
  · simp [FinitePosterior.eager, unrecorded, samplingAux, aux, StateT.run, Functor.map_map]

theorem eager_forget_run (table : D → R) {α : Type}
    (oa : OracleComp ((D →ₒ R) + (unifSpec + (E →ₒ R))) α)
    (s : QueryCache (D →ₒ R) × QueryCache (E →ₒ R)) :
    Prod.map id Prod.snd <$> (simulateQ (FinitePosterior.eager table samplingAux) oa).run s =
      (simulateQ (unrecorded table) oa).run s.2 :=
  (TprfSecurityProof.StateMap.simulateQ (eager_forget_query table) oa s).symm

/-- For a fixed latent table, changing the observation record changes neither
the program's output nor its auxiliary lazy cache. -/
theorem eager_reset (table : D → R) {α : Type}
    (oa : OracleComp ((D →ₒ R) + (unifSpec + (E →ₒ R))) α)
    (record record' : QueryCache (D →ₒ R)) (cache : QueryCache (E →ₒ R)) :
    Prod.map id Prod.snd <$>
      (simulateQ (FinitePosterior.eager table samplingAux) oa).run (record, cache) =
    Prod.map id Prod.snd <$>
      (simulateQ (FinitePosterior.eager table samplingAux) oa).run (record', cache) := by
  rw [eager_forget_run, eager_forget_run]

/-- Private key-generation reads may be erased from the observation record
before the public continuation. Their values remain in the latent table. -/
theorem erase_private (table : D → R) {α β : Type}
    (privateRun : OracleComp ((D →ₒ R) + (unifSpec + (E →ₒ R))) α)
    (next : α → OracleComp ((D →ₒ R) + (unifSpec + (E →ₒ R))) β)
    (s : QueryCache (D →ₒ R) × QueryCache (E →ₒ R)) :
    Prod.map id Prod.snd <$>
      (simulateQ (FinitePosterior.eager table samplingAux) (privateRun >>= next)).run s =
    (do
      let r ← (simulateQ (FinitePosterior.eager table samplingAux) privateRun).run s
      Prod.map id Prod.snd <$>
        (simulateQ (FinitePosterior.eager table samplingAux) (next r.1)).run (s.1, r.2.2)) := by
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  intro r
  exact eager_reset table (next r.1) r.2.1 s.1 r.2.2

set_option backward.isDefEq.respectTransparency false in
theorem eager_route_preserves (f : D → E) (hinj : Function.Injective f) (table : D → R)
    (P : D → Prop) (e : E) (he : ∀ d, f d = e → P d)
    (s : QueryCache (D →ₒ R) × QueryCache (E →ₒ R))
    (hs : ∀ d, (s.1 d).isSome → P d) (r)
    (hr : r ∈ support ((simulateQ (FinitePosterior.eager table samplingAux)
      (routeWithSampling f e)).run s)) : ∀ d, (r.2.1 d).isSome → P d := by
  classical
  by_cases h : ∃ d, f d = e
  · obtain ⟨d, rfl⟩ := h
    rw [routeWithSampling_in f hinj] at hr
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      FinitePosterior.eager, StateT.run, mem_support_pure_iff] at hr
    subst r
    intro other ho
    by_cases hd : other = d
    · subst other; exact he d rfl
    · change ((s.1.cacheQuery d (table d)) other).isSome = true at ho
      rw [QueryCache.cacheQuery_of_ne _ _ hd] at ho
      exact hs other ho
  · have hroute : routeWithSampling (R := R) f e =
        liftM (((D →ₒ R) + (unifSpec + (E →ₒ R))).query (.inr (.inr e))) := by
      simp only [routeWithSampling, route, dif_neg h, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, extend]
    rw [hroute] at hr
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      FinitePosterior.eager] at hr
    have hp := samplingAux_preserves (.inr e) s r hr
    simpa only [hp] using hs

end ProtectedRouting

open Classical in
def protectedLocal (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex) :
    QueryImpl (LocalSpec C)
      (OracleComp ((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))))
  | .inl n => liftM (((ProtectedSlot C →ₒ HashOutput) +
      (unifSpec + (Query C →ₒ HashOutput))).query (.inr (.inl n)))
  | .inr (.inl u) => ProtectedRouting.routeWithSampling (protectedInput x b) u
  | .inr (.inr p) => (fun v => prims.aes.eval (truncateHash v) p.2.2) <$>
      ProtectedRouting.routeWithSampling (protectedInput x b) (.streamKey p.2.1)

set_option backward.isDefEq.respectTransparency false in
theorem protectedLocal_eq (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (t : (LocalSpec C).Domain) :
    TprfSecurityProof.StateMap (ProtectedRouting.split (R := HashOutput) (protectedInput x b))
      (signingLocalAnswer prims t)
      (simulateQ (FinitePosterior.lazy ProtectedRouting.samplingAux) (protectedLocal prims x b t)) := by
  classical
  have hinj := protectedInput_injective x b hno
  rcases t with n | u | p
  · intro cache
    simp only [protectedLocal, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, FinitePosterior.lazy, ProtectedRouting.samplingAux,
      StateT.run, signingLocalAnswer, QueryImpl.add_apply_inl]
    rfl
  · exact ProtectedRouting.queryWithSampling_eq (protectedInput x b) hinj u
  · simpa only [protectedLocal, simulateQ_map, signingLocalAnswer, QueryImpl.add_apply_inr,
      prgAnswer, hashAnswer, map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, Function.comp_def] using
      (ProtectedRouting.queryWithSampling_eq (protectedInput x b) hinj (.streamKey p.2.1)).map
        (fun v => prims.aes.eval (truncateHash v) p.2.2)

set_option backward.isDefEq.respectTransparency false in
theorem protectedLocal_run_eq (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) :
    (simulateQ (FinitePosterior.lazy ProtectedRouting.samplingAux)
      (simulateQ (protectedLocal prims x b) oa)).run (ProtectedRouting.split (protectedInput x b) cache) =
    Prod.map id (ProtectedRouting.split (protectedInput x b)) <$>
      (simulateQ (signingLocalAnswer prims) oa).run cache := by
  classical
  rw [← QueryImpl.simulateQ_compose]
  exact TprfSecurityProof.StateMap.simulateQ (protectedLocal_eq prims x b hno) oa cache

open Classical in
/-- Joint deferred sampling for the actual signing local oracle, including
private sampling and PRG derivations. -/
theorem protectedLocal_joint (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) :
    𝒟[do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h
      let r ← (simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b) oa)).run (ProtectedRouting.split (protectedInput x b) cache)
      pure (r, table)] =
    𝒟[do
      let r ← (simulateQ (signingLocalAnswer prims) oa).run cache
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      pure (Prod.map id (ProtectedRouting.split (protectedInput x b)) r,
        tableExtending (ProtectedRouting.split (protectedInput x b) r.2).1 h)] := by
  rw [FinitePosterior.joint_table_mixed _ ProtectedRouting.samplingAux_preserves,
    protectedLocal_run_eq prims x b hno]
  simp only [bind_map_left, Function.comp_def, Prod.map_snd]

/-- Forget the role tag on local calls. Only the syntactically unreachable
programming branch receives a placeholder response. -/
def worldLocalize : QueryImpl (WorldSpec C) (OracleComp (LocalSpec C))
  | .inl (.inl t) | .inr t => query (spec := LocalSpec C) t
  | .inl (.inr _) => pure false

set_option backward.isDefEq.respectTransparency false in
theorem programFree_simulate_local {m : Type → Type} [Monad m] [LawfulMonad m]
    (I : QueryImpl (LocalSpec C) m) (W : QueryImpl (WorldSpec C) m)
    (hcounted : ∀ t, W (.inl (.inl t)) = I t) (hfree : ∀ t, W (.inr t) = I t)
    {α : Type} (oa : OracleComp (WorldSpec C) α) (h : ProgramFree oa) :
    simulateQ W oa = simulateQ I (simulateQ worldLocalize oa) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]
  | query_bind t k ih =>
    have hb := (isQueryBoundP_query_bind_iff IsProgram t k 0).mp h
    have ht : ¬IsProgram t := by simpa using hb.1
    have hk : ∀ u, ProgramFree (k u) := by simpa [ProgramFree, ht] using hb.2
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    have he : W t = simulateQ I (worldLocalize t) := by
      rcases t with (t | pg) | t
      · simp only [worldLocalize, HasQuery.instOfMonadLift_query, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map, hcounted]
      · exact (ht trivial).elim
      · simp only [worldLocalize, HasQuery.instOfMonadLift_query, simulateQ_query,
          OracleQuery.input_query, OracleQuery.cont_query, id_map, hfree]
    rw [he]
    congr 1
    funext u
    exact ih u (hk u)

def localCost : (LocalSpec C).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

def withLocalCount {σ : Type} (I : QueryImpl (LocalSpec C) (StateT σ ProbComp)) :
    QueryImpl (LocalSpec C) (StateT (σ × ℕ) ProbComp) := fun t =>
  StateT.mk fun p => (fun z => (z.1, (z.2, p.2 + localCost t))) <$> (I t).run p.1

/-- Both role tags charge the same local call exactly once. In particular,
internal PRG expansion does not create another counted world query. -/
theorem programFree_count_local {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : ProgramFree oa) :
    simulateQ (SigningCacheProof.countImpl prims) oa =
      simulateQ (withLocalCount (signingLocalAnswer prims)) (simulateQ worldLocalize oa) := by
  apply programFree_simulate_local _ _ _ _ oa h
  · rintro (n | (q | p)) <;> rfl
  · rintro (n | (q | p)) <;> rfl

/-- Once the residual program at the gate has been selected, its raw log
can be forgotten without changing the final outcome, cache, or count. -/
theorem logged_forget {α : Type} (oa : OracleComp (WorldSpec C) α) (s : LoggedState C) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (loggedImpl prims) oa).run s =
      (simulateQ (SigningCacheProof.countImpl prims) oa).run s.1 :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun t state log => by simp [loggedImpl, Functor.map_map]) oa s.1 s.2

namespace CountedPosterior

open Classical

variable (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)

abbrev AuxSpec (C : Committee) :=
  (unifSpec + (Query C →ₒ HashOutput)) + (ℕ →ₒ Unit)

/-- Auxiliary sampling retains the original-query count. A separate tick
changes only that count, never the protected observation record. -/
def aux : QueryImpl (AuxSpec C)
    (StateT (QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ)) ProbComp)
  | .inl t => StateT.mk fun s =>
      (fun r => (r.1, r.2.1, (r.2.2, s.2.2))) <$>
        (ProtectedRouting.samplingAux t).run (s.1, s.2.1)
  | .inr cost => StateT.mk fun s => pure ((), s.1, (s.2.1, s.2.2 + cost))

def extend : QueryImpl ((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput)))
    (OracleComp ((ProtectedSlot C →ₒ HashOutput) + AuxSpec C))
  | .inl slot => query (spec := (ProtectedSlot C →ₒ HashOutput) + AuxSpec C) (.inl slot)
  | .inr t => query (spec := (ProtectedSlot C →ₒ HashOutput) + AuxSpec C) (.inr (.inl t))

def localQuery (t : (LocalSpec C).Domain) :
    OracleComp ((ProtectedSlot C →ₒ HashOutput) + AuxSpec C) ((LocalSpec C).Range t) := do
  let value ← simulateQ extend (protectedLocal prims x b t)
  let _ ← query (spec := (ProtectedSlot C →ₒ HashOutput) + AuxSpec C) (.inr (.inr (localCost t)))
  pure value

theorem aux_preserves (t : (AuxSpec C).Domain)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ)) :
    ∀ r ∈ support ((aux t).run s), r.2.1 = s.1 := by
  rcases t with t | cost
  · intro r hr
    simp only [aux, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    exact ProtectedRouting.samplingAux_preserves t (s.1, s.2.1) v hv
  · intro r hr
    simp only [aux, StateT.run_mk, mem_support_pure_iff] at hr
    subst r
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem extend_lazy_query
    (t : ((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))).Domain)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) (n : ℕ) :
    (simulateQ (FinitePosterior.lazy aux) (extend t)).run (s.1, (s.2, n)) =
      (fun r => (r.1, r.2.1, (r.2.2, n))) <$>
        ((FinitePosterior.lazy ProtectedRouting.samplingAux) t).run s := by
  rcases t with slot | t
  · simp only [extend, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, FinitePosterior.lazy,
      StateT.run, Functor.map_map]
  · simp only [extend, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, FinitePosterior.lazy,
      aux, StateT.run_mk]
    rfl

theorem extend_lazy_run {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))) α)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) (n : ℕ) :
    (simulateQ (FinitePosterior.lazy aux) (simulateQ extend oa)).run (s.1, (s.2, n)) =
      (fun r => (r.1, r.2.1, (r.2.2, n))) <$>
        (simulateQ (FinitePosterior.lazy ProtectedRouting.samplingAux) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s n with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, extend_lazy_query,
      bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 r.2 n

set_option backward.isDefEq.respectTransparency false in
theorem local_lazy_eq (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (t : (LocalSpec C).Domain) :
    TprfSecurityProof.StateMap
      (fun s : HashCache C × ℕ =>
        ((ProtectedRouting.split (protectedInput x b) s.1).1,
         ((ProtectedRouting.split (protectedInput x b) s.1).2, s.2)))
      (withLocalCount (signingLocalAnswer prims) t)
      (simulateQ (FinitePosterior.lazy aux) (localQuery prims x b t)) := by
  intro s
  simp only [localQuery, simulateQ_bind, simulateQ_pure, HasQuery.instOfMonadLift_query,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    StateT.run_bind, StateT.run_pure, FinitePosterior.lazy, aux, StateT.run_mk,
    pure_bind, bind_pure_comp]
  rw [extend_lazy_run]
  simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query,
    FinitePosterior.lazy, aux, StateT.run_mk, map_pure, bind_map_left, bind_pure_comp]
  rw [protectedLocal_eq prims x b hno t s.1]
  simp only [withLocalCount, StateT.run_mk, Functor.map_map]
  rfl

theorem local_lazy_run (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ) :
    (simulateQ (FinitePosterior.lazy aux) (simulateQ (localQuery prims x b) oa)).run
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        ((ProtectedRouting.split (protectedInput x b) cache).2, n)) =
      (fun r => (r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
        ((ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2))) <$>
      (simulateQ (withLocalCount (signingLocalAnswer prims)) oa).run (cache, n) := by
  rw [← QueryImpl.simulateQ_compose]
  exact TprfSecurityProof.StateMap.simulateQ (local_lazy_eq prims x b hno) oa (cache, n)

set_option backward.isDefEq.respectTransparency false in
/-- Exact joint posterior for the actual local signing oracle with its
original-query count. PRG expansion remains inside one counted call. -/
theorem joint_local (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ) :
    𝒟[do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h
      let r ← (simulateQ (FinitePosterior.eager table aux)
        (simulateQ (localQuery prims x b) oa)).run
          ((ProtectedRouting.split (protectedInput x b) cache).1,
            ((ProtectedRouting.split (protectedInput x b) cache).2, n))
      pure (r, table)] =
    𝒟[do
      let r ← (simulateQ (withLocalCount (signingLocalAnswer prims)) oa).run (cache, n)
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      pure ((r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
        ((ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2)),
        tableExtending (ProtectedRouting.split (protectedInput x b) r.2.1).1 h)] := by
  rw [FinitePosterior.joint_table_mixed (D := ProtectedSlot C) (R := HashOutput)
    (aux (C := C)) aux_preserves (simulateQ (localQuery prims x b) oa)
    ((ProtectedRouting.split (protectedInput x b) cache).1,
      ((ProtectedRouting.split (protectedInput x b) cache).2, n)), local_lazy_run prims x b hno]
  simp only [bind_map_left]

/-- The counted posterior applies to every syntactically program-free
world residual, retaining the actual world count. -/
theorem joint_world (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hfree : ProgramFree oa)
    (cache : HashCache C) (n : ℕ) :
    𝒟[do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h
      let r ← (simulateQ (FinitePosterior.eager table aux)
        (simulateQ (localQuery prims x b) (simulateQ worldLocalize oa))).run
          ((ProtectedRouting.split (protectedInput x b) cache).1,
            ((ProtectedRouting.split (protectedInput x b) cache).2, n))
      pure (r, table)] =
    𝒟[do
      let r ← (simulateQ (SigningCacheProof.countImpl prims) oa).run (cache, n)
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      pure ((r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
        ((ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2)),
        tableExtending (ProtectedRouting.split (protectedInput x b) r.2.1).1 h)] := by
  rw [programFree_count_local prims oa hfree]
  exact joint_local prims x b hno _ cache n

set_option backward.isDefEq.respectTransparency false in
theorem extend_eager_forget_query (table : ProtectedSlot C → HashOutput)
    (t : ((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))).Domain) :
    TprfSecurityProof.StateMap (fun s => (s.1, s.2.1))
      (simulateQ (FinitePosterior.eager table aux) (extend t))
      (FinitePosterior.eager table ProtectedRouting.samplingAux t) := by
  rintro ⟨record, cache, n⟩
  rcases t with slot | t <;>
    simp only [extend, HasQuery.instOfMonadLift_query, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, FinitePosterior.eager,
      aux, StateT.run_mk, StateT.run, map_pure, Functor.map_map]
  all_goals simp [StateT.mk, Functor.map_map, Function.comp_def]

theorem extend_eager_forget_run (table : ProtectedSlot C → HashOutput) {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))) α)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ)) :
    (simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux) oa).run (s.1, s.2.1) =
      (fun r => (r.1, r.2.1, r.2.2.1)) <$>
        (simulateQ (FinitePosterior.eager table aux) (simulateQ extend oa)).run s := by
  rw [← QueryImpl.simulateQ_compose]
  exact TprfSecurityProof.StateMap.simulateQ (extend_eager_forget_query table) oa s

set_option backward.isDefEq.respectTransparency false in
theorem local_eager_forget (table : ProtectedSlot C → HashOutput)
    (t : (LocalSpec C).Domain) :
    TprfSecurityProof.StateMap (fun s => (s.1, s.2.1))
      (simulateQ (FinitePosterior.eager table aux) (localQuery prims x b t))
      (simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (protectedLocal prims x b t)) := by
  intro s
  rw [extend_eager_forget_run table (protectedLocal prims x b t) s]
  simp only [localQuery, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    HasQuery.instOfMonadLift_query, simulateQ_map, StateT.run_map, simulateQ_spec_query,
    FinitePosterior.eager, aux, StateT.run_mk, map_pure, bind_pure_comp, Functor.map_map]
  rfl

theorem eager_forget_run (table : ProtectedSlot C → HashOutput) {α : Type}
    (oa : OracleComp (LocalSpec C) α)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ)) :
    (simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
      (simulateQ (protectedLocal prims x b) oa)).run (s.1, s.2.1) =
      (fun r => (r.1, r.2.1, r.2.2.1)) <$>
        (simulateQ (FinitePosterior.eager table aux) (simulateQ (localQuery prims x b) oa)).run s := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  exact TprfSecurityProof.StateMap.simulateQ (local_eager_forget prims x b table) oa s

end CountedPosterior

namespace TruncatedCompletion

open Classical

variable {D : Type} [DecidableEq D]

def digestOracle : QueryImpl (D →ₒ Digest) (StateT (QueryCache (D →ₒ Digest)) ProbComp) :=
  letI : Inhabited Digest := Classical.inhabited_of_nonempty inferInstance
  letI : SampleableType Digest := .ofFintype Digest
  letI : IsUniformSpec (D →ₒ Digest) := .ofFintypeInhabited _
  (D →ₒ Digest).randomOracle

def project (cache : QueryCache (D →ₒ HashOutput)) : QueryCache (D →ₒ Digest) :=
  fun d => (cache d).map truncateHash

def answer : QueryImpl (D →ₒ Digest) (StateT (QueryCache (D →ₒ HashOutput)) ProbComp) :=
  fun d => truncateHash <$> ((D →ₒ HashOutput).randomOracle d)

def lift : QueryImpl (D →ₒ Digest) (OracleComp (D →ₒ HashOutput)) :=
  fun d => truncateHash <$> query (spec := D →ₒ HashOutput) d

theorem project_update (cache : QueryCache (D →ₒ HashOutput)) (d : D) (value : HashOutput) :
    project (cache.cacheQuery d value) = (project cache).cacheQuery d (truncateHash value) := by
  funext e
  by_cases he : e = d
  · subst e
    simp [project]
  · simp [project, QueryCache.cacheQuery, he]

/-- Full 256-bit private answers project to exactly the lazy 128-bit row
law. This projection is not applied to public adversary answers. -/
theorem query_projection (d : D) (cache : QueryCache (D →ₒ HashOutput)) :
    𝒟[Prod.map id project <$> (answer d).run cache] =
      𝒟[((digestOracle (D := D)) d).run (project cache)] := by
  dsimp only [digestOracle]
  cases hc : cache d with
  | none =>
    have hp : project cache d = none := by simp [project, hc]
    simp only [answer, StateT.run_map]
    rw [QueryImpl.withCaching_run_none _ hc, QueryImpl.withCaching_run_none _ hp]
    simp only [Functor.map_map, Function.comp_def, Prod.map, id_eq, project_update]
    calc
      _ = 𝒟[(fun v => (v, (project cache).cacheQuery d v)) <$>
          (truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput))] := by
        simp only [Functor.map_map, Function.comp_def]
        simp only [evalDist_map, uniformSampleImpl, evalDist_uniformSample]
      _ = _ := by
        rw [evalDist_map, evalDist_truncateHash_uniform, ← evalDist_map]
        simp only [evalDist_map, uniformSampleImpl, evalDist_uniformSample]
  | some value =>
    have hp : project cache d = some (truncateHash value) := by simp [project, hc]
    simp only [answer, StateT.run_map]
    rw [QueryImpl.withCaching_run_some _ hc, QueryImpl.withCaching_run_some _ hp]
    simp

/-- Arbitrary private completion programs may consume the projected
answers adaptively while retaining the correct projected final cache. -/
theorem run_projection {α : Type} (oa : OracleComp (D →ₒ Digest) α)
    (cache : QueryCache (D →ₒ HashOutput)) :
    𝒟[Prod.map id project <$>
      (simulateQ (D →ₒ HashOutput).randomOracle (simulateQ lift oa)).run cache] =
      𝒟[(simulateQ (digestOracle (D := D)) oa).run (project cache)] := by
  have he : QueryImpl.compose (D →ₒ HashOutput).randomOracle lift = (answer (D := D)) := by
    funext d
    simp only [QueryImpl.compose, lift, simulateQ_map, HasQuery.instOfMonadLift_query,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, answer]
  rw [← QueryImpl.simulateQ_compose, he]
  exact evalDist_simulateQ_state_projection answer (digestOracle (D := D)) project
    query_projection oa cache

/-- Projecting away the final cache gives the exact private output law. -/
theorem run'_projection {α : Type} (oa : OracleComp (D →ₒ Digest) α)
    (cache : QueryCache (D →ₒ HashOutput)) :
    𝒟[(simulateQ (D →ₒ HashOutput).randomOracle (simulateQ lift oa)).run' cache] =
      𝒟[(simulateQ (digestOracle (D := D)) oa).run' (project cache)] := by
  have h := congrArg (fun d => Prod.fst <$> d) (run_projection oa cache)
  simpa only [← evalDist_map, Functor.map_map, Function.comp_def, Prod.map_fst,
    id_eq, StateT.run'_eq] using h

set_option maxRecDepth 10000 in
/-- The marked private chain really has `MarkedChain.law`, even though its
underlying oracle samples full 256-bit outputs. -/
theorem walk_law {Index : Type} [DecidableEq Index]
    (observed : Index → Digest → Option Digest) (indices : List Index) (hn : indices.Nodup)
    (start : Digest) (cache : QueryCache ((Index × Digest) →ₒ HashOutput))
    (hc : ∀ index ∈ indices, ∀ input, project cache (index, input) = observed index input) :
    𝒟[(simulateQ ((Index × Digest) →ₒ HashOutput).randomOracle
      (simulateQ lift (MarkedChain.walk observed indices start))).run' cache] =
      liftM (MarkedChain.law (fun k : Fin indices.length => observed indices[k]) start) := by
  rw [run'_projection]
  exact MarkedChain.walk_run observed indices hn start (project cache) hc

set_option maxRecDepth 10000 in
/-- Finite deferred sampling produces the same private output law. The
latent table remains 256-bit and is overlaid only at actually observed cells. -/
theorem table_output {α : Type} [Fintype D]
    (oa : OracleComp (D →ₒ HashOutput) α) (cache : QueryCache (D →ₒ HashOutput)) :
    𝒟[(fun h => (FinitePosterior.evalRecorded oa cache (tableExtending cache h)).1) <$>
      ($ᵗ (D → HashOutput))] =
      𝒟[(simulateQ (D →ₒ HashOutput).randomOracle oa).run' cache] := by
  have h := congrArg (fun d => (fun r => r.1.1) <$> d) (FinitePosterior.joint_table oa cache)
  simp only [← evalDist_map, Functor.map_map, Function.comp_def, map_bind,
    map_pure, bind_pure_comp] at h
  refine h.trans ?_
  rw [StateT.run'_eq, ← bind_pure_comp]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro r
  simp only [evalDist_map, evalDist_uniformSample, evalDist_pure]
  rw [← SPMF.toPMF_inj]
  simp [SPMF.toPMF_map, SPMF.toPMF_liftM, PMF.monad_map_eq_map, PMF.map_bind,
    PMF.pure_map, PMF.bind_const]

/-- Exact full-table realization of the marked private-completion law. -/
theorem table_walk_law {Index : Type} [Fintype Index] [DecidableEq Index]
    (observed : Index → Digest → Option Digest) (indices : List Index) (hn : indices.Nodup)
    (start : Digest) (cache : QueryCache ((Index × Digest) →ₒ HashOutput))
    (hc : ∀ index ∈ indices, ∀ input, project cache (index, input) = observed index input) :
    𝒟[(fun h => (FinitePosterior.evalRecorded (simulateQ lift (MarkedChain.walk observed indices start))
      cache (tableExtending cache h)).1) <$> ($ᵗ ((Index × Digest) → HashOutput))] =
      liftM (MarkedChain.law (fun k : Fin indices.length => observed indices[k]) start) := by
  rw [table_output]
  exact walk_law observed indices hn start cache hc

/-- Uniform sampling of a whole table of independent coordinates factors
joint events exactly; this is the independence needed for all 58 chains. -/
theorem uniform_forall_probability {I T : Type} [Fintype I] [DecidableEq I]
    [Fintype T] [Nonempty T] [SampleableType T] [SampleableType (I → T)]
    (event : I → T → Prop) :
    Pr[fun table => ∀ i, event i (table i) | $ᵗ (I → T)] =
      ∏ i, Pr[event i | $ᵗ T] := by
  classical
  have he (table : I → T) :
      (if ∀ i, event i (table i) then (1 : ℝ≥0∞) else 0) =
      ∏ i, if event i (table i) then (1 : ℝ≥0∞) else 0 := by
    by_cases h : ∀ i, event i (table i)
    · simp [h]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hw (f : I → T → ℝ≥0∞) :
      ∑ table : I → T, (Fintype.card (I → T) : ℝ≥0∞)⁻¹ * ∏ i, f i (table i) =
      ∏ i, ∑ t : T, (Fintype.card T : ℝ≥0∞)⁻¹ * f i t := by
    simp only [← Finset.mul_sum, ← Fintype.prod_sum f, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]
  rw [probEvent_eq_tsum_ite, tsum_fintype]
  simp only [probOutput_uniformSample]
  have hi (c : ℝ≥0∞) (p : Prop) [Decidable p] : (if p then c else 0) = c * (if p then 1 else 0) := by
    split_ifs <;> simp
  trans ∑ table : I → T, (Fintype.card (I → T) : ℝ≥0∞)⁻¹ *
    ∏ i, if event i (table i) then (1 : ℝ≥0∞) else 0
  · apply Finset.sum_congr rfl
    intro table _
    rw [hi, he]
  rw [hw (fun i t => if event i t then 1 else 0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [probEvent_eq_tsum_ite, tsum_fintype]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : event i t <;> simp [ht, probOutput_uniformSample]

set_option backward.isDefEq.respectTransparency false in
/-- The exact joint law of independent full-output chain completions is
 the product of their marked endpoint laws. -/
theorem table_walks_probability {I Index : Type} [Fintype I] [DecidableEq I]
    [Fintype Index] [DecidableEq Index]
    (observed : I → Index → Digest → Option Digest) (indices : List Index) (hn : indices.Nodup)
    (starts endpoints : I → Digest)
    (cache : I → QueryCache ((Index × Digest) →ₒ HashOutput))
    (hc : ∀ i index, index ∈ indices → ∀ input,
      project (cache i) (index, input) = observed i index input) :
    Pr[fun tables => ∀ i,
      (FinitePosterior.evalRecorded (simulateQ lift (MarkedChain.walk (observed i) indices (starts i)))
        (cache i) (tableExtending (cache i) (tables i))).1 = some (endpoints i) |
      $ᵗ (I → (Index × Digest) → HashOutput)] =
      ∏ i, MarkedChain.law (fun k : Fin indices.length => observed i indices[k]) (starts i)
        (some (endpoints i)) := by
  rw [uniform_forall_probability (I := I) (T := (Index × Digest) → HashOutput)
    (fun i table =>
      (FinitePosterior.evalRecorded (simulateQ lift (MarkedChain.walk (observed i) indices (starts i)))
        (cache i) (tableExtending (cache i) table)).1 = some (endpoints i))]
  apply Finset.prod_congr rfl
  intro i _
  have h := table_walk_law (observed i) indices hn (starts i) (cache i) (hc i)
  have hp := congrArg (fun d : SPMF (Option Digest) => d (some (endpoints i))) h
  rw [← probOutput_def, probOutput_map] at hp
  simpa only [SPMF.liftM_apply] using hp

/-- Independent full-output marked completions, averaged over a jointly
uniform start vector, pay one inverse vector-space size at any fixed endpoints. -/
theorem table_walks_density {I Index : Type} [Fintype I] [DecidableEq I]
    [Fintype Index] [DecidableEq Index]
    (observed : I → Index → Digest → Option Digest) (indices : List Index) (hn : indices.Nodup)
    (endpoints : I → Digest)
    (cache : I → QueryCache ((Index × Digest) →ₒ HashOutput))
    (hc : ∀ i index, index ∈ indices → ∀ input,
      project (cache i) (index, input) = observed i index input) :
    (∑ starts : I → Digest, Pr[= starts | $ᵗ (I → Digest)] *
      Pr[fun tables => ∀ i,
        (FinitePosterior.evalRecorded (simulateQ lift (MarkedChain.walk (observed i) indices (starts i)))
          (cache i) (tableExtending (cache i) (tables i))).1 = some (endpoints i) |
        $ᵗ (I → (Index × Digest) → HashOutput)]) ≤
      ((2 ^ 128 : ℝ≥0∞) ^ Fintype.card I)⁻¹ := by
  simp_rw [table_walks_probability observed indices hn _ endpoints cache hc, probOutput_uniformSample]
  have h := MarkedChain.joint_uniformStart_density
    (fun i => fun k : Fin indices.length => observed i indices[k]) endpoints
  simpa only [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat] using h

end TruncatedCompletion

namespace ProtectedTable

open Classical

abbrev Parts (C : Committee) := (TprfSecurityProof.Slot C → HashOutput) ×
  (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput)

/-- Reindex the latent table, keeping both independent blocks. -/
def split : (ProtectedSlot C → HashOutput) ≃ Parts C :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    ((Equiv.refl _).prodCongr (Equiv.curry _ _ _))

def slotCache (cache : QueryCache (ProtectedSlot C →ₒ HashOutput)) :
    TprfSecurityProof.SlotCache C := fun slot => cache (.inl slot)

def chainCache (cache : QueryCache (ProtectedSlot C →ₒ HashOutput)) (l : ChainIndex) :
    QueryCache ((XmssSecurity.ChainStep × Digest) →ₒ HashOutput) :=
  fun p => cache (.inr (l, p))

/-- The observed overlay is applied after splitting the uniform table. -/
theorem split_overlay (cache : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (table : ProtectedSlot C → HashOutput) :
    split (tableExtending cache table) =
      (tableExtending (slotCache cache) (split table).1,
       fun l => tableExtending (chainCache cache l) ((split table).2 l)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem uniform_pair {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [SampleableType A] [SampleableType B]
    [SampleableType (A × B)] :
    𝒟[$ᵗ (A × B)] = 𝒟[do let a ← $ᵗ A; let b ← $ᵗ B; pure (a, b)] := by
  apply evalDist_ext
  intro z
  have hp := probOutput_bind_bind_prod_mk_eq_mul ($ᵗ A) ($ᵗ B) id id z
  simpa only [id_eq, id_map, probOutput_uniformSample, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (a := (Fintype.card A : ℝ≥0∞)) (b := (Fintype.card B : ℝ≥0∞))
      (.inr (by simp)) (.inr (by simp [Fintype.card_ne_zero]))] using hp.symm

/-- Exact posterior factorization, including an arbitrary fixed observed cache. -/
theorem posterior_split (cache : QueryCache (ProtectedSlot C →ₒ HashOutput)) :
    𝒟[(fun table => split (tableExtending cache table)) <$>
      ($ᵗ (ProtectedSlot C → HashOutput))] =
    𝒟[do
      let slots ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
      let chains ← $ᵗ (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput)
      pure (tableExtending (slotCache cache) slots,
        fun l => tableExtending (chainCache cache l) (chains l))] := by
  let overlay : Parts C → Parts C := fun p =>
    (tableExtending (slotCache cache) p.1,
      fun l => tableExtending (chainCache cache l) (p.2 l))
  have h := evalDist_map_bijective_uniform_cross (ProtectedSlot C → HashOutput)
    (split (C := C)) split.bijective
  have hm := congrArg (fun d : SPMF (Parts C) => overlay <$> d) h
  simp only [← evalDist_map, Functor.map_map] at hm
  change 𝒟[(fun table => overlay (split table)) <$> ($ᵗ (ProtectedSlot C → HashOutput))] = _
  rw [hm]
  have hp := congrArg (fun d : SPMF (Parts C) => overlay <$> d) (uniform_pair
    (A := TprfSecurityProof.Slot C → HashOutput)
    (B := ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput))
  simpa only [← evalDist_map, map_bind, map_pure, overlay] using hp

end ProtectedTable

namespace UnopenedPrivacy

open Classical TprfSecurityProof

/-- An unopened-point view may fix all other slots, as well as revealed
shares of the challenged points. Private challenged shares are excluded. -/
def ReadAllowed (D : Finset C.Party) (challenged : Finset Point) : Slot C → Prop
  | .inl (T, p) => Revealed D (.inl T) ∨ p ∉ challenged
  | .inr _ => True

theorem ReadAllowed.mono {D D' : Finset C.Party} (hD : D ⊆ D')
    {challenged : Finset Point} {slot : Slot C} (h : ReadAllowed D challenged slot) :
    ReadAllowed D' challenged slot := by
  rcases slot with ⟨T, p⟩ | pair
  · exact h.imp (revealed_mono hD) id
  · trivial

/-- A direct adversary query to a threshold slot is allowed whenever the
actual hidden-key flag remains clear. This uses the game's flag itself. -/
theorem hiddenHit_readAllowed (x : SigningSecurityProof.Keys3 C) (D : Finset C.Party)
    (challenged : Finset Point) (slot : Slot C)
    (hflag : SigningCoreProof.hiddenHit x D
      (.inr (.inl (slotInput x.2.1 x.2.2 slot))) = false) : ReadAllowed D challenged slot := by
  rcases slot with ⟨T, p⟩ | pair
  · change Revealed D (.inl T) ∨ p ∉ challenged
    left
    by_contra hn
    simp [SigningCoreProof.hiddenHit, slotInput, show ∃ T', x.2.1 T = x.2.1 T' ∧
      ¬Revealed D (.inl T') from ⟨T, rfl, hn⟩] at hflag
  · trivial

def CacheAllowed (D : Finset C.Party) (challenged : Finset Point) (cache : SlotCache C) : Prop :=
  ∀ slot, (cache slot).isSome → ReadAllowed D challenged slot

theorem CacheAllowed.empty (D : Finset C.Party) (challenged : Finset Point) :
    CacheAllowed D challenged ∅ := by
  intro slot h
  simp at h

theorem CacheAllowed.mono {D D' : Finset C.Party} (hD : D ⊆ D')
    {challenged : Finset Point} {cache : SlotCache C} (h : CacheAllowed D challenged cache) :
    CacheAllowed D' challenged cache := fun slot hs => (h slot hs).mono hD

theorem CacheAllowed.cacheQuery {D : Finset C.Party} {challenged : Finset Point}
    {cache : SlotCache C} (h : CacheAllowed D challenged cache) (slot : Slot C)
    (v : HashOutput) (hs : ReadAllowed D challenged slot) :
    CacheAllowed D challenged (cache.cacheQuery slot v) := by
  intro other ho
  by_cases he : other = slot
  · subst other; exact hs
  · rw [QueryCache.cacheQuery_of_ne _ _ he] at ho
    exact h other ho

def ProtectedAllowed (D : Finset C.Party) (challenged : Finset Point) : ProtectedSlot C → Prop
  | .inl slot => ReadAllowed D challenged slot
  | .inr _ => True

def RecordAllowed (D : Finset C.Party) (challenged : Finset Point)
    (record : QueryCache (ProtectedSlot C →ₒ HashOutput)) : Prop :=
  ∀ slot, (record slot).isSome → ProtectedAllowed D challenged slot

theorem RecordAllowed.slots {D : Finset C.Party} {challenged : Finset Point}
    {record : QueryCache (ProtectedSlot C →ₒ HashOutput)} (h : RecordAllowed D challenged record) :
    CacheAllowed D challenged (fun slot => record (.inl slot)) := fun slot hs => h (.inl slot) hs

theorem RecordAllowed.mono {D D' : Finset C.Party} (hD : D ⊆ D')
    {challenged : Finset Point} {record : QueryCache (ProtectedSlot C →ₒ HashOutput)}
    (h : RecordAllowed D challenged record) : RecordAllowed D' challenged record := by
  rintro (slot | cell) hs
  · exact (h (.inl slot) hs).mono hD
  · trivial

set_option backward.isDefEq.respectTransparency false in
/-- The actual local adversary handler preserves the allowed-read invariant
on every branch on which its hidden-key flag stays false. -/
theorem protectedLocal_preserves (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬KeyCollision x.2.1 x.2.2) (table : ProtectedSlot C → HashOutput)
    (D : Finset C.Party) (challenged : Finset Point) (t : (LocalSpec C).Domain)
    (hflag : SigningCoreProof.hiddenHit x D t = false)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C)
    (hs : RecordAllowed D challenged s.1) (r)
    (hr : r ∈ support ((simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
      (protectedLocal prims x b t)).run s)) : RecordAllowed D challenged r.2.1 := by
  have hinj := protectedInput_injective x b hno
  rcases t with n | u | p
  · simp only [protectedLocal, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, FinitePosterior.eager, ProtectedRouting.samplingAux, StateT.run, support_map,
      Set.mem_image] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact hs
  · apply ProtectedRouting.eager_route_preserves (protectedInput x b) hinj table
      (ProtectedAllowed D challenged) u ?_ s hs r hr
    rintro (slot | cell) he
    · change slotInput x.2.1 x.2.2 slot = u at he
      subst u
      exact hiddenHit_readAllowed x D challenged slot hflag
    · trivial
  · simp only [protectedLocal, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    apply ProtectedRouting.eager_route_preserves (protectedInput x b) hinj table
      (ProtectedAllowed D challenged) (.streamKey p.2.1) ?_ s hs v hv
    rintro (slot | cell) he
    · rcases slot with ⟨T, point⟩ | mask <;> cases he
    · trivial

def recordRo (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput) : OracleComp (RoSpec C) →ᵐ
      StateT (QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) ProbComp where
  toFun _ oa := simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
    (simulateQ (protectedLocal prims x b) (liftComp oa (LocalSpec C)))
  toFun_pure' a := by simp only [liftComp_pure, simulateQ_pure]
  toFun_bind' oa f := by simp only [liftComp_bind, simulateQ_bind]

def SafeRecord (D : Finset C.Party) (challenged : Finset Point) {α : Type}
    (oa : StateT (QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) ProbComp α) : Prop :=
  ∀ s, RecordAllowed D challenged s.1 → ∀ r ∈ support (oa.run s), RecordAllowed D challenged r.2.1

theorem SafeRecord.pure (D : Finset C.Party) (challenged : Finset Point) {α : Type} (a : α) :
    SafeRecord D challenged (pure a) := by
  intro s hs r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  exact hs

theorem SafeRecord.bind {D : Finset C.Party} {challenged : Finset Point} {α β : Type}
    {oa : StateT (QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) ProbComp α}
    {next : α → StateT (QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) ProbComp β}
    (h : SafeRecord D challenged oa) (hn : ∀ a, SafeRecord D challenged (next a)) :
    SafeRecord D challenged (oa >>= next) := by
  intro s hs r hr
  rw [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨v, hv, hr⟩ := hr
  exact hn v.1 v.2 (h s hs v hv) r hr

variable (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
  (hno : ¬KeyCollision x.2.1 x.2.2) (table : ProtectedSlot C → HashOutput)
  (D : Finset C.Party) (challenged : Finset Point)

abbrev SafeRo {α : Type} (oa : OracleComp (RoSpec C) α) : Prop :=
  SafeRecord D challenged (recordRo prims x b table oa)

theorem safe_pure {α : Type} (a : α) : SafeRo prims x b table D challenged (pure a) := by
  rw [SafeRo, MonadHom.mmap_pure]
  exact SafeRecord.pure D challenged a

theorem safe_bind {α β : Type} (oa : OracleComp (RoSpec C) α) (next : α → OracleComp (RoSpec C) β)
    (h : SafeRo prims x b table D challenged oa)
    (hn : ∀ a, SafeRo prims x b table D challenged (next a)) :
    SafeRo prims x b table D challenged (oa >>= next) := by
  rw [SafeRo, MonadHom.mmap_bind]
  exact h.bind hn

theorem safe_map {α β : Type} (f : α → β) (oa : OracleComp (RoSpec C) α)
    (h : SafeRo prims x b table D challenged oa) : SafeRo prims x b table D challenged (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact safe_bind prims x b table D challenged _ _ h (fun _ => safe_pure prims x b table D challenged _)

theorem safe_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (items : List α)
    (h : ∀ a ∈ items, SafeRo prims x b table D challenged (f a)) :
    SafeRo prims x b table D challenged (items.mapM f) := by
  induction items with
  | nil => exact safe_pure prims x b table D challenged []
  | cons a rest ih =>
    rw [List.mapM_cons]
    apply safe_bind prims x b table D challenged _ _ (h a (by simp))
    intro value
    apply safe_bind prims x b table D challenged _ _ (ih (fun a ha => h a (by simp [ha])))
    intro tail
    exact safe_pure prims x b table D challenged _

set_option backward.isDefEq.respectTransparency false in
include hno in
theorem safe_hash (u : Query C)
    (hu : ∀ slot, slotInput x.2.1 x.2.2 slot = u → ReadAllowed D challenged slot) :
    SafeRo prims x b table D challenged (hashQuery u) := by
  intro s hs r hr
  change r ∈ support ((simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
    (simulateQ (protectedLocal prims x b)
      (query (spec := LocalSpec C) (.inr (.inl u))))).run s) at hr
  simp only [HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, protectedLocal] at hr
  apply ProtectedRouting.eager_route_preserves (protectedInput x b) (protectedInput_injective x b hno)
    table (ProtectedAllowed D challenged) u ?_ s hs r hr
  rintro (slot | cell) he
  · exact hu slot he
  · trivial

include hno in
theorem safe_prf (seed : HashOutput) (p : Point) (hp : p ∉ challenged) :
    SafeRo prims x b table D challenged (prf seed p) := by
  apply safe_map
  apply safe_hash prims x b hno table D challenged
  rintro (⟨T, p'⟩ | mask) he
  · have he' := (Query.prf.inj he).2
    subst p'
    exact Or.inr hp
  · cases he

include hno in
theorem safe_prfValue (seeds : C.Term → HashOutput) (p : Point) (hp : p ∉ challenged) :
    SafeRo prims x b table D challenged (prfValue seeds p) := by
  unfold prfValue
  apply safe_bind prims x b table D challenged
  · exact safe_mapM prims x b table D challenged _ _
      (fun T _ => safe_prf prims x b hno table D challenged (seeds T) p hp)
  · intro values
    exact safe_pure prims x b table D challenged _

include hno in
theorem safe_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    SafeRo prims x b table D challenged (tweakable oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [ThresholdLeanXmssSecurity.tweakable_pure]
    exact safe_pure prims x b table D challenged a
  | query_bind input next ih =>
    rw [ThresholdLeanXmssSecurity.tweakable_bind]
    apply safe_bind prims x b table D challenged _ _ ?_ ih
    change SafeRo prims x b table D challenged (hashQuery (.hash input))
    exact safe_hash prims x b hno table D challenged _ fun slot he =>
      (slotInput_ne_hash x.2.1 x.2.2 slot input he).elim

include hno in
theorem safe_eval (keys : Keys C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) (hp : p ∉ challenged) :
    SafeRo prims x b table D challenged (eval keys i J p message) := by
  unfold eval
  apply safe_bind prims x b table D challenged
  · exact safe_mapM prims x b table D challenged _ _
      (fun T _ => safe_prf prims x b hno table D challenged (keys.seed T) p hp)
  · intro terms
    apply safe_bind prims x b table D challenged
    · apply safe_mapM prims x b table D challenged
      intro j _
      apply safe_map
      apply safe_hash prims x b hno table D challenged
      rintro (⟨T, p'⟩ | mask) he
      · cases he
      · trivial
    · intro masks
      exact safe_pure prims x b table D challenged _

include hno in
theorem safe_referenceJob (seeds : C.Term → HashOutput) (P : PublicParameter) (job : Job)
    (hp : ∀ p ∈ job.points, p ∉ challenged) :
    SafeRo prims x b table D challenged (referenceJob tweakable (prfValue seeds) P job) := by
  rcases job with ⟨kind, points⟩
  unfold referenceJob
  apply safe_bind prims x b table D challenged
  · exact safe_mapM prims x b table D challenged _ _
      (fun p hmem => safe_prfValue prims x b hno table D challenged seeds p (hp p hmem))
  · intro values
    cases kind with
    | chainEnd e l | chainValue e l digit =>
      exact safe_map prims x b table D challenged _ _ (safe_tweakable prims x b hno table D challenged _)
    | chainRow e l =>
      apply safe_bind prims x b table D challenged _ _ (safe_tweakable prims x b hno table D challenged _)
      intro y₁
      apply safe_bind prims x b table D challenged _ _ (safe_tweakable prims x b hno table D challenged _)
      intro y₂
      apply safe_bind prims x b table D challenged _ _ (safe_tweakable prims x b hno table D challenged _)
      intro y₃
      exact safe_pure prims x b table D challenged _
    | commitment e =>
      exact safe_map prims x b table D challenged _ _ (safe_tweakable prims x b hno table D challenged _)
    | randomizer => exact safe_pure prims x b table D challenged _

theorem shift_read (D : Finset C.Party) (challenged : Finset Point) (Tstar : C.Term)
    (hT : D ⊆ Tstar.1) (δ : Point → TprfCorrectnessProof.XorDigest) (ω : Slot C → HashOutput)
    (slot : Slot C) (h : ReadAllowed D challenged slot) :
    shiftTable [] D challenged Tstar δ ω slot = ω slot := by
  classical
  rcases slot with ⟨T, p⟩ | pair
  · change Revealed D (.inl T) ∨ p ∉ challenged at h
    have hno : ¬(T = Tstar ∧ p ∈ challenged) := by
      rintro ⟨rfl, hp⟩
      rcases h with h | h
      · obtain ⟨i, hi, hh⟩ := h
        simp only [Committee.holders, Finset.mem_compl] at hh
        exact hh (hT hi)
      · exact h hp
    simp [shiftTable, shiftOf, hno]
  · rcases pair with ⟨pair, p, message, J⟩
    simp [shiftTable, shiftOf, Shifted, recordQueriers]

theorem consistent_shift (D : Finset C.Party) (challenged : Finset Point) (Tstar : C.Term)
    (hT : D ⊆ Tstar.1) (reads : List (Slot C × HashOutput))
    (hreads : ∀ r ∈ reads, ReadAllowed D challenged r.1)
    {c c' : Point → TprfCorrectnessProof.XorDigest} {ω : Slot C → HashOutput}
    (h : TprfSecurityProof.Consistent [] reads challenged c ω) :
    TprfSecurityProof.Consistent [] reads challenged c'
      (shiftTable [] D challenged Tstar (fun p => c p + c' p) ω) := by
  refine ⟨by simp, fun r hr => ?_, fun p hp => ?_⟩
  · rw [shift_read D challenged Tstar hT _ _ _ (hreads r hr), h.2.1 r hr]
  · rw [prfSum_shiftTable _ _ hp, h.2.2 p hp, ← add_assoc, TprfSecurityProof.XorDigest.add_self, zero_add]

/-- Equal XOR fibers remain equal even after fixing every nonchallenged slot.
The unrevealed pivot may be selected from the final corruption set. -/
theorem card_consistent_eq (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (challenged : Finset Point) (reads : List (Slot C × HashOutput))
    (hreads : ∀ r ∈ reads, ReadAllowed D challenged r.1) (c c' : Point → TprfCorrectnessProof.XorDigest) :
    (Finset.univ.filter (TprfSecurityProof.Consistent [] reads challenged c)).card =
      (Finset.univ.filter (TprfSecurityProof.Consistent [] reads challenged c')).card := by
  classical
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq hD (by simp [Committee.n]; omega)
  let Tstar : C.Term := ⟨T, hT⟩
  refine Finset.card_nbij'
    (shiftTable [] D challenged Tstar (fun p => c p + c' p))
    (shiftTable [] D challenged Tstar (fun p => c p + c' p)) ?_ ?_
    (fun ω _ => shiftTable_shiftTable _ _) (fun ω _ => shiftTable_shiftTable _ _)
  · intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    exact consistent_shift D challenged Tstar hDT reads hreads hω
  · intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    have h := consistent_shift D challenged Tstar hDT reads hreads (c' := c) hω
    simpa only [add_comm] using h

/-- Fixing the unopened starts costs exactly one uniform digest per point,
even with arbitrary auxiliary data at nonchallenged slots. -/
theorem card_consistent_mul (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (challenged : Finset Point) (reads : List (Slot C × HashOutput))
    (hreads : ∀ r ∈ reads, ReadAllowed D challenged r.1)
    (c : Point → TprfCorrectnessProof.XorDigest) :
    (Finset.univ.filter (TprfSecurityProof.Consistent [] reads challenged c)).card *
        (2 ^ digestBits) ^ challenged.card =
      (Finset.univ.filter (TprfSecurityProof.Consistent [] reads ∅ c)).card := by
  letI : Fintype TprfCorrectnessProof.XorDigest := inferInstanceAs (Fintype Digest)
  letI : DecidableEq TprfCorrectnessProof.XorDigest := inferInstanceAs (DecidableEq Digest)
  let f : (Slot C → HashOutput) → (challenged → TprfCorrectnessProof.XorDigest) :=
    fun ω p => prfSum ω p.1
  rw [Finset.card_eq_sum_card_fiberwise (f := f)
    (s := Finset.univ.filter (TprfSecurityProof.Consistent [] reads ∅ c)) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ d : challenged → TprfCorrectnessProof.XorDigest,
      ((Finset.univ.filter (TprfSecurityProof.Consistent [] reads ∅ c)).filter fun ω => f ω = d).card =
        (Finset.univ.filter (TprfSecurityProof.Consistent [] reads challenged c)).card := by
    intro d
    rw [card_consistent_eq D hD challenged reads hreads c
      (fun p => if h : p ∈ challenged then d ⟨p, h⟩ else 0), Finset.filter_filter]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro ω _
    simp only [TprfSecurityProof.Consistent, List.not_mem_nil, IsEmpty.forall_iff, implies_true, true_and,
      Finset.notMem_empty, and_true, f]
    apply and_congr_right
    intro _
    constructor
    · intro h p hp
      rw [dif_pos hp, ← h]
    · intro h
      funext p
      have he := h p.1 p.2
      rwa [dif_pos p.2] at he
  have hcard : Fintype.card TprfCorrectnessProof.XorDigest = 2 ^ digestBits := by
    change Fintype.card Digest = _
    simp
  rw [Finset.sum_congr rfl fun d _ => hfiber d, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_fun, Fintype.card_coe, hcard, mul_comm]

theorem probability_consistent_mul (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (challenged : Finset Point) (reads : List (Slot C × HashOutput))
    (hreads : ∀ r ∈ reads, ReadAllowed D challenged r.1)
    (c : Point → TprfCorrectnessProof.XorDigest) :
    Pr[TprfSecurityProof.Consistent [] reads challenged c | $ᵗ (Slot C → HashOutput)] *
        (2 ^ digestBits : ℝ≥0∞) ^ challenged.card =
      Pr[TprfSecurityProof.Consistent [] reads ∅ c | $ᵗ (Slot C → HashOutput)] := by
  rw [probEvent_uniformSample, probEvent_uniformSample, div_eq_mul_inv, div_eq_mul_inv,
    mul_right_comm]
  have h := card_consistent_mul D hD challenged reads hreads c
  have hcast := congrArg (fun n : ℕ => (n : ℝ≥0∞)) h
  push_cast at hcast
  rw [hcast]

/-- The protected starts of one top key, one independent digest per chain. -/
def topStarts (b : XmssSecurity.TopIndex) : Finset Point :=
  Finset.univ.image fun l : ChainIndex => Point.chain topLayer (topKey b) l (digit 0)

theorem topStarts_card (b : XmssSecurity.TopIndex) : (topStarts b).card = 58 := by
  rw [topStarts, Finset.card_image_of_injective]
  · simp [numChains]
  · intro l k h
    exact (Point.chain.inj h).2.2.1

/-- All 58 protected starts have equal fibers at fixed allowed slot-read constraints.
This statement retains the view's mass, including inconsistent views of mass zero. -/
theorem topStarts_probability (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (b : XmssSecurity.TopIndex) (reads : List (Slot C × HashOutput))
    (hreads : ∀ r ∈ reads, ReadAllowed D (topStarts b) r.1)
    (c : Point → TprfCorrectnessProof.XorDigest) :
    Pr[TprfSecurityProof.Consistent [] reads (topStarts b) c | $ᵗ (Slot C → HashOutput)] *
        (2 ^ 128 : ℝ≥0∞) ^ 58 =
      Pr[TprfSecurityProof.Consistent [] reads ∅ c | $ᵗ (Slot C → HashOutput)] := by
  simpa only [topStarts_card, digestBits] using
    probability_consistent_mul D hD (topStarts b) reads hreads c

theorem topStarts_randomizer (b : XmssSecurity.TopIndex) (lay : Layer) (e : KeyIndex) :
    Point.randomizer lay e ∉ topStarts b := by
  simp [topStarts]

theorem topStarts_bottom (b : XmssSecurity.TopIndex) (e : KeyIndex) (l : ChainIndex) (d : Digit) :
    Point.chain bottomLayer e l d ∉ topStarts b := by
  simp [topStarts, topLayer, bottomLayer]

theorem topStarts_other (b b' : XmssSecurity.TopIndex) (hne : b' ≠ b)
    (l : ChainIndex) (d : Digit) : Point.chain topLayer (topKey b') l d ∉ topStarts b := by
  intro h
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  apply hne
  exact Fin.ext (congrArg (fun e : KeyIndex => e.val) (Point.chain.inj hk).2.1.symm)

/-- Bottom ceremony jobs contain no protected top-chain start. -/
theorem bottomJobs_avoid (b b' : XmssSecurity.TopIndex) (job : Job)
    (hj : job ∈ bottomJobs b') (p : Point) (hp : p ∈ job.points) : p ∉ topStarts b := by
  simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with ((⟨k, _, l, _, rfl⟩ | ⟨k, _, rfl⟩) | rfl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact topStarts_bottom b _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    exact topStarts_randomizer b _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    exact topStarts_randomizer b _ _

theorem signJobs_avoid (b b' : XmssSecurity.TopIndex) (hne : b' ≠ b)
    (encoding : Encoding) (job : Job) (hj : job ∈ signJobs b' encoding)
    (p : Point) (hp : p ∈ job.points) : p ∉ topStarts b := by
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst p
  exact topStarts_other b b' hne _ _

include hno in
theorem safe_referenceBottom (seeds : C.Term → HashOutput) (P : PublicParameter)
    (top : TopTree) (b' : XmssSecurity.TopIndex) (hne : b' ≠ b) :
    SafeRo prims x b table D (topStarts b) (referenceTree tweakable (prfValue seeds) P top (.bottom b')) := by
  simp only [referenceTree, ceremonyOutput, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def]
  apply safe_bind prims x b table D (topStarts b)
  · exact safe_mapM prims x b table D (topStarts b) _ _ fun job hj =>
      safe_referenceJob prims x b hno table D (topStarts b) seeds P job
        (fun p hp => bottomJobs_avoid b b' job hj p hp)
  · intro outputs
    apply safe_bind prims x b table D (topStarts b) _ _
      (safe_tweakable prims x b hno table D (topStarts b) _)
    intro root
    apply safe_bind prims x b table D (topStarts b) _ _
      (safe_tweakable prims x b hno table D (topStarts b) _)
    intro base
    apply safe_bind prims x b table D (topStarts b) _ _
      (safe_tweakable prims x b hno table D (topStarts b) _)
    rintro (_ | ⟨randomness, encoding⟩)
    · exact safe_pure prims x b table D (topStarts b) _
    · apply safe_bind prims x b table D (topStarts b)
      · exact safe_mapM prims x b table D (topStarts b) _ _ fun job hj =>
          safe_referenceJob prims x b hno table D (topStarts b) seeds P job
            (fun p hp => signJobs_avoid b b' hne encoding job hj p hp)
      · intro values
        apply safe_bind prims x b table D (topStarts b) _ _
          (safe_tweakable prims x b hno table D (topStarts b) _)
        intro path
        apply safe_bind prims x b table D (topStarts b) _ _
          (safe_tweakable prims x b hno table D (topStarts b) _)
        intro topRoot
        split_ifs <;> exact safe_pure prims x b table D (topStarts b) _

theorem safe_sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α),
    (∀ i, SafeRo prims x b table D challenged (f i)) →
    SafeRo prims x b table D challenged (Concrete.sequenceFin f)
  | 0, f, h => safe_pure prims x b table D challenged _
  | n + 1, f, h => by
    unfold Concrete.sequenceFin
    apply safe_bind prims x b table D challenged _ _ (h 0)
    intro first
    apply safe_bind prims x b table D challenged _ _
      (safe_sequenceFin (fun i => f i.succ) (fun i => h i.succ))
    intro rest
    exact safe_pure prims x b table D challenged _

include hno in
theorem safe_signRound2 (keys : Keys C) (i : C.Party) (J : C.Quorum) (P : PublicParameter)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    SafeRo prims x b table D (topStarts b)
      (signRound2With (fun oa => oa) (fun p => eval keys i J p message) P J commitment e message parts) := by
  unfold signRound2With
  apply safe_bind prims x b table D (topStarts b) _ _
    (safe_tweakable prims x b hno table D (topStarts b) _)
  rintro (_ | ⟨randomness, encoding⟩)
  · exact safe_pure prims x b table D (topStarts b) _
  · apply safe_bind prims x b table D (topStarts b)
    · apply safe_sequenceFin prims x b table D (topStarts b)
      intro l
      split_ifs
      · exact safe_map prims x b table D (topStarts b) _ _
          (safe_eval prims x b hno table D (topStarts b) keys i J _ message (topStarts_bottom b _ _ _))
      · exact safe_pure prims x b table D (topStarts b) _
    · intro values
      exact safe_pure prims x b table D (topStarts b) _

private theorem run_liftM_ro {σ α : Type} (oa : OracleComp (RoSpec C) α) (st : σ) :
    (liftM oa : StateT σ (OracleComp (RoSpec C)) α).run st = (fun a => (a, st)) <$> oa := rfl

private theorem apply_liftM_ro {σ α : Type} (oa : OracleComp (RoSpec C) α) (st : σ) :
    (liftM oa : StateT σ (OracleComp (RoSpec C)) α) st = (fun a => (a, st)) <$> oa := rfl

private theorem apply_pure_ro {σ α : Type} (a : α) (st : σ) :
    (pure a : StateT σ (OracleComp (RoSpec C)) α) st = pure (a, st) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
include hno in
theorem safe_tsigOracles_nonopening (top : TopTree) (q : (TsigSpec C).Domain)
    (st : TsigState C) (hclosed : ¬Opens b st (.inr q)) :
    SafeRo prims x b table D (topStarts b)
      ((tsigOracles (fun oa => oa)
        (dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1)) q).run st) := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    all_goals first
      | exact safe_pure prims x b table D (topStarts b) _
      | (simp only [StateT.run_pure, StateT.run_set, pure_bind, apply_pure_ro]
         exact safe_pure prims x b table D (topStarts b) _)
  | tree b' =>
    have hne : b' ≠ b := hclosed
    simp only [tsigOracles, StateT.run_bind, run_liftM_ro, apply_liftM_ro, bind_map_left,
      Function.comp_def, StateT.run_pure, dealtWith, bind_assoc, pure_bind]
    apply safe_bind prims x b table D (topStarts b) _ _
      (safe_referenceBottom prims x b hno table D x.2.1 x.1 top b' hne)
    rintro (_ | (otherTop | tree))
    · exact safe_pure prims x b table D (topStarts b) _
    · exact safe_pure prims x b table D (topStarts b) _
    · simp only [StateT.run_bind, run_liftM_ro, apply_liftM_ro, bind_map_left, Function.comp_def, StateT.run_pure]
      apply safe_bind prims x b table D (topStarts b) _ _
        (safe_prfValue prims x b hno table D (topStarts b) x.2.1 _ (topStarts_randomizer b _ _))
      intro value
      exact safe_pure prims x b table D (topStarts b) _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact safe_pure prims x b table D (topStarts b) _
    · simp only [StateT.run_set, pure_bind, StateT.run_map, run_liftM_ro, apply_liftM_ro, dealtWith,
        Functor.map_map, Function.comp_def]
      apply safe_map
      apply safe_map
      exact safe_eval prims x b hno table D (topStarts b) _ i J _ message (topStarts_randomizer b _ _)
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hguard
    · exact safe_pure prims x b table D (topStarts b) _
    · have hne : treeOf e ≠ b := fun he => hclosed ⟨he, hguard⟩
      simp only [StateT.run_bind, run_liftM_ro, apply_liftM_ro, bind_map_left, Function.comp_def,
        StateT.run_pure, dealtWith, bind_assoc, pure_bind]
      apply safe_bind prims x b table D (topStarts b) _ _
        (safe_referenceBottom prims x b hno table D x.2.1 x.1 top (treeOf e) hne)
      rintro (_ | (otherTop | tree))
      · exact safe_pure prims x b table D (topStarts b) _
      · exact safe_pure prims x b table D (topStarts b) _
      · simp only [StateT.run_bind, run_liftM_ro, apply_liftM_ro, bind_map_left, Function.comp_def, StateT.run_pure]
        apply safe_bind prims x b table D (topStarts b) _ _
          (safe_eval prims x b hno table D (topStarts b) _ i J _ message (topStarts_randomizer b _ _))
        intro own
        apply safe_bind prims x b table D (topStarts b) _ _
          (safe_signRound2 prims x b hno table D _ i J x.1 _ e message _)
        rintro (_ | values)
        · exact safe_pure prims x b table D (topStarts b) _
        · simp only [StateT.run_set, pure_bind]
          exact safe_pure prims x b table D (topStarts b) _

/-- Corruption accounting is independent of the underlying oracle state. -/
theorem tsigOracles_corrupt_cases_general {σ : Type} (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → StateT σ ProbComp α)
    (dealt : Dealt C (StateT σ ProbComp)) (q : (TsigSpec C).Domain) (st : TsigState C) (c : σ) :
    ∀ z ∈ support (((tsigOracles lift dealt q).run st).run c), z.1.2.corrupt = st.corrupt ∨ ∃ i, q = .corrupt i ∧ ¬(C.t - 1 < (insert i st.corrupt).card) ∧
        z.1.2.corrupt = insert i st.corrupt := by
  intro z hz
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp at hz; subst hz; exact Or.inl rfl
    · simp at hz; subst hz; exact Or.inr ⟨i, rfl, ‹_›, rfl⟩
  · simp only [tsigOracles, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
      mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rcases w with ⟨_ | tree, c'⟩
    · simp at hz; subst hz; exact Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        mem_support_bind_iff, StateT.run_pure] at hz
      obtain ⟨w, -, hz⟩ := hz
      simp at hz; subst hz; exact Or.inl rfl
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp at hz; subst hz; exact Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self, pure_bind,
        mem_support_bind_iff, StateT.run_map, support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨a, -, hw⟩ := hw
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact Or.inl rfl
  · simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz
    · simp at hz; subst hz; exact Or.inl rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨w, -, hz⟩ := hz
      rcases w with ⟨_ | tree, c'⟩
      · simp at hz; subst hz; exact Or.inl rfl
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          mem_support_bind_iff] at hz
        obtain ⟨w, -, w', -, hz⟩ := hz
        rcases w' with ⟨_ | values, c''⟩
        · simp at hz; subst hz; exact Or.inl rfl
        · simp at hz; subst hz; exact Or.inl rfl


/-- Interpret the program-free world in the finite protected view. The
programming branch is irrelevant to the actual signing computation. -/
def recordWorld : QueryImpl (WorldSpec C)
    (StateT (QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) ProbComp)
  | .inl (.inl t) | .inr t =>
      simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (protectedLocal prims x b t)
  | .inl (.inr _) => pure false

set_option backward.isDefEq.respectTransparency false in
theorem recordWorld_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (recordWorld prims x b table) (free oa) =
      simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [free, simulateQ_pure]
  | query_bind t k ih =>
    simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map] at ih ⊢
    simp only [HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, recordWorld]
    congr 1
    funext u
    exact ih u

theorem recordWorld_liftFree {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (recordWorld prims x b table) (SigningSecurityProof.liftFree oa) =
      recordRo prims x b table oa := recordWorld_free prims x b table _

set_option backward.isDefEq.respectTransparency false in
theorem recordWorld_adversary_query (t : (LocalSpec C).Domain) :
    simulateQ (recordWorld prims x b table)
      (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) =
      simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (protectedLocal prims x b t) := by
  exact SeedHitProof.simulateQ_adversary_query (recordWorld prims x b table) t

theorem recordWorld_localize {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hfree : ProgramFree oa) :
    simulateQ (recordWorld prims x b table) oa =
      simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b) (simulateQ worldLocalize oa)) := by
  rw [← QueryImpl.simulateQ_compose]
  exact programFree_simulate_local _ _ (fun _ => rfl) (fun _ => rfl) oa hfree

/-- The joint invariant needed for the posterior argument, only on branches
whose actual hidden-key flag remains clear. -/
def ViewInvariant (b : XmssSecurity.TopIndex) (p : TsigState C × Bool)
    (record : QueryCache (ProtectedSlot C →ₒ HashOutput)) : Prop :=
  p.1.corrupt.card ≤ C.t - 1 ∧ (p.2 = false → RecordAllowed p.1.corrupt (topStarts b) record)

set_option backward.isDefEq.respectTransparency false in
include hno in
theorem flaggedOracles_view (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain)
    (p : TsigState C × Bool) (hclosed : ¬Opens b p.1 t)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C)
    (hs : ViewInvariant b p s.1) :
    ∀ r ∈ support ((simulateQ (recordWorld prims x b table)
      ((SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p)).run s),
      ViewInvariant b r.1.2 r.2.1 := by
  rcases t with t | q
  · intro r hr
    simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, simulateQ_map,
      recordWorld_adversary_query, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [recordWorld_adversary_query] at hv
    refine ⟨hs.1, ?_⟩
    intro hflag
    have hf := Bool.or_eq_false_iff.mp hflag
    exact protectedLocal_preserves prims x b hno table p.1.corrupt (topStarts b) t hf.2 s
      (hs.2 hf.1) v hv
  · intro r hr
    simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, actualDealt,
      tsigOracles_free, simulateQ_map, recordWorld_liftFree, StateT.run_map,
      support_map, Set.mem_image] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    have he := SeedHitProof.hom_tsigOracles (recordRo prims x b table) (fun oa => oa)
      (dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1)) q p.1
    have hc := (congrArg (fun action => v ∈ support (action.run s)) he).mp hv
    have hcases := tsigOracles_corrupt_cases_general _ _ q p.1 s v hc
    have hmono : p.1.corrupt ⊆ v.1.2.corrupt := by
      rcases hcases with he | ⟨i, _, _, he⟩
      · rw [he]
      · rw [he]; exact Finset.subset_insert _ _
    have hcard : v.1.2.corrupt.card ≤ C.t - 1 := by
      rcases hcases with he | ⟨i, _, hi, he⟩
      · simpa only [he] using hs.1
      · rw [he]; omega
    refine ⟨hcard, fun hflag => ?_⟩
    exact (safe_tsigOracles_nonopening prims x b hno table p.1.corrupt top q p.1 hclosed
      s (hs.2 hflag) v hv).mono hmono

set_option maxRecDepth 100000 in
set_option backward.isDefEq.respectTransparency false in
include hno in
/-- The actual stopped adversary, including adaptive corruptions and all
honest handler computations, preserves the posterior's allowed-read cache. -/
theorem unopenedRun_view (top : TopTree) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ (p : TsigState C × Bool) (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C),
      ViewInvariant b p s.1 → ∀ r ∈ support
        ((simulateQ (recordWorld prims x b table) (unopenedRun x top b oa p)).run s),
      ∀ v, r.1 = some v → ViewInvariant b v.2 r.2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro p s hs r hr v he
    rw [show unopenedRun x top b (pure a) p = pure (some (a, p)) from rfl] at hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    cases he
    exact hs
  | query_bind t k ih =>
    intro p s hs r hr v he
    change r ∈ support ((simulateQ (recordWorld prims x b table)
      (unopenedRun x top b (OracleComp.queryBind t k) p)).run s) at hr
    rw [show unopenedRun x top b (OracleComp.queryBind t k) p =
      (if Opens b p.1 t then pure none else
        (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p >>= fun r =>
          unopenedRun x top b (k r.1) r.2) from rfl] at hr
    split_ifs at hr with hopen
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      cases he
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨w, hw, hr⟩ := hr
      exact ih w.1.1 w.1.2 w.2
        (flaggedOracles_view prims x b hno table top t p hopen s hs w hw) r hr v he


include hno in
/-- The same allowed-read invariant holds in the counted posterior
interpreter that is distributionally coupled to the actual signing run. -/
theorem unopenedRun_counted_view (top : TopTree) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (p : TsigState C × Bool)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ))
    (hs : ViewInvariant b p s.1) :
    ∀ r ∈ support ((simulateQ (FinitePosterior.eager table CountedPosterior.aux)
      (simulateQ (CountedPosterior.localQuery prims x b)
        (simulateQ worldLocalize (unopenedRun x top b oa p)))).run s),
      ∀ v, r.1 = some v → ViewInvariant b v.2 r.2.1 := by
  intro r hr v he
  have hmap := CountedPosterior.eager_forget_run prims x b table
    (simulateQ worldLocalize (unopenedRun x top b oa p)) s
  rw [← recordWorld_localize prims x b table _ (programFree_unopenedRun x top b oa p)] at hmap
  have hm : (r.1, r.2.1, r.2.2.1) ∈ support
      ((simulateQ (recordWorld prims x b table) (unopenedRun x top b oa p)).run (s.1, s.2.1)) := by
    rw [hmap, support_map]
    exact ⟨r, hr, rfl⟩
  exact unopenedRun_view prims x b hno table top oa p (s.1, s.2.1) hs _ hm v he

theorem shift_tableExtending (D : Finset C.Party) (challenged : Finset Point) (Tstar : C.Term)
    (hT : D ⊆ Tstar.1) (cache : SlotCache C)
    (hcache : ∀ slot, (cache slot).isSome → ReadAllowed D challenged slot)
    (δ : Point → TprfCorrectnessProof.XorDigest) (ω : Slot C → HashOutput) :
    shiftTable [] D challenged Tstar δ (tableExtending cache ω) =
      tableExtending cache (shiftTable [] D challenged Tstar δ ω) := by
  funext slot
  cases hc : cache slot with
  | none => simp only [shiftTable, tableExtending, hc, Option.getD_none]
  | some value =>
    rw [shift_read D challenged Tstar hT δ _ slot (hcache slot (by simp [hc]))]
    simp only [tableExtending, hc, Option.getD_some]

/-- The posterior of an allowed slot cache retains equal fibers for all
protected start vectors. This applies after adaptive observations. -/
theorem overlay_prf_fiber_eq (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (challenged : Finset Point) (cache : SlotCache C)
    (hcache : ∀ slot, (cache slot).isSome → ReadAllowed D challenged slot)
    (c c' : challenged → TprfCorrectnessProof.XorDigest) :
    (Finset.univ.filter fun ω : Slot C → HashOutput =>
      (fun p : challenged => prfSum (tableExtending cache ω) p.1) = c).card =
    (Finset.univ.filter fun ω : Slot C → HashOutput =>
      (fun p : challenged => prfSum (tableExtending cache ω) p.1) = c').card := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_superset_card_eq hD (by simp [Committee.n]; omega)
  let Tstar : C.Term := ⟨T, hcard⟩
  let δ : Point → TprfCorrectnessProof.XorDigest := fun p =>
    if hp : p ∈ challenged then c ⟨p, hp⟩ + c' ⟨p, hp⟩ else 0
  have hforward (u v : challenged → TprfCorrectnessProof.XorDigest)
      (hd : ∀ p : challenged, δ p.1 = u p + v p) (ω : Slot C → HashOutput)
      (hω : (fun p : challenged => prfSum (tableExtending cache ω) p.1) = u) :
      (fun p : challenged => prfSum (tableExtending cache (shiftTable [] D challenged Tstar δ ω)) p.1) = v := by
    funext p
    rw [← shift_tableExtending D challenged Tstar hT cache hcache δ ω,
      prfSum_shiftTable _ _ p.2, congrFun hω p, hd p]
    simp only [← add_assoc, TprfSecurityProof.XorDigest.add_self, zero_add]
  refine Finset.card_nbij' (shiftTable [] D challenged Tstar δ)
    (shiftTable [] D challenged Tstar δ) ?_ ?_
    (fun ω _ => shiftTable_shiftTable _ _) (fun ω _ => shiftTable_shiftTable _ _)
  · intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    exact hforward c c' (fun p => by simp [δ, p.2]) ω hω
  · intro ω hω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    exact hforward c' c (fun p => by simp [δ, p.2, add_comm]) ω hω

set_option backward.isDefEq.respectTransparency false in
theorem overlay_prf_probability (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (challenged : Finset Point) (cache : SlotCache C)
    (hcache : ∀ slot, (cache slot).isSome → ReadAllowed D challenged slot)
    (c : challenged → TprfCorrectnessProof.XorDigest) :
    Pr[fun ω => (fun p : challenged => prfSum (tableExtending cache ω) p.1) = c |
      $ᵗ (Slot C → HashOutput)] = ((2 ^ digestBits : ℝ≥0∞) ^ challenged.card)⁻¹ := by
  let f : (Slot C → HashOutput) → (challenged → TprfCorrectnessProof.XorDigest) :=
    fun ω p => prfSum (tableExtending cache ω) p.1
  have he (v : challenged → TprfCorrectnessProof.XorDigest) :
      Pr[= v | f <$> ($ᵗ (Slot C → HashOutput))] = Pr[= c | f <$> ($ᵗ (Slot C → HashOutput))] := by
    rw [probOutput_map, probOutput_map, probEvent_uniformSample, probEvent_uniformSample]
    dsimp only [f]
    apply congrArg (fun n : ℕ => (n : ℝ≥0∞) / Fintype.card (Slot C → HashOutput))
    have hcard := overlay_prf_fiber_eq D hD challenged cache hcache v c
    refine Eq.trans ?_ (Eq.trans hcard ?_)
    all_goals
      apply congrArg Finset.card
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  letI : Fintype TprfCorrectnessProof.XorDigest := inferInstanceAs (Fintype Digest)
  have hm := sum_probOutput_eq_one (mx := f <$> ($ᵗ (Slot C → HashOutput))) (by simp)
  rw [Finset.sum_congr rfl (fun v _ => he v), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fun, Fintype.card_coe] at hm
  have hc : Fintype.card TprfCorrectnessProof.XorDigest = 2 ^ digestBits := by
    change Fintype.card Digest = _
    simp
  rw [hc] at hm
  push_cast at hm
  rw [mul_comm] at hm
  have h := ENNReal.eq_inv_of_mul_eq_one_left hm
  simpa only [probOutput_map, f] using h

theorem topStarts_posterior_probability (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (b : XmssSecurity.TopIndex) (cache : SlotCache C)
    (hcache : ∀ slot, (cache slot).isSome → ReadAllowed D (topStarts b) slot)
    (c : topStarts b → TprfCorrectnessProof.XorDigest) :
    Pr[fun ω => (fun p : topStarts b => prfSum (tableExtending cache ω) p.1) = c |
      $ᵗ (Slot C → HashOutput)] = ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ := by
  simpa only [topStarts_card, digestBits] using
    overlay_prf_probability D hD (topStarts b) cache hcache c

/-- A job only depends on its declared PRF points. -/
theorem referenceJob_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (F G : Point → m Digest)
    (P : PublicParameter) (job : Job) (h : ∀ p ∈ job.points, F p = G p) :
    referenceJob lift F P job = referenceJob lift G P job := by
  unfold referenceJob
  rw [mapM_congr_mem h]

/-- An unrelated bottom ceremony does not depend on the protected start values
when its public top tree and hash implementation are held fixed. -/
theorem referenceBottom_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (F G : Point → m Digest)
    (P : PublicParameter) (top : TopTree) (b b' : XmssSecurity.TopIndex) (hne : b' ≠ b)
    (h : ∀ p, p ∉ topStarts b → F p = G p) :
    referenceTree lift F P top (.bottom b') = referenceTree lift G P top (.bottom b') := by
  have hbottom : (bottomJobs b').mapM (referenceJob lift F P) =
      (bottomJobs b').mapM (referenceJob lift G P) :=
    mapM_congr_mem (fun job hj => referenceJob_congr lift F G P job
      (fun p hp => h p (bottomJobs_avoid b b' job hj p hp)))
  have hsign : ∀ encoding, (signJobs b' encoding).mapM (referenceJob lift F P) =
      (signJobs b' encoding).mapM (referenceJob lift G P) := fun encoding =>
    mapM_congr_mem (fun job hj => referenceJob_congr lift F G P job
      (fun p hp => h p (signJobs_avoid b b' hne encoding job hj p hp)))
  simp only [referenceTree, ceremonyOutput, hbottom, hsign]

/-- Parts evaluated at unprotected points are unchanged by the same table
bijection, even when their quorum and evaluation context were chosen adaptively. -/
theorem evalSum_shift_unchallenged (D : Finset C.Party) (challenged : Finset Point)
    (Tstar : C.Term) (hT : D ⊆ Tstar.1) (δ : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → HashOutput) (i : C.Party) (J : C.Quorum) (p : Point) (message : Message)
    (hp : p ∉ challenged) :
    evalSum (shiftTable [] D challenged Tstar δ ω) i J p message = evalSum ω i J p message := by
  unfold evalSum
  congr 1
  · apply Finset.sum_congr rfl
    intro T _
    rw [shift_read D challenged Tstar hT δ ω (.inl (T, p)) (Or.inr hp)]
  · apply Finset.sum_congr rfl
    intro j _
    split
    · rfl
    · rw [shift_read D challenged Tstar hT δ ω _ (by trivial)]

end UnopenedPrivacy

namespace SelectedKeygen

def jobs (b : XmssSecurity.TopIndex) : List Job :=
  (List.finRange numChains).map fun l =>
    ⟨.chainEnd (topKey b) l, [.chain topLayer (topKey b) l (digit 0)]⟩

/-- The selected key's private jobs form one contiguous block in the actual
key-generation order. Neither surrounding block contains that key. -/
theorem split_jobs (b : XmssSecurity.TopIndex) :
    ∃ before after : List XmssSecurity.TopIndex,
      b ∉ before ∧ b ∉ after ∧ topJobs = before.flatMap jobs ++ jobs b ++ after.flatMap jobs := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp (List.mem_finRange b)
  have hn : (before ++ b :: after).Nodup := he ▸ List.nodup_finRange _
  refine ⟨before, after, ?_, ?_, ?_⟩
  · intro hb
    exact (List.nodup_append.mp hn).2.2 b hb b (by simp) rfl
  · exact (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  · change (List.finRange XmssSecurity.topLifetime).flatMap jobs = _
    rw [he, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem jobs_avoid (b b' : XmssSecurity.TopIndex) (hne : b' ≠ b)
    (job : Job) (hj : job ∈ jobs b') (p : Point) (hp : p ∈ job.points) :
    p ∉ UnopenedPrivacy.topStarts b := by
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst p
  exact UnopenedPrivacy.topStarts_other b b' hne _ _

/-- The full private domain of the selected top key, not merely its gate
cell: all threshold starts and every input at each of its chain addresses. -/
def selectedInput (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex) : Query C → Prop
  | .prf _ p => p ∈ UnopenedPrivacy.topStarts b
  | .hash input => ∃ l step value,
      input = XmssSecurity.Concrete.CacheView.topChainInput x.1 b l step value
  | _ => False

local instance (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex) :
    DecidablePred (selectedInput x b) := Classical.decPred _

theorem selectedInput_other (x : SigningSecurityProof.Keys3 C) (b b' : XmssSecurity.TopIndex)
    (hne : b' ≠ b) (l : XmssSecurity.ChainIndex) (step : XmssSecurity.ChainStep) (value : Digest) :
    ¬selectedInput x b (.hash (XmssSecurity.Concrete.CacheView.topChainInput x.1 b' l step value)) := by
  rintro ⟨l', step', value', he⟩
  have hd := XmssSecurity.domain_eq_of_tweakableHashInput_eq x.1 he
  exact hne (XmssSecurity.HashDomain.topChain.inj hd).1

theorem value_avoids (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (p : Point) (hp : p ∉ UnopenedPrivacy.topStarts b) :
    (forestValue x.2.1 p).IsQueryBoundP (selectedInput x b) 0 := by
  unfold forestValue
  apply isQueryBoundP_bind (m := 0)
  · apply mapM_bound_zero
    intro T
    simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, selectedInput]
    exact fun h => (hp h).elim
  · intro _ _
    simp

set_option backward.isDefEq.respectTransparency false in
theorem chainWalk_avoids (x : SigningSecurityProof.Keys3 C) (b b' : XmssSecurity.TopIndex)
    (hne : b' ≠ b) (l : ChainIndex) (pos n : ℕ) (v : Digest) :
    (forestHash (C := C) (Concrete.chainWalk x.1 topLayer (topKey b') l pos n v)).IsQueryBoundP
      (selectedInput x b) 0 := by
  induction n with
  | zero => simp [Concrete.chainWalk, forestHash]
  | succ n ih =>
    rw [Concrete.chainWalk]
    simp only [forestHash, simulateQ_bind] at ih ⊢
    apply isQueryBoundP_bind (m := 0) ih
    intro value _
    split_ifs with hk
    · change pos + n < 3 at hk
      have hinput : tweakableHashInput x.1 (.chain topLayer (topKey b') ⟨pos + n, hk⟩)
          (Concrete.chainPayload l value) =
          XmssSecurity.Concrete.CacheView.topChainInput x.1 b' l ⟨pos + n, hk⟩ value := by
        erw [XmssSecurity.Bridge.topChain_input]
        rfl
      simp only [Concrete.tweakableHash, Concrete.oracleHash, simulateQ_bind, simulateQ_pure,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, hinput]
      apply isQueryBoundP_bind (m := 0)
      · simp only [HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, hinput]
        rw [isQueryBoundP_query_iff]
        exact fun h => (selectedInput_other x b b' hne l ⟨pos + n, hk⟩ value h).elim
      · intro _ _
        simp
    · simp only [simulateQ_pure, isQueryBoundP_pure]

theorem job_avoids (x : SigningSecurityProof.Keys3 C) (b b' : XmssSecurity.TopIndex)
    (hne : b' ≠ b) (job : Job) (hj : job ∈ jobs b') :
    (referenceJob forestHash (forestValue x.2.1) x.1 job).IsQueryBoundP (selectedInput x b) 0 := by
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hj
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, pure_bind, bind_assoc]
  apply isQueryBoundP_bind (m := 0)
    (value_avoids x b _ (UnopenedPrivacy.topStarts_other b b' hne l _))
  intro value _
  simp only [List.getD_cons_zero, isQueryBoundP_map_iff]
  exact chainWalk_avoids x b b' hne l 0 3 value

theorem mapM_avoids {α β : Type} (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (f : α → OracleComp (Query C →ₒ HashOutput) β) (items : List α)
    (h : ∀ a ∈ items, (f a).IsQueryBoundP (selectedInput x b) 0) :
    (items.mapM f).IsQueryBoundP (selectedInput x b) 0 := by
  induction items with
  | nil => simp
  | cons a rest ih =>
    rw [List.mapM_cons]
    apply isQueryBoundP_bind (m := 0) (h a (by simp))
    intro value _
    apply isQueryBoundP_bind (m := 0) (ih (fun a ha => h a (by simp [ha])))
    intro tail _
    simp

/-- Every job before the selected key avoids its entire private domain. -/
theorem before_jobs_avoid (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (before : List XmssSecurity.TopIndex) (hb : b ∉ before) :
    ((before.flatMap jobs).mapM (referenceJob forestHash (forestValue x.2.1) x.1)).IsQueryBoundP
      (selectedInput x b) 0 := by
  apply mapM_avoids
  intro job hj
  obtain ⟨b', hb', hj⟩ := List.mem_flatMap.mp hj
  exact job_avoids x b b' (fun he => hb (he ▸ hb')) job hj

/-- A raw computation avoiding the selected domain preserves every absent
cell in that domain. No assumption on unrelated cached values is needed. -/
theorem run_avoids_fresh (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (hbound : oa.IsQueryBoundP (selectedInput x b) 0)
    (target : Query C) (htarget : selectedInput x b target)
    (cache : HashCache C) (hnone : cache target = none)
    (r : α × HashCache C)
    (hr : r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle oa).run cache)) :
    r.2 target = none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hnone
  | query_bind input next ih =>
    rw [isQueryBoundP_query_bind_iff] at hbound
    have hi : ¬selectedInput x b input := by simpa using hbound.1
    have hne : target ≠ input := fun he => hi (he ▸ htarget)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    have hmiddle : v.2 target = none := by
      cases hc : cache input with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hc, support_map] at hv
        obtain ⟨value, _, rfl⟩ := hv
        simpa only [QueryCache.cacheQuery_of_ne _ _ hne] using hnone
      | some value =>
        rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hv
        subst v
        exact hnone
    exact ih v.1 (by simpa [hi] using hbound.2 v.1) v.2 hmiddle r hr

set_option backward.isDefEq.respectTransparency false in
/-- The actual counted hash-only execution forgets to the same raw lazy
oracle. The count is retained in the source execution, not charged twice. -/
theorem hashEmbed_count_forget {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (cache : HashCache C) (n : ℕ) :
    (fun r => (r.1, r.2.1)) <$>
      (simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree (hashEmbed oa))).run (cache, n) =
      (simulateQ (Query C →ₒ HashOutput).randomOracle oa).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache n with
  | pure a => simp [SigningSecurityProof.liftFree, free, hashEmbed]
  | query_bind input next ih =>
    have he : hashEmbed (OracleComp.lift (OracleSpec.query input) >>= next) =
        hashQuery input >>= fun value => hashEmbed (next value) := by
      simp [hashEmbed, simulateQ_bind]
    rw [he, SigningSecurityProof.liftFree, liftComp_bind, free_bind]
    simp only [simulateQ_bind, StateT.run_bind, map_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hq : simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree (hashQuery input)) =
        SigningCacheProof.countImpl prims (.inr (.inr (.inl input))) := by
      rw [SigningSecurityProof.liftFree, hashQuery, free]
      erw [liftComp_query, simulateQ_query]
      simp
    rw [hq]
    change (do
      let r ← (fun z : HashOutput × HashCache C => (z.1, (z.2, n + 1))) <$>
        ((Query C →ₒ HashOutput).randomOracle input).run cache
      (fun z : α × HashCache C × ℕ => (z.1, z.2.1)) <$>
        (simulateQ (SigningCacheProof.countImpl prims)
          (SigningSecurityProof.liftFree (hashEmbed (next r.1)))).run r.2) = _
    rw [bind_map_left]
    exact bind_congr fun r => ih r.1 r.2 (n + 1)

/-- At the boundary preceding the selected block, the real counted cache
still has no selected PRF or structural input, provided they started absent. -/
theorem before_jobs_fresh (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (before : List XmssSecurity.TopIndex) (hb : b ∉ before)
    (initial : HashCache C × ℕ)
    (hfresh : ∀ target, selectedInput x b target → initial.1 target = none)
    (r : List (List Bit) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree ((before.flatMap jobs).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1)))).run initial)) :
    ∀ target, selectedInput x b target → r.2.1 target = none := by
  have he : hashEmbed ((before.flatMap jobs).mapM
      (referenceJob forestHash (forestValue x.2.1) x.1)) =
      (before.flatMap jobs).mapM (referenceJob tweakable (prfValue x.2.1) x.1) := by
    unfold hashEmbed
    rw [simulateQ_list_mapM]
    congr 1
    funext job
    exact hashEmbed_referenceJob x.2.1 x.1 job
  rw [← he] at hr
  have hm : (r.1, r.2.1) ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      ((before.flatMap jobs).mapM (referenceJob forestHash (forestValue x.2.1) x.1))).run initial.1) := by
    rw [← hashEmbed_count_forget prims _ initial.1 initial.2, support_map]
    exact ⟨r, hr, rfl⟩
  intro target ht
  exact run_avoids_fresh x b _ (before_jobs_avoid x b before hb) target ht initial.1
    (hfresh target ht) _ hm

open Classical in
def interpret (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput) :
    OracleComp (RoSpec C) →ᵐ StateT (HashCache C) ProbComp where
  toFun _ oa := simulateQ (ProtectedRouting.unrecorded table)
    (simulateQ (protectedLocal prims x b) (liftComp oa (LocalSpec C)))
  toFun_pure' a := by simp only [liftComp_pure, simulateQ_pure]
  toFun_bind' oa f := by simp only [liftComp_bind, simulateQ_bind]

set_option backward.isDefEq.respectTransparency false in
theorem interpret_hash (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (slot : ProtectedSlot C) :
    interpret prims x b table (hashQuery (protectedInput x b slot)) = pure (table slot) := by
  classical
  change simulateQ (ProtectedRouting.unrecorded table)
    (simulateQ (protectedLocal prims x b) (liftComp (hashQuery (protectedInput x b slot)) (LocalSpec C))) = _
  change simulateQ (ProtectedRouting.unrecorded table)
    (simulateQ (protectedLocal prims x b)
      (query (spec := LocalSpec C) (.inr (.inl (protectedInput x b slot))))) = _
  simp only [HasQuery.instOfMonadLift_query, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map, protectedLocal]
  exact ProtectedRouting.unrecorded_in (protectedInput x b) (protectedInput_injective x b hno) table slot

theorem interpret_prfValue (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (p : Point) :
    interpret prims x b table (prfValue x.2.1 p) =
      pure (((C.terms.map fun T => truncateHash (table (.inl (.inl (T, p)))))).foldl (· ^^^ ·) 0) := by
  rw [prfValue, MonadHom.mmap_bind, SeedHitProof.hom_mapM]
  have hprf (T : C.Term) : interpret prims x b table (prf (x.2.1 T) p) =
      pure (truncateHash (table (.inl (.inl (T, p))))) := by
    rw [prf, SeedHitProof.hom_map]
    rw [show Query.prf (x.2.1 T) p = protectedInput x b (.inl (.inl (T, p))) from rfl,
      interpret_hash prims x b hno, map_pure]
  simp only [hprf, List.mapM_pure, pure_bind, MonadHom.mmap_pure]

def step (table : ProtectedSlot C → HashOutput) (l : XmssSecurity.ChainIndex)
    (k : ℕ) (v : Digest) : Digest :=
  if hk : k < 3 then truncateHash (table (.inr (l, ⟨k, hk⟩, v))) else 0

set_option backward.isDefEq.respectTransparency false in
theorem interpret_chainWalk (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (l : ChainIndex) (pos n : ℕ) (v : Digest) :
    interpret prims x b table (tweakable (Concrete.chainWalk x.1 topLayer (topKey b) l pos n v)) =
      pure (XmssSecurity.Wots.walk (step table l) pos n v) := by
  induction n with
  | zero => simp only [Concrete.chainWalk, ThresholdLeanXmssSecurity.tweakable_pure, MonadHom.mmap_pure,
      XmssSecurity.Wots.walk]
  | succ n ih =>
    rw [Concrete.chainWalk, ThresholdLeanXmssSecurity.tweakable_bind, MonadHom.mmap_bind, ih]
    simp only [pure_bind]
    split_ifs with hk
    · change pos + n < 3 at hk
      have hinput (value : Digest) :
          Query.hash (tweakableHashInput x.1 (.chain topLayer (topKey b) ⟨pos + n, hk⟩)
            (Concrete.chainPayload l value)) = protectedInput x b (.inr (l, ⟨pos + n, hk⟩, value)) := by
        erw [XmssSecurity.Bridge.topChain_input]
        rfl
      simp only [Concrete.tweakableHash, ThresholdLeanXmssSecurity.tweakable_bind,
        ThresholdLeanXmssSecurity.tweakable_oracleHash, MonadHom.mmap_bind, hinput,
        interpret_hash prims x b hno, pure_bind, ThresholdLeanXmssSecurity.tweakable_pure, MonadHom.mmap_pure]
      simp only [XmssSecurity.Wots.walk, step, dif_pos hk]
    · change ¬pos + n < 3 at hk
      simp only [ThresholdLeanXmssSecurity.tweakable_pure, MonadHom.mmap_pure]
      simp only [XmssSecurity.Wots.walk, step, dif_neg hk]

def starts (table : ProtectedSlot C → HashOutput) (b : XmssSecurity.TopIndex) (l : ChainIndex) : Digest :=
  (C.terms.map fun T => truncateHash
    (table (.inl (.inl (T, .chain topLayer (topKey b) l (digit 0)))))).foldl (· ^^^ ·) 0

def endpoints (table : ProtectedSlot C → HashOutput) (b : XmssSecurity.TopIndex) (l : ChainIndex) : Digest :=
  XmssSecurity.Wots.walk (step table l) 0 3 (starts table b l)

theorem starts_eq_prfSum (table : ProtectedSlot C → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    TprfCorrectnessProof.toXor (starts table b l) = TprfSecurityProof.prfSum (table ∘ Sum.inl)
      (.chain topLayer (topKey b) l (digit 0)) := by
  classical
  rw [starts, List.foldl_map, TprfCorrectnessProof.toXor_foldl _ _ _ terms_nodup]
  simp [Committee.terms, TprfSecurityProof.prfSum, TprfCorrectnessProof.toXor, Function.comp_def]
  rfl

theorem interpret_job (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (l : ChainIndex) :
    interpret prims x b table (referenceJob tweakable (prfValue x.2.1) x.1
      ⟨.chainEnd (topKey b) l, [.chain topLayer (topKey b) l (digit 0)]⟩) =
      pure (bitsOfDigest (endpoints table b l)) := by
  rw [SeedHitProof.hom_referenceJob]
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, interpret_prfValue prims x b hno,
    pure_bind, List.getD_cons_zero, SeedHitProof.hom_map, interpret_chainWalk prims x b hno, map_pure]
  rfl

/-- All 58 selected jobs are deterministic under the latent table and leave
the auxiliary cache unchanged. Only the endpoint bit lists reach the continuation. -/
theorem interpret_jobs (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) :
    interpret prims x b table ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) =
      pure ((List.finRange numChains).map fun l => bitsOfDigest (endpoints table b l)) := by
  rw [SeedHitProof.hom_mapM]
  simp only [jobs, List.mapM_map, Function.comp_def, interpret_job prims x b hno, List.mapM_pure]

set_option backward.isDefEq.respectTransparency false in
/-- The actual selected key-generation block can be replaced by its endpoint
vector before an arbitrary local continuation, after hiding its private record. -/
theorem skip_jobs (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) {α : Type}
    (next : List (List Bit) → OracleComp (LocalSpec C) α)
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) :
    Prod.map id Prod.snd <$>
      (simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b) (do
          let outputs ← liftComp ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)
          next outputs))).run s =
    Prod.map id Prod.snd <$>
      (simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b)
          (next ((List.finRange numChains).map fun l => bitsOfDigest (endpoints table b l))))).run s := by
  classical
  rw [ProtectedRouting.eager_forget_run, ProtectedRouting.eager_forget_run]
  simp only [simulateQ_bind]
  change ((interpret prims x b table ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1))) >>=
    fun outputs => simulateQ (ProtectedRouting.unrecorded table)
      (simulateQ (protectedLocal prims x b) (next outputs))).run s.2 = _
  rw [interpret_jobs prims x b hno, pure_bind]

/-- The public continuation of the top ceremony receives only the job
outputs. In particular the selected block exposes only its endpoint bits. -/
def finish {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (P : PublicParameter)
    (outputs : List (List Bit)) : m (Option TreeOutput) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange numChains).map fun l => (topKey b, l)
  let ends := fun (e : KeyIndex) (l : ChainIndex) => digestAt (outputs.getD (keys.idxOf (e, l)) []) 0
  let root ← lift (merkleNode P topLayer ends layerHeight 0)
  pure (some (.top ⟨ends, root⟩))

theorem referenceTree_split {m : Type → Type} [Monad m] [LawfulMonad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (F : Point → m Digest)
    (P : PublicParameter) (top : TopTree) (before after : List XmssSecurity.TopIndex)
    (b : XmssSecurity.TopIndex)
    (hsplit : topJobs = before.flatMap jobs ++ jobs b ++ after.flatMap jobs) :
    referenceTree lift F P top .top = (do
      let left ← (before.flatMap jobs).mapM (referenceJob lift F P)
      let selected ← (jobs b).mapM (referenceJob lift F P)
      let right ← (after.flatMap jobs).mapM (referenceJob lift F P)
      finish lift P (left ++ selected ++ right)) := by
  simp only [referenceTree, ceremonyOutput, hsplit, List.mapM_append,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, finish, List.append_assoc]

set_option maxRecDepth 100000 in
/-- The selected block starts at chain zero, using the same first term for
every key. The gate is before every selected private read. -/
theorem jobs_first (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (T : C.Term) (terms : List C.Term) (hterms : C.terms = T :: terms) :
    ∃ k, SigningSecurityProof.liftFree
      ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) =
      query (spec := WorldSpec C) (.inr (.inr (.inl (topGateInput x T b)))) >>= k := by
  have hchains : List.finRange numChains = (⟨0, by decide⟩ : ChainIndex) :: (List.finRange 57).map Fin.succ :=
    List.finRange_succ
  simp only [jobs, hchains, List.map_cons, List.mapM_cons, referenceJob, List.mapM_nil,
    prfValue, hterms, prf, bind_map_left, bind_assoc, pure_bind,
    SigningSecurityProof.liftFree, liftComp_bind, free_bind, liftComp_map]
  exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- Exact factorization of the actual final run at the first private read
of the selected key. The preceding block contains only other top keys. -/
theorem finalRun_gate_factor (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (T : C.Term) (terms : List C.Term)
    (hterms : C.terms = T :: terms) :
    ∃ before : List XmssSecurity.TopIndex, b ∉ before ∧
      ∃ next : List (List Bit) → HashOutput →
          OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)),
        SigningDescentProof.finalRun A x =
          SigningSecurityProof.liftFree ((before.flatMap jobs).mapM
            (referenceJob tweakable (prfValue x.2.1) x.1)) >>= fun left =>
            query (spec := WorldSpec C) (.inr (.inr (.inl (topGateInput x T b)))) >>= next left := by
  obtain ⟨before, after, hb, _, hsplit⟩ := split_jobs b
  obtain ⟨k, hk⟩ := jobs_first x b T terms hterms
  refine ⟨before, hb, ?_⟩
  unfold SigningDescentProof.finalRun
  dsimp only
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  rw [referenceTree_split tweakable (prfValue x.2.1) x.1 emptyTop before after b hsplit]
  simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind, bind_assoc] at hk ⊢
  rw [hk]
  simp only [bind_assoc]
  exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem hashEmbed_world {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α) :
    SigningSecurityProof.liftFree (hashEmbed oa) =
      simulateQ (fun input => query (spec := WorldSpec C) (.inr (.inr (.inl input)))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [hashEmbed, SigningSecurityProof.liftFree, free]
  | query_bind input next ih =>
    change (query (spec := WorldSpec C) (.inr (.inr (.inl input))) >>= fun value =>
      SigningSecurityProof.liftFree (hashEmbed (next value))) = _
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem hashEmbed_avoids_gate (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    {α : Type} (oa : OracleComp (Query C →ₒ HashOutput) α)
    (hbound : oa.IsQueryBoundP (selectedInput x b) 0)
    (target : Query C) (htarget : selectedInput x b target) :
    (SigningSecurityProof.liftFree (hashEmbed oa)).IsQueryBoundP
      (· = (.inr (.inr (.inl target)) : (WorldSpec C).Domain)) 0 := by
  letI : (WorldSpec C).IsUniformSpec := .ofFintypeInhabited _
  rw [hashEmbed_world]
  apply hbound.simulateQ_of_step
  · intro input _
    apply (isQueryBoundP_query_iff (spec := WorldSpec C)
      (fun t => t = .inr (.inr (.inl target))) (.inr (.inr (.inl input))) 1).mpr
    exact fun _ => Nat.zero_lt_one
  · intro input hi
    apply (isQueryBoundP_query_iff (spec := WorldSpec C)
      (fun t => t = .inr (.inr (.inl target))) (.inr (.inr (.inl input))) 0).mpr
    intro he
    have he' : input = target := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj he))
    subst input
    exact (hi htarget).elim

theorem hashEmbed_jobs (x : SigningSecurityProof.Keys3 C) (items : List Job) :
    hashEmbed (items.mapM (referenceJob forestHash (forestValue x.2.1) x.1)) =
      items.mapM (referenceJob tweakable (prfValue x.2.1) x.1) := by
  unfold hashEmbed
  rw [simulateQ_list_mapM]
  congr 1
  funext job
  exact hashEmbed_referenceJob x.2.1 x.1 job

set_option backward.isDefEq.respectTransparency false in
/-- Full selected-domain freshness at every supported matching first-gate
prefix of the actual final run. Arbitrary raw reachable states are not used. -/
theorem gate_prefix_fresh (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (T : C.Term) (terms : List C.Term)
    (hterms : C.terms = T :: terms) (n : ℕ) (s : LoggedState C)
    (k : HashOutput → OracleComp (WorldSpec C)
      ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)))
    (hp : (OracleComp.queryBind (.inr (.inr (.inl (topGateInput x T b)))) k, s) ∈
      support ((simulateQ (loggedImpl prims)
        (prefixRun (SigningDescentProof.finalRun A x) n)).run loggedInit))
    (hseen : ¬GateSeen (.inr (.inr (.inl (topGateInput x T b)))) s.2) :
    ∀ target, selectedInput x b target → s.1.1 target = none := by
  classical
  obtain ⟨before, hb, next, hfactor⟩ := finalRun_gate_factor A x b T terms hterms
  rw [hfactor] at hp
  have ht : selectedInput x b (topGateInput x T b) := by
    change Point.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0) ∈ UnopenedPrivacy.topStarts b
    exact Finset.mem_image.mpr ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩
  have havoid := hashEmbed_avoids_gate x b _ (before_jobs_avoid x b before hb)
    (topGateInput x T b) ht
  rw [hashEmbed_jobs] at havoid
  obtain ⟨left, hleft⟩ := first_gate_prefix prims _ _ next havoid n loggedInit s k hp hseen
  have hc : (left, s.1) ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree ((before.flatMap jobs).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1)))).run (∅, 0)) := by
    erw [← logged_forget prims _ loggedInit]
    rw [support_map]
    exact ⟨(left, s), hleft, rfl⟩
  exact before_jobs_fresh prims x b before hb (∅, 0) (fun _ _ => rfl) (left, s.1) hc

end SelectedKeygen

namespace PosteriorCompletion

open Classical

def startIndex (b : XmssSecurity.TopIndex) : ChainIndex ≃ UnopenedPrivacy.topStarts b :=
  Equiv.ofBijective (fun l => ⟨.chain topLayer (topKey b) l (digit 0),
    Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro l k h
        exact (Point.chain.inj (congrArg Subtype.val h)).2.2.1
      · rintro ⟨p, hp⟩
        obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
        exact ⟨l, rfl⟩)

def startVector (b : XmssSecurity.TopIndex) (slots : TprfSecurityProof.Slot C → HashOutput)
    (l : ChainIndex) : Digest :=
  TprfSecurityProof.prfSum slots (.chain topLayer (topKey b) l (digit 0))

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole start vector is uniform under every allowed posterior view. -/
theorem starts_uniform (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (b : XmssSecurity.TopIndex) (cache : TprfSecurityProof.SlotCache C)
    (hcache : ∀ slot, (cache slot).isSome →
      UnopenedPrivacy.ReadAllowed D (UnopenedPrivacy.topStarts b) slot) :
    𝒟[(fun slots => startVector b (tableExtending cache slots)) <$>
      ($ᵗ (TprfSecurityProof.Slot C → HashOutput))] = 𝒟[$ᵗ (ChainIndex → Digest)] := by
  apply evalDist_ext
  intro v
  rw [probOutput_map, probOutput_uniformSample]
  let target : UnopenedPrivacy.topStarts b → TprfCorrectnessProof.XorDigest :=
    fun p => v ((startIndex b).symm p)
  have he : (fun slots => startVector b (tableExtending cache slots) = v) =
      (fun slots => (fun p : UnopenedPrivacy.topStarts b =>
        TprfSecurityProof.prfSum (tableExtending cache slots) p.1) = target) := by
    funext slots
    apply propext
    constructor
    · intro h
      funext p
      have hv := congrFun h ((startIndex b).symm p)
      have hi := congrArg Subtype.val ((startIndex b).apply_symm_apply p)
      change Point.chain topLayer (topKey b) ((startIndex b).symm p) (digit 0) = p.1 at hi
      simpa only [startVector, hi, target] using hv
    · intro h
      funext l
      have hv := congrFun h (startIndex b l)
      change TprfSecurityProof.prfSum (tableExtending cache slots)
        (.chain topLayer (topKey b) l (digit 0)) = target (startIndex b l) at hv
      simpa only [target, Equiv.symm_apply_apply, startVector] using hv
  rw [he, UnopenedPrivacy.topStarts_posterior_probability D hD b cache hcache target]
  rw [Fintype.card_fun, show Fintype.card Digest = 2 ^ 128 by simp [digestBits],
    show Fintype.card ChainIndex = 58 from rfl, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]

theorem actual_starts (b : XmssSecurity.TopIndex) (table : ProtectedSlot C → HashOutput) :
    SelectedKeygen.starts table b = startVector b (table ∘ Sum.inl) := by
  funext l
  exact SelectedKeygen.starts_eq_prfSum table b l

set_option maxRecDepth 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- Retain the full chain tables jointly with the uniform private starts. -/
theorem joint_starts_chains (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (b : XmssSecurity.TopIndex) (cache : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (hcache : UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b) cache) :
    𝒟[(fun table => (SelectedKeygen.starts (tableExtending cache table) b,
      (ProtectedTable.split (tableExtending cache table)).2)) <$>
      ($ᵗ (ProtectedSlot C → HashOutput))] =
    𝒟[do
      let starts ← $ᵗ (ChainIndex → Digest)
      let chains ← $ᵗ (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput)
      pure (starts, fun l => tableExtending (ProtectedTable.chainCache cache l) (chains l))] := by
  let f : ProtectedTable.Parts C →
      (ChainIndex → Digest) × (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput) :=
    fun p => (startVector b p.1, p.2)
  have hm := congrArg (fun d : SPMF (ProtectedTable.Parts C) => f <$> d)
    (ProtectedTable.posterior_split cache)
  simp only [← evalDist_map, Functor.map_map, map_bind, map_pure] at hm
  rw [show (fun table => (SelectedKeygen.starts (tableExtending cache table) b,
      (ProtectedTable.split (tableExtending cache table)).2)) =
      (fun table => f (ProtectedTable.split (tableExtending cache table))) by
        funext table
        exact congrArg (fun s => (s, (ProtectedTable.split (tableExtending cache table)).2))
          (actual_starts b _), hm]
  have hu := starts_uniform D hD b (ProtectedTable.slotCache cache)
    (fun slot hs => hcache (.inl slot) hs)
  let next (starts : ChainIndex → Digest) : ProbComp _ := do
    let chains ← $ᵗ (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput)
    pure (starts, fun l => tableExtending (ProtectedTable.chainCache cache l) (chains l))
  change 𝒟[($ᵗ (TprfSecurityProof.Slot C → HashOutput)) >>=
    (fun slots => next (startVector b (tableExtending (ProtectedTable.slotCache cache) slots)))] = _
  have hb : ((fun slots => startVector b
      (tableExtending (ProtectedTable.slotCache cache) slots)) <$>
      ($ᵗ (TprfSecurityProof.Slot C → HashOutput))) >>= next =
      ($ᵗ (TprfSecurityProof.Slot C → HashOutput)) >>= (fun slots =>
        next (startVector b (tableExtending (ProtectedTable.slotCache cache) slots))) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  rw [← hb, evalDist_bind, hu, ← evalDist_bind]

def markedEvent (cache : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (indices : List XmssSecurity.ChainStep) (endpoints : ChainIndex → Digest)
    (p : (ChainIndex → Digest) ×
      (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput)) : Prop :=
  ∀ l, (FinitePosterior.evalRecorded
    (simulateQ TruncatedCompletion.lift (MarkedChain.walk
      (fun k v => TruncatedCompletion.project (ProtectedTable.chainCache cache l) (k, v))
      indices (p.1 l))) (ProtectedTable.chainCache cache l) (p.2 l)).1 = some (endpoints l)

set_option backward.isDefEq.respectTransparency false in
theorem uniform_marked_density (cache : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (indices : List XmssSecurity.ChainStep) (hn : indices.Nodup)
    (endpoints : ChainIndex → Digest) :
    Pr[markedEvent cache indices endpoints | do
      let starts ← $ᵗ (ChainIndex → Digest)
      let chains ← $ᵗ (ChainIndex → (XmssSecurity.ChainStep × Digest) → HashOutput)
      pure (starts, fun l => tableExtending (ProtectedTable.chainCache cache l) (chains l))] ≤
      ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ := by
  rw [probEvent_bind_eq_tsum, tsum_fintype]
  simp only [bind_pure_comp, probEvent_map]
  dsimp only [markedEvent, Function.comp_def]
  have hd := TruncatedCompletion.table_walks_density
    (I := ChainIndex) (Index := XmssSecurity.ChainStep)
    (fun l k v => TruncatedCompletion.project (ProtectedTable.chainCache cache l) (k, v))
    indices hn endpoints (ProtectedTable.chainCache cache) (fun _ _ _ _ => rfl)
  rw [show Fintype.card ChainIndex = 58 from rfl] at hd
  simpa only [probOutput_uniformSample, probEvent_uniformSample] using hd

set_option backward.isDefEq.respectTransparency false in
/-- Marked completion in the actual protected posterior pays the full 58-digest
endpoint density. The observed cache is arbitrary, subject to allowed PRF reads. -/
theorem marked_density (D : Finset C.Party) (hD : D.card ≤ C.t - 1)
    (b : XmssSecurity.TopIndex) (cache : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (hcache : UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b) cache)
    (indices : List XmssSecurity.ChainStep) (hn : indices.Nodup)
    (endpoints : ChainIndex → Digest) :
    Pr[fun table => markedEvent cache indices endpoints
      (SelectedKeygen.starts (tableExtending cache table) b,
        (ProtectedTable.split (tableExtending cache table)).2) |
      $ᵗ (ProtectedSlot C → HashOutput)] ≤ ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ := by
  have he := probEvent_congr' (p := markedEvent cache indices endpoints)
    (q := markedEvent cache indices endpoints) (fun _ _ => Iff.rfl)
    (joint_starts_chains D hD b cache hcache)
  rw [probEvent_map] at he
  exact (le_of_eq he).trans (uniform_marked_density cache indices hn endpoints)

end PosteriorCompletion

namespace PrivateRecord

open Classical

/-- Recover actual queried cells without filling the entire latent table. -/
def merge {D R : Type} (hidden observed : QueryCache (D →ₒ R)) : QueryCache (D →ₒ R) :=
  fun d => (observed d).orElse (fun _ => hidden d)

theorem merge_update {D R : Type} [DecidableEq D]
    (hidden observed : QueryCache (D →ₒ R)) (d : D) (value : R) :
    merge hidden (observed.cacheQuery d value) = (merge hidden observed).cacheQuery d value := by
  funext e
  by_cases h : e = d
  · subst e
    simp [merge]
  · simp [merge, QueryCache.cacheQuery, h]

theorem merge_of_le {D R : Type} (hidden observed : QueryCache (D →ₒ R))
    (h : observed ≤ hidden) : merge hidden observed = hidden := by
  funext d
  cases hd : observed d with
  | none => simp [merge, hd]
  | some value => simp [merge, hd, h hd]

def restore (hidden : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ)) :=
  (merge hidden s.1, s.2)

set_option backward.isDefEq.respectTransparency false in
/-- Private cells can be restored after every public step. The auxiliary cache
and original-query counter are retained exactly. -/
theorem query_restore (hidden : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (table : ProtectedSlot C → HashOutput)
    (t : ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C).Domain) :
    TprfSecurityProof.StateMap (restore hidden)
      (FinitePosterior.eager table CountedPosterior.aux t)
      (FinitePosterior.eager table CountedPosterior.aux t) := by
  rintro ⟨record, raw, n⟩
  rcases t with slot | (u | input) | cost
  · simp [FinitePosterior.eager, restore, StateT.run, merge_update]
  · simp [FinitePosterior.eager, CountedPosterior.aux, ProtectedRouting.samplingAux,
      restore, StateT.run, StateT.mk, Functor.map_map]
  · simp [FinitePosterior.eager, CountedPosterior.aux, ProtectedRouting.samplingAux,
      ProtectedRouting.aux, restore, StateT.run, StateT.mk, Functor.map_map]
  · simp [FinitePosterior.eager, CountedPosterior.aux, restore, StateT.run, StateT.mk]

/-- The execution itself sees the same answers; reconstruction is a projection
of its final state, with no additional cache cells or discarded cost. -/
theorem run_restore (hidden : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (table : ProtectedSlot C → HashOutput) {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C) α)
    (observed : QueryCache (ProtectedSlot C →ₒ HashOutput)) (h : observed ≤ hidden)
    (raw : HashCache C) (n : ℕ) :
    (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run (hidden, raw, n) =
      Prod.map id (restore hidden) <$>
        (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run (observed, raw, n) := by
  have hm := TprfSecurityProof.StateMap.simulateQ (query_restore hidden table) oa (observed, raw, n)
  simpa only [restore, merge_of_le hidden observed h] using hm

end PrivateRecord

namespace CanonicalCompletion

open Classical

@[simp] theorem evalRecorded_pure {D R α : Type} [DecidableEq D]
    (a : α) (cache : QueryCache (D →ₒ R)) (table : D → R) :
    FinitePosterior.evalRecorded (pure a) cache table = (a, cache) := rfl

@[simp] theorem evalRecorded_query_bind {D R α : Type} [DecidableEq D]
    (t : D) (k : R → OracleComp (D →ₒ R) α)
    (cache : QueryCache (D →ₒ R)) (table : D → R) :
    FinitePosterior.evalRecorded (query (spec := D →ₒ R) t >>= k) cache table =
      FinitePosterior.evalRecorded (k (table t)) (cache.cacheQuery t (table t)) table := rfl

theorem evalRecorded_bind {D R α β : Type} [DecidableEq D]
    (oa : OracleComp (D →ₒ R) α) (next : α → OracleComp (D →ₒ R) β)
    (cache : QueryCache (D →ₒ R)) (table : D → R) :
    FinitePosterior.evalRecorded (oa >>= next) cache table =
      FinitePosterior.evalRecorded (next (FinitePosterior.evalRecorded oa cache table).1)
        (FinitePosterior.evalRecorded oa cache table).2 table := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp only [pure_bind, evalRecorded_pure]
  | query_bind t k ih =>
    change FinitePosterior.evalRecorded (k (table t) >>= next) (cache.cacheQuery t (table t)) table = _
    exact ih (table t) (cache.cacheQuery t (table t))

def mapAnswer {State R Index : Type} (project : R → State) :
    QueryImpl ((Index × State) →ₒ State) (OracleComp ((Index × State) →ₒ R)) :=
  fun q => project <$> query (spec := (Index × State) →ₒ R) q

theorem mapAnswer_truncate {Index : Type} :
    mapAnswer (Index := Index) truncateHash =
      TruncatedCompletion.lift (D := Index × Digest) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A canonical path survives every mark when observed alternatives have
unique predecessors along that path. No conditioning or division is used. -/
theorem marked_of_path {State R Index : Type} [Fintype State] [DecidableEq State]
    [DecidableEq Index] (project : R → State)
    (observed : Index → State → Option State) (indices : List Index)
    (table : (Index × State) → R) (a : ℕ → State)
    (hedge : ∀ k (hk : k < indices.length),
      project (table (indices[k], a k)) = a (k + 1))
    (hunique : ∀ k (hk : k < indices.length) other,
      observed indices[k] other = some (a (k + 1)) → other = a k)
    (cache : QueryCache ((Index × State) →ₒ R)) :
    (FinitePosterior.evalRecorded (simulateQ (mapAnswer (Index := Index) project)
      (MarkedChain.walk observed indices (a 0))) cache table).1 = some (a indices.length) := by
  classical
  induction indices generalizing a cache with
  | nil => simp [MarkedChain.walk]
  | cons index rest ih =>
    have he : project (table (index, a 0)) = a 1 := hedge 0 (by simp)
    have hu : ∀ other, observed index other = some (project (table (index, a 0))) → other = a 0 := by
      intro other ho
      rw [he] at ho
      exact hunique 0 (by simp) other ho
    simp only [MarkedChain.walk, simulateQ_bind, simulateQ_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_map, mapAnswer,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      evalRecorded_query_bind, id_eq, hu, ↓reduceIte]
    rw [show project (table (index, a 0)) = a 1 from he]
    rw [if_pos (show ∀ other, observed index other = some (a 1) → other = a 0 from
      hunique 0 (by simp))]
    apply ih (a := fun k => a (k + 1))
    · intro k hk
      exact hedge (k + 1) (by simpa using Nat.succ_lt_succ hk)
    · intro k hk other h
      exact hunique (k + 1) (by simpa using Nat.succ_lt_succ hk) other h

def path (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (j : ℕ) : Digest :=
  XmssSecurity.Wots.walk
    (XmssSecurity.Concrete.CacheView.topChainStep (SigningDescentProof.thView cache) x.1 b l)
    0 j (replayStarts prims x cache topLayer (topKey b) l)

set_option backward.isDefEq.respectTransparency false in
/-- In the exceptional collision-free case the actual canonical paths satisfy
all marks. The completion table need only agree at actually cached cells. -/
theorem marked_of_noCollision (x : SigningSecurityProof.Keys3 C)
    (observed cache : HashCache C) (hle : observed ≤ cache)
    (hno : NoForestCollision prims x cache) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput)
    (hstart : SelectedKeygen.starts table b = fun l => path prims x cache b l 0)
    (hcached : ∀ (l : ChainIndex) (k : XmssSecurity.ChainStep),
      (cache (protectedInput x b (.inr (l, k, path prims x cache b l k.val)))).isSome)
    (hagree : ∀ (l : ChainIndex) (k : XmssSecurity.ChainStep) value,
      cache (protectedInput x b (.inr (l, k, path prims x cache b l k.val))) = some value →
        table (.inr (l, k, path prims x cache b l k.val)) = value) :
    PosteriorCompletion.markedEvent (ProtectedRouting.split (protectedInput x b) observed).1
      (List.finRange 3) (fun l => path prims x cache b l 3)
      (SelectedKeygen.starts table b, (ProtectedTable.split table).2) := by
  intro l
  have he : ∀ k (hk : k < (List.finRange 3).length),
      truncateHash ((ProtectedTable.split table).2 l
        ((List.finRange 3)[k], path prims x cache b l k)) = path prims x cache b l (k + 1) := by
    intro k hk
    have hk' : k < 3 := by simpa using hk
    have hkchain : k < XmssSecurity.chainLength - 1 := hk'
    obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp (hcached l ⟨k, hk'⟩)
    have ht := hagree l ⟨k, hk'⟩ value hv
    simp only [List.getElem_finRange]
    change truncateHash (table (.inr (l, ⟨k, hk'⟩, path prims x cache b l k))) = _
    rw [ht]
    have hd := XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some
      (show SigningDescentProof.thView cache
        (XmssSecurity.Concrete.CacheView.topChainInput x.1 b l ⟨k, hk'⟩
          (path prims x cache b l k)) = some value from hv)
    simpa only [path, XmssSecurity.Wots.walk, Nat.zero_add,
      XmssSecurity.Concrete.CacheView.topChainStep, hkchain, ↓reduceDIte,
      truncateHash, XmssSecurity.truncateHash, digestBits, XmssSecurity.digestBits] using hd.symm
  have hu : ∀ k (hk : k < (List.finRange 3).length) other,
      TruncatedCompletion.project
        (ProtectedTable.chainCache (ProtectedRouting.split (protectedInput x b) observed).1 l)
        ((List.finRange 3)[k], other) = some (path prims x cache b l (k + 1)) →
      other = path prims x cache b l k := by
    intro k hk other ho
    have hidx : (List.finRange 3)[k] = (⟨k, by simpa using hk⟩ : Fin 3) := by simp
    dsimp only [TruncatedCompletion.project, ProtectedTable.chainCache, ProtectedRouting.split,
      protectedInput] at ho
    rw [hidx] at ho
    apply observedTopRows_unique prims x observed cache hle hno b l k
      (by simpa only [observedTopRows_length, List.length_finRange] using hk) other
    simpa only [TruncatedCompletion.project, ProtectedTable.chainCache, ProtectedRouting.split,
      protectedInput, List.getElem_finRange, observedTopRows, List.getElem_ofFn, path] using ho
  have hm := marked_of_path truncateHash
    (fun k v => TruncatedCompletion.project
      (ProtectedTable.chainCache (ProtectedRouting.split (protectedInput x b) observed).1 l) (k, v))
    (List.finRange 3) ((ProtectedTable.split table).2 l) (path prims x cache b l) he hu
    (ProtectedTable.chainCache (ProtectedRouting.split (protectedInput x b) observed).1 l)
  rw [mapAnswer_truncate] at hm
  simpa only [hstart, List.length_finRange] using hm

end CanonicalCompletion

namespace PublicContinuation

open Classical

def rows (record : QueryCache (ProtectedSlot C →ₒ HashOutput)) (l : ChainIndex) :
    List (Digest → Option Digest) :=
  List.ofFn fun k : Fin 3 => fun v => (record (.inr (l, k, v))).map truncateHash

theorem rows_length (record : QueryCache (ProtectedSlot C →ₒ HashOutput)) (l : ChainIndex) :
    (rows record l).length = 3 := by simp [rows]

theorem edge_rows (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (l : ChainIndex) (k : Fin 3) (v : Digest) :
    LayeredGraph.edge (rows record l) k.val v = (record (.inr (l, k, v))).map truncateHash := by
  rw [LayeredGraph.edge, List.getElem?_eq_getElem
    (show k.val < (rows record l).length by rw [rows_length]; exact k.isLt)]
  simp only [Option.bind_some, rows, List.getElem_ofFn]

theorem rows_ext {r s : List (Digest → Option Digest)} (hlen : r.length = s.length)
    (h : ∀ k v, LayeredGraph.edge r k v = LayeredGraph.edge s k v) : r = s := by
  apply List.ext_getElem hlen
  intro k hk hs
  funext v
  simpa only [LayeredGraph.edge, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hs, Option.bind_some] using h k v

theorem rows_update_slot (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (slot : TprfSecurityProof.Slot C) (value : HashOutput) :
    rows (record.cacheQuery (.inl slot) value) = rows record := by
  funext l
  simp [rows, QueryCache.cacheQuery]

set_option backward.isDefEq.respectTransparency false in
theorem rows_update_chain (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (l : ChainIndex) (k : Fin 3) (v : Digest) (value : HashOutput) :
    rows (record.cacheQuery (.inr (l, k, v)) value) =
      Function.update (rows record) l
        (LayeredGraph.insertEdge (rows record l) k.val v (truncateHash value)) := by
  classical
  funext j
  by_cases hj : j = l
  · subst j
    rw [Function.update_self]
    apply rows_ext (by simp [rows_length, LayeredGraph.length_insertEdge])
    intro i input
    by_cases hi : i < 3
    · have hk : k.val < (rows record l).length := by simpa [rows_length] using k.isLt
      rw [LayeredGraph.edge_insertEdge _ _ _ _ hk]
      change LayeredGraph.edge (rows (record.cacheQuery (.inr (l, k, v)) value) l)
          (⟨i, hi⟩ : Fin 3).val input = _
      rw [edge_rows]
      by_cases he : (⟨i, hi⟩ : Fin 3) = k ∧ input = v
      · obtain ⟨hki, rfl⟩ := he
        have hival : i = k.val := congrArg Fin.val hki
        simp only [hival, Fin.eta, QueryCache.cacheQuery_self, Option.map_some,
          and_self, ↓reduceIte]
        have ht : (.inr (l, (⟨i, hi⟩ : Fin 3), input) : ProtectedSlot C) = .inr (l, k, input) :=
          congrArg (fun j : Fin 3 => (.inr (l, j, input) : ProtectedSlot C)) hki
        rw [ht]
        simp
      · have hne : (.inr (l, (⟨i, hi⟩ : Fin 3), input) : ProtectedSlot C) ≠ .inr (l, k, v) := by
          simpa using he
        have hne' : ¬(i = k.val ∧ input = v) := by
          intro h
          exact he ⟨Fin.ext h.1, h.2⟩
        rw [QueryCache.cacheQuery_of_ne _ _ hne, if_neg hne']
        exact (edge_rows record l ⟨i, hi⟩ input).symm
    · have ha : (rows (record.cacheQuery (.inr (l, k, v)) value) l)[i]? = none :=
        List.getElem?_eq_none (by rw [rows_length]; omega)
      have hb : (LayeredGraph.insertEdge (rows record l) k.val v (truncateHash value))[i]? = none :=
        List.getElem?_eq_none (by rw [LayeredGraph.length_insertEdge, rows_length]; omega)
      simp only [LayeredGraph.edge, ha, hb]
  · rw [Function.update_of_ne hj]
    unfold rows
    congr 1
    funext step input
    rw [QueryCache.cacheQuery_of_ne _ _ (by
      intro he
      exact hj (congrArg (fun s : ChainIndex × XmssSecurity.ChainStep × Digest => s.1) (Sum.inr.inj he)))]

set_option backward.isDefEq.respectTransparency false in
/-- Only the marginal used by the potential is projected. The public oracle
still returns the full hash output and keeps its full cache. -/
theorem chain_query_projection (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (n : ℕ) (l : ChainIndex) (k : Fin 3) (v : Digest) :
    𝒟[(fun r => (truncateHash r.1, rows r.2, n + 1)) <$>
      (((ProtectedSlot C →ₒ HashOutput).randomOracle (.inr (l, k, v))).run record)] =
      𝒟[LayeredGraph.step (l, k, v) (rows record, n)] := by
  classical
  cases hc : record (.inr (l, k, v)) with
  | some value =>
    rw [show ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inr (l, k, v))).run record =
      pure (value, record) from QueryImpl.withCaching_run_some _ hc]
    simp only [map_pure, LayeredGraph.step, edge_rows, hc, Option.map_some]
  | none =>
    rw [show ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inr (l, k, v))).run record =
      (fun value => (value, record.cacheQuery (.inr (l, k, v)) value)) <$> ($ᵗ HashOutput) from
        QueryImpl.withCaching_run_none _ hc]
    simp only [Functor.map_map, rows_update_chain, LayeredGraph.step, edge_rows, hc, Option.map_none]
    have hm := congrArg (fun d : SPMF Digest => (fun value =>
      (value, Function.update (rows record) l
        (LayeredGraph.insertEdge (rows record l) k.val v value), n + 1)) <$> d)
      ThresholdLeanXmssSecurity.evalDist_truncateHash_uniform
    simpa only [← evalDist_map, Functor.map_map] using hm

set_option backward.isDefEq.respectTransparency false in
theorem chain_query_discounted (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (n : ℕ) (target : ChainIndex → Digest) (l : ChainIndex) (k : Fin 3) (v : Digest) :
    (∑' r, Pr[= r | ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inr (l, k, v))).run record] *
      LayeredGraph.discounted target (rows r.2, n + 1)) ≤
      LayeredGraph.discounted target (rows record, n) := by
  have hp := chain_query_projection record n l k v
  have hm := congrArg (fun d : SPMF (Digest × LayeredGraph.GraphState ChainIndex Digest) =>
    ∑' r, d r * LayeredGraph.discounted target r.2) hp
  simp only [← probOutput_def, tsum_probOutput_map_mul] at hm
  rw [hm]
  exact LayeredGraph.step_discounted (l, k, v) (rows record, n)
    (fun i => rows_length record i) target

abbrev Spec (C : Committee) := (ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))
abbrev State (C : Committee) := QueryCache (ProtectedSlot C →ₒ HashOutput) × (HashCache C × ℕ)

/-- Count once at each raw hash query. Local PRG expansion has exactly one such
query; the local-to-public translation below keeps the original count. -/
def implementation : QueryImpl (Spec C) (StateT (State C) ProbComp)
  | .inl slot => fun s => (fun r => (r.1, r.2, s.2.1, s.2.2 + 1)) <$>
      ((ProtectedSlot C →ₒ HashOutput).randomOracle slot).run s.1
  | .inr (.inl n) => fun s => (fun value => (value, s)) <$> (liftM (unifSpec.query n) : ProbComp _)
  | .inr (.inr input) => fun s => (fun r => (r.1, s.1, r.2, s.2.2 + 1)) <$>
      ((Query C →ₒ HashOutput).randomOracle input).run s.2.1

def potential (target : ChainIndex → Digest) (s : State C) : ℝ≥0∞ :=
  LayeredGraph.discounted target (rows s.1, s.2.2)

theorem discounted_tick_le (target : ChainIndex → Digest)
    (rs : ChainIndex → List (Digest → Option Digest)) (n : ℕ) :
    LayeredGraph.discounted target (rs, n + 1) ≤ LayeredGraph.discounted target (rs, n) := by
  apply ENNReal.div_le_div le_rfl
  exact pow_le_pow_right₀ LayeredGraph.growth_one_le (Nat.le_succ n)

set_option backward.isDefEq.respectTransparency false in
theorem slot_query_discounted (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (n : ℕ) (target : ChainIndex → Digest) (slot : TprfSecurityProof.Slot C) :
    (∑' r, Pr[= r | ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inl slot)).run record] *
      LayeredGraph.discounted target (rows r.2, n + 1)) ≤
      LayeredGraph.discounted target (rows record, n) := by
  classical
  cases hc : record (.inl slot) with
  | some value =>
    rw [show ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inl slot)).run record =
      pure (value, record) from QueryImpl.withCaching_run_some _ hc,
      tsum_probOutput_pure_mul]
    exact discounted_tick_le target (rows record) n
  | none =>
    rw [show ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inl slot)).run record =
      (fun value => (value, record.cacheQuery (.inl slot) value)) <$> ($ᵗ HashOutput) from
        QueryImpl.withCaching_run_none _ hc, tsum_probOutput_map_mul]
    simp only [rows_update_slot]
    rw [tsum_probOutput_mul_of_const_on_support _ (fun _ _ => rfl) (by simp)]
    exact discounted_tick_le target (rows record) n

set_option backward.isDefEq.respectTransparency false in
theorem query_discounted (target : ChainIndex → Digest) (t : (Spec C).Domain) (s : State C) :
    (∑' r, Pr[= r | (implementation t).run s] * potential target r.2) ≤ potential target s := by
  classical
  rcases t with (slot | ⟨l, k, v⟩) | n | input
  · simpa only [implementation, StateT.run, tsum_probOutput_map_mul, potential] using
      slot_query_discounted s.1 s.2.2 target slot
  · simpa only [implementation, StateT.run, tsum_probOutput_map_mul, potential] using
      chain_query_discounted s.1 s.2.2 target l k v
  · simp only [implementation, StateT.run, tsum_probOutput_map_mul]
    exact le_of_eq (tsum_probOutput_mul_of_const_on_support _ (fun _ _ => rfl) (by simp))
  · simp only [implementation, StateT.run, tsum_probOutput_map_mul, potential]
    rw [tsum_probOutput_mul_of_const_on_support _ (fun _ _ => rfl) (by simp)]
    exact discounted_tick_le target (rows s.1) s.2.2

/-- An adaptive public program may use all 256 answer bits. Only the potential
is projected, so its drift bound retains that adaptivity without a new game. -/
theorem expected_discounted {α : Type} (oa : OracleComp (Spec C) α)
    (target : ChainIndex → Digest) (s : State C) :
    XmssSecurity.expectedFinal implementation (potential target) oa s ≤ potential target s := by
  have hz (oa : OracleComp (Spec C) α) (s : State C) :
      XmssSecurity.expectedSimulatedCost implementation (fun _ _ => 0) oa s = 0 := by
    induction oa using OracleComp.inductionOn generalizing s with
    | pure value => rfl
    | query_bind t k ih =>
      simp only [XmssSecurity.expectedSimulatedCost_query_bind, ih, mul_zero, tsum_zero, add_zero]
  have h := XmssSecurity.expectedFinal_le implementation (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) (potential target) (fun _ _ => 0)
    (fun t s _ => by simpa only [add_zero] using query_discounted target t s) oa s trivial
  simpa only [hz, add_zero] using h

set_option backward.isDefEq.respectTransparency false in
/-- Fixed endpoints and an initially empty selected structural cache suffice
for the public continuation bound, even with an existing positive query count. -/
theorem terminal_probability {α : Type} (oa : OracleComp (Spec C) α)
    (target : ChainIndex → Digest) (s : State C)
    (hempty : rows s.1 = LayeredGraph.emptyRows) (q : ℕ) (hq : q < 2 ^ 127) :
    Pr[fun r => LayeredGraph.Terminal target q (rows r.2.1, r.2.2.2) |
      (simulateQ implementation oa).run s] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  let run := (fun r => (r.1, rows r.2.1, r.2.2.2)) <$> (simulateQ implementation oa).run s
  have hmean : (∑' r, Pr[= r | run] * LayeredGraph.discounted target r.2) ≤ 1 := by
    rw [tsum_probOutput_map_mul]
    apply le_trans (expected_discounted oa target s)
    simp only [potential, LayeredGraph.discounted, hempty, LayeredGraph.potential,
      LayeredGraph.productWeight_empty, ENNReal.ofReal_one]
    calc
      _ ≤ (1 : ℝ≥0∞) / 1 := ENNReal.div_le_div le_rfl (one_le_pow₀ LayeredGraph.growth_one_le)
      _ = 1 := by simp
  have h := LayeredGraph.terminal_probability_of_expected run target q hmean
  rw [probEvent_map] at h
  exact h.trans (LayeredGraph.growth_query_cap q hq
    (show Fintype.card Digest = 2 ^ 128 by simp [digestBits]))

set_option backward.isDefEq.respectTransparency false in
theorem route_count (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (input : Query C) (s : State C) :
    (simulateQ implementation (ProtectedRouting.routeWithSampling (protectedInput x b) input)).run s =
      (fun r => (r.1, r.2.1, r.2.2, s.2.2 + 1)) <$>
        (simulateQ (FinitePosterior.lazy ProtectedRouting.samplingAux)
          (ProtectedRouting.routeWithSampling (protectedInput x b) input)).run (s.1, s.2.1) := by
  classical
  unfold ProtectedRouting.routeWithSampling ProtectedRouting.route
  split <;> simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    ProtectedRouting.extend,
    implementation, FinitePosterior.lazy, ProtectedRouting.samplingAux, ProtectedRouting.aux,
    StateT.run, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Every original local hash or PRG call is exactly one public counted query;
uniform sampling is free in both representations. -/
theorem local_count (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (t : (LocalSpec C).Domain) (s : State C) :
    (simulateQ implementation (protectedLocal prims x b t)).run s =
      (fun r => (r.1, r.2.1, r.2.2, s.2.2 + localCost t)) <$>
        (simulateQ (FinitePosterior.lazy ProtectedRouting.samplingAux)
          (protectedLocal prims x b t)).run (s.1, s.2.1) := by
  rcases t with n | input | p
  · simp only [protectedLocal, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, implementation, FinitePosterior.lazy, ProtectedRouting.samplingAux, StateT.run,
      Functor.map_map, localCost, Nat.add_zero]
    congr 1
  · exact route_count x b input s
  · simp only [protectedLocal, simulateQ_map, StateT.run_map, route_count, Functor.map_map]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem local_eq (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (t : (LocalSpec C).Domain) :
    TprfSecurityProof.StateMap
      (fun s : HashCache C × ℕ =>
        ((ProtectedRouting.split (protectedInput x b) s.1).1,
          (ProtectedRouting.split (protectedInput x b) s.1).2, s.2))
      (withLocalCount (signingLocalAnswer prims) t)
      (simulateQ implementation (protectedLocal prims x b t)) := by
  intro s
  rw [local_count]
  dsimp only
  rw [show ((ProtectedRouting.split (protectedInput x b) s.1).1,
        (ProtectedRouting.split (protectedInput x b) s.1).2) =
      ProtectedRouting.split (protectedInput x b) s.1 from Prod.mk.eta]
  rw [protectedLocal_eq prims x b hno t s.1]
  simp only [withLocalCount, StateT.run_mk, Functor.map_map]
  rfl

theorem local_run (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ) :
    (simulateQ implementation (simulateQ (protectedLocal prims x b) oa)).run
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n) =
      (fun r => (r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
        (ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2)) <$>
        (simulateQ (withLocalCount (signingLocalAnswer prims)) oa).run (cache, n) := by
  rw [← QueryImpl.simulateQ_compose]
  exact TprfSecurityProof.StateMap.simulateQ (local_eq prims x b hno) oa (cache, n)

theorem counted_run (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ) :
    (simulateQ implementation (simulateQ (protectedLocal prims x b) oa)).run
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n) =
      (simulateQ (FinitePosterior.lazy CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) oa)).run
          ((ProtectedRouting.split (protectedInput x b) cache).1,
            (ProtectedRouting.split (protectedInput x b) cache).2, n) :=
  (local_run prims x b hno oa cache n).trans
    (CountedPosterior.local_lazy_run prims x b hno oa cache n).symm

theorem rows_split (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (cache : HashCache C) : rows (ProtectedRouting.split (protectedInput x b) cache).1 =
      fun l => observedTopRows x.1 cache b l := rfl

theorem rows_empty (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (h : ∀ l k v, record (.inr (l, k, v)) = none) : rows record = LayeredGraph.emptyRows := by
  funext l
  simp [rows, h, LayeredGraph.emptyRows]

set_option backward.isDefEq.respectTransparency false in
/-- The public terminal bound applies directly to the counted posterior run
used by the adaptive-read invariant and deferred-sampling identity. -/
theorem counted_terminal_probability (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (target : ChainIndex → Digest) (q : ℕ) (hq : q < 2 ^ 127) :
    Pr[fun r => LayeredGraph.Terminal target q (rows r.2.1, r.2.2.2) |
      (simulateQ (FinitePosterior.lazy CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) oa)).run
          ((ProtectedRouting.split (protectedInput x b) cache).1,
            (ProtectedRouting.split (protectedInput x b) cache).2, n)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [← counted_run prims x b hno oa cache n]
  exact terminal_probability _ target _ (rows_empty _ hempty) q hq

end PublicContinuation

namespace GateProbability

open Classical

def Good (b : XmssSecurity.TopIndex) (target : ChainIndex → Digest) (q : ℕ)
    {α : Type} (r : α × PublicContinuation.State C) (table : ProtectedSlot C → HashOutput) : Prop :=
  (∃ D : Finset C.Party, D.card ≤ C.t - 1 ∧
    UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b) r.2.1) ∧
  PosteriorCompletion.markedEvent r.2.1 (List.finRange 3) target
    (SelectedKeygen.starts table b, (ProtectedTable.split table).2) ∧
  LayeredGraph.Terminal target q (PublicContinuation.rows r.2.1, r.2.2.2)

set_option backward.isDefEq.respectTransparency false in
theorem inner_bound (b : XmssSecurity.TopIndex) (target : ChainIndex → Digest) (q : ℕ)
    {α : Type} (r : α × PublicContinuation.State C) :
    Pr[fun h => Good b target q r (tableExtending r.2.1 h) |
      $ᵗ (ProtectedSlot C → HashOutput)] ≤
      if LayeredGraph.Terminal target q (PublicContinuation.rows r.2.1, r.2.2.2)
      then ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ else 0 := by
  classical
  by_cases ht : LayeredGraph.Terminal target q (PublicContinuation.rows r.2.1, r.2.2.2)
  · rw [if_pos ht]
    by_cases ha : ∃ D : Finset C.Party, D.card ≤ C.t - 1 ∧
        UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b) r.2.1
    · obtain ⟨D, hD, hallowed⟩ := ha
      apply le_trans (probEvent_mono (p := fun h => Good b target q r (tableExtending r.2.1 h))
        (fun _ _ h => h.2.1))
      exact PosteriorCompletion.marked_density D hD b r.2.1 hallowed (List.finRange 3)
        (List.nodup_finRange 3) target
    · simp [Good, ha]
  · simp [Good, ht]

set_option backward.isDefEq.respectTransparency false in
/-- Posterior marking pays one whole endpoint-vector density. The terminal
event stays in the public run, without conditioning on the endpoint relation. -/
theorem posterior_bound {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C) α)
    (s : PublicContinuation.State C) (b : XmssSecurity.TopIndex)
    (target : ChainIndex → Digest) (q : ℕ) :
    Pr[fun p => Good b target q p.1 p.2 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run s
      pure (r, table)] ≤
      ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ *
        Pr[fun r => LayeredGraph.Terminal target q (PublicContinuation.rows r.2.1, r.2.2.2) |
          (simulateQ (FinitePosterior.lazy CountedPosterior.aux) oa).run s] := by
  have hd := FinitePosterior.joint_table_mixed CountedPosterior.aux CountedPosterior.aux_preserves oa s
  have hp := probEvent_congr' (p := fun p => Good b target q p.1 p.2)
    (q := fun p => Good b target q p.1 p.2) (fun _ _ => Iff.rfl) hd
  rw [hp, probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map]
  calc
    _ ≤ ∑' r, Pr[= r | (simulateQ (FinitePosterior.lazy CountedPosterior.aux) oa).run s] *
        (if LayeredGraph.Terminal target q (PublicContinuation.rows r.2.1, r.2.2.2)
          then ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ else 0) :=
      ENNReal.tsum_le_tsum fun r => mul_le_mul_left' (inner_bound b target q r) _
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro r
      split <;> simp only [mul_zero, zero_mul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- For each fixed endpoint vector the actual counted posterior pays its
vector density times the public-continuation bound. -/
theorem fixed_endpoint_bound (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (target : ChainIndex → Digest) (q : ℕ) (hq : q < 2 ^ 127) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => Good b target q p.1 p.2 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) oa)).run s
      pure (r, table)] ≤ ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply le_trans (posterior_bound _ _ b target q)
  exact mul_le_mul_left' (PublicContinuation.counted_terminal_probability prims x b hno oa
    cache n hempty target q hq) _

theorem adaptive_le_sum {T E α : Type} [Fintype E]
    (prior : ProbComp T) (choose : T → E) (run : E → T → ProbComp α)
    (event : E → T → α → Prop) :
    Pr[fun p => event (choose p.2) p.2 p.1 | do
      let t ← prior
      let r ← run (choose t) t
      pure (r, t)] ≤
    ∑ e, Pr[fun p => event e p.2 p.1 | do
      let t ← prior
      let r ← run e t
      pure (r, t)] := by
  classical
  simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map]
  calc
    _ ≤ ∑' t, Pr[= t | prior] * ∑ e, Pr[event e t | run e t] := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply mul_le_mul_left'
      exact Finset.single_le_sum (f := fun e : E => Pr[event e t | run e t])
        (fun _ _ => bot_le) (Finset.mem_univ (choose t))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Summing over the endpoint vector cancels its posterior density. The
endpoint choice remains inside the original table-first execution. -/
theorem adaptive_endpoint_bound (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (next : (ChainIndex → Digest) → OracleComp (LocalSpec C) α)
    (choose : (ProtectedSlot C → HashOutput) → (ChainIndex → Digest))
    (cache : HashCache C) (n : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (q : ℕ) (hq : q < 2 ^ 127) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => Good b (choose p.2) q p.1 p.2 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b) (next (choose table)))).run s
      pure (r, table)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  let s : PublicContinuation.State C :=
    ((ProtectedRouting.split (protectedInput x b) cache).1,
      (ProtectedRouting.split (protectedInput x b) cache).2, n)
  let prior := tableExtending s.1 <$> ($ᵗ (ProtectedSlot C → HashOutput))
  let run := fun target table =>
    (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
      (simulateQ (CountedPosterior.localQuery prims x b) (next target))).run s
  have hs := adaptive_le_sum prior choose run (fun target table r => Good b target q r table)
  simp only [prior, bind_map_left] at hs
  apply le_trans hs
  calc
    _ ≤ ∑ _target : ChainIndex → Digest,
        ((2 ^ 128 : ℝ≥0∞) ^ 58)⁻¹ * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro target _
      exact fixed_endpoint_bound prims x b hno (next target) cache n hempty target q hq
    _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        show Fintype.card Digest = 2 ^ 128 by simp [digestBits],
        show Fintype.card ChainIndex = 58 from rfl, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end GateProbability

namespace PrivateRecord

def shift (offset : ℕ) (s : PublicContinuation.State C) : PublicContinuation.State C :=
  (s.1, s.2.1, offset + s.2.2)

set_option backward.isDefEq.respectTransparency false in
theorem query_shift (offset : ℕ) (table : ProtectedSlot C → HashOutput)
    (t : ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C).Domain) :
    TprfSecurityProof.StateMap (shift offset)
      (FinitePosterior.eager table CountedPosterior.aux t)
      (FinitePosterior.eager table CountedPosterior.aux t) := by
  rintro ⟨record, raw, n⟩
  rcases t with slot | (u | input) | cost
  · simp [FinitePosterior.eager, shift, StateT.run]
  · simp [FinitePosterior.eager, CountedPosterior.aux, ProtectedRouting.samplingAux,
      shift, StateT.run, StateT.mk, Functor.map_map]
  · simp [FinitePosterior.eager, CountedPosterior.aux, ProtectedRouting.samplingAux,
      ProtectedRouting.aux, shift, StateT.run, StateT.mk, Functor.map_map]
  · simp [FinitePosterior.eager, CountedPosterior.aux, shift, StateT.run, StateT.mk, Nat.add_assoc]

theorem run_shift (offset : ℕ) (table : ProtectedSlot C → HashOutput) {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C) α)
    (s : PublicContinuation.State C) :
    (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run (shift offset s) =
      Prod.map id (shift offset) <$>
        (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run s :=
  TprfSecurityProof.StateMap.simulateQ (query_shift offset table) oa s

set_option backward.isDefEq.respectTransparency false in
/-- Restore both the private queried cells and the entire private/prefix cost.
The offset may depend on the private execution; it is fixed inside that bind. -/
theorem run_restore_shift (hidden observed : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (hle : observed ≤ hidden) (offset : ℕ) (table : ProtectedSlot C → HashOutput) {α : Type}
    (oa : OracleComp ((ProtectedSlot C →ₒ HashOutput) + CountedPosterior.AuxSpec C) α)
    (raw : HashCache C) :
    (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run (hidden, raw, offset) =
      (fun r => (r.1, merge hidden r.2.1, r.2.2.1, offset + r.2.2.2)) <$>
        (simulateQ (FinitePosterior.eager table CountedPosterior.aux) oa).run (observed, raw, 0) := by
  rw [run_restore hidden table oa observed hle raw offset]
  rw [show (observed, raw, offset) = shift offset (observed, raw, 0) from by simp [shift],
    run_shift, Functor.map_map]
  rfl

theorem restored_public_count_le (hidden : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (offset : ℕ) (s : PublicContinuation.State C) :
    s.2.2 ≤ (restore hidden (shift offset s)).2.2 := Nat.le_add_left _ _

end PrivateRecord

namespace FinitePosterior

open Classical

/-- Every supported eager execution under a cache-compatible table is also
supported by the lazy run. The full table sample has positive mass. -/
theorem eager_support_lazy {D R Aux α ι : Type} [DecidableEq D]
    [Finite D] [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    {auxSpec : OracleSpec ι}
    (aux : QueryImpl auxSpec (StateT (QueryCache (D →ₒ R) × Aux) ProbComp))
    (haux : ∀ t s r, r ∈ support ((aux t).run s) → r.2.1 = s.1)
    (oa : OracleComp ((D →ₒ R) + auxSpec) α) (s : QueryCache (D →ₒ R) × Aux)
    (h : D → R) (r : α × QueryCache (D →ₒ R) × Aux)
    (hr : r ∈ support ((simulateQ (eager (tableExtending s.1 h) aux) oa).run s)) :
    r ∈ support ((simulateQ (lazy aux) oa).run s) := by
  have hj : (r, tableExtending s.1 h) ∈ support (do
      let h ← $ᵗ (D → R)
      let table := tableExtending s.1 h
      let v ← (simulateQ (eager table aux) oa).run s
      pure (v, table)) := by
    rw [mem_support_bind_iff]
    refine ⟨h, by simp, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨r, hr, by simp⟩
  have hl := (mem_support_iff_of_evalDist_eq (joint_table_mixed aux haux oa s) _).mp hj
  simp only [mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at hl
  obtain ⟨v, hv, table, _, he, _⟩ := hl
  exact he ▸ hv

end FinitePosterior

namespace FinitePosterior

/-- Compatible eager execution only adds queried cells, and every recorded
answer remains equal to the fixed table. -/
theorem eager_cache {D R Aux ι α : Type} [DecidableEq D] {auxSpec : OracleSpec ι}
    (aux : QueryImpl auxSpec (StateT (QueryCache (D →ₒ R) × Aux) ProbComp))
    (haux : ∀ t s r, r ∈ support ((aux t).run s) → r.2.1 = s.1)
    (table : D → R) (oa : OracleComp ((D →ₒ R) + auxSpec) α) :
    ∀ s, s.1.AgreesWithFn table → ∀ r ∈ support ((simulateQ (eager table aux) oa).run s),
      s.1 ≤ r.2.1 ∧ r.2.1.AgreesWithFn table := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨le_rfl, hs⟩
  | query_bind t k ih =>
    intro s hs r hr
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    have hstep : s.1 ≤ v.2.1 ∧ v.2.1.AgreesWithFn table := by
      cases t with
      | inl d =>
        simp only [eager, StateT.run, mem_support_pure_iff] at hv
        subst v
        constructor
        · intro e value he
          by_cases hed : e = d
          · subst e
            simp [hs he]
          · simpa only [QueryCache.cacheQuery_of_ne _ _ hed] using he
        · intro e value he
          by_cases hed : e = d
          · subst e
            change table d = value
            exact Option.some.inj (by simpa only [QueryCache.cacheQuery_self] using he)
          · exact hs ((QueryCache.cacheQuery_of_ne _ _ hed).symm.trans he)
      | inr t =>
        have he := haux t s v hv
        rw [he]
        exact ⟨le_rfl, hs⟩
    obtain ⟨hle, hagree⟩ := ih v.1 v.2 hstep.2 r hr
    exact ⟨hstep.1.trans hle, hagree⟩

theorem extending_agrees {D R : Type} (cache : QueryCache (D →ₒ R)) (table : D → R) :
    cache.AgreesWithFn (tableExtending cache table) := by
  intro d value hv
  simp [tableExtending, hv]

end FinitePosterior

namespace SelectedKeygen

set_option backward.isDefEq.respectTransparency false in
/-- The counted private block still exposes only its endpoint bits; its
possibly execution-dependent counter remains hidden inside the private bind. -/
theorem counted_jobs_projection (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (s : PublicContinuation.State C) :
    (fun r => (r.1, r.2.2.1)) <$>
      (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b)
          (liftComp ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)))).run s =
      pure ((List.finRange numChains).map (fun l => bitsOfDigest (endpoints table b l)), s.2.1) := by
  have hf := CountedPosterior.eager_forget_run prims x b table
    (liftComp ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)) s
  have hh := congrArg (fun oa => Prod.map id Prod.snd <$> oa) hf
  rw [ProtectedRouting.eager_forget_run, Functor.map_map] at hh
  change (interpret prims x b table
    ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1))).run s.2.1 = _ at hh
  rw [interpret_jobs prims x b hno, StateT.run_pure] at hh
  exact hh.symm

theorem counted_jobs_support (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (s : PublicContinuation.State C)
    (r : List (List Bit) × PublicContinuation.State C)
    (hr : r ∈ support ((simulateQ (FinitePosterior.eager table CountedPosterior.aux)
      (simulateQ (CountedPosterior.localQuery prims x b)
        (liftComp ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)))).run s)) :
    r.1 = (List.finRange numChains).map (fun l => bitsOfDigest (endpoints table b l)) ∧
      r.2.2.1 = s.2.1 := by
  have hm : (r.1, r.2.2.1) ∈ support
      ((fun z => (z.1, z.2.2.1)) <$> (simulateQ (FinitePosterior.eager table CountedPosterior.aux)
        (simulateQ (CountedPosterior.localQuery prims x b)
          (liftComp ((jobs b).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)))).run s) := by
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  rw [counted_jobs_projection prims x b hno, mem_support_pure_iff] at hm
  exact Prod.mk.inj hm

end SelectedKeygen

namespace CountedPosterior

abbrev run {α : Type} (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput) (oa : OracleComp (LocalSpec C) α)
    (s : PublicContinuation.State C) : ProbComp (α × PublicContinuation.State C) :=
  (simulateQ (FinitePosterior.eager table aux) (simulateQ (localQuery prims x b) oa)).run s

theorem run_world_bind {α β : Type} (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput) (oa : OracleComp (WorldSpec C) α)
    (next : α → OracleComp (WorldSpec C) β) (s : PublicContinuation.State C) :
    run prims x b table (simulateQ worldLocalize (oa >>= next)) s = (do
      let r ← run prims x b table (simulateQ worldLocalize oa) s
      run prims x b table (simulateQ worldLocalize (next r.1)) r.2) := by
  simp only [run, simulateQ_bind, StateT.run_bind]

end CountedPosterior

namespace PrivateRecord

def restoreOutcome {α : Type} (hidden : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (offset : ℕ) (r : α × PublicContinuation.State C) : α × PublicContinuation.State C :=
  (r.1, restore hidden (shift offset r.2))

/-- Erase the private cache and cost only after fixing its supported outcome.
The restored execution retains the exact original full cache and counter. -/
theorem private_bind_bound (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    {α β : Type} (table : ProtectedSlot C → HashOutput)
    (hidden : OracleComp (LocalSpec C) α) (next : α → OracleComp (LocalSpec C) β)
    (visible : OracleComp (LocalSpec C) β) (s : PublicContinuation.State C)
    (hagrees : s.1.AgreesWithFn table)
    (hnext : ∀ r ∈ support (CountedPosterior.run prims x b table hidden s), next r.1 = visible)
    (hraw : ∀ r ∈ support (CountedPosterior.run prims x b table hidden s), r.2.2.1 = s.2.1)
    (event publicEvent : β × PublicContinuation.State C → Prop)
    (htransport : ∀ p ∈ support (CountedPosterior.run prims x b table hidden s),
      ∀ r ∈ support (CountedPosterior.run prims x b table visible (s.1, s.2.1, 0)),
        event (restoreOutcome p.2.1 p.2.2.2 r) → publicEvent r) :
    Pr[event | CountedPosterior.run prims x b table (hidden >>= next) s] ≤
      Pr[publicEvent | CountedPosterior.run prims x b table visible (s.1, s.2.1, 0)] := by
  simp only [CountedPosterior.run, simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro p hp
  have hle := (FinitePosterior.eager_cache CountedPosterior.aux
    CountedPosterior.aux_preserves table
    (simulateQ (CountedPosterior.localQuery prims x b) hidden) s hagrees p hp).1
  rw [hnext p hp]
  have hs : p.2 = (p.2.1, s.2.1, p.2.2.2) := by rw [← hraw p hp]
  rw [hs, run_restore_shift p.2.1 s.1 hle, probEvent_map]
  exact probEvent_mono (fun r hr he => htransport p hp r hr he)

end PrivateRecord

namespace GateProbability

set_option backward.isDefEq.respectTransparency false in
/-- Quantitative closure after the genuine selected private block. The sole
transport premise is pointwise on supported actual/private and reset/visible
executions; neither the private count nor its cache is averaged prematurely. -/
theorem after_private_bound (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (next : List (List Bit) → OracleComp (LocalSpec C) α)
    (cache : HashCache C) (n q : ℕ)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hq : q < 2 ^ 127)
    (event : (ProtectedSlot C → HashOutput) → α × PublicContinuation.State C → Prop)
    (htransport : ∀ h : ProtectedSlot C → HashOutput,
      let s : PublicContinuation.State C :=
        ((ProtectedRouting.split (protectedInput x b) cache).1,
          (ProtectedRouting.split (protectedInput x b) cache).2, n)
      let table := tableExtending s.1 h
      ∀ p ∈ support (CountedPosterior.run prims x b table
        (liftComp ((SelectedKeygen.jobs b).mapM
          (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)) s),
      ∀ r ∈ support (CountedPosterior.run prims x b table
        (next ((List.finRange numChains).map fun l => bitsOfDigest (SelectedKeygen.endpoints table b l)))
        (s.1, s.2.1, 0)),
      event table (PrivateRecord.restoreOutcome p.2.1 p.2.2.2 r) →
        Good b (SelectedKeygen.endpoints table b) q r table) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => event p.2 p.1 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← CountedPosterior.run prims x b table (do
        let outputs ← liftComp ((SelectedKeygen.jobs b).mapM
          (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)
        next outputs) s
      pure (r, table)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  dsimp only
  let s : PublicContinuation.State C :=
    ((ProtectedRouting.split (protectedInput x b) cache).1,
      (ProtectedRouting.split (protectedInput x b) cache).2, n)
  let visible := fun target : ChainIndex → Digest =>
    next ((List.finRange numChains).map fun l => bitsOfDigest (target l))
  apply le_trans (b := Pr[fun p => Good b (SelectedKeygen.endpoints p.2 b) q p.1 p.2 | do
    let h ← $ᵗ (ProtectedSlot C → HashOutput)
    let table := tableExtending s.1 h
    let r ← CountedPosterior.run prims x b table (visible (SelectedKeygen.endpoints table b))
      (s.1, s.2.1, 0)
    pure (r, table)])
  · simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map]
    apply ENNReal.tsum_le_tsum
    intro h
    apply mul_le_mul_left'
    apply PrivateRecord.private_bind_bound prims x b _ _ _ _ s (FinitePosterior.extending_agrees _ _)
    · intro p hp
      rw [(SelectedKeygen.counted_jobs_support prims x b hno _ s p hp).1]
    · intro p hp
      exact (SelectedKeygen.counted_jobs_support prims x b hno _ s p hp).2
    · exact htransport h
  · exact adaptive_endpoint_bound prims x b hno visible
      (fun table => SelectedKeygen.endpoints table b) cache 0 hempty q hq

end GateProbability

namespace CanonicalCompletion

open Classical

def answer (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput) (cache : HashCache C) : Query C → HashOutput :=
  fun input => if h : ∃ slot, protectedInput x b slot = input
    then table h.choose else SigningCacheProof.answersOf cache input

theorem answer_protected (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (cache : HashCache C) (slot : ProtectedSlot C) :
    answer x b table cache (protectedInput x b slot) = table slot := by
  unfold answer
  split_ifs with h
  · rw [protectedInput_injective x b hno h.choose_spec]
  · exact (h ⟨slot, rfl⟩).elim

theorem answer_agrees (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (cache : HashCache C)
    (hagree : (ProtectedRouting.split (protectedInput x b) cache).1.AgreesWithFn table) :
    cache.AgreesWithFn (answer x b table cache) := by
  intro input value hv
  by_cases h : ∃ slot, protectedInput x b slot = input
  · obtain ⟨slot, rfl⟩ := h
    rw [answer_protected x b hno]
    exact hagree hv
  · simp [answer, h, SigningCacheProof.answersOf, hv]

set_option backward.isDefEq.respectTransparency false in
theorem eval_answer_start (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (cache : HashCache C) (l : ChainIndex) :
    evalWithAnswerFn (answer x b table cache)
      (forestValue x.2.1 (.chain topLayer (topKey b) l (digit 0))) =
      SelectedKeygen.starts table b l := by
  rw [forestValue, evalWithAnswerFn_bind, eval_mapM]
  simp only [evalWithAnswerFn_pure]
  apply congrArg (fun values : List Digest => values.foldl (· ^^^ ·) 0)
  apply List.map_congr_left
  intro T _
  rw [evalWithAnswerFn_map, DeterministicSigning.eval_liftM_query]
  exact congrArg truncateHash (answer_protected x b hno table cache
    (.inl (.inl (T, .chain topLayer (topKey b) l (digit 0)))))

theorem starts_of_resolved_top (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (cache : HashCache C) (top : TopTree)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (hagree : (ProtectedRouting.split (protectedInput x b) cache).1.AgreesWithFn table) :
    SelectedKeygen.starts table b = fun l => path prims x cache b l 0 := by
  funext l
  obtain ⟨start, finish, hs, _⟩ := resolves_referenceTop_chains x cache top htop b l
  have hv := hs.eval (answer x b table cache) (answer_agrees x b hno table cache hagree)
  rw [eval_answer_start x b hno table cache l] at hv
  simp only [path, XmssSecurity.Wots.walk, replayStarts]
  exact hv.trans (resolves_forestValue prims cache cache le_rfl _ _ _ hs).symm

set_option backward.isDefEq.respectTransparency false in
theorem path_cached (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (cache : HashCache C) (top : TopTree)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (l : ChainIndex) (k : XmssSecurity.ChainStep) :
    (cache (protectedInput x b (.inr (l, k, path prims x cache b l k.val)))).isSome := by
  have hc := SigningCacheProof.resolves_topChainWalk 0 _ 3 _
    (resolves_referenceTop_modelChains prims x cache top htop b l) k.val
    (Nat.zero_le _) (show k.val < 0 + 3 from k.isLt) k.isLt
  simpa only [Nat.sub_zero, path, protectedInput, SigningDescentProof.thView] using hc

set_option backward.isDefEq.respectTransparency false in
theorem table_path (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (cache : HashCache C) (top : TopTree)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (hagree : (ProtectedRouting.split (protectedInput x b) cache).1.AgreesWithFn table)
    (l : ChainIndex) : ∀ j, j ≤ 3 →
      XmssSecurity.Wots.walk (SelectedKeygen.step table l) 0 j (SelectedKeygen.starts table b l) =
        path prims x cache b l j := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [XmssSecurity.Wots.walk] using congrFun
      (starts_of_resolved_top prims x b hno table cache top htop hagree) l
  | succ j ih =>
    intro hj
    have hj' : j < 3 := by omega
    have hjchain : j < XmssSecurity.chainLength - 1 := hj'
    rw [XmssSecurity.Wots.walk, ih (by omega)]
    obtain ⟨value, hv⟩ := Option.isSome_iff_exists.mp (path_cached prims x b cache top htop l ⟨j, hj'⟩)
    have ht := hagree hv
    have hd := XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some
      (show SigningDescentProof.thView cache
        (XmssSecurity.Concrete.CacheView.topChainInput x.1 b l ⟨j, hj'⟩
          (path prims x cache b l j)) = some value from hv)
    simp only [SelectedKeygen.step, Nat.zero_add, dif_pos hj', ht]
    simpa only [path, XmssSecurity.Wots.walk, Nat.zero_add,
      XmssSecurity.Concrete.CacheView.topChainStep, hjchain, ↓reduceDIte,
      truncateHash, XmssSecurity.truncateHash, digestBits, XmssSecurity.digestBits] using hd.symm

/-- Table paths agree with the completed canonical paths because the actual
key-generation prefix has already cached every cell of those paths. -/
theorem table_path_extension (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (cache larger : HashCache C)
    (hle : cache ≤ larger) (top : TopTree)
    (htop : DeterministicSigning.Resolves cache
      (referenceTree forestHash (forestValue x.2.1) x.1 emptyTop .top) (some (.top top)))
    (hagree : (ProtectedRouting.split (protectedInput x b) cache).1.AgreesWithFn table) :
    (∀ l j, j ≤ 3 →
      XmssSecurity.Wots.walk (SelectedKeygen.step table l) 0 j (SelectedKeygen.starts table b l) =
        path prims x larger b l j) ∧
    (∀ (l : ChainIndex) (k : XmssSecurity.ChainStep) value,
      larger (protectedInput x b (.inr (l, k, path prims x larger b l k.val))) = some value →
        table (.inr (l, k, path prims x larger b l k.val)) = value) := by
  have hp (l : ChainIndex) (j : ℕ) (hj : j ≤ 3) :
      path prims x larger b l j = path prims x cache b l j :=
    resolves_referenceTop_walks prims x cache larger hle top htop b l j hj
  constructor
  · intro l j hj
    exact (table_path prims x b hno table cache top htop hagree l j hj).trans (hp l j hj).symm
  · intro l k value hv
    rw [hp l k.val (Nat.le_of_lt k.isLt)] at hv ⊢
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp (path_cached prims x b cache top htop l k)
    have he := Option.some.inj ((hle hv').symm.trans hv)
    exact (hagree hv').trans he

end CanonicalCompletion

namespace GateProbability

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
/-- The deterministic transport to the posterior event. Verification must
resolve in the reset observed cache; private restored cells supply only the
canonical completion, never public verification depth. -/
theorem good_of_exception (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : ((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × LoggedState C)
    (hz : z ∈ support (loggedRun prims A x)) (hex : ForestExceptionAt prims x b z)
    (observed : HashCache C) (hobs : observed ≤ z.2.1.1)
    (table : ProtectedSlot C → HashOutput)
    (hagree : (ProtectedRouting.split (protectedInput x b) z.2.1.1).1.AgreesWithFn table)
    (hallowed : ∃ D : Finset C.Party, D.card ≤ C.t - 1 ∧
      UnopenedPrivacy.RecordAllowed D (UnopenedPrivacy.topStarts b)
        (ProtectedRouting.split (protectedInput x b) observed).1)
    (hverify : ∀ top state forgery, z.1.2 = some (top, state, forgery) →
      ∃ verified, DeterministicSigning.Resolves (SigningDescentProof.thView observed)
        (XmssSecurity.Concrete.verify ⟨top.root, x.1⟩ forgery.signature.leafIndex forgery.message
          (XmssSecurity.Bridge.toModelSig forgery.signature) : OracleComp XmssSecurity.HashSpec _) verified)
    {α : Type} (out : α) (count q : ℕ) (hcount : count ≤ q) :
    Good b (SelectedKeygen.endpoints table b) q
      (out, (ProtectedRouting.split (protectedInput x b) observed).1,
        (ProtectedRouting.split (protectedInput x b) observed).2, count) table := by
  obtain ⟨completed, hc, hcollision, top, state, forgery, hsome, encoding,
    hvalid, _, hauth, hcode, _⟩ := forestException_authentic prims A x z hz hex.1
  have hgrow := (recordReads_resolves (forestRun x) ∅ z.2.1.1
    (by intro input value hv; cases hv) completed hc).1
  obtain ⟨top', state', forgery', hsome', hb⟩ := hex.2
  have he := Option.some.inj (hsome'.symm.trans hsome)
  cases he
  have hfull : (z.1, z.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
    rw [← loggedRun_forget, support_map]
    exact ⟨z, hz, rfl⟩
  have htop := exposedRun_top_resolves prims A x (z.1, z.2.1) hfull hex.1.1.1 top state forgery hsome
  obtain ⟨hpaths, hcells⟩ := CanonicalCompletion.table_path_extension prims x b hno table
    z.2.1.1 completed.2 hgrow top htop hagree
  have hstart : SelectedKeygen.starts table b = fun l =>
      CanonicalCompletion.path prims x completed.2 b l 0 := by
    funext l
    exact hpaths l 0 (by omega)
  have hend : SelectedKeygen.endpoints table b = fun l =>
      CanonicalCompletion.path prims x completed.2 b l 3 := by
    funext l
    exact hpaths l 3 le_rfl
  have hmarked := CanonicalCompletion.marked_of_noCollision prims x observed completed.2
    (hobs.trans hgrow) hcollision b table hstart
    (CanonicalCompletion.path_cached prims x b completed.2 top (htop.mono hgrow)) hcells
  obtain ⟨verified, hverified⟩ := hverify top state forgery hsome
  obtain ⟨bottomEncoding, hbottom, htopcode⟩ := hcode
  have hsuffix := (resolves_verify_topWalks observed z.2.1.1 hobs ⟨top.root, x.1⟩
    forgery.signature.leafIndex forgery.message (XmssSecurity.Bridge.toModelSig forgery.signature)
    verified hverified bottomEncoding encoding hbottom htopcode).2
  rw [hb] at hauth hsuffix
  have hterminal := observedTopRows_terminal prims x observed completed.2
    (hobs.trans hgrow) hcollision b encoding hvalid
    (XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue hauth hsuffix count q hcount
  refine ⟨hallowed, ?_, ?_⟩
  · simpa only [hend] using hmarked
  · rw [hend]
    exact hterminal

end GateProbability

namespace PublicVerification

abbrev Output (C : Committee) :=
  (Bool × Bool) × Option (TopTree × TsigState C × Forgery)

/-- The verifier is the last public operation needed to recognize a win.
The freshness computation is left in a separate continuation. -/
def verify (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (r : Forgery × TsigState C × Bool) : OracleComp (WorldSpec C) (Output C) :=
  (fun verified => ((verified, r.2.2), some (top, r.2.1, r.1))) <$>
    SigningSecurityProof.liftFree (tweakable
      (Concrete.verify ⟨top.root, x.1⟩ r.1.message r.1.signature))

def freshness (x : SigningSecurityProof.Keys3 C) : Output C →
    OracleComp (WorldSpec C) (Output C)
  | (flags, none) => pure (flags, none)
  | (flags, some (top, st, forgery)) => do
      let fresh ← if (signersAt st forgery.signature.leafIndex forgery.message).card < C.t
        then pure true else do
          let honest ← honestSignature (fun oa => SigningSecurityProof.liftFree oa)
            (actualDealt x top) forgery.signature.leafIndex forgery.message
          pure (decide (honest ≠ some forgery.signature))
      pure ((flags.1 && fresh, flags.2), some (top, st, forgery))

set_option maxRecDepth 100000 in
theorem finish_factor (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (r : Forgery × TsigState C × Bool) :
    (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
        SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1) =
      verify x top r >>= freshness x := by
  simp only [SigningCoreProof.tsigFinish, verify, bind_map_left, map_bind,
    freshness, map_pure, bind_assoc]
  apply bind_congr
  intro verified
  split_ifs <;> simp only [map_bind, map_pure, pure_bind] <;> rfl

/-- Stop before semantic opening, then retain the actual verification reads. -/
def tail (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) : Option TreeOutput → OracleComp (WorldSpec C) (Output C)
  | some (.top top) => do
      let some r ← unopenedRun x top b (A ⟨top.root, x.1⟩ top) (SigningCoreProof.tsigInit, false)
        | pure ((false, false), none)
      verify x top r
  | _ => pure ((false, false), none)

set_option maxRecDepth 100000 in
theorem unopened_factor (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) :
    unopenedFinalRun A x b = (do
      let output ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top
      let verified ← tail A x b output
      freshness x verified) := by
  unfold unopenedFinalRun
  apply bind_congr
  rintro (_ | (top | bottom))
  · simp [tail, freshness]
  · simp only [tail, bind_assoc]
    apply bind_congr
    rintro (_ | r)
    · simp [freshness]
    · exact finish_factor x top r
  · simp [tail, freshness]

def checkedTail (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) : OracleComp (WorldSpec C) (Output C) :=
  tail A x b output >>= freshness x

/-- The real stopped continuation after one private key block. -/
def afterOutputs (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex)
    (left selected : List (List Bit)) : OracleComp (WorldSpec C) (Output C) := do
  let right ← SigningSecurityProof.liftFree ((after.flatMap SelectedKeygen.jobs).mapM
    (referenceJob tweakable (prfValue x.2.1) x.1))
  let output ← SigningSecurityProof.liftFree (SelectedKeygen.finish (tweakable (C := C)) x.1
    (left ++ selected ++ right))
  checkedTail A x b output

/-- For a fixed endpoint vector this is a genuine local-oracle program.
The selected private block is absent from its observation record. -/
def afterSelected (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex)
    (left : List (List Bit)) (target : ChainIndex → Digest) :
    OracleComp (LocalSpec C) (Output C) :=
  simulateQ worldLocalize (afterOutputs A x b after left
    ((List.finRange numChains).map fun l => bitsOfDigest (target l)))

set_option maxRecDepth 100000 in
theorem unopened_split (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (before after : List XmssSecurity.TopIndex)
    (hsplit : topJobs = before.flatMap SelectedKeygen.jobs ++ SelectedKeygen.jobs b ++
      after.flatMap SelectedKeygen.jobs) :
    unopenedFinalRun A x b = (do
      let left ← SigningSecurityProof.liftFree ((before.flatMap SelectedKeygen.jobs).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1))
      let selected ← SigningSecurityProof.liftFree ((SelectedKeygen.jobs b).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1))
      afterOutputs A x b after left selected) := by
  rw [unopened_factor]
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  rw [SelectedKeygen.referenceTree_split tweakable (prfValue x.2.1) x.1 emptyTop before after b hsplit]
  simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind, bind_assoc, afterOutputs, checkedTail]

set_option backward.isDefEq.respectTransparency false in
theorem localize_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ worldLocalize (free oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [free, simulateQ_pure]
  | query_bind t k ih =>
    simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map] at ih ⊢
    simp only [HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, worldLocalize]
    congr 1
    funext u
    exact ih u

theorem localize_liftFree {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ worldLocalize (SigningSecurityProof.liftFree oa) = liftComp oa (LocalSpec C) :=
  localize_free _


set_option backward.isDefEq.respectTransparency false in
theorem safe_counted_ro (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (table : ProtectedSlot C → HashOutput) (D : Finset C.Party) (challenged : Finset Point)
    {α : Type} (oa : OracleComp (RoSpec C) α)
    (hsafe : UnopenedPrivacy.SafeRo prims x b table D challenged oa)
    (s : PublicContinuation.State C) (hs : UnopenedPrivacy.RecordAllowed D challenged s.1)
    (r : α × PublicContinuation.State C)
    (hr : r ∈ support (CountedPosterior.run prims x b table (liftComp oa (LocalSpec C)) s)) :
    UnopenedPrivacy.RecordAllowed D challenged r.2.1 := by
  have hm : (r.1, r.2.1, r.2.2.1) ∈ support
      ((UnopenedPrivacy.recordRo prims x b table oa).run (s.1, s.2.1)) := by
    change (r.1, r.2.1, r.2.2.1) ∈ support
      ((simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b) (liftComp oa (LocalSpec C)))).run (s.1, s.2.1))
    rw [CountedPosterior.eager_forget_run prims x b table _ s, support_map]
    exact ⟨r, hr, rfl⟩
  exact hsafe (s.1, s.2.1) hs _ hm

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem tail_counted_view (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (output : Option TreeOutput)
    (s : PublicContinuation.State C)
    (hs : UnopenedPrivacy.ViewInvariant b (SigningCoreProof.tsigInit, false) s.1)
    (r : Output C × PublicContinuation.State C)
    (hr : r ∈ support (CountedPosterior.run prims x b table (simulateQ worldLocalize (tail A x b output)) s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) :
    UnopenedPrivacy.ViewInvariant b (state, r.1.1.2) r.2.1 := by
  rcases output with _ | (top' | bottom)
  · simp [tail, CountedPosterior.run] at hr
    subst r
    cases hsome
  · simp only [tail, CountedPosterior.run, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    rcases he : v.1 with _ | value
    · simp only [he, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      cases hsome
    · rw [he] at hr
      have hinv := UnopenedPrivacy.unopenedRun_counted_view prims x b hno table top'
        (A ⟨top'.root, x.1⟩ top') (SigningCoreProof.tsigInit, false) s hs v hv value he
      simp only [verify, simulateQ_map, localize_liftFree, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨w, hw, rfl⟩ := hr
      have htuple := Option.some.inj hsome
      rcases htuple with ⟨rfl, rfl, rfl⟩
      refine ⟨hinv.1, fun hflag => ?_⟩
      exact safe_counted_ro prims x b table value.2.1.corrupt (UnopenedPrivacy.topStarts b) _
        (UnopenedPrivacy.safe_tweakable prims x b hno table value.2.1.corrupt
          (UnopenedPrivacy.topStarts b) _) v.2 (hinv.2 hflag) w hw
  · simp [tail, CountedPosterior.run] at hr
    subst r
    cases hsome


theorem freshness_metadata {σ : Type} (W : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (x : SigningSecurityProof.Keys3 C) (out : Output C) (s : σ)
    (r : Output C × σ) (hr : r ∈ support ((simulateQ W (freshness x out)).run s)) :
    r.1.2 = out.2 ∧ r.1.1.2 = out.1.2 := by
  rcases out with ⟨flags, _ | ⟨top, state, forgery⟩⟩
  · simp only [freshness, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, rfl⟩
  · simp only [freshness] at hr
    split_ifs at hr
    · simp only [pure_bind, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨rfl, rfl⟩
    · simp only [pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨v, _, rfl⟩ := hr
      exact ⟨rfl, rfl⟩

theorem freshness_of_fresh (x : SigningSecurityProof.Keys3 C) (out : Output C)
    (hfresh : ∀ top state forgery, out.2 = some (top, state, forgery) →
      (signersAt state forgery.signature.leafIndex forgery.message).card < C.t) :
    freshness x out = pure out := by
  rcases out with ⟨flags, _ | ⟨top, state, forgery⟩⟩
  · rfl
  · simp only [freshness, if_pos (hfresh top state forgery rfl), pure_bind, Bool.and_true]

set_option backward.isDefEq.respectTransparency false in
theorem safe_other_jobs (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (D : Finset C.Party)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) :
    UnopenedPrivacy.SafeRo prims x b table D (UnopenedPrivacy.topStarts b)
      ((after.flatMap SelectedKeygen.jobs).mapM (referenceJob tweakable (prfValue x.2.1) x.1)) := by
  apply UnopenedPrivacy.safe_mapM
  intro job hj
  obtain ⟨b', hb', hj⟩ := List.mem_flatMap.mp hj
  apply UnopenedPrivacy.safe_referenceJob prims x b hno table D (UnopenedPrivacy.topStarts b)
  intro p hp
  exact SelectedKeygen.jobs_avoid b b' (fun he => hb (he ▸ hb')) job hj p hp

theorem safe_finish (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (D : Finset C.Party) (outputs : List (List Bit)) :
    UnopenedPrivacy.SafeRo prims x b table D (UnopenedPrivacy.topStarts b)
      (SelectedKeygen.finish (tweakable (C := C)) x.1 outputs) := by
  unfold SelectedKeygen.finish
  apply UnopenedPrivacy.safe_bind
  · exact UnopenedPrivacy.safe_tweakable prims x b hno table D (UnopenedPrivacy.topStarts b) _
  · intro root
    exact UnopenedPrivacy.safe_pure prims x b table D (UnopenedPrivacy.topStarts b) _

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem checkedTail_counted_view (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (output : Option TreeOutput)
    (s : PublicContinuation.State C)
    (hs : UnopenedPrivacy.ViewInvariant b (SigningCoreProof.tsigInit, false) s.1)
    (r : Output C × PublicContinuation.State C)
    (hr : r ∈ support (CountedPosterior.run prims x b table
      (simulateQ worldLocalize (checkedTail A x b output)) s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery))
    (hfresh : (signersAt state forgery.signature.leafIndex forgery.message).card < C.t) :
    UnopenedPrivacy.ViewInvariant b (state, r.1.1.2) r.2.1 := by
  simp only [checkedTail, CountedPosterior.run, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨verified, hverified, hr⟩ := hr
  have hmeta := freshness_metadata
    (FinitePosterior.eager table CountedPosterior.aux ∘ₛ
      CountedPosterior.localQuery prims x b ∘ₛ worldLocalize) x verified.1 verified.2 r
    (by
      rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose] at hr
      exact hr)
  have hverifiedSome : verified.1.2 = some (top, state, forgery) := hmeta.1.symm.trans hsome
  have he := freshness_of_fresh x verified.1 (by
    intro top' state' forgery' hh
    have ht := Option.some.inj (hverifiedSome.symm.trans hh)
    cases ht
    exact hfresh)
  rw [he] at hr
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  apply tail_counted_view prims A x b hno table output s hs verified hverified top state forgery hverifiedSome

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem ro_prefix_checkedTail_view (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) {β : Type}
    (first : OracleComp (RoSpec C) β) (second : β → OracleComp (RoSpec C) (Option TreeOutput))
    (hfirst : UnopenedPrivacy.SafeRo prims x b table ∅ (UnopenedPrivacy.topStarts b) first)
    (hsecond : ∀ value, UnopenedPrivacy.SafeRo prims x b table ∅ (UnopenedPrivacy.topStarts b) (second value))
    (s : PublicContinuation.State C)
    (hs : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b) s.1)
    (r : Output C × PublicContinuation.State C)
    (hr : r ∈ support (CountedPosterior.run prims x b table (simulateQ worldLocalize (do
      let value ← SigningSecurityProof.liftFree first
      let output ← SigningSecurityProof.liftFree (second value)
      checkedTail A x b output)) s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery))
    (hfresh : (signersAt state forgery.signature.leafIndex forgery.message).card < C.t) :
    UnopenedPrivacy.ViewInvariant b (state, r.1.1.2) r.2.1 := by
  rw [CountedPosterior.run_world_bind, mem_support_bind_iff] at hr
  obtain ⟨value, hvalue, hr⟩ := hr
  rw [CountedPosterior.run_world_bind, mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [localize_liftFree] at hvalue houtput
  have hvalueSafe := safe_counted_ro prims x b table ∅ (UnopenedPrivacy.topStarts b) first
    hfirst s hs value hvalue
  have houtputSafe := safe_counted_ro prims x b table ∅ (UnopenedPrivacy.topStarts b) (second value.1)
    (hsecond value.1) value.2 hvalueSafe output houtput
  apply checkedTail_counted_view prims A x b hno table output.1 output.2 _ r hr top state forgery hsome hfresh
  exact ⟨by simp [SigningCoreProof.tsigInit], fun _ => houtputSafe⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
/-- On the exceptional fresh branch the actual final continuation preserves
allowed reads; its post-verification freshness check makes no further query. -/
theorem afterOutputs_counted_view (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (after : List XmssSecurity.TopIndex) (hb : b ∉ after)
    (left selected : List (List Bit)) (s : PublicContinuation.State C)
    (hs : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b) s.1)
    (r : Output C × PublicContinuation.State C)
    (hr : r ∈ support (CountedPosterior.run prims x b table
      (simulateQ worldLocalize (afterOutputs A x b after left selected)) s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery))
    (hfresh : (signersAt state forgery.signature.leafIndex forgery.message).card < C.t) :
    UnopenedPrivacy.ViewInvariant b (state, r.1.1.2) r.2.1 := by
  exact ro_prefix_checkedTail_view prims A x b hno table
    ((after.flatMap SelectedKeygen.jobs).mapM (referenceJob tweakable (prfValue x.2.1) x.1))
    (fun right => SelectedKeygen.finish (tweakable (C := C)) x.1 (left ++ selected ++ right))
    (by exact safe_other_jobs prims x b hno table ∅ after hb)
    (by intro right; exact safe_finish prims x b hno table ∅ _)
    s hs r hr top state forgery hsome hfresh




set_option maxRecDepth 100000 in
theorem programFree_checkedTail (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) :
    ProgramFree (checkedTail A x b output) := by
  unfold checkedTail
  rcases output with _ | (top | bottom)
  · simpa only [tail, pure_bind, freshness] using programFree_pure (C := C) ((false, false), none)
  · simp only [tail, bind_assoc]
    apply programFree_bind _ _ (programFree_unopenedRun x top b _ _)
    rintro (_ | r)
    · simpa only [pure_bind, freshness] using programFree_pure (C := C) ((false, false), none)
    · rw [← finish_factor]
      exact programFree_map _ _ (programFree_finish x top _)
  · simpa only [tail, pure_bind, freshness] using programFree_pure (C := C) ((false, false), none)

theorem programFree_ro_checkedTail (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) {β : Type} (first : OracleComp (RoSpec C) β)
    (second : β → OracleComp (RoSpec C) (Option TreeOutput)) :
    ProgramFree (do
      let value ← SigningSecurityProof.liftFree first
      let output ← SigningSecurityProof.liftFree (second value)
      checkedTail A x b output) := by
  apply programFree_bind _ _ (programFree_liftFree _)
  intro value
  apply programFree_bind _ _ (programFree_liftFree _)
  intro output
  exact programFree_checkedTail A x b output

theorem programFree_afterOutputs (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (left selected : List (List Bit)) :
    ProgramFree (afterOutputs A x b after left selected) :=
  programFree_ro_checkedTail A x b _ _

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem tail_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) (s : HashCache C × ℕ)
    (r : Output C × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (tail A x b output)).run s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) :
    ∃ verified, DeterministicSigning.Resolves (SigningDescentProof.thView r.2.1)
      (XmssSecurity.Concrete.verify ⟨top.root, x.1⟩ forgery.signature.leafIndex forgery.message
        (XmssSecurity.Bridge.toModelSig forgery.signature) : OracleComp XmssSecurity.HashSpec _) verified := by
  rcases output with _ | (top' | bottom)
  · simp [tail] at hr
    subst r
    cases hsome
  · simp only [tail, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    rcases he : v.1 with _ | value
    · simp only [he, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      cases hsome
    · rw [he] at hr
      simp only [verify, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨w, hw, rfl⟩ := hr
      have ht := Option.some.inj hsome
      rcases ht with ⟨rfl, rfl, rfl⟩
      have hresolved := SigningCacheProof.run_liftFree_tweakable prims _ v.2 w hw
      rw [XmssSecurity.Bridge.verify_real] at hresolved
      exact ⟨w.1, hresolved⟩
  · simp [tail] at hr
    subst r
    cases hsome

set_option maxRecDepth 100000 in
theorem checkedTail_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) (s : HashCache C × ℕ)
    (r : Output C × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (checkedTail A x b output)).run s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) :
    ∃ verified, DeterministicSigning.Resolves (SigningDescentProof.thView r.2.1)
      (XmssSecurity.Concrete.verify ⟨top.root, x.1⟩ forgery.signature.leafIndex forgery.message
        (XmssSecurity.Bridge.toModelSig forgery.signature) : OracleComp XmssSecurity.HashSpec _) verified := by
  obtain ⟨v, hv, hr⟩ := SigningCacheProof.run_bind_support prims _ _ s r hr
  have hmeta := freshness_metadata (SigningCacheProof.countImpl prims) x v.1 v.2 r hr
  obtain ⟨verified, hverified⟩ := tail_resolves prims A x b output s v hv top state forgery
    (hmeta.1.symm.trans hsome)
  exact ⟨verified, hverified.mono (SigningCacheProof.thView_mono
    (SigningCacheProof.countRun_grows prims (freshness x v.1) v.2 r hr))⟩

/-- Verification resolution composes through arbitrary honest prefixes.
Keeping those prefixes abstract avoids expanding concrete tree computations. -/
theorem ro_prefix_checkedTail_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) {β : Type}
    (first : OracleComp (RoSpec C) β) (second : β → OracleComp (RoSpec C) (Option TreeOutput))
    (s : HashCache C × ℕ) (r : Output C × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (do
      let value ← SigningSecurityProof.liftFree first
      let output ← SigningSecurityProof.liftFree (second value)
      checkedTail A x b output)).run s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) :
    ∃ verified, DeterministicSigning.Resolves (SigningDescentProof.thView r.2.1)
      (XmssSecurity.Concrete.verify ⟨top.root, x.1⟩ forgery.signature.leafIndex forgery.message
        (XmssSecurity.Bridge.toModelSig forgery.signature) : OracleComp XmssSecurity.HashSpec _) verified := by
  obtain ⟨value, _, hr⟩ := SigningCacheProof.run_bind_support prims _ _ s r hr
  obtain ⟨output, _, hr⟩ := SigningCacheProof.run_bind_support prims _ _ value.2 r hr
  exact checkedTail_resolves prims A x b output.1 output.2 r hr top state forgery hsome

theorem afterOutputs_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (left selected : List (List Bit))
    (s : HashCache C × ℕ) (r : Output C × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (afterOutputs A x b after left selected)).run s))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hsome : r.1.2 = some (top, state, forgery)) :
    ∃ verified, DeterministicSigning.Resolves (SigningDescentProof.thView r.2.1)
      (XmssSecurity.Concrete.verify ⟨top.root, x.1⟩ forgery.signature.leafIndex forgery.message
        (XmssSecurity.Bridge.toModelSig forgery.signature) : OracleComp XmssSecurity.HashSpec _) verified :=
  ro_prefix_checkedTail_resolves prims A x b _ _ s r hr top state forgery hsome


end PublicVerification

namespace ProtectedRouting

theorem split_le {D E R : Type} (f : D → E) (left right : QueryCache (E →ₒ R))
    (h₁ : (split f left).1 ≤ (split f right).1)
    (h₂ : (split f left).2 ≤ (split f right).2) : left ≤ right := by
  classical
  intro input value hv
  rcases Classical.em (∃ d : D, f d = input) with h | h
  · obtain ⟨d, rfl⟩ := h
    exact h₁ hv
  · have hl : (split f left).2 input = left input := by simp [split, h]
    have hr : (split f right).2 input = right input := by simp [split, h]
    exact hr.symm.trans (h₂ (hl.trans hv))

theorem split_mono {D E R : Type} (f : D → E) {left right : QueryCache (E →ₒ R)}
    (h : left ≤ right) : (split f left).1 ≤ (split f right).1 ∧
      (split f left).2 ≤ (split f right).2 := by
  classical
  refine ⟨fun {_} {_} hv => h hv, ?_⟩
  intro input value hv
  rcases Classical.em (∃ d : D, f d = input) with he | he
  · simp [split, he] at hv
  · simpa only [split, he, ↓reduceIte] using h (by simpa only [split, he, ↓reduceIte] using hv)

end ProtectedRouting

namespace CountedPosterior

/-- A reset eager run has an actual raw-cache realization, with exactly the
same outputs and original local-query count. -/
theorem eager_local_support (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (cache : HashCache C) (n : ℕ)
    (h : ProtectedSlot C → HashOutput) (r : α × PublicContinuation.State C)
    (hr : r ∈ support (run prims x b
      (tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h) oa
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n))) :
    ∃ v ∈ support ((simulateQ (withLocalCount (signingLocalAnswer prims)) oa).run (cache, n)),
      r = (v.1, (ProtectedRouting.split (protectedInput x b) v.2.1).1,
        (ProtectedRouting.split (protectedInput x b) v.2.1).2, v.2.2) := by
  have hl := FinitePosterior.eager_support_lazy aux aux_preserves
    (simulateQ (localQuery prims x b) oa)
    ((ProtectedRouting.split (protectedInput x b) cache).1,
      (ProtectedRouting.split (protectedInput x b) cache).2, n) h r hr
  rw [local_lazy_run prims x b hno, support_map] at hl
  obtain ⟨v, hv, he⟩ := hl
  exact ⟨v, hv, he.symm⟩

theorem eager_world_support (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hfree : ProgramFree oa) (cache : HashCache C) (n : ℕ)
    (h : ProtectedSlot C → HashOutput) (r : α × PublicContinuation.State C)
    (hr : r ∈ support (run prims x b
      (tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h)
      (simulateQ worldLocalize oa)
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n))) :
    ∃ v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) oa).run (cache, n)),
      r = (v.1, (ProtectedRouting.split (protectedInput x b) v.2.1).1,
        (ProtectedRouting.split (protectedInput x b) v.2.1).2, v.2.2) := by
  rw [programFree_count_local prims oa hfree]
  exact eager_local_support prims x b hno _ cache n h r hr

end CountedPosterior

namespace PrivateRecord

theorem observed_le_merge {D R : Type} (hidden observed : QueryCache (D →ₒ R)) :
    observed ≤ merge hidden observed := by
  intro d value hv
  simp [merge, hv]

end PrivateRecord

namespace PublicVerification

/-- The public run's verifier has actually queried every resolved cell in its
reset raw cache. This statement uses no restored private cells. -/
theorem reset_observed_witness (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (left selected : List (List Bit))
    (cache : HashCache C) (h : ProtectedSlot C → HashOutput)
    (r : Output C × PublicContinuation.State C)
    (hr : r ∈ support (CountedPosterior.run prims x b
      (tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h)
      (simulateQ worldLocalize (afterOutputs A x b after left selected))
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, 0))) :
    ∃ observed : HashCache C,
      r.2.1 = (ProtectedRouting.split (protectedInput x b) observed).1 ∧
      r.2.2.1 = (ProtectedRouting.split (protectedInput x b) observed).2 ∧
      ∀ top state forgery, r.1.2 = some (top, state, forgery) →
        ∃ verified, DeterministicSigning.Resolves (SigningDescentProof.thView observed)
          (XmssSecurity.Concrete.verify ⟨top.root, x.1⟩ forgery.signature.leafIndex forgery.message
            (XmssSecurity.Bridge.toModelSig forgery.signature) : OracleComp XmssSecurity.HashSpec _) verified := by
  obtain ⟨v, hv, rfl⟩ := CountedPosterior.eager_world_support prims x b hno
    (afterOutputs A x b after left selected) (programFree_afterOutputs A x b after left selected)
    cache 0 h r hr
  exact ⟨v.2.1, rfl, rfl, fun top state forgery hsome =>
    afterOutputs_resolves prims A x b after left selected (cache, 0) v hv top state forgery hsome⟩

end PublicVerification

namespace PrivateRecord

theorem merge_agrees {D R : Type} (hidden observed : QueryCache (D →ₒ R)) (table : D → R)
    (hh : hidden.AgreesWithFn table) (ho : observed.AgreesWithFn table) :
    (merge hidden observed).AgreesWithFn table := by
  intro d value hv
  cases he : observed d with
  | none =>
    apply hh
    simpa only [merge, he, Option.orElse_none] using hv
  | some v =>
    have hv' : v = value := by simpa only [merge, he, Option.orElse_some, Option.some.injEq] using hv
    exact (ho he).trans hv'

end PrivateRecord

namespace GateProbability

/-- The event carried through cache splitting retains a supported actual
exceptional trace. The transcript itself is irrelevant to the event. -/
def SupportedException (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (r : PublicVerification.Output C × PublicContinuation.State C) : Prop :=
  ∃ z ∈ support (loggedRun prims A x), ForestExceptionAt prims x b z ∧
    r = (z.1, (ProtectedRouting.split (protectedInput x b) z.2.1.1).1,
      (ProtectedRouting.split (protectedInput x b) z.2.1.1).2, z.2.1.2)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
/-- Every supported restored exception yields the reset posterior event.
This discharges the source-specific premise of `after_private_bound`. -/
theorem restored_exception_good (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (cache : HashCache C) (n q : ℕ)
    (hq : ∀ v ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), v.2 ≤ q)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1)
    (h : ProtectedSlot C → HashOutput) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    let table := tableExtending s.1 h
    ∀ p ∈ support (CountedPosterior.run prims x b table
      (liftComp ((SelectedKeygen.jobs b).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)) s),
    ∀ r ∈ support (CountedPosterior.run prims x b table
      (PublicVerification.afterSelected A x b after left (SelectedKeygen.endpoints table b))
      (s.1, s.2.1, 0)),
    SupportedException prims A x b (PrivateRecord.restoreOutcome p.2.1 p.2.2.2 r) →
      Good b (SelectedKeygen.endpoints table b) q r table := by
  intro s table p hp r hr hex
  obtain ⟨z, hz, hex, he⟩ := hex
  have hout := congrArg Prod.fst he
  have hrecord := congrArg (fun u => u.2.1) he
  have hraw := congrArg (fun u => u.2.2.1) he
  have hcounter := congrArg (fun u => u.2.2.2) he
  change r.1 = z.1 at hout
  change PrivateRecord.merge p.2.1 r.2.1 = (ProtectedRouting.split (protectedInput x b) z.2.1.1).1 at hrecord
  change r.2.2.1 = (ProtectedRouting.split (protectedInput x b) z.2.1.1).2 at hraw
  change p.2.2.2 + r.2.2.2 = z.2.1.2 at hcounter
  have hpCache := (FinitePosterior.eager_cache CountedPosterior.aux CountedPosterior.aux_preserves table
    (simulateQ (CountedPosterior.localQuery prims x b) _) s (FinitePosterior.extending_agrees _ _) p hp).2
  have hrCache := (FinitePosterior.eager_cache CountedPosterior.aux CountedPosterior.aux_preserves table
    (simulateQ (CountedPosterior.localQuery prims x b) _) (s.1, s.2.1, 0)
    (FinitePosterior.extending_agrees _ _) r hr).2
  obtain ⟨observed, hobsRecord, hobsRaw, hverified⟩ := PublicVerification.reset_observed_witness
    prims A x b hno after left _ cache h r hr
  have hobs : observed ≤ z.2.1.1 := by
    apply ProtectedRouting.split_le (protectedInput x b)
    · rw [← hobsRecord, ← hrecord]
      exact PrivateRecord.observed_le_merge _ _
    · rw [← hobsRaw, ← hraw]
  have hagree : (ProtectedRouting.split (protectedInput x b) z.2.1.1).1.AgreesWithFn table := by
    rw [← hrecord]
    exact PrivateRecord.merge_agrees _ _ table hpCache hrCache
  obtain ⟨top, state, forgery, hsome, hfresh⟩ := forestException_fresh prims A x z hz hex.1
  have hsome' : r.1.2 = some (top, state, forgery) := (congrArg Prod.snd hout).trans hsome
  have hview := PublicVerification.afterOutputs_counted_view prims A x b hno table after hb left _
    (s.1, s.2.1, 0) hallowed r hr top state forgery hsome' hfresh
  have hflag : r.1.1.2 = false := by
    rw [hout]
    exact congrArg Prod.snd hex.1.1.1
  have hcap : r.2.2.2 ≤ q := by
    have hzcount := exposedRun_count_le prims A x q hq (z.1, z.2.1) (by
      rw [← loggedRun_forget, support_map]
      exact ⟨z, hz, rfl⟩)
    change z.2.1.2 ≤ q at hzcount
    omega
  have hg := good_of_exception prims A x b hno z hz hex observed hobs table hagree
    ⟨state.corrupt, hview.1, by rw [← hobsRecord]; exact hview.2 hflag⟩
    (fun top state forgery hh => hverified top state forgery ((congrArg Prod.snd hout).trans hh))
    r.1 r.2.2.2 q hcap
  simpa only [← hobsRecord, ← hobsRaw] using hg

set_option backward.isDefEq.respectTransparency false in
/-- The genuine selected private block followed by the real stopped public
continuation has exceptional mass at most `2^-128`, conditional on any fresh
allowed preceding cache. No probability premise remains in this bound. -/
theorem private_afterOutputs_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (cache : HashCache C) (n q : ℕ)
    (hq : ∀ v ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), v.2 ≤ q)
    (hsmall : q < 2 ^ 127)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1) :
    let s : PublicContinuation.State C :=
      ((ProtectedRouting.split (protectedInput x b) cache).1,
        (ProtectedRouting.split (protectedInput x b) cache).2, n)
    Pr[fun p => SupportedException prims A x b p.1 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending s.1 h
      let r ← CountedPosterior.run prims x b table (do
        let selected ← liftComp ((SelectedKeygen.jobs b).mapM
          (referenceJob tweakable (prfValue x.2.1) x.1)) (LocalSpec C)
        simulateQ worldLocalize (PublicVerification.afterOutputs A x b after left selected)) s
      pure (r, table)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply after_private_bound prims x b hno _ cache n q hempty hsmall
    (fun _ => SupportedException prims A x b)
  intro h
  exact restored_exception_good prims A x b hno after hb left cache n q hq hallowed h

end GateProbability

namespace CountedPosterior

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem prior_marginal (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hfree : ProgramFree oa) (cache : HashCache C) (n : ℕ)
    (event : α × PublicContinuation.State C → Prop) :
    Pr[fun r => event (r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
      (ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2) |
      (simulateQ (SigningCacheProof.countImpl prims) oa).run (cache, n)] =
    Pr[fun p => event p.1 | do
      let h ← $ᵗ (ProtectedSlot C → HashOutput)
      let table := tableExtending (ProtectedRouting.split (protectedInput x b) cache).1 h
      let r ← run prims x b table (simulateQ worldLocalize oa)
        ((ProtectedRouting.split (protectedInput x b) cache).1,
          (ProtectedRouting.split (protectedInput x b) cache).2, n)
      pure (r, table)] := by
  classical
  have hp := probEvent_congr' (p := fun p => event p.1) (q := fun p => event p.1)
    (fun _ _ => Iff.rfl) (joint_world prims x b hno oa hfree cache n)
  rw [hp]
  simp only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def, probEvent_const,
    probFailure_uniformSample, tsub_zero]
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro r
  split <;> simp_all only [if_pos, if_neg, mul_one, mul_zero]

end CountedPosterior

namespace PublicVerification

def block (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (left : List (List Bit)) :
    OracleComp (WorldSpec C) (Output C) := do
  let selected ← SigningSecurityProof.liftFree ((SelectedKeygen.jobs b).mapM
    (referenceJob tweakable (prfValue x.2.1) x.1))
  afterOutputs A x b after left selected

theorem programFree_block (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (left : List (List Bit)) :
    ProgramFree (block A x b after left) :=
  programFree_bind _ _ (programFree_liftFree _) (fun _ => programFree_afterOutputs A x b after left _)

end PublicVerification

namespace GateProbability

def RawException (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (r : PublicVerification.Output C × HashCache C × ℕ) : Prop :=
  ∃ log, (r.1, r.2, log) ∈ support (loggedRun prims A x) ∧
    ForestExceptionAt prims x b (r.1, r.2, log)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 100000 in
theorem raw_block_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (cache : HashCache C) (n q : ℕ)
    (hq : ∀ v ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), v.2 ≤ q)
    (hsmall : q < 2 ^ 127)
    (hempty : ∀ l k v, cache (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1) :
    Pr[RawException prims A x b |
      (simulateQ (SigningCacheProof.countImpl prims) (PublicVerification.block A x b after left)).run (cache, n)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  apply le_trans (b := Pr[fun r => SupportedException prims A x b
    (r.1, (ProtectedRouting.split (protectedInput x b) r.2.1).1,
      (ProtectedRouting.split (protectedInput x b) r.2.1).2, r.2.2) |
      (simulateQ (SigningCacheProof.countImpl prims) (PublicVerification.block A x b after left)).run (cache, n)])
  · apply probEvent_mono
    intro r _ hr
    obtain ⟨log, hz, hex⟩ := hr
    exact ⟨(r.1, r.2, log), hz, hex, rfl⟩
  · rw [CountedPosterior.prior_marginal prims x b hno _ (PublicVerification.programFree_block A x b after left)]
    simpa only [PublicVerification.block, simulateQ_bind, PublicVerification.localize_liftFree] using
      private_afterOutputs_bound prims A x b hno after hb left cache n q hq hsmall hempty hallowed

set_option maxRecDepth 100000 in
theorem logged_block_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (after : List XmssSecurity.TopIndex) (hb : b ∉ after) (left : List (List Bit))
    (s : LoggedState C) (q : ℕ)
    (hq : ∀ v ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), v.2 ≤ q)
    (hsmall : q < 2 ^ 127)
    (hempty : ∀ l k v, s.1.1 (protectedInput x b (.inr (l, k, v))) = none)
    (hallowed : UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) s.1.1).1) :
    Pr[fun r => RawException prims A x b (r.1, r.2.1) |
      (simulateQ (loggedImpl prims) (PublicVerification.block A x b after left)).run s] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have he := congrArg (fun oa => Pr[RawException prims A x b | oa])
    (logged_forget prims (PublicVerification.block A x b after left) s)
  simp only [probEvent_map, Function.comp_def] at he
  apply he.le.trans
  exact raw_block_bound prims A x b hno after hb left s.1.1 s.1.2 q hq hsmall hempty hallowed

end GateProbability

namespace PublicVerification

def liveTail (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Option TreeOutput → OracleComp (WorldSpec C) (Output C)
  | some (.top top) => do
      let r ← (simulateQ (SigningCoreProof.flaggedOracles x (actualDealt x top))
        (A ⟨top.root, x.1⟩ top)).run (SigningCoreProof.tsigInit, false)
      (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
        SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1)
  | _ => pure ((false, false), none)

def openedTail (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) : Option TreeOutput → OracleComp (WorldSpec C) (Output C × Bool)
  | some (.top top) => do
      let r ← (simulateQ (openedOracles x top b) (A ⟨top.root, x.1⟩ top)).run
        ((SigningCoreProof.tsigInit, false), false)
      (fun w => (((w.1, r.2.1.2), some (top, w.2.1, w.2.2)), r.2.2)) <$>
        SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1.1)
  | _ => pure (((false, false), none), false)

set_option maxRecDepth 100000 in
theorem openedTail_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) :
    Prod.fst <$> openedTail A x b output = liveTail A x output := by
  rcases output with _ | (top | bottom)
  · simp [openedTail, liveTail]
  · simp only [openedTail, liveTail, map_bind, Functor.map_map]
    erw [← openedRun_forget x top b (A ⟨top.root, x.1⟩ top) (SigningCoreProof.tsigInit, false) false,
      bind_map_left]
  · simp [openedTail, liveTail]

set_option maxRecDepth 100000 in
theorem checkedTail_top (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (top : TopTree) :
    checkedTail A x b (some (.top top)) =
      unopenedRun x top b (A ⟨top.root, x.1⟩ top) (SigningCoreProof.tsigInit, false) >>= fun r =>
        r.elim (pure ((false, false), none)) (fun r =>
          (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
            SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1)) := by
  simp only [checkedTail, tail, bind_assoc]
  apply bind_congr
  rintro (_ | r)
  · simp [freshness]
  · exact (finish_factor x top r).symm

set_option maxRecDepth 100000 in
theorem checkedTail_probability (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) (s : LoggedState C)
    (event : Output C × LoggedState C → Prop) (hnone : ∀ flags s, ¬event ((flags, none), s)) :
    Pr[event | (simulateQ (loggedImpl prims) (checkedTail A x b output)).run s] =
    Pr[fun r => event (r.1.1, r.2) ∧ r.1.2 = false |
      (simulateQ (loggedImpl prims) (openedTail A x b output)).run s] := by
  classical
  rcases output with _ | (top | bottom)
  · simp [checkedTail, tail, freshness, openedTail, hnone]
  · rw [checkedTail_top]
    have he := unopenedRun_bind_probability prims x top b (A ⟨top.root, x.1⟩ top)
      (SigningCoreProof.tsigInit, false) s
      (fun r => (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
        SigningCoreProof.tsigFinish (actualDealt x top) (r.1, r.2.1))
      ((false, false), none) event (hnone (false, false))
    simpa only [openedTail, Functor.map_map] using he
  · simp [checkedTail, tail, freshness, openedTail, hnone]

set_option maxRecDepth 100000 in
theorem openedTail_resolves (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) (initial : HashCache C × ℕ)
    (r : (Output C × Bool) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (openedTail A x b output)).run initial))
    (hopen : r.1.2 = true) :
    ∃ top state forgery, r.1.1.2 = some (top, state, forgery) ∧ BottomResolved x top b r.2.1 := by
  rcases output with _ | (top | bottom)
  · simp [openedTail] at hr
    subst r
    cases hopen
  · obtain ⟨v, hv, hr⟩ := SigningCacheProof.run_bind_support prims _ _ initial r hr
    have hresolved := openedRun_resolves prims x top b (A ⟨top.root, x.1⟩ top)
      ((SigningCoreProof.tsigInit, false), false) initial (by simp) v hv
    have hgrow := SigningCacheProof.countRun_grows prims _ _ r hr
    simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact ⟨top, w.1.2.1, w.1.2.2, rfl, bottomResolved_mono x top b hgrow (hresolved hopen)⟩
  · simp [openedTail] at hr
    subst r
    cases hopen

set_option maxRecDepth 100000 in
/-- Stopping semantic openings preserves the supported exceptional event even
from an arbitrary cache; its witness is an actual original exceptional trace. -/
theorem liveTail_exception_probability (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (output : Option TreeOutput) (s : LoggedState C) :
    Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
      (simulateQ (loggedImpl prims) (liveTail A x output)).run s] =
    Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
      (simulateQ (loggedImpl prims) (checkedTail A x b output)).run s] := by
  rw [← openedTail_forget A x b output, simulateQ_map, StateT.run_map, probEvent_map]
  rw [checkedTail_probability prims A x b output s _ (by
    intro flags s he
    obtain ⟨log, _, hex⟩ := he
    obtain ⟨top, state, forgery, hsome, _⟩ := hex.2
    cases hsome)]
  apply probEvent_congr' _ rfl
  intro r hr
  constructor
  · intro hex
    refine ⟨hex, ?_⟩
    cases hopen : r.1.2 with
    | false => rfl
    | true =>
      have hc : (r.1, r.2.1) ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
          (openedTail A x b output)).run s.1) := by
        rw [← logged_forget prims (openedTail A x b output) s, support_map]
        exact ⟨r, hr, rfl⟩
      obtain ⟨top, state, forgery, hsome, bottom, hresolved⟩ :=
        openedTail_resolves prims A x b output s.1 (r.1, r.2.1) hc hopen
      obtain ⟨log, hz, hex⟩ := hex
      obtain ⟨top', state', forgery', hsome', hb⟩ := hex.2
      have ht := Option.some.inj (hsome'.symm.trans hsome)
      cases ht
      rw [← hb] at hresolved
      exact False.elim (forestException_unopened prims A x (r.1.1, r.2.1, log)
        hz hex.1 top state forgery hsome bottom hresolved)
  · exact And.left

end PublicVerification

namespace PublicVerification

def liveAfterOutputs (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (after : List XmssSecurity.TopIndex) (left selected : List (List Bit)) :
    OracleComp (WorldSpec C) (Output C) := do
  let right ← SigningSecurityProof.liftFree ((after.flatMap SelectedKeygen.jobs).mapM
    (referenceJob tweakable (prfValue x.2.1) x.1))
  let output ← SigningSecurityProof.liftFree (SelectedKeygen.finish (tweakable (C := C)) x.1
    (left ++ selected ++ right))
  liveTail A x output

def liveBlock (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (left : List (List Bit)) :
    OracleComp (WorldSpec C) (Output C) := do
  let selected ← SigningSecurityProof.liftFree ((SelectedKeygen.jobs b).mapM
    (referenceJob tweakable (prfValue x.2.1) x.1))
  liveAfterOutputs A x after left selected

set_option maxRecDepth 100000 in
theorem finalRun_split (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (before after : List XmssSecurity.TopIndex)
    (hsplit : topJobs = before.flatMap SelectedKeygen.jobs ++ SelectedKeygen.jobs b ++
      after.flatMap SelectedKeygen.jobs) :
    SigningDescentProof.finalRun A x = (do
      let left ← SigningSecurityProof.liftFree ((before.flatMap SelectedKeygen.jobs).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1))
      liveBlock A x b after left) := by
  change (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
    (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top >>= liveTail A x) = _
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  rw [SelectedKeygen.referenceTree_split tweakable (prfValue x.2.1) x.1 emptyTop before after b hsplit]
  simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind, bind_assoc, liveBlock, liveAfterOutputs]

/-- Probability congruence under a shared prefix, with each supported state
kept inside its bind. -/
theorem logged_bind_event_congr {α β : Type} (before : OracleComp (WorldSpec C) α)
    (left right : α → OracleComp (WorldSpec C) β) (event : β × LoggedState C → Prop)
    (he : ∀ value state, Pr[event | (simulateQ (loggedImpl prims) (left value)).run state] =
      Pr[event | (simulateQ (loggedImpl prims) (right value)).run state]) (s : LoggedState C) :
    Pr[event | (simulateQ (loggedImpl prims) (before >>= left)).run s] =
      Pr[event | (simulateQ (loggedImpl prims) (before >>= right)).run s] := by
  simp only [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  exact tsum_congr fun r => congrArg (fun v => Pr[= r | (simulateQ (loggedImpl prims) before).run s] * v)
    (he r.1 r.2)

set_option maxRecDepth 100000 in
theorem liveBlock_exception_probability (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (left : List (List Bit))
    (s : LoggedState C) :
    Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
      (simulateQ (loggedImpl prims) (liveBlock A x b after left)).run s] =
    Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
      (simulateQ (loggedImpl prims) (block A x b after left)).run s] := by
  unfold liveBlock block
  apply logged_bind_event_congr
  intro selected s
  unfold liveAfterOutputs afterOutputs
  apply logged_bind_event_congr
  intro right s
  apply logged_bind_event_congr
  intro output s
  exact liveTail_exception_probability prims A x b output s

end PublicVerification

namespace SelectedKeygen

/-- Selected-start freshness is precisely the empty-corruption allowed-read
condition. Mask slots and structural cells impose no extra restriction. -/
theorem fresh_record_allowed (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (cache : HashCache C) (hfresh : ∀ target, selectedInput x b target → cache target = none) :
    UnopenedPrivacy.RecordAllowed ∅ (UnopenedPrivacy.topStarts b)
      (ProtectedRouting.split (protectedInput x b) cache).1 := by
  classical
  rintro ((⟨T, p⟩ | pair) | cell) hs
  · change TprfSecurityProof.Revealed ∅ (.inl T) ∨ p ∉ UnopenedPrivacy.topStarts b
    right
    intro hp
    have he := hfresh (.prf (x.2.1 T) p) hp
    change (cache (.prf (x.2.1 T) p)).isSome = true at hs
    simp only [he, Option.isSome_none, Bool.false_eq_true] at hs
  · trivial
  · trivial

set_option maxRecDepth 100000 in
/-- The first selected PRF query is the start of the whole private block,
not a conditioned partial execution of that block. -/
theorem gate_residual_block (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (T : C.Term) (terms : List C.Term)
    (hterms : C.terms = T :: terms) (n : ℕ) (s : LoggedState C)
    (k : HashOutput → OracleComp (WorldSpec C) (PublicVerification.Output C))
    (hp : (OracleComp.queryBind (.inr (.inr (.inl (topGateInput x T b)))) k, s) ∈
      support ((simulateQ (loggedImpl prims)
        (prefixRun (SigningDescentProof.finalRun A x) n)).run loggedInit))
    (hseen : ¬GateSeen (.inr (.inr (.inl (topGateInput x T b)))) s.2) :
    ∃ after : List XmssSecurity.TopIndex, b ∉ after ∧ ∃ left : List (List Bit),
      OracleComp.queryBind (.inr (.inr (.inl (topGateInput x T b)))) k =
        PublicVerification.liveBlock A x b after left := by
  classical
  obtain ⟨before, after, hb, ha, hsplit⟩ := split_jobs b
  obtain ⟨selectedNext, hselected⟩ := jobs_first x b T terms hterms
  have hfactor : SigningDescentProof.finalRun A x =
      SigningSecurityProof.liftFree ((before.flatMap jobs).mapM
        (referenceJob tweakable (prfValue x.2.1) x.1)) >>= fun left =>
        query (spec := WorldSpec C) (.inr (.inr (.inl (topGateInput x T b)))) >>= fun value =>
          selectedNext value >>= PublicVerification.liveAfterOutputs A x after left := by
    rw [PublicVerification.finalRun_split A x b before after hsplit]
    simp only [PublicVerification.liveBlock, hselected, bind_assoc]
  have ht : selectedInput x b (topGateInput x T b) := by
    change Point.chain topLayer (topKey b) ⟨0, by decide⟩ (digit 0) ∈ UnopenedPrivacy.topStarts b
    exact Finset.mem_image.mpr ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩
  have havoid := hashEmbed_avoids_gate x b _ (before_jobs_avoid x b before hb) (topGateInput x T b) ht
  rw [hashEmbed_jobs] at havoid
  rw [hfactor] at hp
  obtain ⟨left, _, he⟩ := first_gate_residual prims _ _ _ havoid n loggedInit s k hp hseen
  refine ⟨after, ha, left, ?_⟩
  rw [PublicVerification.liveBlock, hselected, bind_assoc]
  exact he

end SelectedKeygen

/-- A gate's conditional bound is sufficient; a single global bound of
`2^-128` on the union of all exceptional keys is unnecessary. -/
def KeyGateBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 → ∃ T : C.Term, ∀ (b : XmssSecurity.TopIndex) s,
      RawReachable prims s → ¬GateSeen (.inr (.inr (.inl (topGateInput x T b)))) s.2 →
      (∑' r, Pr[= r | (loggedImpl prims (.inr (.inr (.inl (topGateInput x T b))))).run s] *
        continuationReserve prims (SigningDescentProof.finalRun A x) (ForestExceptionAt prims x b) r.2) ≤
          (2 ^ 128 : ℝ≥0∞)⁻¹

set_option maxRecDepth 100000 in
/-- The selected key's first PRF gate funds its entire exceptional winning
continuation. The private block starts after this gate's preceding prefix. -/
theorem keyGateBound : KeyGateBound prims C := by
  intro A q x _ hno hq hsmall
  obtain ⟨T, terms, hterms⟩ := terms_cons C
  refine ⟨T, ?_⟩
  intro b s hs hseen
  apply gate_bound_of_prefix prims (SigningDescentProof.finalRun A x)
    (ForestExceptionAt prims x b) (.inr (.inr (.inl (topGateInput x T b))))
    ((2 ^ 128 : ℝ≥0∞)⁻¹) _ s hs hseen
  intro n initial k hp hnotseen
  obtain ⟨after, hb, left, hresidual⟩ := SelectedKeygen.gate_residual_block
    prims A x b T terms hterms n initial k hp hnotseen
  have hfresh := SelectedKeygen.gate_prefix_fresh prims A x b T terms hterms n initial k hp hnotseen
  have hbound := GateProbability.logged_block_bound prims A x b hno after hb left initial q hq hsmall
    (fun l step value => hfresh _ (by exact ⟨l, step, value, rfl⟩))
    (SelectedKeygen.fresh_record_allowed x b initial.1.1 hfresh)
  rw [← PublicVerification.liveBlock_exception_probability prims A x b after left initial] at hbound
  apply le_trans (b := Pr[fun r => GateProbability.RawException prims A x b (r.1, r.2.1) |
    (simulateQ (loggedImpl prims) (OracleComp.queryBind (.inr (.inr (.inl (topGateInput x T b)))) k)).run initial])
  · apply probEvent_mono
    intro r hr hex
    exact ⟨r.2.2, prefixRun_support_resume prims (SigningDescentProof.finalRun A x)
      n _ initial hp r hr, hex⟩
  · rw [hresidual]
    exact hbound

set_option maxRecDepth 100000 in
/-- The concrete per-key route has no unproved deterministic accounting stage:
gate occurrence, disjoint charges, and terminal coverage are all discharged. -/
theorem hitPotential_of_keyGates (hgate : KeyGateBound prims C) : HitPotential prims C := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨T, hT⟩ := hgate A q x hx hkeys hq hsmall
  apply isHitPotential_of_gated_completion prims A x (forestRelevant x.1) (forestCompletion x)
    (forestCompletion_reads x) (topGateInput x T) (topGateInput_injective x T)
    (fun _ => forestRelevant_prf _ _ _) (ForestExceptionAt prims x) hT
  intro z hz hwin
  by_cases h : ∀ r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (forestCompletion x)).run z.2.1.1), CompletedHit (forestRelevant x.1) r.1 z.2.1.1
  · exact Or.inl h
  · obtain ⟨top, state, forgery, hsome, _⟩ := hwin.2
    refine Or.inr ⟨XmssSecurity.topKeyOf forgery.signature.leafIndex,
      ⟨⟨hwin, h⟩, top, state, forgery, hsome, rfl⟩, ?_⟩
    exact finalRun_gate prims A x T _ loggedInit z hz

/-- A stronger sufficient condition for funding the entire exceptional event
at the first query. The unconditional proof instead funds each top key separately. -/
def ForestExceptionBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 → Pr[ForestException prims x | loggedRun prims A x] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹

/-- An alternative assembly using a single first-query reserve, assuming a
bound on the entire exceptional winning event. -/
theorem isHitPotential_forest (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hrare : Pr[ForestException prims x | loggedRun prims A x] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹) :
    ∃ Inv f, IsHitPotential prims A x Inv f := by
  classical
  obtain ⟨T, p, k, hfirst⟩ := finalRun_first A x
  apply isHitPotential_of_completion prims A x (forestRelevant x.1) (forestCompletion x)
    (forestCompletion_reads x) (.prf (x.2.1 T) p) (forestRelevant_prf _ _ _) k hfirst
    (ForestException prims x) hrare
  intro z _ hwin
  by_cases h : ∀ r ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (forestCompletion x)).run z.2.1.1), CompletedHit (forestRelevant x.1) r.1 z.2.1.1
  · exact Or.inl h
  · exact Or.inr ⟨hwin, h⟩

end SigningHitProof

set_option maxRecDepth 100000 in
/-- No outcome of the signing run logs a programming query. -/
theorem noProgramQuery (prims : Primitives) (C : Committee) : NoProgramQuery prims C := by
  intro A x z hz
  exact SigningHitProof.noProgramming_finalRun prims A x loggedInit
    (by simp [loggedInit, Programmed]) z hz

/-- The signing hit potential: completion accounting plus one funded
exceptional-continuation reserve for each top key. -/
theorem hitPotential (prims : Primitives) (C : Committee) : HitPotential prims C :=
  SigningHitProof.hitPotential_of_keyGates prims (SigningHitProof.keyGateBound prims)

/-- The signing hit lane is closed through its original assembly theorem. -/
theorem hitLaneBoundClosed (prims : Primitives) (C : Committee) : HitLaneBound prims C :=
  hitLaneBound prims C (hitPotential prims C) (noProgramQuery prims C)

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fixedHit_le_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fixedHit_le_expectedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fundedContinuation_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fundedContinuation_step

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fundedContinuation_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fundedContinuation_terminal

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.completionPotential_randomOracle_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.completionPotential_randomOracle_step

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.isHitPotential_of_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.isHitPotential_of_completion

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestCompletion_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestCompletion_reads

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestRun_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestRun_unique

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.completedHit_forest_of_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.completedHit_forest_of_collision

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.finalRun_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.finalRun_first

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.isHitPotential_forest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.isHitPotential_forest

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fixedPairHits_le_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fixedPairHits_le_expectedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.fresh_layer_many_guesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.fresh_layer_many_guesses

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.recordReads_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.recordReads_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestRun_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestRun_replay

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestRun_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestRun_payload

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_witness

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.exposedRun_top_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.exposedRun_top_extension

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.exposedRun_top_authentic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.exposedRun_top_authentic

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.valid_encoding_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.valid_encoding_deficit

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_authentic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_authentic

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_replayChanges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_replayChanges

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.MarkedChain.walk_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.MarkedChain.walk_density

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.suffixWeight_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.suffixWeight_pending

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.suffixWeight_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.suffixWeight_join

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.suffixWeight_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.suffixWeight_first

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.authenticDepth_query_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.authenticDepth_query_cap

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.rawReachable_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.rawReachable_prefix

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.prefixRun_support_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.prefixRun_support_resume

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.prefixRun_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.prefixRun_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.gate_bound_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.gate_bound_of_prefix

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.gatedContinuation_sum_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.gatedContinuation_sum_step

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.finalRun_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.finalRun_gate

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.isHitPotential_of_gated_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.isHitPotential_of_gated_completion

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.hitPotential_of_keyGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.hitPotential_of_keyGates

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.resolves_referenceBottom_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.resolves_referenceBottom_targets

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.resolves_referenceTop_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.resolves_referenceTop_targets

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.resolved_ceremonies_noHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.resolved_ceremonies_noHit

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.exposedRun_top_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.exposedRun_top_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_unopened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_unopened

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_no_bottom_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_no_bottom_call

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.resolves_verify_topWalks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.resolves_verify_topWalks

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_authentic_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_authentic_original

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_no_bottom_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_no_bottom_suffix

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.openedFinalRun_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.openedFinalRun_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.prefixRun_opened_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.prefixRun_opened_lift

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestException_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestException_fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestExceptionAt_unopened_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestExceptionAt_unopened_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestExceptionAt_unopened_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestExceptionAt_unopened_prefix

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.continuationReserve_unopened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.continuationReserve_unopened

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.unopenedRun_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.unopenedRun_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.unopenedRun_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.unopenedRun_expectation

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.unopenedRun_bind_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.unopenedRun_bind_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.unopenedFinalRun_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.unopenedFinalRun_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.forestExceptionAt_stopped_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.forestExceptionAt_stopped_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.UnopenedPrivacy.topStarts_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.UnopenedPrivacy.topStarts_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.UnopenedPrivacy.referenceBottom_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.UnopenedPrivacy.referenceBottom_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.UnopenedPrivacy.evalSum_shift_unchallenged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.UnopenedPrivacy.evalSum_shift_unchallenged

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.weight_mean_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.weight_mean_step

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.productWeight_mean_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.productWeight_mean_step

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.productWeight_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.productWeight_terminal

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.expected_discounted_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.expected_discounted_le

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.terminal_probability_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.terminal_probability_digest

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.mixed_terminal_probability_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.mixed_terminal_probability_digest

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.LayeredGraph.component_canonical_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.LayeredGraph.component_canonical_injective

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.observedTopRows_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.observedTopRows_unique

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.observedTopRows_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.observedTopRows_terminal

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.FinitePosterior.joint_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.FinitePosterior.joint_table

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.FinitePosterior.joint_table_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.FinitePosterior.joint_table_mixed

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.UnopenedPrivacy.topStarts_posterior_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.UnopenedPrivacy.topStarts_posterior_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.first_gate_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.first_gate_residual

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.ProtectedTable.posterior_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.ProtectedTable.posterior_split

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.PosteriorCompletion.marked_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.PosteriorCompletion.marked_density

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.PrivateRecord.run_restore_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.PrivateRecord.run_restore_shift

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.CanonicalCompletion.marked_of_noCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.CanonicalCompletion.marked_of_noCollision

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.PublicContinuation.counted_terminal_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.PublicContinuation.counted_terminal_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.GateProbability.adaptive_endpoint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.GateProbability.adaptive_endpoint_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.FinitePosterior.eager_support_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.FinitePosterior.eager_support_lazy

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.GateProbability.after_private_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.GateProbability.after_private_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.GateProbability.good_of_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.GateProbability.good_of_exception

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.PublicVerification.afterOutputs_counted_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.PublicVerification.afterOutputs_counted_view

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.PublicVerification.reset_observed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.PublicVerification.reset_observed_witness

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.GateProbability.restored_exception_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.GateProbability.restored_exception_good

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.GateProbability.private_afterOutputs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.GateProbability.private_afterOutputs_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.GateProbability.logged_block_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.GateProbability.logged_block_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.PublicVerification.liveTail_exception_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.PublicVerification.liveTail_exception_probability

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.SelectedKeygen.gate_residual_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.SelectedKeygen.gate_residual_block

/-- info: 'ThresholdLeanXmssSecurity.SigningHitProof.keyGateBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningHitProof.keyGateBound

/-- info: 'ThresholdLeanXmssSecurity.noProgramQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noProgramQuery

/-- info: 'ThresholdLeanXmssSecurity.hitPotential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hitPotential

/-- info: 'ThresholdLeanXmssSecurity.hitLaneBoundClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hitLaneBoundClosed

end ThresholdLeanXmssSecurity
