import ThresholdLeanXmssSecurity.Proof.SigningGuessLane
import ThresholdLeanXmssSecurity.Proof.SigningHitProof
import XmssSecurity.Scan.Frame
import XmssSecurity.Scan.PerKey
import XmssSecurity.Proof.Bridge.Derivation
import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.CappedGlobalKeygen
import XmssSecurity.Proof.RandomOraclePresampling
import XmssSecurity.Proof.PrecomputedKeygenCache
import XmssSecurity.Proof.QueryCounting
import LeanXmss.Bytes

/-!
The earlier counterexample below refutes the one-unit GuessPartner route only.
The current target is SigningCoreProof.HiddenCoreAt, with two units per call.
Domain separation and a disjoint event partition must preserve that budget.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss SigningCostProof

namespace SigningGuessProof

/-- A potential that starts at zero and pays at most `ε * cost` at each query
bounds the probability of any final event that makes it at least one. -/
theorem probEvent_le_chargedCost
    {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (hinv : ∀ t s, Inv s → ∀ r ∈ support ((impl t).run s), Inv r.2)
    (potential : σ → ℝ≥0∞) (bad : σ → Prop)
    (hbad : ∀ s, bad s → 1 ≤ potential s)
    (cost : spec.Domain → σ → ℝ≥0∞) (ε : ℝ≥0∞)
    (hstep : ∀ t s, Inv s →
      ∑' r, Pr[= r | (impl t).run s] * potential r.2 ≤
        potential s + ε * cost t s)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s)
    (hzero : potential s = 0) :
    Pr[fun r => bad r.2 | (simulateQ impl oa).run s] ≤
      ε * XmssSecurity.expectedSimulatedCost impl cost oa s := by
  refine (XmssSecurity.probEvent_le_expectedFinal impl potential bad hbad oa s).trans ?_
  have h := XmssSecurity.expectedFinal_le impl hinv potential
    (fun t s => ε * cost t s) hstep oa s hs
  simpa only [hzero, zero_add, XmssSecurity.expectedSimulatedCost_const_mul] using h

/-- It suffices to bound the next bad state only when the current state is good. -/
theorem probEvent_le_chargedCost_of_step
    {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (hinv : ∀ t s, Inv s → ∀ r ∈ support ((impl t).run s), Inv r.2)
    (bad : σ → Prop) (cost : spec.Domain → σ → ℝ≥0∞) (ε : ℝ≥0∞)
    (hstep : ∀ t s, Inv s → ¬bad s →
      Pr[fun r => bad r.2 | (impl t).run s] ≤ ε * cost t s)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) (hgood : ¬bad s) :
    Pr[fun r => bad r.2 | (simulateQ impl oa).run s] ≤
      ε * XmssSecurity.expectedSimulatedCost impl cost oa s := by
  classical
  apply probEvent_le_chargedCost impl Inv hinv (fun s => if bad s then 1 else 0)
    bad (by intro s h; simp [h]) cost ε ?_ oa s hs (by simp [hgood])
  intro t s hs
  have heq : (∑' r, Pr[= r | (impl t).run s] * (if bad r.2 then 1 else 0)) =
      Pr[fun r => bad r.2 | (impl t).run s] := by
    simp [probEvent_eq_tsum_ite, mul_ite]
  rw [heq]
  by_cases h : bad s
  · simp only [if_pos h]
    exact probEvent_le_one.trans (le_add_right le_rfl)
  · simpa only [if_neg h, zero_add] using hstep t s hs h

abbrev LoggedState (C : Committee) :=
  (HashCache C × ℕ) × QueryLog (WorldSpec C)

/-- The generic step charging rule specialized to the actual logged signing oracle. -/
theorem logged_probEvent_le_chargedCost {C : Committee} (prims : Primitives)
    {α : Type} (Inv : LoggedState C → Prop)
    (hinv : ∀ t s, Inv s → ∀ r ∈ support ((loggedImpl prims t).run s), Inv r.2)
    (bad : LoggedState C → Prop) (cost : (WorldSpec C).Domain → LoggedState C → ℝ≥0∞)
    (ε : ℝ≥0∞)
    (hstep : ∀ t s, Inv s → ¬bad s →
      Pr[fun r => bad r.2 | (loggedImpl prims t).run s] ≤ ε * cost t s)
    (oa : OracleComp (WorldSpec C) α)
    (hs : Inv ((∅, 0), [])) (hgood : ¬bad ((∅, 0), [])) :
    Pr[fun r => bad r.2 | (simulateQ (loggedImpl prims) oa).run ((∅, 0), [])] ≤
      ε * XmssSecurity.expectedSimulatedCost (loggedImpl prims) cost oa ((∅, 0), []) := by
  exact probEvent_le_chargedCost_of_step (loggedImpl prims) Inv hinv bad cost ε hstep
    oa ((∅, 0), []) hs hgood

/-- Logging a call increases its accumulated cost by exactly that call's cost. -/
theorem logged_step_cost {C : Committee} (prims : Primitives)
    (cost : (WorldSpec C).Domain → ℕ) (t : (WorldSpec C).Domain)
    (s : LoggedState C) :
    (∑' r, Pr[= r | (loggedImpl prims t).run s] *
      (SigningGuessLaneProof.logCost cost r.2.2 : ℝ≥0∞)) =
      (SigningGuessLaneProof.logCost cost s.2 : ℝ≥0∞) + cost t := by
  simp [loggedImpl, SigningGuessLaneProof.logCost, QueryLog.logQuery,
    QueryLog.singleton, tsum_probOutput_map_mul, ENNReal.tsum_mul_right]

/-- Recursive expected query cost is exactly the expectation of the accumulated log cost. -/
theorem logged_expectedCost_eq {C : Committee} (prims : Primitives) {α : Type}
    (cost : (WorldSpec C).Domain → ℕ) (oa : OracleComp (WorldSpec C) α)
    (s : LoggedState C) :
    (SigningGuessLaneProof.logCost cost s.2 : ℝ≥0∞) +
      XmssSecurity.expectedSimulatedCost (loggedImpl prims) (fun t _ => cost t) oa s =
    XmssSecurity.expectedFinal (loggedImpl prims)
      (fun s => SigningGuessLaneProof.logCost cost s.2) oa s := by
  apply le_antisymm
  · exact XmssSecurity.expectedFinal_ge (loggedImpl prims)
      (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) _ _
      (fun t s _ => (logged_step_cost prims cost t s).ge) oa s trivial
  · exact XmssSecurity.expectedFinal_le (loggedImpl prims)
      (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) _ _
      (fun t s _ => (logged_step_cost prims cost t s).le) oa s trivial

set_option maxRecDepth 100000 in
/-- The signing budget bounds the recursive expected cost of the logged run. -/
theorem loggedRun_expectedCost_le {C : Committee} (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    XmssSecurity.expectedSimulatedCost (loggedImpl prims)
      (fun t _ => SeedHitProof.signCost t) (SigningDescentProof.finalRun A x)
      ((∅, 0), []) ≤ q := by
  have heq := logged_expectedCost_eq prims SeedHitProof.signCost
    (SigningDescentProof.finalRun A x) ((∅, 0), [])
  simp only [SigningGuessLaneProof.logCost, List.map_nil, List.sum_nil, Nat.cast_zero,
    zero_add] at heq
  rw [heq, XmssSecurity.expectedFinal]
  change (∑' r, Pr[= r | loggedRun prims A x] *
    (SigningGuessLaneProof.logCost SeedHitProof.signCost r.2.2 : ℝ≥0∞)) ≤ q
  calc
    _ ≤ ∑' r, Pr[= r | loggedRun prims A x] * (q : ℝ≥0∞) := by
      refine ENNReal.tsum_le_tsum fun r => ?_
      by_cases hr : r ∈ support (loggedRun prims A x)
      · refine mul_le_mul_right ?_ _
        rw [← SigningGuessLaneProof.loggedRun_count_eq prims A x r hr]
        exact_mod_cast SigningGuessLaneProof.loggedRun_count_le prims A x q hq r hr
      · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ q := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

/-- The step charging rule with the accumulated cost in the final log. -/
theorem logged_probEvent_le_expectedCost {C : Committee} (prims : Primitives)
    {α : Type} (Inv : LoggedState C → Prop)
    (hinv : ∀ t s, Inv s → ∀ r ∈ support ((loggedImpl prims t).run s), Inv r.2)
    (bad : LoggedState C → Prop) (cost : (WorldSpec C).Domain → ℕ) (ε : ℝ≥0∞)
    (hstep : ∀ t s, Inv s → ¬bad s →
      Pr[fun r => bad r.2 | (loggedImpl prims t).run s] ≤ ε * cost t)
    (oa : OracleComp (WorldSpec C) α)
    (hs : Inv ((∅, 0), [])) (hgood : ¬bad ((∅, 0), [])) :
    Pr[fun r => bad r.2 | (simulateQ (loggedImpl prims) oa).run ((∅, 0), [])] ≤
      ε * ∑' r, Pr[= r | (simulateQ (loggedImpl prims) oa).run ((∅, 0), [])] *
        (SigningGuessLaneProof.logCost cost r.2.2 : ℝ≥0∞) := by
  have h := logged_probEvent_le_chargedCost prims Inv hinv bad (fun t _ => cost t)
    ε hstep oa hs hgood
  have heq := logged_expectedCost_eq prims cost oa ((∅, 0), [])
  simp only [SigningGuessLaneProof.logCost, List.map_nil, List.sum_nil, Nat.cast_zero,
    zero_add] at heq
  rw [heq] at h
  exact h

/-- An encoded address can be recovered without inspecting its variable payload. -/
theorem address_eq_of_input_eq (P : LeanXmss.PublicParameter)
    (left right : LeanXmss.TweakFields) (u v : LeanXmss.HashInput)
    (h : LeanXmss.bytesLE 16 P ++ LeanXmss.fieldBytes left ++ u =
      LeanXmss.bytesLE 16 P ++ LeanXmss.fieldBytes right ++ v) : left = right := by
  exact (LeanXmss.fieldInput_injective h).1

/-- One commitment input cannot be a trial at two bottom keys. -/
theorem commitmentInput_key_eq (P : LeanXmss.PublicParameter)
    {e f : LeanXmss.KeyIndex} {ρ τ : LeanXmss.Digest}
    (h : commitmentInput P e ρ = commitmentInput P f τ) : e = f := by
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hlo := congrArg LeanXmss.TweakFields.lo ha
  apply Fin.ext
  have hn := congrArg BitVec.toNat hlo
  simpa [LeanXmss.tweakFields, Nat.mod_eq_of_lt e.isLt,
    Nat.mod_eq_of_lt f.isLt] using hn

/-- One randomizer input cannot be a trial at two keys. -/
theorem randomizerInput_key_eq (P : LeanXmss.PublicParameter)
    {lay lay' : LeanXmss.Layer} {e f : LeanXmss.KeyIndex}
    {ρ τ : LeanXmss.Digest} {m m' : LeanXmss.HashInput}
    (h : randomizerInput P lay e ρ m = randomizerInput P lay' f τ m') : e = f := by
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hlo := congrArg LeanXmss.TweakFields.lo ha
  apply Fin.ext
  have hn := congrArg BitVec.toNat hlo
  simpa [LeanXmss.tweakFields, Nat.mod_eq_of_lt e.isLt,
    Nat.mod_eq_of_lt f.isLt] using hn

/-- A randomizer input also fixes its opening and message; repeated sessions
with this input therefore address the same cached trial. -/
theorem randomizerInput_payload_eq (P : LeanXmss.PublicParameter)
    {lay lay' : LeanXmss.Layer} {e f : LeanXmss.KeyIndex}
    {ρ τ : LeanXmss.Digest} {m m' : LeanXmss.HashInput}
    (h : randomizerInput P lay e ρ m = randomizerInput P lay' f τ m') :
    ρ = τ ∧ m = m' := by
  have hp : LeanXmss.bytesLE 16 ρ ++ m = LeanXmss.bytesLE 16 τ ++ m' :=
    (LeanXmss.fieldInput_injective (payload := LeanXmss.bytesLE 16 ρ ++ m)
      (payload' := LeanXmss.bytesLE 16 τ ++ m')
      (by simpa only [randomizerInput, List.append_assoc] using h)).2.2
  obtain ⟨hr, hm⟩ := List.append_inj hp (by simp [LeanXmss.bytesLE_length])
  exact ⟨LeanXmss.bytesLE_injective hr, hm⟩

/-- Commitment and randomizer trials have different address steps. -/
theorem commitmentInput_ne_randomizerInput (P : LeanXmss.PublicParameter)
    (e f : LeanXmss.KeyIndex) (lay : LeanXmss.Layer)
    (ρ τ : LeanXmss.Digest) (m : LeanXmss.HashInput) :
    commitmentInput P e ρ ≠ randomizerInput P lay f τ m := by
  intro h
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hs := congrArg LeanXmss.TweakFields.step ha
  norm_num [LeanXmss.tweakFields] at hs

/-- The layer bit prevents a bottom randomizer input from serving a top key. -/
theorem randomizerInput_layer_eq (P : LeanXmss.PublicParameter)
    {lay lay' : LeanXmss.Layer} {e f : LeanXmss.KeyIndex}
    {ρ τ : LeanXmss.Digest} {m m' : LeanXmss.HashInput}
    (h : randomizerInput P lay e ρ m = randomizerInput P lay' f τ m') : lay = lay' := by
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hh := congrArg (fun f => f.hi.toNat) ha
  have hl := lay.isLt
  have hr := lay'.isLt
  apply Fin.ext
  simp only [LeanXmss.tweakFields, LeanXmss.layerHi, Nat.zero_add,
    BitVec.toNat_ofNat] at hh
  change lay.val < 2 at hl
  change lay'.val < 2 at hr
  norm_num at hh
  omega

/-- Repeated successful round-1 requests at a bound key use the same message. -/
theorem bound_message_unique {C : Committee} (st : TsigState C)
    (e : LeanXmss.KeyIndex) (m m' : LeanXmss.Message)
    (hb : st.bound e = some m) (haccept : breaksOneMessagePerKey st e m' = false) :
    m' = m := by
  simp only [breaksOneMessagePerKey, hb, Option.any_some, decide_eq_false_iff_not,
    not_not] at haccept
  exact haccept.symm

/-- Commitment addresses are distinct from every verification hash domain. -/
theorem commitmentInput_ne_tweakableHashInput
    (P P' : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex) (ρ : LeanXmss.Digest)
    (domain : LeanXmss.HashDomain) (payload : LeanXmss.HashInput) :
    commitmentInput P e ρ ≠ LeanXmss.tweakableHashInput P' domain payload := by
  intro h
  have hf := (LeanXmss.fieldInput_injective
    (payload := LeanXmss.bytesLE 16 ρ ++ LeanXmss.bytesLE 16 0)
    (payload' := payload)
    (by simpa only [commitmentInput, LeanXmss.tweakableHashInput, LeanXmss.tweakBytes,
      List.append_assoc] using h)).1
  have ht := congrArg (fun f => f.tag.toNat) hf
  cases domain <;> norm_num [LeanXmss.hashDomainFields, LeanXmss.tweakFields] at ht

/-- A commitment cache insertion leaves every verification hash input unchanged. -/
theorem commitment_cacheQuery_eq {C : Committee} (cache : HashCache C)
    (P P' : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex) (ρ : LeanXmss.Digest)
    (output : LeanXmss.HashOutput) (domain : LeanXmss.HashDomain) (payload : LeanXmss.HashInput) :
    (cache.cacheQuery (.hash (commitmentInput P e ρ)) output)
        (.hash (LeanXmss.tweakableHashInput P' domain payload)) =
      cache (.hash (LeanXmss.tweakableHashInput P' domain payload)) := by
  apply QueryCache.cacheQuery_of_ne
  intro h
  exact commitmentInput_ne_tweakableHashInput P P' e ρ domain payload (Query.hash.inj h).symm

/-- Both targets of a commitment search belong to the residual lane. -/
def CommitmentInput (input : LeanXmss.HashInput) : Prop :=
  ∃ P e ρ, input = commitmentInput P e ρ

def CommitmentCall {C : Committee} : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inr (.inl (.hash input)))) => CommitmentInput input
  | .inr (.inr (.inl (.hash input))) => CommitmentInput input
  | _ => False

open Classical in
def commitmentCost {C : Committee} (t : (WorldSpec C).Domain) : ℕ :=
  if CommitmentCall t then 1 else 0

def hitOnlyCost {C : Committee} (t : (WorldSpec C).Domain) : ℕ :=
  SeedHitProof.signCost t - commitmentCost t

def residualCost {C : Committee} (t : (WorldSpec C).Domain) : ℕ :=
  SeedHitProof.signCost t + commitmentCost t

theorem commitmentCost_le {C : Committee} (t : (WorldSpec C).Domain) :
    commitmentCost t ≤ SeedHitProof.signCost t := by
  unfold commitmentCost
  split_ifs with hc
  · rcases t with ((n | (q | y)) | u) | (n | (q | y)) <;>
      simp_all [CommitmentCall, SeedHitProof.signCost]
  · exact Nat.zero_le _

theorem domainCosts_add {C : Committee} (t : (WorldSpec C).Domain) :
    hitOnlyCost t + residualCost t = 2 * SeedHitProof.signCost t := by
  have h := commitmentCost_le t
  unfold hitOnlyCost residualCost
  omega

theorem domainCosts_of_commitment {C : Committee} (t : (WorldSpec C).Domain)
    (h : CommitmentCall t) : hitOnlyCost t = 0 ∧ residualCost t = 2 := by
  rcases t with ((n | (q | y)) | u) | (n | (q | y)) <;>
    simp_all [CommitmentCall, hitOnlyCost, residualCost, commitmentCost, SeedHitProof.signCost]

theorem domainCosts_of_not_commitment {C : Committee} (t : (WorldSpec C).Domain)
    (h : ¬CommitmentCall t) :
    hitOnlyCost t = SeedHitProof.signCost t ∧ residualCost t = SeedHitProof.signCost t := by
  simp [hitOnlyCost, residualCost, commitmentCost, h]

theorem log_domainCosts_add {C : Committee} (log : QueryLog (WorldSpec C)) :
    SigningGuessLaneProof.logCost hitOnlyCost log +
      SigningGuessLaneProof.logCost residualCost log =
    2 * SigningGuessLaneProof.logCost SeedHitProof.signCost log := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
    simp only [SigningGuessLaneProof.logCost, List.map_cons, List.sum_cons] at ih ⊢
    have h := domainCosts_add entry.1
    omega

/-- Priority goes to Guess/Partner. This is the part of the hit event left over. -/
def WinHitOnly {C : Committee} (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (r : Outcome C) : Prop := WinHit prims x r ∧ ¬WinGuessPartner prims x r

theorem winHitOnly_disjoint {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) :
    ¬(WinHitOnly prims x r ∧ WinGuessPartner prims x r) := by
  exact fun h => h.1.2 h.2

set_option maxRecDepth 100000 in
/-- The descent is covered by two disjoint events, with no assumption about their costs. -/
theorem win_le_disjoint {C : Committee} (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true |
      runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] ≤
    Pr[WinHitOnly prims x | SigningDescentProof.exposedRun prims A x] +
      Pr[WinGuessPartner prims x | SigningDescentProof.exposedRun prims A x] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, probEvent_map]
  refine le_trans (probEvent_mono fun r hr hwin => ?_) (probEvent_or_le _ _ _)
  classical
  have hwin' : r.1.1 = (true, false) := Prod.ext hwin.2 hwin.1
  obtain ⟨top, state, forgery, hsome, hbad⟩ :=
    SigningCacheProof.signing_run_badEvent_closed prims A x r hr hwin'
  by_cases hgp : WinGuessPartner prims x r
  · exact Or.inr hgp
  · left
    refine ⟨?_, hgp⟩
    rcases hbad with h | h
    · exact ⟨hwin', top, state, forgery, hsome, h⟩
    · exact (hgp ⟨hwin', top, state, forgery, hsome, h⟩).elim

/-- The structural half of the earlier domain split. It is proved below by
hitOnlyDomainBoundClosed; its separate Guess/Partner counterpart is false. -/
def HitOnlyDomainBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[fun r => WinHitOnly prims x (SigningGuessLaneProof.forget r) | loggedRun prims A x] ≤
      ∑' r, Pr[= r | loggedRun prims A x] *
        ((SigningGuessLaneProof.logCost hitOnlyCost r.2.2 : ℝ≥0∞) / 2 ^ 128)

/-- An earlier proposed residual bound, rejected by the stopped-search calculation
below. It is retained only as an explicit hypothesis of the earlier reduction. -/
def GuessPartnerDomainBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[fun r => WinGuessPartner prims x (SigningGuessLaneProof.forget r) | loggedRun prims A x] ≤
      ∑' r, Pr[= r | loggedRun prims A x] *
        ((SigningGuessLaneProof.logCost residualCost r.2.2 : ℝ≥0∞) / 2 ^ 128)

set_option maxRecDepth 100000 in
/-- The two domain budgets together never exceed the root claim's two units. -/
theorem domainCharges_le {C : Committee} (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    (∑' r, Pr[= r | loggedRun prims A x] *
      ((SigningGuessLaneProof.logCost hitOnlyCost r.2.2 : ℝ≥0∞) / 2 ^ 128)) +
    (∑' r, Pr[= r | loggedRun prims A x] *
      ((SigningGuessLaneProof.logCost residualCost r.2.2 : ℝ≥0∞) / 2 ^ 128)) ≤
    (q : ℝ≥0∞) / 2 ^ 128 + (q : ℝ≥0∞) / 2 ^ 128 := by
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' r, Pr[= r | loggedRun prims A x] *
        ((q : ℝ≥0∞) / 2 ^ 128 + (q : ℝ≥0∞) / 2 ^ 128) := by
      refine ENNReal.tsum_le_tsum fun r => ?_
      rw [← mul_add, ← ENNReal.add_div, ← ENNReal.add_div]
      by_cases hr : r ∈ support (loggedRun prims A x)
      · apply mul_le_mul_right
        apply ENNReal.div_le_div_right
        rw [← Nat.cast_add, log_domainCosts_add,
          ← SigningGuessLaneProof.loggedRun_count_eq prims A x r hr]
        have h := SigningGuessLaneProof.loggedRun_count_le prims A x q hq r hr
        exact_mod_cast (show 2 * r.2.1.2 ≤ q + q by omega)
      · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

set_option maxRecDepth 100000 in
/-- Root-gap reduction using a disjoint event split and exactly two units per call.
The two probabilistic domain bounds remain explicit hypotheses. -/
theorem hiddenCoreAt_of_domainBounds (prims : Primitives) (C : Committee)
    (hitLane : HitOnlyDomainBound prims C)
    (residualLane : GuessPartnerDomainBound prims C) : SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hc hq hsmall
  rw [signingHashError_eq]
  refine (win_le_disjoint prims A x).trans ?_
  rw [← loggedRun_forget, probEvent_map, probEvent_map]
  exact (add_le_add (hitLane A q x hx hc hq hsmall)
    (residualLane A q x hx hc hq hsmall)).trans (domainCharges_le prims A x q hq)

/-- The binding ledger is write-once, including rejected calls and repeated rounds. -/
def BoundExtends {C : Committee} (st st' : TsigState C) : Prop :=
  ∀ e message, st.bound e = some message → st'.bound e = some message

theorem boundExtends_refl {C : Committee} (st : TsigState C) : BoundExtends st st :=
  fun _ _ h => h

theorem boundExtends_trans {C : Committee} {st st' st'' : TsigState C}
    (h : BoundExtends st st') (h' : BoundExtends st' st'') : BoundExtends st st'' :=
  fun e message hb => h' e message (h e message hb)

private theorem run_liftM_comp {ι σ α : Type} {spec : OracleSpec ι}
    (p : OracleComp spec α) (st : σ) :
    (liftM p : StateT σ (OracleComp spec) α).run st = (fun a => (a, st)) <$> p := rfl

theorem tsigOracles_boundExtends {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((tsigOracles lift dealt t).run st)) : BoundExtends st r.2 := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;>
      simp_all [StateT.run_set, StateT.run_pure, BoundExtends]
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, run_liftM_comp, bind_map_left,
      mem_support_bind_iff] at hr
    obtain ⟨tree, _, hr⟩ := hr
    cases tree <;> simp_all [BoundExtends]
    obtain ⟨value, _, rfl⟩ := hr
    exact fun _ _ h => h
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure, BoundExtends]
    · rename_i ha
      simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map,
        run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      intro e' message' hb
      by_cases he : e' = e
      · subst e'
        have hm := bound_message_unique st e message' message hb
          (by simp_all)
        simp [hm]
      · simpa [Function.update_of_ne he] using hb
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure, BoundExtends]
    · simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
        mem_support_bind_iff] at hr
      obtain ⟨tree, _, hr⟩ := hr
      cases tree with
      | none => simp_all [StateT.run_pure, BoundExtends]
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
          mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;>
          simp_all [StateT.run_set, StateT.run_pure, BoundExtends]

/-- The complete continuation of the forger cannot replace a bound message. -/
theorem gameOracles_boundExtends {C : Committee}
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) :
    ∀ r ∈ support ((simulateQ (SigningCoreProof.gameOracles dealt) oa).run st),
      BoundExtends st r.2 := by
  apply SeedHitProof.support_simulateQ_inv _ (BoundExtends st) _ oa st (boundExtends_refl st)
  intro t s hs r hr
  cases t with
  | inl t =>
    change r ∈ support ((fun a => (a, s)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hr
    simp only [support_map] at hr
    obtain ⟨value, _, rfl⟩ := hr
    exact hs
  | inr t =>
    exact boundExtends_trans hs
      (tsigOracles_boundExtends (fun oa => SigningCoreProof.honestLift oa) dealt t s r hr)

/-- The signing transcript, unlike the underlying hash log, records the message
in round 1 even when that round makes no message-dependent hash query. -/
abbrev SigningLog (C : Committee) := QueryLog (LocalSpec C + TsigSpec C)

def bindingStep {C : Committee}
    (bound : LeanXmss.KeyIndex → Option LeanXmss.Message) :
    (t : (LocalSpec C + TsigSpec C).Domain) → (LocalSpec C + TsigSpec C).Range t →
      LeanXmss.KeyIndex → Option LeanXmss.Message
  | .inr (.round1 _ _ e message), some _ => Function.update bound e (some message)
  | _, _ => bound

def boundOfSigningLog {C : Committee} (log : SigningLog C) :
    LeanXmss.KeyIndex → Option LeanXmss.Message :=
  log.foldl (fun bound entry => bindingStep bound entry.1 entry.2) (fun _ => none)

theorem boundOfSigningLog_append {C : Committee} (log : SigningLog C)
    (t : (LocalSpec C + TsigSpec C).Domain) (u : (LocalSpec C + TsigSpec C).Range t) :
    boundOfSigningLog (log.logQuery t u) = bindingStep (boundOfSigningLog log) t u := by
  simp [boundOfSigningLog, QueryLog.logQuery, QueryLog.singleton, List.foldl_append]

theorem tsigOracles_bindingStep {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((tsigOracles lift dealt t).run st)) :
    r.2.bound = bindingStep st.bound (.inr t) r.1 := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;> simp_all [StateT.run_set, StateT.run_pure, bindingStep]
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, run_liftM_comp, bind_map_left,
      mem_support_bind_iff] at hr
    obtain ⟨tree, _, hr⟩ := hr
    cases tree <;> simp_all [bindingStep]
    obtain ⟨value, _, rfl⟩ := hr
    rfl
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure, bindingStep]
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map,
        run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure, bindingStep]
    · simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
        mem_support_bind_iff] at hr
      obtain ⟨tree, _, hr⟩ := hr
      cases tree with
      | none => simp_all [StateT.run_pure, bindingStep]
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
          mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> simp_all [StateT.run_set, StateT.run_pure, bindingStep]

/-- Only a completed round-2 response adds a signing release to the view. -/
def releaseStep {C : Committee} (released : List (LeanXmss.KeyIndex × LeanXmss.Message × C.Party)) :
    (t : (LocalSpec C + TsigSpec C).Domain) → (LocalSpec C + TsigSpec C).Range t →
      List (LeanXmss.KeyIndex × LeanXmss.Message × C.Party)
  | .inr (.round2 i _ e message _), some _ => released ++ [(e, message, i)]
  | _, _ => released

def releasedOfSigningLog {C : Committee} (log : SigningLog C) :
    List (LeanXmss.KeyIndex × LeanXmss.Message × C.Party) :=
  log.flatMap (fun entry => releaseStep [] entry.1 entry.2)

theorem releaseStep_append {C : Committee}
    (released : List (LeanXmss.KeyIndex × LeanXmss.Message × C.Party))
    (t : (LocalSpec C + TsigSpec C).Domain) (u : (LocalSpec C + TsigSpec C).Range t) :
    releaseStep released t u = released ++ releaseStep [] t u := by
  cases t with
  | inl t => simp [releaseStep]
  | inr t =>
    cases t <;> try simp [releaseStep]
    cases u <;> simp [releaseStep]

theorem releasedOfSigningLog_append {C : Committee} (log : SigningLog C)
    (t : (LocalSpec C + TsigSpec C).Domain) (u : (LocalSpec C + TsigSpec C).Range t) :
    releasedOfSigningLog (log.logQuery t u) = releaseStep (releasedOfSigningLog log) t u := by
  rw [releaseStep_append]
  simp [releasedOfSigningLog, QueryLog.logQuery, QueryLog.singleton]

theorem successfulRound2_mem_released {C : Committee} (log : SigningLog C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (parts : C.Party → LeanXmss.Digest) (values : LeanXmss.ChainIndex → Option LeanXmss.Digest)
    (hmem : ⟨.inr (.round2 i J e message parts), some values⟩ ∈ log) :
    (e, message, i) ∈ releasedOfSigningLog log := by
  apply List.mem_flatMap.mpr
  exact ⟨⟨.inr (.round2 i J e message parts), some values⟩, hmem, by simp [releaseStep]⟩

theorem tsigOracles_releaseStep {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((tsigOracles lift dealt t).run st)) :
    r.2.released = releaseStep st.released (.inr t) r.1 := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;> simp_all [StateT.run_set, StateT.run_pure, releaseStep]
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, run_liftM_comp, bind_map_left,
      mem_support_bind_iff] at hr
    obtain ⟨tree, _, hr⟩ := hr
    cases tree <;> simp_all [releaseStep]
    obtain ⟨value, _, rfl⟩ := hr
    rfl
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure, releaseStep]
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map,
        run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure, releaseStep]
    · simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
        mem_support_bind_iff] at hr
      obtain ⟨tree, _, hr⟩ := hr
      cases tree with
      | none => simp_all [StateT.run_pure, releaseStep]
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
          mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> simp_all [StateT.run_set, StateT.run_pure, releaseStep]


def signingLoggedOracles {C : Committee} (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT (TsigState C × SigningLog C) (OracleComp (WorldSpec C))) :=
  fun t => StateT.mk fun p => (fun z => (z.1, (z.2, p.2.logQuery t z.1))) <$>
    (SigningCoreProof.gameOracles dealt t).run p.1

theorem signingLoggedOracles_forget {C : Committee}
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) (log : SigningLog C) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (signingLoggedOracles dealt) oa).run (st, log) =
      (simulateQ (SigningCoreProof.gameOracles dealt) oa).run st :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun _ _ _ => by simp [signingLoggedOracles, Functor.map_map]) _ _ _

/-- The selected message is reconstructed from actual round-1 requests and
answers. No final-state `bound` lookup is needed to define it. -/
theorem signingLoggedOracles_bound {C : Committee}
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (signingLoggedOracles dealt) oa).run (SigningCoreProof.tsigInit, [])),
      r.2.1.bound = boundOfSigningLog r.2.2 := by
  apply SeedHitProof.support_simulateQ_inv (signingLoggedOracles dealt)
    (fun s : TsigState C × SigningLog C => s.1.bound = boundOfSigningLog s.2) _ oa _ rfl
  intro t s hs r hr
  simp only [signingLoggedOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  rw [boundOfSigningLog_append, ← hs]
  cases t with
  | inl t =>
    change z ∈ support ((fun a => (a, s.1)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hz
    simp only [support_map] at hz
    obtain ⟨value, _, rfl⟩ := hz
    rfl
  | inr t =>
    exact tsigOracles_bindingStep (fun oa => SigningCoreProof.honestLift oa) dealt t s.1 z hz

/-- The actual successful round-2 release ledger is reconstructed from the
public request/response transcript, including aborted attempts. -/
theorem signingLoggedOracles_released {C : Committee}
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (signingLoggedOracles dealt) oa).run (SigningCoreProof.tsigInit, [])),
      r.2.1.released = releasedOfSigningLog r.2.2 := by
  apply SeedHitProof.support_simulateQ_inv (signingLoggedOracles dealt)
    (fun s : TsigState C × SigningLog C => s.1.released = releasedOfSigningLog s.2) _ oa _ rfl
  intro t s hs r hr
  simp only [signingLoggedOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  rw [releasedOfSigningLog_append, ← hs]
  cases t with
  | inl t =>
    change z ∈ support ((fun a => (a, s.1)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hz
    simp only [support_map] at hz
    obtain ⟨value, _, rfl⟩ := hz
    rfl
  | inr t =>
    exact tsigOracles_releaseStep (fun oa => SigningCoreProof.honestLift oa) dealt t s.1 z hz

/-- A successful round-2 reply is possible only at the already bound message. -/
theorem tsigOracles_round2_bound {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (st final : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (parts : C.Party → LeanXmss.Digest) (values : LeanXmss.ChainIndex → Option LeanXmss.Digest)
    (hr : (some values, final) ∈ support
      ((tsigOracles lift dealt (.round2 i J e message parts)).run st)) :
    st.bound e = some message := by
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some_ne_none, false_and] at hr
    have hn := congrArg Prod.fst (Set.mem_singleton_iff.mp hr)
    cases hn
  · rename_i h
    exact not_not.mp (fun hn => h (Or.inr (Or.inr hn)))

def ReleasedBound {C : Committee} (st : TsigState C) : Prop :=
  ∀ e message i, (e, message, i) ∈ st.released → st.bound e = some message

theorem tsigOracles_releasedBound {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hs : ReleasedBound st) (hr : r ∈ support ((tsigOracles lift dealt t).run st)) :
    ReleasedBound r.2 := by
  have hext := tsigOracles_boundExtends lift dealt t st r hr
  have hrel := tsigOracles_releaseStep lift dealt t st r hr
  intro e message i hm
  rw [hrel] at hm
  cases t with
  | corrupt _ => exact hext _ _ (hs _ _ _ hm)
  | tree _ => exact hext _ _ (hs _ _ _ hm)
  | round1 _ _ _ _ => exact hext _ _ (hs _ _ _ hm)
  | round2 j J key msg parts =>
    rcases r with ⟨values, final⟩
    cases values with
    | none => exact hext _ _ (hs _ _ _ hm)
    | some values =>
      rcases List.mem_append.mp hm with hold | hnew
      · exact hext _ _ (hs _ _ _ hold)
      · have ht : (e, message, i) = (key, msg, j) := List.mem_singleton.mp hnew
        obtain ⟨he, hm, hi⟩ := Prod.mk.inj ht |>.imp_right Prod.mk.inj
        subst e
        subst message
        subst i
        exact hext _ _ (tsigOracles_round2_bound lift dealt st final j J key msg parts values hr)

theorem signingLoggedOracles_releasedBound {C : Committee}
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (signingLoggedOracles dealt) oa).run (SigningCoreProof.tsigInit, [])),
      ReleasedBound r.2.1 := by
  apply SeedHitProof.support_simulateQ_inv (signingLoggedOracles dealt)
    (fun s : TsigState C × SigningLog C => ReleasedBound s.1) _ oa _
      (by intro e message i h; cases h)
  intro t s hs r hr
  simp only [signingLoggedOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  cases t with
  | inl t =>
    change z ∈ support ((fun a => (a, s.1)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hz
    simp only [support_map] at hz
    obtain ⟨value, _, rfl⟩ := hz
    exact hs
  | inr t =>
    exact tsigOracles_releasedBound (fun oa => SigningCoreProof.honestLift oa) dealt t s.1 z hs hz

/-- Actual successful round-2 transcript entries provide both the recorded
signer and the permanent message binding needed by the share-view reduction. -/
theorem signingLoggedOracles_successfulRound2 {C : Committee}
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (r : α × TsigState C × SigningLog C)
    (hr : r ∈ support ((simulateQ (signingLoggedOracles dealt) oa).run (SigningCoreProof.tsigInit, [])))
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (parts : C.Party → LeanXmss.Digest) (values : LeanXmss.ChainIndex → Option LeanXmss.Digest)
    (hmem : ⟨.inr (.round2 i J e message parts), some values⟩ ∈ r.2.2) :
    r.2.1.bound e = some message ∧ i ∈ signersAt r.2.1 e message := by
  have hm := successfulRound2_mem_released r.2.2 i J e message parts values hmem
  rw [← signingLoggedOracles_released dealt oa r hr] at hm
  refine ⟨signingLoggedOracles_releasedBound dealt oa r hr e message i hm, ?_⟩
  apply Finset.mem_union_right
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨(e, message, i), ⟨hm, by simp⟩, rfl⟩

/-- The no-hidden-key flag permits an adversarial routed slot read only when
its seed is already revealed. This assertion is not applied to honest reads. -/
theorem hiddenHit_false_slot_revealed {C : Committee}
    (x : SigningSecurityProof.Keys3 C) (corrupt : Finset C.Party)
    (slot : TprfSecurityProof.Slot C)
    (hflag : SigningCoreProof.hiddenHit x corrupt
      (.inr (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 slot))) = false) :
    TprfSecurityProof.Revealed corrupt (TprfSecurityProof.slotKey slot) := by
  classical
  cases slot with
  | inl value =>
    rcases value with ⟨T, point⟩
    change decide (∃ S, x.2.1 T = x.2.1 S ∧
      ¬TprfSecurityProof.Revealed corrupt (.inl S)) = false at hflag
    by_contra hn
    exact (of_decide_eq_false hflag) ⟨T, rfl, hn⟩
  | inr value =>
    rcases value with ⟨pair, point, message, quorum⟩
    change decide (∃ p, x.2.2 pair = x.2.2 p ∧
      ¬TprfSecurityProof.Revealed corrupt (.inr p)) = false at hflag
    by_contra hn
    exact (of_decide_eq_false hflag) ⟨pair, rfl, hn⟩

theorem flaggedOracles_slot_revealed {C : Committee}
    (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (st : TsigState C) (flag : Bool) (slot : TprfSecurityProof.Slot C)
    (r : LeanXmss.HashOutput × TsigState C × Bool)
    (hr : r ∈ support ((SigningCoreProof.flaggedOracles x dealt
      (.inl (.inr (.inl (TprfSecurityProof.slotInput x.2.1 x.2.2 slot))))).run (st, flag)))
    (hflag : r.2.2 = false) :
    TprfSecurityProof.Revealed st.corrupt (TprfSecurityProof.slotKey slot) := by
  simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  apply hiddenHit_false_slot_revealed x st.corrupt slot
  exact (Bool.or_eq_false_iff.mp hflag).2

section PublicShareLog

open Classical
variable {C : Committee}

/-- Corruptions are permanent even when signing calls abort. -/
theorem tsigOracles_corrupt_mono {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((tsigOracles lift dealt t).run st)) :
    st.corrupt ⊆ r.2.corrupt := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;> simp_all [StateT.run_set, StateT.run_pure]
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, run_liftM_comp, bind_map_left,
      mem_support_bind_iff] at hr
    obtain ⟨tree, _, hr⟩ := hr
    cases tree <;> simp_all
    obtain ⟨value, _, rfl⟩ := hr
    exact Finset.Subset.refl _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map,
        run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact Finset.Subset.refl _
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure]
    · simp only [StateT.run_bind, run_liftM_comp, bind_map_left, mem_support_bind_iff] at hr
      obtain ⟨tree, _, hr⟩ := hr
      cases tree with
      | none => simp_all [StateT.run_pure]
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left, mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> simp_all [StateT.run_set, StateT.run_pure]

theorem gameOracles_corrupt_mono
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C)
    (r : (LocalSpec C + TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((SigningCoreProof.gameOracles dealt t).run st)) :
    st.corrupt ⊆ r.2.corrupt := by
  cases t with
  | inl t =>
    change r ∈ support ((fun a => (a, st)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hr
    simp only [support_map] at hr
    obtain ⟨value, _, rfl⟩ := hr
    exact Finset.Subset.refl _
  | inr t =>
    exact tsigOracles_corrupt_mono (fun oa => SigningCoreProof.honestLift oa) dealt t st r hr

theorem tsigOracles_round1_bound {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (st final : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (value : LeanXmss.Digest)
    (hr : (some value, final) ∈ support
      ((tsigOracles lift dealt (.round1 i J e message)).run st)) :
    final.bound e = some message := by
  have hb := tsigOracles_bindingStep lift dealt (.round1 i J e message) st
    (some value, final) hr
  simpa [bindingStep] using congrFun hb e

def Round1Bound (st : TsigState C) (log : SigningLog C) : Prop :=
  ∀ i J e message value,
    ⟨.inr (.round1 i J e message), some value⟩ ∈ log →
      st.bound e = some message

theorem signingLoggedOracles_round1Bound
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (signingLoggedOracles dealt) oa).run (SigningCoreProof.tsigInit, [])),
      Round1Bound r.2.1 r.2.2 := by
  apply SeedHitProof.support_simulateQ_inv (signingLoggedOracles dealt)
    (fun s : TsigState C × SigningLog C => Round1Bound s.1 s.2) _ oa _
    (by intro i J e msg value hm; cases hm)
  intro t s hs r hr
  simp only [signingLoggedOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  have hext : BoundExtends s.1 z.2 := by
    have h := gameOracles_boundExtends dealt (OracleComp.lift (OracleSpec.query t)) s.1 z
    exact h (by simpa using hz)
  intro i J e msg value hm
  simp only [QueryLog.logQuery, QueryLog.singleton, List.mem_append, List.mem_singleton] at hm
  rcases hm with hold | hnew
  · exact hext _ _ (hs _ _ _ _ _ hold)
  · rcases z with ⟨answer, final⟩
    cases hnew
    exact tsigOracles_round1_bound (fun oa => SigningCoreProof.honestLift oa)
      dealt s.1 final i J e msg value hz

def flaggedLoggedOracles (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT ((TsigState C × Bool) × SigningLog C) (OracleComp (WorldSpec C))) :=
  fun t => StateT.mk fun s =>
    (fun r => (r.1, (r.2, s.2.logQuery t r.1))) <$>
      (SigningCoreProof.flaggedOracles x dealt t).run s.1

theorem flaggedLoggedOracles_forget (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) (flag : Bool)
    (log : SigningLog C) :
    (fun r => (r.1, r.2.1)) <$>
      (simulateQ (flaggedLoggedOracles x dealt) oa).run ((st, flag), log) =
      (simulateQ (SigningCoreProof.flaggedOracles x dealt) oa).run (st, flag) :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun _ _ _ => by simp [flaggedLoggedOracles, Functor.map_map]) _ _ _

theorem flaggedOracles_corrupt_mono (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C) (flag : Bool)
    (r : (LocalSpec C + TsigSpec C).Range t × TsigState C × Bool)
    (hr : r ∈ support ((SigningCoreProof.flaggedOracles x dealt t).run (st, flag))) :
    st.corrupt ⊆ r.2.1.corrupt := by
  apply gameOracles_corrupt_mono dealt t st (r.1, r.2.1)
  rw [← SigningCoreProof.flaggedOracles_forget x dealt t st flag, support_map]
  exact ⟨r, hr, rfl⟩

theorem flaggedOracles_flag_false (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C) (flag : Bool)
    (r : (LocalSpec C + TsigSpec C).Range t × TsigState C × Bool)
    (hr : r ∈ support ((SigningCoreProof.flaggedOracles x dealt t).run (st, flag)))
    (hf : r.2.2 = false) : flag = false := by
  cases t with
  | inl t =>
    simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, support_map] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    exact (Bool.or_eq_false_iff.mp hf).1
  | inr t =>
    simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, support_map] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    exact hf

def PublicReadsRevealed (x : SigningSecurityProof.Keys3 C) (D : Finset C.Party)
    (log : SigningLog C) : Prop :=
  ∀ slot answer, ⟨.inl (.inr (.inl
    (TprfSecurityProof.slotInput x.2.1 x.2.2 slot))), answer⟩ ∈ log →
      TprfSecurityProof.Revealed D (TprfSecurityProof.slotKey slot)

/-- Only public adversarial reads enter this invariant. Honest internal slot
reads are absent, including the reads made by failed signing attempts. -/
theorem flaggedLoggedOracles_readsRevealed (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (flaggedLoggedOracles x dealt) oa).run
        ((SigningCoreProof.tsigInit, false), [])),
      r.2.1.2 = false → PublicReadsRevealed x r.2.1.1.corrupt r.2.2 := by
  apply SeedHitProof.support_simulateQ_inv (flaggedLoggedOracles x dealt)
    (fun s : (TsigState C × Bool) × SigningLog C =>
      s.1.2 = false → PublicReadsRevealed x s.1.1.corrupt s.2) _ oa _
    (by intro _ slot answer hm; cases hm)
  intro t s hs r hr
  simp only [flaggedLoggedOracles, StateT.run_mk, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  intro hf slot answer hm
  simp only [QueryLog.logQuery, QueryLog.singleton, List.mem_append, List.mem_singleton] at hm
  rcases hm with hold | hnew
  · exact TprfSecurityProof.revealed_mono
      (flaggedOracles_corrupt_mono x dealt t s.1.1 s.1.2 z hz)
      (hs (flaggedOracles_flag_false x dealt t s.1.1 s.1.2 z hz hf) slot answer hold)
  · rcases z with ⟨reply, final⟩
    cases hnew
    exact TprfSecurityProof.revealed_mono
      (flaggedOracles_corrupt_mono x dealt _ s.1.1 s.1.2 _ hz)
      (flaggedOracles_slot_revealed x dealt s.1.1 s.1.2 slot _ hz hf)

theorem flaggedLoggedOracles_round1Bound (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (flaggedLoggedOracles x dealt) oa).run
        ((SigningCoreProof.tsigInit, false), [])),
      Round1Bound r.2.1.1 r.2.2 := by
  apply SeedHitProof.support_simulateQ_inv (flaggedLoggedOracles x dealt)
    (fun s : (TsigState C × Bool) × SigningLog C => Round1Bound s.1.1 s.2) _ oa _
    (by intro i J e msg value hm; cases hm)
  intro t s hs r hr
  simp only [flaggedLoggedOracles, StateT.run_mk, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  have hg : (z.1, z.2.1) ∈ support ((SigningCoreProof.gameOracles dealt t).run s.1.1) := by
    rw [← SigningCoreProof.flaggedOracles_forget x dealt t s.1.1 s.1.2, support_map]
    exact ⟨z, hz, rfl⟩
  have hext : BoundExtends s.1.1 z.2.1 :=
    gameOracles_boundExtends dealt (OracleComp.lift (OracleSpec.query t)) s.1.1 (z.1, z.2.1)
      (by simpa using hg)
  intro i J e msg value hm
  simp only [QueryLog.logQuery, QueryLog.singleton, List.mem_append, List.mem_singleton] at hm
  rcases hm with hold | hnew
  · exact hext _ _ (hs _ _ _ _ _ hold)
  · rcases z with ⟨answer, final⟩
    cases hnew
    exact tsigOracles_round1_bound (fun oa => SigningCoreProof.honestLift oa)
      dealt s.1.1 final.1 i J e msg value hg

def round1Record : (t : (LocalSpec C + TsigSpec C).Domain) →
    (LocalSpec C + TsigSpec C).Range t → List (TprfSecurityProof.EvalRecord C)
  | .inr (.round1 i J e message), some value =>
    [⟨i, J, .randomizer LeanXmss.bottomLayer e, message, TprfCorrectnessProof.toXor value⟩]
  | _, _ => []

def round1Records (log : SigningLog C) : List (TprfSecurityProof.EvalRecord C) :=
  log.flatMap fun entry => round1Record entry.1 entry.2

theorem mem_round1Records (log : SigningLog C) (record : TprfSecurityProof.EvalRecord C)
    (h : record ∈ round1Records log) :
    ∃ i J e message value,
      ⟨.inr (.round1 i J e message), some value⟩ ∈ log ∧
      record = ⟨i, J, .randomizer LeanXmss.bottomLayer e, message,
        TprfCorrectnessProof.toXor value⟩ := by
  obtain ⟨⟨input, answer⟩, hmem, hrecord⟩ := List.mem_flatMap.mp h
  cases input with
  | inl input => cases input <;> simp [round1Record] at hrecord
  | inr input =>
    cases input with
    | corrupt _ => simp [round1Record] at hrecord
    | tree _ => simp [round1Record] at hrecord
    | round2 _ _ _ _ _ => simp [round1Record] at hrecord
    | round1 i J e msg =>
      cases answer with
      | none => simp [round1Record] at hrecord
      | some value =>
        exact ⟨i, J, e, msg, value, hmem, List.mem_singleton.mp hrecord⟩

theorem round1Records_chain_queriers (log : SigningLog C)
    (lay : LeanXmss.Layer) (e : LeanXmss.KeyIndex) (l : LeanXmss.ChainIndex)
    (digit : LeanXmss.Digit) (message : LeanXmss.Message) :
    TprfSecurityProof.recordQueriers (round1Records log) (.chain lay e l digit) message = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [TprfSecurityProof.recordQueriers, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨r, ⟨hr, hx, hm⟩, _⟩ := hi
  obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_round1Records log r hr
  cases hx

theorem round1Records_unbound_queriers (st : TsigState C) (log : SigningLog C)
    (hbound : Round1Bound st log) (e : LeanXmss.KeyIndex)
    (hunbound : st.bound e = none) (message : LeanXmss.Message) :
    TprfSecurityProof.recordQueriers (round1Records log)
      (.randomizer LeanXmss.bottomLayer e) message = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [TprfSecurityProof.recordQueriers, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨r, ⟨hr, hx, hm⟩, _⟩ := hi
  obtain ⟨party, J, key, msg, value, hmem, rfl⟩ := mem_round1Records log r hr
  have hk : key = e := by simpa only [Point.randomizer.injEq, true_and] using hx
  subst key
  have hb := hbound party J e msg value hmem
  rw [hunbound] at hb
  cases hb

/-- All slot interpretations of a public hash request are retained. Distinct
keys later make the interpretation unique; revelation holds even without it. -/
def publicSlotReads (x : SigningSecurityProof.Keys3 C) (log : SigningLog C) :
    List (TprfSecurityProof.Slot C × LeanXmss.HashOutput) :=
  log.flatMap fun entry =>
    match entry with
    | ⟨.inl (.inr (.inl input)), answer⟩ =>
      ((Finset.univ.filter fun slot =>
        TprfSecurityProof.slotInput x.2.1 x.2.2 slot = input).toList.map
          fun slot => (slot, answer))
    | _ => []

theorem publicSlotReads_revealed (x : SigningSecurityProof.Keys3 C) (D : Finset C.Party)
    (log : SigningLog C) (hrevealed : PublicReadsRevealed x D log) :
    ∀ read ∈ publicSlotReads x log, TprfSecurityProof.Revealed D
      (TprfSecurityProof.slotKey read.1) := by
  intro read hr
  obtain ⟨⟨input, answer⟩, hmem, hread⟩ := List.mem_flatMap.mp hr
  cases input with
  | inr input => cases input <;> simp [publicSlotReads] at hread
  | inl input =>
    cases input with
    | inl input => simp [publicSlotReads] at hread
    | inr input =>
      cases input with
      | inr input => simp [publicSlotReads] at hread
      | inl input =>
        simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
          Finset.mem_univ, true_and, decide_eq_true_eq] at hread
        obtain ⟨slot, hslot, rfl⟩ := hread
        subst input
        exact hrevealed slot answer hmem

end PublicShareLog

/-- The selected trial reconstructed from the signing transcript and the hash
cache. The transcript supplies the message; the cached search supplies the trial. -/
def selectedOfSigningLog {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree) (e : LeanXmss.KeyIndex)
    (cache : HashCache C) (log : SigningLog C) :
    Option (LeanXmss.Message × LeanXmss.Randomness) := do
  let message ← boundOfSigningLog log e
  let h := SigningCacheProof.answersOf cache
  let dealt := dealtWith (m := Id) (fun oa => D prims h oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top
    (fun p => D prims h (prfValue x.2.1 p))
  let tree ← dealt.bottom (treeOf e)
  let ρ := D prims h (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer e))
  let (randomness, _) ← D prims h (signCodeword x.1 (tree.commitment e) e message ρ)
  pure (message, randomness)

theorem selectedOfSigningLog_eq {C : Committee} (prims : Primitives)
    (z : SigningDescentProof.FinalState C) (log : SigningLog C)
    (hb : z.state.bound = boundOfSigningLog log) :
    selectedOfSigningLog prims z.keys z.top z.key z.cache log = z.selected prims := by
  simp only [selectedOfSigningLog, SigningDescentProof.FinalState.selected, hb,
    SigningDescentProof.FinalState.bottomTree, SigningDescentProof.FinalState.dealt]
  rfl

/-- An accepted opening is either canonical or a different preimage. This is
an output-match event, distinct from the chain/leaf/node predicate `Hit`. -/
def DifferentOpening {C : Committee} (h : Query C → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (canonical candidate : LeanXmss.Digest) : Prop :=
  candidate ≠ canonical ∧
    LeanXmss.truncateHash (h (.hash (commitmentInput P e candidate))) =
      LeanXmss.truncateHash (h (.hash (commitmentInput P e canonical)))

theorem signCodeword_some_commitment {C : Committee} (prims : Primitives)
    (h : Query C → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (commitment : LeanXmss.Digest) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (candidate : LeanXmss.Digest) (selected : LeanXmss.Randomness × LeanXmss.Encoding)
    (hs : D prims h (signCodeword P commitment e message candidate) = some selected) :
    LeanXmss.truncateHash (h (.hash (commitmentInput P e candidate))) = commitment := by
  unfold signCodeword at hs
  change E prims h _ = some selected at hs
  rw [E_bind, E_oracleHash] at hs
  dsimp only at hs
  split at hs
  · simp [E_pure] at hs
  · simpa only [not_not] using ‹¬LeanXmss.truncateHash
      (h (.hash (commitmentInput P e candidate))) ≠ commitment›

theorem signCodeword_canonical_or_opening {C : Committee} (prims : Primitives)
    (h : Query C → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (canonical candidate : LeanXmss.Digest)
    (selected : LeanXmss.Randomness × LeanXmss.Encoding)
    (hs : D prims h (signCodeword P
      (LeanXmss.truncateHash (h (.hash (commitmentInput P e canonical)))) e message candidate) = some selected) :
    candidate = canonical ∨ DifferentOpening h P e canonical candidate := by
  by_cases hc : candidate = canonical
  · exact Or.inl hc
  · exact Or.inr ⟨hc, signCodeword_some_commitment prims h P _ e message candidate selected hs⟩

/-- Outside the different-preimage event, every accepted round-2 codeword is
the canonical codeword of the already-bound message, for every quorum/parts. -/
theorem signCodeword_canonical {C : Committee} (prims : Primitives)
    (h : Query C → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (canonical candidate : LeanXmss.Digest)
    (selected : LeanXmss.Randomness × LeanXmss.Encoding)
    (hs : D prims h (signCodeword P
      (LeanXmss.truncateHash (h (.hash (commitmentInput P e canonical)))) e message candidate) = some selected)
    (hn : ¬DifferentOpening h P e canonical candidate) :
    E prims h (grind P LeanXmss.bottomLayer e (LeanXmss.bytesLE 32 message)
      (LeanXmss.truncateHash (h (.hash (randomizerInput P LeanXmss.bottomLayer e canonical
        (LeanXmss.bytesLE 32 message))))) LeanXmss.randomizerAttemptLimit 0) = some selected := by
  have hc := (signCodeword_canonical_or_opening prims h P e message canonical candidate selected hs).resolve_right hn
  subst candidate
  rw [D_signCodeword (prims := prims) (h := h) _ _ _ _ _ rfl] at hs
  exact hs

/-- The canonical-opening reduction applies to actual counted executions,
including cache hits, by replay on any table agreeing with the final cache. -/
theorem run_signCodeword_canonical {C : Committee} (prims : Primitives)
    (h : Query C → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (canonical candidate : LeanXmss.Digest) (s : HashCache C × ℕ)
    (r : Option (LeanXmss.Randomness × LeanXmss.Encoding) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (signCodeword P
        (LeanXmss.truncateHash (h (.hash (commitmentInput P e canonical))))
        e message candidate))).run s))
    (ha : Agrees h r.2.1) (hn : ¬DifferentOpening h P e canonical candidate)
    (selected : LeanXmss.Randomness × LeanXmss.Encoding) (hs : r.1 = some selected) :
    E prims h (grind P LeanXmss.bottomLayer e (LeanXmss.bytesLE 32 message)
      (LeanXmss.truncateHash (h (.hash (randomizerInput P LeanXmss.bottomLayer e canonical
        (LeanXmss.bytesLE 32 message))))) LeanXmss.randomizerAttemptLimit 0) = some selected := by
  apply signCodeword_canonical prims h P e message canonical candidate selected _ hn
  exact (SigningCacheProof.run_liftFree prims _ s r hr h ha).symm.trans hs

/-- Repeated accepted sessions, even with different submitted parts, cannot
select two codewords for the bound message without a different opening. -/
theorem canonicalSelections_unique {C : Committee} (prims : Primitives)
    (h : Query C → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (canonical candidate₁ candidate₂ : LeanXmss.Digest)
    (selected₁ selected₂ : LeanXmss.Randomness × LeanXmss.Encoding)
    (hs₁ : D prims h (signCodeword P
      (LeanXmss.truncateHash (h (.hash (commitmentInput P e canonical))))
      e message candidate₁) = some selected₁)
    (hs₂ : D prims h (signCodeword P
      (LeanXmss.truncateHash (h (.hash (commitmentInput P e canonical))))
      e message candidate₂) = some selected₂)
    (hn₁ : ¬DifferentOpening h P e canonical candidate₁)
    (hn₂ : ¬DifferentOpening h P e canonical candidate₂) : selected₁ = selected₂ := by
  exact Option.some.inj
    ((signCodeword_canonical prims h P e message canonical candidate₁ selected₁ hs₁ hn₁).symm.trans
      (signCodeword_canonical prims h P e message canonical candidate₂ selected₂ hs₂ hn₂))

/-- Exact, unnormalized hiding of one PRF value from a threshold-share view.
This includes adaptive choices once a transcript is fixed; it does not yet
include the public chain/commitment hash outputs of signing key generation. -/
theorem prf_value_uniform_given_share_view {C : Committee}
    (records : List (TprfSecurityProof.EvalRecord C)) (D : Finset C.Party)
    (reads : List (TprfSecurityProof.Slot C × LeanXmss.HashOutput)) (x : Point)
    (Tstar : C.Term) (hT : D ⊆ Tstar.1)
    (hquorum : ∀ message,
      (D ∪ TprfSecurityProof.recordQueriers records x message).card ≤ C.t - 1)
    (hreads : ∀ r ∈ reads, TprfSecurityProof.Revealed D (TprfSecurityProof.slotKey r.1))
    (value : TprfCorrectnessProof.XorDigest) :
    Pr[TprfSecurityProof.Consistent records reads {x} (fun _ => value) |
      $ᵗ (TprfSecurityProof.Slot C → LeanXmss.HashOutput)] =
      Pr[TprfSecurityProof.Consistent records reads ∅ (fun _ => value) |
        $ᵗ (TprfSecurityProof.Slot C → LeanXmss.HashOutput)] / 2 ^ 128 := by
  classical
  have hc := TprfSecurityProof.card_consistent_mul (records := records)
    (D := D) (challenged := {x}) (Tstar := Tstar) hT
    (by intro y hy; simp only [Finset.mem_singleton] at hy; subst y; exact hquorum)
    reads hreads (fun _ => value)
  simp only [Finset.card_singleton, pow_one] at hc
  rw [probEvent_uniformSample, probEvent_uniformSample, ← hc, Nat.cast_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat, LeanXmss.digestBits]
  rw [ENNReal.mul_div_right_comm, ENNReal.mul_div_cancel_right (by norm_num [LeanXmss.digestBits])
    (by norm_num [LeanXmss.digestBits])]

section ShareFibers

open Classical TprfSecurityProof TprfCorrectnessProof

variable {C : Committee}
  (records : List (EvalRecord C)) (D : Finset C.Party)
  (hidden : Finset Point) (Tstar : C.Term)

/-- The hiding bijection leaves every PRF value outside its hidden set alone.
In particular, it preserves values that earlier signing sessions released. -/
theorem prfSum_shiftTable_outside (δ : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → LeanXmss.HashOutput) {x : Point} (hx : x ∉ hidden) :
    prfSum (shiftTable records D hidden Tstar δ ω) x = prfSum ω x := by
  simp [prfSum, shiftTable, shiftOf, hx]

def ReleasedValues (released : Finset Point)
    (values : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → LeanXmss.HashOutput) : Prop :=
  ∀ x ∈ released, prfSum ω x = values x

variable (hT : D ⊆ Tstar.1)
  (hinv : ∀ x ∈ hidden, ∀ message, (D ∪ recordQueriers records x message).card ≤ C.t - 1)
  (reads : List (Slot C × LeanXmss.HashOutput))
  (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))

include hT hinv hreads

/-- Extra observations are permitted when the share-table bijection preserves
them. This separates the counting argument from the eventual public-view coupling. -/
theorem card_consistent_extra_eq
    (extra : (Slot C → LeanXmss.HashOutput) → Prop)
    (hextra : ∀ δ ω, extra (shiftTable records D hidden Tstar δ ω) ↔ extra ω)
    (c c' : Point → TprfCorrectnessProof.XorDigest) :
    (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads hidden c ω ∧ extra ω).card =
      (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads hidden c' ω ∧ extra ω).card := by
  classical
  let shift := shiftTable records D hidden Tstar (fun x => c x + c' x)
  refine Finset.card_nbij' shift shift (fun ω hω => ?_) (fun ω hω => ?_)
    (fun ω _ => shiftTable_shiftTable _ _) (fun ω _ => shiftTable_shiftTable _ _)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    exact ⟨consistent_shiftTable hT hinv reads hreads hω.1, (hextra _ _).mpr hω.2⟩
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    have hc := consistent_shiftTable hT hinv reads hreads (c' := c) hω.1
    have hδ : (fun x => c' x + c x) = fun x => c x + c' x := funext fun x => add_comm _ _
    rw [hδ] at hc
    exact ⟨hc, (hextra _ _).mpr hω.2⟩

theorem card_consistent_extra_mul
    (extra : (Slot C → LeanXmss.HashOutput) → Prop)
    (hextra : ∀ δ ω, extra (shiftTable records D hidden Tstar δ ω) ↔ extra ω)
    (c : Point → TprfCorrectnessProof.XorDigest) :
    (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads hidden c ω ∧ extra ω).card *
        (2 ^ LeanXmss.digestBits) ^ hidden.card =
      (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads ∅ c ω ∧ extra ω).card := by
  classical
  letI : Fintype TprfCorrectnessProof.XorDigest := inferInstanceAs (Fintype LeanXmss.Digest)
  letI : DecidableEq TprfCorrectnessProof.XorDigest := inferInstanceAs (DecidableEq LeanXmss.Digest)
  let f : (Slot C → LeanXmss.HashOutput) → (hidden → TprfCorrectnessProof.XorDigest) := fun ω x => prfSum ω x.1
  rw [Finset.card_eq_sum_card_fiberwise (f := f)
    (s := Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads ∅ c ω ∧ extra ω)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ d : hidden → TprfCorrectnessProof.XorDigest,
      ((Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads ∅ c ω ∧ extra ω).filter
        fun ω => f ω = d).card =
      (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads hidden c ω ∧ extra ω).card := by
    intro d
    rw [card_consistent_extra_eq records D hidden Tstar hT hinv reads hreads extra hextra c
      (fun x => if h : x ∈ hidden then d ⟨x, h⟩ else 0), Finset.filter_filter]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro ω _
    have he : (f ω = d) ↔ ∀ x ∈ hidden,
        prfSum ω x = (if h : x ∈ hidden then d ⟨x, h⟩ else 0) := by
      constructor
      · intro h x hx
        rw [dif_pos hx]
        exact congrFun h ⟨x, hx⟩
      · intro h
        funext x
        simpa only [dif_pos x.2] using h x.1 x.2
    rw [he]
    simp only [TprfSecurityProof.Consistent, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true]
    exact ⟨fun h => ⟨⟨h.1.1.1, h.1.1.2, h.2⟩, h.1.2⟩,
      fun h => ⟨⟨⟨h.1.1, h.1.2.1⟩, h.2⟩, h.1.2.2⟩⟩
  have hcard : Fintype.card TprfCorrectnessProof.XorDigest = 2 ^ LeanXmss.digestBits := by
    change Fintype.card LeanXmss.Digest = _
    simp
  rw [Finset.sum_congr rfl fun d _ => hfiber d, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_fun, Fintype.card_coe, hcard, mul_comm]

/-- Already released values, including values reconstructed by a quorum, do
not consume the entropy of the disjoint hidden coordinates. -/
theorem card_consistent_released_mul
    (released : Finset Point) (hdisjoint : Disjoint hidden released)
    (releasedValues c : Point → TprfCorrectnessProof.XorDigest) :
    (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads hidden c ω ∧
      ReleasedValues released releasedValues ω).card *
        (2 ^ LeanXmss.digestBits) ^ hidden.card =
      (Finset.univ.filter fun ω => TprfSecurityProof.Consistent records reads ∅ c ω ∧
        ReleasedValues released releasedValues ω).card := by
  apply card_consistent_extra_mul records D hidden Tstar hT hinv reads hreads
  intro δ ω
  have houtside : ∀ x ∈ released,
      prfSum (shiftTable records D hidden Tstar δ ω) x = prfSum ω x := by
    intro x hx
    exact prfSum_shiftTable_outside records D hidden Tstar δ ω
      (fun hh => Finset.disjoint_left.mp hdisjoint hh hx)
  exact forall_congr' fun x => forall_congr' fun hx => by rw [houtside x hx]

/-- Exact unnormalized probability after arbitrary earlier authorized releases.
Only the point still being hidden is subject to the threshold restriction. -/
theorem prf_value_uniform_given_releases
    (x : Point) (hhidden : hidden = {x})
    (released : Finset Point) (hdisjoint : Disjoint hidden released)
    (releasedValues : Point → TprfCorrectnessProof.XorDigest) (value : TprfCorrectnessProof.XorDigest) :
    Pr[fun ω => TprfSecurityProof.Consistent records reads hidden (fun _ => value) ω ∧
      ReleasedValues released releasedValues ω |
        $ᵗ (Slot C → LeanXmss.HashOutput)] =
      Pr[fun ω => TprfSecurityProof.Consistent records reads ∅ (fun _ => value) ω ∧
        ReleasedValues released releasedValues ω |
          $ᵗ (Slot C → LeanXmss.HashOutput)] / 2 ^ 128 := by
  classical
  have hc := card_consistent_released_mul records D hidden Tstar hT hinv reads hreads
    released hdisjoint releasedValues (fun _ => value)
  rw [hhidden, Finset.card_singleton, pow_one] at hc
  rw [hhidden, probEvent_uniformSample, probEvent_uniformSample, ← hc, Nat.cast_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat, LeanXmss.digestBits]
  rw [ENNReal.mul_div_right_comm, ENNReal.mul_div_cancel_right (by norm_num)
    (by norm_num)]

end ShareFibers

section ShareRefresh

open Classical TprfSecurityProof

variable {C : Committee}

local instance : Fintype TprfCorrectnessProof.XorDigest :=
  inferInstanceAs (Fintype LeanXmss.Digest)

local instance : SampleableType TprfCorrectnessProof.XorDigest :=
  SampleableType.ofFintype _

/-- Install one prescribed PRF value by shifting its missing term and the
private masks that preserve previously returned shares. -/
def refreshShareTable (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point) (ω : Slot C → LeanXmss.HashOutput)
    (value : TprfCorrectnessProof.XorDigest) : Slot C → LeanXmss.HashOutput :=
  shiftTable records D {x} Tstar (fun _ => prfSum ω x + value) ω

theorem refreshShareTable_value (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point) (ω : Slot C → LeanXmss.HashOutput)
    (value : TprfCorrectnessProof.XorDigest) :
    prfSum (refreshShareTable records D Tstar x ω value) x = value := by
  rw [refreshShareTable, prfSum_shiftTable _ _ (Finset.mem_singleton_self _),
    ← add_assoc, TprfSecurityProof.XorDigest.add_self, zero_add]

/-- Swap a fresh value with the table's old PRF sum. Retaining the old sum
makes installation a bijection rather than a many-to-one overwrite. -/
def refreshSharePair (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point)
    (p : (Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest) :
    (Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest :=
  (refreshShareTable records D Tstar x p.1 p.2, prfSum p.1 x)

theorem refreshSharePair_involutive (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point) : Function.Involutive (refreshSharePair records D Tstar x) := by
  rintro ⟨ω, value⟩
  apply Prod.ext
  · change refreshShareTable records D Tstar x
      (refreshShareTable records D Tstar x ω value) (prfSum ω x) = ω
    rw [refreshShareTable, refreshShareTable_value]
    have hδ : (fun _ : Point => value + prfSum ω x) = fun _ : Point => prfSum ω x + value :=
      funext fun _ => add_comm _ _
    rw [hδ, refreshShareTable, shiftTable_shiftTable]
  · exact refreshShareTable_value records D Tstar x ω value

theorem refreshSharePair_uniform (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point) :
    𝒟[refreshSharePair records D Tstar x <$>
      ($ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest))] =
      𝒟[$ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest)] := by
  exact evalDist_map_bijective_uniform_cross
    (α := (Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest)
    (refreshSharePair records D Tstar x)
    (refreshSharePair_involutive records D Tstar x).bijective

/-- Exact joint lazy-to-eager law for a threshold PRF coordinate: a fresh
uniform value installed in the share table has the real table/value law. -/
theorem refreshShareTable_joint (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point) :
    𝒟[(fun p => (refreshShareTable records D Tstar x p.1 p.2, p.2)) <$>
      ($ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest))] =
      𝒟[(fun ω => (ω, prfSum ω x)) <$> ($ᵗ (Slot C → LeanXmss.HashOutput))] := by
  let observe : ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest) →
      (Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest :=
    fun p => (p.1, prfSum p.1 x)
  have he : (fun p => (refreshShareTable records D Tstar x p.1 p.2, p.2)) =
      observe ∘ refreshSharePair records D Tstar x := by
    funext p
    simp only [Function.comp_apply, observe, refreshSharePair, refreshShareTable_value]
  have hc : (fun p => (refreshShareTable records D Tstar x p.1 p.2, p.2)) <$>
      ($ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest)) =
      observe <$> (refreshSharePair records D Tstar x <$>
        ($ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest))) := by
    rw [Functor.map_map, he]
    rfl
  rw [hc, evalDist_map, refreshSharePair_uniform, ← evalDist_map]
  have hm : observe <$> ($ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest)) =
      (fun ω => (ω, prfSum ω x)) <$>
        (Prod.fst <$> ($ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest))) := by
    rw [Functor.map_map]
  rw [hm, evalDist_map, evalDist_map_fst_uniformSample_prod, ← evalDist_map]

/-- Installation preserves the share view and all previously released values.
Threshold restrictions concern only the point currently being installed. -/
theorem refreshShareTable_preserves_view
    (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (hT : D ⊆ Tstar.1) (x : Point)
    (hquorum : ∀ message, (D ∪ recordQueriers records x message).card ≤ C.t - 1)
    (reads : List (Slot C × LeanXmss.HashOutput))
    (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))
    (released : Finset Point) (hx : x ∉ released)
    (releasedValues : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → LeanXmss.HashOutput) (value : TprfCorrectnessProof.XorDigest)
    (hv : TprfSecurityProof.Consistent records reads ∅ (fun _ => value) ω)
    (hr : ReleasedValues released releasedValues ω) :
    TprfSecurityProof.Consistent records reads ∅ (fun _ => value)
      (refreshShareTable records D Tstar x ω value) ∧
      ReleasedValues released releasedValues (refreshShareTable records D Tstar x ω value) := by
  have hi : ∀ y ∈ ({x} : Finset Point), ∀ message,
      (D ∪ recordQueriers records y message).card ≤ C.t - 1 := by
    intro y hy
    simpa only [Finset.mem_singleton.mp hy] using hquorum
  have hc : TprfSecurityProof.Consistent records reads {x} (fun _ => prfSum ω x) ω :=
    ⟨hv.1, hv.2.1, fun y hy => by rw [Finset.mem_singleton.mp hy]⟩
  have hs := consistent_shiftTable hT hi reads hreads (c' := fun _ => value) hc
  refine ⟨⟨hs.1, hs.2.1, fun _ hy => (Finset.notMem_empty _ hy).elim⟩, ?_⟩
  intro y hy
  rw [refreshShareTable, prfSum_shiftTable_outside records D {x} Tstar _ _
    (by simpa only [Finset.mem_singleton] using fun he : y = x => hx (he ▸ hy))]
  exact hr y hy

/-- The constraints carried by the share simulator after earlier releases. -/
def ShareView (records : List (EvalRecord C)) (reads : List (Slot C × LeanXmss.HashOutput))
    (released : Finset Point) (values : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → LeanXmss.HashOutput) : Prop :=
  TprfSecurityProof.Consistent records reads ∅ (fun _ => 0) ω ∧
    ReleasedValues released values ω

theorem refreshSharePair_view_iff
    (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (hT : D ⊆ Tstar.1) (x : Point)
    (hquorum : ∀ message, (D ∪ recordQueriers records x message).card ≤ C.t - 1)
    (reads : List (Slot C × LeanXmss.HashOutput))
    (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))
    (released : Finset Point) (hx : x ∉ released)
    (values : Point → TprfCorrectnessProof.XorDigest)
    (p : (Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest) :
    ShareView records reads released values (refreshSharePair records D Tstar x p).1 ↔
      ShareView records reads released values p.1 := by
  have forward : ∀ p, ShareView records reads released values p.1 →
      ShareView records reads released values (refreshSharePair records D Tstar x p).1 := by
    intro p hp
    obtain ⟨hc, hr⟩ := refreshShareTable_preserves_view records D Tstar hT x hquorum
      reads hreads released hx values p.1 p.2
      ⟨hp.1.1, hp.1.2.1, by simp⟩ hp.2
    exact ⟨⟨hc.1, hc.2.1, by simp⟩, hr⟩
  refine ⟨fun h => ?_, forward p⟩
  have hback := forward (refreshSharePair records D Tstar x p) h
  simpa only [refreshSharePair_involutive records D Tstar x p] using hback

/-- The reprogramming law holds with the complete recorded share view fixed,
without dividing by its probability or assuming the view has positive mass. -/
theorem refreshShareTable_joint_given_view
    (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (hT : D ⊆ Tstar.1) (x : Point)
    (hquorum : ∀ message, (D ∪ recordQueriers records x message).card ≤ C.t - 1)
    (reads : List (Slot C × LeanXmss.HashOutput))
    (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))
    (released : Finset Point) (hx : x ∉ released)
    (values : Point → TprfCorrectnessProof.XorDigest)
    (event : ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest) → Prop) :
    Pr[fun p => ShareView records reads released values p.1 ∧
      event (refreshShareTable records D Tstar x p.1 p.2, p.2) |
        $ᵗ ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest)] =
      Pr[fun ω => ShareView records reads released values ω ∧ event (ω, prfSum ω x) |
        $ᵗ (Slot C → LeanXmss.HashOutput)] := by
  have he := probEvent_congr'
    (p := fun p => ShareView records reads released values p.1 ∧ event p)
    (fun _ _ => Iff.rfl) (refreshShareTable_joint records D Tstar x)
  rw [probEvent_map, probEvent_map] at he
  refine (probEvent_congr' (fun p _ => ?_) rfl).trans he
  exact and_congr_left fun _ =>
    (refreshSharePair_view_iff records D Tstar hT x hquorum reads hreads released hx values p).symm

local instance : DecidableEq TprfCorrectnessProof.XorDigest :=
  inferInstanceAs (DecidableEq LeanXmss.Digest)

local instance shareViewDecidable (records : List (EvalRecord C))
    (reads : List (Slot C × LeanXmss.HashOutput)) (released : Finset Point)
    (values : Point → TprfCorrectnessProof.XorDigest) :
    DecidablePred (ShareView records reads released values) := Classical.decPred _

set_option maxRecDepth 100000 in
/-- Install a prescribed value at a release, with the full continuation weight
retained. This is the finite-fiber law needed when the public forest already
depends on that value; the value is not resampled independently of the forest. -/
theorem refreshShareTable_weighted
    (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (hT : D ⊆ Tstar.1) (x : Point)
    (hquorum : ∀ message, (D ∪ recordQueriers records x message).card ≤ C.t - 1)
    (reads : List (Slot C × LeanXmss.HashOutput))
    (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))
    (released : Finset Point) (hx : x ∉ released)
    (values : Point → TprfCorrectnessProof.XorDigest)
    (value : TprfCorrectnessProof.XorDigest)
    (f : (Slot C → LeanXmss.HashOutput) → ℝ≥0∞) :
    (∑ ω, if ShareView records reads released values ω then
      f (refreshShareTable records D Tstar x ω value) else 0) =
      (2 ^ 128 : ℝ≥0∞) * ∑ ω,
        if ShareView records reads released values ω ∧ prfSum ω x = value then f ω else 0 := by
  let g : ((Slot C → LeanXmss.HashOutput) × TprfCorrectnessProof.XorDigest) → ℝ≥0∞ :=
    fun p => if ShareView records reads released values p.1 ∧ prfSum p.1 x = value
      then f p.1 else 0
  have he := Fintype.sum_bijective (refreshSharePair records D Tstar x)
    (refreshSharePair_involutive records D Tstar x).bijective
    (fun p => g (refreshSharePair records D Tstar x p)) g (fun _ => rfl)
  have hpoint : ∀ p, g (refreshSharePair records D Tstar x p) =
      if ShareView records reads released values p.1 ∧ p.2 = value then
        f (refreshShareTable records D Tstar x p.1 p.2) else 0 := by
    intro p
    simp only [g, refreshSharePair, refreshShareTable_value]
    simp only [show ShareView records reads released values
        (refreshShareTable records D Tstar x p.1 p.2) ↔
        ShareView records reads released values p.1 from
      refreshSharePair_view_iff records D Tstar hT x hquorum reads hreads released hx values p]
  simp only [hpoint, Fintype.sum_prod_type] at he
  have hcard : Fintype.card TprfCorrectnessProof.XorDigest = 2 ^ 128 := by
    change Fintype.card LeanXmss.Digest = _
    simp [LeanXmss.digestBits]
  simpa only [g, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_ite, mul_zero, Finset.mul_sum] using he

/-- The table constraints retained by an adaptive share computation. Released
values are supplied by a fixed PRF function, jointly with the public forest. -/
structure ShareViewData (C : Committee) where
  records : List (EvalRecord C)
  reads : List (Slot C × LeanXmss.HashOutput)
  released : Finset Point

namespace ShareViewData

set_option maxRecDepth 3000

def predicate (v : ShareViewData C) (values : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → LeanXmss.HashOutput) : Prop :=
  ShareView v.records v.reads v.released values ω

instance (v : ShareViewData C) (values : Point → TprfCorrectnessProof.XorDigest) :
    DecidablePred (v.predicate values) := Classical.decPred _

def full (v : ShareViewData C) (points : Finset Point) : ShareViewData C :=
  { v with released := points }

def release (v : ShareViewData C) (x : Point) : ShareViewData C :=
  { v with released := insert x v.released }

def factor (v : ShareViewData C) (points : Finset Point) : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞) ^ (points \ v.released).card

def mass (v : ShareViewData C) (values : Point → TprfCorrectnessProof.XorDigest)
    (f : (Slot C → LeanXmss.HashOutput) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ ω, if v.predicate values ω then f ω else 0

/-- The remaining coordinates are still below threshold. Earlier releases
need not satisfy a threshold restriction. -/
structure Safe (v : ShareViewData C) where
  corrupt : Finset C.Party
  missing : C.Term
  subset_missing : corrupt ⊆ missing.1
  quorum : ∀ x ∉ v.released, ∀ message,
    (corrupt ∪ recordQueriers v.records x message).card ≤ C.t - 1
  reads_revealed : ∀ r ∈ v.reads, Revealed corrupt (slotKey r.1)

/-- A release only needs hiding at the coordinate currently installed. -/
structure ReleaseSafe (v : ShareViewData C) (x : Point) where
  corrupt : Finset C.Party
  missing : C.Term
  subset_missing : corrupt ⊆ missing.1
  quorum : ∀ message, (corrupt ∪ recordQueriers v.records x message).card ≤ C.t - 1
  reads_revealed : ∀ r ∈ v.reads, Revealed corrupt (slotKey r.1)

def install (v : ShareViewData C) (x : Point) (h : v.ReleaseSafe x)
    (ω : Slot C → LeanXmss.HashOutput) (value : TprfCorrectnessProof.XorDigest) :=
  refreshShareTable v.records h.corrupt h.missing x ω value

theorem predicate_release (v : ShareViewData C) (values : Point → TprfCorrectnessProof.XorDigest)
    (x : Point) (ω : Slot C → LeanXmss.HashOutput) :
    (v.release x).predicate values ω ↔ v.predicate values ω ∧ prfSum ω x = values x := by
  simp only [predicate, release, ShareView, ReleasedValues, Finset.mem_insert,
    forall_eq_or_imp]
  tauto

theorem full_release (v : ShareViewData C) (x : Point) (points : Finset Point) :
    (v.release x).full points = v.full points := rfl

theorem factor_release (v : ShareViewData C) (points : Finset Point) (x : Point)
    (hxP : x ∈ points) (hx : x ∉ v.released) :
    v.factor points = (2 ^ 128 : ℝ≥0∞) * (v.release x).factor points := by
  have aux (S : Finset Point) (hxS : x ∈ S) :
      (S \ v.released).card = (S \ insert x v.released).card + 1 := by
    have hset : (S \ v.released).erase x = S \ insert x v.released := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, not_or]
      tauto
    rw [← hset]
    symm
    apply Finset.card_erase_add_one
    simpa only [Finset.mem_sdiff] using And.intro hxS hx
  have hc := aux points hxP
  unfold factor release
  rw [hc, pow_succ, mul_comm]

theorem mass_install (v : ShareViewData C) (values : Point → TprfCorrectnessProof.XorDigest)
    (x : Point) (hx : x ∉ v.released) (h : v.ReleaseSafe x)
    (f : (Slot C → LeanXmss.HashOutput) → ℝ≥0∞) :
    v.mass values (fun ω => f (v.install x h ω (values x))) =
      (2 ^ 128 : ℝ≥0∞) * (v.release x).mass values f := by
  unfold mass install
  simp only [predicate_release]
  exact refreshShareTable_weighted v.records h.corrupt h.missing h.subset_missing x
    h.quorum v.reads h.reads_revealed v.released hx values (values x) f

/-- The terminal case of the adaptive coupling. No positive-probability
assumption or conditional probability division is needed. -/
theorem mass_const (v : ShareViewData C) (h : v.Safe)
    (points : Finset Point) (hsub : v.released ⊆ points)
    (values : Point → TprfCorrectnessProof.XorDigest) (a : ℝ≥0∞) :
    (v.full points).mass values (fun _ => a) * v.factor points = v.mass values (fun _ => a) := by
  set hidden : Finset Point := points \ v.released with hhidden
  have hinv : ∀ x ∈ hidden, ∀ message,
      (h.corrupt ∪ recordQueriers v.records x message).card ≤ C.t - 1 := by
    intro x hx
    apply h.quorum x
    have hn : x ∉ v.released := by
      simp only [hhidden, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
      exact hx.2
    exact hn
  have hd : Disjoint hidden v.released := by
    simp only [hhidden, Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun _ hx hn => hx.2 hn
  have hc := card_consistent_released_mul v.records h.corrupt hidden h.missing
    h.subset_missing hinv v.reads (by intro r hr; exact h.reads_revealed r hr)
    v.released hd values values
  have hleft : (Finset.univ.filter fun ω =>
      TprfSecurityProof.Consistent v.records v.reads hidden values ω ∧
        ReleasedValues v.released values ω) =
      Finset.univ.filter ((v.full points).predicate values) := by
    apply Finset.filter_congr
    intro ω _
    simp only [TprfSecurityProof.Consistent, predicate, ShareView, full, ReleasedValues,
      hhidden, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.notMem_empty,
      IsEmpty.forall_iff, implies_true, and_true, forall_const]
    constructor
    · rintro ⟨⟨hr, hrds, hh⟩, hrel⟩
      refine ⟨⟨hr, hrds⟩, fun x hxP => ?_⟩
      by_cases hx : x ∈ v.released
      · exact hrel x hx
      · exact hh x ⟨hxP, hx⟩
    · rintro ⟨⟨hr, hrds⟩, hv⟩
      exact ⟨⟨hr, hrds, fun x hx => hv x hx.1⟩, fun x hx => hv x (hsub hx)⟩
  have hright : (Finset.univ.filter fun ω =>
      TprfSecurityProof.Consistent v.records v.reads ∅ values ω ∧
        ReleasedValues v.released values ω) =
      Finset.univ.filter (v.predicate values) := by
    apply Finset.filter_congr
    intro ω _
    simp only [predicate, ShareView, consistent_empty_iff v.records v.reads values (fun _ => 0)]
  rw [hleft, hright] at hc
  have hcast := congrArg (fun n : ℕ => (n : ℝ≥0∞)) hc
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, LeanXmss.digestBits] at hcast

  have hm (w : ShareViewData C) : w.mass values (fun _ => a) =
      (Finset.univ.filter (w.predicate values)).card * a := by
    unfold mass
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hm, hm]
  change _ * (2 ^ 128 : ℝ≥0∞) ^ hidden.card = _
  rw [mul_right_comm, hcast]

/-- Partition an adaptive observation by its returned answer. -/
theorem mass_observe {β : Type} [Fintype β] [DecidableEq β]
    (v : ShareViewData C) (next : β → ShareViewData C)
    (values : Point → TprfCorrectnessProof.XorDigest)
    (g : (Slot C → LeanXmss.HashOutput) → β)
    (hview : ∀ b ω, (next b).predicate values ω ↔ v.predicate values ω ∧ g ω = b)
    (f : β → (Slot C → LeanXmss.HashOutput) → ℝ≥0∞) :
    v.mass values (fun ω => f (g ω) ω) = ∑ b, (next b).mass values (f b) := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [hview, ite_and]
  by_cases hv : v.predicate values ω
  · simp only [hv, if_true, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [hv, if_false, Finset.sum_const_zero]

/-- Independent randomness commutes with the finite share-table weights. -/
theorem mass_tsum {β : Type} (v : ShareViewData C)
    (values : Point → TprfCorrectnessProof.XorDigest)
    (weight : β → ℝ≥0∞) (f : β → (Slot C → LeanXmss.HashOutput) → ℝ≥0∞) :
    v.mass values (fun ω => ∑' b, weight b * f b ω) =
      ∑' b, weight b * v.mass values (f b) := by
  simp only [mass, ← Finset.sum_filter]
  exact sum_tsum_mul _ weight f

/-- An ordinary observation only adds its answer to the retained share view.
This condition is independent of the hidden PRF function. -/
def Observation {β : Type} (v : ShareViewData C) (next : β → ShareViewData C)
    (g : (Slot C → LeanXmss.HashOutput) → β) : Prop :=
  (∀ b, (next b).released = v.released) ∧ ∀ b ω,
    TprfSecurityProof.Consistent (next b).records (next b).reads ∅ (fun _ => 0) ω ↔
      TprfSecurityProof.Consistent v.records v.reads ∅ (fun _ => 0) ω ∧ g ω = b

theorem Observation.predicate {β : Type} {v : ShareViewData C}
    {next : β → ShareViewData C} {g : (Slot C → LeanXmss.HashOutput) → β}
    (h : v.Observation next g) (values : Point → TprfCorrectnessProof.XorDigest) :
    ∀ b ω, (next b).predicate values ω ↔ v.predicate values ω ∧ g ω = b := by
  intro b ω
  simp only [ShareViewData.predicate, ShareView, h.1 b, h.2 b ω]
  tauto

theorem Observation.full {β : Type} {v : ShareViewData C}
    {next : β → ShareViewData C} {g : (Slot C → LeanXmss.HashOutput) → β}
    (h : v.Observation next g) (points : Finset Point)
    (values : Point → TprfCorrectnessProof.XorDigest) :
    ∀ b ω, ((next b).full points).predicate values ω ↔
      (v.full points).predicate values ω ∧ g ω = b := by
  intro b ω
  simp only [ShareViewData.predicate, ShareView, ShareViewData.full, h.2 b ω]
  tauto

/-- Recording one `Eval'` answer is an observation in the adaptive interface. -/
def record (v : ShareViewData C) (i : C.Party) (J : C.Quorum) (x : Point)
    (message : LeanXmss.Message) (answer : TprfCorrectnessProof.XorDigest) : ShareViewData C :=
  { v with records := ⟨i, J, x, message, answer⟩ :: v.records }

theorem observation_record (v : ShareViewData C) (i : C.Party) (J : C.Quorum)
    (x : Point) (message : LeanXmss.Message) :
    v.Observation (v.record i J x message) (fun ω => evalSum ω i J x message) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro answer ω
  simp only [record, TprfSecurityProof.Consistent, List.mem_cons, forall_eq_or_imp]
  tauto

/-- Recording a raw slot read uses the same observation interface. Its safety
requires that the key of the slot is already revealed. -/
def read (v : ShareViewData C) (slot : Slot C) (answer : LeanXmss.HashOutput) : ShareViewData C :=
  { v with reads := (slot, answer) :: v.reads }

theorem observation_read (v : ShareViewData C) (slot : Slot C) :
    v.Observation (v.read slot) (fun ω => ω slot) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro answer ω
  simp only [read, TprfSecurityProof.Consistent, List.mem_cons, forall_eq_or_imp]
  tauto

def Safe.releaseSafe {v : ShareViewData C} (h : v.Safe) (x : Point)
    (hx : x ∉ v.released) : v.ReleaseSafe x :=
  ⟨h.corrupt, h.missing, h.subset_missing, h.quorum x hx, h.reads_revealed⟩

def Safe.release {v : ShareViewData C} (h : v.Safe) (x : Point) : (v.release x).Safe where
  corrupt := h.corrupt
  missing := h.missing
  subset_missing := h.subset_missing
  quorum := by
    intro y hy
    apply h.quorum y
    exact fun hymem => hy (Finset.mem_insert_of_mem hymem)
  reads_revealed := h.reads_revealed

def Safe.read {v : ShareViewData C} (h : v.Safe) (slot : Slot C)
    (hslot : Revealed h.corrupt (slotKey slot)) (answer : LeanXmss.HashOutput) :
    (v.read slot answer).Safe where
  corrupt := h.corrupt
  missing := h.missing
  subset_missing := h.subset_missing
  quorum := h.quorum
  reads_revealed := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hslot
    · exact h.reads_revealed r hr

def empty : ShareViewData C := ⟨[], [], ∅⟩

theorem predicate_empty (values : Point → TprfCorrectnessProof.XorDigest)
    (ω : Slot C → LeanXmss.HashOutput) : (empty (C := C)).predicate values ω := by
  simp only [empty, predicate, ShareView, TprfSecurityProof.Consistent, ReleasedValues,
    List.not_mem_nil, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_self]

def valuesOf (points : Finset Point) (values : points → TprfCorrectnessProof.XorDigest)
    (x : Point) : TprfCorrectnessProof.XorDigest :=
  if hx : x ∈ points then values ⟨x, hx⟩ else 0

def vector (points : Finset Point) (ω : Slot C → LeanXmss.HashOutput) :
    points → TprfCorrectnessProof.XorDigest := fun x => prfSum ω x.1

theorem predicate_empty_full (points : Finset Point)
    (values : points → TprfCorrectnessProof.XorDigest) (ω : Slot C → LeanXmss.HashOutput) :
    ((empty (C := C)).full points).predicate (valuesOf points values) ω ↔
      vector points ω = values := by
  simp only [empty, full, predicate, ShareView, TprfSecurityProof.Consistent,
    ReleasedValues, List.not_mem_nil, Finset.notMem_empty, IsEmpty.forall_iff,
    implies_true, and_self, true_and]
  constructor
  · intro h
    funext x
    simpa only [vector, valuesOf, dif_pos x.2] using h x.1 x.2
  · intro h x hx
    simpa only [vector, valuesOf, dif_pos hx] using congrFun h ⟨x, hx⟩

theorem factor_empty (points : Finset Point) :
    (empty (C := C)).factor points = (2 ^ 128 : ℝ≥0∞) ^ points.card := by
  simp only [factor, empty, Finset.sdiff_empty]

/-- Corruption can enlarge the known-key set once the points that cross their
threshold have been released. The share view itself need not be discarded. -/
def Safe.enlargeCorrupt {v : ShareViewData C} (h : v.Safe) (D : Finset C.Party)
    (hD : h.corrupt ⊆ D) (T : C.Term) (hT : D ⊆ T.1)
    (hquorum : ∀ x ∉ v.released, ∀ message,
      (D ∪ recordQueriers v.records x message).card ≤ C.t - 1) : v.Safe where
  corrupt := D
  missing := T
  subset_missing := hT
  quorum := hquorum
  reads_revealed := by
    intro r hr
    exact revealed_mono hD (h.reads_revealed r hr)

/-- Only the queried point/context changes when an `Eval'` answer is recorded. -/
theorem recordQueriers_record (v : ShareViewData C) (i : C.Party) (J : C.Quorum)
    (x : Point) (message : LeanXmss.Message) (answer : TprfCorrectnessProof.XorDigest)
    (y : Point) (context : LeanXmss.Message) :
    recordQueriers (v.record i J x message answer).records y context =
      if x = y ∧ message = context then insert i (recordQueriers v.records y context)
      else recordQueriers v.records y context := by
  simp only [record, recordQueriers, List.filter_cons, decide_eq_true_eq]
  split_ifs <;> first | rfl | simp only [List.map_cons, List.toFinset_cons]

/-- Record a share after releasing the point if this answer crosses its
threshold. No threshold condition is imposed on previously released points. -/
def Safe.record {v : ShareViewData C} (h : v.Safe) (i : C.Party) (J : C.Quorum)
    (x : Point) (message : LeanXmss.Message) (answer : TprfCorrectnessProof.XorDigest)
    (hquorum : x ∉ v.released →
      (h.corrupt ∪ insert i (recordQueriers v.records x message)).card ≤ C.t - 1) :
    (v.record i J x message answer).Safe where
  corrupt := h.corrupt
  missing := h.missing
  subset_missing := h.subset_missing
  quorum := by
    intro y hy context
    rw [recordQueriers_record]
    split_ifs with heq
    · obtain ⟨rfl, rfl⟩ := heq
      exact hquorum hy
    · exact h.quorum y hy context
  reads_revealed := h.reads_revealed

end ShareViewData

/-- A compositional proof interface for adaptive share observations and
releases. The release operation is internal to the simulation; its permission
must be established from the signing state when this interface is instantiated. -/
inductive ShareProgram (C : Committee) (points : Finset Point) : ShareViewData C → Type → Type 1
  | pure {v : ShareViewData C} {α : Type} (a : α) (safe : v.Safe)
      (subset : v.released ⊆ points) : ShareProgram C points v α
  | finish {v : ShareViewData C} {α : Type}
      (result : (Slot C → LeanXmss.HashOutput) → α) (released : v.released = points) :
      ShareProgram C points v α
  | observe {v : ShareViewData C} {α β : Type} [Fintype β] [DecidableEq β]
      (g : (Slot C → LeanXmss.HashOutput) → β) (nextView : β → ShareViewData C)
      (view : v.Observation nextView g)
      (next : ∀ b, ShareProgram C points (nextView b) α) : ShareProgram C points v α
  | release {v : ShareViewData C} {α : Type} (x : Point) (inPoints : x ∈ points)
      (fresh : x ∉ v.released) (safe : v.ReleaseSafe x)
      (next : TprfCorrectnessProof.XorDigest → ShareProgram C points (v.release x) α) :
      ShareProgram C points v α
  | probe {v : ShareViewData C} {α : Type} (x : Point) (inPoints : x ∈ points)
      (target : XmssSecurity.Digest)
      (next : ShareProgram C points v α) : ShareProgram C points v α
  | encoding {v : ShareViewData C} {α : Type} (key : XmssSecurity.LeafIndex) (sign : Bool)
      (next : XmssSecurity.HashOutput → ShareProgram C points v α) : ShareProgram C points v α
  | sample {v : ShareViewData C} {α β : Type} (computation : ProbComp β)
      (next : β → ShareProgram C points v α) : ShareProgram C points v α

namespace ShareProgram

variable {points : Finset Point} {v : ShareViewData C} {α : Type}

noncomputable def run (simulated : Bool) (values : Point → TprfCorrectnessProof.XorDigest) :
    {v : ShareViewData C} → ShareProgram C points v α →
      (Slot C → LeanXmss.HashOutput) → ProbComp α
  | _, .pure a _ _, _ => Pure.pure a
  | _, .finish result _, ω => Pure.pure (result ω)
  | _, @ShareProgram.observe _ _ _ _ β instF instD g _ _ next, ω =>
      run simulated values (next (g ω)) ω
  | v, .release x _ _ h next, ω => run simulated values (next (values x))
      (if simulated then v.install x h ω (values x) else ω)
  | _, .probe _ _ _ next, ω => run simulated values next ω
  | _, .encoding _ _ next, ω =>
      XmssSecurity.uniformHashOutput >>= fun answer => run simulated values (next answer) ω
  | _, .sample m next, ω => m >>= fun b => run simulated values (next b) ω

set_option maxRecDepth 3000 in
/-- Exact adaptive balance, for every fixed PRF function. Consequently it can
be composed jointly with a forest kernel that depends on that same function. -/
theorem balance (program : ShareProgram C points v α)
    (values : Point → TprfCorrectnessProof.XorDigest) (event : α → Prop) :
    (v.full points).mass values (fun ω => Pr[event | program.run false values ω]) *
        v.factor points =
      v.mass values (fun ω => Pr[event | program.run true values ω]) := by
  induction program with
  | pure a safe subset =>
      simp only [run]
      exact ShareViewData.mass_const _ safe points subset values _
  | @finish v α result released =>
      have hf : v.full points = v := by
        cases v
        simp only [ShareViewData.full, ShareViewData.released] at released ⊢
        exact congrArg (ShareViewData.mk _ _) released.symm
      have hc : v.factor points = 1 := by
        simp only [ShareViewData.factor, released, Finset.sdiff_self, Finset.card_empty, pow_zero]
      simp only [run, hf, hc, mul_one]
  | @observe v α β _ _ g nextView view next ih =>
      simp only [run]
      rw [ShareViewData.mass_observe _ (fun b => (nextView b).full points) values g
        (view.full points values) (fun b ω => Pr[event | (next b).run false values ω]),
        ShareViewData.mass_observe _ nextView values g (view.predicate values)
        (fun b ω => Pr[event | (next b).run true values ω]), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      have h := ih b event
      simpa only [ShareViewData.factor, view.1 b] using h
  | @release v α x inPoints fresh safe next ih =>
      simp only [run, Bool.false_eq_true, if_false, if_true]
      rw [ShareViewData.mass_install _ values x fresh safe
        (fun ω => Pr[event | (next (values x)).run true values ω]),
        ShareViewData.factor_release _ points x inPoints fresh]
      have h := congrArg (fun a : ℝ≥0∞ => (2 ^ 128) * a) (ih (values x) event)
      simpa only [ShareViewData.full_release, mul_assoc, mul_left_comm] using h
  | probe x inPoints target next ih => exact ih event
  | encoding key sign next ih =>
      simp only [run, probEvent_bind_eq_tsum]
      rw [ShareViewData.mass_tsum, ShareViewData.mass_tsum, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro b
      rw [mul_assoc, ih b]
  | sample computation next ih =>
      simp only [run, probEvent_bind_eq_tsum]
      rw [ShareViewData.mass_tsum, ShareViewData.mass_tsum, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro b
      rw [mul_assoc, ih b]

/-- The real computation only consults the prescribed function at released
points, so matching it there gives the ordinary table-backed execution. -/
theorem run_false_congr (program : ShareProgram C points v α)
    (values other : Point → TprfCorrectnessProof.XorDigest)
    (heq : ∀ x ∈ points, values x = other x) (ω : Slot C → LeanXmss.HashOutput) :
    program.run false values ω = program.run false other ω := by
  induction program generalizing ω with
  | pure => rfl
  | finish => rfl
  | observe g nextView view next ih => exact ih (g ω) ω
  | release x inPoints fresh safe next ih =>
      simp only [run, Bool.false_eq_true, if_false, heq x inPoints]
      exact ih (other x) ω
  | probe x inPoints target next ih => exact ih ω
  | encoding key sign next ih =>
      simp only [run]
      congr 1
      funext b
      exact ih b ω
  | sample computation next ih =>
      simp only [run]
      congr 1
      funext b
      exact ih b ω

/-- The ordinary share computation uses the fixed table at every release. -/
noncomputable def real (program : ShareProgram C points v α)
    (ω : Slot C → LeanXmss.HashOutput) : ProbComp α :=
  program.run false (prfSum ω) ω

/-- Balance expressed using the actual fixed table on the real side. -/
theorem balance_real (program : ShareProgram C points v α)
    (values : Point → TprfCorrectnessProof.XorDigest) (event : α → Prop) :
    (v.full points).mass values (fun ω => Pr[event | program.real ω]) *
        v.factor points =
      v.mass values (fun ω => Pr[event | program.run true values ω]) := by
  rw [← program.balance values event]
  congr 1
  unfold ShareViewData.mass
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with hv
  · have he : program.run false values ω = program.real ω := by
      apply program.run_false_congr
      intro x hx
      exact (hv.2 x hx).symm
    exact congrArg (fun m : ProbComp α => Pr[event | m]) he.symm
  · rfl

/-- Average a table-indexed computation without materializing its finite
sample space. -/
theorem uniform_bind_probability {Ω β : Type} [Fintype Ω] [SampleableType Ω]
    (m : Ω → ProbComp β) (event : β → Prop) :
    Pr[event | ($ᵗ Ω) >>= m] =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ * ∑ ω, Pr[event | m ω] := by
  rw [probEvent_bind_eq_tsum, tsum_fintype]
  simp only [probOutput_uniformSample, div_eq_mul_inv, one_mul, Finset.mul_sum]

/-- A finite-fiber balance is preserved by arbitrary probabilistic
continuations, with the real label read from the table. -/
theorem uniform_fiber_probability {Ω Λ β : Type}
    [Fintype Ω] [SampleableType Ω] [Fintype Λ] [SampleableType Λ] [Nonempty Λ]
    [DecidableEq Λ] (label : Ω → Λ)
    (real sim : Λ → Ω → ProbComp β) (event : β → Prop)
    (balance : ∀ value,
      (∑ ω, if label ω = value then Pr[event | real value ω] else 0) *
          (Fintype.card Λ : ℝ≥0∞) =
        ∑ ω, Pr[event | sim value ω]) :
    Pr[event | ($ᵗ Ω) >>= fun ω => real (label ω) ω] =
      Pr[event | ($ᵗ Λ) >>= fun value => ($ᵗ Ω) >>= sim value] := by
  have hsplit : (∑ ω, Pr[event | real (label ω) ω]) =
      ∑ value, ∑ ω, if label ω = value then Pr[event | real value ω] else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hsum : (∑ ω, Pr[event | real (label ω) ω]) * (Fintype.card Λ : ℝ≥0∞) =
      ∑ value, ∑ ω, Pr[event | sim value ω] := by
    rw [hsplit, Finset.sum_mul]
    exact Finset.sum_congr rfl fun value _ => balance value
  have hzero : (Fintype.card Λ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card Λ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [uniform_bind_probability, uniform_bind_probability]
  simp only [uniform_bind_probability, ← Finset.mul_sum]
  rw [← hsum]
  rw [show (Fintype.card Λ : ℝ≥0∞)⁻¹ *
      ((Fintype.card Ω : ℝ≥0∞)⁻¹ *
        ((∑ ω, Pr[event | real (label ω) ω]) * (Fintype.card Λ : ℝ≥0∞))) =
      (Fintype.card Ω : ℝ≥0∞)⁻¹ * (∑ ω, Pr[event | real (label ω) ω]) *
        ((Fintype.card Λ : ℝ≥0∞)⁻¹ * (Fintype.card Λ : ℝ≥0∞)) by ring]
  rw [ENNReal.inv_mul_cancel hzero htop, mul_one]

theorem run_sample {β : Type} (m : ProbComp β)
    (next : β → ShareProgram C points v α) (simulated : Bool)
    (values : Point → TprfCorrectnessProof.XorDigest) (ω : Slot C → LeanXmss.HashOutput) :
    (ShareProgram.sample m next).run simulated values ω =
      m >>= fun b => (next b).run simulated values ω := rfl

theorem real_sample {β : Type} (m : ProbComp β)
    (next : β → ShareProgram C points v α) (ω : Slot C → LeanXmss.HashOutput) :
    (ShareProgram.sample m next).real ω = m >>= fun b => (next b).real ω := rfl

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
/-- Exact joint simulation of adaptive shares with an arbitrary public forest
kernel. The coupling preserves the hidden values in distribution. No claim
that they remain uniform after exposing the forest is used here. -/
theorem adaptive_forest_eq {β : Type} (points : Finset Point)
    (forest : (points → TprfCorrectnessProof.XorDigest) → ProbComp β)
    (program : β → ShareProgram C points ShareViewData.empty α) :
    𝒟[(($ᵗ (Slot C → LeanXmss.HashOutput)) >>= fun ω => do
      let publicData ← forest (ShareViewData.vector points ω)
      (program publicData).real ω)] =
    𝒟[(($ᵗ (points → TprfCorrectnessProof.XorDigest)) >>= fun values => do
      let ω ← $ᵗ (Slot C → LeanXmss.HashOutput)
      let publicData ← forest values
      (program publicData).run true (ShareViewData.valuesOf points values) ω)] := by
  apply evalDist_ext
  intro a
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply uniform_fiber_probability (ShareViewData.vector points)
    (fun values ω => forest values >>= fun publicData => (program publicData).real ω)
    (fun values ω => forest values >>= fun publicData =>
      (program publicData).run true (ShareViewData.valuesOf points values) ω)
    (fun output => output = a)
  intro values
  have h := (ShareProgram.sample (forest values) program).balance_real
    (ShareViewData.valuesOf points values) (fun output => output = a)
  have hcard : (Fintype.card (points → TprfCorrectnessProof.XorDigest) : ℝ≥0∞) =
      (2 ^ 128 : ℝ≥0∞) ^ points.card := by
    have hd : Fintype.card TprfCorrectnessProof.XorDigest = 2 ^ 128 := by
      change Fintype.card LeanXmss.Digest = _
      simp [LeanXmss.digestBits]
    simp only [Fintype.card_fun, Fintype.card_coe, hd, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard]
  simpa only [ShareViewData.mass, ShareViewData.predicate_empty_full,
    ShareViewData.predicate_empty, if_true, ShareViewData.factor_empty,
    real_sample, run_sample] using h

/-- The share simulator accesses hidden values only through monitor reveals.
Probes are silent; encoding trials remain explicit monitor queries. -/
noncomputable def compile : {v : ShareViewData C} → ShareProgram C points v α →
    (Slot C → LeanXmss.HashOutput) →
      OracleComp (XmssSecurity.FirstLaneOracleSimulation.World points) α
  | _, .pure a _ _, _ => Pure.pure a
  | _, .finish result _, ω => Pure.pure (result ω)
  | _, @ShareProgram.observe _ _ _ _ β instF instD g _ _ next, ω => compile (next (g ω)) ω
  | v, .release x inPoints _ h next, ω => do
      let value ← XmssSecurity.FirstLaneOracleSimulation.revealQuery (⟨x, inPoints⟩ : points)
      compile (next value) (v.install x h ω value)
  | _, .probe x inPoints target next, ω => do
      XmssSecurity.FirstLaneOracleSimulation.probeQuery (⟨x, inPoints⟩ : points) target
      compile next ω
  | _, .encoding key sign next, ω => do
      let answer ← if sign then XmssSecurity.FirstLaneOracleSimulation.encodingSignAttemptQuery key
        else XmssSecurity.FirstLaneOracleSimulation.encodingQuery key
      compile (next answer) ω
  | _, .sample m next, ω => do
      let b ← XmssSecurity.FirstLaneOracleSimulation.liftProbComp m
      compile (next b) ω

theorem simulate_eager_liftProbComp (values : points → XmssSecurity.Digest)
    {β : Type} (m : ProbComp β) :
    simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl values)
      (XmssSecurity.FirstLaneOracleSimulation.liftProbComp (Index := points) m) = m := by
  unfold XmssSecurity.FirstLaneOracleSimulation.liftProbComp
  rw [← QueryImpl.simulateQ_compose]
  change simulateQ (QueryImpl.id' unifSpec) m = m
  simp

/-- Erasing the monitor trace gives exactly the adaptive share simulator. -/
theorem simulate_compile (program : ShareProgram C points v α)
    (values : points → TprfCorrectnessProof.XorDigest) (ω : Slot C → LeanXmss.HashOutput) :
    simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl values) (program.compile ω) =
      program.run true (ShareViewData.valuesOf points values) ω := by
  induction program generalizing ω with
  | pure => simp only [compile, run, simulateQ_pure]
  | finish => simp only [compile, run, simulateQ_pure]
  | observe g nextView view next ih => exact ih (g ω) ω
  | release x inPoints fresh safe next ih =>
      simp only [compile, XmssSecurity.FirstLaneOracleSimulation.revealQuery,
        simulateQ_bind, simulateQ_spec_query, XmssSecurity.FirstLaneOracleSimulation.eagerImpl,
        pure_bind, run, if_true, ShareViewData.valuesOf, dif_pos inPoints]
      exact ih (values ⟨x, inPoints⟩) _
  | probe x inPoints target next ih =>
      simp only [compile, XmssSecurity.FirstLaneOracleSimulation.probeQuery,
        simulateQ_bind, simulateQ_spec_query, XmssSecurity.FirstLaneOracleSimulation.eagerImpl,
        pure_bind, run]
      exact ih ω
  | encoding key sign next ih =>
      cases sign <;>
        simp only [compile, Bool.false_eq_true, if_false, if_true,
          XmssSecurity.FirstLaneOracleSimulation.encodingQuery,
          XmssSecurity.FirstLaneOracleSimulation.encodingSignAttemptQuery,
          simulateQ_bind, simulateQ_spec_query, XmssSecurity.FirstLaneOracleSimulation.eagerImpl, run] <;>
        congr 1 <;> funext b <;> exact ih b ω
  | sample m next ih =>
      simp only [compile, simulateQ_bind, simulate_eager_liftProbComp, run]
      congr 1
      funext b
      exact ih b ω

noncomputable def compileFromEmpty (program : ShareProgram C points ShareViewData.empty α) :
    OracleComp (XmssSecurity.FirstLaneOracleSimulation.World points) α := do
  let ω ← XmssSecurity.FirstLaneOracleSimulation.liftProbComp ($ᵗ (Slot C → LeanXmss.HashOutput))
  program.compile ω

/-- The compiled share program has exactly the real result distribution. The
uniform hidden function belongs to the monitor and is absent from the compiler. -/
theorem compile_real_eq (program : ShareProgram C points ShareViewData.empty α) :
    𝒟[($ᵗ (Slot C → LeanXmss.HashOutput)) >>= program.real] =
      𝒟[($ᵗ (points → TprfCorrectnessProof.XorDigest)) >>= fun values =>
        simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl values)
          program.compileFromEmpty] := by
  have h := adaptive_forest_eq points (fun _ => (Pure.pure () : ProbComp Unit)) (fun _ => program)
  simpa only [pure_bind, compileFromEmpty, simulateQ_bind, simulate_eager_liftProbComp,
    simulate_compile] using h

/-- The existing two-component monitor supplies a single fixed-cap unit for
all silent hidden-value probes and bottom encoding partners together. -/
theorem compiled_hit_probability_le (program : ShareProgram C points ShareViewData.empty α)
    (q : ℕ)
    (hbound : program.compileFromEmpty.IsQueryBoundP
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q) :
    Pr[fun result => XmssSecurity.FirstLaneOracleSimulation.CombinedHit result.1 result.2.2 |
      XmssSecurity.FirstLaneOracleSimulation.eagerExperiment program.compileFromEmpty] ≤
        (q : ℝ≥0∞) / 2 ^ 128 := by
  rw [XmssSecurity.FirstLaneOracleSimulation.combinedHit_probability_eq_structuralExperiment
    q _ hbound]
  simpa only [XmssSecurity.digestBits, Nat.cast_pow, Nat.cast_ofNat] using
    XmssSecurity.FirstLaneOracleSimulation.structuralExperiment_empty_true_probability_le
      q program.compileFromEmpty

/-- Erasing the monitor's hidden table and trace leaves the real share result. -/
theorem eager_result_eq_real (program : ShareProgram C points ShareViewData.empty α) :
    𝒟[(fun r => r.2.1) <$>
      XmssSecurity.FirstLaneOracleSimulation.eagerExperiment program.compileFromEmpty] =
      𝒟[($ᵗ (Slot C → LeanXmss.HashOutput)) >>= program.real] := by
  rw [program.compile_real_eq]
  unfold XmssSecurity.FirstLaneOracleSimulation.eagerExperiment
    XmssSecurity.RevealProbeOracleSimulation.eagerTableSample
  simp only [map_bind, map_pure]
  apply evalDist_ext
  intro a
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro values
  rw [probOutput_uniformSample, probOutput_uniformSample]
  have hd : Fintype.card XmssSecurity.Digest = Fintype.card TprfCorrectnessProof.XorDigest := by
    change Fintype.card (BitVec 128) = Fintype.card (BitVec 128)
    rfl
  simp only [Fintype.card_fun, Fintype.card_coe, hd]
  apply congrArg (fun p : ℝ≥0∞ =>
    (↑(Fintype.card TprfCorrectnessProof.XorDigest ^ points.card) : ℝ≥0∞)⁻¹ * p)
  change Pr[= a | Prod.fst <$> (simulateQ
    ((XmssSecurity.FirstLaneOracleSimulation.eagerImpl values).withTraceAppend
      XmssSecurity.FirstLaneOracleSimulation.traceFragment) program.compileFromEmpty).run] = _
  rw [QueryImpl.fst_map_run_withTraceAppend]

/-- Once the concrete event is shown to produce a monitored probe or partner,
the first-lane estimate applies to the real share computation. -/
theorem real_event_le (program : ShareProgram C points ShareViewData.empty α)
    (event : α → Prop) (q : ℕ)
    (hbound : program.compileFromEmpty.IsQueryBoundP
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q)
    (hdetect : ∀ r ∈ support
      (XmssSecurity.FirstLaneOracleSimulation.eagerExperiment program.compileFromEmpty),
      event r.2.1 → XmssSecurity.FirstLaneOracleSimulation.CombinedHit r.1 r.2.2) :
    Pr[event | ($ᵗ (Slot C → LeanXmss.HashOutput)) >>= program.real] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  have he := probEvent_congr' (p := event) (fun _ _ => Iff.rfl) program.eager_result_eq_real
  rw [probEvent_map] at he
  rw [← he]
  exact (probEvent_mono hdetect).trans (program.compiled_hit_probability_le q hbound)

/-- Drain the unreleased part of the finite pool before returning a result
that can depend on the full slot table. These are reveal queries, not hazards. -/
noncomputable def finishAfter (todo : List Point) (v : ShareViewData C) (safe : v.Safe)
    (inside : ∀ x ∈ todo, x ∈ points) (subset : v.released ⊆ points)
    (cover : ∀ x ∈ points, x ∈ v.released ∨ x ∈ todo)
    (result : (Slot C → LeanXmss.HashOutput) → α) : ShareProgram C points v α :=
  match todo with
  | [] => .finish result (Finset.Subset.antisymm subset (by
      intro x hx
      exact (cover x hx).resolve_right (by simp)))
  | x :: rest =>
      if hx : x ∈ v.released then
        finishAfter rest v safe (fun y hy => inside y (List.mem_cons_of_mem x hy)) subset
          (by
            intro y hy
            rcases cover y hy with h | h
            · exact Or.inl h
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl hx
              · exact Or.inr h) result
      else .release x (inside x (List.mem_cons_self)) hx (safe.releaseSafe x hx) (fun _ =>
        finishAfter rest (v.release x) (safe.release x)
          (fun y hy => inside y (List.mem_cons_of_mem x hy))
          (by
            intro y hy
            rcases Finset.mem_insert.mp hy with heq | hy
            · simpa only [heq] using inside x List.mem_cons_self
            · exact subset hy)
          (by
            intro y hy
            rcases cover y hy with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl (Finset.mem_insert_self _ _)
              · exact Or.inr h) result)

noncomputable def finishAll (v : ShareViewData C) (safe : v.Safe)
    (subset : v.released ⊆ points) (result : (Slot C → LeanXmss.HashOutput) → α) :
    ShareProgram C points v α :=
  finishAfter points.toList v safe (by intro x hx; exact Finset.mem_toList.mp hx) subset
    (by intro x hx; exact Or.inr (Finset.mem_toList.mpr hx)) result

theorem real_finishAfter (todo : List Point) (v : ShareViewData C) (safe : v.Safe)
    (inside : ∀ x ∈ todo, x ∈ points) (subset : v.released ⊆ points)
    (cover : ∀ x ∈ points, x ∈ v.released ∨ x ∈ todo)
    (result : (Slot C → LeanXmss.HashOutput) → α) (ω : Slot C → LeanXmss.HashOutput) :
    (finishAfter todo v safe inside subset cover result).real ω = Pure.pure (result ω) := by
  induction todo generalizing v with
  | nil => rfl
  | cons x rest ih =>
      simp only [finishAfter]
      split_ifs with hx
      · exact ih _ _ _ _ _
      · simpa only [real, run, Bool.false_eq_true, if_false] using
          ih (v.release x) (safe.release x) _ _ _

theorem real_finishAll (v : ShareViewData C) (safe : v.Safe)
    (subset : v.released ⊆ points) (result : (Slot C → LeanXmss.HashOutput) → α)
    (ω : Slot C → LeanXmss.HashOutput) :
    (finishAll v safe subset result).real ω = Pure.pure (result ω) :=
  real_finishAfter _ _ _ _ _ _ _ _

end ShareProgram

end ShareRefresh

section ShareMonitorTransport
open Classical
variable {I J : Type} {α : Type}

def shareMonitorTransport (embed : I → J) (mask : I → XmssSecurity.Digest) :
    QueryImpl (XmssSecurity.FirstLaneOracleSimulation.World I)
      (OracleComp (XmssSecurity.FirstLaneOracleSimulation.World J))
  | .uniform n => XmssSecurity.FirstLaneOracleSimulation.uniformQuery n
  | .encodingQuery key => XmssSecurity.FirstLaneOracleSimulation.encodingQuery key
  | .encodingSignAttempt key => XmssSecurity.FirstLaneOracleSimulation.encodingSignAttemptQuery key
  | .probe index target =>
      XmssSecurity.FirstLaneOracleSimulation.probeQuery (embed index) (target ^^^ mask index)
  | .reveal index =>
      (fun value => value ^^^ mask index) <$>
        XmssSecurity.FirstLaneOracleSimulation.revealQuery (embed index)

theorem shareMonitorTransport_eager (embed : I → J) (mask : I → XmssSecurity.Digest)
    (table : J → XmssSecurity.Digest)
    (source : OracleComp (XmssSecurity.FirstLaneOracleSimulation.World I) α) :
    simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl table)
      (simulateQ (shareMonitorTransport embed mask) source) =
    simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl
      (fun i => table (embed i) ^^^ mask i)) source := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  cases t <;> simp [QueryImpl.compose, shareMonitorTransport,
    XmssSecurity.FirstLaneOracleSimulation.uniformQuery,
    XmssSecurity.FirstLaneOracleSimulation.encodingQuery,
    XmssSecurity.FirstLaneOracleSimulation.encodingSignAttemptQuery,
    XmssSecurity.FirstLaneOracleSimulation.probeQuery,
    XmssSecurity.FirstLaneOracleSimulation.revealQuery,
    XmssSecurity.FirstLaneOracleSimulation.eagerImpl]

theorem masked_restriction_uniform [Fintype I] [Fintype J]
    (embed : I → J) (hinj : Function.Injective embed) (mask : I → XmssSecurity.Digest) :
    𝒟[(fun table : J → XmssSecurity.Digest => fun i => table (embed i) ^^^ mask i) <$>
      ($ᵗ (J → XmssSecurity.Digest))] = 𝒟[$ᵗ (I → XmssSecurity.Digest)] := by
  let shift : (I → XmssSecurity.Digest) → I → XmssSecurity.Digest :=
    fun table i => table i ^^^ mask i
  have hinv : Function.Involutive shift := by
    intro table
    funext i
    simp [shift, BitVec.xor_assoc]
  have hr := evalDist_uniformSample_map_comp_injective (R := XmssSecurity.Digest) hinj
  simp only [bind_pure_comp] at hr
  calc
    _ = 𝒟[shift <$> ((fun table : J → XmssSecurity.Digest => table ∘ embed) <$>
      ($ᵗ (J → XmssSecurity.Digest)))] := by simp only [Functor.map_map]; rfl
    _ = 𝒟[shift <$> ($ᵗ (I → XmssSecurity.Digest))] := by
      rw [evalDist_map, hr, ← evalDist_map]
    _ = _ := evalDist_map_bijective_uniform_cross (α := I → XmssSecurity.Digest)
      (β := I → XmssSecurity.Digest) shift hinv.bijective


theorem shareMonitorTransport_bound (embed : I → J) (mask : I → XmssSecurity.Digest)
    (source : OracleComp (XmssSecurity.FirstLaneOracleSimulation.World I) α) (q : ℕ)
    (h : source.IsQueryBoundP XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q) :
    (simulateQ (shareMonitorTransport embed mask) source).IsQueryBoundP
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q := by
  apply h.simulateQ_of_step
  · intro t ht
    cases t <;> simp_all [shareMonitorTransport,
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery,
      XmssSecurity.FirstLaneOracleSimulation.uniformQuery,
      XmssSecurity.FirstLaneOracleSimulation.encodingQuery,
      XmssSecurity.FirstLaneOracleSimulation.encodingSignAttemptQuery,
      XmssSecurity.FirstLaneOracleSimulation.probeQuery,
      XmssSecurity.FirstLaneOracleSimulation.revealQuery]
  · intro t ht
    cases t <;> simp_all [shareMonitorTransport,
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery,
      XmssSecurity.FirstLaneOracleSimulation.uniformQuery,
      XmssSecurity.FirstLaneOracleSimulation.encodingQuery,
      XmssSecurity.FirstLaneOracleSimulation.encodingSignAttemptQuery,
      XmssSecurity.FirstLaneOracleSimulation.probeQuery,
      XmssSecurity.FirstLaneOracleSimulation.revealQuery]

end ShareMonitorTransport

namespace ShareProgram
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
local instance : Fintype TprfCorrectnessProof.XorDigest :=
  inferInstanceAs (Fintype LeanXmss.Digest)
local instance : SampleableType TprfCorrectnessProof.XorDigest := SampleableType.ofFintype _
variable {C : Committee} {points : Finset Point} {α I : Type}
    [Fintype I] [DecidableEq I]

/-- Bottom PRF coordinates use the public XOR masks; extra monitor indices
can hold the intermediate top-chain labels generated by the hash oracle. -/
def compileEmbeddedFromEmpty (program : ShareProgram C points ShareViewData.empty α)
    (embed : points → I) (mask : points → XmssSecurity.Digest) :
    OracleComp (XmssSecurity.FirstLaneOracleSimulation.World I) α :=
  simulateQ (shareMonitorTransport embed mask) program.compileFromEmpty

theorem compileEmbedded_real_eq (program : ShareProgram C points ShareViewData.empty α)
    (embed : points → I) (hinj : Function.Injective embed) (mask : points → XmssSecurity.Digest) :
    𝒟[($ᵗ (TprfSecurityProof.Slot C → LeanXmss.HashOutput)) >>= program.real] =
      𝒟[($ᵗ (I → XmssSecurity.Digest)) >>= fun table =>
        simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl table)
          (program.compileEmbeddedFromEmpty embed mask)] := by
  rw [program.compile_real_eq]
  simp only [compileEmbeddedFromEmpty, shareMonitorTransport_eager]
  calc
    _ = 𝒟[($ᵗ (points → XmssSecurity.Digest)) >>= fun values =>
      simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl values) program.compileFromEmpty] := by
      apply evalDist_ext
      intro a
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      apply tsum_congr
      intro values
      rw [probOutput_uniformSample, probOutput_uniformSample]
      have hc : Fintype.card TprfCorrectnessProof.XorDigest = Fintype.card XmssSecurity.Digest := by
        change Fintype.card (BitVec 128) = Fintype.card (BitVec 128)
        rfl
      simp only [Fintype.card_fun, hc]
    _ = 𝒟[((fun table : I → XmssSecurity.Digest => fun i => table (embed i) ^^^ mask i) <$>
      ($ᵗ (I → XmssSecurity.Digest))) >>= fun values =>
        simulateQ (XmssSecurity.FirstLaneOracleSimulation.eagerImpl values) program.compileFromEmpty] := by
      simp only [evalDist_bind]
      rw [masked_restriction_uniform embed hinj mask]
    _ = _ := by rw [bind_map_left]

theorem compileEmbedded_bound (program : ShareProgram C points ShareViewData.empty α)
    (embed : points → I) (mask : points → XmssSecurity.Digest) (q : ℕ)
    (h : program.compileFromEmpty.IsQueryBoundP
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q) :
    (program.compileEmbeddedFromEmpty embed mask).IsQueryBoundP
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q :=
  shareMonitorTransport_bound embed mask program.compileFromEmpty q h

theorem embedded_eager_result_eq_real (program : ShareProgram C points ShareViewData.empty α)
    (embed : points → I) (hinj : Function.Injective embed) (mask : points → XmssSecurity.Digest) :
    𝒟[(fun r => r.2.1) <$> XmssSecurity.FirstLaneOracleSimulation.eagerExperiment
      (program.compileEmbeddedFromEmpty embed mask)] =
      𝒟[($ᵗ (TprfSecurityProof.Slot C → LeanXmss.HashOutput)) >>= program.real] := by
  rw [program.compileEmbedded_real_eq embed hinj mask]
  unfold XmssSecurity.FirstLaneOracleSimulation.eagerExperiment
    XmssSecurity.RevealProbeOracleSimulation.eagerTableSample
  simp only [map_bind, map_pure]
  apply evalDist_ext
  intro a
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro table
  rw [probOutput_uniformSample, probOutput_uniformSample]
  apply congrArg (fun p : ℝ≥0∞ => (Fintype.card (I → XmssSecurity.Digest) : ℝ≥0∞)⁻¹ * p)
  change Pr[= a | Prod.fst <$> (simulateQ
    ((XmssSecurity.FirstLaneOracleSimulation.eagerImpl table).withTraceAppend
      XmssSecurity.FirstLaneOracleSimulation.traceFragment)
        (program.compileEmbeddedFromEmpty embed mask)).run] = _
  rw [QueryImpl.fst_map_run_withTraceAppend]

theorem embedded_real_event_le (program : ShareProgram C points ShareViewData.empty α)
    (embed : points → I) (hinj : Function.Injective embed) (mask : points → XmssSecurity.Digest)
    (event : α → Prop) (q : ℕ)
    (hbound : program.compileFromEmpty.IsQueryBoundP
      XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery q)
    (hdetect : ∀ r ∈ support (XmssSecurity.FirstLaneOracleSimulation.eagerExperiment
        (program.compileEmbeddedFromEmpty embed mask)),
      event r.2.1 → XmssSecurity.FirstLaneOracleSimulation.CombinedHit r.1 r.2.2) :
    Pr[event | ($ᵗ (TprfSecurityProof.Slot C → LeanXmss.HashOutput)) >>= program.real] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  have he := probEvent_congr' (p := event) (fun _ _ => Iff.rfl)
    (program.embedded_eager_result_eq_real embed hinj mask)
  rw [probEvent_map] at he
  rw [← he]
  apply (probEvent_mono hdetect).trans
  rw [XmssSecurity.FirstLaneOracleSimulation.combinedHit_probability_eq_structuralExperiment
    q _ (program.compileEmbedded_bound embed mask q hbound)]
  simpa only [XmssSecurity.digestBits, Nat.cast_pow, Nat.cast_ofNat] using
    XmssSecurity.FirstLaneOracleSimulation.structuralExperiment_empty_true_probability_le
      q (program.compileEmbeddedFromEmpty embed mask)

end ShareProgram

section PrivateForest

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- Two read-only random-oracle queries commute, retaining both answers and
all cache entries. In particular, neither query is assumed fresh. -/
theorem randomOracle_queries_comm {α : Type} (left right : D)
    (next : R → R → StateT (QueryCache (D →ₒ R)) ProbComp α)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[(do
      let a ← (D →ₒ R).randomOracle left
      let b ← (D →ₒ R).randomOracle right
      next a b).run cache] =
    𝒟[(do
      let b ← (D →ₒ R).randomOracle right
      let a ← (D →ₒ R).randomOracle left
      next a b).run cache] := by
  by_cases heq : left = right
  · subst right
    cases hc : cache left with
    | none =>
      simp only [StateT.run_bind, QueryImpl.withCaching_run_none _ hc, bind_map_left,
        QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]
    | some value =>
      simp only [StateT.run_bind, QueryImpl.withCaching_run_some _ hc, pure_bind]
  · cases hl : cache left <;> cases hr : cache right
    · have hrl (value : R) : (cache.cacheQuery left value) right = none := by
        simpa [QueryCache.cacheQuery_of_ne, Ne.symm heq] using hr
      have hlr (value : R) : (cache.cacheQuery right value) left = none := by
        simpa [QueryCache.cacheQuery_of_ne, heq] using hl
      simp only [StateT.run_bind, QueryImpl.withCaching_run_none _ hl,
        QueryImpl.withCaching_run_none _ hr, bind_map_left]
      simp_rw [QueryImpl.withCaching_run_none _ (hrl _),
        QueryImpl.withCaching_run_none _ (hlr _), bind_map_left]
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro b
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro a
      rw [QueryCache.cacheQuery_comm_of_ne cache heq]
    · have hrl (value : R) : (cache.cacheQuery left value) right = cache right :=
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq)
      simp only [StateT.run_bind, QueryImpl.withCaching_run_none _ hl,
        QueryImpl.withCaching_run_some _ hr, bind_map_left, pure_bind]
      simp_rw [QueryImpl.withCaching_run_some _ ((hrl _).trans hr), pure_bind]
    · have hlr (value : R) : (cache.cacheQuery right value) left = cache left :=
        QueryCache.cacheQuery_of_ne _ _ heq
      simp only [StateT.run_bind, QueryImpl.withCaching_run_some _ hl,
        QueryImpl.withCaching_run_none _ hr, bind_map_left, pure_bind]
      simp_rw [QueryImpl.withCaching_run_some _ ((hlr _).trans hl), pure_bind]
    · simp only [StateT.run_bind, QueryImpl.withCaching_run_some _ hl,
        QueryImpl.withCaching_run_some _ hr, pure_bind]

/-- A private query commutes across an arbitrary read-only source program.
The source may choose later inputs from earlier oracle answers. -/
theorem randomOracle_query_commute {α β : Type} (target : D)
    (source : OracleComp (D →ₒ R) α)
    (next : R → α → StateT (QueryCache (D →ₒ R)) ProbComp β)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[(do
      let a ← (D →ₒ R).randomOracle target
      let b ← simulateQ randomOracle source
      next a b).run cache] =
    𝒟[(do
      let b ← simulateQ randomOracle source
      let a ← (D →ₒ R).randomOracle target
      next a b).run cache] := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    rw [randomOracle_queries_comm]
    simp only [StateT.run_bind]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro result
    exact ih result.1 result.2

/-- Arbitrary private, read-only RO work can move before the source program.
Both results and the union cache have exactly the same joint distribution.
No added freshness or cache-hit hypothesis is needed. -/
theorem randomOracle_programs_commute {α β γ : Type}
    (left : OracleComp (D →ₒ R) α) (right : OracleComp (D →ₒ R) β)
    (next : α → β → StateT (QueryCache (D →ₒ R)) ProbComp γ)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[(do
      let a ← simulateQ randomOracle left
      let b ← simulateQ randomOracle right
      next a b).run cache] =
    𝒟[(do
      let b ← simulateQ randomOracle right
      let a ← simulateQ randomOracle left
      next a b).run cache] := by
  induction left using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    calc
      _ = 𝒟[(do
          let answer ← (D →ₒ R).randomOracle input
          let b ← simulateQ randomOracle right
          let a ← simulateQ randomOracle (continuation answer)
          next a b).run cache] := by
        simp only [StateT.run_bind]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro result
        exact ih result.1 result.2
      _ = _ := randomOracle_query_commute input right
        (fun answer b => do
          let a ← simulateQ randomOracle (continuation answer)
          next a b) cache

/-- Private read-only precomputation does not change the source result law.
Its extra cache entries are deliberately not exposed by this projection. -/
theorem randomOracle_private_prefix_result {α β : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (D →ₒ R) β)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[Prod.fst <$> (simulateQ randomOracle (ghost >>= fun _ => source)).run cache] =
      𝒟[Prod.fst <$> (simulateQ randomOracle source).run cache] := by
  have h := randomOracle_programs_commute ghost source (fun _ result => pure result) cache
  simp only [bind_pure] at h
  rw [simulateQ_bind, evalDist_map, h, ← evalDist_map]
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _

abbrev PrivateRoSpec (D R : Type) := unifSpec + (D →ₒ R)

def privateRoImpl : QueryImpl (PrivateRoSpec D R) (StateT (QueryCache (D →ₒ R)) ProbComp) :=
  unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle

/-- Private uniform sampling may be interleaved with the source's oracle
queries without obstructing private forest precomputation. -/
theorem randomOracle_query_commute_private {α β : Type} (target : D)
    (source : OracleComp (PrivateRoSpec D R) α)
    (next : R → α → StateT (QueryCache (D →ₒ R)) ProbComp β)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[(do
      let a ← (D →ₒ R).randomOracle target
      let b ← simulateQ privateRoImpl source
      next a b).run cache] =
    𝒟[(do
      let b ← simulateQ privateRoImpl source
      let a ← (D →ₒ R).randomOracle target
      next a b).run cache] := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    cases input with
    | inr input =>
      change 𝒟[(do
        let a ← (D →ₒ R).randomOracle target
        let b ← (D →ₒ R).randomOracle input
        let c ← simulateQ privateRoImpl (continuation b)
        next a c).run cache] = _
      rw [randomOracle_queries_comm]
      simp only [StateT.run_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro result
      exact ih result.1 result.2
    | inl n =>
      have hu {γ : Type} (c : QueryCache (D →ₒ R))
          (k : (PrivateRoSpec D R).Range (.inl n) × QueryCache (D →ₒ R) → ProbComp γ) :
          ((privateRoImpl (D := D) (R := R) (.inl n)).run c >>= k) =
            ((query (spec := unifSpec) n : ProbComp (unifSpec.Range n)) >>= fun u => k (u, c)) := by
        change (((fun answer => (answer, c)) <$>
          (query (spec := unifSpec) n : ProbComp (unifSpec.Range n))) >>= k) = _
        erw [bind_map_left]
      simp only [StateT.run_bind, hu]
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      exact ih value cache

theorem randomOracle_programs_commute_private {α β γ : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (PrivateRoSpec D R) β)
    (next : α → β → StateT (QueryCache (D →ₒ R)) ProbComp γ)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[(do
      let a ← simulateQ randomOracle ghost
      let b ← simulateQ privateRoImpl source
      next a b).run cache] =
    𝒟[(do
      let b ← simulateQ privateRoImpl source
      let a ← simulateQ randomOracle ghost
      next a b).run cache] := by
  induction ghost using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    calc
      _ = 𝒟[(do
          let answer ← (D →ₒ R).randomOracle input
          let b ← simulateQ privateRoImpl source
          let a ← simulateQ randomOracle (continuation answer)
          next a b).run cache] := by
        simp only [StateT.run_bind]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro result
        exact ih result.1 result.2
      _ = _ := randomOracle_query_commute_private input source
        (fun answer b => do
          let a ← simulateQ randomOracle (continuation answer)
          next a b) cache

/-- A local cache records exactly the raw RO answers observed by the source.
It never supplies answers or controls the source's branching. -/
def privateRoObserve : QueryImpl (PrivateRoSpec D R)
    (StateT (QueryCache (D →ₒ R)) (OracleComp (PrivateRoSpec D R)))
  | .inl n => StateT.mk fun cache =>
      (fun answer => (answer, cache)) <$> query (spec := PrivateRoSpec D R) (.inl n)
  | .inr input => StateT.mk fun cache =>
      (fun answer => (answer, cache.cacheQuery input answer)) <$>
        query (spec := PrivateRoSpec D R) (.inr input)

theorem privateRoObserve_query (input : (PrivateRoSpec D R).Domain)
    (cache : QueryCache (D →ₒ R)) :
    (simulateQ privateRoImpl ((privateRoObserve input).run cache)).run cache =
      (fun result => ((result.1, result.2), result.2)) <$>
        (privateRoImpl input).run cache := by
  rcases input with n | input
  · simp [privateRoObserve, privateRoImpl, QueryImpl.add, unifFwdImpl]
  · have hquery : simulateQ (privateRoImpl (D := D) (R := R))
        (query (spec := PrivateRoSpec D R) (.inr input)) = (D →ₒ R).randomOracle input :=
        (simulateQ_query _ _).trans (id_map _)
    simp only [privateRoObserve, StateT.run_mk, simulateQ_map, hquery, StateT.run_map]
    change (fun p : R × QueryCache (D →ₒ R) =>
      ((p.1, cache.cacheQuery input p.1), p.2)) <$> ((D →ₒ R).randomOracle input).run cache =
      (fun p : R × QueryCache (D →ₒ R) => ((p.1, p.2), p.2)) <$>
        ((D →ₒ R).randomOracle input).run cache
    cases hc : cache input with
    | none => simp only [QueryImpl.withCaching_run_none _ hc, Functor.map_map]
    | some answer =>
      have hcache : cache.cacheQuery input answer = cache := by
        funext other
        by_cases heq : other = input
        · subst other
          simp [hc]
        · simp [QueryCache.cacheQuery_of_ne _ _ heq]
      simp only [QueryImpl.withCaching_run_some _ hc, map_pure, hcache]

theorem privateRoObserve_run {α : Type} (source : OracleComp (PrivateRoSpec D R) α)
    (cache : QueryCache (D →ₒ R)) :
    (simulateQ privateRoImpl ((simulateQ privateRoObserve source).run cache)).run cache =
      (fun result => ((result.1, result.2), result.2)) <$>
        (simulateQ privateRoImpl source).run cache := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [privateRoObserve_query]
    simp only [bind_map_left, map_bind]
    congr 1
    funext result
    exact ih result.1 result.2

theorem randomOracle_private_prefix_private {α β : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (PrivateRoSpec D R) β)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[Prod.fst <$> (do
      let _ ← simulateQ randomOracle ghost
      simulateQ privateRoImpl source).run cache] =
      𝒟[Prod.fst <$> (simulateQ privateRoImpl source).run cache] := by
  have h := randomOracle_programs_commute_private ghost source
    (fun _ result => pure result) cache
  simp only [bind_pure] at h
  rw [evalDist_map, h, ← evalDist_map]
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _

/-- Private RO precomputation preserves the complete source observation,
including its own cache and any cost counter returned as part of its result. -/
theorem private_forest_private_observation {α β : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (PrivateRoSpec D R) β)
    (cache : QueryCache (D →ₒ R)) :
    𝒟[Prod.fst <$> (do
      let _ ← simulateQ randomOracle ghost
      simulateQ privateRoImpl ((simulateQ privateRoObserve source).run cache)).run cache] =
      𝒟[(simulateQ privateRoImpl source).run cache] := by
  rw [randomOracle_private_prefix_private, privateRoObserve_run, Functor.map_map]
  exact congrArg evalDist (id_map _)

/-- An output target is fixed before the continuation. Only entries absent
from that initial cache can witness this event. -/
def NewTargetHit (initial : QueryCache (D →ₒ R)) (accepts : D → R → Prop)
    (cache : QueryCache (D →ₒ R)) : Prop :=
  ∃ input answer, initial input = none ∧ cache input = some answer ∧ accepts input answer

theorem newTargetHit_update (initial cache : QueryCache (D →ₒ R))
    (accepts : D → R → Prop) (input : D) (answer : R)
    (hit : NewTargetHit initial accepts (cache.cacheQuery input answer)) :
    NewTargetHit initial accepts cache ∨ accepts input answer := by
  obtain ⟨candidate, value, hnone, hvalue, haccept⟩ := hit
  by_cases heq : candidate = input
  · subst candidate
    simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hvalue
    exact Or.inr (hvalue ▸ haccept)
  · exact Or.inl ⟨candidate, value, hnone,
      (QueryCache.cacheQuery_of_ne cache answer heq).symm.trans hvalue, haccept⟩

def privateTargetCost (charge : D → ℝ≥0∞) : (PrivateRoSpec D R).Domain → ℝ≥0∞
  | .inl _ => 0
  | .inr input => charge input

/-- The output-collision charge is valid for the actual raw domain, including
private sampling. It does not assume independence of different target values. -/
theorem privateRo_newTarget_bound {α : Type}
    (source : OracleComp (PrivateRoSpec D R) α)
    (initial : QueryCache (D →ₒ R)) (accepts : D → R → Prop)
    (charge : D → ℝ≥0∞) (ε : ℝ≥0∞)
    (hprob : ∀ input, Pr[accepts input | $ᵗ R] ≤ ε * charge input) :
    Pr[fun result => NewTargetHit initial accepts result.2 |
      (simulateQ privateRoImpl source).run initial] ≤
        ε * XmssSecurity.expectedSimulatedCost privateRoImpl
          (fun input _ => privateTargetCost charge input) source initial := by
  apply probEvent_le_chargedCost_of_step privateRoImpl (fun _ => True)
    (by intros; trivial) (NewTargetHit initial accepts)
    (fun input _ => privateTargetCost charge input) ε ?_ source initial trivial ?_
  · intro input cache _ hgood
    rcases input with n | input
    · have hzero : Pr[fun result => NewTargetHit initial accepts result.2 |
          (privateRoImpl (D := D) (R := R) (.inl n)).run cache] = 0 := by
        simp [privateRoImpl, QueryImpl.add, unifFwdImpl, hgood]
      rw [hzero]
      exact zero_le
    · change Pr[fun result => NewTargetHit initial accepts result.2 |
        ((D →ₒ R).randomOracle input).run cache] ≤ ε * charge input
      cases hc : cache input with
      | some answer =>
        rw [QueryImpl.withCaching_run_some _ hc]
        have hz : Pr[fun result : R × QueryCache (D →ₒ R) =>
            NewTargetHit initial accepts result.2 | (pure (answer, cache) : ProbComp _)] = 0 := by
          simp [hgood]
        exact hz.le.trans zero_le
      | none =>
        rw [QueryImpl.withCaching_run_none _ hc, probEvent_map]
        refine le_trans (probEvent_mono fun answer _ hit => ?_) (hprob input)
        exact (newTargetHit_update initial cache accepts input answer hit).resolve_left hgood
  · rintro ⟨input, answer, hnone, hvalue, _⟩
    rw [hnone] at hvalue
    cases hvalue

/-- Reverse charging extracts an expected-cost bound from a supported final
counter cap. Unlike a syntactic query bound, this permits unreachable branches
of the source program to have larger costs. -/
theorem expectedSimulatedCost_le_cap
    {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (counter : σ → ℝ≥0∞) (cost : spec.Domain → σ → ℝ≥0∞)
    (hstep : ∀ input s, counter s + cost input s ≤
      ∑' r, Pr[= r | (impl input).run s] * counter r.2)
    (source : OracleComp spec α) (initial : σ) (q : ℝ≥0∞)
    (hcap : ∀ r ∈ support ((simulateQ impl source).run initial), counter r.2 ≤ q) :
    XmssSecurity.expectedSimulatedCost impl cost source initial ≤ q := by
  have h := XmssSecurity.expectedFinal_ge impl (Inv := fun _ => True)
    (by intros; trivial) counter cost (fun input s _ => hstep input s) source initial trivial
  refine (le_add_left le_rfl).trans (h.trans ?_)
  unfold XmssSecurity.expectedFinal
  calc
    _ ≤ ∑' r, Pr[= r | (simulateQ impl source).run initial] * q := by
      apply ENNReal.tsum_le_tsum
      intro r
      by_cases hr : r ∈ support ((simulateQ impl source).run initial)
      · exact mul_le_mul_left' (hcap r hr) _
      · simp [probOutput_eq_zero_of_not_mem_support hr]
    _ ≤ q := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul_right' tsum_probOutput_le_one q).trans_eq (one_mul q)

def rawCallCost : (PrivateRoSpec D R).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

def privateRoCounted : QueryImpl (PrivateRoSpec D R)
    (StateT (QueryCache (D →ₒ R) × ℕ) ProbComp) := fun input =>
  StateT.mk fun state =>
    (fun result => (result.1, result.2, state.2 + rawCallCost input)) <$>
      (privateRoImpl input).run state.1

theorem privateRoCounted_projection {α : Type} (source : OracleComp (PrivateRoSpec D R) α)
    (cache : QueryCache (D →ₒ R)) (count : ℕ) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ privateRoCounted source).run (cache, count) =
        (simulateQ privateRoImpl source).run cache := by
  have hs : ∀ input, TprfSecurityProof.StateMap Prod.fst
      (privateRoCounted (D := D) (R := R) input) (privateRoImpl input) := by
    intro input state
    simp [privateRoCounted, Functor.map_map]
  exact (TprfSecurityProof.StateMap.simulateQ hs source (cache, count)).symm

theorem privateRoCounted_increment (input : (PrivateRoSpec D R).Domain)
    (state : QueryCache (D →ₒ R) × ℕ) :
    (state.2 : ℝ≥0∞) + rawCallCost input =
      ∑' result, Pr[= result | (privateRoCounted input).run state] * (result.2.2 : ℝ≥0∞) := by
  simp only [privateRoCounted, StateT.run_mk, tsum_probOutput_map_mul]
  symm
  apply tsum_probOutput_mul_of_const_on_support
  · intro result _
    exact Nat.cast_add _ _
  · simp

theorem privateRoCounted_expectedCost {α : Type}
    (source : OracleComp (PrivateRoSpec D R) α) (cache : QueryCache (D →ₒ R))
    (count : ℕ) (cost : (PrivateRoSpec D R).Domain → ℝ≥0∞) :
    XmssSecurity.expectedSimulatedCost privateRoCounted (fun input _ => cost input)
      source (cache, count) =
    XmssSecurity.expectedSimulatedCost privateRoImpl (fun input _ => cost input)
      source cache := by
  induction source using OracleComp.inductionOn generalizing cache count with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [XmssSecurity.expectedSimulatedCost_query_bind, privateRoCounted,
      StateT.run_mk, tsum_probOutput_map_mul, ih]

theorem privateRo_expectedCost_le_cap {α : Type}
    (source : OracleComp (PrivateRoSpec D R) α) (cache : QueryCache (D →ₒ R))
    (q : ℕ)
    (hcap : ∀ r ∈ support ((simulateQ privateRoCounted source).run (cache, 0)), r.2.2 ≤ q) :
    XmssSecurity.expectedSimulatedCost privateRoImpl (fun input _ => rawCallCost input)
      source cache ≤ q := by
  have h := expectedSimulatedCost_le_cap privateRoCounted
    (fun state => (state.2 : ℝ≥0∞)) (fun input _ => (rawCallCost input : ℝ≥0∞))
    (fun input state => (privateRoCounted_increment input state).le)
    source (cache, 0) (q : ℝ≥0∞) (fun r hr => by exact_mod_cast hcap r hr)
  simpa only [Nat.cast_zero, zero_add, privateRoCounted_expectedCost] using h

theorem privateRo_newTarget_bound_cap {α : Type}
    (source : OracleComp (PrivateRoSpec D R) α)
    (initial : QueryCache (D →ₒ R)) (accepts : D → R → Prop)
    (ε : ℝ≥0∞) (hprob : ∀ input, Pr[accepts input | $ᵗ R] ≤ ε)
    (q : ℕ)
    (hcap : ∀ r ∈ support ((simulateQ privateRoCounted source).run (initial, 0)), r.2.2 ≤ q) :
    Pr[fun result => NewTargetHit initial accepts result.2 |
      (simulateQ privateRoImpl source).run initial] ≤ ε * q := by
  have hb := privateRo_newTarget_bound source initial accepts (fun _ => 1) ε
    (fun input => by simpa only [mul_one] using hprob input)
  have he : (fun (input : (PrivateRoSpec D R).Domain) (_ : QueryCache (D →ₒ R)) =>
      privateTargetCost (fun _ => 1) input) =
      (fun input _ => (rawCallCost input : ℝ≥0∞)) := by
    funext input cache
    cases input <;> simp [privateTargetCost, rawCallCost]
  rw [he] at hb
  exact hb.trans (mul_le_mul_left' (privateRo_expectedCost_le_cap source initial q hcap) ε)

theorem raw_randomOracle_cache_le {α : Type} (source : OracleComp (D →ₒ R) α)
    (cache : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (hr : result ∈ support ((simulateQ randomOracle source).run cache)) : cache ≤ result.2 := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value =>
    have heq : result = (value, cache) := by simpa using hr
    simpa [heq]
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨head, hh, ht⟩ := hr
    exact (QueryImpl.withCaching_cache_le _ input cache head hh).trans (ih head.1 head.2 ht)

/-- A cache-monotone event can only become more likely when a private forest
is moved before the source. This does not reveal its extra entries to the source. -/
theorem private_forest_event_mono {α β : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (PrivateRoSpec D R) β)
    (initial : QueryCache (D →ₒ R)) (win : β × QueryCache (D →ₒ R) → Prop)
    (hmono : ∀ value left right, left ≤ right → win (value, left) → win (value, right)) :
    Pr[win | (simulateQ privateRoImpl source).run initial] ≤
      Pr[win | (do
        let _ ← simulateQ randomOracle ghost
        simulateQ privateRoImpl source).run initial] := by
  have h := randomOracle_programs_commute_private ghost source
    (fun _ result => pure result) initial
  simp only [bind_pure] at h
  conv_rhs => rw [probEvent_def, h, ← probEvent_def]
  simp only [StateT.run_bind, StateT.run_pure]
  conv_lhs => rw [← bind_pure ((simulateQ privateRoImpl source).run initial)]
  apply probEvent_bind_mono
  intro result _
  by_cases hw : win result
  · have hone : Pr[win | ((simulateQ randomOracle ghost).run result.2 >>= fun p =>
        pure (result.1, p.2))] = 1 := by
      apply probEvent_eq_one
      refine ⟨by simp, ?_⟩
      intro out ho
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ho
      obtain ⟨p, hp, rfl⟩ := ho
      exact hmono _ _ _ (raw_randomOracle_cache_le ghost result.2 p hp) hw
    rw [hone]
    exact probEvent_le_one
  · have hz : Pr[win | (pure result : ProbComp _)] = 0 := by simp [hw]
    exact hz.le.trans zero_le

theorem privateRo_cache_le {α : Type} (source : OracleComp (PrivateRoSpec D R) α)
    (cache : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (hr : result ∈ support ((simulateQ privateRoImpl source).run cache)) : cache ≤ result.2 := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value =>
    have heq : result = (value, cache) := by simpa using hr
    simpa [heq]
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨head, hh, ht⟩ := hr
    have hhead : cache ≤ head.2 := by
      rcases input with n | input
      · simp [privateRoImpl, QueryImpl.add, unifFwdImpl, support_map] at hh
        obtain ⟨value, _, rfl⟩ := hh
        exact le_rfl
      · exact QueryImpl.withCaching_cache_le _ input cache head hh
    exact hhead.trans (ih head.1 head.2 ht)

theorem raw_query_support (input : D) (cache : QueryCache (D →ₒ R))
    (result : R × QueryCache (D →ₒ R))
    (hr : result ∈ support (((D →ₒ R).randomOracle input).run cache)) :
    result.2 input = some result.1 ∧ cache ≤ result.2 ∧
      ∀ other, other ≠ input → result.2 other = cache other := by
  cases hc : cache input with
  | none =>
    rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    exact ⟨QueryCache.cacheQuery_self _ _ _, QueryCache.le_cacheQuery _ hc,
      fun other hne => QueryCache.cacheQuery_of_ne _ _ hne⟩
  | some answer =>
    rw [QueryImpl.withCaching_run_some _ hc] at hr
    have heq : result = (answer, cache) := by simpa using hr
    subst result
    exact ⟨hc, le_rfl, fun _ _ => rfl⟩

/-- Counting a selected source domain preserves the actual adaptive cost,
including when the source stops after its first successful trial. -/
theorem private_counted_expectation {α : Type}
    (selected : (PrivateRoSpec D R).Domain → Prop) [DecidablePred selected]
    (source : OracleComp (PrivateRoSpec D R) α) (cache : QueryCache (D →ₒ R)) :
    (∑' result, Pr[= result | (simulateQ privateRoImpl
      (XmssSecurity.QueryCounting.counted selected source)).run cache] *
        (result.1.2 : ℝ≥0∞)) =
      XmssSecurity.expectedSimulatedCost privateRoImpl
        (fun input _ => if selected input then 1 else 0) source cache := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value => simp [XmssSecurity.QueryCounting.counted_pure]
  | query_bind input next ih =>
    simp only [XmssSecurity.QueryCounting.counted_query_bind, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, Nat.cast_add,
      mul_add, ENNReal.tsum_add, XmssSecurity.expectedSimulatedCost_query_bind]
    by_cases hs : selected input <;> simp [ENNReal.tsum_mul_right, ih, hs]

/-- A private prefix preserves expected selected-domain cost as well as the
source's output law. No fixed syntactic query bound is required. -/
theorem private_prefix_expectedCost {α β : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (PrivateRoSpec D R) β)
    (selected : (PrivateRoSpec D R).Domain → Prop) [DecidablePred selected]
    (cache : QueryCache (D →ₒ R)) :
    (∑' pre, Pr[= pre | (simulateQ randomOracle ghost).run cache] *
      XmssSecurity.expectedSimulatedCost privateRoImpl
        (fun input _ => if selected input then 1 else 0) source pre.2) =
      XmssSecurity.expectedSimulatedCost privateRoImpl
        (fun input _ => if selected input then 1 else 0) source cache := by
  have h := randomOracle_private_prefix_private ghost
    (XmssSecurity.QueryCounting.counted selected source) cache
  have he := congrArg (fun d => ∑' result : β × ℕ,
    d result * (result.2 : ℝ≥0∞)) h
  change (∑' result, Pr[= result | Prod.fst <$> (do
      let _ ← simulateQ randomOracle ghost
      simulateQ privateRoImpl (XmssSecurity.QueryCounting.counted selected source)).run cache] *
        (result.2 : ℝ≥0∞)) =
    (∑' result, Pr[= result | Prod.fst <$>
      (simulateQ privateRoImpl (XmssSecurity.QueryCounting.counted selected source)).run cache] *
        (result.2 : ℝ≥0∞)) at he
  simp only [tsum_probOutput_map_mul, StateT.run_bind, tsum_probOutput_bind_mul,
    private_counted_expectation] at he
  exact he

end PrivateForest

/-- Reconstruct precisely the source cache from its low-level RO transcript,
excluding all private precomputation. Internal hash reads must be logged here. -/
def sourceHashObservation {α : Type} (source : OracleComp XmssSecurity.HashSpec α)
    (cache : QueryCache XmssSecurity.HashSpec) :
    OracleComp XmssSecurity.HashSpec (α × QueryCache XmssSecurity.HashSpec) := do
  let result ← source.withQueryLog
  pure (result.1, XmssSecurity.extendHashCacheWithLog cache result.2)

theorem sourceHashObservation_eq {α : Type} (source : OracleComp XmssSecurity.HashSpec α)
    (cache : QueryCache XmssSecurity.HashSpec) :
    𝒟[Prod.fst <$> (simulateQ randomOracle (sourceHashObservation source cache)).run cache] =
      𝒟[(simulateQ randomOracle source).run cache] := by
  rw [sourceHashObservation, simulateQ_bind]
  simp only [simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rw [← XmssSecurity.withQueryLog_cache_projection source cache]
  simp only [map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  intro result hr
  change 𝒟[pure (result.1.1, XmssSecurity.extendHashCacheWithLog cache result.1.2)] =
    𝒟[pure (result.1.1, result.2)]
  rw [XmssSecurity.withQueryLog_finalCache_eq_extendHashCacheWithLog source cache result hr]

/-- The complete source result and its original cache survive an arbitrary
private forest prefix. The source result may include its own exact call count;
no charge for the private prefix is inserted into that result. -/
theorem private_forest_source_observation {α β : Type}
    (ghost : OracleComp XmssSecurity.HashSpec α)
    (source : OracleComp XmssSecurity.HashSpec β)
    (cache : QueryCache XmssSecurity.HashSpec) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (ghost >>= fun _ => sourceHashObservation source cache)).run cache] =
      𝒟[(simulateQ randomOracle source).run cache] :=
  (randomOracle_private_prefix_result ghost (sourceHashObservation source cache) cache).trans
    (sourceHashObservation_eq source cache)


/-- The public bottom row masks its first two chain labels by the two PRF
coordinates and leaves its endpoint unchanged. This map is its own inverse. -/
def bottomMask (masks : LeanXmss.Digest × LeanXmss.Digest)
    (row : LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest) :=
  (row.1 ^^^ masks.1, row.2.1 ^^^ masks.2, row.2.2)

theorem bottomMask_involutive (masks : LeanXmss.Digest × LeanXmss.Digest) :
    Function.Involutive (bottomMask masks) := by
  rintro ⟨a, b, c⟩
  simp [bottomMask, BitVec.xor_assoc]

open Classical in
/-- Joint change of variables for all privately precomputed bottom rows.
The continuation retains both public rows and their actual chain labels;
there is no assertion that labels are independent of the programmed cache. -/
theorem bottomMask_table_change {Index α : Type} [Fintype Index]
    (masks : Index → LeanXmss.Digest × LeanXmss.Digest)
    (next : (Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest) →
      (Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest) → ProbComp α) :
    𝒟[do
      let rows ← $ᵗ (Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest)
      next (fun i => bottomMask (masks i) (rows i)) rows] =
    𝒟[do
      let publicRows ← $ᵗ (Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest)
      next publicRows (fun i => bottomMask (masks i) (publicRows i))] := by
  let shift := fun rows : Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest =>
    fun i => bottomMask (masks i) (rows i)
  have hinv : Function.Involutive shift := by
    intro rows
    funext i
    exact bottomMask_involutive (masks i) (rows i)
  have hu := evalDist_map_bijective_uniform_cross
    (α := Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest) shift hinv.bijective
  calc
    _ = 𝒟[do
      let rows ← shift <$> ($ᵗ (Index → LeanXmss.Digest × LeanXmss.Digest × LeanXmss.Digest))
      next rows (shift rows)] := by
        rw [bind_map_left]
        apply congrArg evalDist
        apply bind_congr
        intro rows
        rw [hinv rows]
    _ = _ := by rw [evalDist_bind, hu, ← evalDist_bind]

/-- Initial top-chain generation admits independent intermediate labels.
The complete programmed cache is retained for subsequent signing queries. -/
theorem top_chain_programmed
    (P : XmssSecurity.PublicParameter) (b : XmssSecurity.TopIndex)
    (chain : XmssSecurity.ChainIndex) (steps : ℕ) (seed : XmssSecurity.Digest)
    (cache : QueryCache XmssSecurity.HashSpec)
    (hsteps : steps ≤ XmssSecurity.chainLength - 1)
    (hfresh : ∀ step : XmssSecurity.ChainStep, ∀ input,
      XmssSecurity.AtHashAddress P (XmssSecurity.ChainKey.chainDomain (.inr b) chain step) input →
        cache input = none) :
    𝒟[(simulateQ randomOracle
      (LeanXmss.Concrete.chainWalk P LeanXmss.topLayer (XmssSecurity.Bridge.topKey b)
        chain 0 steps seed : OracleComp LeanXmss.HashSpec LeanXmss.Digest)).run cache] =
    𝒟[(fun r : Vector XmssSecurity.Digest (steps + 1) × QueryCache XmssSecurity.HashSpec =>
      (r.1.back, r.2)) <$>
      XmssSecurity.programmedChainTrajectory P (.inr b) chain 0 steps seed cache] := by
  rw [XmssSecurity.Bridge.chainWalk_top, ← XmssSecurity.Concrete.keyChainWalk_inr]
  change 𝒟[(simulateQ XmssSecurity.HashSpec.randomOracle
    (XmssSecurity.Concrete.keyChainWalk P (.inr b) chain 0 steps seed :
      OracleComp XmssSecurity.HashSpec XmssSecurity.Digest)).run cache] = _
  rw [← XmssSecurity.evalDist_chainTrajectory_run_cache_eq_keyChainWalk_run_cache]
  rw [evalDist_map, XmssSecurity.evalDist_chainTrajectory_eq_programmed
    P (.inr b) chain 0 steps seed cache (by simpa using hsteps) hfresh, ← evalDist_map]

/-- The top intermediate labels come from chain hashing, not from unused
threshold-PRF coordinates. Their uniform law is supplied by the chain coupling. -/
theorem top_chain_labels_uniform
    (P : XmssSecurity.PublicParameter) (b : XmssSecurity.TopIndex)
    (chain : XmssSecurity.ChainIndex) (steps : ℕ) (seed : XmssSecurity.Digest)
    (cache : QueryCache XmssSecurity.HashSpec)
    (hsteps : steps ≤ XmssSecurity.chainLength - 1) :
    𝒟[Prod.fst <$> XmssSecurity.programmedChainTrajectory P (.inr b) chain 0 steps seed cache] =
      𝒟[XmssSecurity.CappedChain.uniformTrajectoryFromSeed steps seed] := by
  exact XmssSecurity.CappedChain.evalDist_programmedChainTrajectory_fst_eq_uniform
    P (.inr b) chain 0 steps seed cache (by simpa using hsteps)

def topRowTrajectories (P : XmssSecurity.PublicParameter)
    (start : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (steps : ℕ) (rows : List (XmssSecurity.TopIndex × XmssSecurity.ChainIndex)) :
    OracleComp XmssSecurity.HashSpec (List (Vector XmssSecurity.Digest (steps + 1))) :=
  rows.mapM fun row =>
    XmssSecurity.Concrete.chainTrajectory P (.inr row.1) row.2 0 steps (start row.1 row.2)

def programmedTopRows (P : XmssSecurity.PublicParameter)
    (start : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (steps : ℕ) : List (XmssSecurity.TopIndex × XmssSecurity.ChainIndex) →
      QueryCache XmssSecurity.HashSpec →
      ProbComp (List (Vector XmssSecurity.Digest (steps + 1)) × QueryCache XmssSecurity.HashSpec)
  | [], cache => pure ([], cache)
  | row :: rows, cache => do
      let first ← XmssSecurity.programmedChainTrajectory P (.inr row.1) row.2 0 steps
        (start row.1 row.2) cache
      let rest ← programmedTopRows P start steps rows first.2
      pure (first.1 :: rest.1, rest.2)

set_option maxRecDepth 3000 in
set_option maxHeartbeats 800000 in
/-- The whole ordered top-chain prefix has a programmed-cache coupling.
Freshness for each subsequent row follows from address separation. -/
theorem top_rows_programmed (P : XmssSecurity.PublicParameter)
    (start : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (steps : ℕ) (hsteps : steps ≤ XmssSecurity.chainLength - 1)
    (rows : List (XmssSecurity.TopIndex × XmssSecurity.ChainIndex))
    (cache : QueryCache XmssSecurity.HashSpec) (hnodup : rows.Nodup)
    (hfresh : ∀ row ∈ rows, ∀ step : XmssSecurity.ChainStep, ∀ input,
      XmssSecurity.AtHashAddress P
        (XmssSecurity.ChainKey.chainDomain (.inr row.1) row.2 step) input → cache input = none) :
    𝒟[(simulateQ randomOracle (topRowTrajectories P start steps rows)).run cache] =
      𝒟[programmedTopRows P start steps rows cache] := by
  induction rows generalizing cache with
  | nil => simp [topRowTrajectories, programmedTopRows]
  | cons row rows ih =>
    have hfirst := XmssSecurity.evalDist_chainTrajectory_eq_programmed P (.inr row.1) row.2 0
      steps (start row.1 row.2) cache (by simpa using hsteps)
        (fun step input haddr => hfresh row (List.mem_cons_self ..) step input haddr)
    simp only [topRowTrajectories, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, programmedTopRows]
    rw [evalDist_bind, hfirst, ← evalDist_bind]
    apply evalDist_bind_congr
    intro first hprogrammed
    have hactual := (mem_support_iff_of_evalDist_eq hfirst first).mpr hprogrammed
    have htail : ∀ later ∈ rows, ∀ step : XmssSecurity.ChainStep, ∀ input,
        XmssSecurity.AtHashAddress P
          (XmssSecurity.ChainKey.chainDomain (.inr later.1) later.2 step) input →
            first.2 input = none := by
      intro later hlater step input haddr
      apply XmssSecurity.Concrete.CacheReplay.cache_none_of_zero_query_bound
        (XmssSecurity.Concrete.chainTrajectory P (.inr row.1) row.2 0 steps
          (start row.1 row.2)) input cache first.2 first.1
      · apply OracleComp.IsQueryBoundP.of_imp
          (p' := XmssSecurity.AtHashAddress P
            (XmssSecurity.ChainKey.chainDomain (.inr later.1) later.2 step))
        · intro candidate heq
          subst candidate
          exact haddr
        · apply XmssSecurity.Concrete.chainTrajectory_queryBound_zero_of_avoids
          intro offset hoffset hvalid heq
          have he := XmssSecurity.ChainKey.chainDomain_injective heq
          have hr : row = later := Prod.ext (Sum.inr.inj he.1) he.2.1
          exact (List.nodup_cons.mp hnodup).1 (hr ▸ hlater)
      · exact hfresh later (List.mem_cons_of_mem _ hlater) step input haddr
      · exact hactual
    have hrest := ih first.2 (List.nodup_cons.mp hnodup).2 htail
    simp only [topRowTrajectories] at hrest
    rw [evalDist_bind, hrest, ← evalDist_bind]

def topRowOrder : List (Fin (2 ^ LeanXmss.layerHeight) × LeanXmss.ChainIndex) :=
  (List.finRange (2 ^ LeanXmss.layerHeight)).product (List.finRange LeanXmss.numChains)

theorem topRowOrder_nodup : topRowOrder.Nodup :=
  (List.nodup_finRange _).product (List.nodup_finRange _)

/-- The real top-job order, not a reordered enumeration of the chain keys. -/
theorem topJobs_eq_topRowOrder :
    topJobs = topRowOrder.map (fun row =>
      ⟨.chainEnd (topKey row.1) row.2,
        [.chain LeanXmss.topLayer (topKey row.1) row.2 (digit 0)]⟩) := by
  simp only [topJobs, topRowOrder, List.product, List.map_flatMap, List.map_map]
  apply congrArg (fun f => (List.finRange (2 ^ LeanXmss.layerHeight)).flatMap f)
  funext b
  apply congrArg (fun f => (List.finRange LeanXmss.numChains).map f)
  funext chain
  rfl

theorem initial_top_rows_programmed (P : XmssSecurity.PublicParameter)
    (start : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest) :
    𝒟[(simulateQ randomOracle (topRowTrajectories P start 3 topRowOrder)).run ∅] =
      𝒟[programmedTopRows P start 3 topRowOrder ∅] := by
  apply top_rows_programmed P start 3 (by decide) topRowOrder ∅ topRowOrder_nodup
  intro row hrow step input haddr
  rfl

set_option maxRecDepth 3000 in
theorem programmedTopRows_labels_uniform (P : XmssSecurity.PublicParameter)
    (start : XmssSecurity.TopIndex → XmssSecurity.ChainIndex → XmssSecurity.Digest)
    (steps : ℕ) (hsteps : steps ≤ XmssSecurity.chainLength - 1)
    (rows : List (XmssSecurity.TopIndex × XmssSecurity.ChainIndex))
    (cache : QueryCache XmssSecurity.HashSpec) :
    𝒟[Prod.fst <$> programmedTopRows P start steps rows cache] =
      𝒟[rows.mapM (fun row =>
        XmssSecurity.CappedChain.uniformTrajectoryFromSeed steps (start row.1 row.2))] := by
  induction rows generalizing cache with
  | nil => simp [programmedTopRows]
  | cons row rows ih =>
    simp only [programmedTopRows, List.mapM_cons, map_bind, map_pure]
    let firstProgram := XmssSecurity.programmedChainTrajectory P (.inr row.1) row.2 0 steps
      (start row.1 row.2) cache
    let restProgram := rows.mapM (fun row =>
      XmssSecurity.CappedChain.uniformTrajectoryFromSeed steps (start row.1 row.2))
    calc
      _ = 𝒟[firstProgram >>= fun first => restProgram >>= fun rest => pure (first.1 :: rest)] := by
        apply evalDist_bind_congr
        intro first _
        change 𝒟[(fun rest => first.1 :: rest.1) <$>
          programmedTopRows P start steps rows first.2] =
          𝒟[(fun rest => first.1 :: rest) <$> restProgram]
        have hmap : (fun rest => first.1 :: rest.1) <$>
            programmedTopRows P start steps rows first.2 =
            (fun rest => first.1 :: rest) <$>
              (Prod.fst <$> programmedTopRows P start steps rows first.2) := by
          rw [Functor.map_map]
        rw [hmap, evalDist_map, ih first.2, ← evalDist_map]
      _ = 𝒟[(Prod.fst <$> firstProgram) >>= fun first => restProgram >>= fun rest =>
          pure (first :: rest)] := by rw [bind_map_left]
      _ = _ := by
        rw [evalDist_bind, top_chain_labels_uniform P row.1 row.2 steps
          (start row.1 row.2) cache hsteps, ← evalDist_bind]

theorem mapM_map_output {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (xs : List α) (f : α → m β) (g : β → γ) :
    xs.mapM (fun x => g <$> f x) = List.map g <$> xs.mapM f := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.mapM_cons, ih, map_bind, bind_map_left, Functor.map_map]

/-- Normalize an actual top reference job to the endpoint of its coupled
trajectory. Only the start coordinate is read from the threshold PRF. -/
theorem referenceTopJob_eq_trajectory (P : XmssSecurity.PublicParameter)
    (F : Point → LeanXmss.Digest) (b : Fin (2 ^ LeanXmss.layerHeight))
    (chain : LeanXmss.ChainIndex) :
    referenceJob (m := OracleComp LeanXmss.HashSpec) (fun oa => oa) (fun point => pure (F point)) P
      ⟨.chainEnd (topKey b) chain,
        [.chain LeanXmss.topLayer (topKey b) chain (digit 0)]⟩ =
      (fun values : Vector XmssSecurity.Digest 4 => bitsOfDigest values.back) <$>
        XmssSecurity.Concrete.chainTrajectory P (.inr b) chain 0 3
          (F (.chain LeanXmss.topLayer (topKey b) chain (digit 0))) := by
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, pure_bind, map_pure,
    List.getD_cons_zero]
  have hk : topKey b = XmssSecurity.Bridge.topKey b := rfl
  rw [hk, XmssSecurity.Bridge.chainWalk_top]
  change (bitsOfDigest <$> (XmssSecurity.Concrete.topChainWalk P b chain 0 3
    (F (.chain LeanXmss.topLayer (XmssSecurity.Bridge.topKey b) chain (digit 0))) :
      OracleComp XmssSecurity.HashSpec XmssSecurity.Digest)) = _
  rw [← XmssSecurity.Concrete.keyChainWalk_inr,
    ← XmssSecurity.Concrete.chainTrajectory_back_map_eq_keyChainWalk]
  erw [Functor.map_map]

theorem referenceTopJobs_eq_trajectories (P : XmssSecurity.PublicParameter)
    (F : Point → LeanXmss.Digest) :
    topJobs.mapM (referenceJob (m := OracleComp LeanXmss.HashSpec)
      (fun oa => oa) (fun point => pure (F point)) P) =
      List.map (fun values : Vector XmssSecurity.Digest 4 => bitsOfDigest values.back) <$>
        topRowTrajectories P
          (fun b chain => F (.chain LeanXmss.topLayer (topKey b) chain (digit 0))) 3 topRowOrder := by
  rw [topJobs_eq_topRowOrder, List.mapM_map]
  have h := mapM_map_output topRowOrder
    (fun row => XmssSecurity.Concrete.chainTrajectory P (.inr row.1) row.2 0 3
      (F (.chain LeanXmss.topLayer (topKey row.1) row.2 (digit 0))))
    (fun values : Vector XmssSecurity.Digest 4 => bitsOfDigest values.back)
  refine Eq.trans ?_ h
  apply TprfSecurityProof.mapM_congr_mem
  intro row hrow
  exact referenceTopJob_eq_trajectory P F row.1 row.2

set_option maxRecDepth 3000 in
/-- The programmed top rows may be followed by the actual Merkle construction
or any other hash computation that uses the returned row outputs. -/
theorem referenceTopJobs_programmed {α : Type} (P : XmssSecurity.PublicParameter)
    (F : Point → LeanXmss.Digest)
    (next : List (List Bit) → OracleComp LeanXmss.HashSpec α) :
    𝒟[(simulateQ randomOracle (do
      let outputs ← topJobs.mapM (referenceJob (m := OracleComp LeanXmss.HashSpec)
        (fun oa => oa) (fun point => pure (F point)) P)
      next outputs)).run ∅] =
    𝒟[do
      let rows ← programmedTopRows P
        (fun b chain => F (.chain LeanXmss.topLayer (topKey b) chain (digit 0))) 3 topRowOrder ∅
      (simulateQ LeanXmss.HashSpec.randomOracle
        (next (rows.1.map (fun values : Vector XmssSecurity.Digest 4 => bitsOfDigest values.back)))).run rows.2] := by
  rw [referenceTopJobs_eq_trajectories]
  have hrows := initial_top_rows_programmed P
    (fun b chain => F (.chain LeanXmss.topLayer (topKey b) chain (digit 0)))
  generalize htraj : topRowTrajectories P
    (fun b chain => F (.chain LeanXmss.topLayer (topKey b) chain (digit 0)))
      3 topRowOrder = oa at hrows ⊢
  generalize hprog : programmedTopRows P
    (fun b chain => F (.chain LeanXmss.topLayer (topKey b) chain (digit 0)))
      3 topRowOrder ∅ = ob at hrows ⊢
  simp only [simulateQ_bind, StateT.run_bind]
  erw [simulateQ_map, StateT.run_map, bind_map_left]
  change 𝒟[(simulateQ XmssSecurity.HashSpec.randomOracle oa).run ∅ >>= fun r =>
    (simulateQ LeanXmss.HashSpec.randomOracle
      (next (r.1.map (fun values : Vector XmssSecurity.Digest 4 =>
        bitsOfDigest values.back)))).run r.2] = _
  rw [evalDist_bind, hrows, ← evalDist_bind]

def topTreeAfterRows (P : LeanXmss.PublicParameter) (outputs : List (List Bit)) :
    OracleComp LeanXmss.HashSpec (Option TreeOutput) :=
  ceremonyOutput (fun oa => oa) P (fun _ => pure (some outputs)) emptyTop .top

/-- The top forest used by threshold signing, with fixed PRF starts, is
coupled to independently programmed chain rows followed by its own Merkle
construction. This establishes setup, not the later on-demand bottom trees. -/
theorem referenceTopTree_programmed (P : XmssSecurity.PublicParameter)
    (F : Point → LeanXmss.Digest) :
    𝒟[(simulateQ randomOracle
      (referenceTree (m := OracleComp LeanXmss.HashSpec) (fun oa => oa)
        (fun point => pure (F point)) P emptyTop .top)).run ∅] =
    𝒟[do
      let rows ← programmedTopRows P
        (fun b chain => F (.chain LeanXmss.topLayer (topKey b) chain (digit 0))) 3 topRowOrder ∅
      (simulateQ LeanXmss.HashSpec.randomOracle
        (topTreeAfterRows P (rows.1.map (fun values : Vector XmssSecurity.Digest 4 => bitsOfDigest values.back)))).run rows.2] := by
  have h := referenceTopJobs_programmed P F (topTreeAfterRows P)
  simpa only [referenceTree, topTreeAfterRows, ceremonyOutput, bind_map_left, pure_bind] using h

section CommitmentSimulation

open Classical
set_option maxRecDepth 3000

/-- Parsing a commitment trial uses only public data, never the hidden PRF value. -/
def commitmentCandidate (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (input : LeanXmss.HashInput) : Option LeanXmss.Digest :=
  if h : ∃ rho, commitmentInput P e rho = input then some h.choose else none

theorem commitmentCandidate_eq_some (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (input : LeanXmss.HashInput) (rho : LeanXmss.Digest) :
    commitmentCandidate P e input = some rho ↔ commitmentInput P e rho = input := by
  unfold commitmentCandidate
  split_ifs with h
  · constructor
    · intro heq
      simpa only [Option.some.inj heq] using h.choose_spec
    · intro heq
      congr 1
      exact SigningCoreProof.commitmentInput_injective P e (h.choose_spec.trans heq.symm)
  · simp only [Option.noConfusion, false_iff]
    exact fun heq => h ⟨rho, heq⟩

theorem commitmentCandidate_unique_key (P : LeanXmss.PublicParameter)
    (e f : LeanXmss.KeyIndex) (input : LeanXmss.HashInput) (rho tau : LeanXmss.Digest)
    (he : commitmentCandidate P e input = some rho)
    (hf : commitmentCandidate P f input = some tau) : e = f :=
  commitmentInput_key_eq P ((commitmentCandidate_eq_some P e input rho).mp he |>.trans
    ((commitmentCandidate_eq_some P f input tau).mp hf).symm)

/-- A commitment input has one globally selected trial, even with many keys
and signing sessions. This decoder is independent of the hidden table. -/
def commitmentTrial (P : LeanXmss.PublicParameter) (input : LeanXmss.HashInput) :
    Option (LeanXmss.KeyIndex × LeanXmss.Digest) :=
  if h : ∃ trial : LeanXmss.KeyIndex × LeanXmss.Digest,
      commitmentInput P trial.1 trial.2 = input then some h.choose else none

theorem commitmentTrial_eq_some (P : LeanXmss.PublicParameter) (input : LeanXmss.HashInput)
    (e : LeanXmss.KeyIndex) (rho : LeanXmss.Digest) :
    commitmentTrial P input = some (e, rho) ↔ commitmentInput P e rho = input := by
  unfold commitmentTrial
  split_ifs with h
  · constructor
    · intro heq
      simpa only [Option.some.inj heq] using h.choose_spec
    · intro heq
      have hk : h.choose.1 = e := commitmentInput_key_eq P (h.choose_spec.trans heq.symm)
      have hv : h.choose.2 = rho := SigningCoreProof.commitmentInput_injective P e
        (by simpa only [hk] using h.choose_spec.trans heq.symm)
      exact congrArg some (Prod.ext hk hv)
  · simp only [Option.noConfusion, false_iff]
    exact fun heq => h ⟨(e, rho), heq⟩

variable {Index : Type} [Fintype Index] [DecidableEq Index]

local instance commitmentHazardDecidable : DecidablePred
    (XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery (Index := Index)) :=
  Classical.decPred _

def trialProbe {Key : Type} (index : Key → Index)
    (trial : Option (Key × LeanXmss.Digest)) :
    OracleComp (XmssSecurity.FirstLaneOracleSimulation.World Index) Unit :=
  match trial with
  | none => pure ()
  | some pair => XmssSecurity.FirstLaneOracleSimulation.probeQuery (index pair.1) pair.2

theorem trialProbe_call_bound {Key : Type} (index : Key → Index)
    (trial : Option (Key × LeanXmss.Digest)) :
    (trialProbe index trial).IsQueryBoundP
      (XmssSecurity.FirstLaneOracleSimulation.IsHazardQuery (Index := Index)) 1 := by
  cases trial with
  | none => exact isQueryBoundP_pure _ _ _
  | some pair => exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => Nat.zero_lt_one)

/-- Planting the honest commitment commutes with every missed trial. This is
an equality of complete hash-cache executions, including cache hits. -/
theorem commitment_query_miss (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (rho : LeanXmss.Digest) (output : LeanXmss.HashOutput)
    (cache : QueryCache LeanXmss.HashSpec) (input : LeanXmss.HashInput)
    (hmiss : input ≠ commitmentInput P e rho) :
    ((LeanXmss.HashSpec.randomOracle input).run
      (cache.cacheQuery (commitmentInput P e rho) output)) =
      (fun r => (r.1, r.2.cacheQuery (commitmentInput P e rho) output)) <$>
        ((LeanXmss.HashSpec.randomOracle input).run cache) := by
  have heq : cache.cacheQuery (commitmentInput P e rho) output input = cache input :=
    QueryCache.cacheQuery_of_ne cache output hmiss
  cases hc : cache input with
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ (heq.trans hc),
      QueryImpl.withCaching_run_none _ hc, Functor.map_map]
    congr 1
    funext answer
    congr 1
    funext u
    by_cases hi : u = input
    · subst u
      simp [QueryCache.cacheQuery_of_ne, hmiss]
    · by_cases ht : u = commitmentInput P e rho
      · subst u
        simp [QueryCache.cacheQuery_of_ne, hmiss.symm]
      · simp [QueryCache.cacheQuery_of_ne, hi, ht]
  | some answer =>
    simp only [randomOracle, QueryImpl.withCaching_run_some _ (heq.trans hc),
      QueryImpl.withCaching_run_some _ hc, map_pure]

/-- The unrevealed branch of commitment generation. The complete output is
sampled independently; only its truncation is published by referenceJob. -/
theorem commitment_generate_fresh (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (rho : LeanXmss.Digest) (cache : QueryCache LeanXmss.HashSpec)
    (hfresh : cache (commitmentInput P e rho) = none) :
    (LeanXmss.HashSpec.randomOracle (commitmentInput P e rho)).run cache =
      (fun output => (output, cache.cacheQuery (commitmentInput P e rho) output)) <$>
        ($ᵗ LeanXmss.HashOutput) := by
  exact QueryImpl.withCaching_run_none _ hfresh

/-- Repeated tree generation reuses the same planted commitment. -/
theorem commitment_generate_cached (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (rho : LeanXmss.Digest) (output : LeanXmss.HashOutput)
    (cache : QueryCache LeanXmss.HashSpec) :
    (LeanXmss.HashSpec.randomOracle (commitmentInput P e rho)).run
        (cache.cacheQuery (commitmentInput P e rho) output) =
      pure (output, cache.cacheQuery (commitmentInput P e rho) output) := by
  apply QueryImpl.withCaching_run_some
  simp

/-- A proof-only stop at the first true-opening query. The operational
simulator records a probe instead; this stop isolates its no-hit executions. -/
def commitmentStopped (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (rho : LeanXmss.Digest) :
    QueryImpl LeanXmss.HashSpec (OptionT (StateT (QueryCache LeanXmss.HashSpec) ProbComp)) :=
  fun input => if input = commitmentInput P e rho then
    OptionT.mk (pure none) else OptionT.lift (LeanXmss.HashSpec.randomOracle input)

/-- Planting may be postponed past an arbitrary adaptive pre-release hash
computation on its no-hit executions. The returned cache is retained. -/
theorem commitment_stopped_plant (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (rho : LeanXmss.Digest) (output : LeanXmss.HashOutput)
    {α : Type} (oa : OracleComp LeanXmss.HashSpec α)
    (cache : QueryCache LeanXmss.HashSpec) :
    ((simulateQ (commitmentStopped P e rho) oa).run).run
        (cache.cacheQuery (commitmentInput P e rho) output) =
      (fun r => (r.1, r.2.cacheQuery (commitmentInput P e rho) output)) <$>
        (((simulateQ (commitmentStopped P e rho) oa).run).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a => simp
  | query_bind input next ih =>
    by_cases hit : input = commitmentInput P e rho
    · simp [simulateQ_bind, commitmentStopped, hit]
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, commitmentStopped, if_neg hit,
        OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_map_left,
        Option.elim_some, StateT.run_bind]
      rw [commitment_query_miss P e rho output cache input hit]
      simp only [bind_map_left, map_bind, StateT.run_pure, bind_assoc, pure_bind,
        Option.elim_some, ih]

/-- Earlier adversarial queries cannot populate the canonical commitment
entry on a stopped no-hit execution, even if tree generation has not begun. -/
theorem commitment_stopped_fresh (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (rho : LeanXmss.Digest) {α : Type} (oa : OracleComp LeanXmss.HashSpec α)
    (cache : QueryCache LeanXmss.HashSpec) (hfresh : cache (commitmentInput P e rho) = none)
    (r : Option α × QueryCache LeanXmss.HashSpec)
    (hr : r ∈ support (((simulateQ (commitmentStopped P e rho) oa).run).run cache)) :
    r.2 (commitmentInput P e rho) = none := by
  induction oa using OracleComp.inductionOn generalizing cache r with
  | pure a => simpa using (show r = (some a, cache) from by simpa using hr) ▸ hfresh
  | query_bind input next ih =>
    by_cases hit : input = commitmentInput P e rho
    · have heq : r = (none, cache) := by
        simpa [simulateQ_bind, commitmentStopped, hit] using hr
      simpa [heq] using hfresh
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, commitmentStopped, if_neg hit,
        OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_map_left,
        StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, Option.elim_some,
        mem_support_bind_iff] at hr
      obtain ⟨head, hhead, htail⟩ := hr
      apply ih head.1 head.2 ?_ r htail
      cases hc : cache input with
      | none =>
        rw [randomOracle, QueryImpl.withCaching_run_none _ hc] at hhead
        rw [support_map] at hhead
        obtain ⟨answer, _, rfl⟩ := hhead
        change (cache.cacheQuery input answer) (commitmentInput P e rho) = none
        rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hit)]
        exact hfresh
      | some answer =>
        rw [randomOracle, QueryImpl.withCaching_run_some _ hc] at hhead
        have heq : head = (answer, cache) := by simpa using hhead
        simpa [heq] using hfresh

/-- A commitment generated after an adaptive prefix can be sampled before
that prefix on its no-hit executions. Aborted executions expose no cache;
successful executions retain the actual complete cache for later release. -/
theorem commitment_generate_after_prefix (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) (rho : LeanXmss.Digest)
    {α : Type} (oa : OracleComp LeanXmss.HashSpec α)
    (cache : QueryCache LeanXmss.HashSpec) (hfresh : cache (commitmentInput P e rho) = none) :
    𝒟[do
      let r ← ((simulateQ (commitmentStopped P e rho) oa).run).run cache
      match r.1 with
      | none => pure none
      | some a => do
        let generated ← (LeanXmss.HashSpec.randomOracle (commitmentInput P e rho)).run r.2
        pure (some (a, generated.1, generated.2))] =
    𝒟[do
      let output ← $ᵗ LeanXmss.HashOutput
      let r ← ((simulateQ (commitmentStopped P e rho) oa).run).run
        (cache.cacheQuery (commitmentInput P e rho) output)
      pure (r.1.map fun a => (a, output, r.2))] := by
  simp_rw [commitment_stopped_plant, bind_map_left]
  rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply evalDist_bind_congr
  intro r hr
  cases ha : r.1 with
  | none =>
    simp only [ha, Option.map_none]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      ($ᵗ LeanXmss.HashOutput) (by simp) (pure none)).symm
  | some a =>
    rw [commitment_generate_fresh P e rho r.2
      (commitment_stopped_fresh P e rho oa cache hfresh r hr)]
    simp [ha, bind_map_left]

end CommitmentSimulation

section SigningPresample

open TprfSecurityProof

variable {C : Committee} (prims : Primitives)
  (seeds : C.Term → LeanXmss.HashOutput) (pairKeys : C.Pair → LeanXmss.HashOutput)

def signingHashState (s : SeedHitProof.WState C) : QueryCache LeanXmss.HashSpec :=
  fun input => s.1.1 (.hash input)

theorem hashC_stateMap (input : LeanXmss.HashInput) :
    StateMap (signingHashState (C := C)) (SeedHitProof.hashC input)
      (LeanXmss.HashSpec.randomOracle input) := by
  rintro ⟨⟨cache, slots⟩, count⟩
  have hcache : ∀ output : LeanXmss.HashOutput,
      (fun u => (cache.cacheQuery (.hash input) output) (.hash u)) =
        QueryCache.cacheQuery (spec := LeanXmss.HashSpec) (fun u => cache (.hash u)) input output := by
    intro output
    funext u
    by_cases hu : u = input
    · subst u
      simp
    · have hq : (Query.hash u : Query C) ≠ .hash input := fun heq => hu (Query.hash.inj heq)
      simp [QueryCache.cacheQuery_of_ne, hu, hq]
  simp only [SeedHitProof.hashC, SeedHitProof.countStep, StateT.run_mk,
    onCache_run, Functor.map_map]
  cases hc : cache (.hash input) with
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ (show signingHashState
      ((cache, slots), count) input = none from hc), QueryImpl.withCaching_run_none _ hc]
    simp only [Functor.map_map, Function.comp_def, Prod.map, id_eq, signingHashState]
    congr 1
    funext output
    exact congrArg (fun c => (output, c)) (hcache output).symm
  | some output =>
    rw [randomOracle, QueryImpl.withCaching_run_some _ (show signingHashState
      ((cache, slots), count) input = some output from hc), QueryImpl.withCaching_run_some _ hc]
    rfl

/-- The concrete honest hash interpreter projects to the standard random
oracle on hash inputs, retaining the full cache needed by the chain coupling. -/
theorem signing_hash_projection {α : Type} (oa : OracleComp LeanXmss.HashSpec α) :
    StateMap (signingHashState (C := C)) (simulateQ SeedHitProof.hashC oa)
      (simulateQ LeanXmss.HashSpec.randomOracle oa) :=
  StateMap.simulateQ hashC_stateMap oa

theorem mapM_counted_constant {σ α β : Type} (xs : List α)
    (f : α → StateT (σ × ℕ) ProbComp β) (g : α → β) (state : σ)
    (h : ∀ a ∈ xs, ∀ count, (f a).run (state, count) = pure (g a, state, count + 1))
    (count : ℕ) :
    (xs.mapM f).run (state, count) = pure (xs.map g, state, count + xs.length) := by
  induction xs generalizing count with
  | nil => simp
  | cons a xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, h a (List.mem_cons_self ..), pure_bind]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    simp [StateT.run_pure, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem slotC_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (slot : Slot C) (count : ℕ) :
    (SeedHitProof.slotC slot).run ((cache, fullTable omega), count) =
      pure (omega slot, (cache, fullTable omega), count + 1) := by
  simp only [SeedHitProof.slotC, SeedHitProof.countStep, StateT.run_mk,
    onTable_run, slotOracle_run_full, map_pure]

/-- The actual counted signing PRF call becomes the prescribed sum in the
presampled slot table. Its honest calls retain their entire original cost. -/
theorem prfC_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (point : Point) (count : ℕ) :
    (SeedHitProof.prfC point).run ((cache, fullTable omega), count) =
      pure ((show LeanXmss.Digest from prfSum omega point),
        (cache, fullTable omega), count + C.terms.length) := by
  simp only [SeedHitProof.prfC, StateT.run_bind]
  rw [mapM_counted_constant C.terms _
    (fun term => LeanXmss.truncateHash (omega (.inl (term, point)))) _ (fun term _ count => by
      rw [StateT.run_map, slotC_run_full, map_pure])]
  simp only [pure_bind, StateT.run_pure]
  congr 2
  change TprfCorrectnessProof.toXor _ = _
  rw [toXor_foldl_id, List.map_map,
    show TprfCorrectnessProof.toXor (0 : LeanXmss.Digest) = 0 from rfl, zero_add, prfSum]
  have h := sum_terms_filter (C := C) Finset.univ
    (fun term => TprfCorrectnessProof.toXor (LeanXmss.truncateHash (omega (.inl (term, point)))))
  rw [List.filter_eq_self.mpr (fun term _ => by simp)] at h
  exact h

/-- Honest forest computations use only hash calls and prescribed PRF values. -/
abbrev ForestSpec := LeanXmss.HashSpec + (Point →ₒ LeanXmss.Digest)

def forestHash {α : Type} (oa : OracleComp LeanXmss.HashSpec α) :
    OracleComp ForestSpec α :=
  simulateQ (fun input => query (spec := ForestSpec) (.inl input)) oa

def forestTree (P : LeanXmss.PublicParameter) (top : TopTree) (tree : Tree) :
    OracleComp ForestSpec (Option TreeOutput) :=
  referenceTree forestHash (fun point => query (spec := ForestSpec) (.inr point)) P top tree

def sourceForestImpl : QueryImpl ForestSpec (StateT (SeedHitProof.WState C) ProbComp)
  | .inl input => SeedHitProof.hashC input
  | .inr point => SeedHitProof.prfC point

def fixedSlotState (omega : Slot C → LeanXmss.HashOutput)
    (s : HashCache C × ℕ) : SeedHitProof.WState C :=
  ((s.1, fullTable omega), s.2)

def fixedForestImpl (omega : Slot C → LeanXmss.HashOutput) :
    QueryImpl ForestSpec (StateT (HashCache C × ℕ) ProbComp)
  | .inl input => StateT.mk fun s =>
      (fun r => (r.1, r.2, s.2 + 1)) <$>
        ((Query C →ₒ LeanXmss.HashOutput).randomOracle (.hash input)).run s.1
  | .inr point => StateT.mk fun s =>
      pure ((show LeanXmss.Digest from prfSum omega point), s.1, s.2 + C.terms.length)

theorem fixedForestImpl_stateMap (omega : Slot C → LeanXmss.HashOutput)
    (t : ForestSpec.Domain) :
    StateMap (fixedSlotState omega) (fixedForestImpl omega t)
      (sourceForestImpl (C := C) t) := by
  rcases t with input | point
  · rintro ⟨cache, count⟩
    simp only [sourceForestImpl, fixedForestImpl, fixedSlotState, SeedHitProof.hashC,
      SeedHitProof.countStep, StateT.run_mk, onCache_run, Functor.map_map]
    erw [StateT.run_mk, onCache_run, Functor.map_map]
    rfl
  · rintro ⟨cache, count⟩
    simp only [sourceForestImpl, fixedForestImpl, fixedSlotState, prfC_run_full,
      StateT.run_mk, map_pure]
    erw [prfC_run_full]
    rfl

/-- Exact forest execution with the full counted state. In particular this
retains every non-hash cache entry and the original counter, unlike a hash-only
projection. It applies to adaptive continuations expressible in ForestSpec as well as setup. -/
theorem forest_run_full {α : Type} (omega : Slot C → LeanXmss.HashOutput)
    (oa : OracleComp ForestSpec α) (cache : HashCache C) (count : ℕ) :
    (simulateQ (sourceForestImpl (C := C)) oa).run ((cache, fullTable omega), count) =
      Prod.map id (fixedSlotState omega) <$>
        (simulateQ (fixedForestImpl omega) oa).run (cache, count) :=
  StateMap.simulateQ (fixedForestImpl_stateMap omega) oa (cache, count)

theorem source_forestTree (P : LeanXmss.PublicParameter) (top : TopTree) (tree : Tree) :
    simulateQ (sourceForestImpl (C := C)) (forestTree P top tree) =
      referenceTree (fun oa => simulateQ (SeedHitProof.hashC (C := C)) oa)
        SeedHitProof.prfC P top tree := by
  unfold forestTree
  have h := SeedHitProof.hom_referenceTree (simulateQ' (sourceForestImpl (C := C)))
    (@forestHash) (fun point => query (spec := ForestSpec) (.inr point)) P top tree
  refine h.trans (SeedHitProof.referenceTree_congr _ _ _ _ ?_ ?_ P top tree)
  · intro α oa
    have hh : (sourceForestImpl (C := C) ∘ₛ
        fun input => query (spec := ForestSpec) (.inl input)) = SeedHitProof.hashC := by
      funext input
      exact (simulateQ_query _ _).trans (id_map _)
    exact (QueryImpl.simulateQ_compose _ _ oa).symm.trans (congrArg (fun impl => simulateQ impl oa) hh)
  · intro point
    exact (simulateQ_query _ _).trans (id_map _)

theorem signing_tree_run_full
    (hinj : Function.Injective (slotInput seeds pairKeys))
    (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C) (count : ℕ)
    (P : LeanXmss.PublicParameter) (top : TopTree) (tree : Tree) :
    (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
      (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun point => SigningSecurityProof.liftFree (prfValue seeds point)) P top tree)).run
          ((cache, fullTable omega), count) =
      Prod.map id (fixedSlotState omega) <$>
        (simulateQ (fixedForestImpl omega) (forestTree P top tree)).run (cache, count) := by
  rw [SeedHitProof.split_referenceTree prims seeds pairKeys hinj, ← source_forestTree]
  exact forest_run_full omega _ cache count

def prescribedForestImpl (F : Point → LeanXmss.Digest) :
    QueryImpl ForestSpec (StateT (QueryCache LeanXmss.HashSpec) ProbComp)
  | .inl input => LeanXmss.HashSpec.randomOracle input
  | .inr point => pure (F point)

def fixedHashState (s : HashCache C × ℕ) : QueryCache LeanXmss.HashSpec :=
  fun input => s.1 (.hash input)

theorem fixedForestImpl_hashMap (omega : Slot C → LeanXmss.HashOutput)
    (t : ForestSpec.Domain) :
    StateMap (fixedHashState (C := C)) (fixedForestImpl omega t)
      (prescribedForestImpl (fun point => prfSum omega point) t) := by
  rcases t with input | point
  · intro s
    have h := hashC_stateMap (C := C) input (fixedSlotState omega s)
    have hs := fixedForestImpl_stateMap omega (.inl input) s
    change (SeedHitProof.hashC input).run (fixedSlotState omega s) = _ at hs
    rw [hs] at h
    erw [Functor.map_map] at h
    exact h
  · rintro ⟨cache, count⟩
    simp only [prescribedForestImpl, fixedForestImpl, StateT.run_pure, StateT.run_mk, map_pure]
    rfl

theorem prescribed_forestTree (F : Point → LeanXmss.Digest)
    (P : LeanXmss.PublicParameter) (top : TopTree) (tree : Tree) :
    simulateQ (prescribedForestImpl F) (forestTree P top tree) =
      simulateQ LeanXmss.HashSpec.randomOracle
        (referenceTree (m := OracleComp LeanXmss.HashSpec) (fun oa => oa)
          (fun point => pure (F point)) P top tree) := by
  have h₁ := SeedHitProof.hom_referenceTree (simulateQ' (prescribedForestImpl F))
    (@forestHash) (fun point => query (spec := ForestSpec) (.inr point)) P top tree
  have h₂ := SeedHitProof.hom_referenceTree (simulateQ' LeanXmss.HashSpec.randomOracle)
    (fun oa => oa) (fun point => pure (F point)) P top tree
  refine h₁.trans ((SeedHitProof.referenceTree_congr _ _ _ _ ?_ ?_ P top tree).trans h₂.symm)
  · intro α oa
    have hh : (prescribedForestImpl F ∘ₛ
        fun input => query (spec := ForestSpec) (.inl input)) =
        LeanXmss.HashSpec.randomOracle := by
      funext input
      exact (simulateQ_query _ _).trans (id_map _)
    exact (QueryImpl.simulateQ_compose _ _ oa).symm.trans
      (congrArg (fun impl => simulateQ impl oa) hh)
  · intro point
    exact ((simulateQ_query _ _).trans (id_map _)).trans (simulateQ_pure LeanXmss.HashSpec.randomOracle (F point)).symm

/-- Hash projection of the complete, counted source forest. The preceding
full-state theorem retains the counter and slots for budget and continuation
arguments; this equality supplies the ordinary random-oracle coupling. -/
theorem signing_tree_hash_projection
    (hinj : Function.Injective (slotInput seeds pairKeys))
    (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C) (count : ℕ)
    (P : LeanXmss.PublicParameter) (top : TopTree) (tree : Tree) :
    Prod.map id (signingHashState (C := C)) <$>
      (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
        (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
          (fun point => SigningSecurityProof.liftFree (prfValue seeds point)) P top tree)).run
            ((cache, fullTable omega), count) =
      (simulateQ LeanXmss.HashSpec.randomOracle
        (referenceTree (m := OracleComp LeanXmss.HashSpec) (fun oa => oa)
          (fun point => pure (prfSum omega point)) P top tree)).run
            (fun input => cache (.hash input)) := by
  rw [signing_tree_run_full prims seeds pairKeys hinj, Functor.map_map]
  have h := StateMap.simulateQ (fixedForestImpl_hashMap omega)
    (forestTree P top tree) (cache, count)
  rw [prescribed_forestTree] at h
  exact h.symm

/-- The initial top tree of the actual signing execution has the programmed
row law, with its complete hash cache available to later computations. -/
theorem signing_top_tree_programmed
    (hinj : Function.Injective (slotInput seeds pairKeys))
    (omega : Slot C → LeanXmss.HashOutput) (count : ℕ)
    (P : XmssSecurity.PublicParameter) :
    𝒟[Prod.map id (signingHashState (C := C)) <$>
      (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
        (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
          (fun point => SigningSecurityProof.liftFree (prfValue seeds point)) P emptyTop .top)).run
            ((∅, fullTable omega), count)] =
    𝒟[do
      let rows ← programmedTopRows P
        (fun b chain => prfSum omega (.chain LeanXmss.topLayer (topKey b) chain (digit 0)))
          3 topRowOrder ∅
      (simulateQ LeanXmss.HashSpec.randomOracle
        (topTreeAfterRows P (rows.1.map
          (fun values : Vector XmssSecurity.Digest 4 => bitsOfDigest values.back)))).run rows.2] := by
  rw [signing_tree_hash_projection prims seeds pairKeys hinj]
  exact referenceTopTree_programmed P (fun point => prfSum omega point)

/-- A top chain in the actual counted signing world, with its PRF start and
its ordinary hash cache, is the programmed chain from the leanVM coupling. -/
theorem signing_top_chain_programmed
    (hinj : Function.Injective (slotInput seeds pairKeys))
    (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (P : XmssSecurity.PublicParameter) (b : XmssSecurity.TopIndex)
    (chain : XmssSecurity.ChainIndex) (steps count : ℕ)
    (hsteps : steps ≤ XmssSecurity.chainLength - 1)
    (hfresh : ∀ step : XmssSecurity.ChainStep, ∀ input,
      XmssSecurity.AtHashAddress P (XmssSecurity.ChainKey.chainDomain (.inr b) chain step) input →
        cache (.hash input) = none) :
    𝒟[Prod.map id (signingHashState (C := C)) <$>
      (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
        (SigningSecurityProof.liftFree (do
          let start ← prfValue seeds (.chain LeanXmss.topLayer (XmssSecurity.Bridge.topKey b)
            chain ⟨0, by decide⟩)
          tweakable (LeanXmss.Concrete.chainWalk P LeanXmss.topLayer
            (XmssSecurity.Bridge.topKey b) chain 0 steps start)))).run
          ((cache, fullTable omega), count)] =
    𝒟[(fun r : Vector XmssSecurity.Digest (steps + 1) × QueryCache XmssSecurity.HashSpec =>
      (r.1.back, r.2)) <$>
      XmssSecurity.programmedChainTrajectory P (.inr b) chain 0 steps
        (prfSum omega (.chain LeanXmss.topLayer (XmssSecurity.Bridge.topKey b) chain ⟨0, by decide⟩))
        (fun input => cache (.hash input))] := by
  rw [SeedHitProof.simulateQ_split_liftFree, simulateQ_bind,
    SeedHitProof.freeRo_prfValue prims seeds pairKeys hinj, StateT.run_bind,
    prfC_run_full, pure_bind, SeedHitProof.freeRo_tweakable]
  rw [← signing_hash_projection]
  exact top_chain_programmed P b chain steps _ _ hsteps hfresh

/-- The commitment-generation job of the actual signing world, after slot
presampling. This includes every PRF term and the final hash in the count. -/
theorem signing_commitment_run_full
    (hinj : Function.Injective (slotInput seeds pairKeys))
    (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex) (count : ℕ) :
    (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
      (SigningSecurityProof.liftFree (referenceJob tweakable (prfValue seeds) P
        ⟨.commitment e, [.randomizer LeanXmss.bottomLayer e]⟩))).run
          ((cache, fullTable omega), count) =
      (fun r => (bitsOfDigest (LeanXmss.truncateHash r.1),
        (r.2, fullTable omega), count + C.terms.length + 1)) <$>
      (((Query C →ₒ LeanXmss.HashOutput).randomOracle
        (.hash (commitmentInput P e (prfSum omega (.randomizer LeanXmss.bottomLayer e))))).run cache) := by
  rw [SeedHitProof.simulateQ_split_liftFree]
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, bind_pure_comp,
    map_bind, pure_bind, List.getD_cons_zero, simulateQ_bind, simulateQ_map,
    SeedHitProof.freeRo_prfValue prims seeds pairKeys hinj, StateT.run_bind,
    prfC_run_full, simulateQ_pure, StateT.run_map, StateT.run_pure, map_pure, pure_bind]
  rw [SeedHitProof.freeRo_tweakable]
  simp [LeanXmss.Concrete.oracleHash, SeedHitProof.hashC, SeedHitProof.countStep,
    onCache_run, Functor.map_map, Function.comp_def]

/-- Presampling makes an honest share evaluation deterministic without
removing any of its PRF or mask calls from the counted signing world. -/
theorem evalC_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (i : C.Party) (J : C.Quorum) (point : Point) (message : LeanXmss.Message) (count : ℕ) :
    (SeedHitProof.evalC i J point message).run ((cache, fullTable omega), count) =
      pure ((show LeanXmss.Digest from evalSum omega i J point message),
        (cache, fullTable omega), count + (C.terms.filter (· ∈ L J i)).length +
          (C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i)).length) := by
  simp only [SeedHitProof.evalC, StateT.run_bind]
  rw [mapM_counted_constant _ _
    (fun term => LeanXmss.truncateHash (omega (.inl (term, point)))) _ (fun term _ count => by
      rw [StateT.run_map, slotC_run_full, map_pure])]
  simp only [pure_bind]
  rw [mapM_counted_constant _ _
    (fun j => if h : j = i then 0 else LeanXmss.truncateHash
      (omega (.inr (C.pairOf i j (Ne.symm h), point, message, J)))) _ (fun j hj count => by
      have hji : j ≠ i := (of_decide_eq_true (List.mem_filter.mp hj).2).2
      simp only [dif_neg hji, StateT.run_map, slotC_run_full, map_pure])]
  simp only [pure_bind, StateT.run_pure]
  congr 2
  change TprfCorrectnessProof.toXor _ = _
  rw [toXor_foldl_id, List.map_append, List.sum_append, List.map_map, List.map_map,
    show TprfCorrectnessProof.toXor (0 : LeanXmss.Digest) = 0 from rfl, zero_add, evalSum]
  rw [← sum_terms_filter (L J i), ← sum_parties_filter (fun j => j ∈ J.1 ∧ j ≠ i)]
  congr 3

theorem signing_eval_run_full
    (hinj : Function.Injective (slotInput seeds pairKeys))
    (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (P : LeanXmss.PublicParameter) (i : C.Party) (J : C.Quorum) (point : Point)
    (message : LeanXmss.Message) (count : ℕ) :
    (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
      (SigningSecurityProof.liftFree (eval (dealtKeys P seeds pairKeys i) i J point message))).run
        ((cache, fullTable omega), count) =
      pure ((show LeanXmss.Digest from evalSum omega i J point message),
        (cache, fullTable omega), count + (C.terms.filter (· ∈ L J i)).length +
          (C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i)).length) := by
  rw [SeedHitProof.simulateQ_split_liftFree,
    SeedHitProof.freeRo_eval prims seeds pairKeys hinj, evalC_run_full]

theorem round1C_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (keys : C.Party → Keys C) (P : LeanXmss.PublicParameter) (top : TopTree)
    (st : TsigState C) (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (count : ℕ)
    (hi : i ∉ st.corrupt) (hJ : i ∈ J.1) (hbound : breaksOneMessagePerKey st e message = false) :
    (((tsigOracles (fun oa => SeedHitProof.liftC prims oa)
      (SeedHitProof.dealtC keys P top) (.round1 i J e message)).run st).run
        ((cache, fullTable omega), count)) =
      pure ((some (show LeanXmss.Digest from
          evalSum omega i J (.randomizer LeanXmss.bottomLayer e) message),
        { st with bound := Function.update st.bound e (some message) }),
        (cache, fullTable omega), count + (C.terms.filter (· ∈ L J i)).length +
          (C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i)).length) := by
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind, hi, hJ, hbound,
    not_true_eq_false, Bool.false_eq_true, or_self, if_false, StateT.run_set,
    StateT.run_map, StateT.run_monadLift, monadLift_self, SeedHitProof.dealtC,
    evalC_run_full, StateT.run_pure, map_pure]
  rfl

theorem sequenceFin_counted_constant {σ α : Type} {n : ℕ}
    (f : Fin n → StateT (σ × ℕ) ProbComp α) (value : Fin n → α)
    (cost : Fin n → ℕ) (state : σ)
    (h : ∀ i count, (f i).run (state, count) = pure (value i, state, count + cost i))
    (count : ℕ) :
    (LeanXmss.Concrete.sequenceFin f).run (state, count) =
      pure (value, state, count + ∑ i, cost i) := by
  induction n generalizing count with
  | zero =>
    simp only [LeanXmss.Concrete.sequenceFin, StateT.run_pure, Fin.sum_univ_zero, Nat.add_zero]
    congr 2
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [LeanXmss.Concrete.sequenceFin, StateT.run_bind, h, pure_bind]
    rw [ih (fun i => f i.succ) (fun i => value i.succ) (fun i => cost i.succ)
      (fun i count => h i.succ count)]
    simp only [pure_bind, StateT.run_pure, Fin.sum_univ_succ, Nat.add_assoc]
    congr 2
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

def round2ShareValues (omega : Slot C → LeanXmss.HashOutput)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (encoding : LeanXmss.Encoding) : LeanXmss.ChainIndex → Option LeanXmss.Digest := fun chain =>
  if (encoding chain).val < LeanXmss.chainLength - 1 then
    some (show LeanXmss.Digest from evalSum omega i J
      (.chain LeanXmss.bottomLayer e chain (encoding chain)) message) else none

def round2ShareCost (i : C.Party) (J : C.Quorum) (encoding : LeanXmss.Encoding) : ℕ :=
  ∑ chain, if (encoding chain).val < LeanXmss.chainLength - 1 then
    (C.terms.filter (· ∈ L J i)).length +
      (C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i)).length else 0

/-- The actual round-2 chain replies depend only on the selected coordinates.
Every internal PRF/mask read is retained in the original cost. -/
theorem round2Shares_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (encoding : LeanXmss.Encoding) (count : ℕ) :
    (LeanXmss.Concrete.sequenceFin fun chain =>
      if (encoding chain).val < LeanXmss.chainLength - 1 then
        some <$> SeedHitProof.evalC i J (.chain LeanXmss.bottomLayer e chain (encoding chain)) message
      else pure none).run ((cache, fullTable omega), count) =
      pure (round2ShareValues omega i J e message encoding,
        (cache, fullTable omega), count + round2ShareCost i J encoding) := by
  apply sequenceFin_counted_constant
  intro chain count
  by_cases hc : (encoding chain).val < LeanXmss.chainLength - 1
  · simp only [hc, if_true, StateT.run_map, evalC_run_full, map_pure,
      round2ShareValues, Nat.add_assoc]
  · simp only [hc, if_false, StateT.run_pure, round2ShareValues, Nat.add_zero]

/-- The hash-only honest interpreter does not modify the presampled slot table. -/
theorem liftC_slots {α : Type} (source : OracleComp (RoSpec C) α)
    (state : SeedHitProof.WState C) :
    ∀ result ∈ support ((SeedHitProof.liftC prims source).run state),
      result.2.1.2 = state.1.2 := by
  apply SeedHitProof.support_simulateQ_inv (SeedHitProof.roC prims)
    (fun s => s.1.2 = state.1.2) _ source state rfl
  intro input st hs result hr
  simp only [SeedHitProof.roC, SeedHitProof.countStep, TprfSecurityProof.onCache,
    StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨first, hf, rfl⟩ := hr
  obtain ⟨second, _, rfl⟩ := hf
  exact hs

/-- The complete round-2 codeword search and returned shares, on the actual
slot interpreter. The search remains probabilistic and every source call is
counted; only its subsequent share evaluations become table observations. -/
theorem signRound2C_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (i : C.Party) (J : C.Quorum) (P : LeanXmss.PublicParameter) (commitment : LeanXmss.Digest)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest)
    (count : ℕ) :
    (signRound2With (fun oa => SeedHitProof.liftC prims oa)
      (fun point => SeedHitProof.evalC i J point message) P J commitment e message parts).run
        ((cache, fullTable omega), count) = (do
      let result ← (SeedHitProof.liftC prims
        (signCodeword P commitment e message (combine J parts))).run ((cache, fullTable omega), count)
      match result.1 with
      | none => pure (none, result.2)
      | some (_, encoding) => pure (some (round2ShareValues omega i J e message encoding),
          result.2.1, result.2.2 + round2ShareCost i J encoding)) := by
  simp only [signRound2With, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨result, ⟨cache', slots'⟩, count'⟩ hr
  have hs := liftC_slots prims (signCodeword P commitment e message (combine J parts))
    ((cache, fullTable omega), count) _ hr
  dsimp only at hs
  subst slots'
  cases result with
  | none => rfl
  | some selected =>
    obtain ⟨randomness, encoding⟩ := selected
    dsimp only
    rw [StateT.run_bind]
    rw [round2Shares_run_full]
    simp only [pure_bind, StateT.run_pure]

def round2ReplyRecords (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (encoding : LeanXmss.Encoding)
    (values : LeanXmss.ChainIndex → Option LeanXmss.Digest) : List (EvalRecord C) :=
  (List.finRange LeanXmss.numChains).filterMap fun chain =>
    (values chain).map fun answer =>
      ⟨i, J, .chain LeanXmss.bottomLayer e chain (encoding chain), message,
        TprfCorrectnessProof.toXor answer⟩

theorem mem_round2ReplyRecords (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (encoding : LeanXmss.Encoding)
    (values : LeanXmss.ChainIndex → Option LeanXmss.Digest) (record : EvalRecord C)
    (hr : record ∈ round2ReplyRecords i J e message encoding values) :
    ∃ chain answer, values chain = some answer ∧ record =
      ⟨i, J, .chain LeanXmss.bottomLayer e chain (encoding chain), message,
        TprfCorrectnessProof.toXor answer⟩ := by
  obtain ⟨chain, _, hr⟩ := List.mem_filterMap.mp hr
  cases hv : values chain with
  | none => simp [hv] at hr
  | some answer =>
    simp only [hv, Option.map_some, Option.some.injEq] at hr
    exact ⟨chain, answer, hv, hr.symm⟩

/-- The actual completed chain-reply packet gives valid Eval records for its
selected coordinates, including omission of the terminal digit. -/
theorem round2ReplyRecords_consistent (omega : Slot C → LeanXmss.HashOutput)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (encoding : LeanXmss.Encoding) :
    ∀ record ∈ round2ReplyRecords i J e message encoding
      (round2ShareValues omega i J e message encoding),
      evalSum omega record.i record.J record.x record.ec = record.answer := by
  intro record hr
  obtain ⟨chain, answer, hv, rfl⟩ := mem_round2ReplyRecords i J e message encoding _ record hr
  simp only [round2ShareValues] at hv
  split at hv
  · cases Option.some.inj hv
    rfl
  · cases hv

/-- Codeword annotations identify coordinates; the release-ledger inclusion
below does not assume their correctness. A source coupling must separately
identify each annotation with the codeword actually used by that response. -/
def signingChainRecords
    (encodingAt : (LocalSpec C + TsigSpec C).Domain → LeanXmss.Encoding)
    (log : SigningLog C) : List (EvalRecord C) :=
  log.flatMap fun entry => match entry with
    | ⟨.inr (.round2 i J e message parts), some values⟩ =>
      round2ReplyRecords i J e message (encodingAt (.inr (.round2 i J e message parts))) values
    | _ => []

theorem signingChainRecords_released
    (encodingAt : (LocalSpec C + TsigSpec C).Domain → LeanXmss.Encoding)
    (log : SigningLog C) (record : EvalRecord C)
    (hr : record ∈ signingChainRecords encodingAt log)
    (e : LeanXmss.KeyIndex) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (hx : record.x = .chain LeanXmss.bottomLayer e chain digit) :
    (e, record.ec, record.i) ∈ releasedOfSigningLog log := by
  obtain ⟨⟨input, output⟩, hmem, hr⟩ := List.mem_flatMap.mp hr
  cases input with
  | inl input => simp [signingChainRecords] at hr
  | inr input =>
    cases input <;> try simp at hr
    rename_i i J key message parts
    cases output with
    | none => simp at hr
    | some values =>
      obtain ⟨selectedChain, answer, _, rfl⟩ := mem_round2ReplyRecords i J key message _ values record hr
      have he : key = e := by cases hx; rfl
      subst key
      exact successfulRound2_mem_released log i J e message parts values hmem

/-- The actual release ledger bounds the queriers of each individual chain
coordinate. It does not release other coordinates merely because a key has
reached threshold. -/
theorem signingChainRecords_queriers_subset
    (encodingAt : (LocalSpec C + TsigSpec C).Domain → LeanXmss.Encoding)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (r : α × TsigState C × SigningLog C)
    (hr : r ∈ support ((simulateQ (signingLoggedOracles dealt) source).run (SigningCoreProof.tsigInit, [])))
    (e : LeanXmss.KeyIndex) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (message : LeanXmss.Message) :
    r.2.1.corrupt ∪ recordQueriers (signingChainRecords encodingAt r.2.2)
      (.chain LeanXmss.bottomLayer e chain digit) message ⊆ signersAt r.2.1 e message := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ hi
  · simp only [recordQueriers, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hi
    obtain ⟨record, ⟨hm, hx, hmessage⟩, rfl⟩ := hi
    have hrel := signingChainRecords_released encodingAt r.2.2 record hm e chain digit hx
    rw [← signingLoggedOracles_released dealt source r hr, hmessage] at hrel
    apply Finset.mem_union_right
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
    exact ⟨(e, message, record.i), ⟨hrel, by simp⟩, rfl⟩

section Round2Receipts

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Proof-only instrumentation retains the actual search result before any
chain shares are evaluated. It makes no additional oracle queries. -/
def signRound2WithSelection
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (part : Point → m LeanXmss.Digest)
    (P : LeanXmss.PublicParameter) (J : C.Quorum) (commitment : LeanXmss.Digest)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest) :
    m (Option ((LeanXmss.Randomness × LeanXmss.Encoding) × (LeanXmss.ChainIndex → Option LeanXmss.Digest))) := do
  let some (randomness, encoding) ← lift (signCodeword P commitment e message (combine J parts))
    | pure none
  let values ← LeanXmss.Concrete.sequenceFin fun chain =>
    if (encoding chain).val < LeanXmss.chainLength - 1 then
      some <$> part (.chain LeanXmss.bottomLayer e chain (encoding chain)) else pure none
  pure (some ((randomness, encoding), values))

theorem signRound2WithSelection_forget
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (part : Point → m LeanXmss.Digest)
    (P : LeanXmss.PublicParameter) (J : C.Quorum) (commitment : LeanXmss.Digest)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest) :
    Option.map Prod.snd <$> signRound2WithSelection lift part P J commitment e message parts =
      signRound2With lift part P J commitment e message parts := by
  unfold signRound2WithSelection signRound2With
  rw [map_bind]
  congr 1
  funext selected
  cases selected with
  | none => simp
  | some selected =>
    obtain ⟨randomness, encoding⟩ := selected
    simp only [map_bind, map_pure, Option.map_some]

structure Round2Receipt (C : Committee) where
  party : C.Party
  quorum : C.Quorum
  key : LeanXmss.KeyIndex
  message : LeanXmss.Message
  randomness : LeanXmss.Randomness
  encoding : LeanXmss.Encoding
  candidate : LeanXmss.Digest
  commitment : LeanXmss.Digest
  values : LeanXmss.ChainIndex → Option LeanXmss.Digest

def Round2Receipt.records (receipt : Round2Receipt C) : List (EvalRecord C) :=
  round2ReplyRecords receipt.party receipt.quorum receipt.key receipt.message receipt.encoding receipt.values

/-- The full handler records a receipt only after success. Failed attempts
retain their original tree, own-share and search effects. -/
def round2WithReceipt
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (dealt : Dealt C m)
    (st : TsigState C) (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest) :
    m (((Option (LeanXmss.ChainIndex → Option LeanXmss.Digest)) × TsigState C) ×
      Option (Round2Receipt C)) := do
  if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then
    pure ((none, st), none)
  else
    let some tree ← dealt.bottom (treeOf e) | pure ((none, st), none)
    let own ← dealt.part i J (.randomizer LeanXmss.bottomLayer e) message
    let some ((randomness, encoding), values) ← signRound2WithSelection lift
      (fun point => dealt.part i J point message) dealt.parameter J (tree.commitment e)
      e message (Function.update parts i own) | pure ((none, st), none)
    pure ((some values, { st with released := st.released ++ [(e, message, i)] }),
      some ⟨i, J, e, message, randomness, encoding,
        combine J (Function.update parts i own), tree.commitment e, values⟩)

theorem round2WithReceipt_forget
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (dealt : Dealt C m)
    (st : TsigState C) (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest) :
    Prod.fst <$> round2WithReceipt lift dealt st i J e message parts =
      (tsigOracles lift dealt (.round2 i J e message parts)).run st := by
  have hl {β : Type} (oa : m β) (state : TsigState C) :
      (liftM oa : StateT (TsigState C) m β).run state = (fun a => (a, state)) <$> oa := by
    simp [StateT.run_monadLift]
  unfold round2WithReceipt
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hguard
  · simp only [StateT.run_pure, map_pure]
    rfl
  · simp only [map_bind, StateT.run_bind, hl, bind_map_left]
    congr 1
    funext tree
    cases tree with
    | none => simp; rfl
    | some tree =>
      simp only [map_bind, StateT.run_bind, hl, bind_map_left]
      congr 1
      funext own
      rw [← signRound2WithSelection_forget]
      simp only [map_bind, bind_map_left]
      congr 1
      funext selected
      cases selected <;> simp [StateT.run_bind, StateT.run_set, StateT.run_pure] <;> rfl

end Round2Receipts

def Round2Receipt.release (receipt : Round2Receipt C) :
    LeanXmss.KeyIndex × LeanXmss.Message × C.Party :=
  (receipt.key, receipt.message, receipt.party)

theorem round2WithReceipt_released {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp spec α)
    (dealt : Dealt C (OracleComp spec)) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (parts : C.Party → LeanXmss.Digest)
    (result : (Option (LeanXmss.ChainIndex → Option LeanXmss.Digest) × TsigState C) ×
      Option (Round2Receipt C))
    (hr : result ∈ support (round2WithReceipt lift dealt st i J e message parts)) :
    result.1.2.released = st.released ++ result.2.toList.map Round2Receipt.release := by
  unfold round2WithReceipt at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst result
    simp
  · simp only [mem_support_bind_iff] at hr
    obtain ⟨tree, _, hr⟩ := hr
    cases tree with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst result
      simp
    | some tree =>
      simp only [mem_support_bind_iff] at hr
      obtain ⟨own, _, selected, _, hr⟩ := hr
      cases selected with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst result
        simp
      | some selected =>
        obtain ⟨⟨randomness, encoding⟩, values⟩ := selected
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst result
        rfl

/-- Receipt values are computed at the very selected trial, with the original
codeword-search distribution and the exact subsequent share cost. -/
theorem signRound2Selection_run_full (omega : Slot C → LeanXmss.HashOutput) (cache : HashCache C)
    (i : C.Party) (J : C.Quorum) (P : LeanXmss.PublicParameter) (commitment : LeanXmss.Digest)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest)
    (count : ℕ) :
    (signRound2WithSelection (fun oa => SeedHitProof.liftC prims oa)
      (fun point => SeedHitProof.evalC i J point message) P J commitment e message parts).run
        ((cache, fullTable omega), count) = (do
      let result ← (SeedHitProof.liftC prims
        (signCodeword P commitment e message (combine J parts))).run ((cache, fullTable omega), count)
      match result.1 with
      | none => pure (none, result.2)
      | some (randomness, encoding) => pure (some ((randomness, encoding), round2ShareValues omega i J e message encoding),
          result.2.1, result.2.2 + round2ShareCost i J encoding)) := by
  simp only [signRound2WithSelection, StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨result, ⟨cache', slots'⟩, count'⟩ hr
  have hs := liftC_slots prims (signCodeword P commitment e message (combine J parts))
    ((cache, fullTable omega), count) _ hr
  dsimp only at hs
  subst slots'
  cases result with
  | none => rfl
  | some selected =>
    obtain ⟨randomness, encoding⟩ := selected
    dsimp only
    rw [StateT.run_bind, round2Shares_run_full]
    simp only [pure_bind, StateT.run_pure]

def signingWithReceipt (dealt : Dealt C (OracleComp (WorldSpec C))) (st : TsigState C) :
    (input : (LocalSpec C + TsigSpec C).Domain) →
      OracleComp (WorldSpec C) (((LocalSpec C + TsigSpec C).Range input × TsigState C) ×
        Option (Round2Receipt C))
  | .inr (.round2 i J e message parts) =>
    round2WithReceipt (fun oa => SigningCoreProof.honestLift oa) dealt st i J e message parts
  | input => (fun result => (result, none)) <$>
    (SigningCoreProof.gameOracles dealt input).run st

theorem signingWithReceipt_forget (dealt : Dealt C (OracleComp (WorldSpec C)))
    (st : TsigState C) (input : (LocalSpec C + TsigSpec C).Domain) :
    Prod.fst <$> signingWithReceipt dealt st input =
      (SigningCoreProof.gameOracles dealt input).run st := by
  cases input with
  | inl input => simp [signingWithReceipt, Functor.map_map]
  | inr input =>
    cases input <;> try simp [signingWithReceipt, Functor.map_map]
    exact round2WithReceipt_forget (fun oa => SigningCoreProof.honestLift oa) dealt _ _ _ _ _ _

def signingReceiptOracles (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT (TsigState C × List (Round2Receipt C)) (OracleComp (WorldSpec C))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1.1, (result.1.2, state.2 ++ result.2.toList))) <$>
      signingWithReceipt dealt state.1 input

/-- Erasure holds for the entire adaptive forger, before any random-oracle
semantics are chosen. Thus the original world trace and budget are preserved. -/
theorem signingReceiptOracles_forget (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C)
    (receipts : List (Round2Receipt C)) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (signingReceiptOracles dealt) source).run (st, receipts) =
      (simulateQ (SigningCoreProof.gameOracles dealt) source).run st := by
  apply SigningCoreProof.simulateQ_run_forget
  intro input state log
  simp only [signingReceiptOracles, StateT.run_mk, Functor.map_map, Function.comp_def]
  exact signingWithReceipt_forget dealt state input

theorem signingWithReceipt_released (dealt : Dealt C (OracleComp (WorldSpec C)))
    (st : TsigState C) (input : (LocalSpec C + TsigSpec C).Domain)
    (result : ((LocalSpec C + TsigSpec C).Range input × TsigState C) × Option (Round2Receipt C))
    (hr : result ∈ support (signingWithReceipt dealt st input)) :
    result.1.2.released = st.released ++ result.2.toList.map Round2Receipt.release := by
  cases input with
  | inl input =>
    simp only [signingWithReceipt, support_map, Set.mem_image] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    change z ∈ support ((fun answer => (answer, st)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query input))) at hz
    obtain ⟨answer, _, rfl⟩ := (by simpa only [support_map, Set.mem_image] using hz)
    simp
  | inr input =>
    cases input with
    | round2 i J e message parts =>
      exact round2WithReceipt_released _ dealt st i J e message parts result hr
    | corrupt i =>
      simp only [signingWithReceipt, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      simpa [releaseStep] using tsigOracles_releaseStep
        (fun oa => SigningCoreProof.honestLift oa) dealt (.corrupt i) st z hz
    | tree b =>
      simp only [signingWithReceipt, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      simpa [releaseStep] using tsigOracles_releaseStep
        (fun oa => SigningCoreProof.honestLift oa) dealt (.tree b) st z hz
    | round1 i J e message =>
      simp only [signingWithReceipt, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      simpa [releaseStep] using tsigOracles_releaseStep
        (fun oa => SigningCoreProof.honestLift oa) dealt (.round1 i J e message) st z hz

/-- The causal receipts reconstruct the actual release ledger exactly. -/
theorem signingReceiptOracles_released (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (signingReceiptOracles dealt) source).run (SigningCoreProof.tsigInit, [])),
      r.2.1.released = r.2.2.map Round2Receipt.release := by
  apply SeedHitProof.support_simulateQ_inv (signingReceiptOracles dealt)
    (fun state => state.1.released = state.2.map Round2Receipt.release) _ source _ rfl
  intro input state hs result hr
  simp only [signingReceiptOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  simpa only [List.map_append, ← hs] using signingWithReceipt_released dealt state.1 input out hout

theorem signingReceiptOracles_releasedBound (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (r : α × TsigState C × List (Round2Receipt C))
    (hr : r ∈ support ((simulateQ (signingReceiptOracles dealt) source).run (SigningCoreProof.tsigInit, []))) :
    ReleasedBound r.2.1 := by
  have hg : (r.1, r.2.1) ∈ support
      ((simulateQ (SigningCoreProof.gameOracles dealt) source).run SigningCoreProof.tsigInit) := by
    rw [← signingReceiptOracles_forget dealt source SigningCoreProof.tsigInit [], support_map]
    exact ⟨r, hr, rfl⟩
  rw [← signingLoggedOracles_forget dealt source SigningCoreProof.tsigInit [], support_map] at hg
  obtain ⟨logged, hlogged, heq⟩ := hg
  have hb := signingLoggedOracles_releasedBound dealt source logged hlogged
  have hs : logged.2.1 = r.2.1 := congrArg Prod.snd heq
  rwa [hs] at hb

theorem signingReceiptOracles_receipt_bound (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (r : α × TsigState C × List (Round2Receipt C))
    (hr : r ∈ support ((simulateQ (signingReceiptOracles dealt) source).run (SigningCoreProof.tsigInit, [])))
    (receipt : Round2Receipt C) (hreceipt : receipt ∈ r.2.2) :
    r.2.1.bound receipt.key = some receipt.message ∧
      receipt.party ∈ signersAt r.2.1 receipt.key receipt.message := by
  have hmem : receipt.release ∈ r.2.1.released := by
    rw [signingReceiptOracles_released dealt source r hr]
    exact List.mem_map.mpr ⟨receipt, hreceipt, rfl⟩
  refine ⟨signingReceiptOracles_releasedBound dealt source r hr _ _ _ hmem, ?_⟩
  apply Finset.mem_union_right
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨receipt.release, ⟨hmem, by simp [Round2Receipt.release]⟩, rfl⟩

def receiptFlag (x : SigningSecurityProof.Keys3 C) (st : TsigState C) (flag : Bool) :
    (LocalSpec C + TsigSpec C).Domain → Bool
  | .inl input => flag || SigningCoreProof.hiddenHit x st.corrupt input
  | .inr _ => flag

def flaggedReceiptOracles (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT ((TsigState C × Bool) × List (Round2Receipt C)) (OracleComp (WorldSpec C))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1.1,
      ((result.1.2, receiptFlag x state.1.1 state.1.2 input), state.2 ++ result.2.toList))) <$>
      signingWithReceipt dealt state.1.1 input

theorem flaggedReceiptOracles_step_forget (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (input : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C) (flag : Bool)
    (receipts : List (Round2Receipt C)) :
    (fun result => (result.1, result.2.1)) <$>
      (flaggedReceiptOracles x dealt input).run ((st, flag), receipts) =
      (SigningCoreProof.flaggedOracles x dealt input).run (st, flag) := by
  have h := congrArg (fun run => (fun result =>
    (result.1, (result.2, receiptFlag x st flag input))) <$> run)
      (signingWithReceipt_forget dealt st input)
  simp only [Functor.map_map, Function.comp_def] at h
  simp only [flaggedReceiptOracles, StateT.run_mk, Functor.map_map, Function.comp_def]
  rw [h]
  cases input <;> simp [SigningCoreProof.flaggedOracles, SigningCoreProof.gameOracles,
    receiptFlag, QueryImpl.add, Functor.map_map, StateT.run_monadLift]

theorem flaggedReceiptOracles_forget (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) (flag : Bool)
    (receipts : List (Round2Receipt C)) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (flaggedReceiptOracles x dealt) source).run ((st, flag), receipts) =
      (simulateQ (SigningCoreProof.flaggedOracles x dealt) source).run (st, flag) :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun input state log => flaggedReceiptOracles_step_forget x dealt input state.1 state.2 log)
    source (st, flag) receipts

/-- Public requests and answers are recorded alongside the causal selections.
The instrumentation adds no hash calls and reveals no honest internal reads. -/
def publicReceiptOracles (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT (((TsigState C × Bool) × List (Round2Receipt C)) × SigningLog C)
        (OracleComp (WorldSpec C))) :=
  fun t => StateT.mk fun s =>
    (fun r => (r.1, (r.2, s.2.logQuery t r.1))) <$>
      (flaggedReceiptOracles x dealt t).run s.1

theorem publicReceiptOracles_forget_log (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (state : (TsigState C × Bool) × List (Round2Receipt C)) (log : SigningLog C) :
    (fun r => (r.1, r.2.1)) <$>
      (simulateQ (publicReceiptOracles x dealt) oa).run (state, log) =
      (simulateQ (flaggedReceiptOracles x dealt) oa).run state :=
  SigningCoreProof.simulateQ_run_forget _ _
    (fun _ _ _ => by simp [publicReceiptOracles, Functor.map_map]) _ _ _

theorem publicReceiptOracles_forget_receipts (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (state : (TsigState C × Bool) × List (Round2Receipt C)) (log : SigningLog C) :
    (fun r => (r.1, (r.2.1.1, r.2.2))) <$>
      (simulateQ (publicReceiptOracles x dealt) oa).run (state, log) =
      (simulateQ (flaggedLoggedOracles x dealt) oa).run (state.1, log) := by
  apply map_run_simulateQ_eq_of_query_map_eq (publicReceiptOracles x dealt)
    (flaggedLoggedOracles x dealt) (fun s => (s.1.1, s.2))
  intro t s
  have h := congrArg (fun run => (fun r => (r.1, (r.2, s.2.logQuery t r.1))) <$>
    run) (flaggedReceiptOracles_step_forget x dealt t s.1.1.1 s.1.1.2 s.1.2)
  simpa only [publicReceiptOracles, flaggedLoggedOracles, StateT.run_mk,
    Functor.map_map, Function.comp_def, Prod.map, id_eq, Prod.mk.eta] using h

theorem publicReceiptOracles_public_view (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (r : α × (((TsigState C × Bool) × List (Round2Receipt C)) × SigningLog C))
    (hr : r ∈ support ((simulateQ (publicReceiptOracles x dealt) oa).run
      (((SigningCoreProof.tsigInit, false), []), []))) :
    Round1Bound r.2.1.1.1 r.2.2 ∧
      (r.2.1.1.2 = false → ∀ read ∈ publicSlotReads x r.2.2,
        Revealed r.2.1.1.1.corrupt (slotKey read.1)) := by
  have hs : (r.1, r.2.1.1, r.2.2) ∈ support
      ((simulateQ (flaggedLoggedOracles x dealt) oa).run
        ((SigningCoreProof.tsigInit, false), [])) := by
    rw [← publicReceiptOracles_forget_receipts x dealt oa
      ((SigningCoreProof.tsigInit, false), []), support_map]
    exact ⟨r, hr, rfl⟩
  exact ⟨flaggedLoggedOracles_round1Bound x dealt oa _ hs, fun hf =>
    publicSlotReads_revealed x _ _ (flaggedLoggedOracles_readsRevealed x dealt oa _ hs hf)⟩

def receiptFinalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    OracleComp (WorldSpec C)
      (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) × List (Round2Receipt C)) := do
  let value := fun point => SigningSecurityProof.liftFree (prfValue x.2.1 point)
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
    value x.1 emptyTop .top | pure (((false, false), none), [])
  let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
    (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (flaggedReceiptOracles x dealt)
    (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run ((SigningCoreProof.tsigInit, false), [])
  (fun w => (((w.1, r.2.1.2), some (top, w.2.1, w.2.2)), r.2.2)) <$>
    SigningCoreProof.tsigFinish dealt (r.1, r.2.1.1)

set_option maxRecDepth 100000 in
theorem receiptFinalRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Prod.fst <$> receiptFinalRun A x = SigningDescentProof.finalRun A x := by
  unfold receiptFinalRun SigningDescentProof.finalRun
  rw [map_bind]
  apply bind_congr
  intro topResult
  rcases topResult with _ | (top | bottom)
  · simp
  · simp only [map_bind, Functor.map_map]
    rw [← flaggedReceiptOracles_forget x _ _ SigningCoreProof.tsigInit false [], bind_map_left]
  · simp

def receiptExposedRun (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :=
  (simulateQ (SeedHitProof.withCount (SeedHitProof.signImpl prims)) (receiptFinalRun A x)).run
    ((∅ : HashCache C), 0)

set_option maxRecDepth 100000 in
theorem receiptExposedRun_forget (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    (fun result => (result.1.1, result.2)) <$> receiptExposedRun prims A x =
      SigningDescentProof.exposedRun prims A x := by
  unfold receiptExposedRun SigningDescentProof.exposedRun
  rw [← receiptFinalRun_forget A x, simulateQ_map, StateT.run_map]

def publicReceiptFinalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    OracleComp (WorldSpec C)
      ((((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
        List (Round2Receipt C)) × SigningLog C) := do
  let value := fun point => SigningSecurityProof.liftFree (prfValue x.2.1 point)
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
    value x.1 emptyTop .top | pure ((((false, false), none), []), [])
  let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
    (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (publicReceiptOracles x dealt)
    (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run (((SigningCoreProof.tsigInit, false), []), [])
  (fun w => ((((w.1, r.2.1.1.2), some (top, w.2.1, w.2.2)), r.2.1.2), r.2.2)) <$>
    SigningCoreProof.tsigFinish dealt (r.1, r.2.1.1.1)

set_option maxRecDepth 100000 in
theorem publicReceiptFinalRun_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Prod.fst <$> publicReceiptFinalRun A x = receiptFinalRun A x := by
  unfold publicReceiptFinalRun receiptFinalRun
  rw [map_bind]
  apply bind_congr
  intro topResult
  rcases topResult with _ | (top | bottom)
  · simp
  · simp only [map_bind, Functor.map_map]
    rw [← publicReceiptOracles_forget_log x _ _ ((SigningCoreProof.tsigInit, false), []) [],
      bind_map_left]
  · simp

def publicReceiptExposedRun (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :=
  (simulateQ (SeedHitProof.withCount (SeedHitProof.signImpl prims))
    (publicReceiptFinalRun A x)).run ((∅ : HashCache C), 0)

set_option maxRecDepth 100000 in
theorem publicReceiptExposedRun_forget (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    (fun r => (r.1.1, r.2)) <$> publicReceiptExposedRun prims A x =
      receiptExposedRun prims A x := by
  unfold publicReceiptExposedRun receiptExposedRun
  rw [← publicReceiptFinalRun_forget A x, simulateQ_map, StateT.run_map]

theorem publicReceiptExposedRun_source (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    (fun r => (r.1.1.1, r.2)) <$> publicReceiptExposedRun prims A x =
      SigningDescentProof.exposedRun prims A x := by
  rw [← receiptExposedRun_forget, ← publicReceiptExposedRun_forget, Functor.map_map]

set_option maxRecDepth 100000 in
theorem publicReceiptFinalRun_public_view (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r)
    (hr : r ∈ support (publicReceiptFinalRun A x))
    (top : TopTree) (st : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.1.2 = some (top, st, forgery)) :
    Round1Bound st r.2 ∧
      (r.1.1.1.2 = false → ∀ read ∈ publicSlotReads x r.2,
        Revealed st.corrupt (slotKey read.1)) := by
  unfold publicReceiptFinalRun at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨tree, _, hr⟩ := hr
  rcases tree with _ | (top' | bottom)
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    cases hm
  · simp only [mem_support_bind_iff, support_map] at hr
    obtain ⟨run, hrun, finish, hfinish, rfl⟩ := hr
    have hv := publicReceiptOracles_public_view x _ _ run hrun
    have hstate : finish.2.1 = run.2.1.1.1 := by
      unfold SigningCoreProof.tsigFinish at hfinish
      simp only [mem_support_bind_iff] at hfinish
      obtain ⟨verified, _, hfinish⟩ := hfinish
      split at hfinish
      · simpa using congrArg (fun z => z.2.1) (Set.mem_singleton_iff.mp hfinish)
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
          exists_eq_left] at hfinish
        obtain ⟨honest, _, hfinish⟩ := hfinish
        subst finish
        rfl
    have hs : finish.2.1 = st := by
      exact congrArg (fun v => v.2.1) (Option.some.inj hm)
    simpa only [hstate, ← hs] using hv
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    cases hm

set_option maxRecDepth 100000 in
theorem publicReceiptExposedRun_public_view (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r)
    (hr : r ∈ support (publicReceiptExposedRun prims A x))
    (top : TopTree) (st : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.1.1.2 = some (top, st, forgery)) :
    Round1Bound st r.1.2 ∧
      (r.1.1.1.1.2 = false → ∀ read ∈ publicSlotReads x r.1.2,
        Revealed st.corrupt (slotKey read.1)) := by
  apply publicReceiptFinalRun_public_view A x r.1 _ top st forgery hm
  apply support_simulateQ_run'_subset
    (SeedHitProof.withCount (SeedHitProof.signImpl prims)) (publicReceiptFinalRun A x) ((∅ : HashCache C), 0)
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

set_option maxRecDepth 100000 in
theorem receiptExposedRun_count_le (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    ∀ r ∈ support (receiptExposedRun prims A x), r.2.2 ≤ q := by
  intro result hr
  apply exposedRun_count_le prims A x q hq (result.1.1, result.2)
  rw [← receiptExposedRun_forget prims A x, support_map]
  exact ⟨result, hr, rfl⟩

def signingSlots (s : SeedHitProof.WState C) : SlotCache C := s.1.2

def setSigningSlots (s : SeedHitProof.WState C) (cache : SlotCache C) : SeedHitProof.WState C :=
  ((s.1.1, cache), s.2)

/-- Presampling a slot changes neither the signing result nor its query count.
The continuation may retain all observable state except unused slot entries. -/
def PresampledSigning (slot : Slot C) {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  Presampled signingSlots setSigningSlots slot
    (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa)

theorem presampled_signing_pure (slot : Slot C) {α : Type} (a : α) :
    PresampledSigning prims seeds pairKeys slot (pure a : OracleComp (WorldSpec C) α) := by
  simpa only [PresampledSigning, simulateQ_pure] using
    (presampled_pure (getC := signingSlots) (setC := setSigningSlots) slot a)

theorem presampled_signing_bind (slot : Slot C) {α β : Type}
    (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β)
    (ho : PresampledSigning prims seeds pairKeys slot oa)
    (hf : ∀ a, PresampledSigning prims seeds pairKeys slot (f a)) :
    PresampledSigning prims seeds pairKeys slot (oa >>= f) := by
  unfold PresampledSigning at *
  rw [simulateQ_bind]
  exact presampled_bind slot ho hf

theorem presampled_signing_map (slot : Slot C) {α β : Type}
    (oa : OracleComp (WorldSpec C) α) (f : α → β)
    (ho : PresampledSigning prims seeds pairKeys slot oa) :
    PresampledSigning prims seeds pairKeys slot (f <$> oa) := by
  unfold PresampledSigning at *
  rw [simulateQ_map]
  exact presampled_map slot f ho

theorem presampled_signing_local (slot : Slot C) (t : (LocalSpec C).Domain) :
    Presampled₁ slot (SeedHitProof.routedLocal prims seeds pairKeys t) := by
  rcases t with n | q | y
  · exact presampled_onCache slot _
  · change Presampled₁ slot (if h : ∃ s, slotInput seeds pairKeys s = q then _ else _)
    split_ifs
    · exact presampled_onTable slot (presampled_slotOracle slot _)
    · exact presampled_onCache slot _
  · exact presampled_onCache slot _

theorem presampled_signing_count_step (slot : Slot C) (t : (WorldSpec C).Domain)
    (h : Presampled₁ slot (SeedHitProof.routedImpl prims seeds pairKeys t)) :
    Presampled signingSlots setSigningSlots slot
      (SeedHitProof.splitWorld prims seeds pairKeys t) := by
  exact presampled_transport slot Prod.fst
    (fun _ => SeedHitProof.routedImpl prims seeds pairKeys t)
    (fun p z => (z.1, (z.2, p.2 + SeedHitProof.signCost t)))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => h)

theorem presampled_signing_free (slot : Slot C) {α : Type}
    (oa : OracleComp (RoSpec C) α) :
    PresampledSigning prims seeds pairKeys slot (SigningSecurityProof.liftFree oa) := by
  unfold PresampledSigning SeedHitProof.splitWorld
  rw [SeedHitProof.simulateQ_withCount_liftFree]
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa using presampled_pure (getC := signingSlots)
      (setC := setSigningSlots) slot a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact presampled_bind slot
      (presampled_signing_count_step prims seeds pairKeys slot _
        (presampled_signing_local prims seeds pairKeys slot (.inr t))) ih

theorem presampled_signing_adversary (slot : Slot C) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    PresampledSigning prims seeds pairKeys slot (worldRoles.adversary oa) := by
  unfold PresampledSigning
  rw [SeedHitProof.simulateQ_adversary_split]
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa using presampled_pure (getC := signingSlots)
      (setC := setSigningSlots) slot a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact presampled_bind slot
      (presampled_signing_count_step prims seeds pairKeys slot _
        (presampled_signing_local prims seeds pairKeys slot t)) ih

theorem presampled_signing_simulateState (slot : Slot C) {ι α σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (h : ∀ t s, PresampledSigning prims seeds pairKeys slot ((impl t).run s))
    (oa : OracleComp spec α) (s : σ) :
    PresampledSigning prims seeds pairKeys slot ((simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simpa using presampled_signing_pure prims seeds pairKeys slot (a, s)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    exact presampled_signing_bind prims seeds pairKeys slot _ _ (h t s) (fun r => ih r.1 r.2)

set_option maxRecDepth 100000 in
theorem signing_tsigOracles_free (x : SigningSecurityProof.Keys3 C) (top : TopTree)
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

theorem presampled_signing_flaggedOracles (slot : Slot C)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : TsigState C × Bool) :
    PresampledSigning prims seeds pairKeys slot ((SigningCoreProof.flaggedOracles x
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) t).run s) := by
  cases t with
  | inl t =>
    apply presampled_signing_map
    exact presampled_signing_adversary prims seeds pairKeys slot _
  | inr q =>
    apply presampled_signing_map
    rw [signing_tsigOracles_free]
    exact presampled_signing_free prims seeds pairKeys slot _

set_option maxRecDepth 100000 in
theorem presampled_signing_finish (slot : Slot C)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree) (r : LeanXmss.Forgery × TsigState C) :
    PresampledSigning prims seeds pairKeys slot (SigningCoreProof.tsigFinish
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) r) := by
  rcases r with ⟨forgery, st⟩
  unfold SigningCoreProof.tsigFinish
  apply presampled_signing_bind prims seeds pairKeys slot _ _
    (presampled_signing_free prims seeds pairKeys slot _)
  intro verified
  dsimp only
  split_ifs
  · simpa using presampled_signing_pure prims seeds pairKeys slot (verified && true, st, forgery)
  · apply presampled_signing_bind
    · erw [SigningCacheProof.liftFree_honestSignature]
      exact presampled_signing_free prims seeds pairKeys slot _
    · intro honest
      simpa using presampled_signing_pure prims seeds pairKeys slot
        (verified && decide (honest ≠ some forgery.signature), st, forgery)

set_option maxRecDepth 100000 in
theorem presampled_signing_flaggedAfter (slot : Slot C)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    PresampledSigning prims seeds pairKeys slot (SigningCoreProof.flaggedAfter A x) := by
  unfold SigningCoreProof.flaggedAfter
  dsimp only
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  apply presampled_signing_bind prims seeds pairKeys slot _ _
    (presampled_signing_free prims seeds pairKeys slot _)
  intro output
  rcases output with _ | (top | tree)
  · exact presampled_signing_pure prims seeds pairKeys slot _
  · apply presampled_signing_bind
    · exact presampled_signing_simulateState prims seeds pairKeys slot _
        (presampled_signing_flaggedOracles prims seeds pairKeys slot x top) _ _
    · intro r
      exact presampled_signing_map prims seeds pairKeys slot _ _
        (presampled_signing_finish prims seeds pairKeys slot x top _)
  · exact presampled_signing_pure prims seeds pairKeys slot _

/-- Move an arbitrary finite set of fresh share slots before the signing experiment.
The observation retains the counted budget, not just the Boolean outcome. -/
theorem presample_signing_slots_observe {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (observe : α → HashCache C → ℕ → β)
    (h : ∀ slot, PresampledSigning prims seeds pairKeys slot oa)
    (l : List (Slot C)) (hl : l.Nodup) (p : SeedHitProof.WState C)
    (hp : ∀ s ∈ l, signingSlots p s = none) :
    𝒟[($ᵗ (Slot C → LeanXmss.HashOutput)) >>= fun ω =>
      (fun z => observe z.1 z.2.1.1 z.2.2) <$>
        (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa).run
          (setSigningSlots p (fillSlots ω l (signingSlots p)))] =
    𝒟[(fun z => observe z.1 z.2.1.1 z.2.2) <$>
      (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa).run p] := by
  induction l with
  | nil =>
    simp only [fillSlots]
    exact evalDist_uniform_bind_const (α := Slot C → LeanXmss.HashOutput) _
  | cons s l ih =>
    have hs : s ∉ l := (List.nodup_cons.mp hl).1
    rw [evalDist_bind, ← evalDist_uniformSample_bind_update (D := Slot C)
      (R := LeanXmss.HashOutput) s, ← evalDist_bind]
    simp only [bind_assoc, pure_bind, fillSlots, fillSlots_update _ l _ hs, Function.update_self]
    rw [evalDist_bind_bind_swap]
    rw [← ih (List.nodup_cons.mp hl).2 (fun a ha => hp a (List.mem_cons_of_mem _ ha))]
    refine evalDist_bind_congr' _ fun g => ?_
    have hfresh : signingSlots (setSigningSlots p (fillSlots g l (signingSlots p))) s = none := by
      change fillSlots g l (signingSlots p) s = none
      rw [fillSlots_of_not_mem g l _ hs]
      exact hp s (List.mem_cons_self ..)
    have heq := h s (setSigningSlots p (fillSlots g l (signingSlots p))) hfresh
      (fun z => (pure (observe z.1 z.2.1.1 z.2.2) : ProbComp β))
      (fun a p' _ => evalDist_uniform_bind_const (α := LeanXmss.HashOutput)
        (pure (observe a p'.1.1 p'.2)))
    simp only [map_eq_bind_pure_comp]
    exact heq

theorem presample_signing_slots {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : ∀ slot, PresampledSigning prims seeds pairKeys slot oa)
    (l : List (Slot C)) (hl : l.Nodup) (p : SeedHitProof.WState C)
    (hp : ∀ s ∈ l, signingSlots p s = none) :
    𝒟[($ᵗ (Slot C → LeanXmss.HashOutput)) >>= fun ω =>
      (fun z => (z.1, z.2.2)) <$>
        (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa).run
          (setSigningSlots p (fillSlots ω l (signingSlots p)))] =
    𝒟[(fun z => (z.1, z.2.2)) <$>
      (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa).run p] :=
  presample_signing_slots_observe prims seeds pairKeys oa (fun a _ n => (a, n)) h l hl p hp

/-- The actual flagged signing game can start with every share slot sampled.
This equality includes the final counter and makes no independence claim about
the adversary's subsequent view. -/
theorem flaggedAfter_eq_presampled (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (hc : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    𝒟[runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] =
    𝒟[($ᵗ (Slot C → LeanXmss.HashOutput)) >>= fun ω =>
      (fun z => (z.1, z.2.2)) <$>
        (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
          (SigningCoreProof.flaggedAfter A x)).run ((∅, fullTable ω), 0)] := by
  have hinj : Function.Injective (slotInput x.2.1 x.2.2) := by
    simp only [TprfSecurityProof.KeyCollision, not_or, not_not] at hc
    exact slotInput_injective hc.1 hc.2
  rw [SeedHitProof.runSigningWorld_eq_split prims x.2.1 x.2.2 hinj]
  have h := presample_signing_slots prims x.2.1 x.2.2
    (SigningCoreProof.flaggedAfter A x)
    (fun slot => presampled_signing_flaggedAfter prims x.2.1 x.2.2 slot A x)
    (Finset.univ : Finset (Slot C)).toList (Finset.nodup_toList _) ((∅, ∅), 0)
    (fun _ _ => rfl)
  have hfill : ∀ ω : Slot C → LeanXmss.HashOutput,
      setSigningSlots ((∅, ∅), 0)
        (fillSlots ω (Finset.univ : Finset (Slot C)).toList (signingSlots ((∅, ∅), 0))) =
      ((∅, fullTable ω), 0) := by
    intro ω
    dsimp only [setSigningSlots, signingSlots]
    congr 2
    funext s
    exact fillSlots_of_mem ω _ _ (Finset.mem_toList.mpr (Finset.mem_univ s))
  simpa only [hfill] using h.symm

set_option maxRecDepth 100000 in
/-- Structural elimination for the actual signing program. It lets instrumentation
retain the full query transcript without changing any protocol handler. -/
theorem signing_finalRun_closed
    (P : {α : Type} → OracleComp (WorldSpec C) α → Prop)
    (hpure : ∀ {α : Type} (a : α), P (pure a))
    (hbind : ∀ {α β : Type} (oa : OracleComp (WorldSpec C) α)
      (f : α → OracleComp (WorldSpec C) β), P oa → (∀ a, P (f a)) → P (oa >>= f))
    (hfree : ∀ {α : Type} (oa : OracleComp (RoSpec C) α), P (SigningSecurityProof.liftFree oa))
    (hadv : ∀ {α : Type} (oa : OracleComp (LocalSpec C) α), P (worldRoles.adversary oa))
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    P (SigningDescentProof.finalRun A x) := by
  have hmap : ∀ {α β : Type} (f : α → β) (oa : OracleComp (WorldSpec C) α),
      P oa → P (f <$> oa) := by
    intro α β f oa ho
    rw [← bind_pure_comp]
    exact hbind oa _ ho (fun _ => hpure _)
  have hstate : ∀ {ι α σ : Type} {spec : OracleSpec ι}
      (impl : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
      (oa : OracleComp spec α), (∀ t s, P ((impl t).run s)) → ∀ s, P ((simulateQ impl oa).run s) := by
    intro ι α σ spec impl oa hi s
    induction oa using OracleComp.inductionOn generalizing s with
    | pure a => simpa using hpure (a, s)
    | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      exact hbind _ _ (hi t s) (fun r => ih r.1 r.2)
  have hfinish : ∀ top r, P (SigningCoreProof.tsigFinish
      (dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p))) r) := by
    intro top ⟨forgery, st⟩
    unfold SigningCoreProof.tsigFinish
    apply hbind _ _ (hfree _)
    intro verified
    dsimp only
    split_ifs
    · simpa using hpure (verified && true, st, forgery)
    · apply hbind
      · erw [SigningCacheProof.liftFree_honestSignature]
        exact hfree _
      · intro honest
        simpa using hpure (verified && decide (honest ≠ some forgery.signature), st, forgery)
  unfold SigningDescentProof.finalRun
  dsimp only
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  apply hbind _ _ (hfree _)
  intro output
  rcases output with _ | (top | tree)
  · exact hpure _
  · apply hbind
    · apply hstate
      intro t s
      cases t with
      | inl t => exact hmap _ _ (hadv _)
      | inr q =>
        apply hmap
        rw [signing_tsigOracles_free]
        exact hfree _
    · intro r
      exact hmap _ _ (hfinish top _)
  · exact hpure _

/-- A source-level transcript; the original world still answers every query. -/
def traceWorld : QueryImpl (WorldSpec C)
    (StateT (QueryLog (WorldSpec C)) (OracleComp (WorldSpec C))) :=
  fun t => StateT.mk fun log => (fun answer => (answer, log.logQuery t answer)) <$>
    OracleComp.lift (OracleSpec.query t)

def PresampledSigningTrace (slot : Slot C) {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  ∀ log, PresampledSigning prims seeds pairKeys slot ((simulateQ traceWorld oa).run log)

theorem presampled_signing_trace_pure (slot : Slot C) {α : Type} (a : α) :
    PresampledSigningTrace prims seeds pairKeys slot (pure a : OracleComp (WorldSpec C) α) := by
  intro log
  simpa using presampled_signing_pure prims seeds pairKeys slot (a, log)

theorem presampled_signing_trace_bind (slot : Slot C) {α β : Type}
    (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β)
    (ho : PresampledSigningTrace prims seeds pairKeys slot oa)
    (hf : ∀ a, PresampledSigningTrace prims seeds pairKeys slot (f a)) :
    PresampledSigningTrace prims seeds pairKeys slot (oa >>= f) := by
  intro log
  simp only [simulateQ_bind, StateT.run_bind]
  exact presampled_signing_bind prims seeds pairKeys slot _ _ (ho log) (fun r => hf r.1 r.2)

theorem presampled_signing_trace_local (slot : Slot C) (t : (LocalSpec C).Domain) :
    PresampledSigningTrace prims seeds pairKeys slot (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t))) ∧
      PresampledSigningTrace prims seeds pairKeys slot (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t)))) := by
  have hstep : ∀ (t' : (WorldSpec C).Domain),
      Presampled₁ slot (SeedHitProof.routedImpl prims seeds pairKeys t') →
      PresampledSigningTrace prims seeds pairKeys slot (OracleComp.lift (OracleSpec.query t')) := by
    intro t' ht log
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      traceWorld, StateT.run_mk]
    apply presampled_signing_map
    unfold PresampledSigning
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact presampled_signing_count_step prims seeds pairKeys slot t' ht
  exact ⟨hstep (.inr t) (presampled_signing_local prims seeds pairKeys slot t),
    hstep (.inl (.inl t)) (presampled_signing_local prims seeds pairKeys slot t)⟩

theorem presampled_signing_trace_free (slot : Slot C) {α : Type}
    (oa : OracleComp (RoSpec C) α) :
    PresampledSigningTrace prims seeds pairKeys slot (SigningSecurityProof.liftFree oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa only [SigningSecurityProof.liftFree, liftComp_pure, free_pure] using
      presampled_signing_trace_pure prims seeds pairKeys slot a
  | query_bind t k ih =>
    simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind] at ih ⊢
    apply presampled_signing_trace_bind prims seeds pairKeys slot _ _ ?_ ih
    rw [liftComp_query]
    change PresampledSigningTrace prims seeds pairKeys slot
      (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr t))))
    exact (presampled_signing_trace_local prims seeds pairKeys slot (.inr t)).1

set_option maxRecDepth 100000 in
theorem presampled_signing_trace_adversary (slot : Slot C) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    PresampledSigningTrace prims seeds pairKeys slot (worldRoles.adversary oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [worldRoles, liftComp_pure]
    exact presampled_signing_trace_pure prims seeds pairKeys slot a
  | query_bind t k ih =>
    simp only [worldRoles, liftComp_bind, counted_bind] at ih ⊢
    apply presampled_signing_trace_bind prims seeds pairKeys slot _ _ ?_ ih
    rcases t with n | q | y
    · exact (presampled_signing_trace_local prims seeds pairKeys slot (.inl n)).2
    · exact (presampled_signing_trace_local prims seeds pairKeys slot (.inr (.inl q))).2
    · exact (presampled_signing_trace_local prims seeds pairKeys slot (.inr (.inr y))).2

theorem presampled_signing_trace_finalRun (slot : Slot C)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    PresampledSigningTrace prims seeds pairKeys slot (SigningDescentProof.finalRun A x) :=
  signing_finalRun_closed (fun oa => PresampledSigningTrace prims seeds pairKeys slot oa)
    (presampled_signing_trace_pure prims seeds pairKeys slot)
    (presampled_signing_trace_bind prims seeds pairKeys slot)
    (presampled_signing_trace_free prims seeds pairKeys slot)
    (presampled_signing_trace_adversary prims seeds pairKeys slot) A x

open Classical in
def recordSlot (cache : SlotCache C) (q : Query C) (answer : LeanXmss.HashOutput) : SlotCache C :=
  if h : ∃ s, slotInput seeds pairKeys s = q then cache.cacheQuery h.choose answer else cache

def recordLocalSlots (cache : SlotCache C) :
    (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → SlotCache C
  | .inl _, _ => cache
  | .inr (.inl q), answer => recordSlot seeds pairKeys cache q answer
  | .inr (.inr _), _ => cache

def recordWorldSlots (cache : SlotCache C) :
    (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → SlotCache C
  | .inl (.inl t), answer => recordLocalSlots seeds pairKeys cache t answer
  | .inl (.inr _), _ => cache
  | .inr t, answer => recordLocalSlots seeds pairKeys cache t answer

/-- Only the share slots actually queried belong to the original cache.
Internal PRG reads stay in the separately retained ordinary hash cache. -/
def slotsOfWorldLog (log : QueryLog (WorldSpec C)) : SlotCache C :=
  log.foldl (fun cache entry => recordWorldSlots seeds pairKeys cache entry.1 entry.2) ∅

theorem slotsOfWorldLog_logQuery (log : QueryLog (WorldSpec C))
    (t : (WorldSpec C).Domain) (answer : (WorldSpec C).Range t) :
    slotsOfWorldLog seeds pairKeys (log.logQuery t answer) =
      recordWorldSlots seeds pairKeys (slotsOfWorldLog seeds pairKeys log) t answer := by
  simp [slotsOfWorldLog, QueryLog.logQuery, QueryLog.singleton, List.foldl_append]

theorem slotOracle_result_cache (slot : Slot C) (cache : SlotCache C)
    (r : LeanXmss.HashOutput × SlotCache C) (hr : r ∈ support ((slotOracle slot).run cache)) :
    r.2 = cache.cacheQuery slot r.1 := by
  classical
  cases hc : cache slot with
  | none =>
    rw [QueryImpl.withCaching_run_none _ hc] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    rfl
  | some value =>
    rw [QueryImpl.withCaching_run_some _ hc] at hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    funext s
    by_cases hs : s = slot
    · subst s
      simp [hc]
    · simp [QueryCache.cacheQuery_of_ne _ _ hs]

theorem routedLocal_slots (t : (LocalSpec C).Domain) (p : HashCache C × SlotCache C)
    (r : (LocalSpec C).Range t × (HashCache C × SlotCache C))
    (hr : r ∈ support ((SeedHitProof.routedLocal prims seeds pairKeys t).run p)) :
    r.2.2 = recordLocalSlots seeds pairKeys p.2 t r.1 := by
  rcases p with ⟨cache, slots⟩
  rcases t with n | q | y
  · change r ∈ support ((onCache _).run (cache, slots)) at hr
    rw [onCache_run] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨z, _, rfl⟩ := hr
    rfl
  · change r ∈ support ((if h : ∃ s, slotInput seeds pairKeys s = q then
      onTable (slotOracle h.choose) else onCache _).run (cache, slots)) at hr
    classical
    simp only [recordLocalSlots, recordSlot]
    split_ifs at hr ⊢ with h
    · rw [onTable_run] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      exact slotOracle_result_cache h.choose slots z hz
    · rw [onCache_run] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨z, _, rfl⟩ := hr
      rfl
  · change r ∈ support ((onCache _).run (cache, slots)) at hr
    rw [onCache_run] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨z, _, rfl⟩ := hr
    rfl

def TraceSlotsMatch {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  ∀ log p, signingSlots p = slotsOfWorldLog seeds pairKeys log →
    ∀ r ∈ support ((simulateQ (SeedHitProof.splitWorld prims seeds pairKeys)
      ((simulateQ traceWorld oa).run log)).run p),
      signingSlots r.2 = slotsOfWorldLog seeds pairKeys r.1.2

theorem traceSlotsMatch_pure {α : Type} (a : α) :
    TraceSlotsMatch prims seeds pairKeys (pure a : OracleComp (WorldSpec C) α) := by
  intro log p hp r hr
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst r
  exact hp

theorem traceSlotsMatch_bind {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (f : α → OracleComp (WorldSpec C) β)
    (ho : TraceSlotsMatch prims seeds pairKeys oa)
    (hf : ∀ a, TraceSlotsMatch prims seeds pairKeys (f a)) :
    TraceSlotsMatch prims seeds pairKeys (oa >>= f) := by
  intro log p hp r hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨z, hz, hr⟩ := hr
  exact hf z.1.1 z.1.2 z.2 (ho log p hp z hz) r hr

theorem traceSlotsMatch_local (t : (LocalSpec C).Domain) :
    TraceSlotsMatch prims seeds pairKeys
        (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t))) ∧
      TraceSlotsMatch prims seeds pairKeys
        (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t)))) := by
  have hstep : ∀ t' : (WorldSpec C).Domain,
      (∀ p r, r ∈ support ((SeedHitProof.routedImpl prims seeds pairKeys t').run p) →
        r.2.2 = recordWorldSlots seeds pairKeys p.2 t' r.1) →
      TraceSlotsMatch prims seeds pairKeys (OracleComp.lift (OracleSpec.query t')) := by
    intro t' ht log p hp r hr
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      traceWorld, StateT.run_mk, simulateQ_map, StateT.run_map,
      SeedHitProof.splitWorld, SeedHitProof.withCount, Functor.map_map,
      support_map, Set.mem_image] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    rw [slotsOfWorldLog_logQuery, ← hp]
    exact ht p.1 z hz
  exact ⟨hstep (.inr t) (routedLocal_slots prims seeds pairKeys t),
    hstep (.inl (.inl t)) (routedLocal_slots prims seeds pairKeys t)⟩

theorem signing_free_closed
    (P : {α : Type} → OracleComp (WorldSpec C) α → Prop)
    (hpure : ∀ {α : Type} (a : α), P (pure a))
    (hbind : ∀ {α β : Type} (oa : OracleComp (WorldSpec C) α)
      (f : α → OracleComp (WorldSpec C) β), P oa → (∀ a, P (f a)) → P (oa >>= f))
    (hquery : ∀ t : (LocalSpec C).Domain,
      P (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t))))
    {α : Type} (oa : OracleComp (RoSpec C) α) : P (SigningSecurityProof.liftFree oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [SigningSecurityProof.liftFree, liftComp_pure, free_pure] using hpure a
  | query_bind t k ih =>
    simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind] at ih ⊢
    apply hbind _ _ ?_ ih
    rw [liftComp_query]
    exact hquery (.inr t)

theorem signing_adversary_closed
    (P : {α : Type} → OracleComp (WorldSpec C) α → Prop)
    (hpure : ∀ {α : Type} (a : α), P (pure a))
    (hbind : ∀ {α β : Type} (oa : OracleComp (WorldSpec C) α)
      (f : α → OracleComp (WorldSpec C) β), P oa → (∀ a, P (f a)) → P (oa >>= f))
    (hquery : ∀ t : (LocalSpec C).Domain,
      P (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t)))))
    {α : Type} (oa : OracleComp (LocalSpec C) α) : P (worldRoles.adversary oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [worldRoles, liftComp_pure]
    exact hpure a
  | query_bind t k ih =>
    simp only [worldRoles, liftComp_bind, counted_bind] at ih ⊢
    apply hbind _ _ ?_ ih
    rcases t with n | q | y
    · exact hquery (.inl n)
    · exact hquery (.inr (.inl q))
    · exact hquery (.inr (.inr y))

theorem traceSlotsMatch_finalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    TraceSlotsMatch prims seeds pairKeys (SigningDescentProof.finalRun A x) := by
  apply signing_finalRun_closed (fun oa => TraceSlotsMatch prims seeds pairKeys oa)
    (traceSlotsMatch_pure prims seeds pairKeys) (traceSlotsMatch_bind prims seeds pairKeys)
    ?_ ?_ A x
  · exact signing_free_closed _ (traceSlotsMatch_pure prims seeds pairKeys)
      (traceSlotsMatch_bind prims seeds pairKeys) (fun t => (traceSlotsMatch_local prims seeds pairKeys t).1)
  · exact signing_adversary_closed _ (traceSlotsMatch_pure prims seeds pairKeys)
      (traceSlotsMatch_bind prims seeds pairKeys) (fun t => (traceSlotsMatch_local prims seeds pairKeys t).2)

theorem traceWorld_forget {α : Type} (oa : OracleComp (WorldSpec C) α)
    (log : QueryLog (WorldSpec C)) :
    Prod.fst <$> (simulateQ traceWorld oa).run log = oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, traceWorld, StateT.run_bind, StateT.run_mk,
      map_bind, bind_map_left, ih]

/-- Forget the transcript after running it in any stateful world. -/
theorem run_traceWorld_forget {α σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (oa : OracleComp (WorldSpec C) α) (log : QueryLog (WorldSpec C)) (p : σ) :
    (fun z => (z.1.1, z.2)) <$> (simulateQ impl ((simulateQ traceWorld oa).run log)).run p =
      (simulateQ impl oa).run p := by
  conv_rhs => rw [← traceWorld_forget oa log]
  rw [simulateQ_map, StateT.run_map]

/-- Rebuild precisely the original cache, including absence of unvisited slots. -/
def cacheOfWorldLog (cache : HashCache C) (log : QueryLog (WorldSpec C)) : HashCache C :=
  SeedHitProof.mergeCache seeds pairKeys (cache, slotsOfWorldLog seeds pairKeys log)

/-- The instrumented source program, observed with its reconstructed cache. -/
def traceObserved (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (slots : SlotCache C) : ProbComp (Outcome C) :=
  (fun z => (z.1.1, cacheOfWorldLog x.2.1 x.2.2 z.2.1.1 z.1.2, z.2.2)) <$>
    (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
      ((simulateQ traceWorld (SigningDescentProof.finalRun A x)).run [])).run ((∅, slots), 0)

set_option maxRecDepth 100000 in
theorem traceObserved_empty_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hc : ¬KeyCollision x.2.1 x.2.2) :
    𝒟[traceObserved prims A x ∅] = 𝒟[SigningDescentProof.exposedRun prims A x] := by
  have hinj : Function.Injective (slotInput x.2.1 x.2.2) := by
    simp only [KeyCollision, not_or, not_not] at hc
    exact slotInput_injective hc.1 hc.2
  have hs := StateMap.simulateQ (SeedHitProof.stateMap_withCount _ _ _
    (SeedHitProof.stateMap_routedImpl prims x.2.1 x.2.2 hinj)) (SigningDescentProof.finalRun A x)
    ((∅ : HashCache C), 0)
  simp only [Prod.map, id, splitCache_empty] at hs
  have hm : (fun z => (z.1, SeedHitProof.mergeCache x.2.1 x.2.2 z.2.1, z.2.2)) <$>
      (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
        (SigningDescentProof.finalRun A x)).run ((∅, ∅), 0) =
      SigningDescentProof.exposedRun prims A x := by
    rw [hs, Functor.map_map]
    simp only [Prod.map_fst, Prod.map_snd, id, SeedHitProof.mergeCache_splitCache, Prod.mk.eta]
    exact id_map _
  rw [← hm, ← run_traceWorld_forget _ (SigningDescentProof.finalRun A x) [], Functor.map_map]
  unfold traceObserved
  apply evalDist_ext
  intro output
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  apply probEvent_congr' ?_ rfl
  intro r hr
  have hrSlots := traceSlotsMatch_finalRun prims x.2.1 x.2.2 A x [] ((∅, ∅), 0) rfl r hr
  simp only [cacheOfWorldLog, Function.comp_apply]
  rw [← hrSlots]
  rfl

set_option maxRecDepth 100000 in
/-- Full signing presampling, with the original final cache reconstructed from
the visited slots. All cache-based bad events transport through this equality. -/
theorem exposedRun_eq_presampled (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hc : ¬KeyCollision x.2.1 x.2.2) :
    𝒟[SigningDescentProof.exposedRun prims A x] =
      𝒟[($ᵗ (Slot C → LeanXmss.HashOutput)) >>= fun ω => traceObserved prims A x (fullTable ω)] := by
  have h := presample_signing_slots_observe prims x.2.1 x.2.2
    ((simulateQ traceWorld (SigningDescentProof.finalRun A x)).run [])
    (fun r cache count => (r.1, cacheOfWorldLog x.2.1 x.2.2 cache r.2, count))
    (fun slot => presampled_signing_trace_finalRun prims x.2.1 x.2.2 slot A x [])
    (Finset.univ : Finset (Slot C)).toList (Finset.nodup_toList _) ((∅, ∅), 0)
    (fun _ _ => rfl)
  have hfill : ∀ ω : Slot C → LeanXmss.HashOutput,
      setSigningSlots ((∅, ∅), 0)
        (fillSlots ω (Finset.univ : Finset (Slot C)).toList (signingSlots ((∅, ∅), 0))) =
      ((∅, fullTable ω), 0) := by
    intro ω
    dsimp only [setSigningSlots, signingSlots]
    congr 2
    funext s
    exact fillSlots_of_mem ω _ _ (Finset.mem_toList.mpr (Finset.mem_univ s))
  simp only [hfill] at h
  exact (traceObserved_empty_eq prims A x hc).symm.trans h.symm

theorem exposedRun_event_eq_presampled (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (hc : ¬KeyCollision x.2.1 x.2.2)
    (event : Outcome C → Prop) :
    Pr[event | SigningDescentProof.exposedRun prims A x] =
      Pr[event | ($ᵗ (Slot C → LeanXmss.HashOutput)) >>= fun ω =>
        traceObserved prims A x (fullTable ω)] :=
  probEvent_congr' (fun _ _ => Iff.rfl) (exposedRun_eq_presampled prims A x hc)

set_option maxRecDepth 100000 in
/-- The real fixed cap holds for every presampled share table, including runs
after the hidden-key flag is set. Thus presampling does not silently enlarge
the adversary's budget on branches later discarded by the winning event. -/
theorem traceObserved_count_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hc : ¬KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (ω : Slot C → LeanXmss.HashOutput) :
    ∀ r ∈ support (traceObserved prims A x (fullTable ω)), r.2.2 ≤ q := by
  intro r hr
  apply exposedRun_count_le prims A x q hq r
  rw [← mem_support_evalDist_iff, exposedRun_eq_presampled prims A x hc, mem_support_evalDist_iff,
    mem_support_bind_iff]
  exact ⟨ω, by simp, hr⟩

set_option maxRecDepth 100000 in
theorem presampled_finalRun_count_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hc : ¬KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (ω : Slot C → LeanXmss.HashOutput) :
    ∀ r ∈ support ((simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
      ((simulateQ traceWorld (SigningDescentProof.finalRun A x)).run [])).run ((∅, fullTable ω), 0)),
      r.2.2 ≤ q := by
  intro r hr
  apply traceObserved_count_le prims A x hc q hq ω
    (r.1.1, cacheOfWorldLog x.2.1 x.2.2 r.2.1.1 r.1.2, r.2.2)
  rw [traceObserved, support_map]
  exact ⟨r, hr, rfl⟩

/-- The original continuation after initial top-tree generation. -/
def finalRunAfterTop (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Option TreeOutput →
      OracleComp (WorldSpec C) ((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery))
  | some (.top top) => do
      let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
      let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
        (dealtKeys x.1 x.2.1 x.2.2) top value
      let r ← (simulateQ (SigningCoreProof.flaggedOracles x dealt)
        (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run (SigningCoreProof.tsigInit, false)
      (fun w => ((w.1, r.2.2), some (top, w.2.1, w.2.2))) <$>
        SigningCoreProof.tsigFinish dealt (r.1, r.2.1)
  | _ => pure ((false, false), none)

theorem finalRun_eq_top_bind (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    SigningDescentProof.finalRun A x =
      referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun point => SigningSecurityProof.liftFree (prfValue x.2.1 point)) x.1 emptyTop .top >>=
          finalRunAfterTop A x := rfl

/-- Replace only the initial source forest, retaining the actual post-setup
signing continuation and every field of its counted state. -/
def fixedForestFinalRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (omega : Slot C → LeanXmss.HashOutput) := do
  let r ← (simulateQ (fixedForestImpl omega) (forestTree x.1 emptyTop .top)).run (∅, 0)
  (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
    (finalRunAfterTop A x r.1)).run (fixedSlotState omega r.2)

theorem fixedForestFinalRun_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hinj : Function.Injective (slotInput x.2.1 x.2.2))
    (omega : Slot C → LeanXmss.HashOutput) :
    (simulateQ (SeedHitProof.splitWorld prims x.2.1 x.2.2)
      (SigningDescentProof.finalRun A x)).run ((∅, fullTable omega), 0) =
        fixedForestFinalRun prims A x omega := by
  rw [finalRun_eq_top_bind, simulateQ_bind, StateT.run_bind,
    signing_tree_run_full prims x.2.1 x.2.2 hinj, bind_map_left]
  rfl

set_option maxRecDepth 100000 in
/-- The real signing cap holds after the exact full-state setup replacement.
No source-budget hypothesis for the new forest interpreter is introduced. -/
theorem fixedForestFinalRun_count_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (hc : ¬KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (omega : Slot C → LeanXmss.HashOutput) :
    ∀ r ∈ support (fixedForestFinalRun prims A x omega), r.2.2 ≤ q := by
  intro r hr
  have hinj : Function.Injective (slotInput x.2.1 x.2.2) := by
    simp only [KeyCollision, not_or, not_not] at hc
    exact slotInput_injective hc.1 hc.2
  rw [← fixedForestFinalRun_eq prims A x hinj omega,
    ← run_traceWorld_forget _ (SigningDescentProof.finalRun A x) [], support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  exact presampled_finalRun_count_le prims A x hc q hq omega z hz

end SigningPresample

section SigningRawOracle

variable {C : Committee} (prims : Primitives)

abbrev SigningRawSpec (C : Committee) := PrivateRoSpec (Query C) LeanXmss.HashOutput

/-- Lower local calls to their actual primitive RO accesses. The PRG's
stream-key read is explicit here, so observation includes its cache entry. -/
def signingRawLocal : QueryImpl (LocalSpec C) (OracleComp (SigningRawSpec C))
  | .inl n => query (spec := SigningRawSpec C) (.inl n)
  | .inr (.inl input) => query (spec := SigningRawSpec C) (.inr input)
  | .inr (.inr input) => do
      let derived ← query (spec := SigningRawSpec C) (.inr (.streamKey input.2.1))
      pure (prims.aes.eval (LeanXmss.truncateHash derived) input.2.2)

def signingRawWorld : QueryImpl (WorldSpec C) (OracleComp (SigningRawSpec C))
  | .inl (.inl input) => signingRawLocal prims input
  | .inr input => signingRawLocal prims input
  | .inl (.inr _) => pure false

/-- This is used only for computations proved below to contain no programming
calls. The excluded branch is not an implementation of a programming oracle. -/
def signingRawCounted : QueryImpl (WorldSpec C) (AddWriterT ℕ (OracleComp (SigningRawSpec C))) :=
  (signingRawWorld prims).withAddCost SeedHitProof.signCost

def signingRawInterpreted :
    QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  privateRoImpl.writerTMapBase (signingRawCounted prims)

theorem signingRawLocal_eq (input : (LocalSpec C).Domain) :
    simulateQ privateRoImpl (signingRawLocal prims input) = signingLocalAnswer prims input := by
  rcases input with n | input | input
  · exact (simulateQ_query _ _).trans (id_map _)
  · exact (simulateQ_query _ _).trans (id_map _)
  · simp only [signingRawLocal, simulateQ_bind, simulateQ_pure]
    have h : simulateQ (privateRoImpl (D := Query C) (R := LeanXmss.HashOutput))
        (query (spec := SigningRawSpec C) (.inr (.streamKey input.2.1))) =
          (Query C →ₒ LeanXmss.HashOutput).randomOracle (.streamKey input.2.1) :=
      (simulateQ_query _ _).trans (id_map _)
    rw [h]
    rfl

theorem signingRawInterpreted_free (input : (LocalSpec C).Domain) :
    signingRawInterpreted prims (.inr input) = signingWorld prims (.inr input) := by
  apply WriterT.ext
  simp [signingRawInterpreted, signingRawCounted, QueryImpl.writerTMapBase,
    QueryImpl.withAddCost, QueryImpl.withCost, QueryImpl.withTraceBefore,
    QueryImpl.preInsert, signingRawWorld, SeedHitProof.signingWorld_eq,
    SeedHitProof.signImpl, signingRawLocal_eq]

theorem signingRawInterpreted_counted (input : (LocalSpec C).Domain) :
    signingRawInterpreted prims (.inl (.inl input)) = signingWorld prims (.inl (.inl input)) := by
  apply WriterT.ext
  simp [signingRawInterpreted, signingRawCounted, QueryImpl.writerTMapBase,
    QueryImpl.withAddCost, QueryImpl.withCost, QueryImpl.withTraceBefore,
    QueryImpl.preInsert, signingRawWorld, SeedHitProof.signingWorld_eq,
    SeedHitProof.signImpl, signingRawLocal_eq]
  rfl

theorem signingRawInterpreted_finalRun (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    simulateQ (signingRawInterpreted prims) (SigningDescentProof.finalRun A x) =
      simulateQ (signingWorld prims) (SigningDescentProof.finalRun A x) := by
  let P : {α : Type} → OracleComp (WorldSpec C) α → Prop :=
    fun oa => simulateQ (signingRawInterpreted prims) oa = simulateQ (signingWorld prims) oa
  have hpure : ∀ {α : Type} (a : α), P (pure a) := by
    intro α a
    simp [P]
  have hbind : ∀ {α β : Type} (oa : OracleComp (WorldSpec C) α)
      (f : α → OracleComp (WorldSpec C) β), P oa → (∀ a, P (f a)) → P (oa >>= f) := by
    intro α β oa f ho hf
    change simulateQ _ (oa >>= f) = simulateQ _ (oa >>= f)
    simp only [simulateQ_bind]
    rw [show simulateQ (signingRawInterpreted prims) oa = _ from ho]
    congr 1
    funext a
    exact hf a
  apply signing_finalRun_closed P hpure hbind ?_ ?_ A x
  · apply signing_free_closed P hpure hbind
    intro input
    change simulateQ _ _ = simulateQ _ _
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      signingRawInterpreted_free]
  · apply signing_adversary_closed P hpure hbind
    intro input
    change simulateQ _ _ = simulateQ _ _
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      signingRawInterpreted_counted]

/-- Exact lowering of the entire signing experiment, including its original
cost writer. Private forest calls can now be inserted outside this writer. -/
theorem signingRawCounted_finalRun (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
      (SigningDescentProof.finalRun A x)).run) =
      (simulateQ (signingWorld prims) (SigningDescentProof.finalRun A x)).run := by
  have h {α : Type} (oa : OracleComp (WorldSpec C) α) :
      simulateQ privateRoImpl ((simulateQ (signingRawCounted prims) oa).run) =
        (simulateQ (signingRawInterpreted prims) oa).run := by
    induction oa using OracleComp.inductionOn with
    | pure a => simp
    | query_bind input continuation ih =>
      simp [signingRawInterpreted, QueryImpl.writerTMapBase, ih]
  exact (h _).trans (congrArg WriterT.run (signingRawInterpreted_finalRun prims A x))

abbrev SigningRawResult (C : Committee) :=
  ((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) × Multiplicative ℕ

def signingRawOutcome (result : SigningRawResult C × HashCache C) : Outcome C :=
  (result.1.1, result.2, Multiplicative.toAdd result.1.2)

/-- The private forest is retained for the proof. The returned public outcome
contains only source accesses and the original source cost. -/
def privateSigningRun {α : Type} (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (α × Outcome C) :=
  Prod.fst <$> (do
    let forest ← simulateQ randomOracle ghost
    let result ← simulateQ privateRoImpl ((simulateQ privateRoObserve
      ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run)).run ∅)
    pure (forest, signingRawOutcome result)).run ∅

set_option maxRecDepth 100000 in
theorem privateSigningRun_marginal {α : Type}
    (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    𝒟[Prod.snd <$> privateSigningRun prims ghost A x] =
      𝒟[SigningDescentProof.exposedRun prims A x] := by
  have h := private_forest_private_observation ghost
    ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run) ∅
  have hm := congrArg (fun d => (signingRawOutcome (C := C)) <$> d) h
  simp only [← evalDist_map] at hm
  rw [signingRawCounted_finalRun prims A x] at hm
  unfold privateSigningRun SigningDescentProof.exposedRun
  rw [SeedHitProof.withCount_run]
  generalize SigningDescentProof.finalRun A x = oa at hm ⊢
  dsimp only [signingRawOutcome] at hm ⊢
  simp only [Nat.zero_add, StateT.run_bind, StateT.run_pure, StateT.run_map,
    bind_pure_comp, map_bind, Functor.map_map] at hm ⊢
  convert hm using 1 <;> rfl

theorem privateSigningRun_count_le {α : Type}
    (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    ∀ r ∈ support (privateSigningRun prims ghost A x), r.2.2.2 ≤ q := by
  intro r hr
  apply exposedRun_count_le prims A x q hq r.2
  rw [← mem_support_evalDist_iff, ← privateSigningRun_marginal prims ghost A x,
    mem_support_evalDist_iff, support_map]
  exact ⟨r, hr, rfl⟩

/-- Every primitive read emitted by the lowering is paid for by the source
writer. The dummy programming branch emits no read and costs one. -/
def RawCostSound {α : Type}
    (source : OracleComp (SigningRawSpec C) (α × Multiplicative ℕ)) : Prop :=
  ∀ cache count result,
    result ∈ support ((simulateQ privateRoCounted source).run (cache, count)) →
      result.2.2 ≤ count + Multiplicative.toAdd result.1.2

theorem rawCostSound_pure {α : Type} (value : α) :
    RawCostSound (C := C) (pure (value, (1 : Multiplicative ℕ))) := by
  intro cache count result hr
  have heq : result = ((value, 1), cache, count) := by simpa using hr
  subst result
  simp

theorem rawCostSound_bind {α β : Type}
    (head : OracleComp (SigningRawSpec C) (α × Multiplicative ℕ))
    (tail : α → OracleComp (SigningRawSpec C) (β × Multiplicative ℕ))
    (hh : RawCostSound head) (ht : ∀ a, RawCostSound (tail a)) :
    RawCostSound (do
      let a ← head
      (fun b => (b.1, a.2 * b.2)) <$> tail a.1) := by
  intro cache count result hr
  simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨a, ha, b, hb, rfl⟩ := hr
  have h₁ := hh cache count a ha
  have h₂ := ht a.1.1 a.2.1 a.2.2 b hb
  simpa only [toAdd_mul, Nat.add_assoc] using
    h₂.trans (Nat.add_le_add_right h₁ (Multiplicative.toAdd b.1.2))

theorem signingRawCounted_query_cost (input : (WorldSpec C).Domain) :
    RawCostSound ((signingRawCounted prims input).run) := by
  intro cache count result hr
  rcases input with ((n | input | input) | program) | (n | input | input)
  all_goals
    simp [signingRawCounted, QueryImpl.withAddCost, QueryImpl.withCost,
      QueryImpl.withTraceBefore, QueryImpl.preInsert, signingRawWorld,
      signingRawLocal, SeedHitProof.signCost, privateRoCounted, rawCallCost,
      StateT.run_bind, bind_map_left, Functor.map_map, mem_support_bind_iff,
      support_map, Set.mem_image] at hr
  all_goals first
    | (obtain ⟨a, _, rfl⟩ := hr; simp)
    | (have heq := Set.mem_singleton_iff.mp hr; subst result; simp)

theorem signingRawCounted_cost {α : Type} (source : OracleComp (WorldSpec C) α) :
    RawCostSound ((simulateQ (signingRawCounted prims) source).run) := by
  induction source using OracleComp.inductionOn with
  | pure value => simpa using rawCostSound_pure (C := C) value
  | query_bind input continuation ih =>
    simpa only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind] using
      rawCostSound_bind _ _ (signingRawCounted_query_cost prims input) ih

set_option maxRecDepth 100000 in
theorem exposedRun_eq_raw (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    SigningDescentProof.exposedRun prims A x = signingRawOutcome <$>
      (simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
        (SigningDescentProof.finalRun A x)).run)).run ∅ := by
  rw [signingRawCounted_finalRun prims A x]
  unfold SigningDescentProof.exposedRun
  rw [SeedHitProof.withCount_run]
  simp only [Nat.zero_add]
  rfl

set_option maxRecDepth 100000 in
theorem signingRawCounted_count_le (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (r : SigningRawResult C × HashCache C)
    (hr : r ∈ support ((simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
      (SigningDescentProof.finalRun A x)).run)).run ∅)) :
    Multiplicative.toAdd r.1.2 ≤ q := by
  apply exposedRun_count_le prims A x q hq (signingRawOutcome r)
  rw [SigningDescentProof.exposedRun, SeedHitProof.withCount_run, support_map]
  refine ⟨r, ?_, ?_⟩
  · rwa [signingRawCounted_finalRun prims A x] at hr
  · simp [signingRawOutcome]

set_option maxRecDepth 100000 in
theorem signingRawCounted_prefix_count_le {α : Type}
    (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (pre : α × HashCache C)
    (hp : pre ∈ support ((simulateQ randomOracle ghost).run ∅))
    (r : SigningRawResult C × HashCache C)
    (hr : r ∈ support ((simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
      (SigningDescentProof.finalRun A x)).run)).run pre.2)) :
    Multiplicative.toAdd r.1.2 ≤ q := by
  have h := randomOracle_private_prefix_private ghost
    ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run) ∅
  have hm : r.1 ∈ support (Prod.fst <$> (do
      let _ ← simulateQ randomOracle ghost
      simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
        (SigningDescentProof.finalRun A x)).run)).run ∅) := by
    rw [support_map]
    refine ⟨r, ?_, rfl⟩
    rw [StateT.run_bind, mem_support_bind_iff]
    exact ⟨pre, hp, hr⟩
  rw [← mem_support_evalDist_iff, h, mem_support_evalDist_iff, support_map] at hm
  obtain ⟨r', hr', heq⟩ := hm
  have hb := signingRawCounted_count_le prims A x q hq r' hr'
  simpa only [heq] using hb

set_option maxRecDepth 100000 in
/-- The source cap bounds every raw RO read even after an arbitrary supported
private prefix. No cap is imposed on the private forest itself. -/
theorem signingRaw_prefix_raw_cap {α : Type}
    (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (pre : α × HashCache C)
    (hp : pre ∈ support ((simulateQ randomOracle ghost).run ∅)) :
    ∀ r ∈ support ((simulateQ privateRoCounted ((simulateQ (signingRawCounted prims)
      (SigningDescentProof.finalRun A x)).run)).run (pre.2, 0)), r.2.2 ≤ q := by
  intro r hr
  have hcost := signingRawCounted_cost prims (SigningDescentProof.finalRun A x)
    pre.2 0 r hr
  simp only [Nat.zero_add] at hcost
  refine hcost.trans (signingRawCounted_prefix_count_le prims ghost A x q hq pre hp
    (r.1, r.2.1) ?_)
  rw [← privateRoCounted_projection _ pre.2 0, support_map]
  exact ⟨r, hr, rfl⟩

/-- One output unit for the actual signing source after a private forest.
The target may depend on the entire supported forest; only each *new* source
input's uniform output is used in this bound. -/
theorem signingRaw_fresh_output_le {α : Type}
    (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (pre : α × HashCache C)
    (hp : pre ∈ support ((simulateQ randomOracle ghost).run ∅))
    (target : Query C → LeanXmss.Digest) :
    Pr[fun result => NewTargetHit pre.2
      (fun input answer => LeanXmss.truncateHash answer = target input) result.2 |
      (simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
        (SigningDescentProof.finalRun A x)).run)).run pre.2] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  have hb := privateRo_newTarget_bound_cap
    ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run)
    pre.2 (fun input answer => LeanXmss.truncateHash answer = target input)
    ((2 ^ 128 : ℝ≥0∞)⁻¹) (fun input => ?_) q
    (signingRaw_prefix_raw_cap prims ghost A x q hq pre hp)
  · simpa only [div_eq_mul_inv, mul_comm] using hb
  · change Pr[fun answer : XmssSecurity.HashOutput =>
        XmssSecurity.truncateHash answer = target input | $ᵗ XmssSecurity.HashOutput] ≤ _
    simpa only [XmssSecurity.digestBits, Nat.cast_pow, Nat.cast_ofNat] using
      (XmssSecurity.Rom.uniform_truncate_probability (target input)).le

end SigningRawOracle


/-- A query is present after every supported execution of a computation. -/
def Caches {C : Committee} (prims : Primitives) {α : Type}
    (q : Query C) (oa : OracleComp (WorldSpec C) α) : Prop :=
  ∀ s r, r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) oa).run s) →
    ∃ output, r.2.1 q = some output

theorem caches_bind_left {C : Committee} (prims : Primitives) {α β : Type}
    (q : Query C) (oa : OracleComp (WorldSpec C) α)
    (f : α → OracleComp (WorldSpec C) β) (hc : Caches prims q oa) :
    Caches prims q (oa >>= f) := by
  intro s r hr
  obtain ⟨p, hp, hr⟩ := SigningCacheProof.run_bind_support prims oa f s r hr
  obtain ⟨output, ho⟩ := hc s p hp
  exact ⟨output, SigningCacheProof.countRun_grows prims _ _ r hr ho⟩

theorem caches_bind_right {C : Committee} (prims : Primitives) {α β : Type}
    (q : Query C) (oa : OracleComp (WorldSpec C) α)
    (f : α → OracleComp (WorldSpec C) β) (hc : ∀ a, Caches prims q (f a)) :
    Caches prims q (oa >>= f) := by
  intro s r hr
  obtain ⟨p, _, hr⟩ := SigningCacheProof.run_bind_support prims oa f s r hr
  exact hc p.1 p.2 r hr

theorem caches_map {C : Committee} (prims : Primitives) {α β : Type}
    (q : Query C) (oa : OracleComp (WorldSpec C) α)
    (f : α → β) (hc : Caches prims q oa) : Caches prims q (f <$> oa) := by
  rw [← bind_pure_comp]
  exact caches_bind_left prims q oa _ hc

theorem caches_mapM {C : Committee} (prims : Primitives) {α β : Type}
    (q : Query C) (f : α → OracleComp (WorldSpec C) β) (xs : List α)
    (a : α) (ha : a ∈ xs) (hc : Caches prims q (f a)) :
    Caches prims q (xs.mapM f) := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rw [List.mapM_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact caches_bind_left prims q _ _ hc
    · apply caches_bind_right prims q
      intro value
      exact caches_map prims q _ _ (ih ha)

theorem caches_hashQuery {C : Committee} (prims : Primitives) (q : Query C) :
    Caches prims q (SigningSecurityProof.liftFree (hashQuery q)) := by
  intro s r hr
  exact ⟨r.1, SigningCacheProof.run_hashQuery prims q s r hr⟩

/-- Every PRF term, not just a fresh one, is cached by the actual execution. -/
theorem caches_prfValue {C : Committee} (prims : Primitives)
    (seeds : C.Term → LeanXmss.HashOutput) (point : Point) (T : C.Term) :
    Caches prims (.prf (seeds T) point)
      (SigningSecurityProof.liftFree (prfValue seeds point)) := by
  change Caches prims _ (SigningCacheProof.freeHom (prfValue seeds point))
  rw [prfValue, MonadHom.mmap_bind, SeedHitProof.hom_mapM]
  apply caches_bind_left prims
  apply caches_mapM prims _ _ _ T (by simp [Committee.terms])
  rw [prf, SeedHitProof.hom_map]
  exact caches_map prims _ _ _ (caches_hashQuery prims _)

/-- A list computation really executes each member, with a cache contained in
the final cache. This also covers repeated list members and cache hits. -/
theorem run_mapM_member {C : Committee} (prims : Primitives) {α β : Type}
    (f : α → OracleComp (WorldSpec C) β) (xs : List α) (a : α) (ha : a ∈ xs) :
    ∀ s r, r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (xs.mapM f)).run s) →
      ∃ s' p, p ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (f a)).run s') ∧
        p.2.1 ≤ r.2.1 := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    intro s r hr
    rw [List.mapM_cons] at hr
    obtain ⟨p, hp, htail⟩ := SigningCacheProof.run_bind_support prims (f b) _ s r hr
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨s, p, hp, SigningCacheProof.countRun_grows prims _ _ r htail⟩
    · obtain ⟨v, hv, hrest⟩ := SigningCacheProof.run_bind_support prims (xs.mapM f) _ p.2 r htail
      obtain ⟨s', p', hp', hle⟩ := ih ha p.2 v hv
      exact ⟨s', p', hp', hle.trans (SigningCacheProof.countRun_grows prims _ _ r hrest)⟩

theorem referenceCommitment_eq {C : Committee}
    (seeds : C.Term → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) :
    referenceJob tweakable (prfValue seeds) P
      ⟨.commitment e, [.randomizer LeanXmss.bottomLayer e]⟩ =
      (prfValue seeds (.randomizer LeanXmss.bottomLayer e) >>= fun canonical =>
        (bitsOfDigest ∘ LeanXmss.truncateHash) <$>
          hashQuery (.hash (commitmentInput P e canonical))) := by
  simp [referenceJob, List.mapM_cons, List.mapM_nil,
    tweakable_oracleHash]

/-- Running the commitment job caches the PRF terms and its resulting hash
input. The canonical value is evaluated in any extension of the final cache. -/
theorem run_referenceCommitment_cached {C : Committee} (prims : Primitives)
    (seeds : C.Term → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) (s : HashCache C × ℕ)
    (r : List Bit × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceJob tweakable (prfValue seeds) P
        ⟨.commitment e, [.randomizer LeanXmss.bottomLayer e]⟩))).run s))
    (h : Query C → LeanXmss.HashOutput) (ha : Agrees h r.2.1) :
    (∀ T : C.Term, ∃ output,
      r.2.1 (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) = some output) ∧
    ∃ output, r.2.1 (.hash (commitmentInput P e
      (D prims h (prfValue seeds (.randomizer LeanXmss.bottomLayer e))))) = some output := by
  rw [referenceCommitment_eq, SigningSecurityProof.liftFree, liftComp_bind, free_bind] at hr
  obtain ⟨p, hp, hr⟩ := SigningCacheProof.run_bind_support prims _ _ s r hr
  have hgrow := SigningCacheProof.countRun_grows prims _ _ r hr
  have he := SigningCacheProof.run_liftFree prims _ s p hp h (ha.mono hgrow)
  constructor
  · intro T
    obtain ⟨output, ho⟩ := caches_prfValue prims seeds _ T s p hp
    exact ⟨output, hgrow ho⟩
  · rw [← he]
    have hc := caches_map (C := C) prims (.hash (commitmentInput P e p.1))
      (SigningSecurityProof.liftFree (hashQuery (.hash (commitmentInput P e p.1))))
      (bitsOfDigest ∘ LeanXmss.truncateHash) (caches_hashQuery prims _)
    apply hc p.2 r
    change r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningCacheProof.freeHom ((bitsOfDigest ∘ LeanXmss.truncateHash) <$>
        hashQuery (.hash (commitmentInput P e p.1))))).run p.2) at hr
    rw [SeedHitProof.hom_map] at hr
    exact hr

theorem run_bind_support_grows {C : Committee} (prims : Primitives) {α β : Type}
    (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β)
    (s : HashCache C × ℕ) (r : β × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (oa >>= f)).run s)) :
    ∃ p, p ∈ support ((simulateQ (SigningCacheProof.countImpl prims) oa).run s) ∧
      r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (f p.1)).run p.2) ∧
      p.2.1 ≤ r.2.1 := by
  obtain ⟨p, hp, hrest⟩ := SigningCacheProof.run_bind_support prims oa f s r hr
  exact ⟨p, hp, hrest, SigningCacheProof.countRun_grows prims (f p.1) p.2 r hrest⟩

set_option maxRecDepth 100000 in
/-- Generating a bottom tree caches every randomizer commitment in that tree,
even if the later top-signature search fails. -/
theorem run_bottom_commitment_cached {C : Committee} (prims : Primitives)
    (seeds : C.Term → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (top : TopTree) (e : LeanXmss.KeyIndex) (s : HashCache C × ℕ)
    (r : Option TreeOutput × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue seeds) P
        top (.bottom (treeOf e))))).run s))
    (h : Query C → LeanXmss.HashOutput) (ha : Agrees h r.2.1) :
    (∀ T : C.Term, ∃ output,
      r.2.1 (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) = some output) ∧
    ∃ output, r.2.1 (.hash (commitmentInput P e
      (D prims h (prfValue seeds (.randomizer LeanXmss.bottomLayer e))))) = some output := by
  change r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
    (SigningCacheProof.freeHom _)).run s) at hr
  rw [refBottom_eq, MonadHom.mmap_bind, SeedHitProof.hom_mapM] at hr
  obtain ⟨p, hp, _, hrestGrow⟩ := run_bind_support_grows prims _ _ s r hr
  have hm : (⟨.commitment e, [.randomizer LeanXmss.bottomLayer e]⟩ : Job) ∈
      bottomJobs (treeOf e) := by
    rw [bottomJobs_eq]
    apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    refine ⟨⟨e.val % 2 ^ LeanXmss.layerHeight, Nat.mod_lt _ (by decide)⟩, by simp, ?_⟩
    simp only [bottomKey_treeOf]
  obtain ⟨s', p', hp', hle⟩ := run_mapM_member prims _ _ _ hm s p hp
  have hgrow := hle.trans hrestGrow
  obtain ⟨ht, output, ho⟩ := run_referenceCommitment_cached prims seeds P e s' p'
    (by exact hp') h (ha.mono hgrow)
  exact ⟨fun T => by obtain ⟨v, hv⟩ := ht T; exact ⟨v, hgrow hv⟩, output, hgrow ho⟩

theorem caches_signCodeword {C : Committee} (prims : Primitives)
    (P : LeanXmss.PublicParameter) (commitment : LeanXmss.Digest)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (candidate : LeanXmss.Digest) :
    Caches (C := C) prims (.hash (commitmentInput P e candidate))
      (SigningSecurityProof.liftFree (signCodeword P commitment e message candidate)) := by
  change Caches (C := C) prims (.hash (commitmentInput P e candidate))
    (SigningCacheProof.freeHom (signCodeword P commitment e message candidate))
  rw [signCodeword, tweakable_bind, tweakable_oracleHash, MonadHom.mmap_bind]
  exact caches_bind_left prims _ _ _ (caches_hashQuery prims _)

set_option maxRecDepth 100000 in
/-- A successfully generated bottom tree commits to the canonical PRF value
in every extension of the run's cache. -/
theorem run_bottom_commitment_eq {C : Committee} (prims : Primitives)
    (seeds : C.Term → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (top : TopTree) (e : LeanXmss.KeyIndex) (s : HashCache C × ℕ)
    (r : Option TreeOutput × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue seeds) P
        top (.bottom (treeOf e))))).run s))
    (h : Query C → LeanXmss.HashOutput) (ha : Agrees h r.2.1)
    (htop : TopFacts prims h seeds P top) (tree : BottomTree)
    (hs : r.1 = some (.bottom tree)) :
    tree.commitment e = LeanXmss.truncateHash (h (.hash (commitmentInput P e
      (D prims h (prfValue seeds (.randomizer LeanXmss.bottomLayer e)))))) := by
  have hd := (SigningCacheProof.run_liftFree prims _ s r (by exact hr) h ha).symm.trans hs
  rcases D_refBottom P seeds top htop.1 htop.2 (treeOf e) with hn | ⟨tree', ht, hspec⟩
  · rw [hd] at hn
    contradiction
  · have he : tree' = tree := TreeOutput.bottom.inj (Option.some.inj (ht.symm.trans hd))
    subst tree'
    simpa only [bottomKey_treeOf] using
      hspec.commitment ⟨e.val % 2 ^ LeanXmss.layerHeight, Nat.mod_lt _ (by decide)⟩

/-- A different commitment preimage at the forged key. All PRF terms and both
commitment inputs must actually be cached; default-zero replay is not a witness. -/
def OpeningMatch {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := finalOf x r top state forgery
    let point := Point.randomizer LeanXmss.bottomLayer z.key
    let canonical := D prims z.answers (prfValue x.2.1 point)
    (∀ T : C.Term, ∃ output, z.cache (.prf (x.2.1 T) point) = some output) ∧
    ∃ candidate canonicalOutput candidateOutput,
      z.cache (.hash (commitmentInput x.1 z.key canonical)) = some canonicalOutput ∧
      z.cache (.hash (commitmentInput x.1 z.key candidate)) = some candidateOutput ∧
      DifferentOpening z.answers x.1 z.key canonical candidate

section AlternativeCommitments

variable {C : Committee}

def cachedRandomizer (seeds : C.Term → LeanXmss.HashOutput) (cache : HashCache C)
    (e : LeanXmss.KeyIndex) : LeanXmss.Digest :=
  (C.terms.map fun T => LeanXmss.truncateHash
    ((cache (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))).getD 0)).foldl (· ^^^ ·) 0

def RandomizerCached (seeds : C.Term → LeanXmss.HashOutput) (cache : HashCache C)
    (e : LeanXmss.KeyIndex) : Prop :=
  ∀ T : C.Term, ∃ output, cache (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) = some output

theorem cachedRandomizer_eq (prims : Primitives) (seeds : C.Term → LeanXmss.HashOutput)
    (cache : HashCache C) (e : LeanXmss.KeyIndex) :
    D prims (fun input => (cache input).getD 0)
      (prfValue seeds (.randomizer LeanXmss.bottomLayer e)) = cachedRandomizer seeds cache e := by
  rw [prfValue, D_bind, D_mapM, D_pure]
  simp only [prf, D_map, D_hashQuery, cachedRandomizer]

theorem cachedRandomizer_stable (seeds : C.Term → LeanXmss.HashOutput)
    (left right : HashCache C) (e : LeanXmss.KeyIndex)
    (hle : left ≤ right) (hc : RandomizerCached seeds left e) :
    cachedRandomizer seeds left e = cachedRandomizer seeds right e := by
  unfold cachedRandomizer
  congr 1
  apply List.map_congr_left
  intro T _
  obtain ⟨value, hv⟩ := hc T
  rw [hv, hle hv]

def AlternativeCommitment (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C) : Prop :=
  ∃ e candidate canonicalOutput candidateOutput,
    RandomizerCached seeds cache e ∧
    cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e))) = some canonicalOutput ∧
    cache (.hash (commitmentInput P e candidate)) = some candidateOutput ∧
    candidate ≠ cachedRandomizer seeds cache e ∧
    LeanXmss.truncateHash candidateOutput = LeanXmss.truncateHash canonicalOutput

theorem alternativeCommitment_mono (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (left right : HashCache C) (hle : left ≤ right)
    (hit : AlternativeCommitment seeds P left) : AlternativeCommitment seeds P right := by
  obtain ⟨e, candidate, canonicalOutput, candidateOutput, hc, hcanonical, hcandidate, hne, heq⟩ := hit
  have hs := cachedRandomizer_stable seeds left right e hle hc
  refine ⟨e, candidate, canonicalOutput, candidateOutput,
    (fun T => by obtain ⟨v, hv⟩ := hc T; exact ⟨v, hle hv⟩), ?_, hle hcandidate, ?_, heq⟩
  · rw [← hs]
    exact hle hcanonical
  · rwa [← hs]

/-- The commitment-only private prefix contains every canonical commitment
and no alternative opening at any key. -/
def CanonicalCommitments (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C) : Prop :=
  ∀ e, RandomizerCached seeds cache e ∧
    (∃ output, cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e))) = some output) ∧
    ∀ candidate, candidate ≠ cachedRandomizer seeds cache e →
      cache (.hash (commitmentInput P e candidate)) = none

set_option maxRecDepth 100000 in
def commitmentOutputTarget (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C) : Query C → LeanXmss.Digest
  | .hash input => ((commitmentTrial P input).map fun trial => LeanXmss.truncateHash
      ((cache (.hash (commitmentInput P trial.1 (cachedRandomizer seeds cache trial.1)))).getD 0)).getD 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem commitmentOutputTarget_eq (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C) (input : LeanXmss.HashInput)
    (e : LeanXmss.KeyIndex) (candidate : LeanXmss.Digest)
    (ht : commitmentTrial P input = some (e, candidate)) :
    commitmentOutputTarget seeds P cache (.hash input) = LeanXmss.truncateHash
      ((cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e)))).getD 0) := by
  simp only [commitmentOutputTarget, ht, Option.map_some, Option.getD_some]

set_option maxRecDepth 100000 in
theorem alternativeCommitment_newTarget (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (initial final : HashCache C)
    (hinit : CanonicalCommitments seeds P initial) (hle : initial ≤ final)
    (hit : AlternativeCommitment seeds P final) :
    NewTargetHit initial (fun input answer =>
      LeanXmss.truncateHash answer = commitmentOutputTarget seeds P initial input) final := by
  obtain ⟨e, candidate, canonicalOutput, candidateOutput, _, hcanonical, hcandidate, hne, heq⟩ := hit
  obtain ⟨hc, ⟨output, houtput⟩, hnone⟩ := hinit e
  have hs := cachedRandomizer_stable seeds initial final e hle hc
  have ho : output = canonicalOutput := by
    have hg := hle houtput
    rw [hs, hcanonical] at hg
    exact Option.some.inj hg.symm
  refine ⟨.hash (commitmentInput P e candidate), candidateOutput,
    hnone candidate (by rwa [hs]), hcandidate, ?_⟩
  have ht : commitmentTrial P (commitmentInput P e candidate) = some (e, candidate) :=
    (commitmentTrial_eq_some P _ e candidate).mpr rfl
  have htarget := commitmentOutputTarget_eq seeds P initial _ e candidate ht
  rw [houtput] at htarget
  exact heq.trans (by simpa only [Option.getD_some, ho] using htarget.symm)

set_option maxRecDepth 100000 in
theorem alternativeCommitment_bound_of_prefix (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    {α : Type} (ghost : OracleComp (Query C →ₒ LeanXmss.HashOutput) α)
    (hghost : ∀ pre ∈ support ((simulateQ randomOracle ghost).run ∅),
      CanonicalCommitments x.2.1 x.1 pre.2) :
    Pr[fun result => AlternativeCommitment x.2.1 x.1 result.2 |
      (simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
        (SigningDescentProof.finalRun A x)).run)).run ∅] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  refine (private_forest_event_mono ghost
    ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run) ∅
    (fun result => AlternativeCommitment x.2.1 x.1 result.2)
    (fun _ left right hle hh => alternativeCommitment_mono x.2.1 x.1 left right hle hh)).trans ?_
  simp only [StateT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro pre hp
  refine le_trans (probEvent_mono fun result hr hh => ?_)
    (signingRaw_fresh_output_le prims ghost A x q hq pre hp
      (commitmentOutputTarget x.2.1 x.1 pre.2))
  exact alternativeCommitment_newTarget x.2.1 x.1 pre.2 result.2 (hghost pre hp)
    (privateRo_cache_le _ pre.2 result hr) hh

def rawRandomizerTerms (seeds : C.Term → LeanXmss.HashOutput) (e : LeanXmss.KeyIndex)
    (terms : List C.Term) : OracleComp (Query C →ₒ LeanXmss.HashOutput) (List LeanXmss.Digest) :=
  terms.mapM fun T => LeanXmss.truncateHash <$>
    query (spec := Query C →ₒ LeanXmss.HashOutput) (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))

theorem rawRandomizerTerms_support (seeds : C.Term → LeanXmss.HashOutput)
    (e : LeanXmss.KeyIndex) (terms : List C.Term) (cache : HashCache C)
    (result : List LeanXmss.Digest × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (rawRandomizerTerms seeds e terms)).run cache)) :
    result.1 = terms.map (fun T => LeanXmss.truncateHash
      ((result.2 (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))).getD 0)) ∧
    (∀ T ∈ terms, ∃ value, result.2 (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) = some value) ∧
    ∀ input, result.2 (.hash input) = cache (.hash input) := by
  induction terms generalizing cache result with
  | nil =>
    have heq : result = ([], cache) := by simpa [rawRandomizerTerms] using hr
    subst result
    simp
  | cons T terms ih =>
    simp only [rawRandomizerTerms, List.mapM_cons, simulateQ_bind, simulateQ_pure,
      simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, StateT.run_pure,
      StateT.run_map, bind_map_left, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨head, hh, tail, ht, rfl⟩ := hr
    obtain ⟨hvalues, hterms, hhashes⟩ := ih head.2 tail ht
    have hquery : simulateQ randomOracle
        (query (spec := Query C →ₒ LeanXmss.HashOutput)
          (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))) =
        (Query C →ₒ LeanXmss.HashOutput).randomOracle
          (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) :=
      (simulateQ_query _ _).trans (id_map _)
    rw [hquery] at hh
    have hhead := raw_query_support (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) cache head hh
    have hle := raw_randomOracle_cache_le (rawRandomizerTerms seeds e terms) head.2 tail ht
    have hcached := hle hhead.1
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, hvalues, hcached, Option.getD_some]
    · intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨head.1, hcached⟩
      · exact hterms T' hT'
    · intro input
      exact (hhashes input).trans (hhead.2.2 (.hash input) (by intro h; cases h))

def rawRandomizer (seeds : C.Term → LeanXmss.HashOutput) (e : LeanXmss.KeyIndex) :
    OracleComp (Query C →ₒ LeanXmss.HashOutput) LeanXmss.Digest :=
  (fun values => values.foldl (· ^^^ ·) 0) <$> rawRandomizerTerms seeds e C.terms

theorem rawRandomizer_support (seeds : C.Term → LeanXmss.HashOutput)
    (e : LeanXmss.KeyIndex) (cache : HashCache C) (result : LeanXmss.Digest × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (rawRandomizer seeds e)).run cache)) :
    result.1 = cachedRandomizer seeds result.2 e ∧ RandomizerCached seeds result.2 e ∧
      ∀ input, result.2 (.hash input) = cache (.hash input) := by
  simp only [rawRandomizer, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨values, hv, rfl⟩ := hr
  obtain ⟨hvalues, hterms, hhashes⟩ := rawRandomizerTerms_support seeds e C.terms cache values hv
  refine ⟨?_, ?_, hhashes⟩
  · simp only [cachedRandomizer, hvalues]
  · intro T
    exact hterms T (by simp [Committee.terms])

def CommitmentsCanonical (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C) : Prop :=
  ∀ e candidate output, cache (.hash (commitmentInput P e candidate)) = some output →
    RandomizerCached seeds cache e ∧ candidate = cachedRandomizer seeds cache e

def CommitmentCached (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C) (e : LeanXmss.KeyIndex) : Prop :=
  RandomizerCached seeds cache e ∧
    ∃ output, cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e))) = some output

theorem randomizerCached_mono (seeds : C.Term → LeanXmss.HashOutput)
    (left right : HashCache C) (hle : left ≤ right) (e : LeanXmss.KeyIndex)
    (hc : RandomizerCached seeds left e) : RandomizerCached seeds right e := by
  intro T
  obtain ⟨value, hv⟩ := hc T
  exact ⟨value, hle hv⟩

theorem commitmentCached_mono (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (left right : HashCache C) (hle : left ≤ right)
    (e : LeanXmss.KeyIndex) (hc : CommitmentCached seeds P left e) :
    CommitmentCached seeds P right e := by
  obtain ⟨hc, value, hv⟩ := hc
  refine ⟨randomizerCached_mono seeds left right hle e hc, value, ?_⟩
  rw [← cachedRandomizer_stable seeds left right e hle hc]
  exact hle hv

def rawCommitment (seeds : C.Term → LeanXmss.HashOutput) (P : LeanXmss.PublicParameter)
    (e : LeanXmss.KeyIndex) : OracleComp (Query C →ₒ LeanXmss.HashOutput) Unit := do
  let rho ← rawRandomizer seeds e
  let _ ← query (spec := Query C →ₒ LeanXmss.HashOutput) (.hash (commitmentInput P e rho))
  pure ()

theorem rawCommitment_support (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex) (cache : HashCache C)
    (hc : CommitmentsCanonical seeds P cache) (result : Unit × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (rawCommitment seeds P e)).run cache)) :
    CommitmentsCanonical seeds P result.2 ∧ CommitmentCached seeds P result.2 e := by
  simp only [rawCommitment, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨middle, hm, last, hl, rfl⟩ := hr
  obtain ⟨hrho, hslots, hhashes⟩ := rawRandomizer_support seeds e cache middle hm
  have hmid := raw_randomOracle_cache_le (rawRandomizer seeds e) cache middle hm
  have hquery : simulateQ randomOracle
      (query (spec := Query C →ₒ LeanXmss.HashOutput) (.hash (commitmentInput P e middle.1))) =
        (Query C →ₒ LeanXmss.HashOutput).randomOracle (.hash (commitmentInput P e middle.1)) :=
    (simulateQ_query _ _).trans (id_map _)
  rw [hquery] at hl
  have hlast := raw_query_support (.hash (commitmentInput P e middle.1)) middle.2 last hl
  have hstable := cachedRandomizer_stable seeds middle.2 last.2 e hlast.2.1 hslots
  have hmiddle : CommitmentsCanonical seeds P middle.2 := by
    intro key candidate output houtput
    obtain ⟨hkey, hcand⟩ := hc key candidate output ((hhashes _).symm.trans houtput)
    exact ⟨randomizerCached_mono seeds cache middle.2 hmid key hkey,
      hcand.trans (cachedRandomizer_stable seeds cache middle.2 key hmid hkey)⟩
  refine ⟨?_, randomizerCached_mono seeds middle.2 last.2 hlast.2.1 e hslots, last.1, ?_⟩
  · intro key candidate output houtput
    by_cases heq : commitmentInput P key candidate = commitmentInput P e middle.1
    · have hkey := commitmentInput_key_eq P heq
      subst key
      have hcand := SigningCoreProof.commitmentInput_injective P e heq
      exact ⟨randomizerCached_mono seeds middle.2 last.2 hlast.2.1 e hslots,
        hcand.trans (hrho.trans hstable)⟩
    · have hnoneq : Query.hash (C := C) (commitmentInput P key candidate) ≠
          .hash (commitmentInput P e middle.1) := fun h => heq (Query.hash.inj h)
      have hprevious := (hlast.2.2 _ hnoneq).symm.trans houtput
      obtain ⟨hkey, hcand⟩ := hmiddle key candidate output hprevious
      exact ⟨randomizerCached_mono seeds middle.2 last.2 hlast.2.1 key hkey,
        hcand.trans (cachedRandomizer_stable seeds middle.2 last.2 key hlast.2.1 hkey)⟩
  · rw [← hstable, ← hrho]
    exact hlast.1

theorem rawCommitments_support (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (keys : List LeanXmss.KeyIndex) (cache : HashCache C)
    (hc : CommitmentsCanonical seeds P cache) (result : List Unit × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (keys.mapM (rawCommitment seeds P))).run cache)) :
    CommitmentsCanonical seeds P result.2 ∧ ∀ e ∈ keys, CommitmentCached seeds P result.2 e := by
  induction keys generalizing cache result with
  | nil =>
    have heq : result = ([], cache) := by simpa using hr
    subst result
    exact ⟨hc, by simp⟩
  | cons e keys ih =>
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨head, hh, tail, ht, rfl⟩ := hr
    obtain ⟨hcanonical, hkey⟩ := rawCommitment_support seeds P e cache hc head hh
    obtain ⟨hcanonical', hkeys⟩ := ih head.2 hcanonical tail ht
    refine ⟨hcanonical', ?_⟩
    intro key hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact commitmentCached_mono seeds P head.2 tail.2
        (raw_randomOracle_cache_le _ head.2 tail ht) key hkey
    · exact hkeys key hk

def rawCommitmentForest (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) : OracleComp (Query C →ₒ LeanXmss.HashOutput) (List Unit) :=
  (Finset.univ.toList : List LeanXmss.KeyIndex).mapM (rawCommitment seeds P)

theorem rawCommitmentForest_support (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (result : List Unit × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (rawCommitmentForest seeds P)).run ∅)) :
    CanonicalCommitments seeds P result.2 := by
  have hzero : CommitmentsCanonical seeds P (∅ : HashCache C) := by
    intro e candidate output houtput
    cases houtput
  obtain ⟨hcanonical, hkeys⟩ := rawCommitments_support seeds P Finset.univ.toList ∅ hzero result hr
  intro e
  obtain ⟨hslots, houtput⟩ := hkeys e (by simp)
  refine ⟨hslots, houtput, ?_⟩
  intro candidate hne
  cases hv : result.2 (.hash (commitmentInput P e candidate)) with
  | none => rfl
  | some value => exact (hne (hcanonical e candidate value hv).2).elim

/-- All alternative commitment openings, at all keys and across all sessions,
share one output unit of the actual source cap. -/
theorem alternativeCommitment_bound (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    Pr[fun result => AlternativeCommitment x.2.1 x.1 result.2 |
      (simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
        (SigningDescentProof.finalRun A x)).run)).run ∅] ≤ (q : ℝ≥0∞) / 2 ^ 128 :=
  alternativeCommitment_bound_of_prefix prims A x q hq (rawCommitmentForest x.2.1 x.1)
    (rawCommitmentForest_support x.2.1 x.1)

theorem openingMatch_alternativeCommitment (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (result : Outcome C)
    (hit : OpeningMatch prims x result) : AlternativeCommitment x.2.1 x.1 result.2.1 := by
  obtain ⟨top, state, forgery, _, hslots, candidate, canonicalOutput, candidateOutput,
    hcanonical, hcandidate, hne, heq⟩ := hit
  have hcanon := cachedRandomizer_eq prims x.2.1 result.2.1 forgery.signature.leafIndex
  change result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex
    (D prims (fun input => (result.2.1 input).getD 0)
      (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer forgery.signature.leafIndex))))) =
        some canonicalOutput at hcanonical
  change candidate ≠ D prims (fun input => (result.2.1 input).getD 0)
    (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer forgery.signature.leafIndex)) at hne
  rw [hcanon] at hcanonical hne
  refine ⟨forgery.signature.leafIndex, candidate, canonicalOutput, candidateOutput,
    hslots, hcanonical, hcandidate, hne, ?_⟩
  change LeanXmss.truncateHash
      ((result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex candidate))).getD 0) =
    LeanXmss.truncateHash
      ((result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex
        (D prims (fun input => (result.2.1 input).getD 0)
          (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer forgery.signature.leafIndex)))))).getD 0) at heq
  rw [hcanon, hcanonical] at heq
  change result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex candidate)) =
    some candidateOutput at hcandidate
  simpa only [hcandidate, Option.getD_some] using heq

theorem openingMatch_map_le (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (run : ProbComp (SigningRawResult C × HashCache C)) :
    Pr[OpeningMatch prims x | signingRawOutcome <$> run] ≤
      Pr[fun result => AlternativeCommitment x.2.1 x.1 result.2 | run] := by
  rw [probEvent_map]
  exact probEvent_mono fun result _ hh =>
    openingMatch_alternativeCommitment prims x (signingRawOutcome result) hh

/-- The concrete noncanonical-opening event costs one output unit. This bound
alone is not added to HitLaneBound; the expected-domain refinement below
leaves complementary calls available to the structural output charge. -/
theorem openingMatch_bound (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    Pr[OpeningMatch prims x | SigningDescentProof.exposedRun prims A x] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  rw [exposedRun_eq_raw prims A x]
  exact (openingMatch_map_le prims x _).trans (alternativeCommitment_bound prims A x q hq)

/-- Only commitment queries at this public parameter can incur the opening
output charge. The other raw domains remain available to the structural lane. -/
def RawCommitmentInput (P : LeanXmss.PublicParameter) : Query C → Prop
  | .hash input => (commitmentTrial P input).isSome
  | _ => False

def RawCommitmentCall (P : LeanXmss.PublicParameter) : (SigningRawSpec C).Domain → Prop
  | .inl _ => False
  | .inr input => RawCommitmentInput P input

set_option maxRecDepth 100000 in
theorem alternativeCommitment_newTarget_domain (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (initial final : HashCache C)
    (hinit : CanonicalCommitments seeds P initial) (hle : initial ≤ final)
    (hit : AlternativeCommitment seeds P final) :
    NewTargetHit initial (fun input answer => RawCommitmentInput P input ∧
      LeanXmss.truncateHash answer = commitmentOutputTarget seeds P initial input) final := by
  obtain ⟨e, candidate, canonicalOutput, candidateOutput, _, hcanonical, hcandidate, hne, heq⟩ := hit
  obtain ⟨hc, ⟨output, houtput⟩, hnone⟩ := hinit e
  have hs := cachedRandomizer_stable seeds initial final e hle hc
  have ho : output = canonicalOutput := by
    have hg := hle houtput
    rw [hs, hcanonical] at hg
    exact Option.some.inj hg.symm
  have ht : commitmentTrial P (commitmentInput P e candidate) = some (e, candidate) :=
    (commitmentTrial_eq_some P _ e candidate).mpr rfl
  refine ⟨.hash (commitmentInput P e candidate), candidateOutput,
    hnone candidate (by rwa [hs]), hcandidate, ?_, ?_⟩
  · simp only [RawCommitmentInput, ht, Option.isSome_some, Bool.true_eq]
  · have htarget := commitmentOutputTarget_eq seeds P initial _ e candidate ht
    rw [houtput] at htarget
    exact heq.trans (by simpa only [Option.getD_some, ho] using htarget.symm)

open Classical in
def commitmentExpectedCost (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) : ℝ≥0∞ :=
  XmssSecurity.expectedSimulatedCost privateRoImpl
    (fun input _ => if RawCommitmentCall x.1 input then 1 else 0)
    ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run) ∅

set_option maxRecDepth 100000 in
theorem alternativeCommitment_bound_expected (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun result => AlternativeCommitment x.2.1 x.1 result.2 |
      (simulateQ privateRoImpl ((simulateQ (signingRawCounted prims)
        (SigningDescentProof.finalRun A x)).run)).run ∅] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * commitmentExpectedCost prims A x := by
  classical
  let source := (simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run
  let ghost := rawCommitmentForest x.2.1 x.1
  refine (private_forest_event_mono ghost source ∅
    (fun result => AlternativeCommitment x.2.1 x.1 result.2)
    (fun _ left right hle hh => alternativeCommitment_mono x.2.1 x.1 left right hle hh)).trans ?_
  change _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * XmssSecurity.expectedSimulatedCost privateRoImpl
    (fun input _ => if RawCommitmentCall x.1 input then 1 else 0) source ∅
  rw [← private_prefix_expectedCost ghost source (RawCommitmentCall x.1) ∅,
    ← ENNReal.tsum_mul_left]
  simp only [StateT.run_bind, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro pre
  by_cases hp : pre ∈ support ((simulateQ randomOracle ghost).run ∅)
  · rw [← mul_assoc, mul_comm ((2 ^ 128 : ℝ≥0∞)⁻¹), mul_assoc]
    apply mul_le_mul_left'
    refine le_trans (probEvent_mono fun result hr hh =>
      alternativeCommitment_newTarget_domain x.2.1 x.1 pre.2 result.2
        (rawCommitmentForest_support x.2.1 x.1 pre hp)
        (privateRo_cache_le source pre.2 result hr) hh) ?_
    have hb := privateRo_newTarget_bound source pre.2
      (fun input answer => RawCommitmentInput x.1 input ∧
        LeanXmss.truncateHash answer = commitmentOutputTarget x.2.1 x.1 pre.2 input)
      (fun input => if RawCommitmentInput x.1 input then 1 else 0)
      ((2 ^ 128 : ℝ≥0∞)⁻¹) (fun input => ?_)
    · have he : (fun (input : (SigningRawSpec C).Domain) (_ : HashCache C) =>
          privateTargetCost (fun input => if RawCommitmentInput x.1 input then 1 else 0) input) =
        (fun input _ => if RawCommitmentCall x.1 input then 1 else 0) := by
        funext input cache
        cases input <;> simp [privateTargetCost, RawCommitmentCall]
      rw [he] at hb
      exact hb
    · by_cases hc : RawCommitmentInput x.1 input
      · simp only [hc, true_and, if_true, mul_one]
        change Pr[fun output : XmssSecurity.HashOutput => XmssSecurity.truncateHash output =
          commitmentOutputTarget x.2.1 x.1 pre.2 input | $ᵗ XmssSecurity.HashOutput] ≤
            ((2 ^ 128 : ℝ≥0∞)⁻¹)
        simpa only [XmssSecurity.digestBits, Nat.cast_pow, Nat.cast_ofNat] using
          (XmssSecurity.Rom.uniform_truncate_probability
            (commitmentOutputTarget x.2.1 x.1 pre.2 input)).le
      · simp [hc]
  · simp [probOutput_eq_zero_of_not_mem_support hp]

/-- Unlike a true-opening probe, a different-opening output match admits the
expected commitment-domain charge, jointly over all keys and sessions. -/
theorem openingMatch_bound_expected (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[OpeningMatch prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * commitmentExpectedCost prims A x := by
  rw [exposedRun_eq_raw prims A x]
  exact (openingMatch_map_le prims x _).trans
    (alternativeCommitment_bound_expected prims A x)

def RawOtherCall (P : LeanXmss.PublicParameter) : (SigningRawSpec C).Domain → Prop
  | .inl _ => False
  | .inr input => ¬RawCommitmentInput P input

/-- All chain, leaf, node and encoding hash calls use the complementary
domain, even at another public parameter. -/
theorem rawOtherCall_tweakableHashInput (P P' : LeanXmss.PublicParameter)
    (domain : LeanXmss.HashDomain) (payload : LeanXmss.HashInput) :
    RawOtherCall (C := C) P (.inr (.hash (LeanXmss.tweakableHashInput P' domain payload))) := by
  change ¬((commitmentTrial P (LeanXmss.tweakableHashInput P' domain payload)).isSome = true)
  cases ht : commitmentTrial P (LeanXmss.tweakableHashInput P' domain payload) with
  | none => simp
  | some trial =>
    obtain ⟨e, candidate⟩ := trial
    have he := (commitmentTrial_eq_some P _ e candidate).mp ht
    exact (commitmentInput_ne_tweakableHashInput P P' e candidate domain payload he).elim

theorem rawOtherCall_slot (P : LeanXmss.PublicParameter)
    (seeds : C.Term → LeanXmss.HashOutput) (pairKeys : C.Pair → LeanXmss.HashOutput)
    (slot : TprfSecurityProof.Slot C) :
    RawOtherCall P (.inr (TprfSecurityProof.slotInput seeds pairKeys slot)) := by
  cases slot <;> simp [TprfSecurityProof.slotInput, RawOtherCall, RawCommitmentInput]

open Classical in
def otherExpectedCost (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) : ℝ≥0∞ :=
  XmssSecurity.expectedSimulatedCost privateRoImpl
    (fun input _ => if RawOtherCall x.1 input then 1 else 0)
    ((simulateQ (signingRawCounted prims) (SigningDescentProof.finalRun A x)).run) ∅

theorem outputDomainCosts_le (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    commitmentExpectedCost prims A x + otherExpectedCost prims A x ≤ q := by
  classical
  unfold commitmentExpectedCost otherExpectedCost
  rw [← XmssSecurity.expectedSimulatedCost_add]
  have he : (fun (input : (SigningRawSpec C).Domain) (_ : HashCache C) =>
      (if RawCommitmentCall x.1 input then (1 : ℝ≥0∞) else 0) +
        (if RawOtherCall x.1 input then 1 else 0)) =
      (fun input _ => (rawCallCost input : ℝ≥0∞)) := by
    funext input cache
    cases input with
    | inl n => simp [RawCommitmentCall, RawOtherCall, rawCallCost]
    | inr input =>
      by_cases h : RawCommitmentInput x.1 input <;>
        simp [RawCommitmentCall, RawOtherCall, rawCallCost, h]
  rw [he]
  apply privateRo_expectedCost_le_cap
  exact signingRaw_prefix_raw_cap prims (pure () : OracleComp (Query C →ₒ LeanXmss.HashOutput) Unit)
    A x q hq ((), ∅) (by simp)

end AlternativeCommitments

section ReceiptCache

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {C : Committee}

/-- Each accepted receipt has a codeword-search subrun. Later share queries
can only extend the cache containing that search. -/
theorem signRound2Selection_run_code (prims : Primitives)
    (part : Point → OracleComp (WorldSpec C) LeanXmss.Digest)
    (P : LeanXmss.PublicParameter) (J : C.Quorum) (commitment : LeanXmss.Digest)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest)
    (s : HashCache C × ℕ)
    (r : Option ((LeanXmss.Randomness × LeanXmss.Encoding) ×
      (LeanXmss.ChainIndex → Option LeanXmss.Digest)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (signRound2WithSelection (fun oa => SigningSecurityProof.liftFree oa) part
        P J commitment e message parts)).run s))
    (selected : LeanXmss.Randomness × LeanXmss.Encoding)
    (values : LeanXmss.ChainIndex → Option LeanXmss.Digest)
    (hs : r.1 = some (selected, values)) :
    ∃ rCode, rCode ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (signCodeword P commitment e message (combine J parts)))).run s) ∧
      rCode.1 = some selected ∧ rCode.2.1 ≤ r.2.1 := by
  unfold signRound2WithSelection at hr
  obtain ⟨rCode, hCode, hrest, hle⟩ := run_bind_support_grows prims _ _ s r hr
  refine ⟨rCode, hCode, ?_, hle⟩
  cases hc : rCode.1 with
  | none =>
    simp only [hc, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
    rw [hrest] at hs
    contradiction
  | some chosen =>
    obtain ⟨randomness, encoding⟩ := chosen
    simp only [hc] at hrest
    obtain ⟨rValues, _, hlast⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hrest
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hlast
    rw [hlast] at hs
    exact congrArg some (congrArg Prod.fst (Option.some.inj hs))

/-- Supported tree and codeword runs with caches included in the final cache.
The producer extracts the real subruns; this predicate retains their replay
facts, but does not retain their chronological order or assert freshness. -/
def ReceiptRuns (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (cache : HashCache C) (receipt : Round2Receipt C) : Prop :=
  ∃ (tree : BottomTree) (sTree : HashCache C × ℕ)
    (rTree : Option TreeOutput × HashCache C × ℕ)
    (sCode : HashCache C × ℕ)
    (rCode : Option (LeanXmss.Randomness × LeanXmss.Encoding) × HashCache C × ℕ),
    rTree ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
        top (.bottom (treeOf receipt.key))))).run sTree) ∧
    rTree.1 = some (.bottom tree) ∧ rTree.2.1 ≤ cache ∧
    receipt.commitment = tree.commitment receipt.key ∧
    rCode ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (signCodeword x.1 receipt.commitment receipt.key
        receipt.message receipt.candidate))).run sCode) ∧
    rCode.1 = some (receipt.randomness, receipt.encoding) ∧ rCode.2.1 ≤ cache

theorem ReceiptRuns.mono (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) {cache cache' : HashCache C} (hle : cache ≤ cache')
    (receipt : Round2Receipt C) (hr : ReceiptRuns prims x top cache receipt) :
    ReceiptRuns prims x top cache' receipt := by
  obtain ⟨tree, sTree, rTree, sCode, rCode, ht, hto, htl, hc, hs, hso, hsl⟩ := hr
  exact ⟨tree, sTree, rTree, sCode, rCode, ht, hto, htl.trans hle, hc, hs, hso, hsl.trans hle⟩

/-- An invariant for a stateful oracle followed by the actual counted hash
implementation. The invariant may refer to both state and cache. -/
theorem counted_simulateQ_inv (prims : Primitives) {ι σ α : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (Inv : σ → HashCache C → Prop)
    (step : ∀ input state cache, Inv state cache.1 →
      ∀ result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((handler input).run state)).run cache), Inv result.1.2 result.2.1)
    (source : OracleComp spec α) :
    ∀ state cache, Inv state cache.1 →
      ∀ result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((simulateQ handler source).run state)).run cache), Inv result.1.2 result.2.1 := by
  induction source using OracleComp.inductionOn with
  | pure value =>
    intro state cache hinv result hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst result
    exact hinv
  | query_bind input next ih =>
    intro state cache hinv result hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind] at hr
    simp only [mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    exact ih mid.1.1 mid.1.2 mid.2 (step input state cache hinv mid hmid) result hr

def receiptDealt (x : SigningSecurityProof.Keys3 C) (top : TopTree) :
    Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1
    (dealtKeys x.1 x.2.1 x.2.2) top (fun point => SigningSecurityProof.liftFree (prfValue x.2.1 point))

theorem receiptDealt_bottom (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (b : Fin (2 ^ LeanXmss.layerHeight)) :
    (receiptDealt x top).bottom b =
      (fun | some (.bottom tree) => some tree | _ => none) <$>
        SigningSecurityProof.liftFree
          (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b)) := by
  simp only [receiptDealt, dealtWith, referenceTree_φ]
  rfl

theorem round2WithReceipt_subruns (prims : Primitives)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (st : TsigState C) (i : C.Party) (J : C.Quorum)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest)
    (s : HashCache C × ℕ)
    (r : ((Option (LeanXmss.ChainIndex → Option LeanXmss.Digest) × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (round2WithReceipt (fun oa => SigningSecurityProof.liftFree oa)
        dealt st i J e message parts)).run s))
    (receipt : Round2Receipt C) (hs : r.1.2 = some receipt) :
    ∃ (tree : BottomTree) (rTree : Option BottomTree × HashCache C × ℕ)
      (sCode : HashCache C × ℕ)
      (rCode : Option (LeanXmss.Randomness × LeanXmss.Encoding) × HashCache C × ℕ),
      receipt.key = e ∧
      rTree ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (dealt.bottom (treeOf e))).run s) ∧
      rTree.1 = some tree ∧ rTree.2.1 ≤ r.2.1 ∧ receipt.commitment = tree.commitment e ∧
      rCode ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree (signCodeword dealt.parameter receipt.commitment receipt.key
          receipt.message receipt.candidate))).run sCode) ∧
      rCode.1 = some (receipt.randomness, receipt.encoding) ∧ rCode.2.1 ≤ r.2.1 := by
  unfold round2WithReceipt at hr
  split at hr
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hs
    contradiction
  · obtain ⟨rTree, hTree, hr, hTreeLe⟩ := run_bind_support_grows prims _ _ s r hr
    cases ht : rTree.1 with
    | none =>
      simp only [ht, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr] at hs
      contradiction
    | some tree =>
      simp only [ht] at hr
      obtain ⟨rOwn, _, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
      obtain ⟨rSelected, hSelected, hr, hSelectedLe⟩ := run_bind_support_grows prims _ _ _ r hr
      cases hsel : rSelected.1 with
      | none =>
        simp only [hsel, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        rw [hr] at hs
        contradiction
      | some selected =>
        obtain ⟨⟨randomness, encoding⟩, values⟩ := selected
        simp only [hsel, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        have heq := hs
        rw [hr] at heq
        cases Option.some.inj heq
        obtain ⟨rCode, hCode, hCodeOut, hCodeLe⟩ := signRound2Selection_run_code prims _ _ _ _ _ _ _
          rOwn.2 rSelected (by exact hSelected) (randomness, encoding) values hsel
        exact ⟨tree, rTree, rOwn.2, rCode, rfl, hTree, ht, hTreeLe, rfl,
          hCode, hCodeOut, hCodeLe.trans hSelectedLe⟩

theorem round2WithReceipt_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (st : TsigState C) (i : C.Party) (J : C.Quorum)
    (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) (parts : C.Party → LeanXmss.Digest)
    (s : HashCache C × ℕ)
    (r : ((Option (LeanXmss.ChainIndex → Option LeanXmss.Digest) × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (round2WithReceipt (fun oa => SigningSecurityProof.liftFree oa)
        (receiptDealt x top) st i J e message parts)).run s))
    (receipt : Round2Receipt C) (hs : r.1.2 = some receipt) :
    ReceiptRuns prims x top r.2.1 receipt := by
  obtain ⟨tree, rBottom, sCode, rCode, he, ht, hto, htl, hc, hcode, hco, hcl⟩ :=
    round2WithReceipt_subruns prims _ st i J e message parts s r (by exact hr) receipt hs
  rw [receiptDealt_bottom] at ht
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at ht
  obtain ⟨rTree, htree, rfl⟩ := ht
  have hout : rTree.1 = some (.bottom tree) := by
    cases hrTree : rTree.1 with
    | none => simp [hrTree] at hto
    | some result => cases result <;> simpa [hrTree] using hto
  refine ⟨tree, s, rTree, sCode, rCode, ?_, hout, htl, ?_, ?_, hco, hcl⟩
  · simpa only [he] using htree
  · simpa only [he] using hc
  · exact hcode

theorem signingWithReceipt_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (st : TsigState C) (input : (LocalSpec C + TsigSpec C).Domain)
    (s : HashCache C × ℕ)
    (r : (((LocalSpec C + TsigSpec C).Range input × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (signingWithReceipt (receiptDealt x top) st input)).run s))
    (receipt : Round2Receipt C) (hs : r.1.2 = some receipt) :
    ReceiptRuns prims x top r.2.1 receipt := by
  cases input with
  | inl input =>
    simp only [signingWithReceipt, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨out, _, rfl⟩ := hr
    contradiction
  | inr input =>
    cases input with
    | round2 i J e message parts =>
      exact round2WithReceipt_runs prims x top st i J e message parts s r (by exact hr) receipt hs
    | corrupt i | tree b | round1 i J e message =>
      simp only [signingWithReceipt, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨out, _, rfl⟩ := hr
      contradiction

theorem flaggedReceiptOracles_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (state : TsigState C × Bool) (receipts : List (Round2Receipt C)) (s : HashCache C × ℕ)
    (hinit : ∀ receipt ∈ receipts, ReceiptRuns prims x top s.1 receipt) :
    ∀ r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (flaggedReceiptOracles x (receiptDealt x top)) source).run (state, receipts))).run s),
      ∀ receipt ∈ r.1.2.2, ReceiptRuns prims x top r.2.1 receipt := by
  apply counted_simulateQ_inv prims (flaggedReceiptOracles x (receiptDealt x top))
    (fun state cache => ∀ receipt ∈ state.2, ReceiptRuns prims x top cache receipt) _ source _ s hinit
  intro input state cache hstate result hr
  simp only [flaggedReceiptOracles, StateT.run_mk, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  intro receipt hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · exact ReceiptRuns.mono prims x top
      (SigningCacheProof.countRun_grows prims _ cache out hout) receipt (hstate receipt hold)
  · apply signingWithReceipt_runs prims x top state.1.1 input cache out hout receipt
    simpa only [Option.mem_toList, Option.mem_def] using hnew

theorem flaggedReceiptOracles_forgetFlag (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ st flag receipts,
    (fun result => (result.1, (result.2.1.1, result.2.2))) <$>
      (simulateQ (flaggedReceiptOracles x dealt) source).run ((st, flag), receipts) =
      (simulateQ (signingReceiptOracles dealt) source).run (st, receipts) := by
  induction source using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
    intro st flag receipts
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind, flaggedReceiptOracles,
      signingReceiptOracles, StateT.run_mk, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2 (receiptFlag x st flag input) (receipts ++ result.2.toList)

theorem flaggedReceiptOracles_receipt_bound (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (r : α × (TsigState C × Bool) × List (Round2Receipt C))
    (hr : r ∈ support ((simulateQ (flaggedReceiptOracles x dealt) source).run
      ((SigningCoreProof.tsigInit, false), [])))
    (receipt : Round2Receipt C) (hreceipt : receipt ∈ r.2.2) :
    r.2.1.1.bound receipt.key = some receipt.message ∧
      receipt.party ∈ signersAt r.2.1.1 receipt.key receipt.message := by
  apply signingReceiptOracles_receipt_bound dealt source (r.1, r.2.1.1, r.2.2) _ receipt hreceipt
  rw [← flaggedReceiptOracles_forgetFlag x dealt source SigningCoreProof.tsigInit false [], support_map]
  exact ⟨r, hr, rfl⟩

theorem countRun_support (prims : Primitives) {α : Type} (source : OracleComp (WorldSpec C) α)
    (s : HashCache C × ℕ) (r : α × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) source).run s)) :
    r.1 ∈ support source := by
  apply support_simulateQ_run'_subset (SigningCacheProof.countImpl prims) source s
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

theorem tsigFinish_state (dealt : Dealt C (OracleComp (WorldSpec C)))
    (forgery : LeanXmss.Forgery) (state : TsigState C)
    (r : Bool × TsigState C × LeanXmss.Forgery)
    (hr : r ∈ support (SigningCoreProof.tsigFinish dealt (forgery, state))) :
    r.2 = (state, forgery) := by
  simp only [SigningCoreProof.tsigFinish, mem_support_bind_iff] at hr
  obtain ⟨verified, _, hr⟩ := hr
  split at hr
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, exists_eq_left] at hr
    subst r
    rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, exists_eq_left] at hr
    obtain ⟨honest, _, hr⟩ := hr
    subst r
    rfl

theorem tsigOracles_corrupt_le {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hs : st.corrupt.card ≤ C.t - 1) (hr : r ∈ support ((tsigOracles lift dealt t).run st)) :
    r.2.corrupt.card ≤ C.t - 1 := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;> simp_all [StateT.run_set, StateT.run_pure]
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, run_liftM_comp, bind_map_left,
      mem_support_bind_iff] at hr
    obtain ⟨tree, _, hr⟩ := hr
    cases tree <;> simp_all
    obtain ⟨value, _, rfl⟩ := hr
    exact hs
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure]
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map,
        run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hs
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · simp_all [StateT.run_pure]
    · simp only [StateT.run_bind, run_liftM_comp, bind_map_left, mem_support_bind_iff] at hr
      obtain ⟨tree, _, hr⟩ := hr
      cases tree with
      | none => simp_all [StateT.run_pure]
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left, mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> simp_all [StateT.run_set, StateT.run_pure]

theorem gameOracles_corrupt_le (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C)
    (r : (LocalSpec C + TsigSpec C).Range t × TsigState C)
    (hs : st.corrupt.card ≤ C.t - 1)
    (hr : r ∈ support ((SigningCoreProof.gameOracles dealt t).run st)) :
    r.2.corrupt.card ≤ C.t - 1 := by
  cases t with
  | inl t =>
    change r ∈ support ((fun a => (a, st)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨value, _, rfl⟩ := hr
    exact hs
  | inr t => exact tsigOracles_corrupt_le _ dealt t st r hs hr

theorem flaggedReceiptOracles_corrupt_le (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (flaggedReceiptOracles x dealt) source).run
      ((SigningCoreProof.tsigInit, false), [])), r.2.1.1.corrupt.card ≤ C.t - 1 := by
  apply SeedHitProof.support_simulateQ_inv (flaggedReceiptOracles x dealt)
    (fun state => state.1.1.corrupt.card ≤ C.t - 1)
    _ source _ (by simp [SigningCoreProof.tsigInit])
  intro input state hs result hr
  simp only [flaggedReceiptOracles, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  apply gameOracles_corrupt_le dealt input state.1.1 out.1 hs
  rw [← signingWithReceipt_forget dealt state.1.1 input, support_map]
  exact ⟨out, hout, rfl⟩

theorem receiptFinalRun_corrupt_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : ((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) × List (Round2Receipt C))
    (hr : r ∈ support (receiptFinalRun A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.2 = some (top, state, forgery)) : state.corrupt.card ≤ C.t - 1 := by
  unfold receiptFinalRun at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨topResult, _, hr⟩ := hr
  rcases topResult with _ | (actualTop | bottom)
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hmeta
    contradiction
  · simp only [mem_support_bind_iff] at hr
    obtain ⟨rForger, hForger, hr⟩ := hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨rFinish, hFinish, rfl⟩ := hr
    have hstate := congrArg Prod.fst (tsigFinish_state _ _ _ rFinish hFinish)
    have hfinal := congrArg (fun data => data.2.1) (Option.some.inj hmeta)
    have hb := flaggedReceiptOracles_corrupt_le x _ _ rForger hForger
    dsimp only at hstate hfinal
    rw [← hstate, hfinal] at hb
    exact hb
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hmeta
    contradiction

theorem receiptExposedRun_corrupt_le (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery)) : state.corrupt.card ≤ C.t - 1 :=
  receiptFinalRun_corrupt_le A x r.1
    (countRun_support prims _ (∅, 0) r (by exact hr)) top state forgery hmeta

theorem receiptFinalRun_receipt_bound (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : ((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) × List (Round2Receipt C))
    (hr : r ∈ support (receiptFinalRun A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.2 = some (top, state, forgery)) (receipt : Round2Receipt C) (hreceipt : receipt ∈ r.2) :
    state.bound receipt.key = some receipt.message ∧
      receipt.party ∈ signersAt state receipt.key receipt.message := by
  unfold receiptFinalRun at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨topResult, _, hr⟩ := hr
  rcases topResult with _ | (actualTop | bottom)
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hmeta
    contradiction
  · simp only [mem_support_bind_iff] at hr
    obtain ⟨rForger, hForger, hr⟩ := hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨rFinish, hFinish, rfl⟩ := hr
    have hstate := congrArg Prod.fst (tsigFinish_state _ _ _ rFinish hFinish)
    have hfinal := congrArg (fun data => data.2.1) (Option.some.inj hmeta)
    have hb := flaggedReceiptOracles_receipt_bound x _ _ rForger hForger receipt hreceipt
    dsimp only at hstate hfinal
    rw [← hstate, hfinal] at hb
    exact hb
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hmeta
    contradiction

theorem receiptExposedRun_receipt_bound (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery))
    (receipt : Round2Receipt C) (hreceipt : receipt ∈ r.1.2) :
    state.bound receipt.key = some receipt.message ∧
      receipt.party ∈ signersAt state receipt.key receipt.message :=
  receiptFinalRun_receipt_bound A x r.1
    (countRun_support prims _ (∅, 0) r (by exact hr)) top state forgery hmeta receipt hreceipt

theorem receiptFinalRun_runs (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (s : HashCache C × ℕ)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (receiptFinalRun A x)).run s))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery)) :
    ∀ receipt ∈ r.1.2, ReceiptRuns prims x top r.2.1 receipt := by
  unfold receiptFinalRun at hr
  obtain ⟨rTop, _, hr⟩ := SigningCacheProof.run_bind_support prims _ _ s r hr
  cases ht : rTop.1 with
  | none =>
    simp only [ht, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hmeta
    contradiction
  | some result =>
    cases result with
    | bottom tree =>
      simp only [ht, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr] at hmeta
      contradiction
    | top actualTop =>
      simp only [ht] at hr
      obtain ⟨rForger, hForger, hr, hGrow⟩ := run_bind_support_grows prims _ _ _ r hr
      have hinv := flaggedReceiptOracles_runs prims x actualTop
        (A ⟨actualTop.root, x.1⟩ actualTop) (SigningCoreProof.tsigInit, false) [] rTop.2
        (by simp) rForger (by exact hForger)
      simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨rFinish, _, rfl⟩ := hr
      have htop : actualTop = top := congrArg Prod.fst (Option.some.inj hmeta)
      subst top
      intro receipt hmem
      exact ReceiptRuns.mono prims x actualTop hGrow receipt (hinv receipt hmem)

theorem receiptExposedRun_runs (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery)) :
    ∀ receipt ∈ r.1.2, ReceiptRuns prims x top r.2.1 receipt :=
  receiptFinalRun_runs prims A x (∅, 0) r (by exact hr) top state forgery hmeta

theorem hom_dealtWith_bottom {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (hom : m →ᵐ n)
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α)
    (P : LeanXmss.PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → m LeanXmss.Digest) (b : Fin (2 ^ LeanXmss.layerHeight)) :
    hom ((dealtWith lift P keys top value).bottom b) =
      (dealtWith (fun oa => hom (lift oa)) P keys top (fun point => hom (value point))).bottom b := by
  simp only [dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]

def receiptBottomResult : Option TreeOutput → Option BottomTree
  | some (.bottom tree) => some tree
  | _ => none

theorem dealtWith_bottom_result {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α)
    (P : LeanXmss.PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → m LeanXmss.Digest) (b : Fin (2 ^ LeanXmss.layerHeight)) :
    (dealtWith lift P keys top value).bottom b =
      receiptBottomResult <$> referenceTree (fun oa => lift (tweakable oa)) value P top (.bottom b) := rfl

set_option maxHeartbeats 200000 in
theorem receiptDealt_bottom_replay (prims : Primitives) (h : Query C → LeanXmss.HashOutput)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree) (b : Fin (2 ^ LeanXmss.layerHeight)) :
    (dealtWith (m := Id) (fun oa => D prims h oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top
      (fun point => D prims h (prfValue x.2.1 point))).bottom b =
    receiptBottomResult (D prims h (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b))) := by
  calc
    _ = D prims h ((dealtWith (fun oa => oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top
        (prfValue x.2.1)).bottom b) := by
      exact (hom_dealtWith_bottom (SigningCacheProof.fixedHom prims h) (fun oa => oa)
        x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1) b).symm
    _ = D prims h (receiptBottomResult <$>
        referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b)) := by
      exact congrArg (D prims h) (dealtWith_bottom_result (fun oa => oa)
        x.1 (dealtKeys x.1 x.2.1 x.2.2) top (prfValue x.2.1) b)
    _ = _ := D_map h receiptBottomResult _

/-- Actual accepted sessions select exactly the input used by the cache
replay, once their candidate is known to be the canonical randomizer. -/
theorem ReceiptRuns.selected (prims : Primitives) (z : SigningDescentProof.FinalState C)
    (receipt : Round2Receipt C) (hr : ReceiptRuns prims z.keys z.top z.cache receipt)
    (he : receipt.key = z.key) (hb : z.state.bound receipt.key = some receipt.message)
    (hc : receipt.candidate = D prims z.answers
      (prfValue z.keys.2.1 (.randomizer LeanXmss.bottomLayer receipt.key))) :
    z.selected prims = some (receipt.message, receipt.randomness) := by
  obtain ⟨tree, sTree, rTree, sCode, rCode, hTree, hTreeOut, hTreeLe, hcommit,
    hCode, hCodeOut, hCodeLe⟩ := hr
  have ht := (SigningCacheProof.run_liftFree prims _ sTree rTree (by exact hTree)
    z.answers (SigningCacheProof.agrees_answersOf hTreeLe)).symm.trans hTreeOut
  have hs := (SigningCacheProof.run_liftFree prims _ sCode rCode (by exact hCode)
    z.answers (SigningCacheProof.agrees_answersOf hCodeLe)).symm.trans hCodeOut
  unfold SigningDescentProof.FinalState.selected SigningDescentProof.FinalState.bottomTree
    SigningDescentProof.FinalState.dealt
  rw [← he, hb, receiptDealt_bottom_replay, ht]
  simp only [receiptBottomResult]
  change (do
    let selected ← D prims z.answers (signCodeword z.keys.1 (tree.commitment receipt.key)
      receipt.key receipt.message (D prims z.answers
        (prfValue z.keys.2.1 (.randomizer LeanXmss.bottomLayer receipt.key))))
    pure (receipt.message, selected.1)) = some (receipt.message, receipt.randomness)
  rw [← hc, ← hcommit, hs]
  rfl

def receiptRecords (receipts : List (Round2Receipt C)) : List (TprfSecurityProof.EvalRecord C) :=
  receipts.flatMap Round2Receipt.records

theorem receiptRecords_queriers_subset (receipts : List (Round2Receipt C)) (state : TsigState C)
    (hreceipts : ∀ receipt ∈ receipts,
      receipt.party ∈ signersAt state receipt.key receipt.message)
    (e : LeanXmss.KeyIndex) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (message : LeanXmss.Message) :
    state.corrupt ∪ TprfSecurityProof.recordQueriers (receiptRecords receipts)
      (.chain LeanXmss.bottomLayer e chain digit) message ⊆ signersAt state e message := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ hi
  · simp only [TprfSecurityProof.recordQueriers, List.mem_toFinset, List.mem_map,
      List.mem_filter, decide_eq_true_eq] at hi
    obtain ⟨record, ⟨hm, hx, hmessage⟩, rfl⟩ := hi
    obtain ⟨receipt, hr, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨selectedChain, answer, _, rfl⟩ := mem_round2ReplyRecords
      receipt.party receipt.quorum receipt.key receipt.message receipt.encoding receipt.values record hm
    have he : receipt.key = e := (Point.chain.inj hx).2.1
    change receipt.message = message at hmessage
    simpa only [he, hmessage] using hreceipts receipt hr

/-- With a common selected encoding, other digits have no honest chain-share
records, even when the total number of successful signing calls is large. -/
theorem receiptRecords_queriers_eq_empty (receipts : List (Round2Receipt C))
    (e : LeanXmss.KeyIndex) (encoding : LeanXmss.Encoding)
    (hencoding : ∀ receipt ∈ receipts, receipt.key = e → receipt.encoding = encoding)
    (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit) (hdigit : digit ≠ encoding chain)
    (message : LeanXmss.Message) :
    TprfSecurityProof.recordQueriers (receiptRecords receipts)
      (.chain LeanXmss.bottomLayer e chain digit) message = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [TprfSecurityProof.recordQueriers, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨record, ⟨hm, hx, _⟩, _⟩ := hi
  obtain ⟨receipt, hr, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨selectedChain, answer, _, rfl⟩ := mem_round2ReplyRecords
    receipt.party receipt.quorum receipt.key receipt.message receipt.encoding receipt.values record hm
  obtain ⟨_, he, hchain, hd⟩ := Point.chain.inj hx
  apply hdigit
  exact hd.symm.trans (by rw [hencoding receipt hr he, hchain])

theorem receiptExposedRun_queriers_subset (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery))
    (e : LeanXmss.KeyIndex) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (message : LeanXmss.Message) :
    state.corrupt ∪ TprfSecurityProof.recordQueriers (receiptRecords r.1.2)
      (.chain LeanXmss.bottomLayer e chain digit) message ⊆ signersAt state e message :=
  receiptRecords_queriers_subset r.1.2 state
    (fun receipt hreceipt => (receiptExposedRun_receipt_bound prims A x r hr top state forgery
      hmeta receipt hreceipt).2) e chain digit message

end ReceiptCache

set_option maxRecDepth 100000 in
/-- Supported tree generation followed by an accepted noncanonical opening
witnesses the final opening event. Both subruns may be followed by arbitrary
cache-extending work; no freshness of the commitment call is assumed. -/
theorem openingMatch_of_runs {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C)
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.2 = some (top, state, forgery))
    (htop : TopFacts prims (SigningCacheProof.answersOf r.2.1) x.2.1 x.1 top)
    (tree : BottomTree) (sTree : HashCache C × ℕ)
    (rTree : Option TreeOutput × HashCache C × ℕ)
    (hTree : rTree ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
        top (.bottom (treeOf forgery.signature.leafIndex))))).run sTree))
    (hTreeOut : rTree.1 = some (.bottom tree)) (hTreeLe : rTree.2.1 ≤ r.2.1)
    (message : LeanXmss.Message) (candidate : LeanXmss.Digest)
    (selected : LeanXmss.Randomness × LeanXmss.Encoding)
    (sCode : HashCache C × ℕ)
    (rCode : Option (LeanXmss.Randomness × LeanXmss.Encoding) × HashCache C × ℕ)
    (hCode : rCode ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (signCodeword x.1
        (tree.commitment forgery.signature.leafIndex) forgery.signature.leafIndex
        message candidate))).run sCode))
    (hCodeOut : rCode.1 = some selected) (hCodeLe : rCode.2.1 ≤ r.2.1)
    (hne : candidate ≠ D prims (SigningCacheProof.answersOf r.2.1)
      (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer forgery.signature.leafIndex))) :
    OpeningMatch prims x r := by
  have haTree := SigningCacheProof.agrees_answersOf hTreeLe
  have haCode := SigningCacheProof.agrees_answersOf hCodeLe
  obtain ⟨hterms, canonicalOutput, hcanonical⟩ := run_bottom_commitment_cached prims
    x.2.1 x.1 top forgery.signature.leafIndex sTree rTree (by exact hTree) _ haTree
  have hcommit := run_bottom_commitment_eq prims x.2.1 x.1 top
    forgery.signature.leafIndex sTree rTree (by exact hTree) _ haTree htop tree hTreeOut
  obtain ⟨candidateOutput, hcandidate⟩ := caches_signCodeword prims x.1
    (tree.commitment forgery.signature.leafIndex) forgery.signature.leafIndex message
    candidate sCode rCode (by exact hCode)
  have haccepted := (SigningCacheProof.run_liftFree prims _ sCode rCode
    (by exact hCode) _ haCode).symm.trans hCodeOut
  have heq := signCodeword_some_commitment prims (SigningCacheProof.answersOf r.2.1) x.1
    (tree.commitment forgery.signature.leafIndex) forgery.signature.leafIndex message
    candidate selected haccepted
  refine ⟨top, state, forgery, hmeta, ?_⟩
  exact ⟨(fun T => by obtain ⟨v, hv⟩ := hterms T; exact ⟨v, hTreeLe hv⟩),
    candidate, canonicalOutput, candidateOutput, hTreeLe hcanonical,
    hCodeLe hcandidate, hne, heq.trans hcommit⟩

set_option maxRecDepth 100000 in
/-- At the forged key, the absence of a different opening forces every
executed receipt to use the canonical randomizer and its actual selected trial. -/
theorem ReceiptRuns.canonical {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C)
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.2 = some (top, state, forgery))
    (htop : TopFacts prims (SigningCacheProof.answersOf r.2.1) x.2.1 x.1 top)
    (receipt : Round2Receipt C) (hr : ReceiptRuns prims x top r.2.1 receipt)
    (he : receipt.key = forgery.signature.leafIndex) (hn : ¬OpeningMatch prims x r) :
    receipt.candidate = D prims (SigningCacheProof.answersOf r.2.1)
      (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer receipt.key)) ∧
    E prims (SigningCacheProof.answersOf r.2.1)
      (grind x.1 LeanXmss.bottomLayer receipt.key (LeanXmss.bytesLE 32 receipt.message)
        (LeanXmss.truncateHash (SigningCacheProof.answersOf r.2.1
          (.hash (randomizerInput x.1 LeanXmss.bottomLayer receipt.key receipt.candidate
            (LeanXmss.bytesLE 32 receipt.message))))) LeanXmss.randomizerAttemptLimit 0) =
      some (receipt.randomness, receipt.encoding) := by
  obtain ⟨tree, sTree, rTree, sCode, rCode, hTree, hTreeOut, hTreeLe, hcommit,
    hCode, hCodeOut, hCodeLe⟩ := hr
  have hc : receipt.candidate = D prims (SigningCacheProof.answersOf r.2.1)
      (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer receipt.key)) := by
    by_contra hne
    apply hn
    apply openingMatch_of_runs prims x r top state forgery hmeta htop tree sTree rTree
      (by simpa only [← he] using hTree) hTreeOut hTreeLe receipt.message receipt.candidate
      (receipt.randomness, receipt.encoding) sCode rCode
      (by simpa only [← he, ← hcommit] using hCode) hCodeOut hCodeLe
    simpa only [← he] using hne
  refine ⟨hc, ?_⟩
  have htree := run_bottom_commitment_eq prims x.2.1 x.1 top receipt.key sTree rTree
    (by exact hTree) _ (SigningCacheProof.agrees_answersOf hTreeLe) htop tree hTreeOut
  have hcode := (SigningCacheProof.run_liftFree prims _ sCode rCode
    (by exact hCode) _ (SigningCacheProof.agrees_answersOf hCodeLe)).symm.trans hCodeOut
  have hcmt : receipt.commitment = LeanXmss.truncateHash
      (SigningCacheProof.answersOf r.2.1 (.hash (commitmentInput x.1 receipt.key receipt.candidate))) := by
    rw [hcommit, htree, hc]
  rw [D_signCodeword (prims := prims) (h := SigningCacheProof.answersOf r.2.1)
    _ _ _ _ _ hcmt] at hcode
  exact hcode

set_option maxRecDepth 100000 in
theorem receiptExposedRun_canonical {C : Committee} (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery))
    (htop : TopFacts prims (SigningCacheProof.answersOf r.2.1) x.2.1 x.1 top)
    (receipt : Round2Receipt C) (hreceipt : receipt ∈ r.1.2)
    (he : receipt.key = forgery.signature.leafIndex)
    (hn : ¬OpeningMatch prims x (r.1.1, r.2)) :
    receipt.candidate = D prims (SigningCacheProof.answersOf r.2.1)
      (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer receipt.key)) :=
  (ReceiptRuns.canonical prims x (r.1.1, r.2) top state forgery hmeta htop receipt
    (receiptExposedRun_runs prims A x r hr top state forgery hmeta receipt hreceipt) he hn).1

set_option maxRecDepth 100000 in
theorem receiptExposedRun_topFacts {C : Committee} (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x))
    (hwin : r.1.1.1 = (true, false))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery)) :
    TopFacts prims (SigningCacheProof.answersOf r.2.1) x.2.1 x.1 top := by
  have horiginal : (r.1.1, r.2) ∈ support (SigningDescentProof.exposedRun prims A x) := by
    rw [← receiptExposedRun_forget prims A x, support_map]
    exact ⟨r, hr, rfl⟩
  obtain ⟨top', state', forgery', hm, hg, _, _⟩ :=
    SigningCacheProof.exposedRun_facts prims A x (r.1.1, r.2) horiginal hwin
  have he : top' = top := congrArg Prod.fst (Option.some.inj (hm.symm.trans hmeta))
  subst top'
  obtain ⟨generated, hgen, hchain, hroot⟩ :=
    D_refTop (prims := prims) (h := SigningCacheProof.answersOf r.2.1) x.1 x.2.1 emptyTop
  have he : generated = top := TreeOutput.top.inj (Option.some.inj (hgen.symm.trans hg))
  subst generated
  exact ⟨hchain, hroot⟩

theorem E_messageDigest_cache {C : Committee} (prims : Primitives) (cache : HashCache C)
    (P : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (randomness : LeanXmss.Randomness) :
    E prims (SigningCacheProof.answersOf cache)
      (LeanXmss.Concrete.messageDigest P LeanXmss.bottomLayer e (LeanXmss.bytesLE 32 message) randomness) =
    XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView cache) P e (message, randomness) := by
  rw [SigningCacheProof.E_eval, XmssSecurity.Bridge.messageDigest_bottom]
  exact XmssSecurity.Concrete.CacheReplay.eval_encodingHash _ P e message randomness

set_option maxRecDepth 100000 in
/-- Every actual accepted session at the forged key has precisely the
selected input and codeword of the root residual's honest key. -/
theorem receiptExposedRun_selectedEncoding {C : Committee} (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x)) (hwin : r.1.1.1 = (true, false))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery))
    (receipt : Round2Receipt C) (hreceipt : receipt ∈ r.1.2)
    (he : receipt.key = forgery.signature.leafIndex)
    (hn : ¬OpeningMatch prims x (r.1.1, r.2)) :
    let z := finalOf x (r.1.1, r.2) top state forgery
    z.selected prims = some (receipt.message, receipt.randomness) ∧
    SigningDescentProof.selectedEncoding z.cache x.1 z.key (z.honestKey prims) = some receipt.encoding := by
  let z := finalOf x (r.1.1, r.2) top state forgery
  have htop := receiptExposedRun_topFacts prims A x r hr hwin top state forgery hmeta
  have hruns := receiptExposedRun_runs prims A x r hr top state forgery hmeta receipt hreceipt
  have hcanon := ReceiptRuns.canonical prims x (r.1.1, r.2) top state forgery hmeta htop receipt hruns he hn
  have hb := (receiptExposedRun_receipt_bound prims A x r hr top state forgery hmeta receipt hreceipt).1
  have hs : z.selected prims = some (receipt.message, receipt.randomness) :=
    ReceiptRuns.selected prims z receipt hruns he hb hcanon.1
  refine ⟨hs, ?_⟩
  have hd := E_grind_spec (prims := prims) (h := SigningCacheProof.answersOf r.2.1)
    _ _ _ _ _ _ _ _ _ hcanon.2
  rw [E_messageDigest_cache, XmssSecurity.Bridge.decode_eq] at hd
  change (z.selected prims).bind _ = some receipt.encoding
  rw [hs]
  change XmssSecurity.TargetSum.decodeDigest
    (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView r.2.1) x.1
      forgery.signature.leafIndex (receipt.message, receipt.randomness)) = some receipt.encoding
  rw [he] at hd
  exact hd

set_option maxRecDepth 100000 in
/-- Every bottom coordinate strictly below the root descent's opened digit
is still below threshold in the actual receipt view. No assumption is made
about openings or receipts at unrelated keys. -/
theorem receiptExposedRun_chain_safe {C : Committee} (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) ×
      List (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support (receiptExposedRun prims A x)) (hwin : r.1.1.1 = (true, false))
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.1.2 = some (top, state, forgery))
    (hn : ¬OpeningMatch prims x (r.1.1, r.2))
    (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (hlt : digit.val < SigningDescentProof.bottomOpened r.2.1 x.1 forgery.signature.leafIndex
      ((finalOf x (r.1.1, r.2) top state forgery).honestKey prims) chain)
    (message : LeanXmss.Message) :
    (state.corrupt ∪ TprfSecurityProof.recordQueriers (receiptRecords r.1.2)
      (.chain LeanXmss.bottomLayer forgery.signature.leafIndex chain digit) message).card ≤ C.t - 1 := by
  let z := finalOf x (r.1.1, r.2) top state forgery
  by_cases hempty : TprfSecurityProof.recordQueriers (receiptRecords r.1.2)
      (.chain LeanXmss.bottomLayer forgery.signature.leafIndex chain digit) message = ∅
  · rw [hempty, Finset.union_empty]
    exact receiptExposedRun_corrupt_le prims A x r hr top state forgery hmeta
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    simp only [TprfSecurityProof.recordQueriers, List.mem_toFinset, List.mem_map,
      List.mem_filter, decide_eq_true_eq] at hi
    obtain ⟨record, ⟨hm, hx, hmessage⟩, _⟩ := hi
    obtain ⟨receipt, hreceipt, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨selectedChain, answer, _, rfl⟩ := mem_round2ReplyRecords
      receipt.party receipt.quorum receipt.key receipt.message receipt.encoding receipt.values record hm
    obtain ⟨_, he, hchain, hd⟩ := Point.chain.inj hx
    change receipt.message = message at hmessage
    have hselected := (receiptExposedRun_selectedEncoding prims A x r hr hwin top state forgery
      hmeta receipt hreceipt he hn).2
    have hreleased : (z.honestKey prims).released = false := by
      by_contra hfalse
      have htrue := Bool.eq_true_of_not_eq_false hfalse
      have hopen := SigningDescentProof.bottomOpened_of_released r.2.1 x.1 forgery.signature.leafIndex
        (z.honestKey prims) htrue hselected
      have heq := congrFun hopen chain
      rw [heq] at hlt
      have hd' : receipt.encoding chain = digit := by simpa only [hchain] using hd
      rw [hd'] at hlt
      exact (Nat.lt_irrefl _ hlt)
    have hb := (receiptExposedRun_receipt_bound prims A x r hr top state forgery
      hmeta receipt hreceipt).1
    rw [he, hmessage] at hb
    change (match state.bound forgery.signature.leafIndex with
      | some boundMessage => decide (C.t ≤ (signersAt state forgery.signature.leafIndex boundMessage).card)
      | none => false) = false at hreleased
    rw [hb] at hreleased
    have hsigners : (signersAt state forgery.signature.leafIndex message).card < C.t := by
      exact Nat.lt_of_not_ge (of_decide_eq_false hreleased)
    have hcard := Finset.card_le_card (receiptExposedRun_queriers_subset prims A x r hr top state forgery
      hmeta forgery.signature.leafIndex chain digit message)
    omega

section CompleteShareView

open Classical TprfSecurityProof
set_option maxRecDepth 100000
variable {C : Committee}

def publicShareView (x : SigningSecurityProof.Keys3 C)
    (receipts : List (Round2Receipt C)) (log : SigningLog C)
    (released : Finset Point) : ShareViewData C :=
  ⟨round1Records log ++ receiptRecords receipts, publicSlotReads x log, released⟩

theorem recordQueriers_append_lists (left right : List (EvalRecord C))
    (point : Point) (message : LeanXmss.Message) :
    recordQueriers (left ++ right) point message =
      recordQueriers left point message ∪ recordQueriers right point message := by
  simp only [recordQueriers, List.filter_append, List.map_append, List.toFinset_append]

theorem receiptRecords_randomizer_queriers (receipts : List (Round2Receipt C))
    (lay : LeanXmss.Layer) (e : LeanXmss.KeyIndex) (message : LeanXmss.Message) :
    recordQueriers (receiptRecords receipts) (.randomizer lay e) message = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [recordQueriers, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hi
  obtain ⟨record, ⟨hr, hx, _⟩, _⟩ := hi
  obtain ⟨receipt, _, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨chain, answer, _, rfl⟩ := mem_round2ReplyRecords receipt.party receipt.quorum
    receipt.key receipt.message receipt.encoding receipt.values record hr
  cases hx

theorem publicShareView_chain_queriers (x : SigningSecurityProof.Keys3 C)
    (receipts : List (Round2Receipt C)) (log : SigningLog C) (released : Finset Point)
    (lay : LeanXmss.Layer) (e : LeanXmss.KeyIndex) (chain : LeanXmss.ChainIndex)
    (digit : LeanXmss.Digit) (message : LeanXmss.Message) :
    recordQueriers (publicShareView x receipts log released).records (.chain lay e chain digit) message =
      recordQueriers (receiptRecords receipts) (.chain lay e chain digit) message := by
  simp only [publicShareView, recordQueriers_append_lists, round1Records_chain_queriers,
    Finset.empty_union]

/-- Randomizer shares expose no value at an unbound key. This is the point
where a later first binding can still install the hidden randomizer. -/
theorem publicShareView_unbound_queriers (x : SigningSecurityProof.Keys3 C)
    (receipts : List (Round2Receipt C)) (log : SigningLog C) (released : Finset Point)
    (st : TsigState C) (hb : Round1Bound st log) (e : LeanXmss.KeyIndex)
    (hu : st.bound e = none) (message : LeanXmss.Message) :
    recordQueriers (publicShareView x receipts log released).records
      (.randomizer LeanXmss.bottomLayer e) message = ∅ := by
  simp only [publicShareView, recordQueriers_append_lists,
    round1Records_unbound_queriers st log hb e hu message, receiptRecords_randomizer_queriers,
    Finset.empty_union]

def publicShareView_releaseSafe (x : SigningSecurityProof.Keys3 C)
    (receipts : List (Round2Receipt C)) (log : SigningLog C) (released : Finset Point)
    (D : Finset C.Party) (point : Point)
    (hq : ∀ message, (D ∪ recordQueriers
      (publicShareView x receipts log released).records point message).card ≤ C.t - 1)
    (hr : ∀ read ∈ publicSlotReads x log, Revealed D (slotKey read.1)) :
    (publicShareView x receipts log released).ReleaseSafe point := by
  have hD : D.card ≤ C.t - 1 := (Finset.card_le_card Finset.subset_union_left).trans (hq 0)
  apply Classical.choice
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq hD (by simp [Committee.n]; omega)
  exact ⟨⟨D, ⟨T, hT⟩, hDT, hq, hr⟩⟩

theorem publicReceiptExposedRun_chain_quorum (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r)
    (hr : r ∈ support (publicReceiptExposedRun prims A x))
    (hwin : r.1.1.1.1 = (true, false))
    (top : TopTree) (st : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.1.1.2 = some (top, st, forgery))
    (hn : ¬OpeningMatch prims x (r.1.1.1, r.2))
    (released : Finset Point) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (hlt : digit.val < SigningDescentProof.bottomOpened r.2.1 x.1 forgery.signature.leafIndex
      ((finalOf x (r.1.1.1, r.2) top st forgery).honestKey prims) chain)
    (message : LeanXmss.Message) :
    (st.corrupt ∪ recordQueriers (publicShareView x r.1.1.2 r.1.2 released).records
      (.chain LeanXmss.bottomLayer forgery.signature.leafIndex chain digit) message).card ≤ C.t - 1 := by
  rw [publicShareView_chain_queriers]
  apply receiptExposedRun_chain_safe prims A x (r.1.1, r.2) _ hwin top st forgery hm hn chain digit
    hlt message
  rw [← publicReceiptExposedRun_forget, support_map]
  exact ⟨r, hr, rfl⟩

/-- The complete public share transcript, including randomizer replies and
adversarial raw reads, permits refreshing each unopened bottom coordinate.
The public hash forest still needs its separate programmed-oracle coupling. -/
theorem publicReceiptExposedRun_chain_releaseSafe (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r)
    (hr : r ∈ support (publicReceiptExposedRun prims A x))
    (hwin : r.1.1.1.1 = (true, false))
    (top : TopTree) (st : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.1.1.2 = some (top, st, forgery))
    (hn : ¬OpeningMatch prims x (r.1.1.1, r.2))
    (released : Finset Point) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (hlt : digit.val < SigningDescentProof.bottomOpened r.2.1 x.1 forgery.signature.leafIndex
      ((finalOf x (r.1.1.1, r.2) top st forgery).honestKey prims) chain) :
    Nonempty ((publicShareView x r.1.1.2 r.1.2 released).ReleaseSafe
      (.chain LeanXmss.bottomLayer forgery.signature.leafIndex chain digit)) := by
  exact ⟨publicShareView_releaseSafe x _ _ _ st.corrupt _
    (publicReceiptExposedRun_chain_quorum prims A x r hr hwin top st forgery hm hn
      released chain digit hlt)
    ((publicReceiptExposedRun_public_view prims A x r hr top st forgery hm).2
      (congrArg Prod.snd hwin))⟩

theorem publicReceiptExposedRun_unbound_releaseSafe (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r)
    (hr : r ∈ support (publicReceiptExposedRun prims A x))
    (hf : r.1.1.1.1.2 = false)
    (top : TopTree) (st : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.1.1.2 = some (top, st, forgery))
    (released : Finset Point) (key : LeanXmss.KeyIndex) (hu : st.bound key = none) :
    Nonempty ((publicShareView x r.1.1.2 r.1.2 released).ReleaseSafe
      (.randomizer LeanXmss.bottomLayer key)) := by
  have hv := publicReceiptExposedRun_public_view prims A x r hr top st forgery hm
  refine ⟨publicShareView_releaseSafe x _ _ _ st.corrupt _ ?_ (hv.2 hf)⟩
  intro message
  rw [publicShareView_unbound_queriers x _ _ _ st hv.1 key hu message, Finset.union_empty]
  apply receiptExposedRun_corrupt_le prims A x (r.1.1, r.2) _ top st forgery hm
  rw [← publicReceiptExposedRun_forget, support_map]
  exact ⟨r, hr, rfl⟩

end CompleteShareView

/-- Exactly the top-layer branch of `SigningDescentProof.Partner`. Standard
leanVM places this branch in its output-collision lane, not its bottom encoding
monitor (`CappedTop.topEncodingCollision_afterKeygen`). -/
def TopPartner {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := finalOf x r top state forgery
    let hk := z.honestKey prims
    let signature := XmssSecurity.Bridge.toModelSig forgery.signature
    ∃ encoding, XmssSecurity.TargetSum.decodeDigest
        (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
          x.1 z.key (forgery.message, signature.randomness)) = some encoding ∧
      SigningDescentProof.topSignedInput z.cache x.1 z.key hk ≠
        (SigningDescentProof.forgedRoot z.cache x.1 z.key encoding signature, signature.top.randomness) ∧
      XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView z.cache)
          x.1 (XmssSecurity.topKeyOf z.key) (SigningDescentProof.topSignedInput z.cache x.1 z.key hk) =
        XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView z.cache)
          x.1 (XmssSecurity.topKeyOf z.key)
          (SigningDescentProof.forgedRoot z.cache x.1 z.key encoding signature, signature.top.randomness)

/-- A successfully decoded top digest cannot come from the cache's default
zero: zero is not a target-sum codeword. -/
theorem topEncodingInput_cached_of_decode_some
    (cache : QueryCache XmssSecurity.HashSpec) (parameter : XmssSecurity.PublicParameter)
    (key : XmssSecurity.TopIndex) (payload : XmssSecurity.Digest × XmssSecurity.Randomness)
    (encoding : XmssSecurity.Encoding)
    (hdecode : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.topEncodingHash cache parameter key payload) = some encoding) :
    ∃ output, cache (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload) = some output := by
  cases hc : cache (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload) with
  | some output => exact ⟨output, rfl⟩
  | none =>
    rw [XmssSecurity.Concrete.CacheView.topEncodingHash, XmssSecurity.Concrete.CacheView.digestAt,
      hc, XmssSecurity.TargetSum.decodeDigest_zero_eq_none] at hdecode
    contradiction

set_option maxRecDepth 100000 in
/-- On a supported winning run, both sides of a top-partner equality are
cached. This rules out the apparent free match from two default-zero reads. -/
theorem topPartner_inputs_cached {C : Committee} (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (r : Outcome C)
    (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.2 = some (top, state, forgery)) (encoding : XmssSecurity.Encoding)
    (hdecode : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView r.2.1)
        x.1 forgery.signature.leafIndex (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)) = some encoding)
    (heq : XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView r.2.1)
        x.1 (XmssSecurity.topKeyOf forgery.signature.leafIndex)
        (SigningDescentProof.topSignedInput r.2.1 x.1 forgery.signature.leafIndex
          ((finalOf x r top state forgery).honestKey prims)) =
      XmssSecurity.Concrete.CacheView.topEncodingHash (SigningDescentProof.thView r.2.1)
        x.1 (XmssSecurity.topKeyOf forgery.signature.leafIndex)
        (SigningDescentProof.forgedRoot r.2.1 x.1 forgery.signature.leafIndex encoding
          (XmssSecurity.Bridge.toModelSig forgery.signature), (XmssSecurity.Bridge.toModelSig forgery.signature).top.randomness)) :
    (∃ output, SigningDescentProof.thView r.2.1
      (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 (XmssSecurity.topKeyOf forgery.signature.leafIndex)
        (SigningDescentProof.topSignedInput r.2.1 x.1 forgery.signature.leafIndex
          ((finalOf x r top state forgery).honestKey prims))) = some output) ∧
    (∃ output, SigningDescentProof.thView r.2.1
      (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 (XmssSecurity.topKeyOf forgery.signature.leafIndex)
        (SigningDescentProof.forgedRoot r.2.1 x.1 forgery.signature.leafIndex encoding
          (XmssSecurity.Bridge.toModelSig forgery.signature), (XmssSecurity.Bridge.toModelSig forgery.signature).top.randomness)) = some output) := by
  obtain ⟨top', state', forgery', hmeta', _, hresolved, _⟩ :=
    SigningCacheProof.exposedRun_facts prims A x r hr hwin
  rw [hmeta] at hmeta'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmeta')
  have hverified := (XmssSecurity.Concrete.CacheReplay.eval_verify _ _ _ _ _).symm.trans
    (SigningCacheProof.resolves_value hresolved)
  obtain ⟨encoding', hdecode', htop⟩ :=
    (XmssSecurity.Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hverified
  have he : encoding' = encoding := Option.some.inj (hdecode'.symm.trans hdecode)
  subst encoding'
  obtain ⟨topEncoding, htopDecode, _⟩ :=
    (XmssSecurity.Concrete.verifyTopFromCache_eq_true_iff _ _ _ _ _).mp htop
  have hhonest := heq.symm ▸ htopDecode
  exact ⟨topEncodingInput_cached_of_decode_some _ _ _ _ _ hhonest,
    topEncodingInput_cached_of_decode_some _ _ _ _ _ htopDecode⟩

/-- One output-target lane: chain/leaf/node hits, different commitment
preimages, and top digest partners. The input domains keep their targets apart. -/
def WinOutput {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  WinHit prims x r ∨ (WinGuessPartner prims x r ∧ (OpeningMatch prims x r ∨ TopPartner prims x r))

/-- Residual of the disjoint cap split, including true-opening probes. -/
def WinResidual {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  WinGuessPartner prims x r ∧ ¬WinHit prims x r ∧ ¬OpeningMatch prims x r ∧ ¬TopPartner prims x r

/-- The residual partner is a bottom-layer partner. The top partner is charged
to the output lane, as in leanVM's structural collision reduction. -/
theorem winResidual_guess_or_bottomPartner {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) (hr : WinResidual prims x r) :
    ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
      let z := finalOf x r top state forgery
      let hk := z.honestKey prims
      let signature := XmssSecurity.Bridge.toModelSig forgery.signature
      SigningDescentProof.Guess z.cache x.1 z.key hk forgery.message signature ∨
        ∃ selected, hk.selected = some selected ∧ selected ≠ (forgery.message, signature.randomness) ∧
          XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
              x.1 z.key selected =
            XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.cache)
              x.1 z.key (forgery.message, signature.randomness) := by
  obtain ⟨⟨_, top, state, forgery, hmeta, hbad⟩, _, _, htop⟩ := hr
  refine ⟨top, state, forgery, hmeta, ?_⟩
  rcases hbad with hguess | hbottom | htopPartner
  · exact Or.inl hguess
  · exact Or.inr hbottom
  · exact (htop ⟨top, state, forgery, hmeta, htopPartner⟩).elim

theorem capLanes_disjoint {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C) :
    ¬(WinOutput prims x r ∧ WinResidual prims x r) := by
  rintro ⟨h | ⟨_, h | h⟩, _, hn, ho, ht⟩
  · exact hn h
  · exact ho h
  · exact ht h

/-- Required replacement for HitLaneBound: one fixed-cap unit jointly covers
chain/leaf/node hits, different commitment preimages and top digest partners.
This is an extension of the hit event, not a consequence of HitLaneBound.
The standard top-partner theorem needs an additional transport because these
bottom trees are generated on demand. No output bound is assumed proved. -/
def OutputLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[WinOutput prims x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128

/-- The remaining fixed-cap probability obligation. It does not split q by
call type or substitute the expected stopping cost for q. -/
def ResidualLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[WinResidual prims x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128

/-- The precise structural obligation after closing commitment output matches.
Its domain excludes commitment calls, so adding the proved opening charge does
not spend a third unit. This is a refined replacement for HitLaneBound, not a
consequence of its unweighted q/N statement. Top partners and any unopened-tree
completion exception must be handled within this domain's charge. -/
def StructuralOutputDomainBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[fun r => WinOutput prims x r ∧ ¬OpeningMatch prims x r |
      SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * otherExpectedCost prims A x

theorem outputLaneBound_of_domain (prims : Primitives) (C : Committee)
    (hstructural : StructuralOutputDomainBound prims C) : OutputLaneBound prims C := by
  intro A q x hx hc hq hsmall
  classical
  have hevent : Pr[WinOutput prims x | SigningDescentProof.exposedRun prims A x] ≤
      Pr[OpeningMatch prims x | SigningDescentProof.exposedRun prims A x] +
        Pr[fun r => WinOutput prims x r ∧ ¬OpeningMatch prims x r |
          SigningDescentProof.exposedRun prims A x] := by
    refine (probEvent_mono fun r _ hw => ?_).trans (probEvent_or_le _ _ _)
    by_cases ho : OpeningMatch prims x r
    · exact Or.inl ho
    · exact Or.inr ⟨hw, ho⟩
  refine hevent.trans ((add_le_add (openingMatch_bound_expected prims A x)
    (hstructural A q x hx hc hq hsmall)).trans ?_)
  rw [← mul_add]
  have hcost := mul_le_mul_left' (outputDomainCosts_le prims A x q hq)
    ((2 ^ 128 : ℝ≥0∞)⁻¹)
  simpa only [div_eq_mul_inv, mul_comm] using hcost

set_option maxRecDepth 100000 in
theorem win_le_capLanes {C : Committee} (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true |
      runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] ≤
    Pr[WinOutput prims x | SigningDescentProof.exposedRun prims A x] +
      Pr[WinResidual prims x | SigningDescentProof.exposedRun prims A x] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, probEvent_map]
  refine le_trans (probEvent_mono fun r hr hwin => ?_) (probEvent_or_le _ _ _)
  classical
  have hwin' : r.1.1 = (true, false) := Prod.ext hwin.2 hwin.1
  obtain ⟨top, state, forgery, hsome, hbad⟩ :=
    SigningCacheProof.signing_run_badEvent_closed prims A x r hr hwin'
  by_cases hh : WinHit prims x r
  · exact Or.inl (Or.inl hh)
  have hgp : WinGuessPartner prims x r := by
    rcases hbad with h | h
    · exact (hh ⟨hwin', top, state, forgery, hsome, h⟩).elim
    · exact ⟨hwin', top, state, forgery, hsome, h⟩
  by_cases ho : OpeningMatch prims x r
  · exact Or.inl (Or.inr ⟨hgp, Or.inl ho⟩)
  by_cases ht : TopPartner prims x r
  · exact Or.inl (Or.inr ⟨hgp, Or.inr ht⟩)
  · exact Or.inr ⟨hgp, hh, ho, ht⟩

set_option maxRecDepth 100000 in
/-- Fixed-cap assembly. The residual and the extended hit bound are explicit
open hypotheses. The rejected expected-cost bounds for true-opening probes
are not used; output matches admit the separate domain charge proved above. -/
theorem hiddenCoreAt_of_capLanes (prims : Primitives) (C : Committee)
    (hitLane : OutputLaneBound prims C)
    (residualLane : ResidualLaneBound prims C) : SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hc hq hsmall
  rw [signingHashError_eq]
  exact (win_le_capLanes prims A x).trans
    (add_le_add (hitLane A q x hx hc hq hsmall) (residualLane A q x hx hc hq hsmall))

theorem hiddenCoreAt_of_outputDomain (prims : Primitives) (C : Committee)
    (hstructural : StructuralOutputDomainBound prims C)
    (hresidual : ResidualLaneBound prims C) : SigningCoreProof.HiddenCoreAt prims C :=
  hiddenCoreAt_of_capLanes prims C (outputLaneBound_of_domain prims C hstructural) hresidual

/-! A stopped search counting both true-opening probes and output matches must
use the cap, not its expected stopping time. These formulas concern a planted
random function: the true opening and the output target are both counted. -/

def openingSurvival (N : ℝ) (k : ℕ) : ℝ :=
  (1 - k / N) * (1 - 1 / N) ^ k

theorem openingSurvival_step (N : ℝ) (hN : N ≠ 0) (k : ℕ) :
    openingSurvival N k - openingSurvival N (k + 1) =
      (1 - 1 / N) ^ k * (2 / N - ((k : ℝ) + 1) / N ^ 2) := by
  unfold openingSurvival
  rw [pow_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The exact excess over twice the expected number of trials. It is not zero:
after the second distinct miss, the conditional hidden-opening hazard grows. -/
theorem stoppedOpening_charge_gap (N : ℝ) (hN : N ≠ 0) (M : ℕ) :
    (1 - openingSurvival N M) -
        2 / N * (∑ k ∈ Finset.range M, openingSurvival N k) =
      (∑ k ∈ Finset.range M, ((k : ℝ) - 1) * (1 - 1 / N) ^ k) / N ^ 2 := by
  induction M with
  | zero => simp [openingSurvival]
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hs := openingSurvival_step N hN M
    rw [add_div]
    rw [← ih]
    unfold openingSurvival at hs ⊢
    field_simp at hs ⊢
    nlinarith

/-- The same search does satisfy the fixed-cap two-unit bound. -/
theorem opening_fixed_cap (N : ℝ) (hN : 1 ≤ N) (M : ℕ) (hM : (M : ℝ) ≤ N) :
    1 - openingSurvival N M ≤ 2 * (M : ℝ) / N := by
  have hpos : 0 < N := by linarith
  have hi : 1 / N ≤ 1 := (div_le_one hpos).mpr hN
  have hb := one_add_mul_le_pow (R := ℝ) (a := -(1 / N)) (by linarith) M
  have hp : 1 - (M : ℝ) / N ≤ (1 - 1 / N) ^ M := by
    simpa only [mul_neg, ← div_eq_mul_one_div, sub_eq_add_neg] using hb
  have hm : 0 ≤ 1 - (M : ℝ) / N := sub_nonneg.mpr ((div_le_one hpos).mpr hM)
  have hmul := mul_le_mul_of_nonneg_left hp hm
  unfold openingSurvival
  rw [mul_div_assoc]
  nlinarith [sq_nonneg ((M : ℝ) / N)]

/-- Even four trials distinguish the cap bound from an expected-cost bound. -/
theorem stoppedOpening_four :
    2 / (2 ^ 128 : ℝ) * (∑ k ∈ Finset.range 4, openingSurvival (2 ^ 128) k) <
      1 - openingSurvival (2 ^ 128) 4 := by
  norm_num [openingSurvival, Finset.sum_range_succ]

section StructuralCharge

open Classical SigningHitLaneProof

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

variable {C : Committee}

/-- The raw hash input of a counted call, including the stream-key read inside
PRG. Uniform sampling and programming do not contribute to this charge. -/
def rawDomainCost (relevant : Query C → Prop) : (WorldSpec C).Domain → ℕ :=
  fun t => match t with
  | .inl (.inl (.inr (.inl input))) | .inr (.inr (.inl input)) =>
      if relevant input then 1 else 0
  | .inl (.inl (.inr (.inr input))) | .inr (.inr (.inr input)) =>
      if relevant (.streamKey input.2.1) then 1 else 0
  | _ => 0

/-- Domain-sensitive lifting through both source copies and PRG's internal read. -/
theorem cachePotential_domain_step (prims : Primitives)
    (relevant : Query C → Prop) (f : HashCache C → ℝ≥0∞)
    (hhash : ∀ input cache,
      ∑' r, Pr[= r | ((Query C →ₒ LeanXmss.HashOutput).randomOracle input).run cache] * f r.2 ≤
        f cache + if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ht : ¬IsProgram t) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] * f r.2.1.1 ≤
      f s.1.1 + (rawDomainCost relevant t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    tsum_probOutput_map_mul]
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change (∑' r, Pr[= r | (fun u => (u, s.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))] * f r.2) ≤ _
    rw [tsum_probOutput_map_mul]
    simp [rawDomainCost, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]
  · change (∑' r, Pr[= r | ((Query C →ₒ LeanXmss.HashOutput).randomOracle q).run s.1.1] * f r.2) ≤ _
    simpa only [rawDomainCost, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul] using hhash q s.1.1
  · change (∑' r, Pr[= r | (prgAnswer prims p).run s.1.1] * f r.2) ≤ _
    simpa [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, bind_pure_comp,
      tsum_probOutput_map_mul, rawDomainCost, ite_mul] using hhash (.streamKey p.2.1) s.1.1
  · exact (ht (by trivial)).elim
  · change (∑' r, Pr[= r | (fun u => (u, s.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))] * f r.2) ≤ _
    rw [tsum_probOutput_map_mul]
    simp [rawDomainCost, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]
  · change (∑' r, Pr[= r | ((Query C →ₒ LeanXmss.HashOutput).randomOracle q).run s.1.1] * f r.2) ≤ _
    simpa only [rawDomainCost, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul] using hhash q s.1.1
  · change (∑' r, Pr[= r | (prgAnswer prims p).run s.1.1] * f r.2) ≤ _
    simpa [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure, bind_pure_comp,
      tsum_probOutput_map_mul, rawDomainCost, ite_mul] using hhash (.streamKey p.2.1) s.1.1

/-- Structural matches spend only structural calls. The separate top-key
reserve is charged at its designated honest PRF gate. -/
def structuralHitCost (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (t : (WorldSpec C).Domain) : ℕ :=
  rawDomainCost (SigningHitProof.forestRelevant x.1) t +
    if ∃ b, t = .inr (.inr (.inl (SigningHitProof.topGateInput x T b))) then 1 else 0

/-- The checked hit proof's completion and per-top-key reserves, with their
charges kept separate instead of enlarged to every source call. -/
def structuralHitPotential (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (T : C.Term) (s : LoggedState C) : ℝ≥0∞ :=
  SigningHitProof.completionPotential (SigningHitProof.forestRelevant x.1)
    (SigningHitProof.forestCompletion x) s.1.1 +
  ∑ b, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
    (SigningHitProof.ForestExceptionAt prims x b)
    (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s

theorem structuralHitPotential_zero (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (T : C.Term) :
    structuralHitPotential prims A x T loggedInit = 0 := by
  simp [structuralHitPotential, SigningHitProof.completionPotential_empty,
    SigningHitProof.gatedContinuation, SigningHitProof.GateSeen, loggedInit]

set_option backward.isDefEq.respectTransparency false in
theorem structuralHitPotential_step (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (hgate : ∀ b s, SigningHitProof.RawReachable prims s →
      ¬SigningHitProof.GateSeen (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) s.2 →
      (∑' r, Pr[= r | (loggedImpl prims (.inr (.inr (.inl (SigningHitProof.topGateInput x T b))))).run s] *
        SigningHitProof.continuationReserve prims (SigningDescentProof.finalRun A x)
          (SigningHitProof.ForestExceptionAt prims x b) r.2) ≤ (2 ^ 128 : ℝ≥0∞)⁻¹)
    (t : (WorldSpec C).Domain) (s : LoggedState C)
    (hs : SigningHitProof.RawReachable prims s) (ht : ¬IsProgram t) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] * structuralHitPotential prims A x T r.2 ≤
      structuralHitPotential prims A x T s +
        (structuralHitCost x T t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  let gate : XmssSecurity.TopIndex → (WorldSpec C).Domain :=
    fun b => .inr (.inr (.inl (SigningHitProof.topGateInput x T b)))
  have hinj : Function.Injective gate := by
    intro b c h
    exact SigningHitProof.topGateInput_injective x T (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))
  have hc := cachePotential_domain_step prims (SigningHitProof.forestRelevant x.1)
    (SigningHitProof.completionPotential (SigningHitProof.forestRelevant x.1)
      (SigningHitProof.forestCompletion x))
    (SigningHitProof.completionPotential_randomOracle_step _ _
      (SigningHitProof.forestCompletion_reads x)) t s ht
  have hg := SigningHitProof.gatedContinuation_sum_step prims
    (SigningDescentProof.finalRun A x) (SigningHitProof.ForestExceptionAt prims x)
    gate hinj t s (2 ^ 128 : ℝ≥0∞)⁻¹
    (fun b hb he => by subst t; exact hgate b s hs hb)
  by_cases hex : ∃ b, t = gate b
  · simp only [if_pos hex] at hg
    dsimp only [gate] at hex hg
    simp only [structuralHitPotential, mul_add, ENNReal.tsum_add]
    refine (add_le_add hc hg).trans_eq ?_
    simp only [structuralHitCost, if_pos hex, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_add_add_comm (SigningHitProof.completionPotential
      (SigningHitProof.forestRelevant x.1) (SigningHitProof.forestCompletion x) s.1.1) _ _ _
  · simp only [if_neg hex, add_zero] at hg
    dsimp only [gate] at hex hg
    simp only [structuralHitPotential, mul_add, ENNReal.tsum_add]
    refine (add_le_add hc hg).trans_eq ?_
    simp only [structuralHitCost, if_neg hex, add_zero]
    exact add_right_comm (SigningHitProof.completionPotential
      (SigningHitProof.forestRelevant x.1) (SigningHitProof.forestCompletion x) s.1.1) _ _

set_option maxRecDepth 100000 in
theorem structuralHitPotential_terminal (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (z : ((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) × LoggedState C)
    (hz : z ∈ support (loggedRun prims A x)) (hwin : WinHit prims x (z.1, z.2.1)) :
    1 ≤ structuralHitPotential prims A x T z.2 := by
  by_cases hc : ∀ r ∈ support ((simulateQ (Query C →ₒ LeanXmss.HashOutput).randomOracle
      (SigningHitProof.forestCompletion x)).run z.2.1.1),
      SigningHitProof.CompletedHit (SigningHitProof.forestRelevant x.1) r.1 z.2.1.1
  · have he := SigningHitProof.completionPotential_terminal _ _ _ hc
    unfold structuralHitPotential
    rw [he]
    exact le_add_right le_rfl
  · obtain ⟨top, state, forgery, hmeta, _⟩ := hwin.2
    let b := XmssSecurity.topKeyOf forgery.signature.leafIndex
    have he : SigningHitProof.ForestExceptionAt prims x b z :=
      ⟨⟨hwin, hc⟩, top, state, forgery, hmeta, rfl⟩
    have hg := SigningHitProof.finalRun_gate prims A x T b loggedInit z hz
    have hv := SigningHitProof.gatedContinuation_terminal prims
      (SigningDescentProof.finalRun A x) (SigningHitProof.ForestExceptionAt prims x b)
      (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) z hz he hg
    have hsum : SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
        (SigningHitProof.ForestExceptionAt prims x b)
        (.inr (.inr (.inl (SigningHitProof.topGateInput x T b)))) z.2 ≤
      ∑ c, SigningHitProof.gatedContinuation prims (SigningDescentProof.finalRun A x)
        (SigningHitProof.ForestExceptionAt prims x c)
        (.inr (.inr (.inl (SigningHitProof.topGateInput x T c)))) z.2 :=
      Finset.single_le_sum (f := fun c => SigningHitProof.gatedContinuation prims
        (SigningDescentProof.finalRun A x) (SigningHitProof.ForestExceptionAt prims x c)
        (.inr (.inr (.inl (SigningHitProof.topGateInput x T c)))) z.2)
        (fun _ _ => zero_le) (Finset.mem_univ b)
    exact (hv ▸ hsum).trans (le_add_left le_rfl)

/-- The programming guard works for an arbitrary nonnegative domain charge. -/
theorem guarded_domain_step (prims : Primitives) (Inv : LoggedState C → Prop)
    (f : LoggedState C → ℝ≥0∞) (cost : (WorldSpec C).Domain → ℝ≥0∞)
    (hstep : ∀ t s, Inv s → ¬Programmed s.2 → ¬IsProgram t →
      ∑' r, Pr[= r | (loggedImpl prims t).run s] * f r.2 ≤ f s + cost t)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : ¬Programmed s.2 → Inv s) :
    ∑' r, Pr[= r | (loggedImpl prims t).run s] * guarded f r.2 ≤ guarded f s + cost t := by
  by_cases hb : Programmed s.2 ∨ IsProgram t
  · refine le_trans (le_of_eq (tsum_probOutput_mul_of_const_on_support _ (c := 0)
      (fun r hr => ?_) (by simp))) zero_le
    rw [guarded, if_pos (by rw [loggedImpl_log prims t s r hr, programmed_logQuery]; exact hb)]
  · push Not at hb
    rw [guarded, if_neg hb.1]
    refine (ENNReal.tsum_le_tsum fun r => ?_).trans (hstep t s (hs hb.1) hb.1 hb.2)
    gcongr
    simp only [guarded]
    split_ifs <;> simp

set_option maxRecDepth 100000 in
/-- A refinement of the closed hit lane under its original hypotheses. The source cost is
zero on commitment calls and on encoding calls, on both oracle copies. -/
theorem hit_bound_structural_cost (prims : Primitives) (A : TsigAdversary C)
    (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    ∃ T : C.Term, Pr[WinHit prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * XmssSecurity.expectedSimulatedCost (loggedImpl prims)
        (fun t _ => structuralHitCost x T t) (SigningDescentProof.finalRun A x) loggedInit := by
  obtain ⟨T, hT⟩ := SigningHitProof.keyGateBound prims A q x hx hkeys hq hsmall
  refine ⟨T, ?_⟩
  let f := structuralHitPotential prims A x T
  let Inv : LoggedState C → Prop := fun s => ¬Programmed s.2 → SigningHitProof.RawReachable prims s
  have hi : Inv loggedInit := fun _ => .initial
  have hinv : ∀ t s, Inv s → ∀ r ∈ support ((loggedImpl prims t).run s), Inv r.2 := by
    intro t s hs r hr hn
    have hn' : ¬Programmed s.2 ∧ ¬IsProgram t := by
      rw [loggedImpl_log prims t s r hr, programmed_logQuery, not_or] at hn
      exact hn
    exact .step t s (hs hn'.1) hn'.2 r hr
  have hstep := guarded_domain_step prims Inv f
    (fun t => (2 ^ 128 : ℝ≥0∞)⁻¹ * structuralHitCost x T t)
    (fun t s hs hn ht => by
      simpa only [mul_comm] using structuralHitPotential_step prims A x T hT t s (hs hn) ht)
  have hf := XmssSecurity.expectedFinal_le (loggedImpl prims) hinv (guarded f)
    (fun t _ => (2 ^ 128 : ℝ≥0∞)⁻¹ * structuralHitCost x T t)
    (fun t s hs => hstep t s (fun _ => hs)) (SigningDescentProof.finalRun A x) loggedInit hi
  have hz : guarded f loggedInit = 0 := by
    rw [guarded, if_neg (show ¬Programmed (loggedInit (C := C)).2 by simp [loggedInit, Programmed])]
    exact structuralHitPotential_zero prims A x T
  rw [hz, zero_add, XmssSecurity.expectedSimulatedCost_const_mul] at hf
  refine le_trans ?_ hf
  rw [SigningHitLaneProof.winHit_logged, probEvent_eq_tsum_ite, XmssSecurity.expectedFinal]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ support (loggedRun prims A x)
  · by_cases hw : WinHit prims x (z.1, z.2.1)
    · simp only [hw, if_true, guarded, if_neg (noProgramQuery prims C A x z hz)]
      simpa only [mul_one, loggedRun, loggedInit, f] using mul_le_mul_left'
        (structuralHitPotential_terminal prims A x T z hz hw) (Pr[= z | loggedRun prims A x])
    · simp [hw]
  · simp [probOutput_eq_zero_of_not_mem_support hz]

theorem commitment_ne_modelHash (P P' : LeanXmss.PublicParameter) (e : LeanXmss.KeyIndex)
    (candidate : LeanXmss.Digest) (domain : XmssSecurity.HashDomain) (payload : LeanXmss.HashInput) :
    commitmentInput P' e candidate ≠ XmssSecurity.tweakableHashInput P domain payload := by
  intro h
  have heq :
      XmssSecurity.bytesLE 16 P' ++ XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 1 0 e.val) ++
        (LeanXmss.bytesLE 16 candidate ++ LeanXmss.bytesLE 16 0) =
      XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields domain) ++
        (payload ++ XmssSecurity.domainSuffix domain) := by
    rw [← XmssSecurity.Bridge.tweakableHashInput_eq]
    exact h
  have ht := congrArg (fun fields => fields.tag.toNat) (XmssSecurity.Bridge.prefix_inj heq).2.1
  cases domain <;> norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at ht

theorem forestRelevant_not_commitment (P : LeanXmss.PublicParameter) (input : LeanXmss.HashInput)
    (hf : SigningHitProof.forestRelevant (C := C) P (.hash input)) : ¬CommitmentInput input := by
  obtain ⟨domain, payload, _, _, he, _⟩ := hf
  rintro ⟨P', e, candidate, hc⟩
  exact commitment_ne_modelHash P P' e candidate domain payload (hc.symm.trans (Query.hash.inj he))

theorem forestRelevant_not_digest (P : LeanXmss.PublicParameter) (input : LeanXmss.HashInput)
    (hf : SigningHitProof.forestRelevant (C := C) P (.hash input)) :
    ¬SigningGuessLaneProof.DigestInput input := by
  obtain ⟨domain, payload, _, hd, he, _⟩ := hf
  have hi := Query.hash.inj he
  rintro (⟨P', e, trial, hc⟩ | ⟨P', e, trial, hc⟩)
  all_goals
    have heq := hc.symm.trans hi
    simp only [XmssSecurity.Concrete.CacheView.encodingInput,
      XmssSecurity.Concrete.CacheView.topEncodingInput,
      XmssSecurity.Bridge.tweakableHashInput_eq] at heq
    have ht := congrArg (fun fields => fields.tag.toNat) (XmssSecurity.Bridge.prefix_inj heq).2.1
    cases domain <;> simp_all [SigningHitProof.StructuralDomain,
      XmssSecurity.hashDomainFields, XmssSecurity.tweakFields]

theorem commitment_not_digest (input : LeanXmss.HashInput) (hc : CommitmentInput input) :
    ¬SigningGuessLaneProof.DigestInput input := by
  obtain ⟨P, e, candidate, rfl⟩ := hc
  rintro (⟨P', f, trial, hd⟩ | ⟨P', f, trial, hd⟩)
  · exact commitment_ne_modelHash P' P e candidate (.encoding f) _ hd
  · exact commitment_ne_modelHash P' P e candidate (.topEncoding f) _ hd

theorem structuralHitCost_le (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (t : (WorldSpec C).Domain) : structuralHitCost x T t ≤ SeedHitProof.signCost t := by
  by_cases hg : ∃ b, t = .inr (.inr (.inl (SigningHitProof.topGateInput x T b)))
  · obtain ⟨b, rfl⟩ := hg
    simp [structuralHitCost, rawDomainCost, SigningHitProof.topGateInput,
      SigningHitProof.forestRelevant_prf, SeedHitProof.signCost]
  · simp only [structuralHitCost, if_neg hg, add_zero]
    rcases t with ((n | (q | p)) | prog) | (n | (q | p)) <;>
      simp [rawDomainCost, SeedHitProof.signCost] <;> split_ifs <;> omega

theorem structuralHitCost_zero_commitment (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (t : (WorldSpec C).Domain) (hc : CommitmentCall t) : structuralHitCost x T t = 0 := by
  rcases t with ((n | (q | p)) | prog) | (n | (q | p)) <;> try { cases hc }
  all_goals
    cases q <;> try { cases hc }
    rename_i input
    have hf : ¬SigningHitProof.forestRelevant (C := C) x.1 (.hash input) :=
      fun h => forestRelevant_not_commitment x.1 input h hc
    simp [structuralHitCost, rawDomainCost, SigningHitProof.topGateInput, hf]

theorem structuralHitCost_zero_digest (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (t : (WorldSpec C).Domain) (hd : SigningGuessLaneProof.DigestCall t) :
    structuralHitCost x T t = 0 := by
  rcases t with ((n | (q | p)) | prog) | (n | (q | p)) <;> try { cases hd }
  all_goals
    cases q <;> try { cases hd }
    rename_i input
    have hf : ¬SigningHitProof.forestRelevant (C := C) x.1 (.hash input) :=
      fun h => forestRelevant_not_digest x.1 input h hd
    simp [structuralHitCost, rawDomainCost, SigningHitProof.topGateInput, hf]

/-- Exact domain separation for the output lane: structural matches, different
commitment openings, and both digest domains share one source-call unit. -/
theorem structural_commitment_digest_cost_le (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (t : (WorldSpec C).Domain) :
    structuralHitCost x T t + commitmentCost t + SigningGuessLaneProof.digestCost t ≤
      SeedHitProof.signCost t := by
  by_cases hc : CommitmentCall t
  · have hd : ¬SigningGuessLaneProof.DigestCall t := by
      rcases t with ((n | (q | p)) | prog) | (n | (q | p)) <;> try { cases hc }
      all_goals
        cases q <;> try { cases hc }
        exact commitment_not_digest _ hc
    simpa [structuralHitCost_zero_commitment x T t hc, commitmentCost, hc,
      SigningGuessLaneProof.digestCost, hd] using commitmentCost_le t
  · by_cases hd : SigningGuessLaneProof.DigestCall t
    · have he := SigningGuessLaneProof.digestCost_add_guessCost (C := C) t
      have hl : SigningGuessLaneProof.digestCost t ≤ SeedHitProof.signCost t := by omega
      simpa [structuralHitCost_zero_digest x T t hd, commitmentCost, hc] using hl
    · simpa [commitmentCost, hc, SigningGuessLaneProof.digestCost, hd] using structuralHitCost_le x T t

def sourceExpectedCost (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (cost : (WorldSpec C).Domain → ℕ) : ℝ≥0∞ :=
  XmssSecurity.expectedSimulatedCost (loggedImpl prims) (fun t _ => cost t)
    (SigningDescentProof.finalRun A x) loggedInit

theorem sourceExpectedCost_mono (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (left right : (WorldSpec C).Domain → ℕ)
    (hle : ∀ t, left t ≤ right t) :
    sourceExpectedCost prims A x left ≤ sourceExpectedCost prims A x right := by
  apply XmssSecurity.expectedSimulatedCost_mono
  intro t s
  exact_mod_cast hle t

theorem sourceExpectedCost_add (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (left right : (WorldSpec C).Domain → ℕ) :
    sourceExpectedCost prims A x (fun t => left t + right t) =
      sourceExpectedCost prims A x left + sourceExpectedCost prims A x right := by
  simp only [sourceExpectedCost, Nat.cast_add, XmssSecurity.expectedSimulatedCost_add]

/-- The refined hit lane leaves both commitment and digest charges available,
with the real game's supported cap and no additional budget assumption. -/
theorem source_output_costs_le (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (T : C.Term) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    sourceExpectedCost prims A x (structuralHitCost x T) +
      sourceExpectedCost prims A x commitmentCost +
      sourceExpectedCost prims A x SigningGuessLaneProof.digestCost ≤ q := by
  rw [← sourceExpectedCost_add, ← sourceExpectedCost_add]
  exact (sourceExpectedCost_mono prims A x _ _ (structural_commitment_digest_cost_le x T)).trans
    (loggedRun_expectedCost_le prims A x q hq)

theorem sourceExpectedCost_eq_log (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (cost : (WorldSpec C).Domain → ℕ) :
    sourceExpectedCost prims A x cost =
      ∑' r, Pr[= r | loggedRun prims A x] *
        (SigningGuessLaneProof.logCost cost r.2.2 : ℝ≥0∞) := by
  have he := logged_expectedCost_eq prims cost (SigningDescentProof.finalRun A x) loggedInit
  simpa only [sourceExpectedCost, loggedInit, SigningGuessLaneProof.logCost,
    List.map_nil, List.sum_nil, Nat.cast_zero, zero_add, XmssSecurity.expectedFinal,
    loggedRun] using he

/-- The structural half of the earlier domain split is true. Its rejected
GuessPartnerDomainBound counterpart is not used by this theorem. -/
theorem hitOnlyDomainBoundClosed (prims : Primitives) : HitOnlyDomainBound prims C := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨T, hhit⟩ := hit_bound_structural_cost prims A q x hx hkeys hq hsmall
  have hcost : sourceExpectedCost prims A x (structuralHitCost x T) ≤
      sourceExpectedCost prims A x hitOnlyCost := by
    apply sourceExpectedCost_mono
    intro t
    have h := structural_commitment_digest_cost_le x T t
    unfold hitOnlyCost
    omega
  have hbound : Pr[WinHit prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * sourceExpectedCost prims A x hitOnlyCost :=
    hhit.trans (mul_le_mul_left' hcost _)
  rw [SigningHitLaneProof.winHit_logged] at hbound
  refine (probEvent_mono (fun r _ h => h.1)).trans (hbound.trans_eq ?_)
  rw [sourceExpectedCost_eq_log, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [div_eq_mul_inv]
  ac_rfl

end StructuralCharge

section SourceBottomScan

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A source bottom search is the same cached scan as the leanVM signer.
The signature fields are only a projection of the selected codeword. -/
theorem grind_bottom_sign (secretKey : XmssSecurity.SecretKey) (key : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (base : LeanXmss.Randomness) :
    ∀ attempts trial,
      XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey key message base attempts trial =
        (liftM (show OracleComp XmssSecurity.HashSpec _ from Option.map (fun selected => XmssSecurity.Concrete.precomputedSignWithEncoding
          secretKey key selected.1 selected.2) <$>
            grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
              base attempts trial) : OracleComp XmssSecurity.OracleWorld _) := by
  intro attempts
  induction attempts with
  | zero => intro trial; rfl
  | succ attempts ih =>
    intro trial
    rw [XmssSecurity.Concrete.precomputedSignBoundedAttempts, grind]
    simp only [map_bind, liftM_map, liftM_bind]
    rw [XmssSecurity.Bridge.messageDigest_bottom]
    unfold XmssSecurity.Concrete.precomputedSignAttempt
    simp only [liftM_map, map_bind, liftM_bind, liftM_pure, bind_assoc]
    simp only [XmssSecurity.randomnessBits, LeanXmss.digestBits]
    congr 1
    funext digest
    rw [XmssSecurity.Bridge.decode_eq]
    cases hd : XmssSecurity.TargetSum.decodeDigest digest with
    | none => simpa using ih (trial + 1)
    | some encoding => simp

local instance : SampleableType XmssSecurity.Randomness := SampleableType.ofFintype _


theorem romImpl_lift_hash {α : Type} (oa : OracleComp XmssSecurity.HashSpec α) :
    simulateQ XmssSecurity.romImpl (liftM oa : OracleComp XmssSecurity.OracleWorld α) =
      simulateQ (randomOracle : QueryImpl XmssSecurity.HashSpec
        (StateT (QueryCache XmssSecurity.HashSpec) ProbComp)) oa :=
  QueryImpl.simulateQ_liftComp_right_eq_of_apply _ _ (fun _ => rfl) oa

theorem grind_bottom_sign_run (secretKey : XmssSecurity.SecretKey) (key : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (base : LeanXmss.Randomness) (attempts trial : ℕ)
    (cache : QueryCache XmssSecurity.HashSpec) :
    (simulateQ XmssSecurity.romImpl
      (XmssSecurity.Concrete.precomputedSignBoundedAttempts secretKey key message base attempts trial)).run cache =
      (fun r => (Option.map (fun selected => XmssSecurity.Concrete.precomputedSignWithEncoding
          secretKey key selected.1 selected.2) r.1, r.2)) <$>
        (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
          grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
            base attempts trial)).run cache := by
  rw [grind_bottom_sign, romImpl_lift_hash, simulateQ_map, StateT.run_map]

def bottomScan (parameter : LeanXmss.PublicParameter) (key : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (cache : QueryCache XmssSecurity.HashSpec) := do
  let base ← $ᵗ XmssSecurity.Randomness
  (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
    grind parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
      base LeanXmss.randomizerAttemptLimit 0)).run cache

theorem bottomScan_selected_probability (secretKey : XmssSecurity.SecretKey)
    (key : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (cache : QueryCache XmssSecurity.HashSpec) (randomness : LeanXmss.Randomness)
    (hcached : XmssSecurity.Partner.IsHit cache secretKey.parameter key (message, randomness)) :
    Pr[fun r => ∃ selected, r.1 = some selected ∧ selected.1 = randomness |
      bottomScan secretKey.parameter key message cache] =
      XmssSecurity.Partner.W cache secretKey.parameter key (message, randomness) /
        (2 ^ 128 : ℝ≥0∞) := by
  have hh : XmssSecurity.Scan.scanStatus secretKey key message cache randomness = .hit := by
    rw [XmssSecurity.Ghost.scanStatus_eq]
    exact (XmssSecurity.Partner.isHit_iff (message, randomness)).mp hcached
  have h := XmssSecurity.Scan.selection_uniform_eq secretKey key message cache randomness hh
  have hrun :
      Pr[fun result => ∃ sig, result.1 = some sig ∧ sig.randomness = randomness | do
        let base ← $ᵗ XmssSecurity.Randomness
        (simulateQ XmssSecurity.romImpl (XmssSecurity.Concrete.precomputedSignBoundedAttempts
          secretKey key message base XmssSecurity.signingAttemptLimit 0)).run cache] =
      Pr[fun r => ∃ selected, r.1 = some selected ∧ selected.1 = randomness |
        bottomScan secretKey.parameter key message cache] := by
    unfold bottomScan
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    apply tsum_congr
    intro base
    rw [grind_bottom_sign_run, probEvent_map]
    apply congrArg (fun p : ℝ≥0∞ => Pr[= base | ($ᵗ XmssSecurity.Randomness)] * p)
    apply probEvent_ext
    intro r _
    rcases r with ⟨selected, final⟩
    cases selected with
    | none => simp
    | some selected => simp [Function.comp_def,
        XmssSecurity.Concrete.precomputedSignWithEncoding]
  exact hrun.symm.trans (h.trans (by
    rw [XmssSecurity.Partner.W_eq, div_eq_mul_inv]
    simp only [XmssSecurity.randomnessBits, Nat.cast_pow, Nat.cast_ofNat]
    apply congrArg (fun p : ℝ≥0∞ => p * (2 ^ 128 : ℝ≥0∞)⁻¹)
    apply Finset.sum_congr rfl
    intro base _
    rw [XmssSecurity.Ghost.scan_landing_eq, XmssSecurity.Ghost.scanStatus_eq]
    rfl))

/-- A cached partner is charged with the scan weight of its actual position. -/
theorem bottomScan_cachedPartner_probability_le (secretKey : XmssSecurity.SecretKey)
    (key : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (cache : QueryCache XmssSecurity.HashSpec) :
    Pr[fun r => ∃ selected, r.1 = some selected ∧
      XmssSecurity.Partner.IsPartnered cache secretKey.parameter key (message, selected.1) |
      bottomScan secretKey.parameter key message cache] ≤
      XmssSecurity.Partner.Φ cache secretKey.parameter key / (2 ^ 128 : ℝ≥0∞) := by
  let E := fun (y : XmssSecurity.Partner.Position)
      (r : Option (LeanXmss.Randomness × LeanXmss.Encoding) × QueryCache XmssSecurity.HashSpec) =>
    y.1 = message ∧ XmssSecurity.Partner.IsPartnered cache secretKey.parameter key y ∧
      ∃ selected, r.1 = some selected ∧ selected.1 = y.2
  have hE :
      Pr[fun r => ∃ selected, r.1 = some selected ∧
        XmssSecurity.Partner.IsPartnered cache secretKey.parameter key (message, selected.1) |
        bottomScan secretKey.parameter key message cache] =
      Pr[fun r => ∃ y ∈ (Finset.univ : Finset XmssSecurity.Partner.Position), E y r |
        bottomScan secretKey.parameter key message cache] := by
    apply probEvent_ext
    intro r _
    constructor
    · rintro ⟨selected, hs, hp⟩
      exact ⟨(message, selected.1), by simp only [Finset.mem_univ], rfl, hp, selected, hs, rfl⟩
    · rintro ⟨⟨m, rho⟩, _, hm, hp, selected, hs, hr⟩
      change m = message at hm
      cases hm
      change selected.1 = rho at hr
      cases hr
      exact ⟨selected, hs, hp⟩
  rw [hE]
  refine (probEvent_exists_finset_le_sum Finset.univ _ E).trans ?_
  rw [XmssSecurity.Partner.Φ, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro y _
  by_cases hp : XmssSecurity.Partner.IsPartnered cache secretKey.parameter key y
  · rw [if_pos hp]
    by_cases hm : y.1 = message
    · rcases y with ⟨m, rho⟩
      dsimp at hm
      cases hm
      have hh : XmssSecurity.Partner.IsHit cache secretKey.parameter key (message, rho) := by
        obtain ⟨o, ho, hv, _⟩ := hp
        exact ⟨o, ho, hv⟩
      simpa only [E, true_and, and_self, div_eq_mul_inv, hp] using
        (bottomScan_selected_probability secretKey key message cache rho hh).le
    · simp [E, hm]
  · simp [E, hp]

theorem grind_bottom_selected_probability (secretKey : XmssSecurity.SecretKey)
    (key : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (cache : QueryCache XmssSecurity.HashSpec) (base randomness : LeanXmss.Randomness)
    (hcached : XmssSecurity.Partner.IsHit cache secretKey.parameter key (message, randomness)) :
    Pr[fun r => ∃ selected, r.1 = some selected ∧ selected.1 = randomness |
      (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
        grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
          base LeanXmss.randomizerAttemptLimit 0)).run cache] =
      XmssSecurity.LoopWalk.reach XmssSecurity.Scan.nextRand XmssSecurity.Scan.landing
        (XmssSecurity.Scan.scanStatus secretKey key message cache) randomness
          XmssSecurity.signingAttemptLimit base := by
  have hh : XmssSecurity.Scan.scanStatus secretKey key message cache randomness = .hit := by
    rw [XmssSecurity.Ghost.scanStatus_eq]
    exact (XmssSecurity.Partner.isHit_iff (message, randomness)).mp hcached
  have h := XmssSecurity.Scan.selection_eq secretKey key message cache base randomness
    XmssSecurity.Scan.signingAttemptLimit_le hh
  rw [grind_bottom_sign_run, probEvent_map] at h
  refine Eq.trans ?_ h
  apply probEvent_ext
  intro r _
  rcases r with ⟨selected, final⟩
  cases selected <;> simp [XmssSecurity.Concrete.precomputedSignWithEncoding]

theorem encodingInput_ne_randomizerInput (parameter : LeanXmss.PublicParameter)
    (key e : LeanXmss.KeyIndex) (lay : LeanXmss.Layer)
    (message : LeanXmss.Message) (randomness rho : LeanXmss.Randomness)
    (payload : LeanXmss.HashInput) :
    XmssSecurity.Concrete.CacheView.encodingInput parameter key (message, randomness) ≠
      randomizerInput parameter lay e rho payload := by
  intro he
  simp only [XmssSecurity.Concrete.CacheView.encodingInput,
    XmssSecurity.Bridge.tweakableHashInput_eq, randomizerInput] at he
  have heq :
      XmssSecurity.bytesLE 16 parameter ++
        XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields (.encoding key)) ++
          (XmssSecurity.Concrete.encodingPayload message randomness ++
            XmssSecurity.domainSuffix (.encoding key)) =
      XmssSecurity.bytesLE 16 parameter ++
        XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 0 (LeanXmss.layerHi lay 0) e.val) ++
          (LeanXmss.bytesLE 16 rho ++ payload) := by
    simpa only [List.append_assoc, LeanXmss.fieldBytes, LeanXmss.tweakFields,
      LeanXmss.bytesLE, XmssSecurity.fieldBytes, XmssSecurity.tweakFields,
      XmssSecurity.bytesLE] using he
  have ha := (XmssSecurity.Bridge.prefix_inj heq).2.1
  have ht := congrArg (fun fields => fields.tag.toNat) ha
  norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields,
    LeanXmss.tweakFields] at ht

theorem bottomScan_randomizer_cache_status (secretKey : XmssSecurity.SecretKey)
    (key e : LeanXmss.KeyIndex) (message : LeanXmss.Message)
    (cache : QueryCache XmssSecurity.HashSpec) (lay : LeanXmss.Layer)
    (rho : LeanXmss.Digest) (payload : LeanXmss.HashInput) (output : XmssSecurity.HashOutput) :
    XmssSecurity.Scan.scanStatus secretKey key message
      (cache.cacheQuery (randomizerInput secretKey.parameter lay e rho payload) output) =
      XmssSecurity.Scan.scanStatus secretKey key message cache := by
  funext randomness
  unfold XmssSecurity.Scan.scanStatus
  rw [QueryCache.cacheQuery_of_ne]
  exact encodingInput_ne_randomizerInput secretKey.parameter key e lay message randomness rho payload

def bottomRandomizerScan (parameter : LeanXmss.PublicParameter) (key : LeanXmss.KeyIndex)
    (message : LeanXmss.Message) (rho : LeanXmss.Digest) :
    OracleComp XmssSecurity.HashSpec (Option (LeanXmss.Randomness × LeanXmss.Encoding)) :=
    show OracleComp LeanXmss.HashSpec _ from do
  let output ← LeanXmss.Concrete.oracleHash
    (randomizerInput parameter LeanXmss.bottomLayer key rho (LeanXmss.bytesLE 32 message))
  grind parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
    (LeanXmss.truncateHash output) LeanXmss.randomizerAttemptLimit 0

theorem bottomRandomizerScan_fresh_run (parameter : LeanXmss.PublicParameter)
    (key : LeanXmss.KeyIndex) (message : LeanXmss.Message) (rho : LeanXmss.Digest)
    (cache : QueryCache XmssSecurity.HashSpec)
    (hfresh : cache (randomizerInput parameter LeanXmss.bottomLayer key rho
      (LeanXmss.bytesLE 32 message)) = none) :
    (simulateQ randomOracle (bottomRandomizerScan parameter key message rho)).run cache =
      (do
        let output ← $ᵗ XmssSecurity.HashOutput
        (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
          grind parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
            (LeanXmss.truncateHash output) LeanXmss.randomizerAttemptLimit 0)).run
          (cache.cacheQuery (randomizerInput parameter LeanXmss.bottomLayer key rho
            (LeanXmss.bytesLE 32 message)) output)) := by
  have hquery : simulateQ randomOracle
      (show OracleComp XmssSecurity.HashSpec _ from LeanXmss.Concrete.oracleHash
        (m := OracleComp LeanXmss.HashSpec)
        (randomizerInput parameter LeanXmss.bottomLayer key rho (LeanXmss.bytesLE 32 message))) =
      randomOracle (spec := XmssSecurity.HashSpec)
        (randomizerInput parameter LeanXmss.bottomLayer key rho (LeanXmss.bytesLE 32 message)) := by
    exact (simulateQ_query _ _).trans (id_map _)
  simp only [bottomRandomizerScan, simulateQ_bind, hquery, StateT.run_bind,
    randomOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hfresh,
    StateT.run_liftM, StateT.run_modifyGet, bind_assoc, bind_map_left]

theorem bottomRandomizerScan_selected_probability (secretKey : XmssSecurity.SecretKey)
    (key : LeanXmss.KeyIndex) (message : LeanXmss.Message) (rho : LeanXmss.Digest)
    (cache : QueryCache XmssSecurity.HashSpec) (randomness : LeanXmss.Randomness)
    (hfresh : cache (randomizerInput secretKey.parameter LeanXmss.bottomLayer key rho
      (LeanXmss.bytesLE 32 message)) = none)
    (hcached : XmssSecurity.Partner.IsHit cache secretKey.parameter key (message, randomness)) :
    Pr[fun r => ∃ selected, r.1 = some selected ∧ selected.1 = randomness |
      (simulateQ randomOracle (bottomRandomizerScan secretKey.parameter key message rho)).run cache] =
      XmssSecurity.Partner.W cache secretKey.parameter key (message, randomness) /
        (2 ^ 128 : ℝ≥0∞) := by
  rw [bottomRandomizerScan_fresh_run _ _ _ _ _ hfresh]
  have heq :
      Pr[fun r => ∃ selected, r.1 = some selected ∧ selected.1 = randomness | do
        let output ← $ᵗ XmssSecurity.HashOutput
        (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
          grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
            (LeanXmss.truncateHash output) LeanXmss.randomizerAttemptLimit 0)).run
          (cache.cacheQuery (randomizerInput secretKey.parameter LeanXmss.bottomLayer key rho
            (LeanXmss.bytesLE 32 message)) output)] =
      Pr[fun r => ∃ selected, r.1 = some selected ∧ selected.1 = randomness | do
        let output ← $ᵗ XmssSecurity.HashOutput
        (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
          grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
            (LeanXmss.truncateHash output) LeanXmss.randomizerAttemptLimit 0)).run cache] := by
    apply probEvent_bind_congr
    intro output _
    have hh : XmssSecurity.Partner.IsHit
        (cache.cacheQuery (randomizerInput secretKey.parameter LeanXmss.bottomLayer key rho
          (LeanXmss.bytesLE 32 message)) output) secretKey.parameter key (message, randomness) := by
      simpa only [XmssSecurity.Partner.IsHit, XmssSecurity.Partner.input,
        QueryCache.cacheQuery_of_ne _ _
          (encodingInput_ne_randomizerInput secretKey.parameter key key LeanXmss.bottomLayer
            message randomness rho (LeanXmss.bytesLE 32 message))] using hcached
    rw [grind_bottom_selected_probability _ _ _ _ _ _ hh,
      grind_bottom_selected_probability _ _ _ _ _ _ hcached,
      bottomScan_randomizer_cache_status]
  rw [heq]
  have hdist := XmssSecurity.Rom.evalDist_truncate_uniformHashOutput
  have he : 𝒟[(do
      let output ← $ᵗ XmssSecurity.HashOutput
      (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
        grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
          (LeanXmss.truncateHash output) LeanXmss.randomizerAttemptLimit 0)).run cache)] =
      𝒟[bottomScan secretKey.parameter key message cache] := by
    unfold bottomScan
    rw [show (do
      let output ← $ᵗ XmssSecurity.HashOutput
      (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
        grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
          (LeanXmss.truncateHash output) LeanXmss.randomizerAttemptLimit 0)).run cache) =
      (XmssSecurity.truncateHash <$> ($ᵗ XmssSecurity.HashOutput)) >>= fun base =>
        (simulateQ randomOracle (show OracleComp XmssSecurity.HashSpec _ from
          grind secretKey.parameter LeanXmss.bottomLayer key (LeanXmss.bytesLE 32 message)
            base LeanXmss.randomizerAttemptLimit 0)).run cache by simp only [bind_map_left]; rfl]
    rw [evalDist_bind, hdist, evalDist_bind, evalDist_uniformSample, evalDist_uniformSample]
    rfl
  exact (probEvent_congr' (fun _ _ => Iff.rfl) he).trans
    (bottomScan_selected_probability secretKey key message cache randomness hcached)

end SourceBottomScan

section CachedScanBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Virtual signing searches do not consume the caller's hash-query budget. -/
theorem scan_overBudget_zero (publicKey : XmssSecurity.PublicKey)
    (secretKey : XmssSecurity.SecretKey) (Q : ℕ) {α : Type}
    (oa : OracleComp (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec) α) :
    ∀ (n k : ℕ) (cache : QueryCache XmssSecurity.HashSpec) (trace : XmssSecurity.SigningCacheTrace),
      oa.IsQueryBoundP XmssSecurity.Ghost.IsAdvHash n → k + n ≤ Q →
      XmssSecurity.expectedSimulatedCost (XmssSecurity.Ghost.impl publicKey secretKey)
        (XmssSecurity.Ghost.overBudget Q) oa ((cache, trace), k) = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; simp
  | query_bind input next ih =>
    intro n k cache trace hn hk
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [XmssSecurity.expectedSimulatedCost_query_bind]
    have hz : XmssSecurity.Ghost.overBudget Q input ((cache, trace), k) = 0 := by
      unfold XmssSecurity.Ghost.overBudget
      rw [if_neg]
      rintro ⟨hh, hQ⟩
      have hpos := hn.1.resolve_left (not_not.mpr hh)
      omega
    rw [hz, zero_add]
    apply ENNReal.tsum_eq_zero.mpr
    intro r
    by_cases hr : r ∈ support ((XmssSecurity.Ghost.impl publicKey secretKey input).run
        ((cache, trace), k))
    · rw [XmssSecurity.Ghost.impl_run, support_map] at hr
      obtain ⟨v, _, rfl⟩ := hr
      rw [ih v.1 _ _ _ _ (hn.2 v.1)]
      · simp
      · unfold XmssSecurity.Ghost.tick
        by_cases hh : XmssSecurity.Ghost.IsAdvHash input
        · have hpos : 0 < n := hn.1.resolve_left (not_not.mpr hh)
          simp only [hh, if_true]
          omega
        · simp only [hh, if_false]
          exact hk
    · simp [probOutput_eq_zero_of_not_mem_support hr]
end CachedScanBudget


section CanonicalTopCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Classical

variable {C : Committee}

/-- A read made with a larger cache is possible with a smaller coherent cache.
This retains the answer, while the smaller run records only its own reads. -/
theorem rawQuery_support_restrict (input : Query C) (record cache : HashCache C)
    (hle : record ≤ cache) (r : LeanXmss.HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ LeanXmss.HashOutput).randomOracle input).run cache)) :
    (r.1, record.cacheQuery input r.1) ∈
      support (((Query C →ₒ LeanXmss.HashOutput).randomOracle input).run record) := by
  have hout := (randomOracle_support input cache r hr).2.1
  cases hc : record input with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc]
    simp [uniformSampleImpl]
  | some output =>
    have hsame : output = r.1 := Option.some.inj
      (((randomOracle_support input cache r hr).1 (hle hc)).symm.trans hout)
    subst output
    have heq : record.cacheQuery input r.1 = record := by
      funext other
      by_cases he : other = input
      · subst other; simp [hc]
      · simp [QueryCache.cacheQuery_of_ne _ _ he]
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, heq]
    simp

/-- The record of a completion is itself a supported execution from its initial
record. An initially empty record is in the support of an empty-cache run,
even when the completion read answers already cached by the adversary. This
is support inclusion, not an equality of distributions. -/
theorem recordReads_supported {α : Type}
    (oa : OracleComp (Query C →ₒ LeanXmss.HashOutput) α) :
    ∀ record cache, record ≤ cache →
    ∀ z ∈ support ((simulateQ randomOracle
      (SigningHitProof.recordReads oa record)).run cache),
      (z.1.1, z.1.2) ∈ support ((simulateQ randomOracle oa).run record) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro record cache hle z hz
    change z ∈ ({((a, record), cache)} : Set _) at hz
    rcases hz with rfl
    simp
  | query_bind input k ih =>
    intro record cache hle z hz
    change z ∈ support ((simulateQ randomOracle
      (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ LeanXmss.HashOutput) input) >>=
        fun answer => SigningHitProof.recordReads (k answer)
          (record.cacheQuery input answer))).run cache) at hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hz ⊢
    obtain ⟨r, hr, hz⟩ := hz
    refine ⟨(r.1, record.cacheQuery input r.1), rawQuery_support_restrict input record cache hle r hr, ?_⟩
    apply ih r.1 (record.cacheQuery input r.1) r.2 _ z hz
    rw [SigningHitProof.randomOracle_result_cache input cache r hr]
    exact QueryCache.cacheQuery_mono hle input r.1

theorem thView_cacheQuery_hash (cache : HashCache C) (input : LeanXmss.HashInput)
    (answer : LeanXmss.HashOutput) :
    SigningDescentProof.thView (cache.cacheQuery (.hash input) answer) =
      (SigningDescentProof.thView cache).cacheQuery input answer := by
  funext other
  by_cases he : other = input
  · subst other; simp [SigningDescentProof.thView]
  · simp [SigningDescentProof.thView, QueryCache.cacheQuery_of_ne, he]

/-- Project a supported raw threshold hash computation to the leanVM hash
oracle, retaining exactly its hash cache. -/
theorem forestHash_supported {α : Type} (oa : OracleComp XmssSecurity.HashSpec α) :
    ∀ (cache : HashCache C) (z : α × HashCache C),
      z ∈ support ((simulateQ randomOracle (SigningHitProof.forestHash oa)).run cache) →
      (z.1, SigningDescentProof.thView z.2) ∈ support
        ((simulateQ randomOracle oa).run (SigningDescentProof.thView cache)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro cache z hz
    simp only [SigningHitProof.forestHash, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    simp
  | query_bind input k ih =>
    intro cache z hz
    change z ∈ support ((((Query C →ₒ LeanXmss.HashOutput).randomOracle (.hash input)).run cache >>=
      fun r => (simulateQ randomOracle (SigningHitProof.forestHash (k r.1))).run r.2)) at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion]
    refine ⟨(r.1, SigningDescentProof.thView r.2), ?_, ih r.1 r.2 z hz⟩
    rw [SigningHitProof.randomOracle_result_cache (.hash input) cache r hr,
      thView_cacheQuery_hash]
    cases hc : cache (.hash input) with
    | none =>
      have hp : SigningDescentProof.thView cache input = none := hc
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hp]
      simp [uniformSampleImpl]
    | some output =>
      have hp : SigningDescentProof.thView cache input = some output := hc
      have hsame : output = r.1 := Option.some.inj
        (((randomOracle_support (.hash input) cache r hr).1 hc).symm.trans
          (randomOracle_support (.hash input) cache r hr).2.1)
      subst output
      have heq : (SigningDescentProof.thView cache).cacheQuery input r.1 =
          SigningDescentProof.thView cache := by
        funext other
        by_cases he : other = input
        · subst other; simp [hp]
        · simp [QueryCache.cacheQuery_of_ne _ _ he]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hp, heq]
      simp

/-- Every decoding input in the *read record* of a top grind is its selected
trial. This remains true for an arbitrary, adversarially populated initial
cache; unvisited cached inputs are not part of this record. -/
theorem recordedTopGrind_selected (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (root : LeanXmss.Digest) (base : LeanXmss.Randomness)
    (attempts trial : ℕ) (cache : HashCache C)
    (z : ((Option (LeanXmss.Randomness × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (SigningHitProof.recordReads
      (SigningHitProof.forestHash (XmssSecurity.Concrete.topSignFrom parameter key root base attempts trial :
        OracleComp XmssSecurity.HashSpec _)) ∅)).run cache))
    (input : XmssSecurity.HashInput) (encoding : XmssSecurity.Encoding)
    (hd : XmssSecurity.TopDecodesAt parameter key (SigningDescentProof.thView z.1.2) input encoding) :
    ∃ randomness, z.1.1 = some (randomness, encoding) ∧
      input = XmssSecurity.Concrete.CacheView.topEncodingInput parameter key (root, randomness) := by
  have hr := recordReads_supported _ ∅ cache (by intro i v h; cases h) z hz
  have hm := forestHash_supported _ ∅ (z.1.1, z.1.2) hr
  apply XmssSecurity.topSignFrom_decodings parameter key root base attempts trial
    (SigningDescentProof.thView (∅ : HashCache C)) (SigningDescentProof.thView z.1.2)
    z.1.1 hm _ input encoding hd
  rintro other code ⟨_, output, hc, _⟩
  cases hc

/-- The threshold top grind uses exactly the leanVM top scan, for its genuine
PRF-derived base as well as for any other fixed base. -/
theorem grind_top_eq (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (root : LeanXmss.Digest) (base : LeanXmss.Randomness) :
    ∀ attempts trial, grind parameter LeanXmss.topLayer (topKey key) (LeanXmss.bytesLE 16 root)
      base attempts trial = (XmssSecurity.Concrete.topSignFrom parameter key root base attempts trial :
        OracleComp XmssSecurity.HashSpec _) := by
  intro attempts
  induction attempts with
  | zero => intro trial; rfl
  | succ attempts ih =>
    intro trial
    rw [grind, XmssSecurity.Concrete.topSignFrom]
    change (LeanXmss.Concrete.messageDigest parameter LeanXmss.topLayer
      (XmssSecurity.Bridge.topKey key) (LeanXmss.bytesLE 16 root)
      (base + BitVec.ofNat LeanXmss.digestBits trial) >>= _) = _
    rw [XmssSecurity.Bridge.messageDigest_top]
    apply congrArg (Bind.bind (XmssSecurity.Concrete.topEncodingHash parameter key root
      (base + BitVec.ofNat LeanXmss.digestBits trial) : OracleComp XmssSecurity.HashSpec _))
    funext digest
    rw [XmssSecurity.Bridge.decode_eq]
    cases XmssSecurity.TargetSum.decodeDigest digest with
    | none => exact ih (trial + 1)
    | some encoding => rfl

/-- A different successful top digest survives the scan's read exclusion.
Failed trials cannot conceal a partner, including trials answered from the
adversary's pre-existing cache. -/
theorem recordedTopGrind_partner_unread (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (root : LeanXmss.Digest) (base : LeanXmss.Randomness)
    (attempts trial : ℕ) (cache : HashCache C)
    (z : ((Option (LeanXmss.Randomness × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (SigningHitProof.recordReads
      (SigningHitProof.forestHash (grind parameter LeanXmss.topLayer (topKey key)
        (LeanXmss.bytesLE 16 root) base attempts trial)) ∅)).run cache))
    (randomness : LeanXmss.Randomness) (selected : LeanXmss.Encoding)
    (hs : z.1.1 = some (randomness, selected))
    (payload : LeanXmss.Digest × LeanXmss.Randomness) (output : LeanXmss.HashOutput)
    (hc : cache (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload)) = some output)
    (encoding : LeanXmss.Encoding)
    (hd : XmssSecurity.TargetSum.decodeDigest (LeanXmss.truncateHash output) = some encoding)
    (hne : (root, randomness) ≠ payload) :
    z.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload)) = none := by
  rw [grind_top_eq] at hz
  obtain ⟨hcache, _, hrecord, _⟩ := SigningHitProof.recordReads_resolves _ ∅ cache
    (by intro i v h; cases h) z hz
  cases hr : z.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload)) with
  | none => rfl
  | some value =>
    exfalso
    have hv : value = output := Option.some.inj ((hrecord hr).symm.trans (hcache hc))
    subst value
    obtain ⟨chosen, hchosen, hinput⟩ := recordedTopGrind_selected parameter key root base attempts trial
      cache z hz _ encoding ⟨(XmssSecurity.atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl,
        output, hr, hd⟩
    have hrandom : chosen = randomness := congrArg Prod.fst
      (Option.some.inj (hchosen.symm.trans hs))
    subst chosen
    exact hne ((XmssSecurity.Concrete.CacheView.topEncodingInput_injective parameter key) hinput).symm

/-- A zero-bound setup cannot populate the designated raw hash domain. -/
theorem rawRun_preserves_domain {α : Type}
    (oa : OracleComp (Query C →ₒ LeanXmss.HashOutput) α) (relevant : Query C → Prop)
    (hb : oa.IsQueryBoundP relevant 0) :
    ∀ (cache : HashCache C) (z : α × HashCache C),
      z ∈ support ((simulateQ randomOracle oa).run cache) →
      ∀ input, relevant input → z.2 input = cache input := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro cache z hz input hi
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    rfl
  | query_bind t k ih =>
    have hbound := (isQueryBoundP_query_bind_iff relevant t k 0).mp hb
    have ht : ¬relevant t := hbound.1.resolve_right (by omega)
    intro cache z hz input hi
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hk : (k r.1).IsQueryBoundP relevant 0 := by simpa [ht] using hbound.2 r.1
    rw [ih r.1 hk r.2 z hz input hi]
    exact (randomOracle_support t cache r hr).2.2 input (fun he => ht (he ▸ hi))

/-- All raw inputs at one top message-digest address. -/
abbrev topDigestAddress (parameter : LeanXmss.PublicParameter) (key : XmssSecurity.TopIndex) :
    Query C → Prop := SigningHitProof.forestAddress parameter (.topEncoding key)

/-- Compute the actual root and base before grinding. Keeping this setup in
the same fixed oracle program permits both values to depend on earlier answers. -/
def topGrindAfter (parameter : LeanXmss.PublicParameter) (key : XmssSecurity.TopIndex)
    (setup : OracleComp (Query C →ₒ LeanXmss.HashOutput) (LeanXmss.Digest × LeanXmss.Randomness))
    (attempts : ℕ) : OracleComp (Query C →ₒ LeanXmss.HashOutput)
      (LeanXmss.Digest × Option (LeanXmss.Randomness × LeanXmss.Encoding)) := do
  let pair ← setup
  (fun selected => (pair.1, selected)) <$> SigningHitProof.forestHash
    (grind parameter LeanXmss.topLayer (topKey key) (LeanXmss.bytesLE 16 pair.1) pair.2 attempts 0)

/-- The complete setup-and-scan record has only its selected trial decoding
at this key. The setup may be adaptive and may use other hash domains. -/
theorem topGrindAfter_record_selected (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex)
    (setup : OracleComp (Query C →ₒ LeanXmss.HashOutput) (LeanXmss.Digest × LeanXmss.Randomness))
    (hp : setup.IsQueryBoundP (topDigestAddress parameter key) 0)
    (attempts : ℕ) (cache : HashCache C)
    (z : ((LeanXmss.Digest × Option (LeanXmss.Randomness × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (SigningHitProof.recordReads
      (topGrindAfter parameter key setup attempts) ∅)).run cache))
    (input : XmssSecurity.HashInput) (encoding : XmssSecurity.Encoding)
    (hd : XmssSecurity.TopDecodesAt parameter key (SigningDescentProof.thView z.1.2) input encoding) :
    ∃ randomness, z.1.1.2 = some (randomness, encoding) ∧
      input = XmssSecurity.Concrete.CacheView.topEncodingInput parameter key (z.1.1.1, randomness) := by
  rcases z with ⟨⟨⟨root, selected⟩, record⟩, finalCache⟩
  have hr := recordReads_supported _ ∅ cache (by intro i v h; cases h) _ hz
  simp only [topGrindAfter, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨before, hbefore, hscan⟩ := hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hscan
  obtain ⟨after, hafter, he⟩ := hscan
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨⟨rfl, rfl⟩, rfl⟩
  rw [grind_top_eq] at hafter
  apply XmssSecurity.topSignFrom_decodings parameter key before.1.1 before.1.2 attempts 0
    (SigningDescentProof.thView before.2) (SigningDescentProof.thView after.2) after.1
    (forestHash_supported _ before.2 after hafter) _ input encoding hd
  rintro other code ⟨hat, output, hcached, _⟩
  have hn := rawRun_preserves_domain setup (topDigestAddress parameter key) hp ∅ before hbefore
    (.hash other) hat
  change before.2 (.hash other) = some output at hcached
  rw [hn] at hcached
  cases hcached

/-- A successful prefixed scan records its selected digest and decoding. -/
theorem topGrindAfter_record_cached (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex)
    (setup : OracleComp (Query C →ₒ LeanXmss.HashOutput) (LeanXmss.Digest × LeanXmss.Randomness))
    (attempts : ℕ) (cache : HashCache C)
    (z : ((LeanXmss.Digest × Option (LeanXmss.Randomness × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (SigningHitProof.recordReads
      (topGrindAfter parameter key setup attempts) ∅)).run cache))
    (randomness : LeanXmss.Randomness) (encoding : LeanXmss.Encoding)
    (hs : z.1.1.2 = some (randomness, encoding)) :
    ∃ output, z.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key
        (z.1.1.1, randomness))) = some output ∧
      XmssSecurity.TargetSum.decodeDigest (LeanXmss.truncateHash output) = some encoding := by
  rcases z with ⟨⟨⟨root, selected⟩, record⟩, finalCache⟩
  have hr := recordReads_supported _ ∅ cache (by intro i v h; cases h) _ hz
  simp only [topGrindAfter, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨before, hbefore, hscan⟩ := hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hscan
  obtain ⟨after, hafter, he⟩ := hscan
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨⟨rfl, rfl⟩, rfl⟩
  rw [grind_top_eq] at hafter
  have hm := forestHash_supported _ before.2 after hafter
  dsimp only at hs ⊢
  rw [hs] at hm
  obtain ⟨output, hcached, hdecode⟩ := XmssSecurity.topSignFrom_some_cached parameter key before.1.1 before.1.2 attempts 0
      (SigningDescentProof.thView before.2) (SigningDescentProof.thView after.2) randomness encoding hm
  exact ⟨output, hcached, hdecode⟩

theorem topRandomizer_not_topDigest (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (rho root : LeanXmss.Digest) :
    ¬XmssSecurity.AtHashAddress parameter (.topEncoding key)
      (randomizerInput parameter LeanXmss.topLayer (topKey key) rho (LeanXmss.bytesLE 16 root)) := by
  intro h
  have he := h.1
  change (XmssSecurity.bytesLE 16 parameter ++ XmssSecurity.fieldBytes
    (XmssSecurity.tweakFields 7 0 (LeanXmss.layerHi LeanXmss.topLayer 0) (topKey key).val) ++
    (LeanXmss.bytesLE 16 rho ++ LeanXmss.bytesLE 16 root)).take 32 = _ at he
  have ht := congrArg (fun xs => xs.drop 16) he
  simp only [List.take_append, XmssSecurity.length_bytesLE] at ht
  simp at ht
  rw [List.take_of_length_le (by simp)] at ht
  have hf := congrArg (fun f => f.tag.toNat) (XmssSecurity.fieldBytes_injective ht)
  norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at hf


/-- The top digest tag is 12; setup and structural hashes use other tags. -/
theorem sourceTag_not_topDigest (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (fields : XmssSecurity.TweakFields) (payload : LeanXmss.HashInput)
    (htag : fields.tag.toNat ≠ 12) :
    ¬XmssSecurity.AtHashAddress parameter (.topEncoding key)
      (XmssSecurity.bytesLE 16 parameter ++ XmssSecurity.fieldBytes fields ++ payload) := by
  intro h
  have ht := congrArg (fun xs => xs.drop 16) h.1
  simp only [List.take_append, XmssSecurity.length_bytesLE] at ht
  simp at ht
  rw [List.take_of_length_le (by simp)] at ht
  have hf := congrArg (fun f => f.tag.toNat) (XmssSecurity.fieldBytes_injective ht)
  exact htag (by simpa [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] using hf)

theorem sourceTweak_no_topDigest (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (domain : LeanXmss.HashDomain) (payload : LeanXmss.HashInput)
    (htag : (LeanXmss.hashDomainFields domain).tag.toNat ≠ 12) :
    (LeanXmss.Concrete.tweakableHash parameter domain payload : OracleComp LeanXmss.HashSpec _).IsQueryBoundP
      (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0 := by
  unfold LeanXmss.Concrete.tweakableHash
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · change (OracleComp.lift (OracleSpec.query (spec := XmssSecurity.HashSpec)
      (LeanXmss.tweakableHashInput parameter domain payload))).IsQueryBoundP
        (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0
    simp only [isQueryBoundP_query_iff]
    exact fun h => (sourceTag_not_topDigest parameter key
      ⟨(LeanXmss.hashDomainFields domain).tag, (LeanXmss.hashDomainFields domain).step,
        (LeanXmss.hashDomainFields domain).hi, (LeanXmss.hashDomainFields domain).lo⟩ payload htag h).elim
  · intro _ _; simp

theorem sourceChain_no_topDigest (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (lay : LeanXmss.Layer) (e : LeanXmss.KeyIndex)
    (chain : LeanXmss.ChainIndex) (start steps : ℕ) (value : LeanXmss.Digest) :
    (LeanXmss.Concrete.chainWalk parameter lay e chain start steps value : OracleComp LeanXmss.HashSpec _).IsQueryBoundP
      (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0 := by
  induction steps with
  | zero => simp [LeanXmss.Concrete.chainWalk]
  | succ steps ih =>
    rw [LeanXmss.Concrete.chainWalk]
    apply isQueryBoundP_bind (n := 0) (m := 0) ih
    intro previous _
    split_ifs
    · apply sourceTweak_no_topDigest
      norm_num [LeanXmss.hashDomainFields, LeanXmss.tweakFields]
    · simp

theorem sourceMerkle_no_topDigest (parameter : LeanXmss.PublicParameter)
    (key : XmssSecurity.TopIndex) (lay : LeanXmss.Layer)
    (ends : LeanXmss.KeyIndex → LeanXmss.ChainIndex → LeanXmss.Digest) :
    ∀ level node, (merkleNode parameter lay ends level node).IsQueryBoundP
      (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0 := by
  intro level
  induction level with
  | zero =>
    intro node
    apply sourceTweak_no_topDigest
    norm_num [LeanXmss.hashDomainFields, LeanXmss.tweakFields]
  | succ level ih =>
    intro node
    rw [merkleNode]
    apply isQueryBoundP_bind (n := 0) (m := 0) (ih _)
    intro left _
    apply isQueryBoundP_bind (n := 0) (m := 0) (ih _)
    intro right _
    apply sourceTweak_no_topDigest
    norm_num [LeanXmss.hashDomainFields, LeanXmss.tweakFields]

theorem referenceJob_no_topDigest (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (job : Job) :
    (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 job).IsQueryBoundP
      (topDigestAddress x.1 key) 0 := by
  unfold referenceJob
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · apply SigningHitProof.mapM_bound_zero
    intro point
    exact SigningHitProof.forestValue_bound x.2.1 point x.1 (.topEncoding key)
  · intro values _
    cases job.kind with
    | chainEnd e l =>
      apply (isQueryBoundP_map_iff _ _ _).2
      exact SigningHitProof.forestHash_bound _ _ _ 0 (sourceChain_no_topDigest x.1 key _ _ _ _ _ _)
    | chainRow e l =>
      apply isQueryBoundP_bind (n := 0) (m := 0)
        (SigningHitProof.forestHash_bound _ _ _ 0 (sourceChain_no_topDigest x.1 key _ _ _ _ _ _))
      intro _ _
      apply isQueryBoundP_bind (n := 0) (m := 0)
        (SigningHitProof.forestHash_bound _ _ _ 0 (sourceChain_no_topDigest x.1 key _ _ _ _ _ _))
      intro _ _
      apply isQueryBoundP_bind (n := 0) (m := 0)
        (SigningHitProof.forestHash_bound _ _ _ 0 (sourceChain_no_topDigest x.1 key _ _ _ _ _ _))
      intro _ _; simp
    | chainValue e l p =>
      apply (isQueryBoundP_map_iff _ _ _).2
      exact SigningHitProof.forestHash_bound _ _ _ 0 (sourceChain_no_topDigest x.1 key _ _ _ _ _ _)
    | commitment e =>
      apply (isQueryBoundP_map_iff _ _ _).2
      apply SigningHitProof.forestHash_bound
      change (OracleComp.lift (OracleSpec.query (spec := XmssSecurity.HashSpec)
        (commitmentInput x.1 e (values.getD 0 0)))).IsQueryBoundP
          (XmssSecurity.AtHashAddress x.1 (.topEncoding key)) 0
      simp only [isQueryBoundP_query_iff]
      intro h
      exfalso
      apply sourceTag_not_topDigest x.1 key
        (XmssSecurity.tweakFields 7 1 (LeanXmss.layerHi LeanXmss.bottomLayer 0) e.val)
        (LeanXmss.bytesLE 16 (values.getD 0 0) ++ LeanXmss.bytesLE 16 0) _ h
      norm_num [XmssSecurity.tweakFields]
    | randomizer => simp

def canonicalTopKeys (key : XmssSecurity.TopIndex) :=
  (List.finRange (2 ^ LeanXmss.layerHeight)).flatMap fun k =>
    (List.finRange LeanXmss.numChains).map fun l => (bottomKey key k, l)

def canonicalTopEnds (key : XmssSecurity.TopIndex) (outputs : List (List Bit))
    (e : LeanXmss.KeyIndex) (l : LeanXmss.ChainIndex) : LeanXmss.Digest :=
  digestAt (outputs.getD ((canonicalTopKeys key).idxOf (e, l)) []) 2

def canonicalTopRho (key : XmssSecurity.TopIndex) (outputs : List (List Bit)) : LeanXmss.Digest :=
  digestAt (outputs.getD ((canonicalTopKeys key).length + 2 ^ LeanXmss.layerHeight) []) 0

def canonicalTopAfterJobs (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex)
    (outputs : List (List Bit)) (levels : ℕ) :
    OracleComp (Query C →ₒ LeanXmss.HashOutput) (LeanXmss.Digest × LeanXmss.Randomness) := do
  let root ← SigningHitProof.forestHash
    (merkleNode x.1 LeanXmss.bottomLayer (canonicalTopEnds key outputs) levels key.val)
  let base ← SigningHitProof.forestHash (LeanXmss.truncateHash <$> LeanXmss.Concrete.oracleHash
    (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs) (LeanXmss.bytesLE 16 root)))
  pure (root, base)

theorem canonicalTopAfterJobs_no_digest (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (outputs : List (List Bit)) (levels : ℕ) :
    (canonicalTopAfterJobs x key outputs levels).IsQueryBoundP (topDigestAddress x.1 key) 0 := by
  unfold canonicalTopAfterJobs
  refine isQueryBoundP_bind
    (oa := SigningHitProof.forestHash (merkleNode x.1 LeanXmss.bottomLayer
      (canonicalTopEnds key outputs) levels key.val))
    (ob := fun root => do
      let base ← SigningHitProof.forestHash (LeanXmss.truncateHash <$> LeanXmss.Concrete.oracleHash
        (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs) (LeanXmss.bytesLE 16 root)))
      pure (root, base))
    (n := 0) (m := 0) (by
      exact SigningHitProof.forestHash_bound _ _ _ 0 (sourceMerkle_no_topDigest x.1 key _ _ _ _)) ?_
  intro root _
  refine isQueryBoundP_bind
    (oa := SigningHitProof.forestHash (LeanXmss.truncateHash <$> LeanXmss.Concrete.oracleHash
      (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs) (LeanXmss.bytesLE 16 root))))
    (ob := fun base => pure (root, base)) (n := 0) (m := 0) (by
    apply SigningHitProof.forestHash_bound
    apply (isQueryBoundP_map_iff _ _ _).2
    change (OracleComp.lift (OracleSpec.query (spec := XmssSecurity.HashSpec)
      (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs)
        (LeanXmss.bytesLE 16 root)))).IsQueryBoundP
          (XmssSecurity.AtHashAddress x.1 (.topEncoding key)) 0
    simp only [isQueryBoundP_query_iff]
    exact fun h => (topRandomizer_not_topDigest x.1 key _ root h).elim) ?_
  intro _ _; simp

/-- Exactly the first run, root and randomizer-base computation of the actual
bottom ceremony. No state-derived value is supplied as an external parameter. -/
def canonicalTopSetupForJobs (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) (jobs : List Job) (levels : ℕ) :
    OracleComp (Query C →ₒ LeanXmss.HashOutput) (LeanXmss.Digest × LeanXmss.Randomness) :=
  jobs.mapM (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1) >>=
    fun outputs => canonicalTopAfterJobs x key outputs levels

/-- No step before the top grind reads its top digest address. -/
theorem canonicalTopSetupForJobs_no_digest (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) (jobs : List Job) (levels : ℕ) :
    (canonicalTopSetupForJobs x key jobs levels).IsQueryBoundP (topDigestAddress x.1 key) 0 := by
  exact isQueryBoundP_bind
    (oa := jobs.mapM (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1))
    (ob := fun outputs => canonicalTopAfterJobs x key outputs levels) (n := 0) (m := 0) (by
    apply SigningHitProof.mapM_bound_zero
    intro job
    exact referenceJob_no_topDigest x key job) (by
      intro outputs _
      exact canonicalTopAfterJobs_no_digest x key outputs levels)

def canonicalTopSetup (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :=
  canonicalTopSetupForJobs x key (bottomJobs key) LeanXmss.layerHeight

theorem canonicalTopSetup_no_digest (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :
    (canonicalTopSetup x key).IsQueryBoundP (topDigestAddress x.1 key) 0 :=
  canonicalTopSetupForJobs_no_digest x key (bottomJobs key) LeanXmss.layerHeight

/-- A canonical scan with the threshold root and PRF-derived base. -/
def canonicalTopGrind (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :=
  topGrindAfter x.1 key (canonicalTopSetup x key) LeanXmss.randomizerAttemptLimit

theorem canonicalTopGrind_record_selected (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (cache : HashCache C)
    (z : ((LeanXmss.Digest × Option (LeanXmss.Randomness × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle
      (SigningHitProof.recordReads (canonicalTopGrind x key) ∅)).run cache))
    (input : XmssSecurity.HashInput) (encoding : XmssSecurity.Encoding)
    (hd : XmssSecurity.TopDecodesAt x.1 key (SigningDescentProof.thView z.1.2) input encoding) :
    ∃ randomness, z.1.1.2 = some (randomness, encoding) ∧
      input = XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (z.1.1.1, randomness) :=
  topGrindAfter_record_selected x.1 key (canonicalTopSetup x key)
    (canonicalTopSetup_no_digest x key) LeanXmss.randomizerAttemptLimit cache z hz input encoding hd

/-- Exact top digest inputs, so malformed hash payloads spend no digest charge. -/
def topDigestInput (parameter : LeanXmss.PublicParameter) (key : XmssSecurity.TopIndex)
    (input : Query C) : Prop :=
  ∃ payload, input = .hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload)

def topGrindTargets (parameter : LeanXmss.PublicParameter) (key : XmssSecurity.TopIndex)
    (result : LeanXmss.Digest × Option (LeanXmss.Randomness × LeanXmss.Encoding))
    (record : HashCache C) : SigningHitProof.CompletionTargets C := fun input =>
  match result.2 with
  | none => (input, 0)
  | some selected =>
      let honest := Query.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key
        (result.1, selected.1))
      (honest, LeanXmss.truncateHash ((record honest).getD 0))

/-- The fixed program computes both the root and genuine PRF-derived scan base. -/
def canonicalTopCompletion (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :
    OracleComp (Query C →ₒ LeanXmss.HashOutput) (SigningHitProof.CompletionTargets C) :=
  SigningHitProof.recordedCompletion (canonicalTopGrind x key) (topGrindTargets x.1 key)

/-- A partner whose entire canonical root/base/scan computation is already
resolved by the source cache. Unopened trees need the separate gate argument. -/
def ResolvedTopPartner (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex)
    (cache : HashCache C) : Prop :=
  ∃ root randomness encoding honestOutput payload output,
    DeterministicSigning.Resolves cache (canonicalTopGrind x key) (root, some (randomness, encoding)) ∧
    cache (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (root, randomness))) = some honestOutput ∧
    cache (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key payload)) = some output ∧
    (root, randomness) ≠ payload ∧ LeanXmss.truncateHash output = LeanXmss.truncateHash honestOutput

/-- Every supported completion detects a resolved top partner. The proof uses
only its read record; hostile prior cache entries are not silently excluded. -/
theorem resolvedTopPartner_completed (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex)
    (cache : HashCache C) (hpartner : ResolvedTopPartner x key cache)
    (z : SigningHitProof.CompletionTargets C × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (canonicalTopCompletion x key)).run cache)) :
    SigningHitProof.CompletedHit (topDigestInput x.1 key) z.1 cache := by
  obtain ⟨root, randomness, encoding, honestOutput, payload, output, hresolved, hh, hc, hne, heq⟩ := hpartner
  simp only [canonicalTopCompletion, SigningHitProof.recordedCompletion, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨hcache, _, hrecord, hrun⟩ := SigningHitProof.recordReads_resolves _ ∅ cache
    (by intro i v h; cases h) r hr
  have hresult : r.1.1 = (root, some (randomness, encoding)) :=
    (hrun.mono hrecord).unique (hresolved.mono hcache)
  have hs : r.1.1.2 = some (randomness, encoding) := congrArg Prod.snd hresult
  have hroot : r.1.1.1 = root := congrArg Prod.fst hresult
  obtain ⟨honest, hhonest, hdecode⟩ := topGrindAfter_record_cached x.1 key (canonicalTopSetup x key)
    LeanXmss.randomizerAttemptLimit cache r hr randomness encoding hs
  rw [hroot] at hhonest
  have hout : honest = honestOutput := Option.some.inj ((hrecord hhonest).symm.trans (hcache hh))
  subst honest
  have hmissing : r.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key payload)) = none := by
    cases ha : r.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key payload)) with
    | none => rfl
    | some answer =>
      exfalso
      have ho : answer = output := Option.some.inj ((hrecord ha).symm.trans (hcache hc))
      subst answer
      have hdecode' : XmssSecurity.TargetSum.decodeDigest (LeanXmss.truncateHash output) = some encoding :=
        heq ▸ hdecode
      obtain ⟨chosen, hchosen, hinput⟩ := canonicalTopGrind_record_selected x key cache r hr _ encoding
        ⟨(XmssSecurity.atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl, output, ha, hdecode'⟩
      have hchosen' : chosen = randomness := congrArg Prod.fst (Option.some.inj (hchosen.symm.trans hs))
      subst chosen
      rw [hroot] at hinput
      exact hne ((XmssSecurity.Concrete.CacheView.topEncodingInput_injective x.1 key) hinput).symm
  apply SigningHitProof.completedHit_recordedTargets _ _ _ _ |>.2
  refine ⟨.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key payload), output,
    hc, hmissing, ⟨payload, rfl⟩, ?_, ?_⟩
  · simp only [topGrindTargets, hresult]
    intro he
    apply hne
    exact ((XmssSecurity.Concrete.CacheView.topEncodingInput_injective x.1 key)
      (Query.hash.inj he)).symm
  · simp only [topGrindTargets, hs]
    change LeanXmss.truncateHash output = LeanXmss.truncateHash
      ((r.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (r.1.1.1, randomness)))).getD 0)
    rw [hroot, hhonest]
    exact heq

theorem topDigestInput_key_unique (parameter : LeanXmss.PublicParameter) (input : Query C)
    (left right : XmssSecurity.TopIndex)
    (hl : topDigestInput parameter left input) (hr : topDigestInput parameter right input) : left = right := by
  obtain ⟨lp, hl⟩ := hl
  obtain ⟨rp, hr⟩ := hr
  have he := Query.hash.inj (hl.symm.trans hr)
  have hal := (XmssSecurity.atHashAddress_tweakableHashInput_iff parameter (.topEncoding left)
    (.topEncoding left) (XmssSecurity.Concrete.topEncodingPayload lp.1 lp.2)).2 rfl
  have har := (XmssSecurity.atHashAddress_tweakableHashInput_iff parameter (.topEncoding right)
    (.topEncoding right) (XmssSecurity.Concrete.topEncodingPayload rp.1 rp.2)).2 rfl
  change XmssSecurity.AtHashAddress parameter (.topEncoding left)
    (XmssSecurity.Concrete.CacheView.topEncodingInput parameter left lp) at hal
  change XmssSecurity.AtHashAddress parameter (.topEncoding right)
    (XmssSecurity.Concrete.CacheView.topEncodingInput parameter right rp) at har
  rw [he] at hal
  exact XmssSecurity.HashDomain.topEncoding.inj (XmssSecurity.atHashAddress_unique _ _ _ _ hal har)

def anyTopDigestInput (parameter : LeanXmss.PublicParameter) (input : Query C) : Prop :=
  ∃ key, topDigestInput parameter key input

local instance (parameter : LeanXmss.PublicParameter) (input : Query C) :
    Decidable (anyTopDigestInput parameter input) := Classical.propDecidable _

def topPartnerPotential (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) : ℝ≥0∞ :=
  ∑ key : XmssSecurity.TopIndex, SigningHitProof.completionPotential (topDigestInput x.1 key)
    (canonicalTopCompletion x key) cache

theorem topPartnerPotential_zero (x : SigningSecurityProof.Keys3 C) : topPartnerPotential x ∅ = 0 := by
  simp [topPartnerPotential, SigningHitProof.completionPotential_empty]

set_option backward.isDefEq.respectTransparency false in
/-- The per-key completion charges are disjoint: one raw input has at most one
key, even though each key's canonical root and base are computed adaptively. -/
theorem topPartnerPotential_step (x : SigningSecurityProof.Keys3 C)
    (input : Query C) (cache : HashCache C) :
    ∑' r, Pr[= r | ((Query C →ₒ LeanXmss.HashOutput).randomOracle input).run cache] *
      topPartnerPotential x r.2 ≤ topPartnerPotential x cache +
        if anyTopDigestInput x.1 input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [topPartnerPotential, Finset.mul_sum]
  have hswap := ENNReal.tsum_comm (f := fun r : LeanXmss.HashOutput × HashCache C =>
    fun key : XmssSecurity.TopIndex => Pr[= r | ((Query C →ₒ LeanXmss.HashOutput).randomOracle input).run cache] *
      SigningHitProof.completionPotential (topDigestInput x.1 key) (canonicalTopCompletion x key) r.2)
  simp only [tsum_fintype] at hswap
  rw [hswap]
  refine (Finset.sum_le_sum (fun key _ => SigningHitProof.completionPotential_randomOracle_step
    (topDigestInput x.1 key) (canonicalTopCompletion x key)
      (SigningHitProof.recordedCompletion_reads _ _ _) input cache)).trans_eq ?_
  rw [Finset.sum_add_distrib]
  apply congrArg (fun value : ℝ≥0∞ => (∑ key : XmssSecurity.TopIndex,
    SigningHitProof.completionPotential (topDigestInput x.1 key) (canonicalTopCompletion x key) cache) + value)
  by_cases hex : ∃ key, topDigestInput x.1 key input
  · obtain ⟨key, hk⟩ := hex
    rw [if_pos ⟨key, hk⟩, Finset.sum_eq_single key]
    · simp [hk]
    · intro other _ hne
      rw [if_neg (fun ho => hne (topDigestInput_key_unique x.1 input other key ho hk))]
    · simp
  · simp only [not_exists] at hex
    simp [anyTopDigestInput, hex]

set_option backward.isDefEq.respectTransparency false in
theorem topPartnerPotential_terminal (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (h : ∃ key, ResolvedTopPartner x key cache) : 1 ≤ topPartnerPotential x cache := by
  obtain ⟨key, hk⟩ := h
  have he := SigningHitProof.completionPotential_terminal (topDigestInput x.1 key)
    (canonicalTopCompletion x key) cache (resolvedTopPartner_completed x key cache hk)
  unfold topPartnerPotential
  rw [← he]
  exact Finset.single_le_sum (f := fun b : XmssSecurity.TopIndex =>
    SigningHitProof.completionPotential (topDigestInput x.1 b) (canonicalTopCompletion x b) cache)
      (fun _ _ => zero_le) (Finset.mem_univ key)

open SigningHitLaneProof in
/-- A cache potential for a fixed completion can charge its own raw domain in
the actual signing source. Programming is guarded until the source's proved
no-programming invariant removes the guard at the end. -/
theorem cachePotential_bound_source (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (relevant : Query C → Prop)
    (f : HashCache C → ℝ≥0∞) (event : HashCache C → Prop)
    (hzero : f ∅ = 0)
    (hterminal : ∀ cache, event cache → 1 ≤ f cache)
    (hhash : ∀ input cache,
      ∑' r, Pr[= r | ((Query C →ₒ LeanXmss.HashOutput).randomOracle input).run cache] * f r.2 ≤
        f cache + if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) :
    Pr[fun r => event r.2.1 | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * sourceExpectedCost prims A x (rawDomainCost relevant) := by
  let potential : LoggedState C → ℝ≥0∞ := fun s => f s.1.1
  let bad : LoggedState C → Prop := fun s => event s.1.1 ∧ ¬Programmed s.2
  have hbad : ∀ s, bad s → 1 ≤ guarded potential s := by
    intro s hs
    rw [guarded, if_neg hs.2]
    exact hterminal _ hs.1
  have hstep : ∀ t s, True →
      ∑' r, Pr[= r | (loggedImpl prims t).run s] * guarded potential r.2 ≤
        guarded potential s + (2 ^ 128 : ℝ≥0∞)⁻¹ * (rawDomainCost relevant t : ℝ≥0∞) := by
    intro t s _
    apply guarded_domain_step prims (fun _ => True) potential
      (fun t => (2 ^ 128 : ℝ≥0∞)⁻¹ * (rawDomainCost relevant t : ℝ≥0∞)) _ t s (fun _ => trivial)
    intro t s _ _ ht
    simpa only [potential, mul_comm] using cachePotential_domain_step prims relevant f hhash t s ht
  have hz : guarded potential (loggedInit (C := C)) = 0 := by
    simp [guarded, potential, loggedInit, Programmed, hzero]
  have hb := probEvent_le_chargedCost (loggedImpl prims) (fun _ => True)
    (fun _ _ _ _ _ => trivial) (guarded potential) bad hbad
    (fun t _ => (rawDomainCost relevant t : ℝ≥0∞)) (2 ^ 128 : ℝ≥0∞)⁻¹ hstep
    (SigningDescentProof.finalRun A x) loggedInit trivial hz
  refine le_trans ?_ hb
  rw [← loggedRun_forget, probEvent_map]
  apply probEvent_mono
  intro r hr hevent
  exact ⟨hevent, noProgramQuery prims C A x r hr⟩

theorem topDigest_rawCost_le (parameter : LeanXmss.PublicParameter) (t : (WorldSpec C).Domain) :
    rawDomainCost (anyTopDigestInput parameter) t ≤
      SigningGuessLaneProof.digestCost t := by
  rcases t with ((n | (input | input)) | programming) | (n | (input | input))
  · simp [rawDomainCost]
  · by_cases hd : ∃ key, topDigestInput parameter key input
    · obtain ⟨key, payload, rfl⟩ := hd
      have he : SigningGuessLaneProof.DigestInput
          (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload) :=
        Or.inr ⟨parameter, key, payload, rfl⟩
      simp [rawDomainCost, SigningGuessLaneProof.digestCost, SigningGuessLaneProof.DigestCall,
        he, topDigestInput]
      split_ifs <;> omega
    · simp [rawDomainCost, anyTopDigestInput, hd]
  · simp [rawDomainCost, anyTopDigestInput, topDigestInput]
  · simp [rawDomainCost]
  · simp [rawDomainCost]
  · by_cases hd : ∃ key, topDigestInput parameter key input
    · obtain ⟨key, payload, rfl⟩ := hd
      have he : SigningGuessLaneProof.DigestInput
          (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload) :=
        Or.inr ⟨parameter, key, payload, rfl⟩
      simp [rawDomainCost, SigningGuessLaneProof.digestCost, SigningGuessLaneProof.DigestCall,
        he, topDigestInput]
      split_ifs <;> omega
    · simp [rawDomainCost, anyTopDigestInput, hd]
  · simp [rawDomainCost, anyTopDigestInput, topDigestInput]

set_option backward.isDefEq.respectTransparency false in
/-- All keys together spend at most one unit per actual digest call. This is
an unconditional probability bound for resolved canonical top partners in the
actual signing source, with no freshness assumption on their selected trial. -/
theorem resolvedTopPartner_bound_digest_cost (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => ∃ key, ResolvedTopPartner x key r.2.1 | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * sourceExpectedCost prims A x SigningGuessLaneProof.digestCost := by
  have h := cachePotential_bound_source prims A x (anyTopDigestInput x.1)
    (topPartnerPotential x) (fun cache => ∃ key, ResolvedTopPartner x key cache)
    (by exact topPartnerPotential_zero x)
    (by intro cache he; exact topPartnerPotential_terminal x cache he)
    (by intro input cache; convert topPartnerPotential_step x input cache using 1)
  exact h.trans (mul_le_mul_left'
    (sourceExpectedCost_mono prims A x _ _ (topDigest_rawCost_le x.1)) _)

/-- Every completed bottom ceremony resolves the canonical setup and scan,
including ceremonies that return no tree. -/
theorem resolves_referenceBottom_topGrind (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (key : XmssSecurity.TopIndex)
    (output : Option TreeOutput)
    (h : DeterministicSigning.Resolves cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom key)) output) :
    ∃ root selected, DeterministicSigning.Resolves cache (canonicalTopGrind x key) (root, selected) := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, hrest⟩ := h.of_bind
  obtain ⟨values, hvalues, houtputs⟩ := houtputs.of_map
  subst outputs
  obtain ⟨root, hroot, hrest⟩ := hrest.of_bind
  obtain ⟨base, hbase, hrest⟩ := hrest.of_bind
  obtain ⟨selected, hscan, _⟩ := hrest.of_bind
  refine ⟨root, selected, ?_⟩
  have hsetup : DeterministicSigning.Resolves cache (canonicalTopSetup x key) (root, base) := by
    unfold canonicalTopSetup canonicalTopSetupForJobs
    apply hvalues.bind
    unfold canonicalTopAfterJobs
    apply hroot.bind
    apply hbase.bind
    exact .pure _
  unfold canonicalTopGrind topGrindAfter
  apply hsetup.bind
  exact hscan.map (fun selected => (root, selected))

/-- A returned bottom tree identifies the root and selected randomness of the
canonical scan. Acceptance checks after the scan do not change either value. -/
theorem resolves_referenceBottom_topGrind_some (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (key : XmssSecurity.TopIndex) (tree : BottomTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom key))
      (some (.bottom tree))) :
    ∃ encoding, DeterministicSigning.Resolves cache (canonicalTopGrind x key)
      (tree.root, some (tree.topSignature.randomness, encoding)) := by
  unfold referenceTree ceremonyOutput at h
  obtain ⟨outputs, houtputs, hrest⟩ := h.of_bind
  obtain ⟨values, hvalues, houtputs⟩ := houtputs.of_map
  subst outputs
  obtain ⟨root, hroot, hrest⟩ := hrest.of_bind
  obtain ⟨base, hbase, hrest⟩ := hrest.of_bind
  obtain ⟨selected, hscan, hrest⟩ := hrest.of_bind
  have hcanon : DeterministicSigning.Resolves cache (canonicalTopGrind x key) (root, selected) := by
    have hsetup : DeterministicSigning.Resolves cache (canonicalTopSetup x key) (root, base) := by
      unfold canonicalTopSetup canonicalTopSetupForJobs
      apply hvalues.bind
      unfold canonicalTopAfterJobs
      apply hroot.bind
      apply hbase.bind
      exact .pure _
    unfold canonicalTopGrind topGrindAfter
    apply hsetup.bind
    exact hscan.map (fun selected => (root, selected))
  cases selected with
  | none => cases hrest.pure_inv
  | some selected =>
    rcases selected with ⟨randomness, encoding⟩
    obtain ⟨outputs, houtputs, hrest⟩ := hrest.of_bind
    obtain ⟨values', _, houtputs⟩ := houtputs.of_map
    subst outputs
    obtain ⟨path, _, hrest⟩ := hrest.of_bind
    obtain ⟨verified, _, hrest⟩ := hrest.of_bind
    split_ifs at hrest
    · cases hrest.pure_inv
    · have he := hrest.pure_inv
      have ht := TreeOutput.bottom.inj (Option.some.inj he)
      subst tree
      exact ⟨encoding, hcanon⟩

theorem bottomSpec_honestRoot (prims : Primitives) (z : SigningDescentProof.FinalState C)
    (tree : BottomTree)
    (hs : BottomSpec prims z.answers z.keys.2.1 z.keys.1 z.top (treeOf z.key) tree) :
    SigningDescentProof.honestRoot z.cache z.keys.1 z.key (z.honestKey prims) = tree.root := by
  have hends : ∀ i : XmssSecurity.LeafIndex, i.val / 2 ^ 16 = (treeOf z.key).val →
      ∀ l, (tree.cpk i l).2.2 =
      XmssSecurity.Wots.walk (XmssSecurity.Concrete.CacheView.chainStep
        (SigningDescentProof.thView z.cache) z.keys.1 i l) 0 3
        (z.chainStarts prims LeanXmss.bottomLayer i l) := by
    intro i hi l
    let k : Fin (2 ^ LeanXmss.layerHeight) := ⟨i.val % 2 ^ 16, Nat.mod_lt _ (by decide)⟩
    have hek : bottomKey (treeOf z.key) k = i := by
      apply Fin.ext
      simp only [bottomKey, k, ← hi, LeanXmss.layerHeight]
      exact Nat.div_add_mod _ _
    have hc := congrArg (fun p => p.2.2) (hs.cpk k l)
    dsimp only at hc
    rw [hek] at hc
    exact hc.trans (SigningCacheProof.E_chainWalk_bottom prims z.cache z.keys.1 i l 0 3 _)
  have ht := SigningCacheProof.eval_merkleNode_bottom (SigningDescentProof.thView z.cache)
    z.keys.1 (fun i l => (tree.cpk i l).2.2) (z.chainStarts prims LeanXmss.bottomLayer)
    16 le_rfl (treeOf z.key).val (treeOf z.key).isLt hends
  have hp := SigningCacheProof.path_ascends_to_treeNode (SigningDescentProof.thView z.cache)
    z.keys.1 (z.chainStarts prims LeanXmss.bottomLayer) z.key 16 le_rfl
  change SigningDescentProof.honestRoot z.cache z.keys.1 z.key (z.honestKey prims) =
    XmssSecurity.Concrete.CacheReplay.treeNode (SigningDescentProof.thView z.cache) z.keys.1
      (z.chainStarts prims LeanXmss.bottomLayer) 16
      (XmssSecurity.Concrete.merkleNodeOfNat (treeOf z.key).val) at hp
  rw [hs.root, SigningCacheProof.E_eval]
  exact hp.trans ht.symm

theorem resolved_bottom_topSignedInput (prims : Primitives) (z : SigningDescentProof.FinalState C)
    (tree : BottomTree)
    (htop : D prims z.answers
      (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 emptyTop .top) = some (.top z.top))
    (hres : DeterministicSigning.Resolves z.cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue z.keys.2.1)
        z.keys.1 z.top (.bottom (treeOf z.key))) (some (.bottom tree))) :
    SigningDescentProof.topSignedInput z.cache z.keys.1 z.key (z.honestKey prims) =
      (tree.root, tree.topSignature.randomness) := by
  have heval : D prims z.answers
      (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 z.top (.bottom (treeOf z.key))) =
        some (.bottom tree) := by
    rw [← SigningHitProof.hashEmbed_referenceTree, SigningHitProof.eval_hashEmbed]
    exact hres.eval z.answers (SigningCacheProof.agrees_answersOf le_rfl)
  obtain ⟨top, href, hc, hr⟩ := D_refTop (prims := prims) (h := z.answers) z.keys.1 z.keys.2.1 emptyTop
  rw [htop] at href
  have he := TreeOutput.top.inj (Option.some.inj href)
  subst top
  obtain hnone | ⟨tree', he', hs⟩ := D_refBottom (prims := prims) (h := z.answers)
    z.keys.1 z.keys.2.1 z.top hc hr (treeOf z.key)
  · rw [heval] at hnone
    contradiction
  · rw [heval] at he'
    cases TreeOutput.bottom.inj (Option.some.inj he')
    have hb := SigningCacheProof.dealt_bottom prims z (treeOf z.key) _ heval
    apply Prod.ext
    · exact bottomSpec_honestRoot prims z tree hs
    · change ((z.bottomTree prims).map _).getD 0 = tree.topSignature.randomness
      change (((z.dealt prims).bottom (treeOf z.key)).map _).getD 0 = _
      rw [hb]
      rfl

/-- A top partner of a successfully returned, cached bottom ceremony is one
of the canonical partners counted by the all-key completion potential. -/
theorem topPartner_resolved (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : Outcome C)
    (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (hpartner : TopPartner prims x r)
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hmeta : r.1.2 = some (top, state, forgery)) (tree : BottomTree)
    (hres : DeterministicSigning.Resolves r.2.1
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
        x.1 top (.bottom (treeOf forgery.signature.leafIndex))) (some (.bottom tree))) :
    ResolvedTopPartner x (XmssSecurity.topKeyOf forgery.signature.leafIndex) r.2.1 := by
  obtain ⟨top', state', forgery', hm, encoding, hd, hn, he⟩ := hpartner
  rw [hmeta] at hm
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  have htop := SigningHitProof.exposedRun_top_extension prims A x r hr hwin top state forgery hmeta r.2.1 le_rfl
  have hi := resolved_bottom_topSignedInput prims (finalOf x r top state forgery) tree htop hres
  obtain ⟨hcanonEncoding, hcanon⟩ := resolves_referenceBottom_topGrind_some x r.2.1 top
    (treeOf forgery.signature.leafIndex) tree hres
  obtain ⟨⟨honestOutput, hh⟩, ⟨output, ho⟩⟩ :=
    topPartner_inputs_cached prims A x r hr hwin top state forgery hmeta encoding hd he
  erw [hi] at hn he hh
  refine ⟨tree.root, tree.topSignature.randomness, hcanonEncoding, honestOutput, _, output,
    hcanon, hh, ho, hn, ?_⟩
  unfold XmssSecurity.Concrete.CacheView.topEncodingHash XmssSecurity.Concrete.CacheView.digestAt at he
  erw [hh, ho] at he
  exact he.symm

def commitmentTargets (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (record : HashCache C) : SigningHitProof.CompletionTargets C :=
  fun input => match input with
  | .hash value => ((commitmentTrial P value).map fun trial =>
      (Query.hash (commitmentInput P trial.1 (cachedRandomizer seeds record trial.1)),
        commitmentOutputTarget seeds P record input)).getD (input, 0)
  | _ => (input, 0)

theorem commitmentTargets_eq (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (record : HashCache C) (input : LeanXmss.HashInput)
    (key : LeanXmss.KeyIndex) (candidate : LeanXmss.Digest)
    (ht : commitmentTrial P input = some (key, candidate)) :
    commitmentTargets seeds P record (.hash input) =
      (.hash (commitmentInput P key (cachedRandomizer seeds record key)),
        commitmentOutputTarget seeds P record (.hash input)) := by
  simp only [commitmentTargets, ht, Option.map_some, Option.getD_some]

def commitmentCompletion (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) :
    OracleComp (Query C →ₒ LeanXmss.HashOutput) (SigningHitProof.CompletionTargets C) :=
  SigningHitProof.recordedCompletion (rawCommitmentForest seeds P) (fun _ => commitmentTargets seeds P)

theorem alternativeCommitment_completed (seeds : C.Term → LeanXmss.HashOutput)
    (P : LeanXmss.PublicParameter) (cache : HashCache C)
    (h : AlternativeCommitment seeds P cache)
    (z : SigningHitProof.CompletionTargets C × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (commitmentCompletion seeds P)).run cache)) :
    SigningHitProof.CompletedHit (RawCommitmentInput P) z.1 cache := by
  simp only [commitmentCompletion, SigningHitProof.recordedCompletion, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨result, hresult, rfl⟩ := hz
  rcases result with ⟨⟨values, record⟩, completed⟩
  have hrecord := recordReads_supported (rawCommitmentForest seeds P) ∅ cache
    (by intro input value hv; cases hv) ((values, record), completed) hresult
  have hcanonical := rawCommitmentForest_support seeds P (values, record) hrecord
  have hreads := SigningHitProof.recordReads_resolves (rawCommitmentForest seeds P) ∅ cache
    (by intro input value hv; cases hv) ((values, record), completed) hresult
  obtain ⟨key, candidate, honestOutput, output, hslots, hh, ho, hn, he⟩ := h
  obtain ⟨hrslots, ⟨recordOutput, hrc⟩, hrnone⟩ := hcanonical key
  have hcache : cache ≤ completed := hreads.1
  have hs : cachedRandomizer seeds record key = cachedRandomizer seeds cache key :=
    (cachedRandomizer_stable seeds record completed key hreads.2.2.1 hrslots).trans
      (cachedRandomizer_stable seeds cache completed key hcache hslots).symm
  have hrho : recordOutput = honestOutput := by
    have hg := hreads.2.2.1 hrc
    rw [hs] at hg
    exact Option.some.inj (hg.symm.trans (hcache hh))
  have hnone : record (.hash (commitmentInput P key candidate)) = none :=
    hrnone candidate (by rwa [hs])
  have ht : commitmentTrial P (commitmentInput P key candidate) = some (key, candidate) :=
    (commitmentTrial_eq_some P _ key candidate).mpr rfl
  apply SigningHitProof.completedHit_recordedTargets _ _ _ _ |>.2
  refine ⟨.hash (commitmentInput P key candidate), output, ho, hnone, ?_, ?_, ?_⟩
  · simp only [RawCommitmentInput, ht, Option.isSome_some, Bool.true_eq]
  · rw [commitmentTargets_eq seeds P record _ key candidate ht]
    intro heq
    exact hn ((SigningCoreProof.commitmentInput_injective P key (Query.hash.inj heq)).trans hs)
  · rw [commitmentTargets_eq seeds P record _ key candidate ht]
    rw [commitmentOutputTarget_eq seeds P record _ key candidate ht]
    exact he.trans ((congrArg (fun value : Option LeanXmss.HashOutput =>
      LeanXmss.truncateHash (value.getD 0)) hrc).trans (congrArg LeanXmss.truncateHash hrho)).symm

theorem commitment_rawCost_le (P : LeanXmss.PublicParameter) (t : (WorldSpec C).Domain) :
    rawDomainCost (RawCommitmentInput P) t ≤ commitmentCost t := by
  have hhash : ∀ input : LeanXmss.HashInput, RawCommitmentInput (C := C) P (.hash input) →
      CommitmentInput input := by
    intro input h
    cases ht : commitmentTrial P input with
    | none => simp [RawCommitmentInput, ht] at h
    | some trial =>
      exact ⟨P, trial.1, trial.2, ((commitmentTrial_eq_some P input _ _).mp ht).symm⟩
  rcases t with ((n | (input | input)) | programming) | (n | (input | input))
  · simp [rawDomainCost]
  · by_cases hd : RawCommitmentInput P input
    · cases input with
      | hash input => simp [rawDomainCost, hd, commitmentCost, CommitmentCall, hhash input hd]
      | _ => cases hd
    · simp [rawDomainCost, hd]
  · simp [rawDomainCost, RawCommitmentInput]
  · simp [rawDomainCost]
  · simp [rawDomainCost]
  · by_cases hd : RawCommitmentInput P input
    · cases input with
      | hash input => simp [rawDomainCost, hd, commitmentCost, CommitmentCall, hhash input hd]
      | _ => cases hd
    · simp [rawDomainCost, hd]
  · simp [rawDomainCost, RawCommitmentInput]

/-- The commitment-output lane is charged in the same source frame as
structural hits and top partners. -/
theorem alternativeCommitment_bound_source (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => AlternativeCommitment x.2.1 x.1 r.2.1 | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * sourceExpectedCost prims A x commitmentCost := by
  have h := cachePotential_bound_source prims A x (RawCommitmentInput x.1)
    (SigningHitProof.completionPotential (RawCommitmentInput x.1) (commitmentCompletion x.2.1 x.1))
    (AlternativeCommitment x.2.1 x.1)
    (by exact SigningHitProof.completionPotential_empty _ _)
    (by intro cache hh
        exact le_of_eq (SigningHitProof.completionPotential_terminal _ _ cache
          (alternativeCommitment_completed x.2.1 x.1 cache hh)).symm)
    (by intro input cache
        exact SigningHitProof.completionPotential_randomOracle_step _ _
          (SigningHitProof.recordedCompletion_reads _ _ _) input cache)
  exact h.trans (mul_le_mul_left'
    (sourceExpectedCost_mono prims A x _ _ (commitment_rawCost_le x.1)) _)

/-- The first unit uses disjoint source domains. The event itself need not
be disjoint internally; the complementary winning event below is disjoint. -/
def ChargedOutput (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  WinHit prims x r ∨ AlternativeCommitment x.2.1 x.1 r.2.1 ∨ ∃ key, ResolvedTopPartner x key r.2.1

theorem chargedOutput_bound_of_cost (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (hitCost : (WorldSpec C).Domain → ℕ) (q : ℕ)
    (hhit : Pr[WinHit prims x | SigningDescentProof.exposedRun prims A x] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * sourceExpectedCost prims A x hitCost)
    (hcost : sourceExpectedCost prims A x hitCost + sourceExpectedCost prims A x commitmentCost +
      sourceExpectedCost prims A x SigningGuessLaneProof.digestCost ≤ q) :
    Pr[ChargedOutput prims x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  have hevent := probEvent_or_le (SigningDescentProof.exposedRun prims A x) (WinHit prims x)
    (fun r => AlternativeCommitment x.2.1 x.1 r.2.1 ∨ ∃ key, ResolvedTopPartner x key r.2.1)
  have htail := probEvent_or_le (SigningDescentProof.exposedRun prims A x)
    (fun r => AlternativeCommitment x.2.1 x.1 r.2.1)
    (fun r => ∃ key, ResolvedTopPartner x key r.2.1)
  have hsum := hevent.trans (add_le_add hhit (htail.trans
    (add_le_add (alternativeCommitment_bound_source prims A x)
      (resolvedTopPartner_bound_digest_cost prims A x))))
  change Pr[ChargedOutput prims x | SigningDescentProof.exposedRun prims A x] ≤ _ at hsum
  rw [← mul_add, ← mul_add] at hsum
  exact hsum.trans (by
    simpa only [div_eq_mul_inv, mul_comm, add_assoc] using
      mul_le_mul_left' hcost ((2 ^ 128 : ℝ≥0∞)⁻¹))

/-- The residual retains true-opening probes, bottom guesses/partners, and
top partners without a successful cached bottom ceremony. -/
def UnchargedWin (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  r.1.1 = (true, false) ∧ ¬ChargedOutput prims x r

theorem charged_uncharged_disjoint (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (r : Outcome C) : ¬(ChargedOutput prims x r ∧ UnchargedWin prims x r) :=
  fun h => h.2.2 h.1

theorem win_le_charged_uncharged (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => r.1.2 = false ∧ r.1.1 = true |
      runSigningWorld prims (SigningCoreProof.flaggedAfter A x)] ≤
    Pr[ChargedOutput prims x | SigningDescentProof.exposedRun prims A x] +
      Pr[UnchargedWin prims x | SigningDescentProof.exposedRun prims A x] := by
  rw [SigningDescentProof.runSigningWorld_flaggedAfter, probEvent_map]
  refine (probEvent_mono fun r _ hw => ?_).trans (probEvent_or_le _ _ _)
  by_cases hc : ChargedOutput prims x r
  · exact Or.inl hc
  · exact Or.inr ⟨Prod.ext hw.2 hw.1, hc⟩

theorem chargedOutput_bound (prims : Primitives) (A : TsigAdversary C)
    (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    Pr[ChargedOutput prims x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  obtain ⟨T, hhit⟩ := hit_bound_structural_cost prims A q x hx hkeys hq hsmall
  exact chargedOutput_bound_of_cost prims A x (structuralHitCost x T) q hhit
    (source_output_costs_le prims A x T q hq)

/-- One fixed-cap obligation remains. It includes unsuccessful/unopened
bottom ceremonies, rather than assuming their canonical scan succeeded. -/
def UnchargedLaneBound (prims : Primitives) (C : Committee) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    Pr[UnchargedWin prims x | SigningDescentProof.exposedRun prims A x] ≤
      (q : ℝ≥0∞) / 2 ^ 128

/-- The first unit is closed; only the named residual bound is assumed. -/
theorem hiddenCoreAt_of_uncharged (prims : Primitives) (C : Committee)
    (hresidual : UnchargedLaneBound prims C) : SigningCoreProof.HiddenCoreAt prims C := by
  intro A q x hx hkeys hq hsmall
  rw [signingHashError_eq]
  exact (win_le_charged_uncharged prims A x).trans
    (add_le_add (chargedOutput_bound prims A q x hx hkeys hq hsmall)
      (hresidual A q x hx hkeys hq hsmall))

/-- Every successful free bottom-ceremony subrun is excluded for an
uncharged top partner, including a standalone tree request. Failed ceremonies
are deliberately not excluded. -/
theorem uncharged_topPartner_no_successful_bottom (prims : Primitives)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (r : Outcome C)
    (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hu : UnchargedWin prims x r) (hp : TopPartner prims x r)
    (top : TopTree) (state : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.2 = some (top, state, forgery)) (tree : BottomTree)
    (initial final : HashCache C × ℕ)
    (hsub : (some (TreeOutput.bottom tree), final) ∈ support
      ((simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree
          (referenceTree tweakable (prfValue x.2.1) x.1 top
            (.bottom (treeOf forgery.signature.leafIndex))))).run initial))
    (hle : final.1 ≤ r.2.1) : False := by
  have hres : DeterministicSigning.Resolves final.1
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
        x.1 top (.bottom (treeOf forgery.signature.leafIndex))) (some (.bottom tree)) := by
    apply SigningHitProof.run_hashEmbed_resolves prims
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
        x.1 top (.bottom (treeOf forgery.signature.leafIndex))) initial
      (some (TreeOutput.bottom tree), final)
    simpa only [SigningHitProof.hashEmbed_referenceTree] using hsub
  exact hu.2 (Or.inr (Or.inr ⟨_, topPartner_resolved prims A x r hr hu.1 hp
    top state forgery hm tree (hres.mono hle)⟩))

section ResidualPublicView

set_option maxRecDepth 100000

/-- The residual event itself supplies the no-alternative-opening premise;
the complete public share view requires no extra privacy hypothesis. -/
theorem uncharged_chain_releaseSafe (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r)
    (hr : r ∈ support (publicReceiptExposedRun prims A x))
    (hu : UnchargedWin prims x (r.1.1.1, r.2))
    (top : TopTree) (st : TsigState C) (forgery : LeanXmss.Forgery)
    (hm : r.1.1.1.2 = some (top, st, forgery))
    (released : Finset Point) (chain : LeanXmss.ChainIndex) (digit : LeanXmss.Digit)
    (hlt : digit.val < SigningDescentProof.bottomOpened r.2.1 x.1 forgery.signature.leafIndex
      ((finalOf x (r.1.1.1, r.2) top st forgery).honestKey prims) chain) :
    Nonempty ((publicShareView x r.1.1.2 r.1.2 released).ReleaseSafe
      (.chain LeanXmss.bottomLayer forgery.signature.leafIndex chain digit)) := by
  apply publicReceiptExposedRun_chain_releaseSafe prims A x r hr hu.1 top st forgery hm
    _ released chain digit hlt
  intro hopen
  exact hu.2 (Or.inr (Or.inl (openingMatch_alternativeCommitment prims x _ hopen)))

theorem publicReceiptExposedRun_count_le (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) :
    ∀ r ∈ support (publicReceiptExposedRun prims A x), r.2.2 ≤ q := by
  intro r hr
  apply exposedRun_count_le prims A x q hq (r.1.1.1, r.2)
  rw [← publicReceiptExposedRun_source, support_map]
  exact ⟨r, hr, rfl⟩

theorem uncharged_public_probability (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    Pr[UnchargedWin prims x | SigningDescentProof.exposedRun prims A x] =
      Pr[fun r => UnchargedWin prims x (r.1.1.1, r.2) | publicReceiptExposedRun prims A x] := by
  rw [← publicReceiptExposedRun_source, probEvent_map]
  rfl

end ResidualPublicView

end CanonicalTopCompletion

end SigningGuessProof

/-
COUNTEREXAMPLE TO THE EARLIER ONE-UNIT ROUTE ONLY

Earlier target: guessPartnerLaneBoundClosed (prims : Primitives) (C : Committee) :
  GuessPartnerLaneBound prims C.

The following is a mathematical counterexample, not a Lean formalization of
the adversary or its probability. The generic charging lemmas above are proved.

Take t = 2 (hence n = 3), corrupt party 0, and use quorum {0, 1} at one
bottom key e. Fix distinct term/pair keys in the support of keyGen3. Let
N = 2^128, M = 2^120, B = 2^90, and q = M + 2^113 < 2^127.

On any failed search, return a dummy forgery on an unsigned message. Thus the
postgame never needs honestSignature for a threshold-authorized message.

1. Request the bottom tree, exposing c_e = trunc H(commitmentInput P e rho_e).
   Among M fixed distinct randomizers, find the first rho' with commitment c_e.
   These are commitment calls, not digest calls or calls on hidden PRF keys.
   The probability of finding one is exactly
     1 - (1 - M/N) * (1 - 1/N)^M >= (3/2) * M/N.
   The real rho_e contributes M/N; different commitment preimages contribute
   the additional term. It is essential not to discard this second branch.

2. Before round 1, for B distinct messages m, query randomizerInput with rho'
   and the first digest trial at the resulting base R_m. Find m0 != m1 with
   the same valid digest. Both searches select their first trial. The digest
   inputs are distinct because the messages are distinct.
   There are K valid digests, with 2^107 <= K <= 2^108 (Scan/Card.lean).
   For the number X of equal-valid unordered pairs, independence gives
     mu = E[X] = choose(B,2)*K/N^2 >= 2^29,
     Var(X) <= mu + B^3*K/N^3.
   Thus P(X=0) <= 1/mu + 16*N/(B*K) <= 2^-29 + 2^-65 < 1/8.

3. Ask party 1 for round 1 on m0, obtaining its actual part d1. Give round 2
   parts[0] = rho' XOR d1 and parts[1] = d1. The oracle overwrites only its
   own part (Ideal.tsigOracles), so combine is rho'. signCodeword accepts
   this value because its commitment equals c_e. Compute the corrupted
   party's genuine chain parts on m0 from its revealed keys. Combine with
   party 1's chain parts and the public cpk to get the honest chain values at
   the selected digits, exactly as Scheme.assemble does.

4. Output these chain values, the public authentication path and top signature,
   but message m1 and randomness R_m1. The digest equals that of (m0,R_m0),
   so verification succeeds. Only party 0 counts as a signer for m1, hence
   freshness holds. The hidden-key flag is false: hash calls do not set it,
   and the corrupted party's PRF/mask calls use revealed keys only.

5. This win is ALWAYS in Guess OR Partner, including when rho' != rho_e.
   The canonical selected input is for the bound message m0 and the true rho_e.
   If it is absent, bottomOpened is constantly 3 and guess_of_signed applies.
   If its encoding differs from the forged encoding, exists_forged_lt_signed
   supplies a smaller forged digit; its forged value is the honest chain value,
   giving Guess. If the encodings agree, injectivity of successful decoding
   gives equal digests; the messages differ, giving Partner. In particular,
   a commitment collision can be a WinGuessPartner. Such a collision is NOT
   the formal Hit event, which contains only chain/leaf/node collisions.

The bottom tree's top search succeeds with probability at least 7/8: its
2^32 distinct trials have validity probability K/N >= 2^-21. This bound
holds conditional on the commitment data. The fresh bottom digest trials in
step 2 likewise give the 7/8 bound conditional on the earlier history.
Consequently the winning Guess/Partner probability is at least
  (7/8)^2 * (3/2) * M/N = (147/128) * M/N,
whereas the proposed bound is q/N = (129/128) * M/N.
The query budget includes M commitment calls, 2*B trial calls, the fixed
tree/verification work and the constant number of signing calls. Even with
every honest search capped at 2^32, all work other than M is below 2^113.

This does not refute HiddenCoreAt: its bound is 2q/N = (258/128)*M/N.
Many keys do not multiply the targets of one input: commitmentInput_key_eq,
randomizerInput_key_eq, randomizerInput_layer_eq and randomizerInput_payload_eq
identify the key/layer/opening/message. bound_message_unique rules out a second
bound message at the same key. Commitment trials have one hidden opening and
one commitment-output target, not a separate target per repeated session.

The split PartnerLaneBound already fails on the true-rho branch, since the
commitment search is charged to guessCost. The combined target also fails:
the false-rho branch enters Guess/Partner after spending the hit probability.
The split GuessLaneBound is not independently refuted by this trace. No
frozen statement has been changed, and no closed proof of the false target
is asserted.

REJECTED EXPECTED-COST ROUTE; CURRENT FIXED-CAP ROUTE

The conditional theorem hiddenCoreAt_of_domainBounds is checked, but its
expected-cost hypotheses are not the active route. Stop the commitment scan
at its first match. With a = 1 - 1/N, survival after k distinct trials is
S_k = (1-k/N)a^k and E[T] = sum_{k<M} S_k. The exact algebraic identity
stoppedOpening_charge_gap proves
  (1-S_M) - 2 E[T]/N = sum_{k<M} (k-1)a^k / N^2.
This is positive already at four trials (stoppedOpening_four). At M=2^120
the gap exceeds 2^-20. Taking B=2^96 in the earlier birthday construction
makes its failure less than 2^-40; its total extra cost is below 2^100,
whose normalized charge is at most 2^-28. The top search failure is at most
exp(-2048), not the earlier coarse 1/8 estimate. Thus the stopped variant
also refutes GuessPartnerDomainBound. This extension is a mathematical trace,
not a formal adversary construction. None of these facts refutes HiddenCoreAt.
opening_fixed_cap proves the correct 2M/N cap inequality for this search.

The replacement route separates hidden-input probes from output matches,
each with cap q/N. Output matches can use expected domain costs; true opening
probes belong to the first; different commitment preimages belong to the
second alongside chain/leaf/node output hits and top digest partners.
Top partners follow the standard second-lane orientation in
XmssSecurity.CappedTop.topEncodingCollision_afterKeygen; the existing
FirstLaneOracleSimulation encoding monitor covers only bottom partners.
OutputLaneBound and ResidualLaneBound retain the earlier assembly. The active
route is now hiddenCoreAt_of_uncharged: chargedOutput_bound closes one q/N
unit, and UnchargedLaneBound is its sole remaining probability hypothesis.
The weighted hit theorem, rather than the unweighted HitLaneBound alone,
keeps commitment and digest costs available in that first unit.

Completed protocol bridges: tsigOracles_boundExtends and
gameOracles_boundExtends make the message ledger write-once;
signingLoggedOracles_forget preserves the actual game computation;
signingLoggedOracles_bound reconstructs the bound message from the signing
transcript (including t=1, where round 1 has no message-dependent hash call);
selectedOfSigningLog_eq reconstructs the actual selected trial;
signCodeword_canonical reduces an accepted round-2 opening to the canonical
grind outside DifferentOpening. run_bottom_commitment_cached proves that
actual bottom generation caches all canonical PRF terms and commitments;
run_bottom_commitment_eq identifies each successful tree's commitment in
every extension of its cache. openingMatch_of_runs combines supported tree
and accepted codeword subruns into the final OpeningMatch event, without a
freshness assumption. receiptExposedRun_runs now extracts both witnesses
from every actual accepted session and preserves them through verification.
These support facts do not assert hidden-value independence or search freshness.

The successful round-2 release ledger is also reconstructed exactly by
signingLoggedOracles_released. signingLoggedOracles_successfulRound2 proves
that every successful transcript entry contributes a signer and retains the
same bound message in the final state. flaggedOracles_slot_revealed connects
an actual unflagged adversarial slot read to Revealed; it excludes honest
internal reads from the public share view. signRound2C_run_full retains the
actual probabilistic codeword search, identifies the returned selected share
coordinates, and preserves every internal PRF/mask call in the count.
round2ReplyRecords_consistent proves the returned records satisfy evalSum;
signingChainRecords_queriers_subset bounds each recorded chain-coordinate
querier set by actual signersAt. The causal Round2Receipt instrumentation
now replaces the arbitrary encodingAt annotations: receiptExposedRun_forget
preserves the full experiment and counter; receiptExposedRun_receipt_bound
retains the permanently bound message; receiptExposedRun_selectedEncoding
identifies every receipt at the forged key with the descent-selected trial
outside OpeningMatch. TopFacts is derived from the actual initial tree
without a Good-table hypothesis. receiptExposedRun_chain_safe proves that
every bottom coordinate below the descent-opened digit remains below
threshold in the actual receipt view, including unreleased signatures.
This covers bottom-layer Guess coordinates only; the top-layer Guess branch
still needs the public-top-signature and chain-programming argument.
publicReceiptExposedRun now records the actual public request/response log
jointly with the causal round-2 receipts. Erasure preserves the original
outcome, final cache and query count. publicShareView includes the round-1
randomizer replies and public raw-slot reads as well as the chain receipts.
publicReceiptExposedRun_chain_releaseSafe and
publicReceiptExposedRun_unbound_releaseSafe prove the threshold and revealed-read
conditions for bottom coordinates below the opened digit and for unbound
randomizers. uncharged_chain_releaseSafe discharges the no-opening-match
premise directly from UnchargedWin. These are share-table refresh conditions;
they do not assert independence from the public hash forest.
The full deferred-sampling forest/monitor coupling, selected-trial
freshness analysis, and residual monitor-cost accounting remain open. In particular,
no-receipt replay selections are not certified as actual honest trials.

Completed probability bridges: card_consistent_released_mul fixes arbitrary
earlier releases while imposing the threshold restriction only on disjoint
hidden points. refreshShareTable_joint_given_view gives an exact reversible
installation law jointly with any event of the refreshed table and value.
refreshShareTable_weighted additionally installs a prescribed value while
preserving arbitrary continuation weights. ShareProgram.balance_real proves
adaptive composition across share observations, independent randomness and
later releases. observation_record/observation_read instantiate the actual
Eval-sum and raw-slot observations; Safe.record and Safe.enlargeCorrupt retain
the invariant after releasing the coordinates whose thresholds are crossed.
adaptive_forest_eq couples this simulation jointly with any fixed-function
forest kernel. It does not assert that an arbitrary such kernel hides F.

ShareProgram.compile now interprets releases, silent probes and bottom
encoding trials in FirstLaneOracleSimulation.World. simulate_compile checks
its eager semantics; compile_real_eq/eager_result_eq_real transport the actual
share result; real_event_le applies the existing fixed-cap q/N monitor bound.
The finish constructor requires released=points before returning arbitrary
slot-table data. finishAll drains remaining coordinates by reveal queries;
real_finishAll proves that this leaves the real terminal result unchanged.
ShareProgram.compileEmbeddedFromEmpty additionally embeds the PRF coordinates
into a larger monitor pool and transports them by fixed public XOR masks.
compileEmbedded_real_eq proves exact result-distribution preservation;
compileEmbedded_bound preserves the same hazard cap. This accommodates masked
bottom coordinates and separate top intermediate labels without identifying
the latter with unused PRF points. embedded_real_event_le supplies the q/N
bound once the concrete source compiler and event detection are established.

Completed concrete forest bridges: top_rows_programmed couples the ordered
initial top chains with their entire cache, and referenceTopTree_programmed
continues through the actual Merkle construction. signing_tree_run_full
replaces the source interpreter of either tree by fixedForestImpl, retaining
the full slot table, all non-hash cache entries and every original count.
signing_top_tree_programmed connects its hash projection to the programmed
top setup. fixedForestFinalRun_eq performs the replacement inside the complete
original signing run. fixedForestFinalRun_count_le transports the real cap
through this exact replacement without a new budget assumption. It does not
yet bound monitor hazards or the cost of extra ghost computations.

The alternate private-precomputation route can reuse the standard chain
replay theorem, with a separate cache of actually visited inputs. Unrequested
failed bottom searches must remain private, rather than aborting the game.
bottomMask_table_change proves the joint invertible transformation from
uniform bottom labels to uniform public cpk rows, retaining the labels for
arbitrary later cache-dependent continuations. It applies to the stated
uniform sampling, not to arbitrary conditioned labels. Extra commitment and
randomizer queries still need their own probe/redirect cases, including the
cached randomizer used to derive topBase. Standard setup's independent topBase
cannot simply be identified with that source value.

Remaining source-specific work: compile the actual signing computations into
this interface with a causal programmed forest, prove the source/monitor
coupling up to a monitored hit, establish the hazard cap from the counted
source calls, and show that UnchargedWin forces a monitor hit. The arbitrary
forest kernel in adaptive_forest_eq does NOT discharge these obligations.
For the forest hop, the existing per-query interface is
CappedGlobalChainHighReplay.relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit
(line 1069 in that module), with setup from
CappedGlobalChainHighSetup.relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable
(line 421). Its setup must be adapted to on-demand threshold bottom trees
and the extra commitment/randomizer domains. Bottom intermediate labels
translate by public cpk XOR; top intermediate labels need auxiliary monitor
coordinates or a proved label transport, not identification with unused PRF
points. These source adaptations remain unproved. The earlier
StructuralOutputDomainBound route is superseded by chargedOutput_bound;
unresolved top partners are retained in UnchargedWin.
exposedRun_eq_presampled moves every share slot before the actual signing
experiment, retaining the entire Outcome, including the original final cache.
traceObserved keeps the ordinary cache (including internal PRG hash reads)
and reconstructs just the visited share slots from the instrumented world log.
presampled_finalRun_count_le transfers the real cap to every full share table,
including flagged branches. This instrumented log contains honest internal
answers: it is not the adversary's share view and need not remain unchanged
under the next refresh coupling.

The private-prefix route now has an exact raw-oracle lowering of finalRun,
including internal PRG streamKey reads and the original cost writer.
privateSigningRun_marginal retains the source-only cache and outcome;
signingRaw_prefix_raw_cap bounds raw source calls after every supported
private prefix, without charging that prefix. signingRaw_fresh_output_le
therefore bounds one fixed fresh-output target per input by q/N.
rawCommitmentForest_support constructs a prefix containing every canonical
commitment and no alternative. openingMatch_bound closes the concrete
noncanonical-opening subevent at q/N for all keys and sessions. This is NOT
a third additive lane. openingMatch_bound_expected sharpens it to the actual
expected commitment-domain count. private_prefix_expectedCost preserves this
count even under adaptive stopping. outputDomainCosts_le proves that this
charge and the complementary raw-domain charge sum to at most q. All
tweakable hash domains and PRF/mask slots lie in the complementary domain,
by rawOtherCall_tweakableHashInput and rawOtherCall_slot.
outputLaneBound_of_domain closes the assembly from StructuralOutputDomainBound,
which includes top partners and unopened-tree completion exceptions and is
not implied by the older unweighted HitLaneBound. The absence clause of
CanonicalCommitments must be preserved by extra forest queries using domain
separation; arbitrary cache extension alone does not preserve it.

The closed hit proof now also supplies hit_bound_structural_cost: its
completion potential charges only structural hash inputs, and its exceptional
continuations charge their designated top PRF gates. The original supported
source cap, distinct-key and small-budget hypotheses are unchanged.
structural_commitment_digest_cost_le proves that this hit charge, commitment
calls and digest calls jointly spend at most one unit per source call.
source_output_costs_le transfers that inequality to expected source costs.
hitOnlyDomainBoundClosed closes the structural half of the earlier split;
the refuted GuessPartnerDomainBound is not used. CanonicalTopCompletion uses
the exact source bottomJobs, Merkle root, top randomizer and scan. Its all-key
completion potential charges at most one unit per digest call, without
requiring a fresh selected trial. topPartner_resolved proves the bridge for
successful cached bottom ceremonies, including the exact replayed root.
alternativeCommitment_bound_source now puts commitment output matches in
the same source-cost frame. chargedOutput_bound combines these three bounds
at q/N. The hit proof's auxiliary base-zero top scans are not substituted
for the source's canonical scans.
A randomizer base can enter a cached run of failed digest trials; the residual
proof must charge those earlier trials rather than assume a fresh selected
codeword conditional on the previous cache.

Still open: UnchargedLaneBound. The actual threshold-share view must be
coupled to an adaptive silent-probe/reveal experiment, and its selected digest
must be coupled to the cached randomizer scan. This residual includes top
partners without a successful resolved bottom ceremony. The proved
uncharged_topPartner_no_successful_bottom excludes every supported successful
subrun whose cache extends into the final cache; failed subruns remain.
Rho can be installed/revealed after the first binding of the message. Chain
coordinates must be installed/revealed only at the actual signing threshold,
including threshold crossings caused by corruption; revealing them at the
first round-2 answer would invalidate freshness. The target simulator has type
QueryImpl Source (StateT SimState (OracleComp (FirstLaneOracleSimulation.World Point))):
private draws use liftProbComp, and silent probes/reveals use the existing
monitor. Public forest outputs must be included jointly in the coupling,
not conditioned away by the share-view counting lemma. The top partner
orientation additionally needs virtual precomputation or an online proof,
since the standard theorem assumes all top selections precede the forger.
If the forged bottom
tree was never requested, its replay may contain default-zero PRF values;
the descent must instead start with the genuinely cached top layer. The
current file proves the first lane and the conditional root theorem
hiddenCoreAt_of_uncharged, but does not claim UnchargedLaneBound or root closure.

Routes checked: the original split is refuted above; simply excluding Hit
does not fix commitment trials; multi-key/session amplification is prevented
by the proved input/message equalities; direct fresh-query charging fails for
hidden inputs already cached by key generation; presampling and indexed-table
coordinate lemmas still need a coupling for the full signing view; the leanVM
capped-game results do not directly apply to the threshold share interface.
The generic charging lemma therefore cannot discharge the residual on its own.
In particular a noncommitment randomizer query may guess the true opening or
have a base that coincides with a later canonical base. The choice of the
selected digest partner must be included in the charging argument; merely
counting local bad predicates would not justify the proposed one-unit charge.
-/

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.logged_probEvent_le_expectedCost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.logged_probEvent_le_expectedCost

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.loggedRun_expectedCost_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.loggedRun_expectedCost_le

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_domainBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_domainBounds

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.prf_value_uniform_given_share_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.prf_value_uniform_given_share_view

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingLoggedOracles_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingLoggedOracles_bound

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_of_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_of_runs

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_capLanes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_capLanes

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.prf_value_uniform_given_releases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.prf_value_uniform_given_releases

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.refreshShareTable_joint_given_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.refreshShareTable_joint_given_view

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.exposedRun_eq_presampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.exposedRun_eq_presampled

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.presampled_finalRun_count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.presampled_finalRun_count_le

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.topPartner_inputs_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.topPartner_inputs_cached

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.refreshShareTable_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.refreshShareTable_weighted

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.balance_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.balance_real

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.adaptive_forest_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.adaptive_forest_eq

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.simulate_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.simulate_compile

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.compile_real_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.compile_real_eq

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.eager_result_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.eager_result_eq_real

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.real_event_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.real_event_le

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.real_finishAll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.real_finishAll

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.commitment_generate_after_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.commitment_generate_after_prefix

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.referenceTopTree_programmed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.referenceTopTree_programmed

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signing_tree_run_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signing_tree_run_full

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signing_top_tree_programmed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signing_top_tree_programmed

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.fixedForestFinalRun_count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.fixedForestFinalRun_count_le

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.bottomMask_table_change' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.bottomMask_table_change

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.randomOracle_programs_commute_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.randomOracle_programs_commute_private

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.private_forest_private_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.private_forest_private_observation

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.privateRo_newTarget_bound_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.privateRo_newTarget_bound_cap

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.privateSigningRun_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.privateSigningRun_marginal

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingRaw_prefix_raw_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingRaw_prefix_raw_cap

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingRaw_fresh_output_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingRaw_fresh_output_le

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.rawCommitmentForest_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.rawCommitmentForest_support

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.privateRoCounted_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.privateRoCounted_expectedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.privateRo_expectedCost_le_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.privateRo_expectedCost_le_cap

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.private_counted_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.private_counted_expectation

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.private_prefix_expectedCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.private_prefix_expectedCost

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_bound_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_bound_expected

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.outputDomainCosts_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.outputDomainCosts_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.rawOtherCall_tweakableHashInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.rawOtherCall_tweakableHashInput

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingLoggedOracles_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingLoggedOracles_released

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingLoggedOracles_successfulRound2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingLoggedOracles_successfulRound2

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.flaggedOracles_slot_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.flaggedOracles_slot_revealed

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.round2Shares_run_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.round2Shares_run_full

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signRound2C_run_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signRound2C_run_full

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.outputLaneBound_of_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.outputLaneBound_of_domain

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_outputDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_outputDomain

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.round2ReplyRecords_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.round2ReplyRecords_consistent

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingChainRecords_queriers_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingChainRecords_queriers_subset

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_forget

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signRound2Selection_run_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signRound2Selection_run_full

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_runs

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_receipt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_receipt_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.canonical

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.selected

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_topFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_topFacts

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_selectedEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_selectedEncoding

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_chain_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptExposedRun_chain_safe

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.receiptRecords_queriers_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.receiptRecords_queriers_eq_empty

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hit_bound_structural_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hit_bound_structural_cost

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.structural_commitment_digest_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.structural_commitment_digest_cost_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.source_output_costs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.source_output_costs_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hitOnlyDomainBoundClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hitOnlyDomainBoundClosed

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.recordReads_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.recordReads_supported

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.canonicalTopGrind_record_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.canonicalTopGrind_record_selected

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.resolvedTopPartner_bound_digest_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.resolvedTopPartner_bound_digest_cost

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.resolves_referenceBottom_topGrind_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.resolves_referenceBottom_topGrind_some

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.bottomSpec_honestRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.bottomSpec_honestRoot

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.topPartner_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.topPartner_resolved

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.alternativeCommitment_bound_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.alternativeCommitment_bound_source

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.chargedOutput_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.chargedOutput_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.charged_uncharged_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.charged_uncharged_disjoint

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_uncharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hiddenCoreAt_of_uncharged

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.uncharged_topPartner_no_successful_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.uncharged_topPartner_no_successful_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.flaggedLoggedOracles_readsRevealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.flaggedLoggedOracles_readsRevealed

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_source

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_public_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_public_view

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_chain_releaseSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_chain_releaseSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_unbound_releaseSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_unbound_releaseSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.compileEmbedded_real_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.compileEmbedded_real_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.embedded_real_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ShareProgram.embedded_real_event_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.uncharged_chain_releaseSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.uncharged_chain_releaseSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.publicReceiptExposedRun_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.uncharged_public_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.uncharged_public_probability
