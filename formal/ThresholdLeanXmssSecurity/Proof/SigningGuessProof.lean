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
# The charged output events of the signing core

This module bounds the charged output events of the signing core by expected source costs. It holds
the charging lemma `probEvent_le_chargedCost`, the domain separation of the hash inputs, the message
ledger and the round-2 receipts of the signing oracles, and the canonical commitments and top trees
of a run. `SigningCoreProof.HiddenCoreAt` uses two units `2 ^ -128` for each call, and the example
at the end of the module rules out one.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss SigningCostProof

namespace SigningGuessProof
attribute [local irreducible] MonadAttach.support

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
      ∑' r, Pr{let z ← (impl t).run s}[z = r] * potential r.2 ≤
        potential s + ε * cost t s)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s)
    (hzero : potential s = 0) :
    Pr{let r ← (simulateQ impl oa).run s}[bad r.2] ≤
      ε * XmssSecurity.expectedSimulatedCost impl cost oa s := by
  refine (le_of_eq_of_le (one_mul _).symm
    (XmssSecurity.const_mul_probEvent_le_expectedFinal impl potential bad 1 hbad oa s)).trans ?_
  have h := XmssSecurity.expectedFinal_le impl hinv potential
    (fun t s => ε * cost t s) hstep oa s hs
  simpa only [hzero, zero_add, XmssSecurity.expectedSimulatedCost_const_mul] using h

abbrev LoggedState (C : Committee) :=
  (HashCache C × ℕ) × QueryLog (WorldSpec C)

/-- Logging a call increases its accumulated cost by exactly that call's cost. -/
theorem logged_step_cost {C : Committee} (prims : Primitives)
    (cost : (WorldSpec C).Domain → ℕ) (t : (WorldSpec C).Domain)
    (s : LoggedState C) :
    (∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] *
      (SigningGuessLaneProof.logCost cost r.2.2 : ℝ≥0∞)) =
      (SigningGuessLaneProof.logCost cost s.2 : ℝ≥0∞) + cost t := by
  refine OracleComp.tsum_prEvent_mul_of_const_on_support _ fun r hr => ?_
  rw [SigningHitLaneProof.loggedImpl_log prims t s r hr]
  simp [SigningGuessLaneProof.logCost, QueryLog.logQuery, QueryLog.singleton]

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
  change (∑' r, Pr{let z ← loggedRun prims A x}[z = r] *
    (SigningGuessLaneProof.logCost SeedHitProof.signCost r.2.2 : ℝ≥0∞)) ≤ q
  calc
    _ ≤ ∑' r, Pr{let z ← loggedRun prims A x}[z = r] * (q : ℝ≥0∞) := by
      refine ENNReal.tsum_le_tsum fun r => ?_
      by_cases hr : r ∈ support (loggedRun prims A x)
      · refine mul_le_mul_right ?_ _
        rw [← SigningGuessLaneProof.loggedRun_count_eq prims A x r hr]
        exact_mod_cast SigningGuessLaneProof.loggedRun_count_le prims A x q hq r hr
      · simp [prEvent_eq_zero_of_not_mem_support _ hr]
    _ ≤ q := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le (OracleComp.tsum_prEvent_le_one _)

/-- An encoded address can be recovered without inspecting its variable payload. -/
theorem address_eq_of_input_eq (P : HashSig.PublicParameter)
    (left right : LeanXmss.TweakFields) (u v : HashSig.HashInput)
    (h : HashSig.littleEndianBytes 16 P ++ LeanXmss.addressBytes left ++ u =
      HashSig.littleEndianBytes 16 P ++ LeanXmss.addressBytes right ++ v) : left = right := by
  exact (LeanXmss.fieldInput_injective h).1

/-- One commitment input cannot be a trial at two bottom keys. -/
theorem commitmentInput_key_eq (P : HashSig.PublicParameter)
    {e f : LeanXmss.KeyIndex} {ρ τ : HashSig.Digest}
    (h : commitmentInput P e ρ = commitmentInput P f τ) : e = f := by
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hlo := congrArg LeanXmss.TweakFields.lo ha
  apply Fin.ext
  have hn := congrArg BitVec.toNat hlo
  simp [LeanXmss.tweakFields] at hn
  exact (Nat.mod_eq_of_lt e.isLt).symm.trans (hn.trans (Nat.mod_eq_of_lt f.isLt))

/-- One randomizer input cannot be a trial at two keys. -/
theorem randomizerInput_key_eq (P : HashSig.PublicParameter)
    {lay lay' : LeanXmss.Layer} {e f : LeanXmss.KeyIndex}
    {ρ τ : HashSig.Digest} {m m' : HashSig.HashInput}
    (h : randomizerInput P lay e ρ m = randomizerInput P lay' f τ m') : e = f := by
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hlo := congrArg LeanXmss.TweakFields.lo ha
  apply Fin.ext
  have hn := congrArg BitVec.toNat hlo
  simp [LeanXmss.tweakFields] at hn
  exact (Nat.mod_eq_of_lt e.isLt).symm.trans (hn.trans (Nat.mod_eq_of_lt f.isLt))

set_option backward.isDefEq.respectTransparency false in
/-- A randomizer input also fixes its opening and message; repeated sessions
with this input therefore address the same cached trial. -/
theorem randomizerInput_payload_eq (P : HashSig.PublicParameter)
    {lay lay' : LeanXmss.Layer} {e f : LeanXmss.KeyIndex}
    {ρ τ : HashSig.Digest} {m m' : HashSig.HashInput}
    (h : randomizerInput P lay e ρ m = randomizerInput P lay' f τ m') :
    ρ = τ ∧ m = m' := by
  have hp : HashSig.littleEndianBytes 16 ρ ++ m = HashSig.littleEndianBytes 16 τ ++ m' :=
    (LeanXmss.fieldInput_injective (payload := HashSig.littleEndianBytes 16 ρ ++ m)
      (payload' := HashSig.littleEndianBytes 16 τ ++ m')
      (by simpa only [randomizerInput, List.append_assoc] using h)).2.2
  obtain ⟨hr, hm⟩ := List.append_inj hp (by simp [LeanXmss.bytesLE_length])
  exact ⟨LeanXmss.bytesLE_injective hr, hm⟩

/-- Commitment and randomizer trials have different address steps. -/
theorem commitmentInput_ne_randomizerInput (P : HashSig.PublicParameter)
    (e f : LeanXmss.KeyIndex) (lay : LeanXmss.Layer)
    (ρ τ : HashSig.Digest) (m : HashSig.HashInput) :
    commitmentInput P e ρ ≠ randomizerInput P lay f τ m := by
  intro h
  have ha := address_eq_of_input_eq P _ _ _ _ h
  have hs := congrArg LeanXmss.TweakFields.step ha
  norm_num [LeanXmss.tweakFields] at hs

/-- The layer bit prevents a bottom randomizer input from serving a top key. -/
theorem randomizerInput_layer_eq (P : HashSig.PublicParameter)
    {lay lay' : LeanXmss.Layer} {e f : LeanXmss.KeyIndex}
    {ρ τ : HashSig.Digest} {m m' : HashSig.HashInput}
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
    (e : LeanXmss.KeyIndex) (m m' : HashSig.Message)
    (hb : st.bound e = some m) (haccept : breaksOneMessagePerKey st e m' = false) :
    m' = m := by
  simp only [breaksOneMessagePerKey, hb, Option.any_some, decide_eq_false_iff_not,
    not_not] at haccept
  exact haccept.symm

/-- Commitment addresses are distinct from every verification hash domain. -/
theorem commitmentInput_ne_tweakableHashInput
    (P P' : HashSig.PublicParameter) (e : LeanXmss.KeyIndex) (ρ : HashSig.Digest)
    (domain : LeanXmss.HashDomain) (payload : HashSig.HashInput) :
    commitmentInput P e ρ ≠ LeanXmss.tweakableHashInput P' domain payload := by
  intro h
  have hf := (LeanXmss.fieldInput_injective
    (payload := HashSig.littleEndianBytes 16 ρ ++ HashSig.littleEndianBytes 16 0)
    (payload' := payload)
    (by simpa only [commitmentInput, LeanXmss.tweakableHashInput, LeanXmss.tweakBytes,
      List.append_assoc] using h)).1
  have ht := congrArg (fun f => f.tag.toNat) hf
  cases domain <;> norm_num [LeanXmss.hashDomainFields, LeanXmss.tweakFields] at ht

/-- Both targets of a commitment search belong to the residual lane. -/
def CommitmentInput (input : HashSig.HashInput) : Prop :=
  ∃ P e ρ, input = commitmentInput P e ρ

def CommitmentCall {C : Committee} : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inr (.inl (.hash input)))) => CommitmentInput input
  | .inr (.inr (.inl (.hash input))) => CommitmentInput input
  | _ => False

open Classical in
def commitmentCost {C : Committee} (t : (WorldSpec C).Domain) : ℕ :=
  if CommitmentCall t then 1 else 0

theorem commitmentCost_le {C : Committee} (t : (WorldSpec C).Domain) :
    commitmentCost t ≤ SeedHitProof.signCost t := by
  unfold commitmentCost
  split_ifs with hc
  · rcases t with ((n | (q | y)) | u) | (n | (q | y)) <;>
      simp_all [CommitmentCall, SeedHitProof.signCost]
  · exact Nat.zero_le _

/-- The binding ledger is write-once, including rejected calls and repeated rounds. -/
def BoundExtends {C : Committee} (st st' : TsigState C) : Prop :=
  ∀ e message, st.bound e = some message → st'.bound e = some message

theorem boundExtends_refl {C : Committee} (st : TsigState C) : BoundExtends st st :=
  fun _ _ h => h

private theorem run_liftM_comp {ι σ α : Type} {spec : OracleSpec ι}
    (p : OracleComp spec α) (st : σ) :
    (liftM p : StateT σ (OracleComp spec) α).run st = (fun a => (a, st)) <$> p := by
  rw [map_eq_bind_pure_comp]
  rfl

/-- Building a bottom tree changes only the stored trees. -/
theorem bottomOnce_frame {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (dealt : Dealt C (OracleComp spec)) (b : Fin (2 ^ LeanXmss.layerHeight)) (st : TsigState C)
    (r : Option BottomTree × TsigState C) (hr : r ∈ support ((bottomOnce dealt b).run st)) :
    r.2.corrupt = st.corrupt ∧ r.2.bound = st.bound ∧ r.2.released = st.released := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases ht : st.trees b <;>
    simp [ht, StateT.run_bind] at hr
  · obtain ⟨tree, _, rfl⟩ := hr
    simp
  · subst r
    simp

theorem tsigOracles_boundExtends {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((tsigOracles lift dealt t).run st)) : BoundExtends st r.2 := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;>
      (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [BoundExtends])
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
    obtain ⟨_, hbound, hrel⟩ := bottomOnce_frame dealt b st _ ht
    cases tree with
    | none => simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [BoundExtends]
    | some tree =>
      simp [StateT.run_bind, bind_map_left] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact fun _ _ h => hbound ▸ h
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [BoundExtends])
    · rename_i ha
      simp only [StateT.run_bind, StateT.run_set, pure_bind] at hr
      erw [StateT.run_map] at hr
      simp only [run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
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
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [BoundExtends])
    · simp only [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
      obtain ⟨_, hbound, hrel⟩ := bottomOnce_frame dealt (treeOf e) st _ ht
      cases tree with
      | none => (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [BoundExtends])
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
          mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;>
          (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [BoundExtends])

def bindingStep {C : Committee}
    (bound : LeanXmss.KeyIndex → Option HashSig.Message) :
    (t : (LocalSpec C + TsigSpec C).Domain) → (LocalSpec C + TsigSpec C).Range t →
      LeanXmss.KeyIndex → Option HashSig.Message
  | .inr (.round1 _ _ e message), some _ => Function.update bound e (some message)
  | _, _ => bound

/-- Only a completed round-2 response adds a signing release to the view. -/
def releaseStep {C : Committee} (released : List (LeanXmss.KeyIndex × HashSig.Message × C.Party)) :
    (t : (LocalSpec C + TsigSpec C).Domain) → (LocalSpec C + TsigSpec C).Range t →
      List (LeanXmss.KeyIndex × HashSig.Message × C.Party)
  | .inr (.round2 i _ e message _), some _ => released ++ [(e, message, i)]
  | _, _ => released

theorem releaseStep_append {C : Committee}
    (released : List (LeanXmss.KeyIndex × HashSig.Message × C.Party))
    (t : (LocalSpec C + TsigSpec C).Domain) (u : (LocalSpec C + TsigSpec C).Range t) :
    releaseStep released t u = released ++ releaseStep [] t u := by
  cases t with
  | inl t => simp [releaseStep]
  | inr t =>
    cases t <;> try simp [releaseStep]
    cases u <;> simp

theorem tsigOracles_releaseStep {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (t : (TsigSpec C).Domain) (st : TsigState C)
    (r : (TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((tsigOracles lift dealt t).run st)) :
    r.2.released = releaseStep st.released (.inr t) r.1 := by
  cases t with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr <;> (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [releaseStep])
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
    obtain ⟨_, hbound, hrel⟩ := bottomOnce_frame dealt b st _ ht
    cases tree with
    | none => simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [releaseStep]
    | some tree =>
      simp [StateT.run_bind, bind_map_left] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hrel
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [releaseStep])
    · simp only [StateT.run_bind, StateT.run_set, pure_bind] at hr
      erw [StateT.run_map] at hr
      simp only [run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [releaseStep])
    · simp only [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
      obtain ⟨_, hbound, hrel⟩ := bottomOnce_frame dealt (treeOf e) st _ ht
      cases tree with
      | none => (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [releaseStep])
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left,
          mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all [releaseStep])


/-- A successful round-2 reply is possible only at the already bound message. -/
theorem tsigOracles_round2_bound {C : Committee} {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp spec β)
    (dealt : Dealt C (OracleComp spec)) (st final : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : HashSig.Message)
    (parts : C.Party → HashSig.Digest) (values : LeanXmss.ChainIndex → Option HashSig.Digest)
    (hr : (some values, final) ∈ support
      ((tsigOracles lift dealt (.round2 i J e message parts)).run st)) :
    st.bound e = some message := by
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · erw [StateT.run_pure] at hr
    simp at hr
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
    split at hr <;> (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
    obtain ⟨hcorrupt, _, _⟩ := bottomOnce_frame dealt b st _ ht
    cases tree with
    | none => simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all
    | some tree =>
      simp [StateT.run_bind, bind_map_left] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hcorrupt ▸ Finset.Subset.refl _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
    · simp only [StateT.run_bind, StateT.run_set, pure_bind] at hr
      erw [StateT.run_map] at hr
      simp only [run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact Finset.Subset.refl _
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
    · simp only [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
      obtain ⟨hcorrupt, _, _⟩ := bottomOnce_frame dealt (treeOf e) st _ ht
      cases tree with
      | none => (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left, mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)

end PublicShareLog

/-- An accepted opening is either canonical or a different preimage. This is
an output-match event, distinct from the chain/leaf/node predicate `Hit`. -/
def DifferentOpening {C : Committee} (h : Query C → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (e : LeanXmss.KeyIndex)
    (canonical candidate : HashSig.Digest) : Prop :=
  candidate ≠ canonical ∧
    HashSig.truncateHash (h (.hash (commitmentInput P e candidate))) =
      HashSig.truncateHash (h (.hash (commitmentInput P e canonical)))

theorem signCodeword_some_commitment {C : Committee} (prims : Primitives)
    (h : Query C → HashSig.HashOutput) (P : HashSig.PublicParameter)
    (commitment : HashSig.Digest) (e : LeanXmss.KeyIndex) (message : HashSig.Message)
    (candidate : HashSig.Digest) (selected : HashSig.Randomizer × LeanXmss.Encoding)
    (hs : D prims h (signCodeword P commitment e message candidate) = some selected) :
    HashSig.truncateHash (h (.hash (commitmentInput P e candidate))) = commitment := by
  unfold signCodeword at hs
  change E prims h _ = some selected at hs
  rw [E_bind, E_oracleHash] at hs
  dsimp only at hs
  split at hs
  · simp [E_pure] at hs
  · simpa only [not_not] using ‹¬HashSig.truncateHash
      (h (.hash (commitmentInput P e candidate))) ≠ commitment›

section ShareFibers

open Classical TprfSecurityProof TprfCorrectnessProof

variable {C : Committee}
  (records : List (EvalRecord C)) (D : Finset C.Party)
  (hidden : Finset Point) (Tstar : C.Term)

variable (hT : D ⊆ Tstar.1)
  (hinv : ∀ x ∈ hidden, ∀ message, (D ∪ recordQueriers records x message).card ≤ C.t - 1)
  (reads : List (Slot C × HashSig.HashOutput))
  (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))

include hT hinv hreads

end ShareFibers

section ShareRefresh

open Classical TprfSecurityProof

variable {C : Committee}

/-- Install one prescribed PRF value by shifting its missing term and the
private masks that preserve previously returned shares. -/
def refreshShareTable (records : List (EvalRecord C)) (D : Finset C.Party)
    (Tstar : C.Term) (x : Point) (ω : Slot C → HashSig.HashOutput)
    (value : TprfCorrectnessProof.XorDigest) : Slot C → HashSig.HashOutput :=
  shiftTable records D {x} Tstar (fun _ => prfSum ω x + value) ω

/-- The table constraints retained by an adaptive share computation. Released
values are supplied by a fixed PRF function, jointly with the public forest. -/
structure ShareViewData (C : Committee) where
  records : List (EvalRecord C)
  reads : List (Slot C × HashSig.HashOutput)
  released : Finset Point

namespace ShareViewData


def release (v : ShareViewData C) (x : Point) : ShareViewData C :=
  { v with released := insert x v.released }

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
    (ω : Slot C → HashSig.HashOutput) (value : TprfCorrectnessProof.XorDigest) :=
  refreshShareTable v.records h.corrupt h.missing x ω value

/-- An ordinary observation only adds its answer to the retained share view.
This condition is independent of the hidden PRF function. -/
def Observation {β : Type} (v : ShareViewData C) (next : β → ShareViewData C)
    (g : (Slot C → HashSig.HashOutput) → β) : Prop :=
  (∀ b, (next b).released = v.released) ∧ ∀ b ω,
    TprfSecurityProof.Consistent (next b).records (next b).reads ∅ (fun _ => 0) ω ↔
      TprfSecurityProof.Consistent v.records v.reads ∅ (fun _ => 0) ω ∧ g ω = b

end ShareViewData

/-- A compositional proof interface for adaptive share observations and
releases. The release operation is internal to the simulation; its permission
must be established from the signing state when this interface is instantiated. -/
inductive ShareProgram (C : Committee) (points : Finset Point) : ShareViewData C → Type → Type 1
  | pure {v : ShareViewData C} {α : Type} (a : α) (safe : v.Safe)
      (subset : v.released ⊆ points) : ShareProgram C points v α
  | finish {v : ShareViewData C} {α : Type}
      (result : (Slot C → HashSig.HashOutput) → α) (released : v.released = points) :
      ShareProgram C points v α
  | observe {v : ShareViewData C} {α β : Type} [Fintype β] [DecidableEq β]
      (g : (Slot C → HashSig.HashOutput) → β) (nextView : β → ShareViewData C)
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
      (Slot C → HashSig.HashOutput) → ProbComp α
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

end ShareProgram

end ShareRefresh

section PrivateForest

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-- Two read-only random-oracle queries commute, retaining both answers and
all cache entries. In particular, neither query is assumed fresh. -/
theorem randomOracle_queries_comm {α : Type} (left right : D)
    (next : R → R → StateT (QueryCache (D →ₒ R)) ProbComp α)
    (cache : QueryCache (D →ₒ R)) :
    (do
      let a ← (D →ₒ R).randomOracle left
      let b ← (D →ₒ R).randomOracle right
      next a b).run cache =ᵈ
    (do
      let b ← (D →ₒ R).randomOracle right
      let a ← (D →ₒ R).randomOracle left
      next a b).run cache := by
  by_cases heq : left = right
  · subst right
    cases hc : cache left with
    | none =>
      simp only [StateT.run_bind, QueryImpl.withCaching_run_none _ hc, bind_map_left,
        QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind,
        EvalDistEq.refl]
    | some value =>
      simp only [StateT.run_bind, QueryImpl.withCaching_run_some _ hc, pure_bind,
        EvalDistEq.refl]
  · cases hl : cache left <;> cases hr : cache right
    · have hrl (value : R) : (cache.cacheQuery left value) right = none := by
        simpa [QueryCache.cacheQuery_of_ne, Ne.symm heq] using hr
      have hlr (value : R) : (cache.cacheQuery right value) left = none := by
        simpa [QueryCache.cacheQuery_of_ne, heq] using hl
      simp only [StateT.run_bind, QueryImpl.withCaching_run_none _ hl,
        QueryImpl.withCaching_run_none _ hr, bind_map_left]
      simp_rw [QueryImpl.withCaching_run_none _ (hrl _),
        QueryImpl.withCaching_run_none _ (hlr _), bind_map_left]
      refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.bind_right _ fun b => ?_
      refine EvalDistEq.bind_right _ fun a => ?_
      rw [QueryCache.cacheQuery_comm_of_ne cache heq]
    · have hrl (value : R) : (cache.cacheQuery left value) right = cache right :=
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq)
      simp only [StateT.run_bind, QueryImpl.withCaching_run_none _ hl,
        QueryImpl.withCaching_run_some _ hr, bind_map_left, pure_bind]
      simp_rw [QueryImpl.withCaching_run_some _ ((hrl _).trans hr), pure_bind]
      exact EvalDistEq.rfl
    · have hlr (value : R) : (cache.cacheQuery right value) left = cache left :=
        QueryCache.cacheQuery_of_ne _ _ heq
      simp only [StateT.run_bind, QueryImpl.withCaching_run_some _ hl,
        QueryImpl.withCaching_run_none _ hr, bind_map_left, pure_bind]
      simp_rw [QueryImpl.withCaching_run_some _ ((hlr _).trans hl), pure_bind]
      exact EvalDistEq.rfl
    · simp only [StateT.run_bind, QueryImpl.withCaching_run_some _ hl,
        QueryImpl.withCaching_run_some _ hr, pure_bind, EvalDistEq.refl]

abbrev PrivateRoSpec (D R : Type) := unifSpec + (D →ₒ R)

def privateRoImpl : QueryImpl (PrivateRoSpec D R) (StateT (QueryCache (D →ₒ R)) ProbComp) :=
  unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle

/-- Private uniform sampling may be interleaved with the source's oracle
queries without obstructing private forest precomputation. -/
theorem randomOracle_query_commute_private {α β : Type} (target : D)
    (source : OracleComp (PrivateRoSpec D R) α)
    (next : R → α → StateT (QueryCache (D →ₒ R)) ProbComp β)
    (cache : QueryCache (D →ₒ R)) :
    (do
      let a ← (D →ₒ R).randomOracle target
      let b ← simulateQ privateRoImpl source
      next a b).run cache =ᵈ
    (do
      let b ← simulateQ privateRoImpl source
      let a ← (D →ₒ R).randomOracle target
      next a b).run cache := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    cases input with
    | inr input =>
      change (do
        let a ← (D →ₒ R).randomOracle target
        let b ← (D →ₒ R).randomOracle input
        let c ← simulateQ privateRoImpl (continuation b)
        next a c).run cache =ᵈ (do
        let b ← (D →ₒ R).randomOracle input
        let c ← simulateQ privateRoImpl (continuation b)
        let a ← (D →ₒ R).randomOracle target
        next a c).run cache
      refine (randomOracle_queries_comm target input
        (fun a b => do
          let c ← simulateQ privateRoImpl (continuation b)
          next a c) cache).trans ?_
      simp only [StateT.run_bind]
      refine EvalDistEq.bind_right _ fun result => ?_
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
      refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
      refine EvalDistEq.bind_right _ fun value => ?_
      exact ih value cache

theorem randomOracle_programs_commute_private {α β γ : Type}
    (ghost : OracleComp (D →ₒ R) α) (source : OracleComp (PrivateRoSpec D R) β)
    (next : α → β → StateT (QueryCache (D →ₒ R)) ProbComp γ)
    (cache : QueryCache (D →ₒ R)) :
    (do
      let a ← simulateQ randomOracle ghost
      let b ← simulateQ privateRoImpl source
      next a b).run cache =ᵈ
    (do
      let b ← simulateQ privateRoImpl source
      let a ← simulateQ randomOracle ghost
      next a b).run cache := by
  induction ghost using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    refine EvalDistEq.trans ?_ (randomOracle_query_commute_private input source
      (fun answer b => do
        let a ← simulateQ randomOracle (continuation answer)
        next a b) cache)
    simp only [StateT.run_bind]
    refine EvalDistEq.bind_right _ fun result => ?_
    exact ih result.1 result.2

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
  · simp [privateRoObserve, privateRoImpl, unifFwdImpl]
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
        refine QueryCache.ext fun other => ?_
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
    (Prod.fst <$> (do
      let _ ← simulateQ randomOracle ghost
      simulateQ privateRoImpl source).run cache) =ᵈ
      (Prod.fst <$> (simulateQ privateRoImpl source).run cache) := by
  have h := randomOracle_programs_commute_private ghost source
    (fun _ result => pure result) cache
  simp only [bind_pure] at h
  refine (h.map Prod.fst).trans ?_
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right _ fun result => ?_
  exact OracleComp.EvalDistEq.bind_const _ _

theorem raw_randomOracle_cache_le {α : Type} (source : OracleComp (D →ₒ R) α)
    (cache : QueryCache (D →ₒ R)) (result : α × QueryCache (D →ₒ R))
    (hr : result ∈ support ((simulateQ randomOracle source).run cache)) : cache ≤ result.2 := by
  induction source using OracleComp.inductionOn generalizing cache with
  | pure value =>
    have heq : result = (value, cache) := by simpa using hr
    simp [heq]
  | query_bind input continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨head, hh, ht⟩ := hr
    exact (QueryImpl.withCaching_cache_le _ input cache head hh).trans (ih head.1 head.2 ht)

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

end PrivateForest

section CommitmentSimulation

open Classical

/-- A commitment input has one globally selected trial, even with many keys
and signing sessions. This decoder is independent of the hidden table. -/
def commitmentTrial (P : HashSig.PublicParameter) (input : HashSig.HashInput) :
    Option (LeanXmss.KeyIndex × HashSig.Digest) :=
  if h : ∃ trial : LeanXmss.KeyIndex × HashSig.Digest,
      commitmentInput P trial.1 trial.2 = input then some h.choose else none

theorem commitmentTrial_eq_some (P : HashSig.PublicParameter) (input : HashSig.HashInput)
    (e : LeanXmss.KeyIndex) (rho : HashSig.Digest) :
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
  · simp only [false_iff]
    exact fun heq => h ⟨(e, rho), heq⟩

variable {Index : Type} [Fintype Index] [DecidableEq Index]

end CommitmentSimulation

section SigningPresample

open TprfSecurityProof

variable {C : Committee} (prims : Primitives)
  (seeds : C.Term → HashSig.HashOutput) (pairKeys : C.Pair → HashSig.HashOutput)

section Round2Receipts

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Proof-only instrumentation retains the actual search result before any
chain shares are evaluated. It makes no additional oracle queries. -/
def signRound2WithSelection
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (part : Point → m HashSig.Digest)
    (P : HashSig.PublicParameter) (J : C.Quorum) (commitment : HashSig.Digest)
    (e : LeanXmss.KeyIndex) (message : HashSig.Message) (parts : C.Party → HashSig.Digest) :
    m (Option ((HashSig.Randomizer × LeanXmss.Encoding) × (LeanXmss.ChainIndex → Option HashSig.Digest))) := do
  let some (randomness, encoding) ← lift (signCodeword P commitment e message (combine J parts))
    | pure none
  let values ← HashSig.OverPermutation.sequenceFin fun chain =>
    if (encoding chain).val < HashSig.chainLength - 1 then
      some <$> part (.chain LeanXmss.bottomLayer e chain (encoding chain)) else pure none
  pure (some ((randomness, encoding), values))

theorem signRound2WithSelection_forget
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (part : Point → m HashSig.Digest)
    (P : HashSig.PublicParameter) (J : C.Quorum) (commitment : HashSig.Digest)
    (e : LeanXmss.KeyIndex) (message : HashSig.Message) (parts : C.Party → HashSig.Digest) :
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
  message : HashSig.Message
  randomness : HashSig.Randomizer
  encoding : LeanXmss.Encoding
  candidate : HashSig.Digest
  commitment : HashSig.Digest
  values : LeanXmss.ChainIndex → Option HashSig.Digest

/-- The full handler records a receipt only after success. Failed attempts
keep their tree build, own-share and search effects. -/
def round2WithReceipt
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α) (dealt : Dealt C m)
    (st : TsigState C) (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex)
    (message : HashSig.Message) (parts : C.Party → HashSig.Digest) :
    m (((Option (LeanXmss.ChainIndex → Option HashSig.Digest)) × TsigState C) ×
      Option (Round2Receipt C)) := do
  if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then
    pure ((none, st), none)
  else
    let (found, st) ← (bottomOnce dealt (treeOf e)).run st
    let some tree := found | pure ((none, st), none)
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
    (message : HashSig.Message) (parts : C.Party → HashSig.Digest) :
    Prod.fst <$> round2WithReceipt lift dealt st i J e message parts =
      (tsigOracles lift dealt (.round2 i J e message parts)).run st := by
  have hl {β : Type} (oa : m β) (state : TsigState C) :
      (liftM oa : StateT (TsigState C) m β).run state = (fun a => (a, state)) <$> oa := by
    simp [StateT.run_monadLift]
  unfold round2WithReceipt
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hguard
  · simp only [map_pure]
    rfl
  · simp only [map_bind, StateT.run_bind]
    congr 1
    funext found
    rcases found with ⟨_ | tree, st⟩
    · simp; rfl
    · simp only [map_bind, StateT.run_bind, hl, bind_map_left]
      congr 1
      funext own
      rw [← signRound2WithSelection_forget]
      simp only [bind_map_left]
      congr 1
      funext selected
      cases selected <;> simp [StateT.run_bind] <;> rfl

end Round2Receipts

def Round2Receipt.release (receipt : Round2Receipt C) :
    LeanXmss.KeyIndex × HashSig.Message × C.Party :=
  (receipt.key, receipt.message, receipt.party)

theorem round2WithReceipt_released {ι : Type} {spec : OracleSpec ι}
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp spec α)
    (dealt : Dealt C (OracleComp spec)) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : HashSig.Message)
    (parts : C.Party → HashSig.Digest)
    (result : (Option (LeanXmss.ChainIndex → Option HashSig.Digest) × TsigState C) ×
      Option (Round2Receipt C))
    (hr : result ∈ support (round2WithReceipt lift dealt st i J e message parts)) :
    result.1.2.released = st.released ++ result.2.toList.map Round2Receipt.release := by
  unfold round2WithReceipt at hr
  split at hr
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst result
    simp
  · simp only [mem_support_bind_iff] at hr
    obtain ⟨⟨found, st'⟩, ht, hr⟩ := hr
    obtain ⟨_, _, hrel⟩ := bottomOnce_frame dealt (treeOf e) st _ ht
    cases found with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst result
      simpa using hrel
    | some tree =>
      simp only [mem_support_bind_iff] at hr
      obtain ⟨own, _, selected, _, hr⟩ := hr
      cases selected with
      | none =>
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst result
        simpa using hrel
      | some selected =>
        obtain ⟨⟨randomness, encoding⟩, values⟩ := selected
        simp only [support_pure, Set.mem_singleton_iff] at hr
        subst result
        simpa [Round2Receipt.release] using hrel

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
  | inl input => simp [signingWithReceipt.eq_def, Functor.map_map]
  | inr input =>
    cases input <;> try simp [signingWithReceipt.eq_def, Functor.map_map]
    exact round2WithReceipt_forget (fun oa => SigningCoreProof.honestLift oa) dealt _ _ _ _ _ _

def signingReceiptOracles (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT (TsigState C × List (Round2Receipt C)) (OracleComp (WorldSpec C))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1.1, (result.1.2, state.2 ++ result.2.toList))) <$>
      signingWithReceipt dealt state.1 input

theorem signingWithReceipt_released (dealt : Dealt C (OracleComp (WorldSpec C)))
    (st : TsigState C) (input : (LocalSpec C + TsigSpec C).Domain)
    (result : ((LocalSpec C + TsigSpec C).Range input × TsigState C) × Option (Round2Receipt C))
    (hr : result ∈ support (signingWithReceipt dealt st input)) :
    result.1.2.released = st.released ++ result.2.toList.map Round2Receipt.release := by
  cases input with
  | inl input =>
    simp only [signingWithReceipt.eq_def, support_map, Set.mem_image] at hr
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
      simp only [signingWithReceipt.eq_def, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      simpa [releaseStep] using tsigOracles_releaseStep
        (fun oa => SigningCoreProof.honestLift oa) dealt (.corrupt i) st z hz
    | tree b =>
      simp only [signingWithReceipt.eq_def, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      simpa [releaseStep] using tsigOracles_releaseStep
        (fun oa => SigningCoreProof.honestLift oa) dealt (.tree b) st z hz
    | round1 i J e message =>
      simp only [signingWithReceipt.eq_def, support_map, Set.mem_image] at hr
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
  simp only [Functor.map_map] at h
  simp only [flaggedReceiptOracles, StateT.run_mk, Functor.map_map]
  rw [h]
  cases input <;> simp [SigningCoreProof.flaggedOracles, SigningCoreProof.gameOracles,
    receiptFlag, Functor.map_map]

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

def signingSlots (s : SeedHitProof.WState C) : SlotCache C := s.1.2

def setSigningSlots (s : SeedHitProof.WState C) (cache : SlotCache C) : SeedHitProof.WState C :=
  ((s.1.1, cache), s.2)

/-- Presampling a slot changes neither the signing result nor its query count.
The continuation may retain all observable state except unused slot entries. -/
def PresampledSigning (slot : Slot C) {α : Type} (oa : OracleComp (WorldSpec C) α) : Prop :=
  Presampled signingSlots setSigningSlots slot
    (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa)

theorem presampled_signing_local (slot : Slot C) (t : (LocalSpec C).Domain) :
    Presampled₁ slot (SeedHitProof.routedLocal prims seeds pairKeys t) := by
  rcases t with n | q | y
  · exact presampled_onCache slot _
  · rw [SeedHitProof.routedLocal]
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

/-- Move an arbitrary finite set of fresh share slots before the signing experiment.
The observation retains the counted budget, not just the Boolean outcome. -/
theorem presample_signing_slots_observe {α β : Type} (oa : OracleComp (WorldSpec C) α)
    (observe : α → HashCache C → ℕ → β)
    (h : ∀ slot, PresampledSigning prims seeds pairKeys slot oa)
    (l : List (Slot C)) (hl : l.Nodup) (p : SeedHitProof.WState C)
    (hp : ∀ s ∈ l, signingSlots p s = none) :
    (($ᵗ (Slot C → HashSig.HashOutput)) >>= fun ω =>
      (fun z => observe z.1 z.2.1.1 z.2.2) <$>
        (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa).run
          (setSigningSlots p (fillSlots ω l (signingSlots p)))) =ᵈ
    ((fun z => observe z.1 z.2.1.1 z.2.2) <$>
      (simulateQ (SeedHitProof.splitWorld prims seeds pairKeys) oa).run p) := by
  induction l with
  | nil =>
    simp only [fillSlots]
    exact evalDist_uniform_bind_const (α := Slot C → HashSig.HashOutput) _
  | cons s l ih =>
    have hs : s ∉ l := (List.nodup_cons.mp hl).1
    refine (evalDistEq_uniformSample_bind_update (D := Slot C)
      (R := HashSig.HashOutput) s _).symm.trans ?_
    simp only [fillSlots, fillSlots_update _ l _ hs, Function.update_self]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun g => ?_)
      (ih (List.nodup_cons.mp hl).2 (fun a ha => hp a (List.mem_cons_of_mem _ ha)))
    have hfresh : signingSlots (setSigningSlots p (fillSlots g l (signingSlots p))) s = none := by
      change fillSlots g l (signingSlots p) s = none
      rw [fillSlots_of_not_mem g l _ hs]
      exact hp s (List.mem_cons_self ..)
    have heq := h s (setSigningSlots p (fillSlots g l (signingSlots p))) hfresh
      (fun z => (pure (observe z.1 z.2.1.1 z.2.2) : ProbComp β))
      (fun a p' _ => evalDist_uniform_bind_const (α := HashSig.HashOutput)
        (pure (observe a p'.1.1 p'.2)))
    simp only [map_eq_bind_pure_comp]
    exact heq

end SigningPresample

section SigningRawOracle

variable {C : Committee} (prims : Primitives)

abbrev SigningRawSpec (C : Committee) := PrivateRoSpec (Query C) HashSig.HashOutput

/-- Lower local calls to their actual primitive RO accesses. The PRG's
stream-key read is explicit here, so observation includes its cache entry. -/
def signingRawLocal : QueryImpl (LocalSpec C) (OracleComp (SigningRawSpec C))
  | .inl n => query (spec := SigningRawSpec C) (.inl n)
  | .inr (.inl input) => query (spec := SigningRawSpec C) (.inr input)
  | .inr (.inr input) => do
      let derived ← query (spec := SigningRawSpec C) (.inr (.streamKey input.2.1))
      pure (prims.aes.eval (HashSig.truncateHash derived) input.2.2)

def signingRawWorld : QueryImpl (WorldSpec C) (OracleComp (SigningRawSpec C))
  | .inl (.inl input) => signingRawLocal prims input
  | .inr input => signingRawLocal prims input
  | .inl (.inr _) => pure false

theorem signingRawLocal_eq (input : (LocalSpec C).Domain) :
    simulateQ privateRoImpl (signingRawLocal prims input) = signingLocalAnswer prims input := by
  rcases input with n | input | input
  · exact (simulateQ_query _ _).trans (id_map _)
  · exact (simulateQ_query _ _).trans (id_map _)
  · simp only [signingRawLocal, simulateQ_bind, simulateQ_pure]
    have h : simulateQ (privateRoImpl (D := Query C) (R := HashSig.HashOutput))
        (query (spec := SigningRawSpec C) (.inr (.streamKey input.2.1))) =
          (Query C →ₒ HashSig.HashOutput).randomOracle (.streamKey input.2.1) :=
      (simulateQ_query _ _).trans (id_map _)
    rw [h]
    rfl

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
      exact caches_bind_left prims q _ _ (ih ha)

theorem caches_hashQuery {C : Committee} (prims : Primitives) (q : Query C) :
    Caches prims q (SigningSecurityProof.liftFree (hashQuery q)) := by
  intro s r hr
  exact ⟨r.1, SigningCacheProof.run_hashQuery prims q s r hr⟩

/-- Every PRF term, not just a fresh one, is cached by the actual execution. -/
theorem caches_prfValue {C : Committee} (prims : Primitives)
    (seeds : C.Term → HashSig.HashOutput) (point : Point) (T : C.Term) :
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
    (seeds : C.Term → HashSig.HashOutput) (P : HashSig.PublicParameter)
    (e : LeanXmss.KeyIndex) :
    referenceJob tweakable (prfValue seeds) P
      ⟨.commitment e, [.randomizer LeanXmss.bottomLayer e]⟩ =
      (prfValue seeds (.randomizer LeanXmss.bottomLayer e) >>= fun canonical =>
        (bitsOfDigest ∘ HashSig.truncateHash) <$>
          hashQuery (.hash (commitmentInput P e canonical))) := by
  simp [referenceJob, List.mapM_cons, List.mapM_nil,
    tweakable_oracleHash]

/-- Running the commitment job caches the PRF terms and its resulting hash
input. The canonical value is evaluated in any extension of the final cache. -/
theorem run_referenceCommitment_cached {C : Committee} (prims : Primitives)
    (seeds : C.Term → HashSig.HashOutput) (P : HashSig.PublicParameter)
    (e : LeanXmss.KeyIndex) (s : HashCache C × ℕ)
    (r : List Bit × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceJob tweakable (prfValue seeds) P
        ⟨.commitment e, [.randomizer LeanXmss.bottomLayer e]⟩))).run s))
    (h : Query C → HashSig.HashOutput) (ha : Agrees h r.2.1) :
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
      (bitsOfDigest ∘ HashSig.truncateHash) (caches_hashQuery prims _)
    apply hc p.2 r
    change r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningCacheProof.freeHom ((bitsOfDigest ∘ HashSig.truncateHash) <$>
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
    (seeds : C.Term → HashSig.HashOutput) (P : HashSig.PublicParameter)
    (top : TopTree) (e : LeanXmss.KeyIndex) (s : HashCache C × ℕ)
    (r : Option TreeOutput × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue seeds) P
        top (.bottom (treeOf e))))).run s))
    (h : Query C → HashSig.HashOutput) (ha : Agrees h r.2.1) :
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
    (P : HashSig.PublicParameter) (commitment : HashSig.Digest)
    (e : LeanXmss.KeyIndex) (message : HashSig.Message) (candidate : HashSig.Digest) :
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
    (seeds : C.Term → HashSig.HashOutput) (P : HashSig.PublicParameter)
    (top : TopTree) (e : LeanXmss.KeyIndex) (s : HashCache C × ℕ)
    (r : Option TreeOutput × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue seeds) P
        top (.bottom (treeOf e))))).run s))
    (h : Query C → HashSig.HashOutput) (ha : Agrees h r.2.1)
    (htop : TopFacts prims h seeds P top) (tree : BottomTree)
    (hs : r.1 = some (.bottom tree)) :
    tree.commitment e = HashSig.truncateHash (h (.hash (commitmentInput P e
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

def cachedRandomizer (seeds : C.Term → HashSig.HashOutput) (cache : HashCache C)
    (e : LeanXmss.KeyIndex) : HashSig.Digest :=
  (C.terms.map fun T => HashSig.truncateHash
    ((cache (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))).getD 0)).foldl (· ^^^ ·) 0

def RandomizerCached (seeds : C.Term → HashSig.HashOutput) (cache : HashCache C)
    (e : LeanXmss.KeyIndex) : Prop :=
  ∀ T : C.Term, ∃ output, cache (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) = some output

theorem cachedRandomizer_eq (prims : Primitives) (seeds : C.Term → HashSig.HashOutput)
    (cache : HashCache C) (e : LeanXmss.KeyIndex) :
    D prims (fun input => (cache input).getD 0)
      (prfValue seeds (.randomizer LeanXmss.bottomLayer e)) = cachedRandomizer seeds cache e := by
  rw [prfValue, D_bind, D_mapM, D_pure]
  simp only [prf, D_map, D_hashQuery, cachedRandomizer]

theorem cachedRandomizer_stable (seeds : C.Term → HashSig.HashOutput)
    (left right : HashCache C) (e : LeanXmss.KeyIndex)
    (hle : left ≤ right) (hc : RandomizerCached seeds left e) :
    cachedRandomizer seeds left e = cachedRandomizer seeds right e := by
  unfold cachedRandomizer
  congr 1
  apply List.map_congr_left
  intro T _
  obtain ⟨value, hv⟩ := hc T
  rw [hv, hle hv]

def AlternativeCommitment (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C) : Prop :=
  ∃ e candidate canonicalOutput candidateOutput,
    RandomizerCached seeds cache e ∧
    cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e))) = some canonicalOutput ∧
    cache (.hash (commitmentInput P e candidate)) = some candidateOutput ∧
    candidate ≠ cachedRandomizer seeds cache e ∧
    HashSig.truncateHash candidateOutput = HashSig.truncateHash canonicalOutput

theorem alternativeCommitment_mono (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (left right : HashCache C) (hle : left ≤ right)
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
def CanonicalCommitments (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C) : Prop :=
  ∀ e, RandomizerCached seeds cache e ∧
    (∃ output, cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e))) = some output) ∧
    ∀ candidate, candidate ≠ cachedRandomizer seeds cache e →
      cache (.hash (commitmentInput P e candidate)) = none

def commitmentOutputTarget (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C) : Query C → HashSig.Digest
  | .hash input => ((commitmentTrial P input).map fun trial => HashSig.truncateHash
      ((cache (.hash (commitmentInput P trial.1 (cachedRandomizer seeds cache trial.1)))).getD 0)).getD 0
  | _ => 0

theorem commitmentOutputTarget_eq (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C) (input : HashSig.HashInput)
    (e : LeanXmss.KeyIndex) (candidate : HashSig.Digest)
    (ht : commitmentTrial P input = some (e, candidate)) :
    commitmentOutputTarget seeds P cache (.hash input) = HashSig.truncateHash
      ((cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e)))).getD 0) := by
  simp only [commitmentOutputTarget, ht, Option.map_some, Option.getD_some]

def rawRandomizerTerms (seeds : C.Term → HashSig.HashOutput) (e : LeanXmss.KeyIndex)
    (terms : List C.Term) : OracleComp (Query C →ₒ HashSig.HashOutput) (List HashSig.Digest) :=
  terms.mapM fun T => HashSig.truncateHash <$>
    query (spec := Query C →ₒ HashSig.HashOutput) (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))

theorem rawRandomizerTerms_support (seeds : C.Term → HashSig.HashOutput)
    (e : LeanXmss.KeyIndex) (terms : List C.Term) (cache : HashCache C)
    (result : List HashSig.Digest × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (rawRandomizerTerms seeds e terms)).run cache)) :
    result.1 = terms.map (fun T => HashSig.truncateHash
      ((result.2 (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))).getD 0)) ∧
    (∀ T ∈ terms, ∃ value, result.2 (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e)) = some value) ∧
    ∀ input, result.2 (.hash input) = cache (.hash input) := by
  induction terms generalizing cache result with
  | nil =>
    have heq : result = ([], cache) := by simpa [rawRandomizerTerms] using hr
    subst result
    simp
  | cons T terms ih =>
    simp only [rawRandomizerTerms, List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_map_left, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨head, hh, tail, ht, rfl⟩ := hr
    obtain ⟨hvalues, hterms, hhashes⟩ := ih head.2 tail ht
    have hquery : simulateQ randomOracle
        (query (spec := Query C →ₒ HashSig.HashOutput)
          (.prf (seeds T) (.randomizer LeanXmss.bottomLayer e))) =
        (Query C →ₒ HashSig.HashOutput).randomOracle
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

def rawRandomizer (seeds : C.Term → HashSig.HashOutput) (e : LeanXmss.KeyIndex) :
    OracleComp (Query C →ₒ HashSig.HashOutput) HashSig.Digest :=
  (fun values => values.foldl (· ^^^ ·) 0) <$> rawRandomizerTerms seeds e C.terms

theorem rawRandomizer_support (seeds : C.Term → HashSig.HashOutput)
    (e : LeanXmss.KeyIndex) (cache : HashCache C) (result : HashSig.Digest × HashCache C)
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

def CommitmentsCanonical (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C) : Prop :=
  ∀ e candidate output, cache (.hash (commitmentInput P e candidate)) = some output →
    RandomizerCached seeds cache e ∧ candidate = cachedRandomizer seeds cache e

def CommitmentCached (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C) (e : LeanXmss.KeyIndex) : Prop :=
  RandomizerCached seeds cache e ∧
    ∃ output, cache (.hash (commitmentInput P e (cachedRandomizer seeds cache e))) = some output

theorem randomizerCached_mono (seeds : C.Term → HashSig.HashOutput)
    (left right : HashCache C) (hle : left ≤ right) (e : LeanXmss.KeyIndex)
    (hc : RandomizerCached seeds left e) : RandomizerCached seeds right e := by
  intro T
  obtain ⟨value, hv⟩ := hc T
  exact ⟨value, hle hv⟩

theorem commitmentCached_mono (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (left right : HashCache C) (hle : left ≤ right)
    (e : LeanXmss.KeyIndex) (hc : CommitmentCached seeds P left e) :
    CommitmentCached seeds P right e := by
  obtain ⟨hc, value, hv⟩ := hc
  refine ⟨randomizerCached_mono seeds left right hle e hc, value, ?_⟩
  rw [← cachedRandomizer_stable seeds left right e hle hc]
  exact hle hv

def rawCommitment (seeds : C.Term → HashSig.HashOutput) (P : HashSig.PublicParameter)
    (e : LeanXmss.KeyIndex) : OracleComp (Query C →ₒ HashSig.HashOutput) Unit := do
  let rho ← rawRandomizer seeds e
  let _ ← query (spec := Query C →ₒ HashSig.HashOutput) (.hash (commitmentInput P e rho))
  pure ()

theorem rawCommitment_support (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (e : LeanXmss.KeyIndex) (cache : HashCache C)
    (hc : CommitmentsCanonical seeds P cache) (result : Unit × HashCache C)
    (hr : result ∈ support ((simulateQ randomOracle (rawCommitment seeds P e)).run cache)) :
    CommitmentsCanonical seeds P result.2 ∧ CommitmentCached seeds P result.2 e := by
  simp only [rawCommitment, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hr
  obtain ⟨middle, hm, last, hl, rfl⟩ := hr
  obtain ⟨hrho, hslots, hhashes⟩ := rawRandomizer_support seeds e cache middle hm
  have hmid := raw_randomOracle_cache_le (rawRandomizer seeds e) cache middle hm
  have hquery : simulateQ randomOracle
      (query (spec := Query C →ₒ HashSig.HashOutput) (.hash (commitmentInput P e middle.1))) =
        (Query C →ₒ HashSig.HashOutput).randomOracle (.hash (commitmentInput P e middle.1)) :=
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

theorem rawCommitments_support (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (keys : List LeanXmss.KeyIndex) (cache : HashCache C)
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

def rawCommitmentForest (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) : OracleComp (Query C →ₒ HashSig.HashOutput) (List Unit) :=
  (Finset.univ.toList : List LeanXmss.KeyIndex).mapM (rawCommitment seeds P)

theorem rawCommitmentForest_support (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (result : List Unit × HashCache C)
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
  change HashSig.truncateHash
      ((result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex candidate))).getD 0) =
    HashSig.truncateHash
      ((result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex
        (D prims (fun input => (result.2.1 input).getD 0)
          (prfValue x.2.1 (.randomizer LeanXmss.bottomLayer forgery.signature.leafIndex)))))).getD 0) at heq
  rw [hcanon, hcanonical] at heq
  change result.2.1 (.hash (commitmentInput x.1 forgery.signature.leafIndex candidate)) =
    some candidateOutput at hcandidate
  simpa only [hcandidate, Option.getD_some] using heq

/-- Only commitment queries at this public parameter can incur the opening
output charge. The other raw domains remain available to the structural lane. -/
def RawCommitmentInput (P : HashSig.PublicParameter) : Query C → Prop
  | .hash input => (commitmentTrial P input).isSome
  | _ => False

end AlternativeCommitments

section ReceiptCache


variable {C : Committee}

/-- Each accepted receipt has a codeword-search subrun. Later share queries
can only extend the cache containing that search. -/
theorem signRound2Selection_run_code (prims : Primitives)
    (part : Point → OracleComp (WorldSpec C) HashSig.Digest)
    (P : HashSig.PublicParameter) (J : C.Quorum) (commitment : HashSig.Digest)
    (e : LeanXmss.KeyIndex) (message : HashSig.Message) (parts : C.Party → HashSig.Digest)
    (s : HashCache C × ℕ)
    (r : Option ((HashSig.Randomizer × LeanXmss.Encoding) ×
      (LeanXmss.ChainIndex → Option HashSig.Digest)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (signRound2WithSelection (fun oa => SigningSecurityProof.liftFree oa) part
        P J commitment e message parts)).run s))
    (selected : HashSig.Randomizer × LeanXmss.Encoding)
    (values : LeanXmss.ChainIndex → Option HashSig.Digest)
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
    (rCode : Option (HashSig.Randomizer × LeanXmss.Encoding) × HashCache C × ℕ),
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

/-- Every successful stored tree retains a counted construction witness in the cache. -/
def StoredTreeRuns (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (cache : HashCache C) (st : TsigState C) : Prop :=
  ∀ b tree, st.trees b = some (some tree) →
    ∃ (start : HashCache C × ℕ) (result : Option TreeOutput × HashCache C × ℕ),
      result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
          top (.bottom b)))).run start) ∧
      result.1 = some (.bottom tree) ∧ result.2.1 ≤ cache

theorem StoredTreeRuns.mono (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) {cache cache' : HashCache C} {st : TsigState C}
    (hle : cache ≤ cache') (hr : StoredTreeRuns prims x top cache st) :
    StoredTreeRuns prims x top cache' st := by
  intro b tree ht
  obtain ⟨start, result, hs, ho, hc⟩ := hr b tree ht
  exact ⟨start, result, hs, ho, hc.trans hle⟩

theorem receiptDealt_bottom_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (b : Fin (2 ^ LeanXmss.layerHeight)) (s : HashCache C × ℕ)
    (r : Option BottomTree × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((receiptDealt x top).bottom b)).run s)) (tree : BottomTree) (ht : r.1 = some tree) :
    ∃ result, result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
        top (.bottom b)))).run s) ∧
      result.1 = some (.bottom tree) ∧ result.2.1 = r.2.1 := by
  rw [receiptDealt_bottom] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨result, hs, rfl⟩ := hr
  refine ⟨result, hs, ?_, rfl⟩
  cases hout : result.1 with
  | none => simp [hout] at ht
  | some value => cases value <;> simpa [hout] using ht

theorem bottomOnce_storedTreeRuns (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (b : Fin (2 ^ LeanXmss.layerHeight)) (st : TsigState C)
    (s : HashCache C × ℕ) (hinv : StoredTreeRuns prims x top s.1 st)
    (r : (Option BottomTree × TsigState C) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((bottomOnce (receiptDealt x top) b).run st)).run s)) :
    StoredTreeRuns prims x top r.2.1 r.1.2 := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases ht : st.trees b with
  | some stored =>
    simp only [ht, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hinv
  | none =>
    simp only [ht, StateT.run_bind, run_liftM_comp, bind_map_left,
      StateT.run_modify, StateT.run_pure, pure_bind] at hr
    obtain ⟨built, hb, hr⟩ := SigningCacheProof.run_bind_support prims _ _ s r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    intro b' tree htree
    by_cases he : b' = b
    · subst b'
      have ho : built.1 = some tree := by simpa using htree
      obtain ⟨result, hs, ho, hc⟩ := receiptDealt_bottom_runs prims x top b s built hb tree ho
      exact ⟨s, result, hs, ho, hc.le⟩
    · have old : st.trees b' = some (some tree) := by simpa [Function.update_of_ne he] using htree
      exact StoredTreeRuns.mono prims x top
        (SigningCacheProof.countRun_grows prims _ s built hb) hinv b' tree old

theorem round2WithReceipt_subruns (prims : Primitives)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (st : TsigState C) (i : C.Party) (J : C.Quorum)
    (e : LeanXmss.KeyIndex) (message : HashSig.Message) (parts : C.Party → HashSig.Digest)
    (s : HashCache C × ℕ)
    (r : ((Option (LeanXmss.ChainIndex → Option HashSig.Digest) × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (round2WithReceipt (fun oa => SigningSecurityProof.liftFree oa)
        dealt st i J e message parts)).run s))
    (receipt : Round2Receipt C) (hs : r.1.2 = some receipt) :
    ∃ (tree : BottomTree) (sCode : HashCache C × ℕ)
      (rCode : Option (HashSig.Randomizer × LeanXmss.Encoding) × HashCache C × ℕ),
      receipt.key = e ∧
      ((∃ rTree, rTree ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        (dealt.bottom (treeOf e))).run s) ∧ rTree.1 = some tree ∧ rTree.2.1 ≤ r.2.1) ∨
        st.trees (treeOf e) = some (some tree)) ∧ receipt.commitment = tree.commitment e ∧
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
    cases ht : rTree.1.1 with
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
        refine ⟨tree, rOwn.2, rCode, rfl, ?_, rfl,
          hCode, hCodeOut, hCodeLe.trans hSelectedLe⟩
        simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind] at hTree
        cases hstored : st.trees (treeOf e) with
        | some stored =>
          simp only [hstored, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hTree
          rw [hTree] at ht
          exact Or.inr (congrArg some ht)
        | none =>
          simp only [hstored, StateT.run_bind, run_liftM_comp, bind_map_left,
            StateT.run_modify, StateT.run_pure, pure_bind] at hTree
          obtain ⟨built, hb, heq⟩ := SigningCacheProof.run_bind_support prims _ _ s rTree hTree
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at heq
          subst rTree
          exact Or.inl ⟨built, hb, ht, hTreeLe⟩

theorem round2WithReceipt_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (st : TsigState C) (i : C.Party) (J : C.Quorum)
    (e : LeanXmss.KeyIndex) (message : HashSig.Message) (parts : C.Party → HashSig.Digest)
    (s : HashCache C × ℕ)
    (r : ((Option (LeanXmss.ChainIndex → Option HashSig.Digest) × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (round2WithReceipt (fun oa => SigningSecurityProof.liftFree oa)
        (receiptDealt x top) st i J e message parts)).run s))
    (hstored : StoredTreeRuns prims x top s.1 st)
    (receipt : Round2Receipt C) (hs : r.1.2 = some receipt) :
    ReceiptRuns prims x top r.2.1 receipt := by
  obtain ⟨tree, sCode, rCode, he, ht, hc, hcode, hco, hcl⟩ :=
    round2WithReceipt_subruns prims _ st i J e message parts s r (by exact hr) receipt hs
  have htree : ∃ start result,
      result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1
          top (.bottom (treeOf e))))).run start) ∧
      result.1 = some (.bottom tree) ∧ result.2.1 ≤ r.2.1 := by
    rcases ht with ⟨rBottom, ht, hto, htl⟩ | ht
    · obtain ⟨result, hs, ho, hc⟩ := receiptDealt_bottom_runs prims x top _ s rBottom ht tree hto
      exact ⟨s, result, hs, ho, hc.le.trans htl⟩
    · exact StoredTreeRuns.mono prims x top
        (SigningCacheProof.countRun_grows prims _ s r hr) hstored _ tree ht
  obtain ⟨start, result, ht, ho, hl⟩ := htree
  refine ⟨tree, start, result, sCode, rCode, ?_, ho, hl, ?_, hcode, hco, hcl⟩
  · simpa only [he] using ht
  · simpa only [he] using hc

theorem signingWithReceipt_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) (st : TsigState C) (input : (LocalSpec C + TsigSpec C).Domain)
    (s : HashCache C × ℕ)
    (r : (((LocalSpec C + TsigSpec C).Range input × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (signingWithReceipt (receiptDealt x top) st input)).run s))
    (hstored : StoredTreeRuns prims x top s.1 st)
    (receipt : Round2Receipt C) (hs : r.1.2 = some receipt) :
    ReceiptRuns prims x top r.2.1 receipt := by
  cases input with
  | inl input =>
    simp only [signingWithReceipt.eq_def, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨out, _, rfl⟩ := hr
    contradiction
  | inr input =>
    cases input with
    | round2 i J e message parts =>
      exact round2WithReceipt_runs prims x top st i J e message parts s r (by exact hr) hstored receipt hs
    | corrupt i | tree b | round1 i J e message =>
      simp only [signingWithReceipt.eq_def, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨out, _, rfl⟩ := hr
      contradiction

theorem round2WithReceipt_storedTreeRuns (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree) (st : TsigState C)
    (i : C.Party) (J : C.Quorum) (e : LeanXmss.KeyIndex) (message : HashSig.Message)
    (parts : C.Party → HashSig.Digest) (s : HashCache C × ℕ)
    (hinv : StoredTreeRuns prims x top s.1 st)
    (r : ((Option (LeanXmss.ChainIndex → Option HashSig.Digest) × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (round2WithReceipt (fun oa => SigningSecurityProof.liftFree oa)
        (receiptDealt x top) st i J e message parts)).run s)) :
    StoredTreeRuns prims x top r.2.1 r.1.1.2 := by
  unfold round2WithReceipt at hr
  split at hr
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hinv
  · obtain ⟨mid, hm, hr, hle⟩ := run_bind_support_grows prims _ _ s r hr
    have hi := StoredTreeRuns.mono prims x top hle
      (bottomOnce_storedTreeRuns prims x top (treeOf e) st s hinv mid hm)
    cases ht : mid.1.1 with
    | none =>
      simp only [ht, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      simpa only [hr, StoredTreeRuns] using hi
    | some tree =>
      simp only [ht] at hr
      obtain ⟨own, _, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
      obtain ⟨selected, _, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
      cases hs : selected.1 with
      | none =>
        simp only [hs, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
        simpa only [hr, StoredTreeRuns] using hi
      | some selection =>
        rcases selection with ⟨⟨randomness, encoding⟩, values⟩
        simp only [hs, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
        simpa only [hr, StoredTreeRuns] using hi

set_option backward.isDefEq.respectTransparency false in
theorem signingWithReceipt_storedTreeRuns (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree) (st : TsigState C)
    (input : (LocalSpec C + TsigSpec C).Domain) (s : HashCache C × ℕ)
    (hinv : StoredTreeRuns prims x top s.1 st)
    (r : (((LocalSpec C + TsigSpec C).Range input × TsigState C) ×
      Option (Round2Receipt C)) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (signingWithReceipt (receiptDealt x top) st input)).run s)) :
    StoredTreeRuns prims x top r.2.1 r.1.1.2 := by
  cases input with
  | inl input =>
    simp only [signingWithReceipt.eq_def, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨out, ho, rfl⟩ := hr
    change out ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((fun answer => (answer, st)) <$> worldRoles.adversary
        (OracleComp.lift (OracleSpec.query input)))).run s) at ho
    simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at ho
    obtain ⟨answer, ha, rfl⟩ := ho
    exact StoredTreeRuns.mono prims x top (SigningCacheProof.countRun_grows prims _ s answer ha) hinv
  | inr input =>
    cases input with
    | round2 i J e message parts =>
      exact round2WithReceipt_storedTreeRuns prims x top st i J e message parts s hinv r hr
    | corrupt i =>
      simp only [signingWithReceipt.eq_def, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨out, ho, rfl⟩ := hr
      change out ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((tsigOracles (fun oa => SigningSecurityProof.liftFree oa) (receiptDealt x top) (.corrupt i)).run st)).run s) at ho
      simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at ho
      split at ho <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
          support_pure, Set.mem_singleton_iff] at ho <;> subst out <;> exact hinv
    | round1 i J e message =>
      simp only [signingWithReceipt.eq_def, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨out, ho, rfl⟩ := hr
      change out ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((tsigOracles (fun oa => SigningSecurityProof.liftFree oa) (receiptDealt x top)
          (.round1 i J e message)).run st)).run s) at ho
      simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at ho
      split at ho
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at ho
        subst out
        exact hinv
      · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map,
          run_liftM_comp, Functor.map_map, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at ho
        obtain ⟨answer, ha, rfl⟩ := ho
        exact StoredTreeRuns.mono prims x top (SigningCacheProof.countRun_grows prims _ s answer ha) hinv
    | tree b =>
      simp only [signingWithReceipt.eq_def, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨out, ho, rfl⟩ := hr
      change out ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((tsigOracles (fun oa => SigningSecurityProof.liftFree oa) (receiptDealt x top) (.tree b)).run st)).run s) at ho
      simp only [tsigOracles, StateT.run_bind] at ho
      obtain ⟨mid, hm, ho, hle⟩ := run_bind_support_grows prims _ _ s out ho
      have hi := StoredTreeRuns.mono prims x top hle
        (bottomOnce_storedTreeRuns prims x top b st s hinv mid hm)
      cases ht : mid.1.1 with
      | none =>
        simp only [ht, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at ho
        subst out
        exact hi
      | some tree =>
        simp only [ht, StateT.run_bind, run_liftM_comp, bind_map_left, StateT.run_pure] at ho
        obtain ⟨answer, _, heq⟩ := SigningCacheProof.run_bind_support prims _ _ _ out ho
        rw [MonadAttach.mem_support] at heq
        change out = ((some (tree, answer.1), mid.1.2), answer.2) at heq
        subst out
        exact hi

theorem flaggedReceiptOracles_runs (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (state : TsigState C × Bool) (receipts : List (Round2Receipt C)) (s : HashCache C × ℕ)
    (hstored : StoredTreeRuns prims x top s.1 state.1)
    (hinit : ∀ receipt ∈ receipts, ReceiptRuns prims x top s.1 receipt) :
    ∀ r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (flaggedReceiptOracles x (receiptDealt x top)) source).run (state, receipts))).run s),
      ∀ receipt ∈ r.1.2.2, ReceiptRuns prims x top r.2.1 receipt := by
  intro r hr
  have hboth : StoredTreeRuns prims x top r.2.1 r.1.2.1.1 ∧
      ∀ receipt ∈ r.1.2.2, ReceiptRuns prims x top r.2.1 receipt := by
    apply counted_simulateQ_inv prims (flaggedReceiptOracles x (receiptDealt x top))
      (fun state cache => StoredTreeRuns prims x top cache state.1.1 ∧
        ∀ receipt ∈ state.2, ReceiptRuns prims x top cache receipt) _ source _ s
      ⟨hstored, hinit⟩ r hr
    intro input state cache hstate result hr
    simp only [flaggedReceiptOracles, StateT.run_mk, simulateQ_map, StateT.run_map,
      support_map, Set.mem_image] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    constructor
    · exact signingWithReceipt_storedTreeRuns prims x top state.1.1 input cache hstate.1 out hout
    · intro receipt hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact ReceiptRuns.mono prims x top
          (SigningCacheProof.countRun_grows prims _ cache out hout) receipt (hstate.2 receipt hold)
      · apply signingWithReceipt_runs prims x top state.1.1 input cache out hout hstate.1 receipt
        simpa only [Option.mem_toList, Option.mem_def] using hnew
  exact hboth.2

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
    split at hr <;> (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
  | tree b =>
    simp only [tsigOracles, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
    obtain ⟨hcorrupt, _, _⟩ := bottomOnce_frame dealt b st _ ht
    cases tree with
    | none => simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all
    | some tree =>
      simp [StateT.run_bind, bind_map_left] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hcorrupt ▸ hs
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
    · simp only [StateT.run_bind, StateT.run_set, pure_bind] at hr
      erw [StateT.run_map] at hr
      simp only [run_liftM_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨value, _, rfl⟩ := hr
      exact hs
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split at hr
    · (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
    · simp only [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨⟨tree, st'⟩, ht, hr⟩ := hr
      obtain ⟨hcorrupt, _, _⟩ := bottomOnce_frame dealt (treeOf e) st _ ht
      cases tree with
      | none => (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)
      | some tree =>
        simp only [StateT.run_bind, run_liftM_comp, bind_map_left, mem_support_bind_iff] at hr
        obtain ⟨own, _, values, _, hr⟩ := hr
        cases values <;> (simp at hr; erw [StateT.run_pure] at hr; simp at hr; subst hr; simp_all)

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

theorem hom_dealtWith_bottom {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (hom : m →ᵐ n)
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α)
    (P : HashSig.PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → m HashSig.Digest) (b : Fin (2 ^ LeanXmss.layerHeight)) :
    hom ((dealtWith lift P keys top value).bottom b) =
      (dealtWith (fun oa => hom (lift oa)) P keys top (fun point => hom (value point))).bottom b := by
  simp only [dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]

def receiptBottomResult : Option TreeOutput → Option BottomTree
  | some (.bottom tree) => some tree
  | _ => none

theorem dealtWith_bottom_result {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α)
    (P : HashSig.PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → m HashSig.Digest) (b : Fin (2 ^ LeanXmss.layerHeight)) :
    (dealtWith lift P keys top value).bottom b =
      receiptBottomResult <$> referenceTree (fun oa => lift (tweakable oa)) value P top (.bottom b) := rfl

set_option maxRecDepth 100000 in
theorem receiptDealt_bottom_replay (prims : Primitives) (h : Query C → HashSig.HashOutput)
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

end ReceiptCache

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
    (message : HashSig.Message) (candidate : HashSig.Digest)
    (selected : HashSig.Randomizer × LeanXmss.Encoding)
    (sCode : HashCache C × ℕ)
    (rCode : Option (HashSig.Randomizer × LeanXmss.Encoding) × HashCache C × ℕ)
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
      (grind x.1 LeanXmss.bottomLayer receipt.key (HashSig.littleEndianBytes 32 receipt.message)
        (HashSig.truncateHash (SigningCacheProof.answersOf r.2.1
          (.hash (randomizerInput x.1 LeanXmss.bottomLayer receipt.key receipt.candidate
            (HashSig.littleEndianBytes 32 receipt.message))))) LeanXmss.randomizerAttemptLimit 0) =
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
  have hcmt : receipt.commitment = HashSig.truncateHash
      (SigningCacheProof.answersOf r.2.1 (.hash (commitmentInput x.1 receipt.key receipt.candidate))) := by
    rw [hcommit, htree, hc]
  rw [D_signCodeword (prims := prims) (h := SigningCacheProof.answersOf r.2.1)
    _ _ _ _ _ hcmt] at hcode
  exact hcode

theorem E_messageDigest_cache {C : Committee} (prims : Primitives) (cache : HashCache C)
    (P : HashSig.PublicParameter) (e : LeanXmss.KeyIndex) (message : HashSig.Message)
    (randomness : HashSig.Randomizer) :
    E prims (SigningCacheProof.answersOf cache)
      (LeanXmss.Verification.messageDigestWithHash P LeanXmss.bottomLayer e (HashSig.littleEndianBytes 32 message) randomness) =
    XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView cache) P e (message, randomness) := by
  rw [SigningCacheProof.E_eval]
  erw [XmssSecurity.Bridge.messageDigest_bottom]
  exact XmssSecurity.Concrete.CacheReplay.eval_encodingHash (SigningDescentProof.thView cache)
    P e message randomness

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

/-! A stopped search counting both true-opening probes and output matches must
use the cap, not its expected stopping time. These formulas concern a planted
random function: the true opening and the output target are both counted. -/

section StructuralCharge

open Classical SigningHitLaneProof


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
      ∑' r, Pr{let z ← ((Query C →ₒ HashSig.HashOutput).randomOracle input).run cache}[z = r] * f r.2 ≤
        f cache + if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (ht : ¬IsProgram t) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * f r.2.1.1 ≤
      f s.1.1 + (rawDomainCost relevant t : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  classical
  simp only [loggedImpl, SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    OracleComp.tsum_prEvent_map_mul]
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change (∑' r, Pr{let z ← (fun u => (u, s.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))}[z = r] * f r.2) ≤ _
    rw [OracleComp.tsum_prEvent_map_mul]
    exact le_trans (le_of_eq (OracleComp.tsum_prEvent_mul_of_const_on_support _ fun _ _ => rfl)) le_self_add
  · change (∑' r, Pr{let z ← ((Query C →ₒ HashSig.HashOutput).randomOracle q).run s.1.1}[z = r] * f r.2) ≤ _
    simpa only [rawDomainCost, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul] using hhash q s.1.1
  · change (∑' r, Pr{let z ← (prgAnswer prims p).run s.1.1}[z = r] * f r.2) ≤ _
    have hrun : (prgAnswer prims p).run s.1.1 =
        (fun z : HashSig.HashOutput × HashCache C =>
          (prims.aes.eval (HashSig.truncateHash z.1) p.2.2, z.2)) <$>
          ((Query C →ₒ HashSig.HashOutput).randomOracle (.streamKey p.2.1)).run s.1.1 := by
      simp only [prgAnswer, hashAnswer, bind_pure_comp, StateT.run_map]
    rw [hrun, OracleComp.tsum_prEvent_map_mul]
    simpa [rawDomainCost, ite_mul] using hhash (.streamKey p.2.1) s.1.1
  · exact (ht (by trivial)).elim
  · change (∑' r, Pr{let z ← (fun u => (u, s.1.1)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))}[z = r] * f r.2) ≤ _
    rw [OracleComp.tsum_prEvent_map_mul]
    exact le_trans (le_of_eq (OracleComp.tsum_prEvent_mul_of_const_on_support _ fun _ _ => rfl)) le_self_add
  · change (∑' r, Pr{let z ← ((Query C →ₒ HashSig.HashOutput).randomOracle q).run s.1.1}[z = r] * f r.2) ≤ _
    simpa only [rawDomainCost, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul] using hhash q s.1.1
  · change (∑' r, Pr{let z ← (prgAnswer prims p).run s.1.1}[z = r] * f r.2) ≤ _
    have hrun : (prgAnswer prims p).run s.1.1 =
        (fun z : HashSig.HashOutput × HashCache C =>
          (prims.aes.eval (HashSig.truncateHash z.1) p.2.2, z.2)) <$>
          ((Query C →ₒ HashSig.HashOutput).randomOracle (.streamKey p.2.1)).run s.1.1 := by
      simp only [prgAnswer, hashAnswer, bind_pure_comp, StateT.run_map]
    rw [hrun, OracleComp.tsum_prEvent_map_mul]
    simpa [rawDomainCost, ite_mul] using hhash (.streamKey p.2.1) s.1.1

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
      (∑' r, Pr{let z ← (loggedImpl prims (.inr (.inr (.inl (SigningHitProof.topGateInput x T b))))).run s}[z = r] *
        SigningHitProof.continuationReserve prims (SigningDescentProof.finalRun A x)
          (SigningHitProof.ForestExceptionAt prims x b) r.2) ≤ (2 ^ 128 : ℝ≥0∞)⁻¹)
    (t : (WorldSpec C).Domain) (s : LoggedState C)
    (hs : SigningHitProof.RawReachable prims s) (ht : ¬IsProgram t) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * structuralHitPotential prims A x T r.2 ≤
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

theorem structuralHitPotential_terminal (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (T : C.Term)
    (z : ((Bool × Bool) × Option (TopTree × TsigState C × LeanXmss.Forgery)) × LoggedState C)
    (hz : z ∈ support (loggedRun prims A x)) (hwin : WinHit prims x (z.1, z.2.1)) :
    1 ≤ structuralHitPotential prims A x T z.2 := by
  by_cases hc : ∀ r ∈ support ((simulateQ (Query C →ₒ HashSig.HashOutput).randomOracle
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
      ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * f r.2 ≤ f s + cost t)
    (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : ¬Programmed s.2 → Inv s) :
    ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * guarded f r.2 ≤ guarded f s + cost t := by
  by_cases hb : Programmed s.2 ∨ IsProgram t
  · refine le_trans (le_of_eq (OracleComp.tsum_prEvent_mul_of_const_on_support _ (c := 0)
      (fun r hr => ?_))) zero_le
    rw [guarded, if_pos (by rw [loggedImpl_log prims t s r hr, programmed_logQuery]; exact hb)]
  · push Not at hb
    rw [guarded, if_neg hb.1]
    refine (ENNReal.tsum_le_tsum fun r => ?_).trans (hstep t s (hs hb.1) hb.1 hb.2)
    gcongr
    simp only [guarded]
    split_ifs <;> simp

/-- A refinement of the closed hit lane under its original hypotheses. The source cost is
zero on commitment calls and on encoding calls, on both oracle copies. -/
theorem hit_bound_structural_cost (prims : Primitives) (A : TsigAdversary C)
    (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (hx : x ∈ support (TprfSecurityProof.keyGen3 (C := C)))
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (hq : ∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q)
    (hsmall : q < 2 ^ 127) :
    ∃ T : C.Term, Pr{let z ← SigningDescentProof.exposedRun prims A x}[WinHit prims x z] ≤
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
  rw [SigningHitLaneProof.winHit_logged, OracleComp.prEvent_eq_tsum_ite, XmssSecurity.expectedFinal]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ support (loggedRun prims A x)
  · by_cases hw : WinHit prims x (z.1, z.2.1)
    · simp only [hw, if_true, guarded, if_neg (noProgramQuery prims C A x z hz)]
      simpa only [mul_one, loggedRun, loggedInit, f] using mul_le_mul_right
        (structuralHitPotential_terminal prims A x T z hz hw) (Pr{let y ← loggedRun prims A x}[y = z])
    · simp [hw]
  · simp [prEvent_eq_zero_of_not_mem_support _ hz]

theorem commitment_ne_modelHash (P P' : HashSig.PublicParameter) (e : LeanXmss.KeyIndex)
    (candidate : HashSig.Digest) (domain : XmssSecurity.HashDomain) (payload : HashSig.HashInput) :
    commitmentInput P' e candidate ≠ XmssSecurity.tweakableHashInput P domain payload := by
  intro h
  have heq :
      XmssSecurity.bytesLE 16 P' ++ XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 1 0 e.val) ++
        (HashSig.littleEndianBytes 16 candidate ++ HashSig.littleEndianBytes 16 0) =
      XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields domain) ++
        (payload ++ XmssSecurity.domainSuffix domain) := by
    exact h.trans (XmssSecurity.Bridge.tweakableHashInput_eq P domain payload)
  have ht := congrArg (fun fields => fields.tag.toNat) (XmssSecurity.Bridge.prefix_inj heq).2.1
  cases domain <;> norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at ht

theorem forestRelevant_not_commitment (P : HashSig.PublicParameter) (input : HashSig.HashInput)
    (hf : SigningHitProof.forestRelevant (C := C) P (.hash input)) : ¬CommitmentInput input := by
  obtain ⟨domain, payload, _, _, he, _⟩ := hf
  rintro ⟨P', e, candidate, hc⟩
  exact commitment_ne_modelHash P P' e candidate domain payload (hc.symm.trans (Query.hash.inj he))

theorem forestRelevant_not_digest (P : HashSig.PublicParameter) (input : HashSig.HashInput)
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

theorem commitment_not_digest (input : HashSig.HashInput) (hc : CommitmentInput input) :
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
    split_ifs <;> omega
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

end StructuralCharge

section SourceBottomScan

set_option backward.isDefEq.respectTransparency false

theorem encodingInput_ne_randomizerInput (parameter : HashSig.PublicParameter)
    (key e : LeanXmss.KeyIndex) (lay : LeanXmss.Layer)
    (message : HashSig.Message) (randomness rho : HashSig.Randomizer)
    (payload : HashSig.HashInput) :
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
          (HashSig.littleEndianBytes 16 rho ++ payload) := by
    simpa only [List.append_assoc, LeanXmss.addressBytes, LeanXmss.tweakFields,
      HashSig.littleEndianBytes, XmssSecurity.fieldBytes, XmssSecurity.tweakFields,
      XmssSecurity.bytesLE] using he
  have ha := (XmssSecurity.Bridge.prefix_inj heq).2.1
  have ht := congrArg (fun fields => fields.tag.toNat) ha
  norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields,
    LeanXmss.tweakFields] at ht

end SourceBottomScan


section CanonicalTopCompletion

set_option backward.isDefEq.respectTransparency false

open Classical

variable {C : Committee}

/-- A read made with a larger cache is possible with a smaller coherent cache.
This retains the answer, while the smaller run records only its own reads. -/
theorem rawQuery_support_restrict (input : Query C) (record cache : HashCache C)
    (hle : record ≤ cache) (r : HashSig.HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ HashSig.HashOutput).randomOracle input).run cache)) :
    (r.1, record.cacheQuery input r.1) ∈
      support (((Query C →ₒ HashSig.HashOutput).randomOracle input).run record) := by
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
      refine QueryCache.ext fun other => ?_
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
    (oa : OracleComp (Query C →ₒ HashSig.HashOutput) α) :
    ∀ record cache, record ≤ cache →
    ∀ z ∈ support ((simulateQ randomOracle
      (SigningHitProof.recordReads oa record)).run cache),
      (z.1.1, z.1.2) ∈ support ((simulateQ randomOracle oa).run record) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro record cache hle z hz
    rw [MonadAttach.mem_support] at hz
    change z ∈ ({((a, record), cache)} : Set _) at hz
    rcases hz with rfl
    simp
  | query_bind input k ih =>
    intro record cache hle z hz
    change z ∈ support ((simulateQ randomOracle
      (OracleComp.lift (OracleSpec.query (spec := Query C →ₒ HashSig.HashOutput) input) >>=
        fun answer => SigningHitProof.recordReads (k answer)
          (record.cacheQuery input answer))).run cache) at hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hz ⊢
    obtain ⟨r, hr, hz⟩ := hz
    refine ⟨(r.1, record.cacheQuery input r.1), rawQuery_support_restrict input record cache hle r hr, ?_⟩
    apply ih r.1 (record.cacheQuery input r.1) r.2 _ z hz
    rw [SigningHitProof.randomOracle_result_cache input cache r hr]
    exact QueryCache.cacheQuery_mono hle input r.1

theorem thView_cacheQuery_hash (cache : HashCache C) (input : HashSig.HashInput)
    (answer : HashSig.HashOutput) :
    SigningDescentProof.thView (cache.cacheQuery (.hash input) answer) =
      (SigningDescentProof.thView cache).cacheQuery input answer := by
  refine QueryCache.ext fun other => ?_
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
    change z ∈ support ((((Query C →ₒ HashSig.HashOutput).randomOracle (.hash input)).run cache >>=
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
        refine QueryCache.ext fun other => ?_
        by_cases he : other = input
        · subst other; simp [hp]
        · simp [QueryCache.cacheQuery_of_ne _ _ he]
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hp, heq]
      simp

/-- The threshold top grind uses exactly the leanVM top scan, for its genuine
PRF-derived base as well as for any other fixed base. -/
theorem grind_top_eq (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex) (root : HashSig.Digest) (base : HashSig.Randomizer) :
    ∀ attempts trial, grind parameter LeanXmss.topLayer (topKey key) (HashSig.littleEndianBytes 16 root)
      base attempts trial = (XmssSecurity.Concrete.topSignFrom parameter key root base attempts trial :
        OracleComp XmssSecurity.HashSpec _) := by
  intro attempts
  induction attempts with
  | zero => intro trial; rfl
  | succ attempts ih =>
    intro trial
    rw [grind, XmssSecurity.Concrete.topSignFrom]
    change (LeanXmss.Verification.messageDigestWithHash parameter LeanXmss.topLayer
      (XmssSecurity.Bridge.topKey key) (HashSig.littleEndianBytes 16 root)
      (base + BitVec.ofNat HashSig.digestBits trial) >>= _) = _
    rw [XmssSecurity.Bridge.messageDigest_top]
    apply congrArg (Bind.bind (XmssSecurity.Concrete.topEncodingHash parameter key root
      (base + BitVec.ofNat HashSig.digestBits trial) : OracleComp XmssSecurity.HashSpec _))
    funext digest
    rw [XmssSecurity.Bridge.decode_eq]
    cases XmssSecurity.TargetSum.decodeDigest digest with
    | none => exact ih (trial + 1)
    | some encoding => rfl

/-- A zero-bound setup cannot populate the designated raw hash domain. -/
theorem rawRun_preserves_domain {α : Type}
    (oa : OracleComp (Query C →ₒ HashSig.HashOutput) α) (relevant : Query C → Prop)
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
abbrev topDigestAddress (parameter : HashSig.PublicParameter) (key : XmssSecurity.TopIndex) :
    Query C → Prop := SigningHitProof.forestAddress parameter (.topEncoding key)

/-- Compute the actual root and base before grinding. Keeping this setup in
the same fixed oracle program permits both values to depend on earlier answers. -/
def topGrindAfter (parameter : HashSig.PublicParameter) (key : XmssSecurity.TopIndex)
    (setup : OracleComp (Query C →ₒ HashSig.HashOutput) (HashSig.Digest × HashSig.Randomizer))
    (attempts : ℕ) : OracleComp (Query C →ₒ HashSig.HashOutput)
      (HashSig.Digest × Option (HashSig.Randomizer × LeanXmss.Encoding)) := do
  let pair ← setup
  (fun selected => (pair.1, selected)) <$> SigningHitProof.forestHash
    (grind parameter LeanXmss.topLayer (topKey key) (HashSig.littleEndianBytes 16 pair.1) pair.2 attempts 0)

/-- The complete setup-and-scan record has only its selected trial decoding
at this key. The setup may be adaptive and may use other hash domains. -/
theorem topGrindAfter_record_selected (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex)
    (setup : OracleComp (Query C →ₒ HashSig.HashOutput) (HashSig.Digest × HashSig.Randomizer))
    (hp : setup.IsQueryBoundP (topDigestAddress parameter key) 0)
    (attempts : ℕ) (cache : HashCache C)
    (z : ((HashSig.Digest × Option (HashSig.Randomizer × LeanXmss.Encoding)) × HashCache C) × HashCache C)
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
theorem topGrindAfter_record_cached (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex)
    (setup : OracleComp (Query C →ₒ HashSig.HashOutput) (HashSig.Digest × HashSig.Randomizer))
    (attempts : ℕ) (cache : HashCache C)
    (z : ((HashSig.Digest × Option (HashSig.Randomizer × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle (SigningHitProof.recordReads
      (topGrindAfter parameter key setup attempts) ∅)).run cache))
    (randomness : HashSig.Randomizer) (encoding : LeanXmss.Encoding)
    (hs : z.1.1.2 = some (randomness, encoding)) :
    ∃ output, z.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key
        (z.1.1.1, randomness))) = some output ∧
      XmssSecurity.TargetSum.decodeDigest (HashSig.truncateHash output) = some encoding := by
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

theorem topRandomizer_not_topDigest (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex) (rho root : HashSig.Digest) :
    ¬XmssSecurity.AtHashAddress parameter (.topEncoding key)
      (randomizerInput parameter LeanXmss.topLayer (topKey key) rho (HashSig.littleEndianBytes 16 root)) := by
  intro h
  have he := h.1
  change (XmssSecurity.bytesLE 16 parameter ++ XmssSecurity.fieldBytes
    (XmssSecurity.tweakFields 7 0 (LeanXmss.layerHi LeanXmss.topLayer 0) (topKey key).val) ++
    (HashSig.littleEndianBytes 16 rho ++ HashSig.littleEndianBytes 16 root)).take 32 = _ at he
  have ht := congrArg (fun xs => xs.drop 16) he
  simp only [List.take_append, XmssSecurity.length_bytesLE] at ht
  simp at ht
  rw [List.take_of_length_le (by simp)] at ht
  have hf := congrArg (fun f => f.tag.toNat) (XmssSecurity.fieldBytes_injective ht)
  norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at hf


/-- The top digest tag is 12; setup and structural hashes use other tags. -/
theorem sourceTag_not_topDigest (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex) (fields : XmssSecurity.TweakFields) (payload : HashSig.HashInput)
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

theorem sourceTweak_no_topDigest (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex) (domain : LeanXmss.HashDomain) (payload : HashSig.HashInput)
    (htag : (LeanXmss.hashDomainFields domain).tag.toNat ≠ 12) :
    (LeanXmss.Verification.tweakableHashWithHash parameter domain payload : OracleComp LeanXmss.HashSpec _).IsQueryBoundP
      (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0 := by
  unfold LeanXmss.Verification.tweakableHashWithHash
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · change (OracleComp.lift (OracleSpec.query (spec := XmssSecurity.HashSpec)
      (LeanXmss.tweakableHashInput parameter domain payload))).IsQueryBoundP
        (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0
    simp only [isQueryBoundP_query_iff]
    exact fun h => (sourceTag_not_topDigest parameter key
      ⟨(LeanXmss.hashDomainFields domain).tag, (LeanXmss.hashDomainFields domain).step,
        (LeanXmss.hashDomainFields domain).hi, (LeanXmss.hashDomainFields domain).lo⟩ payload htag h).elim
  · intro _ _; simp

theorem sourceChain_no_topDigest (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex) (lay : LeanXmss.Layer) (e : LeanXmss.KeyIndex)
    (chain : LeanXmss.ChainIndex) (start steps : ℕ) (value : HashSig.Digest) :
    (LeanXmss.Verification.chainWalkWithHash parameter lay e chain start steps value : OracleComp LeanXmss.HashSpec _).IsQueryBoundP
      (XmssSecurity.AtHashAddress parameter (.topEncoding key)) 0 := by
  induction steps with
  | zero => simp [LeanXmss.Verification.chainWalkWithHash, HashSig.OverPermutation.walkChain]
  | succ steps ih =>
    rw [LeanXmss.Verification.chainWalkWithHash]
    apply isQueryBoundP_bind (n := 0) (m := 0) ih
    intro previous _
    split_ifs
    · apply sourceTweak_no_topDigest
      norm_num [LeanXmss.hashDomainFields, LeanXmss.tweakFields]
    · simp

theorem sourceMerkle_no_topDigest (parameter : HashSig.PublicParameter)
    (key : XmssSecurity.TopIndex) (lay : LeanXmss.Layer)
    (ends : LeanXmss.KeyIndex → LeanXmss.ChainIndex → HashSig.Digest) :
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
        (HashSig.littleEndianBytes 16 (values.getD 0 0) ++ HashSig.littleEndianBytes 16 0) _ h
      norm_num [XmssSecurity.tweakFields]
    | randomizer => simp

def canonicalTopKeys (key : XmssSecurity.TopIndex) :=
  (List.finRange (2 ^ LeanXmss.layerHeight)).flatMap fun k =>
    (List.finRange LeanXmss.chainCount).map fun l => (bottomKey key k, l)

def canonicalTopEnds (key : XmssSecurity.TopIndex) (outputs : List (List Bit))
    (e : LeanXmss.KeyIndex) (l : LeanXmss.ChainIndex) : HashSig.Digest :=
  digestAt (outputs.getD ((canonicalTopKeys key).idxOf (e, l)) []) 2

def canonicalTopRho (key : XmssSecurity.TopIndex) (outputs : List (List Bit)) : HashSig.Digest :=
  digestAt (outputs.getD ((canonicalTopKeys key).length + 2 ^ LeanXmss.layerHeight) []) 0

def canonicalTopAfterJobs (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex)
    (outputs : List (List Bit)) (levels : ℕ) :
    OracleComp (Query C →ₒ HashSig.HashOutput) (HashSig.Digest × HashSig.Randomizer) := do
  let root ← SigningHitProof.forestHash
    (merkleNode x.1 LeanXmss.bottomLayer (canonicalTopEnds key outputs) levels key.val)
  let base ← SigningHitProof.forestHash (HashSig.truncateHash <$> LeanXmss.Verification.oracleHashWithHash
    (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs) (HashSig.littleEndianBytes 16 root)))
  pure (root, base)

theorem canonicalTopAfterJobs_no_digest (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (outputs : List (List Bit)) (levels : ℕ) :
    (canonicalTopAfterJobs x key outputs levels).IsQueryBoundP (topDigestAddress x.1 key) 0 := by
  unfold canonicalTopAfterJobs
  refine isQueryBoundP_bind
    (oa := SigningHitProof.forestHash (merkleNode x.1 LeanXmss.bottomLayer
      (canonicalTopEnds key outputs) levels key.val))
    (ob := fun root => do
      let base ← SigningHitProof.forestHash (HashSig.truncateHash <$> LeanXmss.Verification.oracleHashWithHash
        (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs) (HashSig.littleEndianBytes 16 root)))
      pure (root, base))
    (n := 0) (m := 0) (by
      exact SigningHitProof.forestHash_bound _ _ _ 0 (sourceMerkle_no_topDigest x.1 key _ _ _ _)) ?_
  intro root _
  refine isQueryBoundP_bind
    (oa := SigningHitProof.forestHash (HashSig.truncateHash <$> LeanXmss.Verification.oracleHashWithHash
      (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs) (HashSig.littleEndianBytes 16 root))))
    (ob := fun base => pure (root, base)) (n := 0) (m := 0) (by
    apply SigningHitProof.forestHash_bound
    apply (isQueryBoundP_map_iff _ _ _).2
    change (OracleComp.lift (OracleSpec.query (spec := XmssSecurity.HashSpec)
      (randomizerInput x.1 LeanXmss.topLayer (topKey key) (canonicalTopRho key outputs)
        (HashSig.littleEndianBytes 16 root)))).IsQueryBoundP
          (XmssSecurity.AtHashAddress x.1 (.topEncoding key)) 0
    simp only [isQueryBoundP_query_iff]
    exact fun h => (topRandomizer_not_topDigest x.1 key _ root h).elim) ?_
  intro _ _; simp

/-- Exactly the ceremony of the tree, root and randomizer-base computation of the actual
bottom tree. No state-derived value is supplied as an external parameter. -/
def canonicalTopSetupForJobs (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) (jobs : List Job) (levels : ℕ) :
    OracleComp (Query C →ₒ HashSig.HashOutput) (HashSig.Digest × HashSig.Randomizer) :=
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

set_option maxRecDepth 100000 in
theorem canonicalTopSetup_no_digest (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :
    (canonicalTopSetup x key).IsQueryBoundP (topDigestAddress x.1 key) 0 :=
  canonicalTopSetupForJobs_no_digest x key (bottomJobs key) LeanXmss.layerHeight

/-- A canonical scan with the threshold root and PRF-derived base. -/
def canonicalTopGrind (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :=
  topGrindAfter x.1 key (canonicalTopSetup x key) LeanXmss.randomizerAttemptLimit

set_option maxRecDepth 100000 in
theorem canonicalTopGrind_record_selected (x : SigningSecurityProof.Keys3 C)
    (key : XmssSecurity.TopIndex) (cache : HashCache C)
    (z : ((HashSig.Digest × Option (HashSig.Randomizer × LeanXmss.Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ randomOracle
      (SigningHitProof.recordReads (canonicalTopGrind x key) ∅)).run cache))
    (input : XmssSecurity.HashInput) (encoding : XmssSecurity.Encoding)
    (hd : XmssSecurity.TopDecodesAt x.1 key (SigningDescentProof.thView z.1.2) input encoding) :
    ∃ randomness, z.1.1.2 = some (randomness, encoding) ∧
      input = XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (z.1.1.1, randomness) :=
  topGrindAfter_record_selected x.1 key (canonicalTopSetup x key)
    (canonicalTopSetup_no_digest x key) LeanXmss.randomizerAttemptLimit cache z hz input encoding hd

/-- Exact top digest inputs, so malformed hash payloads spend no digest charge. -/
def topDigestInput (parameter : HashSig.PublicParameter) (key : XmssSecurity.TopIndex)
    (input : Query C) : Prop :=
  ∃ payload, input = .hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key payload)

def topGrindTargets (parameter : HashSig.PublicParameter) (key : XmssSecurity.TopIndex)
    (result : HashSig.Digest × Option (HashSig.Randomizer × LeanXmss.Encoding))
    (record : HashCache C) : SigningHitProof.CompletionTargets C := fun input =>
  match result.2 with
  | none => (input, 0)
  | some selected =>
      let honest := Query.hash (XmssSecurity.Concrete.CacheView.topEncodingInput parameter key
        (result.1, selected.1))
      (honest, HashSig.truncateHash ((record honest).getD 0))

/-- The fixed program computes both the root and genuine PRF-derived scan base. -/
def canonicalTopCompletion (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex) :
    OracleComp (Query C →ₒ HashSig.HashOutput) (SigningHitProof.CompletionTargets C) :=
  SigningHitProof.recordedCompletion (canonicalTopGrind x key) (topGrindTargets x.1 key)

/-- A partner whose entire canonical root/base/scan computation is already
resolved by the source cache. Unopened trees need the separate gate argument. -/
def ResolvedTopPartner (x : SigningSecurityProof.Keys3 C) (key : XmssSecurity.TopIndex)
    (cache : HashCache C) : Prop :=
  ∃ root randomness encoding honestOutput payload output,
    DeterministicSigning.Resolves cache (canonicalTopGrind x key) (root, some (randomness, encoding)) ∧
    cache (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (root, randomness))) = some honestOutput ∧
    cache (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key payload)) = some output ∧
    (root, randomness) ≠ payload ∧ HashSig.truncateHash output = HashSig.truncateHash honestOutput

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
      have hdecode' : XmssSecurity.TargetSum.decodeDigest (HashSig.truncateHash output) = some encoding :=
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
    change HashSig.truncateHash output = HashSig.truncateHash
      ((r.1.2 (.hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (r.1.1.1, randomness)))).getD 0)
    rw [hroot, hhonest]
    exact heq

theorem topDigestInput_key_unique (parameter : HashSig.PublicParameter) (input : Query C)
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

def anyTopDigestInput (parameter : HashSig.PublicParameter) (input : Query C) : Prop :=
  ∃ key, topDigestInput parameter key input

local instance (parameter : HashSig.PublicParameter) (input : Query C) :
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
    ∑' r, Pr{let z ← ((Query C →ₒ HashSig.HashOutput).randomOracle input).run cache}[z = r] *
      topPartnerPotential x r.2 ≤ topPartnerPotential x cache +
        if anyTopDigestInput x.1 input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [topPartnerPotential, Finset.mul_sum]
  have hswap := ENNReal.tsum_comm (f := fun r : HashSig.HashOutput × HashCache C =>
    fun key : XmssSecurity.TopIndex => Pr{let z ← ((Query C →ₒ HashSig.HashOutput).randomOracle input).run cache}[z = r] *
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
      ∑' r, Pr{let z ← ((Query C →ₒ HashSig.HashOutput).randomOracle input).run cache}[z = r] * f r.2 ≤
        f cache + if relevant input then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) :
    Pr{let r ← SigningDescentProof.exposedRun prims A x}[event r.2.1] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * sourceExpectedCost prims A x (rawDomainCost relevant) := by
  let potential : LoggedState C → ℝ≥0∞ := fun s => f s.1.1
  let bad : LoggedState C → Prop := fun s => event s.1.1 ∧ ¬Programmed s.2
  have hbad : ∀ s, bad s → 1 ≤ guarded potential s := by
    intro s hs
    rw [guarded, if_neg hs.2]
    exact hterminal _ hs.1
  have hstep : ∀ t s, True →
      ∑' r, Pr{let z ← (loggedImpl prims t).run s}[z = r] * guarded potential r.2 ≤
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
  rw [← loggedRun_forget, prEvent_map]
  apply prEvent_mono_of_support
  intro r hr hevent
  exact ⟨hevent, noProgramQuery prims C A x r hr⟩

theorem topDigest_rawCost_le (parameter : HashSig.PublicParameter) (t : (WorldSpec C).Domain) :
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
        he]
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
        he]
      split_ifs <;> omega
    · simp [rawDomainCost, anyTopDigestInput, hd]
  · simp [rawDomainCost, anyTopDigestInput, topDigestInput]

/-- A returned bottom tree identifies the root and selected randomness of the
canonical scan. Acceptance checks after the scan do not change either value. -/
theorem resolves_referenceBottom_topGrind_some (x : SigningSecurityProof.Keys3 C)
    (cache : HashCache C) (top : TopTree) (key : XmssSecurity.TopIndex) (tree : BottomTree)
    (h : DeterministicSigning.Resolves cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom key))
      (some (.bottom tree))) :
    ∃ encoding, DeterministicSigning.Resolves cache (canonicalTopGrind x key)
      (tree.root, some (tree.topSignature.randomizer, encoding)) := by
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

set_option maxRecDepth 100000 in
theorem resolved_bottom_topSignedInput (prims : Primitives) (z : SigningDescentProof.FinalState C)
    (tree : BottomTree)
    (htop : D prims z.answers
      (referenceTree tweakable (prfValue z.keys.2.1) z.keys.1 emptyTop .top) = some (.top z.top))
    (hres : DeterministicSigning.Resolves z.cache
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue z.keys.2.1)
        z.keys.1 z.top (.bottom (treeOf z.key))) (some (.bottom tree))) :
    SigningDescentProof.topSignedInput z.cache z.keys.1 z.key (z.honestKey prims) =
      (tree.root, tree.topSignature.randomizer) := by
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
    · change ((z.bottomTree prims).map _).getD 0 = tree.topSignature.randomizer
      change (((z.dealt prims).bottom (treeOf z.key)).map _).getD 0 = _
      rw [hb]
      rfl

/-- A top partner of a successfully returned, cached bottom tree is one
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
  refine ⟨tree.root, tree.topSignature.randomizer, hcanonEncoding, honestOutput, _, output,
    hcanon, hh, ho, hn, ?_⟩
  unfold XmssSecurity.Concrete.CacheView.topEncodingHash XmssSecurity.Concrete.CacheView.digestAt at he
  erw [hh, ho] at he
  exact he.symm

def commitmentTargets (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (record : HashCache C) : SigningHitProof.CompletionTargets C :=
  fun input => match input with
  | .hash value => ((commitmentTrial P value).map fun trial =>
      (Query.hash (commitmentInput P trial.1 (cachedRandomizer seeds record trial.1)),
        commitmentOutputTarget seeds P record input)).getD (input, 0)
  | _ => (input, 0)

theorem commitmentTargets_eq (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (record : HashCache C) (input : HashSig.HashInput)
    (key : LeanXmss.KeyIndex) (candidate : HashSig.Digest)
    (ht : commitmentTrial P input = some (key, candidate)) :
    commitmentTargets seeds P record (.hash input) =
      (.hash (commitmentInput P key (cachedRandomizer seeds record key)),
        commitmentOutputTarget seeds P record (.hash input)) := by
  simp only [commitmentTargets, ht, Option.map_some, Option.getD_some]

def commitmentCompletion (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) :
    OracleComp (Query C →ₒ HashSig.HashOutput) (SigningHitProof.CompletionTargets C) :=
  SigningHitProof.recordedCompletion (rawCommitmentForest seeds P) (fun _ => commitmentTargets seeds P)

theorem alternativeCommitment_completed (seeds : C.Term → HashSig.HashOutput)
    (P : HashSig.PublicParameter) (cache : HashCache C)
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
  · simp only [RawCommitmentInput, ht, Option.isSome_some]
  · rw [commitmentTargets_eq seeds P record _ key candidate ht]
    intro heq
    exact hn ((SigningCoreProof.commitmentInput_injective P key (Query.hash.inj heq)).trans hs)
  · rw [commitmentTargets_eq seeds P record _ key candidate ht]
    rw [commitmentOutputTarget_eq seeds P record _ key candidate ht]
    exact he.trans ((congrArg (fun value : Option HashSig.HashOutput =>
      HashSig.truncateHash (value.getD 0)) hrc).trans (congrArg HashSig.truncateHash hrho)).symm

theorem commitment_rawCost_le (P : HashSig.PublicParameter) (t : (WorldSpec C).Domain) :
    rawDomainCost (RawCommitmentInput P) t ≤ commitmentCost t := by
  have hhash : ∀ input : HashSig.HashInput, RawCommitmentInput (C := C) P (.hash input) →
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
    Pr{let r ← SigningDescentProof.exposedRun prims A x}[AlternativeCommitment x.2.1 x.1 r.2.1] ≤
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
  exact h.trans (mul_le_mul_right
    (sourceExpectedCost_mono prims A x _ _ (commitment_rawCost_le x.1)) _)

/-- The first unit uses disjoint source domains. The event itself need not
be disjoint internally; the complementary winning event below is disjoint. -/
def ChargedOutput (prims : Primitives) (x : SigningSecurityProof.Keys3 C) (r : Outcome C) : Prop :=
  WinHit prims x r ∨ AlternativeCommitment x.2.1 x.1 r.2.1 ∨ ∃ key, ResolvedTopPartner x key r.2.1

end CanonicalTopCompletion

end SigningGuessProof

/-!
## The signing core uses two units for each call, and the example rules out one

`hit_bound_structural_cost`, `alternativeCommitment_bound_source` and
`SigningPartnerLinkProof.resolvedTopPartner_bound_topDigest`, with `source_output_costs_le`, bound
`ChargedOutput` by one unit `2 ^ -128` for each call. `SigningLinkPaidProof.chargedLane_bound_oneRun`
also bounds the R1 hit in the same unit. `HiddenCoreAt` has the bound `signingHashError q`.

The example below is a mathematical counterexample and not a Lean proof. It shows that one unit
does not bound the guess and partner wins together. Let `N = 2 ^ 128`, `M = 2 ^ 120`, `B = 2 ^ 90`.

* The setting is `t = 2` with one corrupt operator and distinct supported keys.
* The forger makes `M` distinct commitment trials `ρ'` against `c_e`. A second preimage of `c_e`
  also counts, so a match has a probability of at least `(3/2) * M / N`.
* With `ρ'`, the first digest trials of `B` messages give `m0 ≠ m1` with the same valid digest.
* In round 2 the corrupt share is `ρ' XOR d1`, with `d1` the honest share. So the combined value is
  `ρ'`. A matching commitment alone passes only the commitment check of `signCodeword`, and its
  grind can still fail.
* The forger outputs the signature of `m0` on `m1`. The digests are equal, so the verification
  accepts it. Only the corrupt operator signs `m1`, so the forgery is fresh.
* The top search of the bottom tree and the digest collision each succeed with a conditional
  probability of at least `7/8`. This gives `(7/8)^2 * (3/2) = 147/128`.
* The forger makes at most `q = M + 2 ^ 113` counted calls, with the honest work and the
  verification. So the guess or partner win has a probability of at least `(147/128) * M / N`,
  but `q / N` is only `(129/128) * M / N`.

The commitment collision itself is not a structural `SigningDescentProof.Hit`. On the
different-opening branch, `AlternativeCommitment` covers it.

Many keys or sessions do not multiply the targets of one input. `commitmentInput_key_eq`,
`randomizerInput_key_eq`, `randomizerInput_layer_eq` and `randomizerInput_payload_eq` fix the key,
the layer, the opening and the message of an input. `bound_message_unique` fixes the bound message.
-/

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.loggedRun_expectedCost_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.loggedRun_expectedCost_le

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_of_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.openingMatch_of_runs

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.topPartner_inputs_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.topPartner_inputs_cached

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.randomOracle_programs_commute_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.randomOracle_programs_commute_private

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessProof.rawCommitmentForest_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.rawCommitmentForest_support

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.canonical

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.ReceiptRuns.selected

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.hit_bound_structural_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.hit_bound_structural_cost

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.structural_commitment_digest_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.structural_commitment_digest_cost_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.source_output_costs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.source_output_costs_le

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.recordReads_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.recordReads_supported

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.canonicalTopGrind_record_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.canonicalTopGrind_record_selected

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

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.StoredTreeRuns.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.StoredTreeRuns.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.bottomOnce_storedTreeRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.bottomOnce_storedTreeRuns

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.round2WithReceipt_subruns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.round2WithReceipt_subruns

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.round2WithReceipt_storedTreeRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.round2WithReceipt_storedTreeRuns

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.signingWithReceipt_storedTreeRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.signingWithReceipt_storedTreeRuns

/-- info: 'ThresholdLeanXmssSecurity.SigningGuessProof.flaggedReceiptOracles_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuessProof.flaggedReceiptOracles_runs
