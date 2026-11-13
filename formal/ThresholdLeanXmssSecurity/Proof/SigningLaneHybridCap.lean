import ThresholdLeanXmssSecurity.Proof.SigningLaneUnion
import ThresholdLeanXmssSecurity.Proof.SigningLane2TraceLink
import ThresholdLeanXmssSecurity.Proof.Dealer
import Mathlib.Tactic.DeriveFintype
import XmssSecurity.Proof.ExactQueryCount

/-!
# The capped signing compiler

The source replaces hidden tree inputs by symbolic pending answers. An internal
chain edge keeps its next secret as its low half and samples only its high half.
Virtual PRF entries and materialized entries remain distinct until release; the
first remaining term supplies the threshold-XOR slack. Tree builds store symbolic
top signatures, and a successful tree request reveals their canonical suffixes.

`compilerImpl` adds the existing cached-randomizer grind, trace and stale bit to
this backend. Silent planting is restricted to non-message inputs. The total
lane-two potential is stopped when the stale bit rises.

`laneTraceCap_of_compiler` reduces the original guarded union cap to a local
non-stale potential step and a coupling to this one fixed source/backend pair.
The coupling includes adaptive PRF programming, candidate coverage and count
transport. It does not accept a separately chosen program or implementation.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningLaneHybridCapProof

open SigningOpeningProof SigningSecurityProof

deriving instance DecidableEq, Fintype for HiddenKey

instance : Inhabited HiddenKey := ⟨.opening bottomLayer ⟨0, by decide⟩⟩

instance : SampleableType HiddenKey := SampleableType.ofFintype _

/-- The message-digest domain is disjoint from every hidden-input coordinate. -/
theorem hiddenCandidate_none_of_isMsg (P : PublicParameter) (input : HashInput)
    (h : IsMsg input) : hiddenCandidate P input = none := by
  have hc : ¬∃ e ρ, input = commitmentInput P e ρ := by
    rintro ⟨e, ρ, rfl⟩
    exact not_isMsg_of_mpc (Or.inr ⟨P, e, ρ, rfl⟩) h
  have hr : ¬∃ lay e ρ message, input = randomizerInput P lay e ρ message := by
    rintro ⟨lay, e, ρ, message, rfl⟩
    exact SigningLane2BridgeProof.not_isMsg_randomizerInput _ _ _ _ _ h
  have hb : ¬∃ e l p v, input = XmssSecurity.Concrete.CacheView.chainInput P e l p v := by
    rintro ⟨e, l, p, v, rfl⟩
    rw [SigningGuessLinkProof.chainInput_eq_bridge] at h
    exact byte23_chain _ _ _ _ _ h
  have ht : ¬∃ b l p v, input = XmssSecurity.Concrete.CacheView.topChainInput P b l p v := by
    rintro ⟨b, l, p, v, rfl⟩
    rw [SigningGuessLinkProof.topChainInput_eq_bridge] at h
    exact byte23_chain _ _ _ _ _ h
  simp only [hiddenCandidate, dif_neg hc, dif_neg hr, dif_neg hb, dif_neg ht]

variable {C : Committee}

/-- The unique hidden coordinate carried by a hash call on either copy. -/
def worldCandidate (P : PublicParameter) : (WorldSpec C).Domain → Option (HiddenKey × Digest)
  | .inl (.inl (.inr (.inl (.hash input)))) => hiddenCandidate P input
  | .inr (.inr (.inl (.hash input))) => hiddenCandidate P input
  | _ => none

def InputSide (P : PublicParameter) (t : (WorldSpec C).Domain) : Prop :=
  (worldCandidate P t).isSome

theorem worldCandidate_hashCall (P : PublicParameter) (input : HashInput)
    (t : (WorldSpec C).Domain) (h : SigningFlatProof.HashCallAt input t) :
    worldCandidate P t = hiddenCandidate P input := by
  rcases h with rfl | rfl <;> rfl

/-- A message-digest call never carries an input-side candidate. -/
theorem not_inputSide_msgCall (P : PublicParameter) (t : (WorldSpec C).Domain)
    (h : SigningLane2FlatProof.MsgCall t) : ¬InputSide P t := by
  obtain ⟨input, hi, h | ⟨u, rfl⟩⟩ := h
  · simp only [InputSide, worldCandidate_hashCall P input t h,
      hiddenCandidate_none_of_isMsg P input hi, Option.isSome_none, Bool.false_eq_true,
      not_false_eq_true]
  · simp [InputSide, worldCandidate]

/-- The calls that the signing world counts, namely each call of `H` and of `PRG` and each
programming query, on both copies. -/
def SigningCounted : (WorldSpec C).Domain → Prop
  | .inl (.inl (.inl _)) => False
  | .inr (.inl _) => False
  | _ => True

theorem inputSide_counted (P : PublicParameter) (t : (WorldSpec C).Domain)
    (h : InputSide P t) : SigningCounted t := by
  rcases t with ((n | q | y) | p) | (n | q | y)
  all_goals trivial

attribute [local instance] Classical.propDecidable

/-- A digest expression contains a public value or one unrevealed coordinate. -/
inductive DeferredDigest
  | known (value : Digest)
  | secret (key : HiddenKey)
deriving DecidableEq

/-- A pending answer has fresh high bits and a symbolic low half. -/
structure DeferredOutput where
  high : Digest
  low : DeferredDigest

/-- The hash points used inside the clear tree evaluator. -/
inductive PendingInput
  | commitment (e : KeyIndex)
  | base (lay : Layer) (e : KeyIndex) (message : HashInput)
  | bottom (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex)
      (p : XmssSecurity.ChainStep)
  | top (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex)
      (p : XmssSecurity.ChainStep)
deriving DecidableEq

def PendingInput.key : PendingInput → HiddenKey
  | .commitment e => .opening bottomLayer e
  | .base lay e _ => .opening lay e
  | .bottom e l p => .bottomChain e l p
  | .top b l p => .topChain b l p

/-- Only the low halves of the two internal edges are further secrets. -/
def PendingInput.next : PendingInput → Option HiddenKey
  | .bottom e l p => if h : p.val + 1 < 3 then
      some (.bottomChain e l ⟨p.val + 1, h⟩) else none
  | .top b l p => if h : p.val + 1 < 3 then
      some (.topChain b l ⟨p.val + 1, h⟩) else none
  | _ => none

def PendingInput.input (P : PublicParameter) (p : PendingInput) (value : Digest) : HashInput :=
  match p with
  | .commitment e => commitmentInput P e value
  | .base lay e message => randomizerInput P lay e value message
  | .bottom e l step => XmssSecurity.Concrete.CacheView.chainInput P e l step value
  | .top b l step => XmssSecurity.Concrete.CacheView.topChainInput P b l step value

/-- Interpreting an expression is used in relations, never by the backend. -/
def DeferredDigest.interpret (s : HiddenKey → Digest) : DeferredDigest → Digest
  | .known value => value
  | .secret k => s k

def DeferredOutput.interpret (s : HiddenKey → Digest) (value : DeferredOutput) : HashOutput :=
  XmssSecurity.Rom.hashOutputEquivDigestPair.symm (value.high, value.low.interpret s)

/-- The backend table is independent of the hidden coordinates. Virtual PRF calls retain
both their point and their term, even though they have no concrete answer yet. -/
structure DeferredState (C : Committee) where
  cache : HashCache C
  pending : PendingInput → Option DeferredOutput
  virtual : Finset (C.Term × Point)
  pads : Point → Option Digest

/-- Silent planting has no message-digest constructor. In particular it cannot
increase the lane-two cache potential without a counted hash query. -/
inductive PlantInput
  | prf (seed : HashOutput) (p : Point)
  | pending (P : PublicParameter) (p : PendingInput) (input : Digest)

def PlantInput.query : PlantInput → Query C
  | .prf seed p => .prf seed p
  | .pending P p input => .hash (p.input P input)

/-- Every pending-input constructor is outside the message-digest domain. -/
theorem PendingInput.not_isMsg (P : PublicParameter) (p : PendingInput) (value : Digest) :
    ¬IsMsg (p.input P value) := by
  cases p with
  | commitment e => exact not_isMsg_of_mpc (Or.inr ⟨P, e, value, rfl⟩)
  | base lay e message => exact SigningLane2BridgeProof.not_isMsg_randomizerInput _ _ _ _ _
  | bottom e l step =>
      simp only [PendingInput.input, SigningGuessLinkProof.chainInput_eq_bridge]
      exact byte23_chain _ _ _ _ _
  | top b l step =>
      simp only [PendingInput.input, SigningGuessLinkProof.topChainInput_eq_bridge]
      exact byte23_chain _ _ _ _ _

/-- Each `hash`, `pending` and `virtual` is one actual hash/PRF call. The other
constructors are compiler bookkeeping and consume no hash budget. -/
inductive DeferredQuery (C : Committee)
  | hash (q : Query C)
  | pending (p : PendingInput)
  | virtual (T : C.Term) (p : Point)
  | pad (p : Point)
  | inspect (p : PendingInput)
  | plant (q : PlantInput) (value : HashOutput)
  | snapshot
  | sample
  | record (p : PendingInput) (value : HashOutput)
  | uniform (n : ℕ)
  | bindKey (e : KeyIndex) (message : Message)

def DeferredSpec (C : Committee) : OracleSpec (DeferredQuery C)
  | .hash _ => HashOutput
  | .pending _ => DeferredOutput
  | .virtual .. => Unit
  | .pad _ => Digest
  | .inspect _ => Option DeferredOutput
  | .plant .. => Bool
  | .snapshot => DeferredState C
  | .sample => HashOutput
  | .record .. => Unit
  | .uniform n => Fin (n + 1)
  | .bindKey .. => Unit

def deferredCounted : DeferredQuery C → Prop
  | .hash _ | .pending _ | .virtual .. => True
  | _ => False

def deferredCandidate (P : PublicParameter) : DeferredQuery C → Option (HiddenKey × Digest)
  | .hash (.hash input) => hiddenCandidate P input
  | _ => none

def deferredInputSide (P : PublicParameter) (q : DeferredQuery C) : Prop :=
  (deferredCandidate P q).isSome

def deferredKey (P : PublicParameter) (q : DeferredQuery C) : HiddenKey :=
  ((deferredCandidate P q).getD (default, 0)).1

def deferredPoint (P : PublicParameter) (q : DeferredQuery C) : Digest :=
  ((deferredCandidate P q).getD (default, 0)).2

/-- Sampling a pending answer never reads the coordinate in its low half. -/
def samplePending (p : PendingInput) : ProbComp DeferredOutput := do
  let halves ← XmssSecurity.Rom.hashOutputEquivDigestPair <$> ($ᵗ HashOutput)
  pure ⟨halves.1, match p.next with
    | some k => .secret k
    | none => .known halves.2⟩

/-- A caching backend with no access to the secret table. Planting is conservative:
a conflicting already-cached value is reported, never overwritten. -/
def deferredImpl : QueryImpl (DeferredSpec C) (StateT (DeferredState C) ProbComp)
  | .hash q => fun st => (fun r => (r.1, { st with cache := r.2 })) <$>
      (((Query C →ₒ HashOutput).randomOracle q).run st.cache)
  | .pending p => fun st => match st.pending p with
      | some value => pure (value, st)
      | none => (fun value => (value, { st with pending := Function.update st.pending p (some value) })) <$> samplePending p
  | .virtual T p => fun st => pure ((), { st with virtual := insert (T, p) st.virtual })
  | .pad p => fun st => match st.pads p with
      | some value => pure (value, st)
      | none => (fun value => (value, { st with pads := Function.update st.pads p (some value) })) <$> ($ᵗ Digest)
  | .inspect p => fun st => pure (st.pending p, st)
  | .plant q value => fun st => match st.cache q.query with
      | some prior => pure (decide (prior = value), st)
      | none => pure (true, { st with cache := st.cache.cacheQuery q.query value })
  | .snapshot => fun st => pure (st, st)
  | .sample => fun st => (fun v => (v, st)) <$> ($ᵗ HashOutput)
  | .record p value => fun st =>
      let halves := XmssSecurity.Rom.hashOutputEquivDigestPair value
      let answer : DeferredOutput := ⟨halves.1, match p.next with
        | some k => .secret k
        | none => .known halves.2⟩
      pure ((), { st with pending := Function.update st.pending p (some answer) })
  | .uniform n => fun st => (fun v => (v, st)) <$>
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))
  | .bindKey .. => fun st => pure ((), st)

def deferredInit : DeferredState C := ⟨∅, fun _ => none, ∅, fun _ => none⟩

/-- Every pending edge points to precisely its next hidden chain coordinate. -/
def PendingValid (st : DeferredState C) : Prop :=
  ∀ p value, st.pending p = some value →
    (∃ k, p.next = some k ∧ value.low = .secret k) ∨
    (p.next = none ∧ ∃ d, value.low = .known d)

theorem samplePending_valid (p : PendingInput) (v : DeferredOutput)
    (hv : v ∈ support (samplePending p)) :
    (∃ k, p.next = some k ∧ v.low = .secret k) ∨
    (p.next = none ∧ ∃ d, v.low = .known d) := by
  simp only [samplePending, mem_support_bind_iff, mem_support_pure_iff] at hv
  obtain ⟨a, _, rfl⟩ := hv
  cases h : p.next with
  | none => exact Or.inr ⟨rfl, _, rfl⟩
  | some k => exact Or.inl ⟨k, rfl, rfl⟩

theorem pendingValid_init : PendingValid (deferredInit (C := C)) := by
  intro p v hv
  simp [deferredInit] at hv

/-- The symbolic-next invariant is preserved by every concrete backend query. -/
theorem pendingValid_step (q : DeferredQuery C) (st : DeferredState C)
    (hst : PendingValid st) (r : DeferredSpec C q × DeferredState C)
    (hr : r ∈ support ((deferredImpl q).run st)) : PendingValid r.2 := by
  cases q with
  | hash q =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact hst
  | pending p =>
      cases hp : st.pending p with
      | some v =>
          simp [deferredImpl, StateT.run, hp] at hr
          subst r
          exact hst
      | none =>
          simp only [deferredImpl, StateT.run, hp, support_map] at hr
          obtain ⟨a, ha, rfl⟩ := hr
          intro w v hv
          by_cases hwp : w = p
          · subst w
            simp only [Function.update_self, Option.some.injEq] at hv
            subst v
            exact samplePending_valid p a ha
          · simp only [Function.update_of_ne hwp] at hv
            exact hst w v hv
  | virtual T p =>
      simp [deferredImpl, StateT.run] at hr
      subst r
      exact hst
  | pad p =>
      cases hp : st.pads p with
      | some v =>
          simp [deferredImpl, StateT.run, hp] at hr
          subst r
          exact hst
      | none =>
          simp only [deferredImpl, StateT.run, hp, support_map] at hr
          obtain ⟨a, _, rfl⟩ := hr
          exact hst
  | inspect p =>
      simp [deferredImpl, StateT.run] at hr
      subst r
      exact hst
  | plant q v =>
      cases hp : st.cache q.query <;> simp [deferredImpl, StateT.run, hp] at hr <;>
        subst r <;> exact hst
  | snapshot =>
      simp [deferredImpl, StateT.run] at hr
      subst r
      exact hst
  | sample =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact hst
  | record p value =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      intro w v hv
      by_cases hwp : w = p
      · subst w
        simp only [Function.update_self, Option.some.injEq] at hv
        subst v
        cases h : p.next with
        | none => exact Or.inr ⟨rfl, _, rfl⟩
        | some k => exact Or.inl ⟨k, rfl, rfl⟩
      · simp only [Function.update_of_ne hwp] at hv
        exact hst w v hv
  | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact hst
  | bindKey e message =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hst

/-- The semantic low half of an internal edge is its next coordinate, regardless of
which high bits the pending call sampled. -/
theorem pending_truncate_next (st : DeferredState C) (hst : PendingValid st)
    (p : PendingInput) (v : DeferredOutput) (hv : st.pending p = some v)
    (k : HiddenKey) (hk : p.next = some k) (s : HiddenKey → Digest) :
    truncateHash (v.interpret s) = s k := by
  obtain ⟨k', hk', hv'⟩ | ⟨hk', _⟩ := hst p v hv
  · have heq : k' = k := Option.some.inj (hk'.symm.trans hk)
    subst k'
    change (XmssSecurity.Rom.hashOutputEquivDigestPair (v.interpret s)).2 = _
    simp [DeferredOutput.interpret, hv', DeferredDigest.interpret]
  · rw [hk] at hk'
    contradiction

/-- A cached pending call still spends one counted call. -/
theorem pending_cached_count (p : PendingInput) (st : DeferredState C)
    (v : DeferredOutput) (hv : st.pending p = some v) (n : ℕ) :
    ((countImpl deferredImpl deferredCounted (.pending p)).run (st, n)) =
      pure (v, st, n + 1) := by
  simp [countImpl, deferredImpl, StateT.run, StateT.mk, hv, deferredCounted]
  rfl

/-- Two reads of the same edge reuse the entire symbolic answer. -/
theorem pending_repeat (p : PendingInput) (st : DeferredState C)
    (v : DeferredOutput) (st' : DeferredState C)
    (hv : (v, st') ∈ support ((deferredImpl (.pending p)).run st)) :
    (deferredImpl (.pending p)).run st' = pure (v, st') := by
  cases h : st.pending p with
  | some a =>
      simp [deferredImpl, StateT.run, h] at hv
      obtain ⟨rfl, rfl⟩ := hv
      simp [deferredImpl, StateT.run, h]
      rfl
  | none =>
      simp only [deferredImpl, StateT.run, h, support_map] at hv
      obtain ⟨a, _, hpair⟩ := hv
      cases hpair
      simp [deferredImpl, StateT.run]
      rfl

def deferredQuery (q : DeferredQuery C) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) (DeferredSpec C q) :=
  query (spec := DeferredSpec C + RevealSpec HiddenKey Digest) (.inl q)

def revealQuery (k : HiddenKey) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) Digest :=
  query (spec := DeferredSpec C + RevealSpec HiddenKey Digest) (.inr k)

/-- The compiler obtains every secret value through `RevealSpec`. -/
def revealDigest : DeferredDigest → OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) Digest
  | .known value => pure value
  | .secret k => revealQuery k

/-- Materialize one pending edge only after revealing its input and its symbolic low
half. `inspect` does not issue a second counted hash call. -/
def materializePending (P : PublicParameter) (p : PendingInput) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) Bool := do
  let some answer ← deferredQuery (.inspect p) | pure true
  let input ← revealQuery p.key
  let low ← revealDigest answer.low
  deferredQuery (.plant (.pending P p input)
    (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low)))

/-- The source-level capped kernel. Its backend cannot inspect `s`. -/
abbrev deferredCapped (P : PublicParameter) (q : ℕ) (s : HiddenKey → Digest) :=
  SigningCappedExpectProof.cappedHybrid (deferredImpl (C := C))
    (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s

/-- The symbolic-next invariant also survives the count and reveal wrappers. -/
theorem pendingValid_capped_step (P : PublicParameter) (q : ℕ) (s : HiddenKey → Digest)
    (t : (DeferredSpec C + RevealSpec HiddenKey Digest).Domain)
    (st : (DeferredState C × ℕ) × (HiddenKey → Option Digest) × Bool)
    (hst : PendingValid st.1.1)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t ×
      ((DeferredState C × ℕ) × (HiddenKey → Option Digest) × Bool))
    (hr : r ∈ support ((deferredCapped P q s t).run st)) : PendingValid r.2.1.1 := by
  cases t with
  | inl t =>
      simp only [deferredCapped, SigningCappedExpectProof.cappedHybrid, revealImpl,
        countImpl, StateT.run_mk, support_map] at hr
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
      exact pendingValid_step t st.1.1 hst b hb
  | inr k =>
      simp only [deferredCapped, SigningCappedExpectProof.cappedHybrid, revealImpl,
        StateT.run_mk, mem_support_pure_iff] at hr
      subst r
      exact hst

/-- Any source program over this fixed backend preserves symbolic chain edges,
including runs that interleave materialization with concrete hash queries. -/
theorem pendingValid_capped_run {α : Type} (P : PublicParameter) (q : ℕ)
    (s : HiddenKey → Digest) (oa : OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) α)
    (st : (DeferredState C × ℕ) × (HiddenKey → Option Digest) × Bool)
    (hst : PendingValid st.1.1) :
    ∀ r ∈ support ((simulateQ (deferredCapped P q s) oa).run st), PendingValid r.2.1.1 :=
  simulateQ_run_preservesInv (deferredCapped P q s) (fun st => PendingValid st.1.1)
    (pendingValid_capped_step P q s) oa st hst

/-- The six calls in `referenceJob.chainRow`, including both repeated prefixes. -/
def bottomRowCalls (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) : List PendingInput :=
  [.bottom e l ⟨0, by decide⟩,
   .bottom e l ⟨0, by decide⟩, .bottom e l ⟨1, by decide⟩,
   .bottom e l ⟨0, by decide⟩, .bottom e l ⟨1, by decide⟩, .bottom e l ⟨2, by decide⟩]

def bottomRowPrfCalls (C : Committee) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) : List (DeferredQuery C) :=
  [digit 0, digit 1, digit 2].flatMap fun p =>
    C.terms.map fun T => .virtual T (.chain bottomLayer e l p)

def backendQuery (q : DeferredQuery C) : OracleComp (DeferredSpec C) (DeferredSpec C q) :=
  liftM (OracleSpec.query (spec := DeferredSpec C) q)

/-- The public row stays independent of all three chain values. `cpk` values at
positions one and two are pads; their PRF targets are `pad XOR secret`. -/
def deferredBottomRow (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) :
    OracleComp (DeferredSpec C) (Digest × Digest × Digest) := do
  let _ ← (bottomRowPrfCalls C e l).mapM fun q => do
    let _ ← backendQuery q
    pure ()
  let cpk₁ ← backendQuery (.pad (.chain bottomLayer e l (digit 1)))
  let cpk₂ ← backendQuery (.pad (.chain bottomLayer e l (digit 2)))
  let outputs : List DeferredOutput ← (bottomRowCalls e l).mapM fun p => backendQuery (.pending p)
  let last : Option DeferredDigest := outputs.getLast?.map (·.low)
  pure (cpk₁, cpk₂, match last with
    | some (.known value) => value
    | _ => 0)

/-- The top-tree source uses the same three edges as `referenceJob.chainEnd`. Its
result is concrete, while the chain inputs remain symbolic. -/
def deferredTopEnd (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) :
    OracleComp (DeferredSpec C) Digest := do
  let _ ← C.terms.mapM fun T =>
    backendQuery (.virtual T (.chain topLayer (topKey b) l (digit 0)))
  let _ ← backendQuery (.pending (.top b l ⟨0, by decide⟩))
  let _ ← backendQuery (.pending (.top b l ⟨1, by decide⟩))
  let last ← backendQuery (.pending (.top b l ⟨2, by decide⟩))
  pure (match last.low with | .known value => value | .secret _ => 0)

def deferredHash {α : Type} (oa : OracleComp HashSpec α) : OracleComp (DeferredSpec C) α :=
  simulateQ (fun input => backendQuery (.hash (.hash input))) oa

/-- The complete top-tree setup, with symbolic chain inputs and ordinary Merkle
queries. The type gives setup no reveal oracle. -/
def deferredTopTree (P : PublicParameter) : OracleComp (DeferredSpec C) TopTree := do
  let indices := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange numChains).map fun l => (b, l)
  let ends ← indices.mapM fun bl => deferredTopEnd (C := C) bl.1 bl.2
  let keys := indices.map fun bl => (topKey bl.1, bl.2)
  let chainEnd := fun e l => ends.getD (keys.idxOf (e, l)) 0
  let root ← deferredHash (merkleNode P topLayer chainEnd layerHeight 0)
  pure ⟨chainEnd, root⟩

/-- The exact predicate count of a finite list of calls, by the existing leanVM
exact-count induction. -/
theorem exact_mapM {ι α β : Type} {spec : OracleSpec ι} (p : ι → Prop)
    [DecidablePred p] (xs : List α) (f : α → OracleComp spec β) (cost : α → ℕ)
    (hf : ∀ a ∈ xs, XmssSecurity.ExactPredicateQueryCount p (f a) (cost a)) :
    XmssSecurity.ExactPredicateQueryCount p (xs.mapM f) ((xs.map cost).sum) := by
  induction xs with
  | nil => exact .pure []
  | cons a xs ih =>
      simp only [List.mapM_cons, List.map_cons, List.sum_cons]
      refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
        (hf a (List.mem_cons_self ..)) _ _ fun y => ?_
      simpa only [Nat.add_zero] using
        (XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
          (ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))) _ 0
          (fun ys => XmssSecurity.ExactPredicateQueryCount.pure (y :: ys)))

/-- One backend query contributes exactly its declared cost, even if cached. -/
theorem exact_backendQuery (q : DeferredQuery C) :
    XmssSecurity.ExactPredicateQueryCount deferredCounted (backendQuery q)
      (if deferredCounted q then 1 else 0) := by
  simpa only [backendQuery, bind_pure, Nat.zero_add] using
    (XmssSecurity.ExactPredicateQueryCount.query q
      (fun y => (pure y : OracleComp (DeferredSpec C) (DeferredSpec C q))) 0
      (fun y => XmssSecurity.ExactPredicateQueryCount.pure y))

theorem exact_pending_calls (ps : List PendingInput) :
    XmssSecurity.ExactPredicateQueryCount deferredCounted
      (ps.mapM fun p => backendQuery (C := C) (.pending p)) ps.length := by
  simpa using (exact_mapM deferredCounted ps
    (fun p => backendQuery (C := C) (.pending p)) (fun _ => 1)
    (fun p _ => by simpa only [DeferredSpec, deferredCounted, if_true] using
      exact_backendQuery (C := C) (.pending p)))

/-- Prefix caching does not reduce the six calls performed by the bottom row. -/
theorem exact_bottomRow_pending (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) :
    XmssSecurity.ExactPredicateQueryCount deferredCounted
      ((bottomRowCalls e l).mapM fun p => backendQuery (C := C) (.pending p)) 6 := by
  exact exact_pending_calls (bottomRowCalls e l)

/-- The row compiler pays once per PRF term at each of its three input points. -/
theorem exact_bottomRow_prf (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) :
    XmssSecurity.ExactPredicateQueryCount deferredCounted
      ((bottomRowPrfCalls C e l).mapM fun q => do
        let _ ← backendQuery q
        pure ()) (3 * C.terms.length) := by
  have hquery : ∀ q ∈ bottomRowPrfCalls C e l,
      XmssSecurity.ExactPredicateQueryCount deferredCounted
        (do let _ ← backendQuery q; pure ()) 1 := by
    intro q hq
    have hc : deferredCounted q := by
      simp only [bottomRowPrfCalls, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨p, _, T, _, rfl⟩ := hq
      trivial
    simpa only [hc, if_true, Nat.add_zero] using
      (XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
        (exact_backendQuery q) (fun _ => pure ()) 0
        (fun _ => XmssSecurity.ExactPredicateQueryCount.pure ()))
  have h := exact_mapM deferredCounted (bottomRowPrfCalls C e l)
    (fun q => do let _ ← backendQuery q; pure ()) (fun _ => 1) hquery
  have hn : (List.map (fun _ => 1) (bottomRowPrfCalls C e l)).sum = 3 * C.terms.length := by
    simp [bottomRowPrfCalls]
    omega
  rw [hn] at h
  exact h

/-- The compiler retains the full source cost, including all cached repeated edges. -/
theorem exact_deferredBottomRow (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) :
    XmssSecurity.ExactPredicateQueryCount deferredCounted
      (deferredBottomRow (C := C) e l) (3 * C.terms.length + 6) := by
  unfold deferredBottomRow
  refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
    (exact_bottomRow_prf e l) _ 6 fun _ => ?_
  have hp (p : Point) : XmssSecurity.ExactPredicateQueryCount deferredCounted
      (backendQuery (C := C) (.pad p)) 0 := by
    simpa only [deferredCounted, if_false] using exact_backendQuery (C := C) (.pad p)
  refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind (hp _) _ 6 fun _ => ?_
  refine XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind (hp _) _ 6 fun _ => ?_
  simpa only [Nat.add_zero] using
    (XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
      (exact_bottomRow_pending (C := C) e l) _ 0
      (fun _ => XmssSecurity.ExactPredicateQueryCount.pure _))

set_option backward.isDefEq.respectTransparency false in
/-- The three ordinary chain walks underlying one symbolic bottom row. -/
theorem bottom_walks_of_edges (P : PublicParameter) (H : HashInput → HashOutput)
    (e : KeyIndex) (l : ChainIndex)
    (s₀ s₁ s₂ endpoint : Digest)
    (h₀ : truncateHash (H (PendingInput.input P (.bottom e l ⟨0, by decide⟩) s₀)) = s₁)
    (h₁ : truncateHash (H (PendingInput.input P (.bottom e l ⟨1, by decide⟩) s₁)) = s₂)
    (h₂ : truncateHash (H (PendingInput.input P (.bottom e l ⟨2, by decide⟩) s₂)) = endpoint) :
    evalTh H (Concrete.chainWalk P bottomLayer e l 0 1 s₀) = s₁ ∧
    evalTh H (Concrete.chainWalk P bottomLayer e l 0 2 s₀) = s₂ ∧
    evalTh H (Concrete.chainWalk P bottomLayer e l 0 3 s₀) = endpoint := by
  letI : NeZero (chainLength - 1) := ⟨by decide⟩
  let step : Fin (chainLength - 1) → Digest → Digest := fun p value =>
    truncateHash (H (tweakableHashInput P (.chain bottomLayer e p) (Concrete.chainPayload l value)))
  have he₀ : step 0 s₀ = s₁ := by
    simpa [step, PendingInput.input, SigningGuessLinkProof.chainInput_eq_bridge,
      chainLength, winternitzBits] using h₀
  have he₁ : step 1 s₁ = s₂ := by
    simpa [step, PendingInput.input, SigningGuessLinkProof.chainInput_eq_bridge,
      chainLength, winternitzBits] using h₁
  have he₂ : step 2 s₂ = endpoint := by
    simp only [PendingInput.input, SigningGuessLinkProof.chainInput_eq_bridge] at h₂
    change truncateHash (H (tweakableHashInput P (.chain bottomLayer e ⟨2, by decide⟩)
      (Concrete.chainPayload l s₂))) = endpoint
    exact h₂
  change step 0 s₀ = s₁ ∧ step 1 (step 0 s₀) = s₂ ∧
    step 2 (step 1 (step 0 s₀)) = endpoint
  rw [he₀, he₁, he₂]
  exact ⟨rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The real `referenceJob` row evaluates to the public pads and endpoint when the
PRF targets are the corresponding masked symbolic chain values. -/
theorem referenceJob_row_of_walks (P : PublicParameter) (H : HashInput → HashOutput)
    (F : Point → Digest) (e : KeyIndex) (l : ChainIndex)
    (s₀ s₁ s₂ cpk₁ cpk₂ endpoint : Digest)
    (hF₀ : F (.chain bottomLayer e l (digit 0)) = s₀)
    (hF₁ : F (.chain bottomLayer e l (digit 1)) = s₁ ^^^ cpk₁)
    (hF₂ : F (.chain bottomLayer e l (digit 2)) = s₂ ^^^ cpk₂)
    (hwalk : evalTh H (Concrete.chainWalk P bottomLayer e l 0 1 s₀) = s₁ ∧
      evalTh H (Concrete.chainWalk P bottomLayer e l 0 2 s₀) = s₂ ∧
      evalTh H (Concrete.chainWalk P bottomLayer e l 0 3 s₀) = endpoint) :
    referenceJob (m := Id) (fun oa => evalTh H oa) F P
      ⟨.chainRow e l, [.chain bottomLayer e l (digit 0),
        .chain bottomLayer e l (digit 1), .chain bottomLayer e l (digit 2)]⟩ =
      bitsOfDigest cpk₁ ++ bitsOfDigest cpk₂ ++ bitsOfDigest endpoint := by
  rw [referenceJob_id]
  simp [refCore, hF₀, hF₁, hF₂, hwalk.1, hwalk.2.1, hwalk.2.2,
    ← BitVec.xor_assoc]
  change bitsOfDigest (s₁ ^^^ s₁ ^^^ cpk₁) ++
    (bitsOfDigest (s₂ ^^^ s₂ ^^^ cpk₂) ++ bitsOfDigest endpoint) = _
  simp

open scoped BigOperators

/-- The XOR of the concrete truncated term entries. -/
def termSum (f : C.Term → Digest) : Digest :=
  (∑ T, TprfCorrectnessProof.toXor (f T) : TprfCorrectnessProof.XorDigest)

def otherTermSum (f : C.Term → Digest) (slack : C.Term) : Digest :=
  (∑ T ∈ Finset.univ.erase slack, TprfCorrectnessProof.toXor (f T) :
    TprfCorrectnessProof.XorDigest)

/-- Programming one term to `target XOR others` fixes the aggregate exactly. -/
theorem termSum_program (f : C.Term → Digest) (slack : C.Term) (target : Digest) :
    termSum (Function.update f slack (target ^^^ otherTermSum f slack)) = target := by
  change (∑ T, TprfCorrectnessProof.toXor
    (Function.update f slack (target ^^^ otherTermSum f slack) T)) =
      TprfCorrectnessProof.toXor target
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ slack)]
  rw [Function.update_self, TprfSecurityProof.toXor_xor]
  have ho : (∑ T ∈ Finset.univ.erase slack,
      TprfCorrectnessProof.toXor (Function.update f slack
        (target ^^^ otherTermSum f slack) T)) =
      TprfCorrectnessProof.toXor (otherTermSum f slack) := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [Function.update_of_ne (Finset.mem_erase.mp hT).1]
  rw [ho, add_left_comm, TprfSecurityProof.XorDigest.add_self, add_zero]

/-- The first remaining term is chosen at the current cache, after all previous
honest answers and adaptive corruptions have already fixed their entries. -/
def firstUnmaterialized (seeds : C.Term → HashOutput) (st : DeferredState C) (p : Point) :
    Option C.Term :=
  C.terms.find? fun T => (st.cache (.prf (seeds T) p)).isNone

def cachedTerm (seeds : C.Term → HashOutput) (st : DeferredState C) (p : Point)
    (T : C.Term) : Digest :=
  truncateHash ((st.cache (.prf (seeds T) p)).getD 0)

/-- Silent presampling fills one term; the corresponding actual call is still
issued and counted when the source evaluates it. -/
def fillTerm (seeds : C.Term → HashOutput) (p : Point) (T : C.Term) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) Unit := do
  let st ← deferredQuery .snapshot
  if (st.cache (.prf (seeds T) p)).isNone then
    let value ← deferredQuery .sample
    let _ ← deferredQuery (.plant (.prf (seeds T) p) value)
    pure ()
  else pure ()

/-- Complete a threshold PRF point with one adaptive slack term. The target is
an already-revealed digest supplied by the caller. All high halves are sampled. -/
def completePrf (seeds : C.Term → HashOutput) (p : Point) (target : Digest) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) Bool := do
  let st ← deferredQuery .snapshot
  match firstUnmaterialized seeds st p with
  | none => pure (decide (termSum (cachedTerm seeds st p) = target))
  | some slack =>
      let _ ← (C.terms.filter (· ≠ slack)).mapM (fillTerm seeds p)
      let st' ← deferredQuery .snapshot
      let high ← deferredQuery .sample
      let low := target ^^^ otherTermSum (cachedTerm seeds st' p) slack
      deferredQuery (.plant (.prf (seeds slack) p)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (truncateHash high, low)))

/-- Release the bottom opening and establish its threshold PRF constraint. -/
def releaseBottomOpening (seeds : C.Term → HashOutput) (e : KeyIndex) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) Bool := do
  let value ← revealQuery (.opening bottomLayer e)
  completePrf seeds (.randomizer bottomLayer e) value

/-- Backend readiness uses both actual and virtual PRF entries. It does not confuse
an earlier tree evaluation with the materialization of an honest answer. -/
def OpeningReady (seeds : C.Term → HashOutput) (st : DeferredState C)
    (signing : TsigState C) (e : KeyIndex) : Prop :=
  signing.bound e ≠ none ∧ ∀ T : C.Term,
    (T, Point.randomizer bottomLayer e) ∈ st.virtual ∨
      (st.cache (.prf (seeds T) (.randomizer bottomLayer e))).isSome

/-- A stored top signature keeps its chain values symbolic until a successful tree
request returns them. It can coexist with a cached bottom tree used by round two. -/
structure DeferredTopSignature where
  randomness : Randomness
  encoding : Encoding
  chainValue : ChainIndex → DeferredDigest
  path : Fin layerHeight → Digest

def DeferredTopSignature.materialize (sig : DeferredTopSignature) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) LayerSignature := do
  let values ← Concrete.sequenceFin fun l => revealDigest (sig.chainValue l)
  pure ⟨sig.randomness, values, sig.path⟩

/-- The bottom tree stores its top signature without revealing its chain inputs. -/
structure DeferredBottomTree where
  cpk : KeyIndex → ChainIndex → Digest × Digest × Digest
  commitment : KeyIndex → Digest
  root : Digest
  topSignature : DeferredTopSignature

/-- The source remembers only values it obtained from `RevealSpec`, together with
which pending points it allocated. This state is separate from the backend. -/
structure SourceState (C : Committee) where
  signing : TsigState C
  revealed : HiddenKey → Option Digest
  allocated : List PendingInput
  consistent : Bool
  trees : XmssSecurity.TopIndex → Option (Option DeferredBottomTree)
  hiddenFlag : Bool
  exposed : Finset XmssSecurity.TopIndex
  candidates : List (HiddenKey × Digest)

abbrev SourceM (C : Committee) :=
  StateT (SourceState C) (OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest))

def sourceInit : SourceState C :=
  ⟨SigningCoreProof.tsigInit, fun _ => none, [], true, fun _ => none, false, ∅, []⟩

def sourceReveal (k : HiddenKey) : SourceM C Digest := do
  match (← get).revealed k with
  | some value => pure value
  | none =>
      let value ← liftM (revealQuery (C := C) k)
      modify fun (st : SourceState C) => { st with revealed := Function.update st.revealed k (some value) }
      pure value

def sourceRevealDigest : DeferredDigest → SourceM C Digest
  | .known value => pure value
  | .secret k => sourceReveal k

/-- The source plants only already-allocated points, using reveal-oracle values for
both input and low half. A cache conflict is retained in `consistent`. -/
def sourcePlant (P : PublicParameter) (p : PendingInput) : SourceM C Unit := do
  let some answer ← liftM (deferredQuery (C := C) (.inspect p)) | pure ()
  let input ← sourceReveal p.key
  let low ← sourceRevealDigest answer.low
  let ok ← liftM (deferredQuery (C := C) (.plant (.pending P p input)
    (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low))))
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }

/-- A new pending point whose input was already revealed uses the ordinary cache.
This includes a commitment built after P and previously queried by the forger. -/
def sourcePending (P : PublicParameter) (p : PendingInput) : SourceM C DeferredOutput := do
  let prior ← liftM (deferredQuery (C := C) (.inspect p))
  let known := (← get).revealed p.key
  match prior, known, p.next with
  | none, some input, none =>
      let value ← liftM (deferredQuery (C := C) (.hash (.hash (p.input P input))))
      let _ ← liftM (deferredQuery (C := C) (.record p value))
      let halves := XmssSecurity.Rom.hashOutputEquivDigestPair value
      modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
      pure ⟨halves.1, .known halves.2⟩
  | _, _, _ =>
      if prior.isNone && known.isSome && p.next.isSome then
        modify fun (st : SourceState C) => { st with consistent := false }
      let value ← liftM (deferredQuery (C := C) (.pending p))
      if prior.isNone then modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
      pure value

/-- P completes the PRF constraint and plants every already-built commitment at the
newly revealed input. -/
def sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceM C Unit := do
  if ((← get).revealed (.opening bottomLayer e)).isNone then
    let value ← sourceReveal (.opening bottomLayer e)
    let ok ← liftM (completePrf seeds (.randomizer bottomLayer e) value)
    modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
    let pending := (← get).allocated.filter (fun p => p.key = .opening bottomLayer e)
    let _ ← pending.mapM (sourcePlant P)
    pure ()

/-- Before returning a materialized PRF answer, P sees the cache that this query
will complete. The completing term can therefore still serve as slack. -/
def ReadyAfter (seeds : C.Term → HashOutput) (st : DeferredState C)
    (signing : TsigState C) (e : KeyIndex) (q : Query C) : Prop :=
  signing.bound e ≠ none ∧ ∀ T : C.Term,
    (T, Point.randomizer bottomLayer e) ∈ st.virtual ∨
      (st.cache (.prf (seeds T) (.randomizer bottomLayer e))).isSome ∨
      q = .prf (seeds T) (.randomizer bottomLayer e)

def sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : Query C) : SourceM C HashOutput := do
  match q with
  | .prf _ (.randomizer lay e) =>
      if lay = bottomLayer then
        let backend ← liftM (deferredQuery (C := C) .snapshot)
        if ReadyAfter seeds backend (← get).signing e q then sourceReleaseOpening P seeds e
  | _ => pure ()
  liftM (deferredQuery (C := C) (.hash q))

/-- A virtually cached term completes P after its one counted call. -/
def sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) : SourceM C Unit := do
  let _ ← liftM (deferredQuery (C := C) (.virtual T p))
  match p with
  | .randomizer lay e =>
      if lay = bottomLayer then
        let backend ← liftM (deferredQuery (C := C) .snapshot)
        if OpeningReady seeds backend (← get).signing e then sourceReleaseOpening P seeds e
  | _ => pure ()

/-- Interpret the fixed setup/row programs with source-owned release bookkeeping.
Hash and virtual PRF calls retain one counted backend call apiece. -/
def sourceBackend (P : PublicParameter) (seeds : C.Term → HashOutput) :
    QueryImpl (DeferredSpec C) (SourceM C)
  | .hash q => sourceHash P seeds q
  | .pending p => sourcePending P p
  | .virtual T p => sourceVirtual P seeds T p
  | q => liftM (deferredQuery q)

def sourceTopTree (P : PublicParameter) (seeds : C.Term → HashOutput) : SourceM C TopTree :=
  simulateQ (sourceBackend P seeds) (deferredTopTree P)

def sourceBottomRow (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceM C (Digest × Digest × Digest) :=
  simulateQ (sourceBackend P seeds) (deferredBottomRow e l)

/-- The commitment source follows `referenceJob`: all PRF terms, then one hash.
P may fire during the terms, and `sourcePending` then reuses the concrete cache. -/
def sourceCommitment (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceM C Digest := do
  let _ ← C.terms.mapM fun T => sourceVirtual P seeds T (.randomizer bottomLayer e)
  let value ← sourcePending P (.commitment e)
  pure (match value.low with | .known d => d | .secret _ => 0)


def sourceHashProgram {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : OracleComp HashSpec α) : SourceM C α :=
  simulateQ (sourceBackend P seeds) (deferredHash oa)

/-- The top signature job repeats the prefix walk at its chosen position and keeps
its returned chain value symbolic. -/
def sourceTopValue (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) : SourceM C DeferredDigest := do
  let _ ← C.terms.mapM fun T => sourceVirtual P seeds T (.chain topLayer (topKey b) l (digit 0))
  let values ← (List.finRange p.val).mapM fun i => sourcePending P (.top b l
    ⟨i.val, by have hi := i.isLt; have hp := p.isLt; change i.val < 3; change p.val < 4 at hp; omega⟩)
  pure ((values.getLast?.map (·.low)).getD (.secret (.topChain b l ⟨0, by decide⟩)))

/-- The verification suffix of an honestly generated symbolic top chain. -/
def sourceTopRecover (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (p : Digit) (initial : DeferredDigest) : SourceM C Digest := do
  let values ← (List.finRange (3 - p.val)).mapM fun i => sourcePending P (.top b l
    ⟨p.val + i.val, by have hi := i.isLt; change p.val + i.val < 3; omega⟩)
  let last := (values.getLast?.map (·.low)).getD initial
  match last with
  | .known value => pure value
  | .secret _ =>
      modify fun (st : SourceState C) => { st with consistent := false }
      pure 0

/-- The actual two-run bottom ceremony, with a symbolic top signature. Both its
prefix signing walk and its verification suffix retain their original hash calls. -/
def sourceBottomTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : SourceM C (Option DeferredBottomTree) := do
  let indices := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let rows ← indices.mapM fun el => sourceBottomRow P seeds el.1 el.2
  let commitments ← (List.finRange (2 ^ layerHeight)).mapM fun k =>
    sourceCommitment P seeds (bottomKey b k)
  let _ ← C.terms.mapM fun T => sourceVirtual P seeds T (.randomizer topLayer (topKey b))
  let cpk := fun e l => rows.getD (indices.idxOf (e, l)) (0, 0, 0)
  let commitment := fun (e : KeyIndex) => commitments.getD (e.val % 2 ^ layerHeight) 0
  let root ← sourceHashProgram P seeds
    (merkleNode P bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)
  let message := bytesLE 16 root
  let baseAnswer ← sourcePending P (.base topLayer (topKey b) message)
  let base := match baseAnswer.low with | .known value => value | .secret _ => 0
  let some (randomness, encoding) ← sourceHashProgram P seeds
    (grind P topLayer (topKey b) message base randomizerAttemptLimit 0) | pure none
  let values ← Concrete.sequenceFin fun l => sourceTopValue P seeds b l (encoding l)
  let path ← sourceHashProgram P seeds (merklePath P topLayer top.chainEnd (topKey b))
  let digest ← sourceHashProgram P seeds (Concrete.messageDigest P topLayer (topKey b) message randomness)
  let some checked := Codeword.decode digest | pure none
  if checked ≠ encoding then
    modify fun (st : SourceState C) => { st with consistent := false }
    pure none
  else
    let ends ← Concrete.sequenceFin fun l => sourceTopRecover P b l (encoding l) (values l)
    let leaf ← sourceHashProgram P seeds (Concrete.leafHash P topLayer (topKey b) ends)
    let topRoot ← sourceHashProgram P seeds (Concrete.treeFold P topLayer (topKey b) path layerHeight leaf)
    if topRoot ≠ top.root then pure none else
      pure (some ⟨cpk, commitment, root, ⟨randomness, encoding, values, path⟩⟩)

/-- D17 retains successful and failed symbolic bottom builds. -/
def sourceBottomOnce (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) : SourceM C (Option DeferredBottomTree) := do
  match (← get).trees b with
  | some tree => pure tree
  | none =>
      let tree ← sourceBottomTree P seeds top b
      modify fun (st : SourceState C) => { st with trees := Function.update st.trees b (some tree) }
      pure tree

/-- Q reveals only the canonical suffix and programs its already-masked PRF
points. Its caller supplies the position chosen by the successful codeword check. -/
def sourceReleaseBottomSuffix (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) (start : Digit) : SourceM C Unit := do
  let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
  let _ ← keys.mapM fun p => do
    let value ← sourceReveal (.bottomChain e l p)
    let offset ← if p.val = 0 then pure 0 else
      liftM (deferredQuery (C := C) (.pad (.chain bottomLayer e l ⟨p.val, by have hp := p.isLt; change p.val < 4; change p.val < 3 at hp; omega⟩)))
    let ok ← liftM (completePrf seeds (.chain bottomLayer e l ⟨p.val, by have hp := p.isLt; change p.val < 4; change p.val < 3 at hp; omega⟩) (value ^^^ offset))
    modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  let _ ← keys.mapM fun p => sourcePlant P (.bottom e l p)
  pure ()

/-- R is invoked only when the tree request has a successful stored result.
Opening and chain suffixes are revealed at this boundary, never during its build. -/
def sourceReturnTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (tree : DeferredBottomTree) : SourceM C (BottomTree × Digest) := do
  let opening ← sourceReveal (.opening topLayer (topKey b))
  let ok ← liftM (completePrf seeds (.randomizer topLayer (topKey b)) opening)
  modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
  let pending := (← get).allocated.filter fun p => p.key = .opening topLayer (topKey b)
  let _ ← pending.mapM (sourcePlant P)
  let values ← Concrete.sequenceFin fun l => do
    let start := tree.topSignature.encoding l
    let keys := (List.finRange 3).filter fun p => start.val ≤ p.val
    let _ ← keys.mapM fun p => sourceReveal (.topChain b l p)
    if start.val = 0 then
      let value ← sourceReveal (.topChain b l ⟨0, by decide⟩)
      let ok ← liftM (completePrf seeds (.chain topLayer (topKey b) l (digit 0)) value)
      modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }
    let _ ← keys.mapM fun p => sourcePlant P (.top b l p)
    sourceRevealDigest (tree.topSignature.chainValue l)
  pure (⟨tree.cpk, tree.commitment, tree.root,
    ⟨tree.topSignature.randomness, values, tree.topSignature.path⟩⟩, opening)

/-- A PRG call keeps its single charged stream-key lookup; private sampling is free. -/
def sourceRo (prims : Primitives) (P : PublicParameter) (seeds : C.Term → HashOutput) :
    QueryImpl (RoSpec C) (SourceM C)
  | .inl q => sourceHash P seeds q
  | .inr inp => do
      let value ← sourceHash P seeds (.streamKey inp.2.1)
      pure (prims.aes.eval (truncateHash value) inp.2.2)

def sourceRoProgram {α : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (oa : OracleComp (RoSpec C) α) : SourceM C α :=
  simulateQ (sourceRo prims P seeds) oa

def sourcePart (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) : SourceM C Digest :=
  sourceRoProgram prims x.1 x.2.1 (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J p message)

/-- The signing oracle uses the original guards and order of the two rounds.
The backend receives only a write-once message binding. -/
def sourceTsig (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (TsigSpec C) (SourceM C)
  | .corrupt i => do
      let st := (← get).signing
      if C.t - 1 < (insert i st.corrupt).card then pure none else
        modify fun (s : SourceState C) => { s with signing := { st with corrupt := insert i st.corrupt } }
        pure (some (dealtKeys x.1 x.2.1 x.2.2 i))
  | .tree b => do
      let some tree ← sourceBottomOnce x.1 x.2.1 top b | pure none
      let result ← sourceReturnTree x.1 x.2.1 b tree
      let opening ← sourceRoProgram prims x.1 x.2.1 (prfValue x.2.1 (.randomizer topLayer (topKey b)))
      pure (some (result.1, opening))
  | .round1 i J e message => do
      let st := (← get).signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ breaksOneMessagePerKey st e message then pure none else
        modify fun (s : SourceState C) => { s with signing :=
          { st with bound := Function.update st.bound e (some message) } }
        let _ ← liftM (deferredQuery (C := C) (.bindKey e message))
        let backend ← liftM (deferredQuery (C := C) .snapshot)
        if OpeningReady x.2.1 backend (← get).signing e then sourceReleaseOpening x.1 x.2.1 e
        some <$> sourcePart prims x i J (.randomizer bottomLayer e) message
  | .round2 i J e message parts => do
      let st := (← get).signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else
        let some tree ← sourceBottomOnce x.1 x.2.1 top (treeOf e) | pure none
        let own ← sourcePart prims x i J (.randomizer bottomLayer e) message
        let parts := Function.update parts i own
        let some values ← signRound2With (fun oa => sourceRoProgram prims x.1 x.2.1 oa)
            (fun p => do
              match p with
              | .chain _ key l pos => sourceReleaseBottomSuffix x.1 x.2.1 key l pos
              | _ => pure ()
              sourcePart prims x i J p message)
            x.1 J (tree.commitment e) e message parts | pure none
        modify fun (s : SourceState C) => { s with signing :=
          { s.signing with released := s.signing.released ++ [(e, message, i)] } }
        pure (some values)

def sourceLocal (prims : Primitives) (x : Keys3 C) : QueryImpl (LocalSpec C) (SourceM C)
  | .inl n => liftM (deferredQuery (C := C) (.uniform n))
  | .inr q => sourceRo prims x.1 x.2.1 q

/-- The original hidden-key flag and candidate log are kept at adversary calls. -/
def sourceOracles (prims : Primitives) (x : Keys3 C) (top : TopTree) :
    QueryImpl (LocalSpec C + TsigSpec C) (SourceM C)
  | .inl t => do
      let st ← get
      let value ← sourceLocal prims x t
      modify fun (s : SourceState C) => { s with hiddenFlag := st.hiddenFlag || SigningCoreProof.hiddenHit x st.signing.corrupt t, candidates := st.candidates ++ unreleasedCandidates x.1 st.signing st.exposed t }
      pure value
  | .inr q => do
      let value ← sourceTsig prims x top q
      modify fun (s : SourceState C) => { s with exposed := releasedTrees s.exposed q }
      pure value

/-- The reference signature suffix rebuilds the bottom tree as `honestSignature`
does. Its final top-chain reveals occur after its last counted query. -/
def sourceHonestSignature (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (e : KeyIndex) (message : Message) : SourceM C (Option Signature) := do
  let some tree ← sourceBottomTree x.1 x.2.1 top (treeOf e) | pure none
  sourceReleaseOpening x.1 x.2.1 e
  let opening ← sourceRoProgram prims x.1 x.2.1 (prfValue x.2.1 (.randomizer bottomLayer e))
  let some (randomness, encoding) ← sourceRoProgram prims x.1 x.2.1
    (signCodeword x.1 (tree.commitment e) e message opening) | pure none
  let values ← Concrete.sequenceFin fun l =>
    if (encoding l).val = 3 then pure (tree.cpk e l).2.2 else do
      sourceReleaseBottomSuffix x.1 x.2.1 e l (encoding l)
      let value ← sourceRoProgram prims x.1 x.2.1 (prfValue x.2.1 (.chain bottomLayer e l (encoding l)))
      pure (if (encoding l).val = 0 then value else
        (if (encoding l).val = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ value)
  let path ← sourceHashProgram x.1 x.2.1
    (merklePath x.1 bottomLayer (fun key l => (tree.cpk key l).2.2) e)
  let topValues ← Concrete.sequenceFin fun l => sourceRevealDigest (tree.topSignature.chainValue l)
  let topPart : LayerSignature := ⟨tree.topSignature.randomness, topValues, tree.topSignature.path⟩
  pure (some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, values, path⟩ else topPart⟩)

/-- The fixed setup, adversary and verification program over the capped backend. -/
def sourceGame (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    SourceM C (Bool × TopTree × Forgery) := do
  let top ← sourceTopTree x.1 x.2.1
  let forgery ← simulateQ (sourceOracles prims x top) (A ⟨top.root, x.1⟩ top)
  let st ← get
  let verifyImpl : QueryImpl HashSpec (SourceM C) := fun input => do
    let value ← sourceHash x.1 x.2.1 (.hash input)
    modify fun (s : SourceState C) => { s with candidates := s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
    pure value
  let verified ← simulateQ verifyImpl (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)
  let fresh ← if (signersAt st.signing forgery.signature.leafIndex forgery.message).card < C.t then
    pure true else do
      let honest ← sourceHonestSignature prims x top forgery.signature.leafIndex forgery.message
      pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh, top, forgery)

/-- The capped kernel carries the same cached-randomizer trace and stale bit as
`traceRun`, plus the symbolic backend. Its binding map is write-once. -/
structure CompilerBackend (C : Committee) where
  data : DeferredState C
  bound : KeyIndex → Option Message
  trace : XmssSecurity.SigningCacheTrace × Bool

def compilerInit : CompilerBackend C := ⟨deferredInit, fun _ => none, [], false⟩

def compilerSigning (st : CompilerBackend C) : TsigState C :=
  { SigningCoreProof.tsigInit with bound := st.bound }

/-- Actual hash calls use `cachedExtra`; the added grind is silent, as in the
existing split run. Pending calls retain their own one-call cost and do not grind. -/
def compilerImpl (P : PublicParameter) (seeds : C.Term → HashOutput) :
    QueryImpl (DeferredSpec C) (StateT (CompilerBackend C) ProbComp)
  | .hash q => fun st => do
      let r ← (deferredImpl (.hash q)).run st.data
      let call : (WorldSpec C).Domain := .inr (.inr (.inl q))
      let before : SigningFlatProof.FlatState C := (((st.data.cache, 0), []), compilerSigning st, false)
      let after : SigningFlatProof.FlatState C := (((r.2.cache, 0), []), compilerSigning st, false)
      let prefetched ← (simulateQ (Query C →ₒ HashOutput).randomOracle
        (SigningR1FixedProof.cachedExtra seeds P before call after)).run r.2.cache
      pure (r.1, { st with data := { r.2 with cache := prefetched.2 }, trace := SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st) call prefetched.2 st.trace })
  | .bindKey e message => fun st => pure ((), { st with bound := if st.bound e = none then Function.update st.bound e (some message) else st.bound })
  | q => fun st => (fun r => (r.1, { st with data := r.2 })) <$> (deferredImpl q).run st.data

def compilerView (st : CompilerBackend C) :
    XmssSecurity.HashSpec.QueryCache × XmssSecurity.SigningCacheTrace :=
  (SigningLane2BridgeProof.keptView IsMsg st.data.cache, st.trace.1)

/-- Reachability of the one fixed counted kernel. It closes under each supported
local step, independently of the source's choices and its reveal history. -/
inductive CompilerReachable (P : PublicParameter) (seeds : C.Term → HashOutput) :
    CompilerBackend C × ℕ → Prop
  | initial : CompilerReachable P seeds (compilerInit, 0)
  | step (t : DeferredQuery C) (st : CompilerBackend C × ℕ)
      (r : DeferredSpec C t × (CompilerBackend C × ℕ))
      (hst : CompilerReachable P seeds st)
      (hr : r ∈ support ((countImpl (compilerImpl P seeds) deferredCounted t).run st)) :
      CompilerReachable P seeds r.2

def compilerPotential (P : PublicParameter) (q : ℕ) (st : CompilerBackend C × ℕ) : ℝ≥0∞ :=
  if st.1.trace.2 = true then 0 else
    SigningLane2Proof.lane2Potential q (2 ^ 128) XmssSecurity.Partner.landing
      (fun s => XmssSecurity.Ghost.f1 (SigningLane2FlatProof.laneKey P) (compilerView s.1, s.2))
      (fun s => XmssSecurity.Ghost.f2 (SigningLane2FlatProof.laneKey P) (compilerView s.1, s.2))
      (fun s => XmssSecurity.Ghost.f3 (SigningLane2FlatProof.laneKey P) q (compilerView s.1, s.2))
      (fun s => XmssSecurity.Ghost.f4 (SigningLane2FlatProof.laneKey P) (compilerView s.1, s.2)) st

def compilerEvent (P : PublicParameter) (q : ℕ) (st : CompilerBackend C × ℕ) : Prop :=
  st.1.trace.2 = false ∧
    SigningLane2Proof.ghostEvent (SigningLane2FlatProof.laneKey P) compilerView st ∧ st.2 ≤ q

/-- The full compiled source, including setup and verification. -/
def sourceProgram (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) :
    OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest)
      ((Bool × TopTree × Forgery) × SourceState C) :=
  (sourceGame prims A x).run sourceInit

abbrev CompilerOutcome (C : Committee) :=
  ((Bool × TopTree × Forgery) × SourceState C) ×
    ((CompilerBackend C × ℕ) × (HiddenKey → Option Digest) × Bool)

/-- One capped experiment for the fixed source and the fixed eager backend. -/
def compilerRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) :
    ProbComp (CompilerOutcome C) := do
  let s ← $ᵗ (HiddenKey → Digest)
  (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl x.1 x.2.1)
    (deferredInputSide x.1) deferredCounted (deferredKey x.1) (deferredPoint x.1) q s)
    (sourceProgram prims A x)).run ((compilerInit, 0), fun _ => none, false)

/-- The total stopped potential, rather than four individually stopped ghost
terms, supplies the local capped-expectation step. -/
def CompilerPotentialStep : Prop :=
  ∀ (x : Keys3 C) (q : ℕ), q < 2 ^ 127 →
    ∀ (t : DeferredQuery C) (st : CompilerBackend C × ℕ), CompilerReachable x.1 x.2.1 st →
      st.1.trace.2 = false → ∑' r, Pr[= r | (countImpl (compilerImpl x.1 x.2.1) deferredCounted t).run st] *
        compilerPotential x.1 q r.2 ≤ compilerPotential x.1 q st +
          if cappedCall deferredCounted q t st ∧ ¬deferredInputSide x.1 t then
            (2 ^ 128 : ℝ≥0∞)⁻¹ else 0

/-- The real guarded union and the one compiled experiment. The cap flag pays for
input hits and stale bases; the stopped ghost event pays for lane two. -/
def CompilerCoupling (prims : Primitives) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q) → q < 2 ^ 127 →
    Pr[fun z => SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
      SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
      (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
        SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z) |
      SigningLaneUnionProof.traceRun prims A x] ≤
        Pr[fun r => r.2.2.2 = true ∨ compilerEvent x.1 q r.2.1 | compilerRun prims A x q]

/-- The trace adapter preserves the pending-edge invariant of its backend. -/
theorem compilerImpl_pendingValid (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C) (hs : PendingValid st.data)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) : PendingValid r.2.data := by
  cases t with
  | hash q =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, _, rfl⟩ := hr
      exact pendingValid_step (.hash q) st.data hs a ha
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hs
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact pendingValid_step _ st.data hs a ha

theorem CompilerReachable.pendingValid (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C × ℕ) (hs : CompilerReachable P seeds st) : PendingValid st.1.data := by
  induction hs with
  | initial => exact pendingValid_init
  | step t st r _ hr ih =>
      simp only [countImpl, StateT.run_mk, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact compilerImpl_pendingValid P seeds t st.1 ih a ha

set_option maxRecDepth 100000 in
/-- Staleness is absorbing for the fixed backend. -/
theorem compilerImpl_stale (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C) (hs : st.trace.2 = true)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) : r.2.trace.2 = true := by
  cases t with
  | hash q =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, _, b, _, rfl⟩ := hr
      change (SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st)
        (.inr (.inr (.inl q))) b.2 st.trace).2 = true
      exact (SigningLane2TraceLinkProof.traceStepAt_mono seeds P st.data.cache b.2
        (compilerSigning st) (.inr (.inr (.inl q))) st.trace).2 hs
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hs
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact hs

/-- The total potential has the correct step inequality on every already-stale
state, without imposing a false lower bound on a stopped compensator. -/
theorem compilerPotential_step_stale (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (t : DeferredQuery C) (st : CompilerBackend C × ℕ) (hs : st.1.trace.2 = true) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st +
        if cappedCall deferredCounted q t st ∧ ¬deferredInputSide P t then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  have hz : ∀ r ∈ support ((countImpl (compilerImpl P seeds) deferredCounted t).run st),
      compilerPotential P q r.2 = 0 := by
    intro r hr
    simp only [countImpl, StateT.run_mk, support_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    simp only [compilerPotential, if_pos (compilerImpl_stale P seeds t st.1 hs a ha)]
  rw [SigningLane2Proof.tsum_congr_support _ _ (fun _ => 0) hz]
  simp only [mul_zero, tsum_zero]
  exact zero_le

theorem compilerView_initial : compilerView (compilerInit (C := C)) = (∅, []) := by
  apply Prod.ext
  · funext input
    simp [compilerView, compilerInit, deferredInit, SigningLane2BridgeProof.keptView]
    intro _
    rfl
  · rfl

/-- The empty trace and empty cache give zero total potential. -/
theorem compilerPotential_initial (P : PublicParameter) (q : ℕ) :
    compilerPotential P q (compilerInit (C := C), 0) = 0 := by
  have hc : ∀ e y, (∅ : XmssSecurity.HashSpec.QueryCache)
      (XmssSecurity.Partner.input (SigningLane2FlatProof.laneKey P).parameter e y) = none :=
    fun _ _ => rfl
  have h1 := XmssSecurity.Ghost.f1_initial (SigningLane2FlatProof.laneKey P) hc
  have h3 := XmssSecurity.Ghost.f3_initial (SigningLane2FlatProof.laneKey P) hc q
  rw [compilerPotential, if_neg (by simp [compilerInit]), SigningLane2Proof.lane2Potential,
    if_pos (Nat.zero_le q), SigningLane2Proof.lane2Sum]
  simp only [compilerView_initial, h1, h3, zero_tsub, zero_add]
  simp [XmssSecurity.Ghost.f4, XmssSecurity.Ghost.postPot_nil]

/-- The stopped ghost event is dominated by the total potential. -/
theorem compilerEvent_le_potential (P : PublicParameter) (q : ℕ) (st : CompilerBackend C × ℕ)
    (he : compilerEvent P q st) : 1 ≤ compilerPotential P q st := by
  obtain ⟨hs, he, hq⟩ := he
  have hN : (((2 ^ XmssSecurity.digestBits : ℕ) : ℝ≥0∞)) = (2 ^ 128 : ℝ≥0∞) := by
    norm_num [XmssSecurity.digestBits]
  have hbad : (2 ^ 128 : ℝ≥0∞) * 2 ^ 128 ≤
      XmssSecurity.Ghost.f1 (SigningLane2FlatProof.laneKey P) (compilerView st.1, st.2) +
        XmssSecurity.Ghost.f4 (SigningLane2FlatProof.laneKey P) (compilerView st.1, st.2) := by
    rcases he with he | he
    · refine le_trans ?_ le_self_add
      unfold XmssSecurity.Ghost.f1
      rw [if_pos he, mul_one, hN]
      exact le_self_add
    · refine le_trans ?_ le_add_self
      unfold XmssSecurity.Ghost.f4 XmssSecurity.Ghost.postPot
      rw [if_pos he, mul_one, hN]
  rw [compilerPotential, if_neg (by simp [hs]), SigningLane2Proof.lane2Potential,
    if_pos hq, SigningLane2Proof.lane2Sum]
  calc (1 : ℝ≥0∞) = (2 ^ 128 * 2 ^ 128) * (2 ^ 128 * 2 ^ 128)⁻¹ :=
      (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm
    _ ≤ _ := by
      refine mul_le_mul' (hbad.trans ?_) le_rfl
      rw [add_right_comm]
      exact le_self_add

/-- The fixed compiler's local potential step and real-to-compiler coupling imply
the original `LaneTraceCap`, with its original keys, support and budget hypotheses. -/
theorem laneTraceCap_of_compiler (prims : Primitives)
    (hstep : CompilerPotentialStep (C := C)) (hcouple : CompilerCoupling (C := C) prims) :
    SigningLaneUnionProof.LaneTraceCap (C := C) prims := by
  intro A q x hx hkeys hq hsmall
  exact SigningCappedExpectProof.probEvent_le_of_capped_expect
    (impl := compilerImpl x.1 x.2.1) (inputSide := deferredInputSide x.1) (p := deferredCounted)
    (run := SigningLaneUnionProof.traceRun prims A x)
    (event := fun z => SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
      SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
      (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
        SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z))
    (keyOf := deferredKey x.1) (point := deferredPoint x.1) (q := q)
    (Inv := CompilerReachable x.1 x.2.1) (f := compilerPotential x.1 q)
    (hinv := fun t st hs r hr => CompilerReachable.step t st r hs hr)
    (hstep := fun t st hs => by
      cases hb : st.1.trace.2 with
      | false => exact hstep x q hsmall t st hs hb
      | true => exact compilerPotential_step_stale x.1 x.2.1 q t st hb)
    (E := compilerEvent x.1 q)
    (hE := compilerEvent_le_potential x.1 q) (oa := sourceProgram prims A x)
    (σ₀ := compilerInit) (hσ₀ := CompilerReachable.initial)
    (hf₀ := compilerPotential_initial x.1 q)
    (hcouple := hcouple A q x hx hkeys hq hsmall)

/-- Silent presampling and recording cannot add a message-digest cache entry. -/
theorem deferredImpl_keptView_uncounted (t : DeferredQuery C)
    (ht : ¬deferredCounted t) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) :
    SigningLane2BridgeProof.keptView IsMsg r.2.cache =
      SigningLane2BridgeProof.keptView IsMsg st.cache := by
  cases t with
  | hash q => simp [deferredCounted] at ht
  | pending p => simp [deferredCounted] at ht
  | virtual T p => simp [deferredCounted] at ht
  | pad p =>
      cases hp : st.pads p with
      | none =>
          simp only [deferredImpl, StateT.run, hp, support_map] at hr
          obtain ⟨a, _, rfl⟩ := hr
          rfl
      | some value =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          rfl
  | plant p value =>
      cases hp : st.cache p.query with
      | none =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          apply SigningLane2BridgeProof.keptView_cacheQuery_of_not
          intro input hi
          cases p with
          | prf seed point => cases hi
          | pending P p value =>
              cases hi
              exact PendingInput.not_isMsg P p value
      | some prior =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          rfl
  | sample =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      rfl
  | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      rfl
  | _ =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      rfl

/-- Every uncounted compiler call keeps both the lane-two view and its stopped bit. -/
theorem compilerImpl_view_uncounted (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (ht : ¬deferredCounted t) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) :
    compilerView r.2 = compilerView st ∧ r.2.trace.2 = st.trace.2 := by
  cases t with
  | hash q => simp [deferredCounted] at ht
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact ⟨rfl, rfl⟩
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact ⟨Prod.ext (deferredImpl_keptView_uncounted _ ht st.data a ha) rfl, rfl⟩

/-- The potential depends only on the public cache/trace view, the stopped bit,
and the number of counted calls. -/
theorem compilerPotential_congr (P : PublicParameter) (q : ℕ)
    (s t : CompilerBackend C × ℕ) (hv : compilerView s.1 = compilerView t.1)
    (hs : s.1.trace.2 = t.1.trace.2) (hc : s.2 = t.2) :
    compilerPotential P q s = compilerPotential P q t := by
  simp only [compilerPotential, SigningLane2Proof.lane2Potential,
    SigningLane2Proof.lane2Sum, hv, hs, hc]

/-- All uncounted local cases of `CompilerPotentialStep` hold without a
reachability or non-stale hypothesis. -/
theorem compilerPotential_step_uncounted (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (t : DeferredQuery C) (ht : ¬deferredCounted t)
    (st : CompilerBackend C × ℕ) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st +
        if cappedCall deferredCounted q t st ∧ ¬deferredInputSide P t then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  have heq : ∀ r ∈ support ((countImpl (compilerImpl P seeds) deferredCounted t).run st),
      compilerPotential P q r.2 = compilerPotential P q st := by
    intro r hr
    simp only [countImpl, StateT.run_mk, support_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    obtain ⟨hv, hs⟩ := compilerImpl_view_uncounted P seeds t ht st.1 a ha
    exact compilerPotential_congr P q _ st hv hs (by simp [ht])
  rw [SigningLane2Proof.tsum_congr_support _ _ (fun _ => compilerPotential P q st) heq,
    ENNReal.tsum_mul_right]
  exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans le_self_add

/-- Advancing the count while keeping the view cannot increase the stopped
potential. The moment term decreases with the remaining budget. -/
theorem compilerPotential_tick (P : PublicParameter) (q : ℕ) (st : CompilerBackend C)
    (k : ℕ) : compilerPotential P q (st, k + 1) ≤ compilerPotential P q (st, k) := by
  by_cases hs : st.trace.2 = true
  · simp only [compilerPotential, if_pos hs, le_refl]
  simp only [compilerPotential, if_neg hs, SigningLane2Proof.lane2Potential]
  by_cases hk : k + 1 ≤ q
  · rw [if_pos hk, if_pos (by omega : k ≤ q)]
    dsimp only [SigningLane2Proof.lane2Sum]
    have h3 : XmssSecurity.Ghost.f3 (SigningLane2FlatProof.laneKey P) q
        (compilerView st, k + 1) ≤
        XmssSecurity.Ghost.f3 (SigningLane2FlatProof.laneKey P) q (compilerView st, k) :=
      XmssSecurity.Partner.F3_budget (by omega)
    refine mul_le_mul' ?_ le_rfl
    refine add_le_add ?_ le_rfl
    refine add_le_add le_rfl ?_
    exact tsub_le_tsub_right h3 _
  · rw [if_neg hk]
    exact zero_le

/-- A pending hash answer changes only the symbolic table. -/
theorem compilerImpl_view_pending (P : PublicParameter) (seeds : C.Term → HashOutput)
    (p : PendingInput) (st : CompilerBackend C)
    (r : DeferredOutput × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds (.pending p)).run st)) :
    compilerView r.2 = compilerView st ∧ r.2.trace.2 = st.trace.2 := by
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  cases hp : st.data.pending p with
  | none =>
      simp only [deferredImpl, hp, support_map] at ha
      obtain ⟨v, _, rfl⟩ := ha
      exact ⟨rfl, rfl⟩
  | some value =>
      simp only [deferredImpl, hp, mem_support_pure_iff] at ha
      subst a
      exact ⟨rfl, rfl⟩

/-- A virtual PRF call changes only its term/point presence table. -/
theorem compilerImpl_view_virtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (p : Point) (st : CompilerBackend C)
    (r : Unit × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds (.virtual T p)).run st)) :
    compilerView r.2 = compilerView st ∧ r.2.trace.2 = st.trace.2 := by
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  simp only [deferredImpl, mem_support_pure_iff] at ha
  subst a
  exact ⟨rfl, rfl⟩

/-- A counted call that keeps the view satisfies the potential step with no
increase, even when it crosses the cap. -/
theorem compilerPotential_step_of_sameView (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (t : DeferredQuery C)
    (ht : deferredCounted t) (st : CompilerBackend C × ℕ)
    (hview : ∀ r ∈ support ((compilerImpl P seeds t).run st.1),
      compilerView r.2 = compilerView st.1 ∧ r.2.trace.2 = st.1.trace.2) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted t).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st +
        if cappedCall deferredCounted q t st ∧ ¬deferredInputSide P t then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  refine (XmssSecurity.Ghost.tsum_le_of_support _ _ _ ?_).trans le_self_add
  intro r hr
  simp only [countImpl, StateT.run_mk, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  obtain ⟨hv, hs⟩ := hview a ha
  rw [compilerPotential_congr P q _ (st.1, st.2 + 1) hv hs (by simp [ht])]
  exact compilerPotential_tick P q st.1 st.2

/-- The pending-call case of the fixed local potential contract is unconditional. -/
theorem compilerPotential_step_pending (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (p : PendingInput) (st : CompilerBackend C × ℕ) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted (.pending p)).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st +
        if cappedCall (deferredCounted (C := C)) q (.pending p) st ∧
            ¬deferredInputSide (C := C) P (.pending p) then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 :=
  compilerPotential_step_of_sameView P seeds q (.pending p) trivial st
    (compilerImpl_view_pending P seeds p st.1)

/-- The virtual-PRF case of the fixed local potential contract is unconditional. -/
theorem compilerPotential_step_virtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (T : C.Term) (p : Point) (st : CompilerBackend C × ℕ) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted (.virtual T p)).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st +
        if cappedCall deferredCounted q (.virtual T p) st ∧ ¬deferredInputSide P (.virtual T p) then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 :=
  compilerPotential_step_of_sameView P seeds q (.virtual T p) trivial st
    (compilerImpl_view_virtual P seeds T p st.1)

/-- After the concrete bookkeeping, pending and virtual cases, the local
contract is exactly its actual hash/PRF-call cases. -/
theorem compilerPotentialStep_iff_hash : CompilerPotentialStep (C := C) ↔
    ∀ (x : Keys3 C) (q : ℕ), q < 2 ^ 127 →
      ∀ (t : Query C) (st : CompilerBackend C × ℕ),
        CompilerReachable x.1 x.2.1 st → st.1.trace.2 = false →
        ∑' r, Pr[= r | (countImpl (compilerImpl x.1 x.2.1) deferredCounted (.hash t)).run st] *
          compilerPotential x.1 q r.2 ≤ compilerPotential x.1 q st +
            if cappedCall deferredCounted q (.hash t) st ∧ ¬deferredInputSide x.1 (.hash t) then
              (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  constructor
  · intro h x q hq t st hst hs
    exact h x q hq (.hash t) st hst hs
  · intro h x q hq t st hst hs
    cases t with
    | hash t => exact h x q hq t st hst hs
    | pending p => exact compilerPotential_step_pending x.1 x.2.1 q p st
    | virtual T p => exact compilerPotential_step_virtual x.1 x.2.1 q T p st
    | _ => exact compilerPotential_step_uncounted x.1 x.2.1 q _ (by simp [deferredCounted]) st

/-- A non-`Th` query, including a PRF, mask or stream-key query, has no input
in the message hash cache. -/
theorem deferredImpl_keptView_not_hash (t : Query C) (ht : ∀ input, t ≠ .hash input)
    (st : DeferredState C) (r : DeferredSpec C (.hash t) × DeferredState C)
    (hr : r ∈ support ((deferredImpl (.hash t)).run st)) :
    SigningLane2BridgeProof.keptView IsMsg r.2.cache =
      SigningLane2BridgeProof.keptView IsMsg st.cache := by
  simp only [deferredImpl, StateT.run, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  change a ∈ support (((Query C →ₒ HashOutput).randomOracle t).run st.cache) at ha
  cases hc : st.cache t with
  | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at ha
      obtain ⟨u, _, rfl⟩ := ha
      exact SigningLane2BridgeProof.keptView_cacheQuery_of_not
        (fun input he => False.elim (ht input he)) _ _
  | some value =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc,
        mem_support_pure_iff] at ha
      subst a
      rfl

set_option maxRecDepth 100000 in
/-- A non-`Th` call cannot trigger the eager base grind or its signing trace entry. -/
theorem compilerImpl_view_not_hash (P : PublicParameter) (seeds : C.Term → HashOutput)
    (call : DeferredQuery C) (hcall : ∃ t, call = .hash t ∧ ∀ input, t ≠ .hash input)
    (st : CompilerBackend C) (r : DeferredSpec C call × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds call).run st)) :
    compilerView r.2 = compilerView st ∧ r.2.trace.2 = st.trace.2 := by
  obtain ⟨t, rfl, ht⟩ := hcall
  have hn : ∀ cache (state : TsigState C), ¬∃ e,
      SigningGuessProof.RandomizerCached seeds cache e ∧
        SigningFlatProof.BaseCall P e (SigningGuessProof.cachedRandomizer seeds cache e)
          state (.inr (.inr (.inl t))) := by
    intro cache state
    rintro ⟨e, _, input, _, hcall⟩
    rcases hcall with hcall | hcall
    · cases hcall
    · cases hcall
      exact ht input rfl
  simp only [compilerImpl, StateT.run, SigningR1FixedProof.cachedExtra,
    if_neg (hn st.data.cache (compilerSigning st)), simulateQ_pure] at hr
  change r ∈ support (do
    let a ← (deferredImpl (.hash t)).run st.data
    pure (a.1, { st with data := a.2, trace := (
      SigningLaneUnionProof.traceStepAt seeds P st.data.cache (compilerSigning st)
        (.inr (.inr (.inl t))) a.2.cache st.trace) })) at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  simp only [compilerView, SigningLaneUnionProof.traceStepAt,
    dif_neg (hn st.data.cache (compilerSigning st))]
  exact ⟨Prod.ext (deferredImpl_keptView_not_hash t ht st.data a ha) rfl, trivial⟩

/-- All concrete non-`Th` cases of the local contract have zero potential increase. -/
theorem compilerPotential_step_not_hash (P : PublicParameter)
    (seeds : C.Term → HashOutput) (q : ℕ) (t : Query C)
    (ht : ∀ input, t ≠ .hash input) (st : CompilerBackend C × ℕ) :
    ∑' r, Pr[= r | (countImpl (compilerImpl P seeds) deferredCounted (.hash t)).run st] *
      compilerPotential P q r.2 ≤ compilerPotential P q st +
        if cappedCall deferredCounted q (.hash t) st ∧ ¬deferredInputSide P (.hash t) then
          (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 :=
  compilerPotential_step_of_sameView P seeds q (.hash t) trivial st
    (compilerImpl_view_not_hash P seeds (.hash t) ⟨t, rfl, ht⟩ st.1)

/-- The only remaining local cases are concrete calls to `Th`; the real PRF,
mask, stream-key and ceremony calls have already been discharged. -/
theorem compilerPotentialStep_iff_hashInput : CompilerPotentialStep (C := C) ↔
    ∀ (x : Keys3 C) (q : ℕ), q < 2 ^ 127 →
      ∀ (input : HashInput) (st : CompilerBackend C × ℕ),
        CompilerReachable x.1 x.2.1 st → st.1.trace.2 = false →
        ∑' r, Pr[= r | (countImpl (compilerImpl x.1 x.2.1) deferredCounted
          (.hash (.hash input))).run st] *
          compilerPotential x.1 q r.2 ≤ compilerPotential x.1 q st +
            if cappedCall (deferredCounted (C := C)) q (.hash (.hash input)) st ∧
                ¬deferredInputSide (C := C) x.1 (.hash (.hash input)) then
              (2 ^ 128 : ℝ≥0∞)⁻¹ else 0 := by
  constructor
  · intro h x q hq input st hst hs
    exact h x q hq (.hash (.hash input)) st hst hs
  · intro h
    apply compilerPotentialStep_iff_hash.mpr
    intro x q hq t st hst hs
    cases t with
    | hash input => exact h x q hq input st hst hs
    | _ =>
        exact compilerPotential_step_not_hash x.1 x.2.1 q _
          (by intro input he; cases he) st

/-- Conservative planting and all other symbolic operations preserve every
already materialized oracle answer. -/
theorem deferredImpl_cache_le (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C)
    (hr : r ∈ support ((deferredImpl t).run st)) : st.cache ≤ r.2.cache := by
  cases t with
  | hash q =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact (randomOracle_support q st.cache a ha).1
  | pending p =>
      cases hp : st.pending p with
      | none =>
          simp only [deferredImpl, StateT.run, hp, support_map] at hr
          obtain ⟨a, _, rfl⟩ := hr
          exact le_rfl
      | some value =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          exact le_rfl
  | pad p =>
      cases hp : st.pads p with
      | none =>
          simp only [deferredImpl, StateT.run, hp, support_map] at hr
          obtain ⟨a, _, rfl⟩ := hr
          exact le_rfl
      | some value =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          exact le_rfl
  | plant p value =>
      cases hp : st.cache p.query with
      | none =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          exact QueryCache.le_cacheQuery _ hp
      | some prior =>
          simp only [deferredImpl, StateT.run, hp, mem_support_pure_iff] at hr
          subst r
          exact le_rfl
  | sample =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact le_rfl
  | uniform n =>
      simp only [deferredImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact le_rfl
  | _ =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact le_rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The eager adapter also preserves every materialized oracle answer. -/
theorem compilerImpl_cache_le (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C) (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) : st.data.cache ≤ r.2.data.cache := by
  cases t with
  | hash q =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, hb, rfl⟩ := hr
      refine (deferredImpl_cache_le (.hash q) st.data a ha).trans ?_
      exact SeedHitProof.support_simulateQ_inv (Query C →ₒ HashOutput).randomOracle
        (fun cache => a.2.cache ≤ cache)
        (fun query cache hc answer hanswer => hc.trans (randomOracle_support query cache answer hanswer).1)
        (SigningR1FixedProof.cachedExtra seeds P
          (((st.data.cache, 0), []), compilerSigning st, false) (.inr (.inr (.inl q)))
          (((a.2.cache, 0), []), compilerSigning st, false)) a.2.cache le_rfl b
          (by
            dsimp only [StateT.run]
            with_reducible exact hb)
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact le_rfl
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_cache_le _ st.data a ha

/-- The backend binding map extends its previous assignments on every step. -/
theorem compilerImpl_boundExtends (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C) (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) :
    SigningGuessProof.BoundExtends (compilerSigning st) (compilerSigning r.2) := by
  cases t with
  | hash q =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, _, b, _, rfl⟩ := hr
      exact fun _ _ h => h
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      intro f old hb
      change st.bound f = some old at hb
      change (if st.bound e = none then Function.update st.bound e (some message)
        else st.bound) f = some old
      by_cases he : st.bound e = none
      · rw [if_pos he]
        have hfe : f ≠ e := by
          intro h
          subst f
          rw [he] at hb
          cases hb
        simpa only [Function.update_of_ne hfe] using hb
      · simpa only [if_neg he] using hb
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact fun _ _ h => h

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
/-- The compiler maintains the actual trace-entry provenance and unique leaf
indices using the already-proved dynamic `traceStepAt` invariant. -/
theorem compilerImpl_entryBases (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) (st : CompilerBackend C)
    (hs : SigningLane2TraceLinkProof.EntryBases seeds P st.data.cache
      (compilerSigning st) st.trace.1 ∧ st.trace.1.leafIndices.Nodup)
    (r : DeferredSpec C t × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds t).run st)) :
    SigningLane2TraceLinkProof.EntryBases seeds P r.2.data.cache
      (compilerSigning r.2) r.2.trace.1 ∧ r.2.trace.1.leafIndices.Nodup := by
  have hbound := compilerImpl_boundExtends P seeds t st r hr
  cases t with
  | hash q =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, hb, rfl⟩ := hr
      have hab : a.2.cache ≤ b.2 :=
        SeedHitProof.support_simulateQ_inv (Query C →ₒ HashOutput).randomOracle
          (fun cache => a.2.cache ≤ cache)
          (fun query cache hc answer hanswer => hc.trans (randomOracle_support query cache answer hanswer).1)
          (SigningR1FixedProof.cachedExtra seeds P
            (((st.data.cache, 0), []), compilerSigning st, false) (.inr (.inr (.inl q)))
            (((a.2.cache, 0), []), compilerSigning st, false)) a.2.cache le_rfl b
            (by
              dsimp only [StateT.run]
              with_reducible exact hb)
      have hac : st.data.cache ≤ a.2.cache := deferredImpl_cache_le (.hash q) st.data a ha
      have hself : a.2.cache q = some a.1 := by
        simp only [deferredImpl, StateT.run, support_map] at ha
        obtain ⟨raw, hraw, rfl⟩ := ha
        exact (randomOracle_support q st.data.cache raw hraw).2.1
      apply SigningLane2TraceLinkProof.traceStepAt_bases seeds P st.data.cache b.2
        (compilerSigning st) (.inr (.inr (.inl q))) st.trace (hac.trans hab) _ hs.1 hs.2
      intro input hcall
      rcases hcall with hcall | hcall
      · cases hcall
      · cases hcall
        exact ⟨a.1, hab hself⟩
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact ⟨hs.1.mono le_rfl hbound, hs.2⟩
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact ⟨hs.1.mono (deferredImpl_cache_le _ st.data a ha) hbound, hs.2⟩

/-- Reachability gives base provenance and a duplicate-free signing trace even
when plants, records and bindings are chosen independently of the source. -/
theorem CompilerReachable.entryBases (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C × ℕ) (hs : CompilerReachable P seeds st) :
    SigningLane2TraceLinkProof.EntryBases seeds P st.1.data.cache
      (compilerSigning st.1) st.1.trace.1 ∧ st.1.trace.1.leafIndices.Nodup := by
  induction hs with
  | initial =>
      exact ⟨fun _ h => (List.not_mem_nil h).elim,
        by simp [compilerInit, XmssSecurity.SigningCacheTrace.leafIndices]⟩
  | step t st r _ hr ih =>
      simp only [countImpl, StateT.run_mk, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact compilerImpl_entryBases P seeds t st.1 ih a ha

end SigningLaneHybridCapProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.hiddenCandidate_none_of_isMsg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.hiddenCandidate_none_of_isMsg

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.not_inputSide_msgCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.not_inputSide_msgCall

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.PendingInput.not_isMsg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.PendingInput.not_isMsg
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.pendingValid_capped_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.pendingValid_capped_run
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.exact_deferredBottomRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.exact_deferredBottomRow
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.bottom_walks_of_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.bottom_walks_of_edges
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.referenceJob_row_of_walks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.referenceJob_row_of_walks
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.termSum_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.termSum_program
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.CompilerReachable.pendingValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.CompilerReachable.pendingValid
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerImpl_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerImpl_stale
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_step_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_step_stale
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_initial
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerEvent_le_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerEvent_le_potential
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.laneTraceCap_of_compiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.laneTraceCap_of_compiler

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_step_uncounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_step_uncounted
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_tick
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_step_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_step_pending
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_step_virtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_step_virtual
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotentialStep_iff_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotentialStep_iff_hash
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotential_step_not_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotential_step_not_hash
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerPotentialStep_iff_hashInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerPotentialStep_iff_hashInput
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.deferredImpl_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.deferredImpl_cache_le
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerImpl_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerImpl_cache_le
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerImpl_boundExtends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerImpl_boundExtends
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.compilerImpl_entryBases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.compilerImpl_entryBases
/-- info: 'ThresholdLeanXmssSecurity.SigningLaneHybridCapProof.CompilerReachable.entryBases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigningLaneHybridCapProof.CompilerReachable.entryBases

end ThresholdLeanXmssSecurity
