import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Sync

/-! # The relation inside a handler of the O1 coupling

- `ExtraOpen` is `ExtraO1` with the clause `bottomSeen` void at the rows of `openRow`. A row is open
  from its first honest PRF read to its last pending answer.
- `PadsFixed` states that each stored pad of the compiler is the fixed pad. `backend_padsFixed`
  states that each run on the backend keeps it.
- `SyncAt` is the relation inside a handler. It reads two views of the carried state.
  `syncO1_iff_syncIn` states that the boundary relation with the fixed pads is `SyncIn` at the carried
  state of the real state.
- `CallFrame` holds the effect of honest calls on both states. `ExtraOpen.frame` and `TopO1.frame`
  carry the clauses over a frame.
- `step_pads` adds the fixed pads to a step contract of `SyncO1`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Frame
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

/-! ## Views of the real state -/

/-- The state that the opening handler carries. A world call does not change it. -/
abbrev Carried (C : Committee) := SigningJointEagerProof.OpeningState C

/-- The real state with another carried state. A handler holds its own signing state until it
returns, and a tree request names its tree when it returns. -/
def withCarried (a : RealState C) (c : Carried C) : RealState C := ((a.1.1, c), a.2)

/-- The real state with the hidden-key flag up. In `ExtraO1` only `prfSeen` and `bottomSeen` read
the flag. -/
def flagUp (a : RealState C) : RealState C := ((a.1.1, ((a.1.2.1.1, true), a.1.2.2)), a.2)

theorem withCarried_self (a : RealState C) : withCarried a a.1.2 = a := rfl

theorem withSigning_eq (a : RealState C) (sig : TsigState C) :
    withSigning a sig = withCarried a ((sig, a.1.2.1.2), a.1.2.2) := rfl

theorem withCandidates_eq (a : RealState C) (cs : List (HiddenKey × Digest)) :
    withCandidates a cs = withCarried a (a.1.2.1, a.1.2.2.1, cs) := rfl

/-! ## The relation with open rows -/

/-- `ExtraO1` with `bottomSeen` void at the rows of `openRow`. A row is open from its first honest
PRF read to its last pending answer. -/
structure ExtraOpen (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (rev : HiddenKey → Option Digest) (openRow : KeyIndex → ChainIndex → Prop)
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop where
  /-- Each clause that does not read the flag. -/
  rest : ExtraO1 prims x top s rev (flagUp a) b
  /-- The clause `prfSeen` of `ExtraO1`. -/
  prfSeen : realFlag a = false → ∀ T p, visibleOf a (.prf (x.2.1 T) p) ≠ none →
    TprfSecurityProof.Revealed (realSigning a).corrupt (.inl T) ∨ Constrained p
  /-- The clause `bottomSeen` of `ExtraO1` outside the open rows. -/
  bottomSeen : realFlag a = false → ∀ T e l (d : XmssSecurity.ChainStep), ¬openRow e l →
    visibleOf a (.prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) ≠ none →
      TprfSecurityProof.Revealed (realSigning a).corrupt (.inl T) ∨
        ∀ d' : XmssSecurity.ChainStep, (dataOf x b.2).pending (.bottom e l d') ≠ none

section Open
variable (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
  (rev : HiddenKey → Option Digest)

/-- With no open row the relation is `ExtraO1`. -/
theorem extraOpen_of_extra (a : RealState C) (b : SourceStateO1 C × CompState C)
    (h : ExtraO1 prims x top s rev a b) :
    ExtraOpen prims x top s rev (fun _ _ => False) a b :=
  ⟨{ h with
      prfSeen := fun hf => by cases hf
      bottomSeen := fun hf => by cases hf },
    h.prfSeen, fun hf T e l d _ hv => h.bottomSeen hf T e l d hv⟩

/-- The relation with open rows gives `ExtraO1` when each open row has its pending answers. -/
theorem extra_of_extraOpen (openRow : KeyIndex → ChainIndex → Prop) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (h : ExtraOpen prims x top s rev openRow a b)
    (hrows : ∀ e l, openRow e l →
      ∀ d' : XmssSecurity.ChainStep, (dataOf x b.2).pending (.bottom e l d') ≠ none) :
    ExtraO1 prims x top s rev a b :=
  { h.rest with
    prfSeen := h.prfSeen
    bottomSeen := fun hf T e l d hv => by
      by_cases ho : openRow e l
      · exact Or.inr (hrows e l ho)
      · exact h.bottomSeen hf T e l d ho hv }

/-- A larger set of open rows keeps the relation. -/
theorem ExtraOpen.mono (openRow openRow' : KeyIndex → ChainIndex → Prop) (a : RealState C)
    (b : SourceStateO1 C × CompState C) (h : ExtraOpen prims x top s rev openRow a b)
    (hsub : ∀ e l, openRow e l → openRow' e l) :
    ExtraOpen prims x top s rev openRow' a b :=
  ⟨h.rest, h.prfSeen,
    fun hf T e l d ho hv => h.bottomSeen hf T e l d (fun hold => ho (hsub e l hold)) hv⟩

end Open

/-! ## The fixed pads -/

section Pads
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- A stored pad of the compiler is the fixed pad. A row reads its two pads again when the tree is
built again. -/
def PadsFixed (st : CompState C) : Prop :=
  ∀ p v, (dataOf x st).pads p = some v → v = pads p

/-- The cached-extra suffix of a read keeps the stored pads. -/
theorem hashTail_pads (P : PublicParameter) (seeds : C.Term → HashOutput) (input : Query C)
    (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (hashTail P seeds input st value cache)) :
    r.2.1.1.data.pads = st.1.1.data.pads := by
  simp only [hashTail, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨a, _, rfl⟩ := hr
  rfl

attribute [local irreducible] hashTail

/-- An ordinary capped step stores only fixed pads. -/
theorem ordinary_padsFixed (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (h : ∀ p v, st.1.1.data.pads p = some v → v = pads p)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinary P seeds q s pads t st)) :
    ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
  have cap (t : DeferredQuery C ⊕ HiddenKey) (ht : ∀ p, t ≠ .inl (.pad p))
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (hr : r ∈ support ((SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
        (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s t).run st)) :
      ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
    rw [cappedCompiler_pads_of_ne P seeds q s t ht st r hr]
    exact h
  cases t with
  | inr k => exact cap _ (fun _ he => by cases he) r hr
  | inl t =>
    cases t with
    | pad point =>
      simp only [ordinary, mem_support_pure_iff] at hr
      subst r
      cases hp : st.1.1.data.pads point with
      | some value => simpa only [padStep, hp] using h
      | none =>
        intro p v hv
        simp only [padStep, hp] at hv
        by_cases he : p = point
        · subst p
          simpa only [Function.update_self, Option.some.injEq] using hv.symm
        · exact h p v (by simpa only [Function.update_of_ne he] using hv)
    | _ => exact cap _ (fun _ he => by cases he) r hr

/-- A free-slot read keeps the stored pads. -/
theorem freshRestT_padsFixed (z : RestSlot C) (st : CappedCompilerState C)
    (h : ∀ p v, st.1.1.data.pads p = some v → v = pads p) (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
      (freshRest x.1 x.2.1 x.2.2 z st))) :
    ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
  rw [freshRestT_run] at hr
  cases hc : st.1.1.data.cache (restInput x.2.1 x.2.2 z) <;> rw [hc] at hr <;>
    rw [hashTail_pads x.1 x.2.1 _ st _ _ r hr] <;> exact h

/-- An ordinary step over the fixed tables stores only fixed pads. -/
theorem ordinaryT_padsFixed (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (h : ∀ p v, st.1.1.data.pads p = some v → v = pads p)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinaryT x.1 x.2.1 x.2.2 q s pads noise rest t st)) :
    ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
  have pend (edge : ChainNoiseIndex) (r : DeferredOutput × CappedCompilerState C)
      (hr : r ∈ support (simulateQ (resolvePrivateTable (Sum.elim noise rest))
        (freshPending edge st))) :
      ∀ p v, r.2.1.1.data.pads p = some v → v = pads p := by
    cases hp : st.1.1.data.pending (chainPending edge) with
    | some v =>
      simp only [freshPending, hp, simulateQ_pure, mem_support_pure_iff] at hr
      subst r
      exact h
    | none =>
      simp only [freshPending, hp, simulateQ_bind, HasQuery.instOfMonadLift_query,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        resolvePrivateTable, Sum.elim_inl, simulateQ_pure, pure_bind, mem_support_pure_iff] at hr
      subst r
      exact h
  cases t with
  | inr k =>
    simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
    exact ordinary_padsFixed q s pads x.1 x.2.1 _ st h r hr
  | inl t =>
    cases t with
    | hash input =>
      simp only [ordinaryT, ordinaryRaw] at hr
      cases hz : restRoute x.2.1 x.2.2 input with
      | some z =>
        simp only [hz] at hr
        exact freshRestT_padsFixed x pads rest noise z st h r hr
      | none =>
        simp only [hz, resolvePrivateTable_lift] at hr
        exact ordinary_padsFixed q s pads x.1 x.2.1 _ st h r hr
    | pending p =>
      cases p with
      | bottom e l p => exact pend _ r hr
      | top b l p => exact pend _ r hr
      | _ =>
        simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
        exact ordinary_padsFixed q s pads x.1 x.2.1 _ st h r hr
    | _ =>
      simp only [ordinaryT, ordinaryRaw, resolvePrivateTable_lift] at hr
      exact ordinary_padsFixed q s pads x.1 x.2.1 _ st h r hr

/-- Each backend query keeps the fixed pads. -/
theorem backendT_padsFixed (t : (SpecX C).Domain) (st : CompState C) (h : PadsFixed x pads st)
    (r : SpecX C t × CompState C)
    (hr : r ∈ support ((compBackend x q s pads u rest noise t).run st)) :
    PadsFixed x pads r.2 := by
  apply backendT_preserves (fun _ => True) capTag x q s pads (tauOf s pads) (gOf s pads u) noise
    rest (fun cs _ => ∀ p v, cs.1.1.data.pads p = some v → v = pads p) ?_ ?_ ?_ t trivial st h r hr
  · intro t _ cs sh h r hr
    exact ordinaryT_padsFixed x q s pads rest noise t (merged x.2.1 cs sh.cache) h r hr
  · intro cs sh h T p tag a _ r hr
    change ∀ p v, r.2.1.1.data.pads p = some v → v = pads p
    rw [hashTail_pads x.1 x.2.1 _ _ _ _ r hr]
    exact h
  · intro cs sh h _ _ _ _ _
    exact h

/-- Each run on the backend keeps the fixed pads. -/
theorem backend_padsFixed {α : Type} (oa : OracleComp (SpecX C) α) (st : CompState C)
    (h : PadsFixed x pads st) (r : α × CompState C)
    (hr : r ∈ support ((simulateQ (compBackend x q s pads u rest noise) oa).run st)) :
    PadsFixed x pads r.2 :=
  simulateQ_sticky (compBackend x q s pads u rest noise) (PadsFixed x pads)
    (fun t st h r hr => backendT_padsFixed x q s pads u rest noise t st h r hr) oa st h r hr

end Pads

/-! ## The relation inside a handler -/

section Relation
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The relation inside a handler. `cCore` is the carried state that the compiler state matches.
`cTime` is the carried state that the timing clauses read. `rev` is the reveal map that the timing
clauses read. -/
def SyncAt (top : TopTree) (rev : HiddenKey → Option Digest)
    (openRow : KeyIndex → ChainIndex → Prop) (cCore cTime : Carried C)
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (b.1.base, b.2) ∧
    ExtraOpen prims x top s rev openRow (withCarried a cTime) b ∧ TopO1 prims x top a b ∧
    PadsFixed x pads b.2

/-- The relation inside a handler with no open row and the reveal map of the source. -/
abbrev SyncIn (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C) : Prop :=
  SyncAt prims x s pads u rest noise top b.1.base.revealed (fun _ _ => False) cCore cTime a b

/-- The boundary relation with the fixed pads is the relation inside a handler at the carried state
of the real state. -/
theorem syncO1_iff_syncIn (top : TopTree) (a : RealState C) (b : SourceStateO1 C × CompState C) :
    SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2 ↔
      SyncIn prims x s pads u rest noise top a.1.2 a.1.2 a b := by
  constructor
  · rintro ⟨⟨⟨hcore, hx⟩, htop⟩, hp⟩
    exact ⟨hcore, extraOpen_of_extra prims x top s _ a b hx, htop, hp⟩
  · rintro ⟨hcore, hx, htop, hp⟩
    exact ⟨⟨⟨hcore, extra_of_extraOpen prims x top s _ _ a b hx (fun _ _ h => h.elim)⟩, htop⟩, hp⟩

/-- The relation inside a signing handler of `SyncMid` gives the relation with views. -/
theorem syncIn_of_syncMid (top : TopTree) (sigCore sigTime : TsigState C) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b)
    (hp : PadsFixed x pads b.2) :
    SyncIn prims x s pads u rest noise top ((sigCore, a.1.2.1.2), a.1.2.2)
      ((sigTime, a.1.2.1.2), a.1.2.2) a b :=
  ⟨hs.1, extraOpen_of_extra prims x top s _ _ b hs.2.1, hs.2.2, hp⟩

/-- The relation with views gives the relation inside a signing handler of `SyncMid`. The lemmas of
the chain release take it. -/
theorem syncMid_of_syncIn (top : TopTree) (sigCore sigTime : TsigState C) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top ((sigCore, a.1.2.1.2), a.1.2.2)
      ((sigTime, a.1.2.1.2), a.1.2.2) a b) :
    SyncMid prims x top s pads noise (gOf s pads u) rest sigCore sigTime a b ∧
      PadsFixed x pads b.2 := by
  obtain ⟨hcore, hx, htop, hp⟩ := hs
  exact ⟨⟨hcore, extra_of_extraOpen prims x top s _ _ _ b hx (fun _ _ h => h.elim), htop⟩, hp⟩

end Relation

/-! ## The effect of honest calls -/

/-- The effect of honest calls and of the opening releases that they trigger. `seen` holds each
query that the calls add to the visible cache. No call is a canonical base call, so the trace does
not move. -/
structure CallFrame (x : Keys3 C) (seen : Query C → Prop) (a a' : RealState C)
    (b b' : SourceState C × CompState C) : Prop where
  carried : a'.1.2 = a.1.2
  visible : visibleOf a ≤ visibleOf a'
  fresh : ∀ query, visibleOf a' query ≠ none → visibleOf a query ≠ none ∨ seen query
  log : realLog a ≤ realLog a'
  logAgreement : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1 →
    SigningPartnerCompareProof.LogAgreement x.1 a'.1.1.1.1.1
  trace : a'.1.1.2 = a.1.1.2
  signing : b'.1.signing = b.1.signing
  trees : b'.1.trees = b.1.trees
  exposed : b'.1.exposed = b.1.exposed
  candidates : b'.1.candidates = b.1.candidates
  revealed : ∀ k, b.1.revealed k ≠ none → b'.1.revealed k = b.1.revealed k
  opened : ∀ k, b.1.revealed k = none → b'.1.revealed k ≠ none →
    ∃ e, k = .opening bottomLayer e ∧ b.1.signing.bound e ≠ none
  pending : ∀ p, (dataOf x b.2).pending p ≠ none → (dataOf x b'.2).pending p ≠ none
  virtual : ∀ T p, (T, p) ∈ (dataOf x b.2).virtual → (T, p) ∈ (dataOf x b'.2).virtual

section Frame
variable (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)

/-- The input of a pending point names the point. The premise on pending inputs of
`ExtraOpen.frame` reads it at a chain call, a commitment call and a top base call. -/
theorem pendingInput_injective (P : PublicParameter) (p p' : PendingInput) (v v' : Digest)
    (h : p.input P v = p'.input P v') : p = p' := by
  have hk := congrArg (SigningOpeningProof.hiddenCandidate P) h
  rw [PendingInput.hiddenCandidate, PendingInput.hiddenCandidate] at hk
  have hkey : p.key = p'.key := congrArg Prod.fst (Option.some.inj hk)
  cases p <;> cases p' <;> simp only [PendingInput.key, HiddenKey.opening.injEq,
    HiddenKey.bottomChain.injEq, HiddenKey.topChain.injEq, reduceCtorEq] at hkey <;>
    simp only [PendingInput.input] at h <;> simp only [PendingInput.commitment.injEq,
      PendingInput.base.injEq, PendingInput.bottom.injEq, PendingInput.top.injEq, reduceCtorEq]
  case commitment.commitment => exact hkey.2
  case commitment.base => exact SigningGuessProof.commitmentInput_ne_randomizerInput _ _ _ _ _ _ _ h
  case base.commitment =>
    exact SigningGuessProof.commitmentInput_ne_randomizerInput _ _ _ _ _ _ _ h.symm
  case base.base => exact ⟨hkey.1, hkey.2, (SigningGuessProof.randomizerInput_payload_eq P h).2⟩
  case bottom.bottom => exact hkey
  case top.top => exact hkey

/-- No call keeps both states. -/
theorem CallFrame.refl (a : RealState C) (b : SourceState C × CompState C) :
    CallFrame x (fun _ => False) a a b b :=
  ⟨rfl, le_rfl, fun _ h => Or.inl h, le_rfl, fun h => h, rfl, rfl, rfl, rfl, rfl,
    fun _ _ => rfl, fun _ h h' => (h' h).elim, fun _ h => h, fun _ _ h => h⟩

/-- Two frames compose. -/
theorem CallFrame.trans (seen seen' : Query C → Prop) (a a' a'' : RealState C)
    (b b' b'' : SourceState C × CompState C)
    (h : CallFrame x seen a a' b b') (h' : CallFrame x seen' a' a'' b' b'') :
    CallFrame x (fun query => seen query ∨ seen' query) a a'' b b'' where
  carried := h'.carried.trans h.carried
  visible := le_trans h.visible h'.visible
  fresh query hq := (h'.fresh query hq).elim (fun h1 => (h.fresh query h1).imp_right Or.inl)
    (fun hs => Or.inr (Or.inr hs))
  log := le_trans h.log h'.log
  logAgreement hl := h'.logAgreement (h.logAgreement hl)
  trace := h'.trace.trans h.trace
  signing := h'.signing.trans h.signing
  trees := h'.trees.trans h.trees
  exposed := h'.exposed.trans h.exposed
  candidates := h'.candidates.trans h.candidates
  revealed k hk := (h'.revealed k (by rw [h.revealed k hk]; exact hk)).trans (h.revealed k hk)
  opened k hk hk'' := by
    by_cases hm : b'.1.revealed k = none
    · obtain ⟨e, he, hb⟩ := h'.opened k hm hk''
      exact ⟨e, he, h.signing ▸ hb⟩
    · exact h.opened k hk hm
  pending p hp := h'.pending p (h.pending p hp)
  virtual T p hp := h'.virtual T p (h.virtual T p hp)

/-- A larger set of seen queries keeps the frame. -/
theorem CallFrame.weaken (seen seen' : Query C → Prop) (a a' : RealState C)
    (b b' : SourceState C × CompState C) (h : CallFrame x seen a a' b b')
    (hsub : ∀ query, seen query → seen' query) : CallFrame x seen' a a' b b' :=
  { h with fresh := fun query hq => (h.fresh query hq).imp_right (hsub query) }

/-- A top digest input that a log cache holds decodes the same in a larger cache. -/
theorem topDigit_mono {L L' : HashCache C} (hle : L ≤ L') (P : PublicParameter)
    (bi : XmssSecurity.TopIndex) (input : Digest × XmssSecurity.Randomness)
    (encoding : XmssSecurity.Encoding)
    (h : (SigningDescentProof.thView L
        (XmssSecurity.Concrete.CacheView.topEncodingInput P bi input)).isSome ∧
      XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.topEncodingHash
        (SigningDescentProof.thView L) P bi input) = some encoding) :
    (SigningDescentProof.thView L'
        (XmssSecurity.Concrete.CacheView.topEncodingInput P bi input)).isSome ∧
      XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.topEncodingHash
        (SigningDescentProof.thView L') P bi input) = some encoding := by
  obtain ⟨hsome, hdec⟩ := h
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hsome
  have hw' := SigningCacheProof.thView_mono hle hw
  refine ⟨by rw [hw']; rfl, ?_⟩
  rw [← hdec]
  simp only [XmssSecurity.Concrete.CacheView.topEncodingHash,
    XmssSecurity.Concrete.CacheView.digestAt, hw, hw']

/-- The clauses pass over a frame. No seen query is a bottom base input, an input of a pending point
with an unrevealed key and no answer. A seen PRF point is constrained, or its term is revealed. A
seen bottom chain point has a revealed term, an open row or its row of pending answers. The reveal
map `rev'` holds `rev`, and each new key of it is the opening of a bound bottom key. -/
theorem ExtraOpen.frame (seen : Query C → Prop) (openRow openRow' : KeyIndex → ChainIndex → Prop)
    (rev rev' : HiddenKey → Option Digest)
    (cTime : Carried C) (a a' : RealState C) (b b' : SourceStateO1 C × CompState C)
    (hx : ExtraOpen prims x top s rev openRow (withCarried a cTime) b)
    (hf : CallFrame x seen a a' (b.1.base, b.2) (b'.1.base, b'.2))
    (hstarts : b'.1.starts = b.1.starts)
    (hrev : ∀ k, rev k ≠ none → rev' k ≠ none)
    (hnew : ∀ k, rev' k ≠ none → rev k ≠ none ∨
      ∃ e, k = .opening bottomLayer e ∧ cTime.1.1.bound e ≠ none)
    (hbase : ∀ e ρ message, ¬seen (.hash (randomizerInput x.1 bottomLayer e ρ message)))
    (hguess : ∀ p : PendingInput, b'.1.base.revealed p.key = none →
      (dataOf x b'.2).pending p = none → ¬seen (.hash (p.input x.1 (s p.key))))
    (hprf : ∀ T p, seen (.prf (x.2.1 T) p) →
      TprfSecurityProof.Revealed cTime.1.1.corrupt (.inl T) ∨ Constrained p)
    (hrow : ∀ T e l (d : XmssSecurity.ChainStep),
      seen (.prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) →
        TprfSecurityProof.Revealed cTime.1.1.corrupt (.inl T) ∨ openRow' e l ∨
          ∀ d' : XmssSecurity.ChainStep, (dataOf x b'.2).pending (.bottom e l d') ≠ none)
    (hopen : ∀ e l, openRow e l → openRow' e l) :
    ExtraOpen prims x top s rev' openRow' (withCarried a' cTime) b' := by
  have hr := hx.rest
  have htrees : b'.1.base.trees = b.1.base.trees := hf.trees
  have hsig : b'.1.base.signing = b.1.base.signing := hf.signing
  have hcand : b'.1.base.candidates = b.1.base.candidates := hf.candidates
  have hlog : realLog a ≤ realLog a' := hf.log
  have htrace : a'.1.1.2 = a.1.1.2 := hf.trace
  have hrevealed : ∀ k, b'.1.base.revealed k = none → b.1.base.revealed k = none := by
    intro k hk
    by_contra hne
    have he : b'.1.base.revealed k = b.1.base.revealed k := hf.revealed k hne
    exact hne (he ▸ hk)
  have hpend : ∀ p, (dataOf x b'.2).pending p = none → (dataOf x b.2).pending p = none :=
    fun p hp => by_contra fun hne => hf.pending p hne hp
  have hvirt : ∀ T p, (T, p) ∈ (dataOf x b.2).virtual → (T, p) ∈ (dataOf x b'.2).virtual :=
    hf.virtual
  have hvis : ∀ query, visibleOf a' query ≠ none → ¬seen query → visibleOf a query ≠ none :=
    fun query hq hs => (hf.fresh query hq).resolve_right hs
  refine ⟨?_, ?_, ?_⟩
  · exact
      { treeRows := fun bi hbi k l d => by
          have hrows := hr.treeRows bi (htrees ▸ hbi) k l d
          exact ⟨fun T => hvirt _ _ (hrows.1 T), hf.pending _ hrows.2⟩
        storedTrees := fun bi => by
          rw [htrees]
          exact hr.storedTrees bi
        storedTopDigit := fun bi tree ht =>
          topDigit_mono hlog x.1 bi _ _ (hr.storedTopDigit bi tree (htrees ▸ ht))
        startsTreed := fun e l h => by
          rw [htrees]
          exact hr.startsTreed e l (hstarts ▸ h)
        boundTreeRevealed := fun e hb ht => by
          have h0 := hr.boundTreeRevealed e (hsig ▸ hb) (htrees ▸ ht)
          have he : b'.1.base.revealed (.opening bottomLayer e) =
            b.1.base.revealed (.opening bottomLayer e) := hf.revealed _ h0
          rw [he]
          exact h0
        revealedReleased := fun lay e h => by
          rcases hnew _ h with h0 | ⟨e', he, hb⟩
          · exact hr.revealedReleased lay e h0
          · injection he with hl he
            subst hl he
            exact Or.inl ⟨rfl, hb⟩
        revealedCovered := fun e l p h => by
          rcases hnew _ h with h0 | ⟨e', he, _⟩
          · rw [hstarts]
            exact hr.revealedCovered e l p h0
          · cases he
        revealedTop := fun bi l p h => by
          rcases hnew _ h with h0 | ⟨e', he, _⟩
          · rw [htrees]
            exact hr.revealedTop bi l p h0
          · cases he
        candidatesPaid := fun c hc hs => hrev _ (hr.candidatesPaid c (hcand ▸ hc) hs)
        openingFresh := fun c hc => hr.openingFresh c (hcand ▸ hc)
        staleFree := by
          change a'.1.1.2.2 = false
          rw [htrace]
          exact hr.staleFree
        noEarlyGuess := fun e message hk => by
          have h0 := hr.noEarlyGuess e message (hrevealed _ hk)
          by_contra hne
          exact hvis _ hne (hbase _ _ _) h0
        guessFree := fun p hk hp => by
          have h0 := hr.guessFree p (hrevealed _ hk) (hpend _ hp)
          by_contra hne
          exact hvis _ hne (hguess p hk hp) h0
        treeTerms := fun bi hbi => by
          obtain ⟨h1, h2⟩ := hr.treeTerms bi (htrees ▸ hbi)
          exact ⟨fun k T => hvirt _ _ (h1 k T), fun T => hvirt _ _ (h2 T)⟩
        treeStarts := fun bi tree ht T l => hvirt _ _ (hr.treeStarts bi tree (htrees ▸ ht) T l)
        treeValues := fun bi tree ht => hr.treeValues bi tree (htrees ▸ ht)
        baseTraced := fun e message hb hv => by
          change e ∈ a'.1.1.2.1.leafIndices
          rw [htrace]
          exact hr.baseTraced e message hb (hvis _ hv (hbase _ _ _))
        logAgreement := hf.logAgreement hr.logAgreement
        storedRuns := SigningGuessProof.StoredTreeRuns.mono prims x top hlog hr.storedRuns
        startsTraced := fun e l d hd => by
          obtain ⟨receipt, h1, h2, h3, h4⟩ := hr.startsTraced e l d (hstarts ▸ hd)
          exact ⟨receipt, h1, h2, h3, SigningGuessProof.ReceiptRuns.mono prims x top hlog receipt h4⟩
        corruptBound := hr.corruptBound
        releasedBound := hr.releasedBound
        prfSeen := fun hfl => by cases hfl
        bottomSeen := fun hfl => by cases hfl }
  · intro hfl T p hv
    rcases hf.fresh _ hv with h0 | hs
    · exact hx.prfSeen hfl T p h0
    · exact hprf T p hs
  · intro hfl T e l d ho hv
    rcases hf.fresh _ hv with h0 | hs
    · rcases hx.bottomSeen hfl T e l d (fun h => ho (hopen e l h)) h0 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr fun d' => hf.pending _ (h1 d')
    · rcases hrow T e l d hs with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd h1 ho
      · exact Or.inr h1

/-- The top clauses pass over a frame. -/
theorem TopO1.frame (seen : Query C → Prop) (a a' : RealState C)
    (b b' : SourceStateO1 C × CompState C) (ht : TopO1 prims x top a b)
    (hf : CallFrame x seen a a' (b.1.base, b.2) (b'.1.base, b'.2)) :
    TopO1 prims x top a' b' := by
  obtain ⟨start, result, hs, ho, hc⟩ := ht.topRun
  exact ⟨fun bi l d => hf.pending _ (ht.topRows bi l d), start, result, hs, ho, hc.trans hf.log⟩

/-- New candidates keep the clauses. A new candidate that carries its secret has a revealed key, and
no new opening candidate carries its secret. The local step and the verification use it. -/
theorem ExtraOpen.candidates (openRow : KeyIndex → ChainIndex → Prop)
    (rev : HiddenKey → Option Digest) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (new : List (HiddenKey × Digest))
    (hx : ExtraOpen prims x top s rev openRow a b)
    (hpaid : ∀ c ∈ new, c.2 = s c.1 → rev c.1 ≠ none)
    (hfresh : ∀ c ∈ new, ∀ lay e, c.1 = .opening lay e → c.2 ≠ s c.1) :
    ExtraOpen prims x top s rev openRow (withCandidates a (a.1.2.2.2 ++ new))
      (⟨{ b.1.base with candidates := b.1.base.candidates ++ new }, b.1.starts⟩, b.2) := by
  refine ⟨{ hx.rest with candidatesPaid := ?_, openingFresh := ?_ }, hx.prfSeen, hx.bottomSeen⟩
  · intro c hc hs
    rcases List.mem_append.1 hc with hc | hc
    · exact hx.rest.candidatesPaid c hc hs
    · exact hpaid c hc hs
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hx.rest.openingFresh c hc
    · exact hfresh c hc

/-- More exposed trees in the timing view keep the clauses. A tree request names its tree when it
returns, and its release reads the name before. -/
theorem ExtraOpen.expose (openRow : KeyIndex → ChainIndex → Prop)
    (rev : HiddenKey → Option Digest) (cTime : Carried C) (trees : Finset (Fin (2 ^ layerHeight)))
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hx : ExtraOpen prims x top s rev openRow (withCarried a cTime) b)
    (hsub : cTime.2.1 ⊆ trees) :
    ExtraOpen prims x top s rev openRow (withCarried a (cTime.1, trees, cTime.2.2)) b := by
  refine ⟨{ hx.rest with revealedReleased := ?_, revealedTop := ?_ }, hx.prfSeen, hx.bottomSeen⟩
  · intro lay e h
    rcases hx.rest.revealedReleased lay e h with h0 | ⟨hl, bi, hb, he⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hl, bi, hsub hb, he⟩
  · intro bi l p h
    obtain ⟨hb, hrest⟩ := hx.rest.revealedTop bi l p h
    exact ⟨hsub hb, hrest⟩

end Frame

/-! ## The step contract with the fixed pads -/

section Step
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The real world calls over the fixed tables. -/
abbrev realWorld : QueryImpl (WorldSpec C) (StateT (RealState C) ProbComp) :=
  SigningCompilerUntil.fuse (rawTraceWorld prims x) (realImpl x (gOf s pads u) rest)

/-- One honest call of `H` in the real world. -/
abbrev realCall (input : Query C) : StateT (RealState C) ProbComp HashOutput :=
  realWorld prims x s pads u rest (.inr (.inr (.inl input)))

/-- The run of an honest computation in the real world. -/
abbrev realHonest {α : Type} (oa : OracleComp (RoSpec C) α) : StateT (RealState C) ProbComp α :=
  simulateQ (realWorld prims x s pads u rest) (SigningSecurityProof.liftFree oa)

/-- A read of `H` or of the PRG in the real world, on the copy of the forger or on the free copy
of the honest operators. -/
def readCall (forger : Bool) (rq : (RoSpec C).Domain) :
    StateT (RealState C) ProbComp ((RoSpec C).Range rq) :=
  if forger then realWorld prims x s pads u rest (.inl (.inl (.inr rq)))
  else realWorld prims x s pads u rest (.inr (.inr rq))

/-- The post of coupled calls from the real state `a` and the compiler state `(src, st)`. `value`
relates the two answers and `seen` holds the queries of the calls. -/
def CallPost (cCore : Carried C) (seen : Query C → Prop) (a : RealState C) (src : SourceState C)
    (st : CompState C) {α β : Type} (value : α → β → Prop) (ra : α × RealState C)
    (rb : (β × SourceState C) × CompState C) : Prop :=
  RealStop q ra.2 ∨ Stop rb.2 ∨
    (value ra.1 rb.1.1 ∧
      SyncCore x s pads noise (gOf s pads u) rest (withCarried ra.2 cCore) (rb.1.2, rb.2) ∧
      CallFrame x seen a ra.2 (src, st) (rb.1.2, rb.2) ∧ rb.2.1.2 = false)

-- Port of TreeSim.treeSim_relTriple_support, as in `SigningCompilerSyncLocalRead`.
private theorem relTriple_supported {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun a b => R a b ∧ a ∈ support oa ∧ b ∈ support ob) := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ⟨hc z hz, ?_, ?_⟩⟩
  · have hp : z.1 ∈ support (Prod.fst <$> c.1) := by
      rw [support_map]; exact ⟨z, hz, rfl⟩
    rw [c.2.map_fst] at hp
    exact (mem_support_evalDist_iff _ _).1 hp
  · have hp : z.2 ∈ support (Prod.snd <$> c.1) := by
      rw [support_map]; exact ⟨z, hz, rfl⟩
    rw [c.2.map_snd] at hp
    exact (mem_support_evalDist_iff _ _).1 hp

/-- The contract of one oracle call of the forger for the boundary relation with the fixed pads. -/
def StepO1' (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) : Prop :=
  ∀ (a : RealState C) (b : SourceStateO1 C × CompState C),
    SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2 →
    ¬RealStop q a → ¬Stop b.2 →
    RelTriple ((realOracles prims x s pads u rest top t).run a)
      ((compOracles prims x q s pads u rest noise top t).run b)
      (Until (RealStop q) CompStop (fun a b =>
        SyncO1 prims x top s pads noise (gOf s pads u) rest a b ∧ PadsFixed x pads b.2))

/-- A step contract for the boundary relation gives the contract with the fixed pads. The
corruption step takes it. -/
theorem step_pads (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain)
    (h : StepO1 prims x q s pads u rest noise top t) :
    StepO1' prims x q s pads u rest noise top t := by
  intro a b hs ha hb
  refine relTriple_post_mono (relTriple_supported (h a b hs.1 ha hb)) ?_
  rintro ra rb ⟨hu, -, hrb⟩
  rcases hu with h1 | h1 | ⟨heq, hsync⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨heq, hsync, ?_⟩)
    simp only [SigningCompilerUntil.fuse, StateT.run, support_map, Set.mem_image] at hrb
    obtain ⟨z, hz, rfl⟩ := hrb
    exact backend_padsFixed x q s pads u rest noise _ b.2 hs.2 z hz

end Step

end ThresholdLeanXmssSecurity.SigningCompilerO1Frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.withCarried_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.withCarried_self

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.withSigning_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.withSigning_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.withCandidates_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.withCandidates_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.extraOpen_of_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.extraOpen_of_extra

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.extra_of_extraOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.extra_of_extraOpen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.hashTail_pads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.hashTail_pads

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ordinary_padsFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ordinary_padsFixed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.freshRestT_padsFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.freshRestT_padsFixed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ordinaryT_padsFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ordinaryT_padsFixed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.backendT_padsFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.backendT_padsFixed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.backend_padsFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.backend_padsFixed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.syncO1_iff_syncIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.syncO1_iff_syncIn

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.syncIn_of_syncMid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.syncIn_of_syncMid

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.syncMid_of_syncIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.syncMid_of_syncIn

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.pendingInput_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.pendingInput_injective

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.CallFrame.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.CallFrame.refl

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.CallFrame.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.CallFrame.trans

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.CallFrame.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.CallFrame.weaken

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.topDigit_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.topDigit_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.TopO1.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.TopO1.frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.candidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.candidates

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.expose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.ExtraOpen.expose

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Frame.step_pads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Frame.step_pads
