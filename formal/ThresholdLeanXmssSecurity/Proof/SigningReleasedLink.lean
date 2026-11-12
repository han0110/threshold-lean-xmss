import ThresholdLeanXmssSecurity.Proof.SigningLinkPaid
import ThresholdLeanXmssSecurity.Proof.SigningPartnerCompare

/-!
# Releases in the monitored signing execution

A query occurrence retains its actual state, response and continuation in one supported
execution. The release ledger changes only at a successful round-two response. Selection
alignment and signed-cache separation imply the released-partner link: the replayed selection
provides a valid digest, so both sides of the partner equality are cached.
-/

open OracleComp OracleSpec

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningReleasedLinkProof

open LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof
  SigningJointEagerProof SigningPartnerBoundProof SigningOneRunProof

attribute [local instance] Classical.propDecidable

section Occurrence

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- One query in a supported execution, retaining the original continuation and final result. -/
inductive QueryOccurrence (V : QueryImpl spec (StateT σ ProbComp))
    (t : spec.Domain) (before : σ) (after : spec.Range t × σ) :
    OracleComp spec α → σ → α × σ → Prop
  | here (next : spec.Range t → OracleComp spec α) (result : α × σ)
      (head : after ∈ support ((V t).run before))
      (tail : result ∈ support ((simulateQ V (next after.1)).run after.2)) :
      QueryOccurrence V t before after (query t >>= next) before result
  | later (q : spec.Domain) (next : spec.Range q → OracleComp spec α)
      (initial : σ) (middle : spec.Range q × σ) (result : α × σ)
      (head : middle ∈ support ((V q).run initial))
      (tail : QueryOccurrence V t before after (next middle.1) middle.2 result) :
      QueryOccurrence V t before after (query q >>= next) initial result

theorem QueryOccurrence.head_support
    {V : QueryImpl spec (StateT σ ProbComp)} {t : spec.Domain}
    {before : σ} {after : spec.Range t × σ} {source : OracleComp spec α}
    {initial : σ} {result : α × σ}
    (h : QueryOccurrence V t before after source initial result) :
    after ∈ support ((V t).run before) := by
  induction h with
  | here _ _ head _ => exact head
  | later _ _ _ _ _ _ _ ih => exact ih

/-- The first failure of a state predicate is an actual query of the same execution. -/
theorem first_failure (V : QueryImpl spec (StateT σ ProbComp)) (P : σ → Prop)
    (source : OracleComp spec α) (initial : σ) (hinitial : P initial)
    (result : α × σ) (hr : result ∈ support ((simulateQ V source).run initial))
    (hresult : ¬P result.2) :
    ∃ t before after, QueryOccurrence V t before after source initial result ∧
      P before ∧ ¬P after.2 := by
  induction source using OracleComp.inductionOn generalizing initial with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    exact (hresult (hr ▸ hinitial)).elim
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨middle, hhead, htail⟩ := hr
    by_cases hm : P middle.2
    · obtain ⟨q, before, after, hvisit, hp, hn⟩ := ih middle.1 middle.2 hm htail
      exact ⟨q, before, after,
        .later t next initial middle result hhead hvisit, hp, hn⟩
    · exact ⟨t, initial, middle, .here next result hhead htail, hinitial, hm⟩

end Occurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {C : Committee} (prims : Primitives)

abbrev SplitState (C : Committee) :=
  ((SigningHitLaneProof.LoggedState C × Monitor) × (XmssSecurity.LeafIndex → Bool)) × OpeningState C

abbrev world (x : SigningSecurityProof.Keys3 C) :=
  keyedSplitWorld prims (XmssSecurity.encodingInputLeafIndex? x.1) (jointCachedExtra x.2.1 x.1)

abbrev forger (x : SigningSecurityProof.Keys3 C) (top : TopTree) :=
  flatWith (SigningOpeningProof.openingOracles x (dealtOf x top)) (world prims x)

/-- Projection to the source handler retains its actual response and signing state. -/
theorem forger_source (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : SplitState C)
    (r : (LocalSpec C + TsigSpec C).Range t × SplitState C)
    (hr : r ∈ support ((forger prims x top t).run s)) :
    (r.1, r.2.2.1.1) ∈ support
      ((SigningCoreProof.gameOracles (dealtOf x top) t).run s.2.1.1) := by
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  have hs : w.1 ∈ support
      ((SigningOpeningProof.openingOracles x (dealtOf x top) t).run s.2) := by
    apply support_simulateQ_run'_subset (world prims x) _ s
    rw [StateT.run'_eq, support_map]
    exact ⟨w, hw, rfl⟩
  rw [← SigningCoreProof.flaggedOracles_forget x _ t s.2.1.1 s.2.1.2,
    ← SigningOpeningProof.openingOracles_forget x _ t s.2.1 s.2.2,
    Functor.map_map, support_map]
  exact ⟨w.1, hs, rfl⟩

theorem forger_corrupt_le (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : SplitState C) (hs : s.2.1.1.corrupt.card ≤ C.t - 1) r
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s)) :
    r.2.2.1.1.corrupt.card ≤ C.t - 1 := by
  exact SeedHitProof.support_simulateQ_inv _ (fun p : SplitState C =>
    p.2.1.1.corrupt.card ≤ C.t - 1)
    (fun t p hp r hr => SigningGuessProof.gameOracles_corrupt_le _ t _ _ hp
      (forger_source prims x top t p r hr)) source s hs r hr

theorem forger_releaseStep (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : SplitState C) r
    (hr : r ∈ support ((forger prims x top t).run s)) :
    r.2.2.1.1.released = SigningGuessProof.releaseStep s.2.1.1.released t r.1 := by
  have h := forger_source prims x top t s r hr
  cases t with
  | inl t =>
    change (r.1, r.2.2.1.1) ∈ support ((fun a => (a, s.2.1.1)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at h
    obtain ⟨_, _, heq⟩ := (by simpa only [support_map, Set.mem_image] using h)
    exact congrArg (fun p => p.2.released) heq.symm
  | inr t => exact SigningGuessProof.tsigOracles_releaseStep _ _ t _ _ h

/-- A newly present release has a successful round-two occurrence in the original execution. -/
theorem forger_release_occurrence (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : SplitState C) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s))
    (e : KeyIndex) (message : Message) (i : C.Party)
    (hs : (e, message, i) ∉ s.2.1.1.released)
    (hout : (e, message, i) ∈ r.2.2.1.1.released) :
    ∃ (J : C.Quorum) (parts : C.Party → Digest) (values : ChainIndex → Option Digest)
      (before after : SplitState C),
      QueryOccurrence (forger prims x top) (.inr (.round2 i J e message parts))
        before (some values, after) source s r := by
  obtain ⟨t, before, after, hv, hb, ha⟩ := first_failure (forger prims x top)
    (fun p : SplitState C => (e, message, i) ∉ p.2.1.1.released) source s hs r hr
      (by simpa using hout)
  have hstep := forger_releaseStep prims x top t before after hv.head_support
  rw [hstep] at ha
  simp only [not_not] at ha
  rcases t with t | t
  · exact (hb ha).elim
  cases t with
  | round2 j J f m parts =>
    rcases after with ⟨_ | values, after⟩
    · exact (hb ha).elim
    simp only [SigningGuessProof.releaseStep, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at ha
    rcases ha with hold | ⟨rfl, rfl, rfl⟩
    · exact (hb hold).elim
    exact ⟨J, parts, values, before, after, hv⟩
  | _ => exact (hb ha).elim


set_option linter.constructorNameAsVariable false in
/-- The monitored world carries the signing state unchanged through every hash call. -/
theorem world_carried (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain)
    (s : SplitState C) (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((world prims x t).run s)) : r.2.2 = s.2 := by
  simp only [world, keyedSplitWorld, carry, StateT.run_mk, bind_map_left,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, y, hy, rfl⟩ := hr
  rfl

theorem world_run_carried (x : SigningSecurityProof.Keys3 C) {α : Type}
    (source : OracleComp (WorldSpec C) α) (s : SplitState C) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (world prims x) source).run s)) : r.2.2 = s.2 := by
  exact SeedHitProof.support_simulateQ_inv _ (fun p : SplitState C => p.2 = s.2)
    (fun t p hp r hr => (world_carried prims x t p r hr).trans hp) source s rfl r hr

/-- The exact top-tree, adversary and verification subruns of the split execution. -/
theorem splitRun_subruns (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : SplitOutcome C) (hz : z ∈ support (splitRunAt prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hmeta : z.1.1.2 = some (top, state, forgery)) :
    ∃ (start : SplitState C) (middle : Forgery × SplitState C),
      start.2 = ((SigningCoreProof.tsigInit, false), ∅, []) ∧
      middle ∈ support ((simulateQ (forger prims x top)
        (A ⟨top.root, x.1⟩ top)).run start) ∧
      middle.1 = forgery ∧ middle.2.2.1.1 = state ∧
      ∃ finished, finished ∈ support ((simulateQ (world prims x)
        (SigningGuessLinkProof.tsigFinishLogged (dealtOf x top) middle.2.2.2.1
          (middle.1, middle.2.2.1.1))).run middle.2) ∧ finished.2 = z.2 := by
  unfold splitRunAt SigningOneRunProof.splitGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hs := world_run_carried prims x _ _ setup hsetup
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hmeta
    contradiction
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz] at hmeta
      contradiction
    | top actualTop =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      have hf := SigningSelectionProof.tsigFinishLogged_state (dealtOf x actualTop)
        middle.2.2.2.1 middle.1 middle.2.2.1.1 finished.1
        (by
          apply support_simulateQ_run'_subset (world prims x) _ middle.2
          rw [StateT.run'_eq, support_map]
          exact ⟨finished, hfinished, rfl⟩)
      rw [hz] at hmeta
      have ht : actualTop = top := congrArg Prod.fst (Option.some.inj hmeta)
      subst actualTop
      have he : (middle.2.2.1.1, middle.1) = (state, forgery) := by
        rw [← hf]
        exact congrArg Prod.snd (Option.some.inj hmeta)
      refine ⟨setup.2, middle, hs, hmiddle, congrArg Prod.snd he, congrArg Prod.fst he,
        finished, hfinished, ?_⟩
      rw [hz]

/-- The cache-dependent trigger runs the actual grind at a canonical base call. -/
theorem jointCachedExtra_base (x : SigningSecurityProof.Keys3 C)
    (p p' : FlatJointState C) (t : (WorldSpec C).Domain) (e : KeyIndex)
    (message : Message) (answer : HashOutput)
    (hcache : SigningGuessProof.RandomizerCached x.2.1 p.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 p.1.1.1 e) p.2.1.1 t)
    (hbound : p.2.1.1.bound e = some message)
    (hanswer : p'.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 p.1.1.1 e) (bytesLE 32 message))) = some answer) :
    jointCachedExtra x.2.1 x.1 p t p' = baseGrind x.1 e message answer := by
  unfold jointCachedExtra SigningR1FixedProof.cachedExtra
  rw [if_pos ⟨e, hcache, hbase⟩]
  unfold grindExtra
  have hb : ∃ f, BaseCall x.1 f (SigningGuessProof.cachedRandomizer x.2.1 p.1.1.1 f) p.2.1.1 t :=
    ⟨e, hbase⟩
  rw [dif_pos hb]
  have he : hb.choose = e := SigningR1FixedProof.baseCall_key_eq hb.choose_spec hbase
  simp only [he, hbound]
  rw [he, hanswer]

set_option linter.constructorNameAsVariable false in
/-- At a cached canonical base call, the split world contains the monitored grind subrun.
The subrun includes the real per-key cached-selection flags. -/
theorem world_base_subrun (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain)
    (s : SplitState C) (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((world prims x t).run s)) (e : KeyIndex) (message : Message)
    (hcache : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hbound : s.2.1.1.bound e = some message) :
    ∃ (called : (WorldSpec C).Range t × FlatJointState C) (answer : HashOutput)
      (ground : Unit × ((HashCache C × Monitor) × (XmssSecurity.LeafIndex → Bool))),
      called ∈ support ((carry (SigningCostProof.loggedImpl prims) t).run (s.1.1.1, s.2)) ∧
      called.2.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message))) = some answer ∧
      ground ∈ support ((simulateQ (keyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
        (baseGrind x.1 e message answer)).run
          ((called.2.1.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
            s.1.1.2 (hashEntry ⟨t, called.1⟩)), s.1.2)) ∧
      r.1 = called.1 ∧ r.2.1.1.2 = ground.2.1.2 ∧ r.2.1.2 = ground.2.2 := by
  simp only [world, keyedSplitWorld, StateT.run_mk, mem_support_bind_iff,
    support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  have hcall : HashCallAt (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message)) t := by
    obtain ⟨input, hi, ht⟩ := hbase
    have he : randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message) = input := by
      unfold baseInput at hi
      rw [hbound] at hi
      exact Option.some.inj hi
    exact he.symm ▸ ht
  have hc' := hc
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc'
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc'
  obtain ⟨answer, ha⟩ := countImpl_hash_cached prims _ t hcall _ counted hcounted
  have hanswer : called.2.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (bytesLE 32 message))) = some answer := by
    rw [← heq]
    exact ha
  rw [jointCachedExtra_base x (s.1.1.1, s.2) called.2 t e message answer hcache hbase hbound hanswer] at hg
  exact ⟨called, answer, ground, hc, hanswer, hg, rfl, rfl, rfl⟩

/-- A threshold of signers contains a recorded honest release, since corruption stops below it. -/
theorem signers_release (state : TsigState C) (hc : state.corrupt.card ≤ C.t - 1)
    (e : KeyIndex) (message : Message) (ht : C.t ≤ (signersAt state e message).card) :
    ∃ i, (e, message, i) ∈ state.released := by
  have hhonest : (((state.released.filter fun r => r.1 = e ∧ r.2.1 = message).map
      (·.2.2)).toFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    unfold signersAt at ht
    rw [hempty, Finset.union_empty] at ht
    have := C.one_le_t
    omega
  obtain ⟨i, hi⟩ := hhonest
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨⟨key, msg, party⟩, ⟨ha, rfl, rfl⟩, -⟩ := hi
  exact ⟨party, ha⟩

/-- A release at the forged key occurs in the actual adversary subrun of this split execution. -/
theorem splitRun_release_occurrence (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : SplitOutcome C) (hz : z ∈ support (splitRunAt prims A x))
    (hrel : SigningLinkPaidProof.ReleasedAt z.1.1.2) :
    ∃ (top : TopTree) (state : TsigState C) (forgery : Forgery) (message : Message)
      (start : SplitState C) (middle : Forgery × SplitState C)
      (i : C.Party) (J : C.Quorum) (parts : C.Party → Digest)
      (values : ChainIndex → Option Digest) (before after : SplitState C),
      z.1.1.2 = some (top, state, forgery) ∧
      state.bound forgery.signature.leafIndex = some message ∧
      middle.1 = forgery ∧ middle.2.2.1.1 = state ∧
      (forgery.signature.leafIndex, message, i) ∈ state.released ∧
      QueryOccurrence (forger prims x top)
        (.inr (.round2 i J forgery.signature.leafIndex message parts)) before (some values, after)
        (A ⟨top.root, x.1⟩ top) start middle ∧
      ∃ finished, finished ∈ support ((simulateQ (world prims x)
        (SigningGuessLinkProof.tsigFinishLogged (dealtOf x top) middle.2.2.2.1
          (middle.1, middle.2.2.1.1))).run middle.2) ∧ finished.2 = z.2 := by
  obtain ⟨top, state, forgery, hm, message, hb, ht⟩ := hrel
  obtain ⟨start, middle, hs, hmiddle, hf, hstate, finish⟩ :=
    splitRun_subruns prims A x z hz top state forgery hm
  have hc : middle.2.2.1.1.corrupt.card ≤ C.t - 1 :=
    forger_corrupt_le prims x top _ start (by simp [hs, SigningCoreProof.tsigInit]) _ hmiddle
  rw [hstate] at hc
  obtain ⟨i, hi⟩ := signers_release state hc _ message ht
  obtain ⟨J, parts, values, before, after, hv⟩ :=
    forger_release_occurrence prims x top _ start middle hmiddle forgery.signature.leafIndex
      message i (by simp [hs, SigningCoreProof.tsigInit]) (hstate ▸ hi)
  exact ⟨top, state, forgery, message, start, middle, i, J, parts, values, before, after,
    hm, hb, hf, hstate, hi, hv, finish⟩

/-- At a released key, the replayed selection is the monitor target unless the cached-trial
flag or a commitment collision accounts for it. This is an alignment statement, independent of
any forgery digest equality. -/
def ReleasedSelectionAlignment : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C),
    z ∈ support (splitRunAt prims A x) →
    ∀ top state forgery, z.1.1.2 = some (top, state, forgery) →
    ∀ (keyForgery : Forgery) message i, (keyForgery.signature.leafIndex, message, i) ∈ state.released →
    ∀ selected, (SigningDescentProof.FinalState.mk x top state keyForgery
      z.2.1.1.1.1.1 false).selected prims = some selected →
    z.2.1.2 keyForgery.signature.leafIndex = true ∨
      SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 ∨
      z.2.1.1.2.state.signed keyForgery.signature.leafIndex = some
        (XmssSecurity.Concrete.CacheView.encodingHash
          (SigningDescentProof.thView z.2.1.1.1.1.1) x.1 keyForgery.signature.leafIndex selected)

/-- A signed monitor digest cannot have two distinct cached preimages at its key without a hit.
This concerns every key and cached hash input of the actual split run. -/
def SignedCacheSeparation : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C),
    z ∈ support (splitRunAt prims A x) →
    ∀ e digest, z.2.1.1.2.state.signed e = some digest →
    ∀ left right : XmssSecurity.HashInput, left ≠ right →
    XmssSecurity.encodingInputLeafIndex? x.1 left = some e →
    XmssSecurity.encodingInputLeafIndex? x.1 right = some e →
    ∀ a b, z.2.1.1.1.1.1 (.hash left) = some a →
    z.2.1.1.1.1.1 (.hash right) = some b →
    XmssSecurity.truncateHash a = digest → XmssSecurity.truncateHash b = digest →
    z.2.1.1.2.hit = true

/-- Selection alignment and signed-cache separation imply the original released-partner link. -/
theorem releasedLink_of_alignment_separation
    (halign : ReleasedSelectionAlignment prims (C := C))
    (hsep : SignedCacheSeparation prims (C := C)) :
    SigningLinkPaidProof.ReleasedLink prims (C := C) := by
  intro A x z hz _hwin hpartner hrel hnflag
  obtain ⟨top, state, forgery, hm, selected, hsel, hne, heq⟩ := hpartner
  have hs : (SigningDescentProof.FinalState.mk x top state forgery
      z.2.1.1.1.1.1 false).selected prims = some selected := hsel
  obtain ⟨top', state', forgery', message, start, middle, i, J, parts, values, before, after,
      hm', hb, hf, hstate, hrelease, hv, hfinish⟩ := splitRun_release_occurrence prims A x z hz hrel
  rw [hm] at hm'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
  rcases halign A x z hz top state forgery hm forgery message i hrelease selected hs with hflag | halt | hsign
  · exact (hnflag ⟨top, state, forgery, hm, hflag⟩).elim
  · exact Or.inr halt
  left
  obtain ⟨encoding, hdecode⟩ := SigningPartnerCompareProof.selected_decode prims
    (SigningDescentProof.FinalState.mk x top state forgery z.2.1.1.1.1.1 false) selected hs
  change XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.2.1.1.1.1.1)
      x.1 forgery.signature.leafIndex selected =
    XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView z.2.1.1.1.1.1)
      x.1 forgery.signature.leafIndex
      (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness) at heq
  obtain ⟨a, ha⟩ := XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some
    (SigningDescentProof.thView z.2.1.1.1.1.1) x.1 forgery.signature.leafIndex
    selected.1 selected.2 encoding hdecode
  obtain ⟨b, hb⟩ := XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some
    (SigningDescentProof.thView z.2.1.1.1.1.1) x.1 forgery.signature.leafIndex
    forgery.message (XmssSecurity.Bridge.toModelSig forgery.signature).randomness encoding
    (heq ▸ hdecode)
  refine hsep A x z hz forgery.signature.leafIndex _ hsign _ _
    (fun h => hne (XmssSecurity.Concrete.CacheView.encodingInput_injective _ _ h))
    (XmssSecurity.encodingInputLeafIndex?_encodingInput _ _ _)
    (XmssSecurity.encodingInputLeafIndex?_encodingInput _ _ _) a b ha hb ?_ ?_
  · exact (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ha).symm
  · exact (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hb).symm.trans heq.symm

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedLinkProof.QueryOccurrence.head_support' does not depend on any axioms -/
#guard_msgs in
#print axioms QueryOccurrence.head_support

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedLinkProof.first_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_failure

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedLinkProof.splitRun_release_occurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitRun_release_occurrence

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedLinkProof.jointCachedExtra_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointCachedExtra_base

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedLinkProof.world_base_subrun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms world_base_subrun

/-- info: 'ThresholdLeanXmssSecurity.SigningReleasedLinkProof.releasedLink_of_alignment_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms releasedLink_of_alignment_separation


end SigningReleasedLinkProof
end ThresholdLeanXmssSecurity
