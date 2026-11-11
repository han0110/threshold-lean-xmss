import ThresholdLeanXmssSecurity.Proof.SigningGuessLink

/-!
# Support facts of the uncharged lane

## The state of the signing oracles only grows

* `StateGrows st st'` says that `bound` is write-once, and that the corrupt set and the release list
  grow. `gameOracles_stateGrows` gives one call. `openingOracles_grows` gives a whole run of
  `openingOracles` from any state, with the released trees and the log. So the state at each
  adversary call grows to the final state. The verification calls of `verifyRun` run at the final
  state.
* `signersAt_mono` and `releasedAt_mono` follow.

## The opened position at call time

* `releasedAt st e` is `HonestKey.released` read at the state `st`. `honestKey_released` shows that
  the final key uses the final state.
* `bottomOpened_callTime` shows that a position below the final opened position is below the
  position opened at each earlier state, on one cache. `topOpened` does not read the state.

## The cache of a released signature

* `bottomOpened_cache_mono` gives the read on a smaller cache an opened position at least as high.
  `verifyRun_bottomOpened` applies it to the cache of the verification calls. This does not show
  that a value below the opened position was unreleased, see step 6 of the trace.
* `bottomOpened_cache_eq` shows that the read does not change when the selected digest input is
  already in the smaller cache (`SelectedCached`).
* `ReleasedResolved` is the open fact at the start of the verification, outside `OpeningMatch`.
  `verifyRun_bottomOpened_eq` gives the equal read from it.
* The unconditional form "a released signature is resolved in the cache" is false. The trace
  below breaks it. Each step is a call of the game.

1. Round 1 of an honest `i` at key `e` binds message `m`. The adversary holds `t - 1` corrupt
   operators, and the quorum `J` has a second member `j`.
2. The adversary finds `ρ' ≠ ρ_e` with `truncateHash (H (commitmentInput P e ρ')) = c_e`. This is
   `SigningGuessProof.DifferentOpening`.
3. Round 2 of `i` gets a part at `j` such that `combine J parts = ρ'`. `signCodeword` accepts. It
   calls `randomizerInput P bottomLayer e ρ' m` and grinds from that base. The adversary makes no
   call on the selected digest input of `hk.selected`, so it stays out of the cache.
4. `(e, m, i)` joins the release list. With the `t - 1` corrupt operators, `releasedAt` is true.
5. The forgery is at `(e, m)`. Each later adversary call and the verification read the chain end as
   the opened position. The fresh check of `tsigFinish` runs `honestSignature` with `ρ_e` and caches
   the selected input. So the final read gives the canonical digits `d`.
6. Round 2 released the digits `d'` of `ρ'`. A chain value at a position in `[d'_l, d_l)` is public,
   but `chainTarget` counts it as hidden.

Step 2 leaves both commitment inputs in the final cache. So the run has
`SigningGuessProof.OpeningMatch`, hence `AlternativeCommitment`
(`SigningGuessProof.openingMatch_alternativeCommitment`), which `ChargedOutput` holds and
`UnchargedWin` excludes. Outside it, an accepted round 2 runs the canonical grind
(`SigningGuessProof.signCodeword_canonical`), which calls the selected input.

## Bottom cache reads

`bottomPartner_inputs_cached` is the bottom form of `SigningGuessProof.topPartner_inputs_cached`.
Both digest reads of a bottom partner on a winning run come from the cache, not from the default
zero. It uses `encodingInput_cached_of_decode_some` of leanVM.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningSupportProof

open LeanXmss ThresholdLeanXmss SigningOpeningProof

variable {C : Committee}

section BottomPartner

variable (prims : Primitives)

set_option maxRecDepth 100000 in
/-- On a supported winning run, both sides of a bottom digest equality are cached. -/
theorem bottomPartner_inputs_cached (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningCostProof.Outcome C) (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hmeta : r.1.2 = some (top, state, forgery))
    (selected : XmssSecurity.Message × XmssSecurity.Randomness)
    (heq : XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView r.2.1) x.1
        forgery.signature.leafIndex selected =
      XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView r.2.1) x.1
        forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)) :
    (∃ output, SigningDescentProof.thView r.2.1
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected) =
        some output) ∧
    (∃ output, SigningDescentProof.thView r.2.1
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)) =
        some output) := by
  obtain ⟨top', state', forgery', hmeta', _, hresolved, _⟩ :=
    SigningCacheProof.exposedRun_facts prims A x r hr hwin
  rw [hmeta] at hmeta'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmeta')
  have hverified := (XmssSecurity.Concrete.CacheReplay.eval_verify _ _ _ _ _).symm.trans
    (SigningCacheProof.resolves_value hresolved)
  obtain ⟨encoding, hdecode, _⟩ :=
    (XmssSecurity.Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hverified
  have hselected := heq.symm ▸ hdecode
  exact ⟨XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some _ _ _ selected.1 selected.2
      encoding hselected,
    XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some _ _ _ _ _ encoding hdecode⟩

end BottomPartner

section Grows

/-- The state of the signing oracles grows from `st` to `st'`. `bound` is write-once, and the
corrupt set and the release list grow. -/
def StateGrows (st st' : TsigState C) : Prop :=
  SigningGuessProof.BoundExtends st st' ∧ st.corrupt ⊆ st'.corrupt ∧ st.released <+: st'.released

theorem stateGrows_refl (st : TsigState C) : StateGrows st st :=
  ⟨SigningGuessProof.boundExtends_refl st, Finset.Subset.refl _, List.prefix_refl _⟩

theorem stateGrows_trans {st st' st'' : TsigState C} (h : StateGrows st st') (h' : StateGrows st' st'') :
    StateGrows st st'' :=
  ⟨SigningGuessProof.boundExtends_trans h.1 h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- Once `bound e` is some message, it stays that message. -/
theorem StateGrows.bound_eq {st st' : TsigState C} (h : StateGrows st st') {e : KeyIndex}
    {message : Message} (hb : st.bound e = some message) : st'.bound e = some message :=
  h.1 e message hb

theorem signersAt_mono {st st' : TsigState C} (h : StateGrows st st') (e : KeyIndex) (message : Message) :
    signersAt st e message ⊆ signersAt st' e message := by
  obtain ⟨rest, hrest⟩ := h.2.2
  unfold signersAt
  rw [← hrest]
  refine Finset.union_subset_union h.2.1 ?_
  intro i hi
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hi ⊢
  obtain ⟨a, ⟨ha, hf⟩, rfl⟩ := hi
  exact ⟨a, ⟨List.mem_append_left _ ha, hf⟩, rfl⟩

theorem gameOracles_stateGrows (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C)
    (r : (LocalSpec C + TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((SigningCoreProof.gameOracles dealt t).run st)) : StateGrows st r.2 := by
  cases t with
  | inl t =>
    change r ∈ support ((fun a => (a, st)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hr
    simp only [support_map] at hr
    obtain ⟨value, _, rfl⟩ := hr
    exact stateGrows_refl st
  | inr t =>
    refine ⟨SigningGuessProof.tsigOracles_boundExtends _ dealt t st r hr,
      SigningGuessProof.tsigOracles_corrupt_mono _ dealt t st r hr, ?_⟩
    rw [SigningGuessProof.tsigOracles_releaseStep _ dealt t st r hr, SigningGuessProof.releaseStep_append]
    exact List.prefix_append _ _

/-- One call of `openingOracles` grows the state, the released trees and the log. -/
def OpeningGrows (s s' : (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) :
    Prop :=
  StateGrows s.1.1 s'.1.1 ∧ s.2.1 ⊆ s'.2.1 ∧ s.2.2 <+: s'.2.2

theorem openingGrows_trans {s s' s''} (h : OpeningGrows (C := C) s s') (h' : OpeningGrows s' s'') :
    OpeningGrows s s'' :=
  ⟨stateGrows_trans h.1 h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

theorem openingOracles_step_grows (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) (t : (LocalSpec C + TsigSpec C).Domain)
    (s : (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest))
    (z : (LocalSpec C + TsigSpec C).Range t ×
      (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest))
    (hz : z ∈ support ((openingOracles x dealt t).run s)) : OpeningGrows s z.2 := by
  have hflag : (z.1, z.2.1) ∈ support ((SigningCoreProof.flaggedOracles x dealt t).run s.1) := by
    rw [← openingOracles_forget x dealt t s.1 s.2, support_map]
    exact ⟨z, hz, rfl⟩
  have hgame : (z.1, z.2.1.1) ∈ support ((SigningCoreProof.gameOracles dealt t).run s.1.1) := by
    rw [← SigningCoreProof.flaggedOracles_forget x dealt t s.1.1 s.1.2, support_map]
    exact ⟨_, hflag, rfl⟩
  refine ⟨gameOracles_stateGrows dealt t s.1.1 _ hgame, ?_⟩
  rcases t with t | q
  · simp only [openingOracles, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, _, rfl⟩ := hz
    exact ⟨Finset.Subset.refl _, List.prefix_append _ _⟩
  · simp only [openingOracles, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, _, rfl⟩ := hz
    refine ⟨?_, List.prefix_refl _⟩
    cases q <;> simp [releasedTrees, Finset.subset_insert]

/-- A run of `openingOracles` from any state grows it. Each adversary call starts a rest of the run,
so the state at each call grows to the final state. -/
theorem openingOracles_grows (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) {α : Type} (oa : OracleComp (LocalSpec C + TsigSpec C) α)
    (s : (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) :
    ∀ z ∈ support ((simulateQ (openingOracles x dealt) oa).run s), OpeningGrows s z.2 :=
  SeedHitProof.support_simulateQ_inv (openingOracles x dealt) (OpeningGrows s)
    (fun t s' hs z hz => openingGrows_trans hs (openingOracles_step_grows x dealt t s' z hz)) oa s
    ⟨stateGrows_refl _, Finset.Subset.refl _, List.prefix_refl _⟩

end Grows

section CallTime

/-- `HonestKey.released` read at the state `st`. At least `t` operators can give the chain parts at
`e` for the bound message. -/
def releasedAt (st : TsigState C) (e : KeyIndex) : Bool :=
  match st.bound e with
  | some message => decide (C.t ≤ (signersAt st e message).card)
  | none => false

theorem honestKey_released (prims : Primitives) (z : SigningDescentProof.FinalState C) :
    (z.honestKey prims).released = releasedAt z.state z.key := rfl

theorem releasedAt_mono {st st' : TsigState C} (h : StateGrows st st') (e : KeyIndex)
    (hr : releasedAt st e = true) : releasedAt st' e = true := by
  unfold releasedAt at hr ⊢
  cases hb : st.bound e with
  | none => simp [hb] at hr
  | some message =>
    rw [hb] at hr
    rw [h.bound_eq hb]
    simp only [decide_eq_true_eq] at hr ⊢
    exact hr.trans (Finset.card_le_card (signersAt_mono h e message))

/-- A position below the opened position of the final state is below the position opened at each
earlier state. -/
theorem bottomOpened_callTime (c : HashCache C) (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex)
    (hk : SigningDescentProof.HonestKey) {st st' : TsigState C} (h : StateGrows st st')
    (hfinal : hk.released = releasedAt st' e) (l : XmssSecurity.ChainIndex) {p : ℕ}
    (hp : p < SigningDescentProof.bottomOpened c P e hk l) :
    p < SigningDescentProof.bottomOpened c P e { hk with released := releasedAt st e } l := by
  cases hr : releasedAt st e with
  | false =>
    rw [SigningDescentProof.bottomOpened_of_not_released (hr := rfl)]
    exact lt_of_lt_of_le hp (SigningGuessLinkProof.bottomOpened_le c P e hk l)
  | true =>
    have hk' : hk.released = true := hfinal.trans (releasedAt_mono h e hr)
    have heq : { hk with released := true } = hk := by
      cases hk
      simp only at hk'
      subst hk'
      rfl
    rw [heq]
    exact hp

/-- The final key at the final cache. A position below its opened position is below the position
opened at each earlier state. -/
theorem finalState_bottomOpened_callTime (prims : Primitives) (z : SigningDescentProof.FinalState C)
    {st : TsigState C} (h : StateGrows st z.state) (l : XmssSecurity.ChainIndex) {p : ℕ}
    (hp : p < SigningDescentProof.bottomOpened z.cache z.keys.1 z.key (z.honestKey prims) l) :
    p < SigningDescentProof.bottomOpened z.cache z.keys.1 z.key
      { z.honestKey prims with released := releasedAt st z.key } l :=
  bottomOpened_callTime z.cache z.keys.1 z.key (z.honestKey prims) h (honestKey_released prims z) l hp

/-- The read of `bottomOpened` on a smaller cache, with the same key, opens no lower position. A
cached selected digest keeps its value, and a missing one reads as the chain end. -/
theorem bottomOpened_cache_mono {c c' : HashCache C} (hle : c ≤ c') (P : XmssSecurity.PublicParameter)
    (e : XmssSecurity.LeafIndex) (hk : SigningDescentProof.HonestKey) (l : XmssSecurity.ChainIndex) {p : ℕ}
    (hp : p < SigningDescentProof.bottomOpened c' P e hk l) :
    p < SigningDescentProof.bottomOpened c P e hk l := by
  cases hsel : SigningDescentProof.selectedEncoding c P e hk with
  | none =>
    have : SigningDescentProof.bottomOpened c P e hk l = XmssSecurity.chainLength - 1 := by
      unfold SigningDescentProof.bottomOpened
      rw [hsel]
      split <;> simp_all
    rw [this]
    exact lt_of_lt_of_le hp (SigningGuessLinkProof.bottomOpened_le c' P e hk l)
  | some encoding =>
    have hsel' : SigningDescentProof.selectedEncoding c' P e hk = some encoding := by
      unfold SigningDescentProof.selectedEncoding at hsel ⊢
      cases hs : hk.selected with
      | none => simp [hs] at hsel
      | some s =>
        rw [hs] at hsel
        simp only [Option.bind_some] at hsel ⊢
        obtain ⟨output, hout⟩ := XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some
          (SigningDescentProof.thView c) P e s.1 s.2 encoding hsel
        have hout' : SigningDescentProof.thView c'
            (XmssSecurity.Concrete.CacheView.encodingInput P e (s.1, s.2)) = some output :=
          hle (show c (.hash _) = some output from hout)
        rw [XmssSecurity.Concrete.CacheView.encodingHash,
          XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout'] at ⊢
        rw [XmssSecurity.Concrete.CacheView.encodingHash,
          XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout] at hsel
        exact hsel
    unfold SigningDescentProof.bottomOpened at hp ⊢
    rw [hsel] at ⊢
    rw [hsel'] at hp
    exact hp

/-- The selected digest input of `hk` is in the cache `c`. -/
def SelectedCached (c : HashCache C) (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex)
    (hk : SigningDescentProof.HonestKey) : Prop :=
  ∀ s ∈ hk.selected, (SigningDescentProof.thView c (XmssSecurity.Concrete.CacheView.encodingInput P e s)).isSome

/-- If the selected digest input is in the smaller cache, the read of `bottomOpened` does not
change. -/
theorem bottomOpened_cache_eq {c c' : HashCache C} (hle : c ≤ c') (P : XmssSecurity.PublicParameter)
    (e : XmssSecurity.LeafIndex) (hk : SigningDescentProof.HonestKey) (hc : SelectedCached c P e hk) :
    SigningDescentProof.bottomOpened c P e hk = SigningDescentProof.bottomOpened c' P e hk := by
  have hsel : SigningDescentProof.selectedEncoding c P e hk = SigningDescentProof.selectedEncoding c' P e hk := by
    unfold SigningDescentProof.selectedEncoding
    cases hs : hk.selected with
    | none => simp only [Option.bind_none]
    | some s =>
      simp only [Option.bind_some]
      obtain ⟨output, hout⟩ := Option.isSome_iff_exists.mp (hc s (by simp [hs]))
      have hout' : SigningDescentProof.thView c'
          (XmssSecurity.Concrete.CacheView.encodingInput P e s) = some output :=
        hle (show c (.hash _) = some output from hout)
      rw [XmssSecurity.Concrete.CacheView.encodingHash, XmssSecurity.Concrete.CacheView.encodingHash,
        XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout,
        XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout']
  funext l
  unfold SigningDescentProof.bottomOpened
  rw [hsel]

end CallTime

section Verification

variable (prims : Primitives)

set_option maxRecDepth 100000 in
/-- The verification calls of `verifyRun` run at the final state, with a cache below the final
cache. A position below the opened position on the final cache is below the opened position on the
cache of the verification. -/
theorem verifyRun_bottomOpened (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C) (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery)) :
    ∃ (trees : Finset (Fin (2 ^ layerHeight))) (adversaryLog : List (HiddenKey × Digest))
      (s : HashCache C × ℕ) (v : (Bool × List (HiddenKey × Digest)) × HashCache C × ℕ),
      v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
        (SigningGuessLinkProof.loggedTweakable x.1 state trees
          (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)))).run s) ∧
      r.1.2 = adversaryLog ++ v.1.2 ∧ v.2.1 ≤ r.2.1 ∧
      ∀ (hk : SigningDescentProof.HonestKey) (l : XmssSecurity.ChainIndex) (p : ℕ),
        p < SigningDescentProof.bottomOpened r.2.1 x.1 forgery.signature.leafIndex hk l →
        p < SigningDescentProof.bottomOpened v.2.1 x.1 forgery.signature.leafIndex hk l := by
  obtain ⟨trees, adversaryLog, s, v, hv, hlog, hle⟩ :=
    SigningGuessLinkProof.verifyRun_verification prims A x r hr top state forgery hm
  exact ⟨trees, adversaryLog, s, v, hv, hlog, hle, fun hk l _ hp => bottomOpened_cache_mono hle _ _ hk l hp⟩

/-- The open fact of the cache. Outside `OpeningMatch`, a released signature of the final key has
its selected digest input in the cache when the verification starts. -/
def ReleasedResolved : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C),
    r ∈ support (SigningGuessLinkProof.verifyRun prims A x) →
    ∀ top state forgery, r.1.1.2 = some (top, state, forgery) →
      ¬SigningGuessProof.OpeningMatch prims x (r.1.1, r.2) →
      ∃ (trees : Finset (Fin (2 ^ layerHeight))) (adversaryLog : List (HiddenKey × Digest))
        (s : HashCache C × ℕ) (v : (Bool × List (HiddenKey × Digest)) × HashCache C × ℕ),
        v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
          (SigningGuessLinkProof.loggedTweakable x.1 state trees
            (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)))).run s) ∧
        r.1.2 = adversaryLog ++ v.1.2 ∧ v.2.1 ≤ r.2.1 ∧
        let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
        (z.honestKey prims).released = true → SelectedCached s.1 x.1 z.key (z.honestKey prims)

set_option maxRecDepth 100000 in
/-- Under `ReleasedResolved`, the read of `bottomOpened` at the start of the verification is the
read on the final cache. -/
theorem verifyRun_bottomOpened_eq (hresolved : ReleasedResolved prims (C := C)) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x)) (top : TopTree) (state : TsigState C)
    (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (hn : ¬SigningGuessProof.OpeningMatch prims x (r.1.1, r.2)) :
    ∃ s : HashCache C × ℕ, s.1 ≤ r.2.1 ∧
      let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
      SigningDescentProof.bottomOpened s.1 x.1 z.key (z.honestKey prims) =
        SigningDescentProof.bottomOpened r.2.1 x.1 z.key (z.honestKey prims) := by
  obtain ⟨_, _, s, v, hv, _, hle, hc⟩ := hresolved A x r hr top state forgery hm hn
  have hs : s.1 ≤ r.2.1 := (SigningCacheProof.countRun_grows prims _ s v hv).trans hle
  refine ⟨s, hs, ?_⟩
  cases hrel : (SigningCostProof.finalOf x (r.1.1, r.2) top state forgery).honestKey prims |>.released with
  | false =>
    exact (SigningDescentProof.bottomOpened_of_not_released _ _ _ _ hrel).trans
      (SigningDescentProof.bottomOpened_of_not_released _ _ _ _ hrel).symm
  | true => exact bottomOpened_cache_eq hs _ _ _ (hc hrel)

end Verification

end SigningSupportProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.bottomPartner_inputs_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.bottomPartner_inputs_cached

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.openingOracles_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.openingOracles_grows

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.releasedAt_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.releasedAt_mono

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.bottomOpened_callTime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.bottomOpened_callTime

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.finalState_bottomOpened_callTime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.finalState_bottomOpened_callTime

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.bottomOpened_cache_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.bottomOpened_cache_mono

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.bottomOpened_cache_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.bottomOpened_cache_eq

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.verifyRun_bottomOpened' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.verifyRun_bottomOpened

/--
info: 'ThresholdLeanXmssSecurity.SigningSupportProof.verifyRun_bottomOpened_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSupportProof.verifyRun_bottomOpened_eq
