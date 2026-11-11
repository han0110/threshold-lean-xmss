import ThresholdLeanXmssSecurity.Proof.SigningRoute
import ThresholdLeanXmssSecurity.Proof.SigningReleased

/-!
# The guarded flag of the uncharged lane

This module repairs the two defects of the signing review (R1 and R2).

## R2. The flag

`UnchargedFlagSoundCoupling` is false. Its flag holds without a win, and `chainTarget` reads a chain
start whose PRF entries are absent as the replay default zero. One adversary call at value zero then
raises the flag with probability one.

* `partialChainTarget` is `none` when a PRF entry of the chain start is absent from the final cache.
* `GuardedFlag` is `UnchargedWinLogged` together with the parts of `UnchargedFlag` on the partial
  target. So the flag has no mass outside the winning forgeries (`probEvent_guardedFlag_not_win`).
* `guardedFlag_of_win` gives the link from the win to the guarded flag.
* `hiddenCoreAt_of_guardedCoupling` replaces `hiddenCoreAt_of_unchargedCoupling`.

`GuardedFlag` has one more part, `ForgedStartAbsent`. A chain start at the key of the forgery has an
absent PRF entry. Nothing here excludes it in a win. If the bottom tree of the key is never built,
the replay data of the bottom key are public zeros, and a forgery that wins at the top layer can
still be a bottom `Guess`. This part is an open row of the hybrid.

The two counterexamples of the review fail on the guarded flag.

* The first forgery does not need to win. `guardedFlag_win` asks for a win, and
  `partialChainTarget_absent` gives no target at an absent chain start.
* The second one calls the PRF on a hardcoded seed. `hiddenHit_prf`, `flaggedOracles_hiddenHit` and
  `flaggedOracles_run_flag` set the flag of the run, and `guardedFlag_flag_false` asks for no flag.

## R1. The verification prefix

`VerificationPrefix` is the real decomposition of an outcome of `verifyRun`, with the state `q.2` at
the actual start of the verification. `verificationPrefix_exists` gives it.
`verificationPrefix_bottomOpened_eq` reads `bottomOpened` at `q.2.1` for every decomposition, so no
witness is chosen.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningGuardedFlagProof

open LeanXmss ThresholdLeanXmss SigningOpeningProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The PRF entries of the chain start of chain `l` at the key `e` of layer `lay` are all in the
cache. The start is their XOR, so it is random only when each entry is cached. -/
def StartsCached (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (lay : Layer) (e : KeyIndex)
    (l : ChainIndex) : Prop :=
  ∀ T ∈ C.terms, (cache (.prf (x.2.1 T) (.chain lay e l (digit 0)))).isSome

/-- The chain starts that the target of a hidden key reads are cached. An opening reads none. -/
def KeyStartsCached (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) : HiddenKey → Prop
  | .opening _ _ => True
  | .bottomChain e l _ => StartsCached x cache bottomLayer e l
  | .topChain b l _ => StartsCached x cache topLayer (topKey b) l

/-- The partial chain target. It is `chainTarget` when the final cache holds every PRF entry of the
chain start, and `none` otherwise. A replay default is never a target. -/
def partialChainTarget (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (key : HiddenKey) : Option Digest :=
  if KeyStartsCached x r.2.1 key then SigningGuessLinkProof.chainTarget prims x r key else none

/-- A chain start at the key of the forgery, at the bottom key or at its top key, has a PRF entry
that is absent from the final cache. -/
def ForgedStartAbsent (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C) : Prop :=
  ∃ top state forgery, r.1.1.2 = some (top, state, forgery) ∧ ∃ l : ChainIndex,
    ¬StartsCached x r.2.1 bottomLayer forgery.signature.leafIndex l ∨
      ¬StartsCached x r.2.1 topLayer (topKey (XmssSecurity.topKeyOf forgery.signature.leafIndex)) l

/-- A hit on the total chain target is a hit on the partial target, unless a chain start at the key
of the forgery is absent. -/
theorem hiddenInputHit_partial (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (hhit : HiddenInputHit x (SigningGuessLinkProof.chainTarget prims x r) r)
    (hcached : ¬ForgedStartAbsent x r) :
    HiddenInputHit x (partialChainTarget prims x r) r := by
  obtain ⟨c, hc, ht⟩ := hhit
  refine ⟨c, hc, ?_⟩
  rcases c with ⟨key, d⟩
  cases key with
  | opening lay e => exact ht
  | bottomChain e l p =>
    simp only [hiddenTarget, partialChainTarget] at ht ⊢
    rw [if_pos]
    · exact ht
    obtain ⟨⟨top, state, forgery⟩, hm⟩ : ∃ v, r.1.1.2 = some v := by
      cases hm : r.1.1.2 with
      | none => simp [SigningGuessLinkProof.chainTarget, hm] at ht
      | some v => exact ⟨v, rfl⟩
    simp only [SigningGuessLinkProof.chainTarget, hm] at ht
    split_ifs at ht with h
    obtain ⟨rfl, -⟩ := h
    by_contra hn
    exact hcached ⟨top, state, forgery, hm, l, Or.inl hn⟩
  | topChain b l p =>
    simp only [hiddenTarget, partialChainTarget] at ht ⊢
    rw [if_pos]
    · exact ht
    obtain ⟨⟨top, state, forgery⟩, hm⟩ : ∃ v, r.1.1.2 = some v := by
      cases hm : r.1.1.2 with
      | none => simp [SigningGuessLinkProof.chainTarget, hm] at ht
      | some v => exact ⟨v, rfl⟩
    simp only [SigningGuessLinkProof.chainTarget, hm] at ht
    split_ifs at ht with h
    obtain ⟨rfl, -⟩ := h
    by_contra hn
    exact hcached ⟨top, state, forgery, hm, l, Or.inr hn⟩

open SigningUnchargedLoggedProof SigningPartnerBoundProof in
/-- The guarded flag of the uncharged lane. It is the uncharged win on the log together with one of
its parts.

* An input-side hit on the partial chain target.
* A bottom partner whose selection is not fresh.
* A top partner that no successful bottom ceremony resolves.
* A chain start at the key of the forgery with an absent PRF entry.
-/
def GuardedFlag (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  UnchargedWinLogged prims x (w.1.1, w.2) ∧
    (HiddenInputHit x (partialChainTarget prims x (w.1, w.2.1)) (w.1, w.2.1) ∨
      (SigningPartnerLinkProof.BottomPartnerCase prims x (w.1.1, w.2.1) ∧ ¬FreshSelection prims x w) ∨
      (SigningGuessProof.TopPartner prims x (w.1.1, w.2.1) ∧
        ¬∃ key, SigningGuessProof.ResolvedTopPartner x key w.2.1.1) ∨
      ForgedStartAbsent x (w.1, w.2.1))

open SigningUnchargedLoggedProof SigningPartnerBoundProof in
set_option maxRecDepth 100000 in
/-- An uncharged win on the log raises the guarded flag. -/
theorem guardedFlag_of_win (hlink : FreshPartnerLink (C := C) prims) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) (hw : w ∈ support (jointRun prims A x))
    (hu : UnchargedWinLogged prims x (w.1.1, w.2)) : GuardedFlag prims x w := by
  refine ⟨hu, ?_⟩
  by_cases habsent : ForgedStartAbsent x (w.1, w.2.1)
  · exact Or.inr (Or.inr (Or.inr habsent))
  rcases unchargedFlag_of_win prims hlink A x w hw hu with hhit | hbottom | htop
  · exact Or.inl (hiddenInputHit_partial prims x (w.1, w.2.1) hhit habsent)
  · exact Or.inr (Or.inl hbottom)
  · exact Or.inr (Or.inr (Or.inl htop))

open SigningUnchargedLoggedProof in
/-- The coupling of the uncharged lane for the guarded flag. It is the `hcouple` premise of
`SigningOpeningProof.probEvent_le_of_capped` for `GuardedFlag`. -/
def GuardedFlagCoupling : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    ∃ (κ σ β K : Type) (spec : OracleSpec κ) (_ : Fintype K) (_ : DecidableEq K)
      (_ : SampleableType (K → Digest)) (impl : QueryImpl spec (StateT σ ProbComp))
      (inputSide p : κ → Prop) (keyOf : κ → K) (point : κ → Digest)
      (outHit : (t : κ) → σ × ℕ → spec t × (σ × ℕ) → Prop)
      (oa : OracleComp (spec + RevealSpec K Digest) β) (σ₀ : σ),
      (∀ t σ₁ n, p t → ¬inputSide t →
        Pr[outHit t (σ₁, n) | (countImpl impl p t).run (σ₁, n)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹) ∧
      Pr[GuardedFlag prims x | jointRun prims A x] ≤
        Pr[fun r => r.2.2.2 = true | $ᵗ (K → Digest) >>= fun s =>
          (simulateQ (revealImpl (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point s) oa).run
            ((σ₀, 0), fun _ => none, false)]

open SigningUnchargedLoggedProof SigningPartnerBoundProof in
set_option maxRecDepth 100000 in
/-- The uncharged lane on the log from the fresh partner link and the guarded coupling. -/
theorem unchargedLaneBoundLogged_of_guardedCoupling (hlink : FreshPartnerLink (C := C) prims)
    (hcouple : GuardedFlagCoupling (C := C) prims) : UnchargedLaneBoundLogged (C := C) prims := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨κ, σ, β, K, spec, _, _, _, impl, inputSide, p, keyOf, point, outHit, oa, σ₀, hout, hflag⟩ :=
    hcouple A q x hx hkeys hq hsmall
  have hle : Pr[UnchargedWinLogged prims x | SigningCostProof.loggedRun prims A x] ≤
      Pr[GuardedFlag prims x | jointRun prims A x] := by
    rw [← jointRun_logged, probEvent_map]
    exact probEvent_mono fun w hw hu => guardedFlag_of_win prims hlink A x w hw hu
  exact hle.trans (probEvent_le_of_capped impl inputSide p
    (jointRun prims A x) (GuardedFlag prims x) keyOf point q outHit hout oa σ₀ hflag)

/-- `HiddenCoreAt` from the one open coupling of the uncharged lane, the guarded one. It replaces
`hiddenCoreAt_of_unchargedCoupling`. -/
theorem hiddenCoreAt_of_guardedCoupling (hcouple : GuardedFlagCoupling (C := C) prims) :
    SigningCoreProof.HiddenCoreAt prims C :=
  SigningPartnerBoundProof.hiddenCoreAt_of_logged prims
    (unchargedLaneBoundLogged_of_guardedCoupling prims
      (SigningUnchargedLoggedProof.freshPartnerLink_of_classification prims
        (SigningSelectionProof.selectionClassification prims)) hcouple)

/-! ## The two counterexamples of review R2 -/

open SigningUnchargedLoggedProof in
/-- The guarded flag holds only on a winning forgery without the flag of a hidden-key call. -/
theorem guardedFlag_win (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) (h : GuardedFlag prims x w) :
    w.1.1.1 = (true, false) :=
  h.1.1

open SigningUnchargedLoggedProof in
/-- The guarded flag has no mass outside the winning forgeries. In the first counterexample the
forgery is arbitrary, so the flag has probability at most the win. -/
theorem probEvent_guardedFlag_not_win (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun w => GuardedFlag prims x w ∧ w.1.1.1 ≠ (true, false) | jointRun prims A x] = 0 :=
  probEvent_eq_zero fun w _ h => h.2 (guardedFlag_win prims x w h.1)

/-- A chain start with an absent PRF entry gives no target. The logged zero of the first
counterexample therefore meets no target. -/
theorem partialChainTarget_absent (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep)
    (hmiss : ∀ T, r.2.1 (.prf (x.2.1 T) (.chain bottomLayer e l (digit 0))) = none) :
    partialChainTarget prims x r (.bottomChain e l p) = none := by
  obtain ⟨T₀, -⟩ := lackedTerm_empty (C := C)
  unfold partialChainTarget
  rw [if_neg]
  intro h
  have := h T₀ (mem_terms T₀)
  rw [hmiss T₀] at this
  exact absurd this (by simp)

/-- A PRF call on an unrevealed seed is a hidden-key call. This is the call of the second
counterexample, which hardcodes the seeds. -/
theorem hiddenHit_prf (x : SigningSecurityProof.Keys3 C) (D : Finset C.Party) (T : C.Term) (j : Point)
    (h : ¬TprfSecurityProof.Revealed D (.inl T)) :
    SigningCoreProof.hiddenHit x D (.inr (.inl (.prf (x.2.1 T) j))) = true := by
  simp only [SigningCoreProof.hiddenHit, decide_eq_true_eq]
  exact ⟨T, rfl, h⟩

/-- A hidden-key call of the adversary sets the flag. -/
theorem flaggedOracles_hiddenHit (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C).Domain) (st : TsigState C) (flag : Bool)
    (h : SigningCoreProof.hiddenHit x st.corrupt t = true)
    (z : (LocalSpec C + TsigSpec C).Range (.inl t) × TsigState C × Bool)
    (hz : z ∈ support ((SigningCoreProof.flaggedOracles x dealt (.inl t)).run (st, flag))) : z.2.2 = true := by
  simp only [SigningCoreProof.flaggedOracles, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨a, -, rfl⟩ := hz
  simp [h]

/-- Once set, the flag stays set for the rest of the run of the oracles. -/
theorem flaggedOracles_run_flag (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    {α : Type} (oa : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C)
    (z : α × TsigState C × Bool)
    (hz : z ∈ support ((simulateQ (SigningCoreProof.flaggedOracles x dealt) oa).run (st, true))) :
    z.2.2 = true := by
  induction oa using OracleComp.inductionOn generalizing st z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hflag : y.2.2 = true := by
      by_contra hn
      exact absurd (SigningGuessProof.flaggedOracles_flag_false x dealt t st true y hy
        (Bool.eq_false_iff.mpr hn)) (by simp)
    rcases y with ⟨a, st', b⟩
    simp only at hflag
    subst hflag
    exact ih a st' z hz

open SigningUnchargedLoggedProof in
/-- The guarded flag leaves out every run with a hidden-key call. In the second counterexample the
flag is set, so the guarded flag fails. -/
theorem guardedFlag_flag_false (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (h : GuardedFlag prims x w) : w.1.1.1.2 = false :=
  congrArg Prod.snd (guardedFlag_win prims x w h)

/-! ## The verification prefix (review R1) -/

/-- The dealt keys of the game with the top tree `top`. -/
abbrev dealtOf (x : SigningSecurityProof.Keys3 C) (top : TopTree) : Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top
    fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)

/-- The real decomposition of an outcome `r` of `verifyRun`. The run builds the top tree (`p`),
runs the adversary (`q`), runs the verification from the state `q.2` (`v`) and runs the freshness
check (`f`). So `q.2` is the cache and the count at the actual start of the verification. -/
def VerificationPrefix (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C)
    (q : (Forgery × (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ)
    (v : (Bool × List (HiddenKey × Digest)) × HashCache C × ℕ) : Prop :=
  ∃ (top : TopTree) (p : Option TreeOutput × HashCache C × ℕ) (f : Bool × HashCache C × ℕ),
    p ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top)).run (∅, 0)) ∧
    p.1 = some (.top top) ∧
    q ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (openingOracles x (dealtOf x top))
        (A ⟨(dealtOf x top).top.root, (dealtOf x top).parameter⟩ (dealtOf x top).top)).run
          ((SigningCoreProof.tsigInit, false), ∅, []))).run p.2) ∧
    v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
      (SigningGuessLinkProof.loggedTweakable x.1 q.1.2.1.1 q.1.2.2.1
        (Concrete.verify ⟨top.root, x.1⟩ q.1.1.message q.1.1.signature)))).run q.2) ∧
    f ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (if (signersAt q.1.2.1.1 q.1.1.signature.leafIndex q.1.1.message).card < C.t then pure true
      else
        (fun honest => decide (honest ≠ some q.1.1.signature)) <$>
          honestSignature (fun oa => SigningCoreProof.honestLift oa) (dealtOf x top)
            q.1.1.signature.leafIndex q.1.1.message)).run v.2) ∧
    r = ((((v.1.1 && f.1, q.1.2.1.2), some (top, q.1.2.1.1, q.1.1)), q.1.2.2.2 ++ v.1.2), f.2)

set_option maxRecDepth 100000 in
/-- Every outcome of `verifyRun` with a forgery has its real decomposition. -/
theorem verificationPrefix_exists (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C) (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery)) :
    ∃ q v, VerificationPrefix prims A x r q v := by
  unfold SigningGuessLinkProof.verifyRun SigningGuessLinkProof.verifyFinal at hr
  dsimp only at hr
  obtain ⟨p, hp, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
  rcases hp1 : p.1 with _ | (top' | tree)
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hm
  swap
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hm
  rw [hp1] at hr
  dsimp only at hr
  obtain ⟨q, hq, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
  rw [simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [SigningGuessLinkProof.tsigFinishLogged_eq] at hw
  obtain ⟨v, hv, hw⟩ := SigningCacheProof.run_bind_support prims _ _ _ w hw
  rw [simulateQ_map, StateT.run_map, support_map] at hw
  obtain ⟨f, hf, rfl⟩ := hw
  exact ⟨q, v, top', p, f, hp, hp1, hq, hv, hf, rfl⟩

set_option maxRecDepth 100000 in
/-- Outside `OpeningMatch`, a released signature of the final key has its selected digest input in
the cache at the actual start of the verification. -/
theorem verificationPrefix_selectedCached (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C) (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (hn : ¬SigningGuessProof.OpeningMatch prims x (r.1.1, r.2)) :
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    (z.honestKey prims).released = true → SigningSupportProof.SelectedCached q.2.1 x.1 z.key (z.honestKey prims) := by
  obtain ⟨top', p, f, hp, hp1, hq, hv, hf, rfl⟩ := hpre
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  intro z hrel
  have hqv : q.2.1 ≤ f.2.1 := (SigningCacheProof.countRun_grows prims _ _ v hv).trans
    (SigningCacheProof.countRun_grows prims _ _ f hf)
  rw [SigningSupportProof.honestKey_released] at hrel
  unfold SigningSupportProof.releasedAt at hrel
  change (match q.1.2.1.1.bound q.1.1.signature.leafIndex with
    | some message => decide (C.t ≤ (signersAt q.1.2.1.1 q.1.1.signature.leafIndex message).card)
    | none => false) = true at hrel
  cases hb : q.1.2.1.1.bound q.1.1.signature.leafIndex with
  | none =>
    rw [hb] at hrel
    cases hrel
  | some message =>
  rw [hb] at hrel
  have ht := of_decide_eq_true hrel
  obtain ⟨q', hq', -, hstate, hcache⟩ := SigningReleasedProof.openingRun_receipts prims x _ _
    SigningCoreProof.tsigInit false p.2 q hq
  obtain ⟨receipt, -, hkey, hmessage, hruns⟩ := SigningReleasedProof.receiptRun_released prims x top' _ p.2 q'
    (by exact hq') q.1.1.signature.leafIndex message (by rw [hstate]; exact ht)
  rw [hcache] at hruns
  have htop : TopFacts prims (SigningCacheProof.answersOf f.2.1) x.2.1 x.1 top' := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _] at hp
    have hval := SigningCacheProof.run_liftFree prims _ _ p hp (SigningCacheProof.answersOf f.2.1)
      (SigningCacheProof.agrees_answersOf ((SigningCacheProof.countRun_grows prims _ _ q hq).trans hqv))
    rw [hp1] at hval
    obtain ⟨generated, hgen, hchain, hroot⟩ :=
      D_refTop (prims := prims) (h := SigningCacheProof.answersOf f.2.1) x.1 x.2.1 emptyTop
    have he : generated = top' := TreeOutput.top.inj (Option.some.inj (hgen.symm.trans hval.symm))
    subst generated
    exact ⟨hchain, hroot⟩
  have hfinal := SigningGuessProof.ReceiptRuns.mono prims x top' hqv receipt hruns
  dsimp only at hn
  have hcanon := SigningGuessProof.ReceiptRuns.canonical prims x
    (((v.1.1 && f.1, q.1.2.1.2), some (top', q.1.2.1.1, q.1.1)), f.2) top' q.1.2.1.1 q.1.1 rfl htop
    receipt hfinal hkey hn
  have hselected := SigningGuessProof.ReceiptRuns.selected prims z receipt hfinal hkey
    (by rw [hkey, hmessage]; exact hb) hcanon.1
  intro selected hmem
  have hs : selected = (receipt.message, receipt.randomness) :=
    Option.some.inj ((Option.mem_def.mp hmem).symm.trans hselected)
  subst selected
  obtain ⟨-, -, -, sCode, rCode, -, -, -, -, hCode, hCodeOut, hCodeLe⟩ := hruns
  obtain ⟨output, houtput⟩ := Option.isSome_iff_exists.mp (SigningReleasedProof.run_signCodeword_cached prims x.1
    receipt.commitment receipt.key receipt.message receipt.candidate sCode rCode hCode
    receipt.randomness receipt.encoding hCodeOut)
  rw [show z.key = receipt.key from hkey.symm]
  exact Option.isSome_iff_exists.mpr ⟨output, hCodeLe houtput⟩

/-- The cache at the start of the verification is below the final cache. -/
theorem verificationPrefix_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C) (q v) (hpre : VerificationPrefix prims A x r q v) :
    q.2.1 ≤ r.2.1 := by
  obtain ⟨top', p, f, -, -, -, hv, hf, rfl⟩ := hpre
  exact (SigningCacheProof.countRun_grows prims _ _ v hv).trans (SigningCacheProof.countRun_grows prims _ _ f hf)

set_option maxRecDepth 100000 in
/-- Outside `OpeningMatch`, the read of `bottomOpened` at the actual start of the verification is
the read on the final cache. It holds for every real decomposition of the run. -/
theorem verificationPrefix_bottomOpened_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C) (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (hn : ¬SigningGuessProof.OpeningMatch prims x (r.1.1, r.2)) :
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    SigningDescentProof.bottomOpened q.2.1 x.1 z.key (z.honestKey prims) =
      SigningDescentProof.bottomOpened r.2.1 x.1 z.key (z.honestKey prims) := by
  have hc := verificationPrefix_selectedCached prims A x r q v hpre top state forgery hm hn
  have hs := verificationPrefix_le prims A x r q v hpre
  cases hrel : (SigningCostProof.finalOf x (r.1.1, r.2) top state forgery).honestKey prims |>.released with
  | false =>
    exact (SigningDescentProof.bottomOpened_of_not_released _ _ _ _ hrel).trans
      (SigningDescentProof.bottomOpened_of_not_released _ _ _ _ hrel).symm
  | true => exact SigningSupportProof.bottomOpened_cache_eq hs _ _ _ (hc hrel)

end SigningGuardedFlagProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.guardedFlag_of_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.guardedFlag_of_win

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.unchargedLaneBoundLogged_of_guardedCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.unchargedLaneBoundLogged_of_guardedCoupling

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.hiddenCoreAt_of_guardedCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.hiddenCoreAt_of_guardedCoupling

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.probEvent_guardedFlag_not_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.probEvent_guardedFlag_not_win

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.partialChainTarget_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.partialChainTarget_absent

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.flaggedOracles_run_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.flaggedOracles_run_flag

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.verificationPrefix_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.verificationPrefix_exists

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.verificationPrefix_bottomOpened_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.verificationPrefix_bottomOpened_eq
