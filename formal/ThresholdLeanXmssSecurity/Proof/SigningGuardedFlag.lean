import ThresholdLeanXmssSecurity.Proof.SigningSelection
import ThresholdLeanXmssSecurity.Proof.SigningReleased

/-!
# The partial chain target and the verification prefix

## The partial chain target

`chainTarget` reads a chain start whose PRF entries are absent as the replay default zero.

* `partialChainTarget` is `none` when a PRF entry of the chain start is absent from the final cache.
* `ForgedStartAbsent` holds when a chain start at the key of the forgery has an absent PRF entry.
  If the bottom tree of the key is never built, the replay data of the bottom key are public zeros.
  Then a forgery that wins at the top layer can still be a bottom Guess.
* `hiddenInputHit_partial` moves a hit on `chainTarget` to `partialChainTarget`, unless
  `ForgedStartAbsent` holds.

## The verification prefix

`VerificationPrefix` is the real decomposition of an outcome of `verifyRun`, with the state `q.2` at
the actual start of the verification. `verificationPrefix_exists` gives it.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningGuardedFlagProof

open HashSig LeanXmss ThresholdLeanXmss SigningOpeningProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)
attribute [local irreducible] MonadAttach.support

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
    rw [ite_eq_left]
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
    rw [ite_eq_left]
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

/-! ## The verification prefix -/

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
        (Verification.verifyWithHash ⟨top.root, x.1⟩ q.1.1.message q.1.1.signature)))).run q.2) ∧
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

end SigningGuardedFlagProof

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningGuardedFlagProof.verificationPrefix_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningGuardedFlagProof.verificationPrefix_exists
