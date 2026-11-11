import ThresholdLeanXmssSecurity.Proof.SigningOpening

/-!
# The Guess half of the uncharged lane

A Guess forges a hidden honest chain value below the opened position. The verification in
`tsigFinish` then calls `H` on that value. This module shows that every Guess raises
`HiddenInputHit` on a log that also holds the verification calls.

## The verification log

* `tsigFinish` runs the verification as honest calls after the adversary, outside
  `openingOracles`. So a Guess can first appear there.
* `loggedTweakable` runs a computation of leanVM under `tweakable` and logs the unreleased
  candidates of its calls in call order. `callCandidates` is the `hash` row of
  `unreleasedCandidates`. It filters with an explicit classical instance, because the kernel does
  not reduce the matcher of `unreleasedCandidates` on a chain input.
* `verifyRun` is `openingRun` whose log ends with the candidates of the verification calls. Its
  outcome type is the type of `openingRun`, so `HiddenInputHit` applies unchanged.
  `verifyRun_forget` gives back `exposedRun` exactly.
* `verifyRun_verification` gives the call-time data of the verification calls. They run at the
  final state of the oracles, their log ends the log of the run, and their cache is below the final
  cache.

## The targets

* `chainTarget` reads the honest chain value below the opened position from the final state, at the
  key of the forgery. It is `none` at an opened position and at every other key.
* A chain value is never released by `Released` (`not_released_bottomChain`,
  `not_released_topChain`). So each verification call on a chain input logs its candidate.

## The link

* `Reads` says that a computation of leanVM, with the answers of a cache, calls `H` on an input.
  `logged_reads` puts the candidates of each such call in the log, for every later cache.
* `reads_verify_chain` and `reads_verify_topChain` walk the verification of leanVM with the
  `CacheReplay` evaluation lemmas. The first step of chain `l` calls `H` on the forged value at the
  forged digit.
* `guess_hiddenInputHit` and `probEvent_guess_le` give the Guess case of
  `SigningGuessProof.winResidual_guess_or_bottomPartner` as a `HiddenInputHit`. The proof does not
  use the win, so `UnchargedWin` only selects the case.

## The top partner

The table of `SigningOpening` lists the top partner as uncharged. The docstring of
`winResidual_guess_or_bottomPartner` says that it is charged. Both are right for their own split.

* `WinResidual` belongs to the split `WinOutput`/`WinResidual`, whose `OutputLaneBound` holds every
  `TopPartner` and stays an open hypothesis.
* The live route is `hiddenCoreAt_of_uncharged`. There `ChargedOutput` holds only
  `ResolvedTopPartner`. `topPartner_resolved` and `uncharged_topPartner_no_successful_bottom` show
  that a top partner with a successful cached bottom ceremony is charged. A top partner without one
  stays in `UnchargedWin`.

## Open problem of the bottom partner

An adversary call of `encodingInput` may carry two uncharged targets. One is the selected
randomness, the base plus `k` with a hidden base (the grind of `Scheme.lean`). The other is the
selected digest. The charged lane already charges each bottom digest call. So one capped flag may
not fit the partner.

leanVM `CappedEncodingActionTrace` charges both orders with one monitor action for each leaf index.
`runObserved_empty_eq_true_of_query_before_sign_of_valid` covers an adversary query whose output
meets a later signed output. `runObserved_empty_eq_true_of_sign_before_query_of_valid` covers a
signed output that a later forged query meets. Both need the valid sign leaf indices to be
distinct, and the monitor fires once for each leaf index.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningGuessLinkProof

open LeanXmss ThresholdLeanXmss SigningOpeningProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The unreleased candidates of a call of `H` on `input`. It is the `hash` row of
`unreleasedCandidates`. -/
def callCandidates (P : PublicParameter) (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    (input : HashInput) : List (HiddenKey × Digest) :=
  (hiddenCandidate P input).toList.filter fun c => @decide (¬Released st trees c.1) (Classical.dec _)

/-- The handler of `tweakable` that also logs the unreleased candidates of each call. -/
def logImpl (P : PublicParameter) (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight))) :
    QueryImpl HashSpec (StateT (List (HiddenKey × Digest)) (OracleComp (RoSpec C))) := fun input =>
  StateT.mk fun log => (fun a => (a, log ++ callCandidates P st trees input)) <$>
    hashQuery (C := C) (.hash input)

/-- A computation of leanVM under `tweakable` that also logs the unreleased candidates of its
calls, in call order. -/
def loggedTweakable (P : PublicParameter) (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    {α : Type} (oa : OracleComp HashSpec α) : OracleComp (RoSpec C) (α × List (HiddenKey × Digest)) :=
  (simulateQ (logImpl P st trees) oa).run []

theorem loggedTweakable_forget (P : PublicParameter) (st : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) {α : Type} (oa : OracleComp HashSpec α) :
    Prod.fst <$> loggedTweakable P st trees oa = tweakable oa := by
  unfold loggedTweakable tweakable logImpl
  generalize ([] : List (HiddenKey × Digest)) = log
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, StateT.run_mk, map_bind, bind_map_left, ih]

/-- `tsigFinish` with the log of the unreleased candidates of the verification calls. -/
def tsigFinishLogged (dealt : Dealt C (OracleComp (WorldSpec C))) (trees : Finset (Fin (2 ^ layerHeight))) :
    Forgery × TsigState C →
      OracleComp (WorldSpec C) ((Bool × TsigState C × Forgery) × List (HiddenKey × Digest))
  | (forgery, st) => do
    let verified ← SigningCoreProof.honestLift (loggedTweakable dealt.parameter st trees
      (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ forgery.message forgery.signature))
    let fresh ← if (signersAt st forgery.signature.leafIndex forgery.message).card < C.t then pure true else do
      let honest ← honestSignature (fun oa => SigningCoreProof.honestLift oa) dealt
        forgery.signature.leafIndex forgery.message
      pure (decide (honest ≠ some forgery.signature))
    pure ((verified.1 && fresh, st, forgery), verified.2)

theorem tsigFinishLogged_forget (dealt : Dealt C (OracleComp (WorldSpec C)))
    (trees : Finset (Fin (2 ^ layerHeight))) (p : Forgery × TsigState C) :
    Prod.fst <$> tsigFinishLogged dealt trees p = SigningCoreProof.tsigFinish dealt p := by
  rcases p with ⟨forgery, st⟩
  unfold tsigFinishLogged SigningCoreProof.tsigFinish
  dsimp only
  have h : SigningCoreProof.honestLift (tweakable (C := C)
      (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ forgery.message forgery.signature)) =
      Prod.fst <$> SigningCoreProof.honestLift (loggedTweakable dealt.parameter st trees
        (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ forgery.message forgery.signature)) := by
    rw [← loggedTweakable_forget dealt.parameter st trees]
    unfold SigningCoreProof.honestLift worldRoles free
    dsimp only
    rw [liftComp_map]
    exact simulateQ_map _ _ _
  rw [h, bind_map_left, map_bind]
  refine bind_congr fun v => ?_
  split_ifs <;> simp

/-- `openingFinal` whose log also holds the unreleased candidates of the verification calls, after
the candidates of the adversary calls. -/
def verifyFinal (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    OracleComp (WorldSpec C)
      (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa)) value x.1 emptyTop .top
    | pure (((false, false), none), [])
  let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (openingOracles x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
    ((SigningCoreProof.tsigInit, false), ∅, [])
  (fun w => (((w.1.1, r.2.1.2), some (top, w.1.2.1, w.1.2.2)), r.2.2.2 ++ w.2)) <$>
    tsigFinishLogged dealt r.2.2.1 (r.1, r.2.1.1)

theorem verifyFinal_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Prod.fst <$> verifyFinal A x = SigningDescentProof.finalRun A x := by
  unfold verifyFinal SigningDescentProof.finalRun
  rw [map_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp
  · simp only [map_bind, Functor.map_map]
    rw [← SigningCoreProof.simulateQ_run_forget _ _ (openingOracles_forget x _) _ _ (∅, []), bind_map_left]
    refine bind_congr fun r => ?_
    rw [← tsigFinishLogged_forget _ r.2.2.1, Functor.map_map]
  · simp

/-- `exposedRun` with the log of the unreleased candidates of the adversary calls and of the
verification calls. -/
def verifyRun (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp ((((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ) :=
  (simulateQ (SeedHitProof.withCount (SeedHitProof.signImpl prims)) (verifyFinal A x)).run ((∅ : HashCache C), 0)

theorem verifyRun_forget (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun r => (r.1.1, r.2)) <$> verifyRun prims A x = SigningDescentProof.exposedRun prims A x := by
  unfold verifyRun SigningDescentProof.exposedRun
  rw [← verifyFinal_forget, simulateQ_map, StateT.run_map]

/-- A computation of leanVM, run with the answers of a cache, calls `H` on an input. -/
inductive Reads (cache : QueryCache XmssSecurity.HashSpec) {α : Type} :
    OracleComp XmssSecurity.HashSpec α → XmssSecurity.HashInput → Prop
  | here (input : XmssSecurity.HashInput) (next : XmssSecurity.HashOutput → OracleComp XmssSecurity.HashSpec α) :
      Reads cache (liftM (XmssSecurity.HashSpec.query input) >>= next) input
  | later (input : XmssSecurity.HashInput) (next : XmssSecurity.HashOutput → OracleComp XmssSecurity.HashSpec α)
      (other : XmssSecurity.HashInput)
      (tail : Reads cache (next (XmssSecurity.Concrete.CacheReplay.answer cache input)) other) :
      Reads cache (liftM (XmssSecurity.HashSpec.query input) >>= next) other

theorem Reads.bind_left {cache : QueryCache XmssSecurity.HashSpec} {α β : Type}
    {oa : OracleComp XmssSecurity.HashSpec α} {input : XmssSecurity.HashInput} (h : Reads cache oa input)
    (f : α → OracleComp XmssSecurity.HashSpec β) : Reads cache (oa >>= f) input := by
  induction h with
  | here x next => rw [bind_assoc]; exact .here x _
  | later x next other _ ih => rw [bind_assoc]; exact .later x _ other ih

theorem Reads.bind_right {cache : QueryCache XmssSecurity.HashSpec} {α β : Type}
    (oa : OracleComp XmssSecurity.HashSpec α) (f : α → OracleComp XmssSecurity.HashSpec β)
    {input : XmssSecurity.HashInput}
    (h : Reads cache (f (evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn cache) oa)) input) :
    Reads cache (oa >>= f) input := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h
  | query_bind x k ih =>
    rw [bind_assoc]
    refine .later x _ input (ih _ ?_)
    rw [evalWithAnswerFn_bind] at h
    have hq : evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn cache)
        (liftM (OracleSpec.query x) : OracleComp XmssSecurity.HashSpec _) =
        XmssSecurity.Concrete.CacheReplay.answer cache x :=
      evalWithAnswerFn_query (XmssSecurity.Concrete.CacheReplay.answerFn cache) x
    rw [hq] at h
    exact h

section LogRun

variable (prims : Primitives) (P : PublicParameter) (st : TsigState C)
  (trees : Finset (Fin (2 ^ layerHeight)))

/-- The run of a logged call. The answer is in the cache, the cache grows, and the log gets the
candidates of the call. -/
theorem logged_query_support {α : Type} (input : XmssSecurity.HashInput)
    (next : XmssSecurity.HashOutput → OracleComp HashSpec α) (log : List (HiddenKey × Digest))
    (s : HashCache C × ℕ) (z : (α × List (HiddenKey × Digest)) × HashCache C × ℕ)
    (hz : z ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
      ((simulateQ (logImpl P st trees) (liftM (HashSpec.query input) >>= next)).run log))).run s)) :
    ∃ p : HashOutput × HashCache C × ℕ, p.2.1 (.hash input) = some p.1 ∧ s.1 ≤ p.2.1 ∧
      z ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
        ((simulateQ (logImpl P st trees) (next p.1)).run
          (log ++ callCandidates P st trees input)))).run p.2) := by
  have heq : (simulateQ (logImpl P st trees) (liftM (HashSpec.query input) >>= next)).run log =
      hashQuery (C := C) (.hash input) >>= fun a => (simulateQ (logImpl P st trees) (next a)).run
        (log ++ callCandidates P st trees input) := by
    simp [logImpl]
  rw [heq, SigningSecurityProof.liftFree, liftComp_bind, free_bind] at hz
  obtain ⟨p, hp, hz⟩ := SigningCacheProof.run_bind_support prims _ _ s z hz
  exact ⟨p, SigningCacheProof.run_hashQuery prims _ s p hp, SigningCacheProof.countRun_grows prims _ s p hp, hz⟩

/-- A logged run only appends to its log. -/
theorem logged_prefix {α : Type} (oa : OracleComp HashSpec α) :
    ∀ log s, ∀ z ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
      ((simulateQ (logImpl P st trees) oa).run log))).run s), ∃ rest, z.1.2 = log ++ rest := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log s z hz
    simp [SigningSecurityProof.liftFree, free] at hz
    subst hz
    exact ⟨[], by simp⟩
  | query_bind x k ih =>
    intro log s z hz
    obtain ⟨p, -, -, hz⟩ := logged_query_support prims P st trees x k log s z hz
    obtain ⟨rest, hrest⟩ := ih p.1 _ p.2 z hz
    exact ⟨callCandidates P st trees x ++ rest, by rw [hrest, List.append_assoc]⟩

/-- Every call of a logged run with the answers of a later cache has its candidates in the log. -/
theorem logged_reads (cache : HashCache C) {α : Type} {oa : OracleComp HashSpec α}
    {input : XmssSecurity.HashInput} (h : Reads (SigningDescentProof.thView cache) oa input) :
    ∀ log s, ∀ z ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
      ((simulateQ (logImpl P st trees) oa).run log))).run s), z.2.1 ≤ cache →
      ∀ c ∈ callCandidates P st trees input, c ∈ z.1.2 := by
  induction h with
  | here x next =>
    intro log s z hz _ c hc
    obtain ⟨p, -, -, hz⟩ := logged_query_support prims P st trees x next log s z hz
    obtain ⟨rest, hrest⟩ := logged_prefix prims P st trees _ _ p.2 z hz
    rw [hrest]
    simp [hc]
  | later x next other _ ih =>
    intro log s z hz hle c hc
    obtain ⟨p, hp, -, hz⟩ := logged_query_support prims P st trees x next log s z hz
    have hcache : cache (.hash x) = some p.1 :=
      hle (SigningCacheProof.countRun_grows prims _ p.2 z hz hp)
    have hanswer : XmssSecurity.Concrete.CacheReplay.answer (SigningDescentProof.thView cache) x = p.1 := by
      simp only [XmssSecurity.Concrete.CacheReplay.answer, SigningDescentProof.thView, hcache]
      rfl
    rw [hanswer] at ih
    exact ih _ p.2 z hz hle c hc

end LogRun

section VerifyReads

variable (cache : QueryCache XmssSecurity.HashSpec)

theorem reads_sequenceFin {α : Type} {n : ℕ} (computation : Fin n → OracleComp XmssSecurity.HashSpec α)
    (i : Fin n) {input : XmssSecurity.HashInput} (h : Reads cache (computation i) input) :
    Reads cache (XmssSecurity.Concrete.sequenceFin computation) input := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    unfold XmssSecurity.Concrete.sequenceFin
    refine Fin.cases ?_ (fun j hj => ?_) i h
    · intro h0
      exact h0.bind_left _
    · exact Reads.bind_right _ _ ((ih _ j hj).bind_left _)

/-- The first step of a walk from position `p` calls `H` on the chain input at `p`. -/
theorem reads_chainWalk (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) (p : ℕ) (hp : p < XmssSecurity.chainLength - 1) (v : XmssSecurity.Digest) :
    ∀ steps, Reads cache (XmssSecurity.Concrete.chainWalk P e l p (steps + 1) v)
      (XmssSecurity.Concrete.CacheView.chainInput P e l ⟨p, hp⟩ v)
  | 0 => by
    unfold XmssSecurity.Concrete.chainWalk
    refine Reads.bind_right _ _ ?_
    simp only [XmssSecurity.Concrete.chainWalk, evalWithAnswerFn_pure, Nat.add_zero, hp, dif_pos]
    exact Reads.bind_left (.here _ _) _
  | steps + 1 => by
    unfold XmssSecurity.Concrete.chainWalk
    exact (reads_chainWalk P e l p hp v steps).bind_left _

/-- The verification calls `H` on the first step of each bottom chain below the end. -/
theorem reads_verify_chain (pk : XmssSecurity.PublicKey) (e : XmssSecurity.LeafIndex)
    (m : XmssSecurity.Message) (σ : XmssSecurity.Signature) (encoding : XmssSecurity.Encoding)
    (hdecode : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash cache pk.parameter e (m, σ.randomness)) = some encoding)
    (l : XmssSecurity.ChainIndex) (h : (encoding l).val < XmssSecurity.chainLength - 1) :
    Reads cache (XmssSecurity.Concrete.verify pk e m σ)
      (XmssSecurity.Concrete.CacheView.chainInput pk.parameter e l ⟨(encoding l).val, h⟩ (σ.chainValue l)) := by
  unfold XmssSecurity.Concrete.verify
  refine Reads.bind_right _ _ ?_
  rw [XmssSecurity.Concrete.CacheReplay.eval_encodingHash, hdecode]
  refine Reads.bind_left ?_ _
  unfold XmssSecurity.Concrete.recoverEndpoints
  refine reads_sequenceFin cache _ l ?_
  unfold XmssSecurity.Concrete.recoverChain
  have hsteps : XmssSecurity.chainLength - 1 - (encoding l).val =
      (XmssSecurity.chainLength - 1 - (encoding l).val - 1) + 1 := by omega
  rw [hsteps]
  exact reads_chainWalk cache _ _ _ _ h _ _

/-- The first step of a top walk from position `p` calls `H` on the top chain input at `p`. -/
theorem reads_topChainWalk (P : XmssSecurity.PublicParameter) (b : XmssSecurity.TopIndex)
    (l : XmssSecurity.ChainIndex) (p : ℕ) (hp : p < XmssSecurity.chainLength - 1) (v : XmssSecurity.Digest) :
    ∀ steps, Reads cache (XmssSecurity.Concrete.topChainWalk P b l p (steps + 1) v)
      (XmssSecurity.Concrete.CacheView.topChainInput P b l ⟨p, hp⟩ v)
  | 0 => by
    unfold XmssSecurity.Concrete.topChainWalk
    refine Reads.bind_right _ _ ?_
    simp only [XmssSecurity.Concrete.topChainWalk, evalWithAnswerFn_pure, Nat.add_zero, hp, dif_pos]
    exact Reads.bind_left (.here _ _) _
  | steps + 1 => by
    unfold XmssSecurity.Concrete.topChainWalk
    exact (reads_topChainWalk P b l p hp v steps).bind_left _

/-- The verification calls `H` on the first step of each top chain below the end. -/
theorem reads_verify_topChain (pk : XmssSecurity.PublicKey) (e : XmssSecurity.LeafIndex)
    (m : XmssSecurity.Message) (σ : XmssSecurity.Signature) (encoding : XmssSecurity.Encoding)
    (hdecode : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash cache pk.parameter e (m, σ.randomness)) = some encoding)
    (topCodeword : XmssSecurity.Encoding)
    (htop : XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.topEncodingHash cache pk.parameter (XmssSecurity.topKeyOf e)
        (XmssSecurity.Merkle.ascend (XmssSecurity.Concrete.CacheView.nodeHash cache pk.parameter e)
          (XmssSecurity.Concrete.signaturePath σ) 0 XmssSecurity.treeHeight
          (XmssSecurity.Concrete.CacheView.leafHash cache pk.parameter e
            (XmssSecurity.recoveredEndpoints
              (fun chain => XmssSecurity.Concrete.CacheView.chainStep cache pk.parameter e chain)
              encoding σ.chainValue)), σ.top.randomness)) = some topCodeword)
    (l : XmssSecurity.ChainIndex) (h : (topCodeword l).val < XmssSecurity.chainLength - 1) :
    Reads cache (XmssSecurity.Concrete.verify pk e m σ)
      (XmssSecurity.Concrete.CacheView.topChainInput pk.parameter (XmssSecurity.topKeyOf e) l
        ⟨(topCodeword l).val, h⟩ (σ.top.chainValue l)) := by
  unfold XmssSecurity.Concrete.verify
  refine Reads.bind_right _ _ ?_
  rw [XmssSecurity.Concrete.CacheReplay.eval_encodingHash, hdecode]
  refine Reads.bind_right _ _ ?_
  rw [XmssSecurity.Concrete.CacheReplay.eval_recoverEndpoints]
  refine Reads.bind_right _ _ ?_
  rw [XmssSecurity.Concrete.CacheReplay.eval_leafHash]
  unfold XmssSecurity.Concrete.verifyAfterLeaf
  refine Reads.bind_right _ _ ?_
  rw [XmssSecurity.Concrete.CacheReplay.eval_authenticationRoot]
  unfold XmssSecurity.Concrete.verifyTop
  refine Reads.bind_right _ _ ?_
  have hdigest : ∀ root, evalWithAnswerFn (XmssSecurity.Concrete.CacheReplay.answerFn cache)
      (XmssSecurity.Concrete.topEncodingHash pk.parameter (XmssSecurity.topKeyOf e) root σ.top.randomness :
        OracleComp XmssSecurity.HashSpec XmssSecurity.Digest) =
      XmssSecurity.Concrete.CacheView.topEncodingHash cache pk.parameter (XmssSecurity.topKeyOf e)
        (root, σ.top.randomness) := by
    intro root
    simp [XmssSecurity.Concrete.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingHash,
      XmssSecurity.Concrete.CacheView.topEncodingInput, XmssSecurity.Concrete.CacheView.tweakableHash]
  rw [hdigest, htop]
  refine Reads.bind_left ?_ _
  refine reads_sequenceFin cache _ l ?_
  have hsteps : XmssSecurity.chainLength - 1 - (topCodeword l).val =
      (XmssSecurity.chainLength - 1 - (topCodeword l).val - 1) + 1 := by omega
  rw [hsteps]
  exact reads_topChainWalk cache _ _ _ _ h _ _

end VerifyReads

section Candidates

/-- Randomizer addresses are distinct from every verification hash domain, as
`SigningGuessProof.commitmentInput_ne_tweakableHashInput`. -/
theorem randomizerInput_ne_tweakableHashInput
    (P P' : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest) (m : HashInput)
    (domain : HashDomain) (payload : HashInput) :
    randomizerInput P lay e ρ m ≠ tweakableHashInput P' domain payload := by
  intro h
  have hf := (fieldInput_injective
    (payload := bytesLE 16 ρ ++ m)
    (payload' := payload)
    (by simpa only [randomizerInput, tweakableHashInput, tweakBytes,
      List.append_assoc] using h)).1
  have ht := congrArg (fun f => f.tag.toNat) hf
  cases domain <;> norm_num [hashDomainFields, tweakFields] at ht

theorem chainInput_eq_bridge (P : PublicParameter) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (v : Digest) :
    XmssSecurity.Concrete.CacheView.chainInput P e l p v =
      tweakableHashInput P (.chain bottomLayer e p) (Concrete.chainPayload l v) :=
  (XmssSecurity.Bridge.chain_input P e l p v).symm

theorem topChainInput_eq_bridge (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (v : Digest) :
    XmssSecurity.Concrete.CacheView.topChainInput P b l p v =
      tweakableHashInput P (.chain topLayer (topKey b) p) (Concrete.chainPayload l v) :=
  (XmssSecurity.Bridge.topChain_input P b l p v).symm

theorem hiddenCandidate_chainInput (P : PublicParameter) (e : XmssSecurity.LeafIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (v : Digest) :
    hiddenCandidate P (XmssSecurity.Concrete.CacheView.chainInput P e l p v) = some (.bottomChain e l p, v) := by
  unfold hiddenCandidate
  rw [dif_neg (by
    rintro ⟨f, ρ, h⟩
    rw [chainInput_eq_bridge] at h
    exact SigningGuessProof.commitmentInput_ne_tweakableHashInput _ _ _ _ _ _ h.symm)]
  rw [dif_neg (by
    rintro ⟨lay, f, ρ, m, h⟩
    rw [chainInput_eq_bridge] at h
    exact randomizerInput_ne_tweakableHashInput _ _ _ _ _ _ _ _ h.symm)]
  have hex : ∃ e' l' p' v', XmssSecurity.Concrete.CacheView.chainInput P e l p v =
      XmssSecurity.Concrete.CacheView.chainInput P e' l' p' v' := ⟨e, l, p, v, rfl⟩
  rw [dif_pos hex]
  have hspec := hex.choose_spec.choose_spec.choose_spec.choose_spec
  have hd := XmssSecurity.domain_eq_of_tweakableHashInput_eq P hspec
  simp only [XmssSecurity.HashDomain.chain.injEq] at hd
  obtain ⟨he, hl, hp⟩ := hd
  have hv : v = hex.choose_spec.choose_spec.choose_spec.choose := by
    refine XmssSecurity.Concrete.CacheView.chainInput_injective P e l p ?_
    convert hspec using 2
  simp only [Option.some.injEq, Prod.mk.injEq, HiddenKey.bottomChain.injEq]
  exact ⟨⟨he.symm, hl.symm, hp.symm⟩, hv.symm⟩

theorem hiddenCandidate_topChainInput (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) (v : Digest) :
    hiddenCandidate P (XmssSecurity.Concrete.CacheView.topChainInput P b l p v) = some (.topChain b l p, v) := by
  unfold hiddenCandidate
  rw [dif_neg (by
    rintro ⟨f, ρ, h⟩
    rw [topChainInput_eq_bridge] at h
    exact SigningGuessProof.commitmentInput_ne_tweakableHashInput _ _ _ _ _ _ h.symm)]
  rw [dif_neg (by
    rintro ⟨lay, f, ρ, m, h⟩
    rw [topChainInput_eq_bridge] at h
    exact randomizerInput_ne_tweakableHashInput _ _ _ _ _ _ _ _ h.symm)]
  rw [dif_neg (by
    rintro ⟨e, l', p', v', h⟩
    have hd := XmssSecurity.domain_eq_of_tweakableHashInput_eq P h
    cases hd)]
  have hex : ∃ b' l' p' v', XmssSecurity.Concrete.CacheView.topChainInput P b l p v =
      XmssSecurity.Concrete.CacheView.topChainInput P b' l' p' v' := ⟨b, l, p, v, rfl⟩
  rw [dif_pos hex]
  have hspec := hex.choose_spec.choose_spec.choose_spec.choose_spec
  have hd := XmssSecurity.domain_eq_of_tweakableHashInput_eq P hspec
  simp only [XmssSecurity.HashDomain.topChain.injEq] at hd
  obtain ⟨hb, hl, hp⟩ := hd
  have hv : v = hex.choose_spec.choose_spec.choose_spec.choose := by
    apply XmssSecurity.Concrete.digestBytes_injective
    refine XmssSecurity.payload_eq_of_tweakableHashInput_eq P (.topChain b l p) ?_
    convert hspec using 2
    · rfl
    · unfold XmssSecurity.Concrete.CacheView.topChainInput
      exact congrArg (fun d => XmssSecurity.tweakableHashInput P d _)
        ((XmssSecurity.HashDomain.topChain.injEq _ _ _ _ _ _).mpr ⟨hb, hl, hp⟩)
  simp only [Option.some.injEq, Prod.mk.injEq, HiddenKey.topChain.injEq]
  exact ⟨⟨hb.symm, hl.symm, hp.symm⟩, hv.symm⟩

theorem not_released_bottomChain (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) :
    ¬Released st trees (HiddenKey.bottomChain e l p) := by
  rw [Released.eq_2]
  · exact id
  · exact fun _ _ h => HiddenKey.noConfusion h

theorem not_released_topChain (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep) :
    ¬Released st trees (HiddenKey.topChain b l p) := by
  rw [Released.eq_2]
  · exact id
  · exact fun _ _ h => HiddenKey.noConfusion h

theorem callCandidates_chainInput (P : PublicParameter) (st : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex)
    (p : XmssSecurity.ChainStep) (v : Digest) :
    callCandidates P st trees (XmssSecurity.Concrete.CacheView.chainInput P e l p v) =
      [(.bottomChain e l p, v)] := by
  unfold callCandidates
  rw [hiddenCandidate_chainInput, Option.toList_some]
  exact List.filter_cons_of_pos (@decide_eq_true _ (Classical.dec _) (not_released_bottomChain st trees e l p))

theorem callCandidates_topChainInput (P : PublicParameter) (st : TsigState C)
    (trees : Finset (Fin (2 ^ layerHeight))) (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex)
    (p : XmssSecurity.ChainStep) (v : Digest) :
    callCandidates P st trees (XmssSecurity.Concrete.CacheView.topChainInput P b l p v) =
      [(.topChain b l p, v)] := by
  unfold callCandidates
  rw [hiddenCandidate_topChainInput, Option.toList_some]
  exact List.filter_cons_of_pos (@decide_eq_true _ (Classical.dec _) (not_released_topChain st trees b l p))

end Candidates

section Run

variable (prims : Primitives)

theorem tsigFinishLogged_eq (dealt : Dealt C (OracleComp (WorldSpec C)))
    (trees : Finset (Fin (2 ^ layerHeight))) (forgery : Forgery) (st : TsigState C) :
    tsigFinishLogged dealt trees (forgery, st) =
      SigningCoreProof.honestLift (loggedTweakable dealt.parameter st trees
        (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ forgery.message forgery.signature)) >>= fun v =>
        (fun fresh => ((v.1 && fresh, st, forgery), v.2)) <$>
          (if (signersAt st forgery.signature.leafIndex forgery.message).card < C.t then pure true else
            (fun honest => decide (honest ≠ some forgery.signature)) <$>
              honestSignature (fun oa => SigningCoreProof.honestLift oa) dealt
                forgery.signature.leafIndex forgery.message) := by
  unfold tsigFinishLogged
  refine bind_congr fun v => ?_
  split_ifs <;> simp

set_option maxRecDepth 100000 in
/-- The verification calls of a run of `verifyRun`. They run at the final state of the oracles,
their log ends the log of the run, and their cache is below the final cache. -/
theorem verifyRun_verification (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ)
    (hr : r ∈ support (verifyRun prims A x)) (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    ∃ (trees : Finset (Fin (2 ^ layerHeight))) (adversaryLog : List (HiddenKey × Digest))
      (s : HashCache C × ℕ) (v : (Bool × List (HiddenKey × Digest)) × HashCache C × ℕ),
      v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
        (loggedTweakable x.1 state trees
          (Concrete.verify ⟨top.root, x.1⟩ forgery.message forgery.signature)))).run s) ∧
      r.1.2 = adversaryLog ++ v.1.2 ∧ v.2.1 ≤ r.2.1 := by
  unfold verifyRun verifyFinal at hr
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
  rw [tsigFinishLogged_eq] at hw
  obtain ⟨v, hv, hw⟩ := SigningCacheProof.run_bind_support prims _ _ _ w hw
  rw [simulateQ_map, StateT.run_map, support_map] at hw
  obtain ⟨f, hf, rfl⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  exact ⟨_, _, _, v, hv, rfl, SigningCacheProof.countRun_grows prims _ _ f hf⟩

/-- Every call that the verification makes with the answers of a later cache has its candidates
in the log of the verification. -/
theorem verification_reads (P : PublicParameter) (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    (root : Digest) (forgery : Forgery) (s : HashCache C × ℕ)
    (v : (Bool × List (HiddenKey × Digest)) × HashCache C × ℕ)
    (hv : v ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
        (loggedTweakable P st trees (Concrete.verify ⟨root, P⟩ forgery.message forgery.signature)))).run s))
    (cache : HashCache C) (hle : v.2.1 ≤ cache) {input : XmssSecurity.HashInput}
    (h : Reads (SigningDescentProof.thView cache)
      (XmssSecurity.Concrete.verify (XmssSecurity.Bridge.toModelPk ⟨root, P⟩) forgery.signature.leafIndex
        forgery.message (XmssSecurity.Bridge.toModelSig forgery.signature)) input) :
    ∀ c ∈ callCandidates P st trees input, c ∈ v.1.2 := by
  unfold loggedTweakable at hv
  rw [XmssSecurity.Bridge.verify_real] at hv
  exact logged_reads prims P st trees cache h [] s v hv hle

end Run

section Target

variable (prims : Primitives)

/-- An outcome of `verifyRun`. -/
abbrev LoggedOutcome (C : Committee) :=
  (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) × HashCache C × ℕ

/-- The chain targets of an outcome. A chain value at the key of the forgery has the honest value
below the opened position as its target. The opened position and every other key have none. -/
def chainTarget (x : SigningSecurityProof.Keys3 C) (r : LoggedOutcome C) : HiddenKey → Option Digest :=
  match r.1.1.2 with
  | none => fun _ => none
  | some (top, state, forgery) =>
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    let hk := z.honestKey prims
    fun
    | .opening _ _ => none
    | .bottomChain e l p =>
      if e = z.key ∧ p.val < SigningDescentProof.bottomOpened z.cache x.1 z.key hk l then
        some (SigningDescentProof.honestValue (SigningDescentProof.bottomStep z.cache x.1 z.key) hk.secret l p.val)
      else none
    | .topChain b l p =>
      if b = XmssSecurity.topKeyOf z.key ∧ p.val < SigningDescentProof.topOpened z.cache x.1 z.key hk l then
        some (SigningDescentProof.honestValue (SigningDescentProof.topStep z.cache x.1 z.key) hk.topSecret l p.val)
      else none

theorem bottomOpened_le (c : HashCache C) (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex)
    (hk : SigningDescentProof.HonestKey) (l : XmssSecurity.ChainIndex) :
    SigningDescentProof.bottomOpened c P e hk l ≤ XmssSecurity.chainLength - 1 := by
  unfold SigningDescentProof.bottomOpened
  split
  · exact Nat.le_pred_of_lt (Fin.isLt _)
  · exact le_rfl

theorem topOpened_le (c : HashCache C) (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex)
    (hk : SigningDescentProof.HonestKey) (l : XmssSecurity.ChainIndex) :
    SigningDescentProof.topOpened c P e hk l ≤ XmssSecurity.chainLength - 1 := by
  unfold SigningDescentProof.topOpened
  split
  · exact Nat.le_pred_of_lt (Fin.isLt _)
  · exact le_rfl

set_option maxRecDepth 100000 in
/-- A guess of the forgery is an input-side hit of a verification call on its chain target. -/
theorem guess_hiddenInputHit (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (r : LoggedOutcome C)
    (hr : r ∈ support (verifyRun prims A x)) (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery))
    (hguess : let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
      SigningDescentProof.Guess z.cache x.1 z.key (z.honestKey prims) forgery.message
        (XmssSecurity.Bridge.toModelSig forgery.signature)) :
    HiddenInputHit x (chainTarget prims x r) r := by
  obtain ⟨trees, adversaryLog, s, v, hv, hlog, hle⟩ :=
    verifyRun_verification prims A x r hr top state forgery hm
  obtain ⟨encoding, hdecode, hbottom | ⟨topCodeword, htop, htopGuess⟩⟩ := hguess
  · obtain ⟨l, hlt, hvalue⟩ := hbottom
    have hd : (encoding l).val < XmssSecurity.chainLength - 1 :=
      lt_of_lt_of_le hlt (bottomOpened_le _ _ _ _ l)
    have hreads := reads_verify_chain (SigningDescentProof.thView r.2.1)
      (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩) forgery.signature.leafIndex forgery.message
      (XmssSecurity.Bridge.toModelSig forgery.signature) encoding hdecode l hd
    have hmem := verification_reads prims x.1 state trees top.root forgery s v hv r.2.1 hle hreads
    have hc : ((.bottomChain forgery.signature.leafIndex l ⟨_, hd⟩ : HiddenKey),
        (XmssSecurity.Bridge.toModelSig forgery.signature).chainValue l) ∈ v.1.2 := by
      refine hmem _ ?_
      rw [show (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩).parameter = x.1 from rfl,
        callCandidates_chainInput]
      exact List.mem_singleton_self _
    refine ⟨_, hlog ▸ List.mem_append_right adversaryLog hc, ?_⟩
    simp only [hiddenTarget, chainTarget, hm]
    rw [if_pos ⟨rfl, hlt⟩]
    exact congrArg some hvalue.symm
  · obtain ⟨l, hlt, hvalue⟩ := htopGuess
    have hd : (topCodeword l).val < XmssSecurity.chainLength - 1 :=
      lt_of_lt_of_le hlt (topOpened_le _ _ _ _ l)
    have hreads := reads_verify_topChain (SigningDescentProof.thView r.2.1)
      (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩) forgery.signature.leafIndex forgery.message
      (XmssSecurity.Bridge.toModelSig forgery.signature) encoding hdecode topCodeword htop l hd
    have hmem := verification_reads prims x.1 state trees top.root forgery s v hv r.2.1 hle hreads
    have hc : ((.topChain (XmssSecurity.topKeyOf forgery.signature.leafIndex) l ⟨_, hd⟩ : HiddenKey),
        (XmssSecurity.Bridge.toModelSig forgery.signature).top.chainValue l) ∈ v.1.2 := by
      refine hmem _ ?_
      rw [show (XmssSecurity.Bridge.toModelPk ⟨top.root, x.1⟩).parameter = x.1 from rfl,
        callCandidates_topChainInput]
      exact List.mem_singleton_self _
    refine ⟨_, hlog ▸ List.mem_append_right adversaryLog hc, ?_⟩
    simp only [hiddenTarget, chainTarget, hm]
    rw [if_pos ⟨rfl, hlt⟩]
    exact congrArg some hvalue.symm

/-- The Guess case of `SigningGuessProof.winResidual_guess_or_bottomPartner` on an outcome of
`exposedRun`. -/
def GuessCase (x : SigningSecurityProof.Keys3 C) (r : SigningCostProof.Outcome C) : Prop :=
  ∃ top state forgery, r.1.2 = some (top, state, forgery) ∧
    let z := SigningCostProof.finalOf x r top state forgery
    SigningDescentProof.Guess z.cache x.1 z.key (z.honestKey prims) forgery.message
      (XmssSecurity.Bridge.toModelSig forgery.signature)

set_option maxRecDepth 100000 in
/-- An uncharged win in the Guess case raises the input-side flag on the extended log. The win is
not needed, so the claim holds for every Guess. -/
theorem probEvent_guess_le (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Pr[fun r => SigningGuessProof.UnchargedWin prims x r ∧ GuessCase prims x r |
        SigningDescentProof.exposedRun prims A x] ≤
      Pr[fun r => HiddenInputHit x (chainTarget prims x r) r | verifyRun prims A x] := by
  rw [← verifyRun_forget, probEvent_map]
  refine probEvent_mono fun r hr h => ?_
  obtain ⟨top, state, forgery, hm, hguess⟩ := h.2
  exact guess_hiddenInputHit prims A x r hr top state forgery hm hguess

end Target

end SigningGuessLinkProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessLinkProof.verifyRun_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessLinkProof.verifyRun_forget

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessLinkProof.guess_hiddenInputHit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessLinkProof.guess_hiddenInputHit

/--
info: 'ThresholdLeanXmssSecurity.SigningGuessLinkProof.probEvent_guess_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningGuessLinkProof.probEvent_guess_le
