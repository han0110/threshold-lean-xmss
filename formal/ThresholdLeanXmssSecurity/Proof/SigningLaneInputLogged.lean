import ThresholdLeanXmssSecurity.Proof.SigningLaneUnion

/-!
# Input-side signing hits reconstructed from the call log

Opening targets read PRF entries, and chain targets read PRF and ordinary hash entries.
The bottom-tree replay used by the unopened-top test and the charged-event test
have the same restriction.
Consequently the input-side row is unchanged when a cache is replaced by any cache
that agrees at all tracked inputs, including the cache reconstructed from its log.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section

namespace ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof

open SigningOpeningProof SigningGuardedFlagProof SigningGuessLinkProof SigningDescentProof
  SigningCacheLogProof SigningPartnerTransferProof SigningFlatEagerProof SigningTopRowsProof
  SigningUnchargedLoggedProof SigningAssemblyProof SigningLinkPaidProof SigningLaneUnionProof

attribute [local instance] Classical.propDecidable
variable {C : Committee} (prims : Primitives)

/-- Opening reconstruction reads only the PRF entries of its terms. -/
theorem cachedOpening_eq (x : SigningSecurityProof.Keys3 C) (key : OpeningKey)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    cachedOpening x a key = cachedOpening x b key := by
  unfold cachedOpening
  have hf : (fun T : C.Term => truncateHash <$> a (.prf (x.2.1 T) (.randomizer key.1 key.2))) =
      (fun T : C.Term => truncateHash <$> b (.prf (x.2.1 T) (.randomizer key.1 key.2))) := by
    funext T
    rw [h _ (tracked_prf _ _)]
  rw [hf]

theorem startsCached_congr (x : SigningSecurityProof.Keys3 C) (lay : Layer)
    (e : KeyIndex) (l : ChainIndex) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) : StartsCached x a lay e l ↔ StartsCached x b lay e l := by
  simp only [StartsCached, h _ (tracked_prf _ _)]

theorem keyStartsCached_congr (x : SigningSecurityProof.Keys3 C) (key : HiddenKey)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    KeyStartsCached x a key ↔ KeyStartsCached x b key := by
  cases key with
  | opening lay e => rfl
  | bottomChain e l p => exact startsCached_congr x _ _ _ h
  | topChain b l p => exact startsCached_congr x _ _ _ h

theorem bottomStep_eq {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q)
    (P : PublicParameter) (e : KeyIndex) : bottomStep a P e = bottomStep b P e := by
  unfold bottomStep
  rw [thView_eq h]

theorem topStep_eq {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q)
    (P : PublicParameter) (e : KeyIndex) : topStep a P e = topStep b P e := by
  unfold topStep
  rw [thView_eq h]

/-- Selected chain positions and values depend only on tracked entries. -/
theorem chainTarget_eq (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (candidates : List (HiddenKey × Digest)) (n : ℕ) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    chainTarget prims x ((r, candidates), a, n) = chainTarget prims x ((r, candidates), b, n) := by
  simp only [chainTarget, SigningCostProof.finalOf, honestKey_eq prims x _ _ _ h,
    FinalState.key, bottomOpened, topOpened, selectedEncoding, topEncoding,
    topSignedInput, honestRoot, bottomStep_eq h, topStep_eq h, thView_eq h]

theorem partialChainTarget_eq (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (candidates : List (HiddenKey × Digest)) (n : ℕ) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    partialChainTarget prims x ((r, candidates), a, n) =
      partialChainTarget prims x ((r, candidates), b, n) := by
  funext key
  simp only [partialChainTarget, keyStartsCached_congr x key h, chainTarget_eq prims x r candidates n h]

/-- Reference trees contain no stream-key oracle calls. -/
theorem referenceTree_tracked (x : SigningSecurityProof.Keys3 C) (top : TopTree) (tree : Tree) :
    TrackedOnly (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1)
      x.1 top tree) := by
  have hrun (jobs : List Job) : IsQueryBoundP
      (some <$> jobs.mapM (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1))
      (fun q => ¬Tracked q) 0 := by
    apply (isQueryBoundP_map_iff _ _ _).2
    apply SigningHitProof.mapM_bound_zero
    intro job
    exact referenceJob_tracked x job
  have hhash {α : Type} (source : OracleComp HashSpec α) :
      IsQueryBoundP (SigningHitProof.forestHash (C := C) source) (fun q => ¬Tracked q) 0 :=
    forestHash_tracked source
  unfold referenceTree ceremonyOutput TrackedOnly
  cases tree with
  | top =>
    with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hrun topJobs) ?_
    intro outputs _
    cases outputs with
    | none => simp
    | some outputs =>
      with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hhash _) ?_
      intro _ _; simp
  | bottom b =>
    with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hrun (bottomJobs b)) ?_
    intro outputs _
    cases outputs with
    | none => simp
    | some outputs =>
      with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hhash _) ?_
      intro root _
      with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hhash _) ?_
      intro base _
      with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hhash _) ?_
      intro found _
      cases found with
      | none => simp
      | some found =>
        with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hrun (signJobs b found.2)) ?_
        intro values _
        cases values with
        | none => simp
        | some values =>
          with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hhash _) ?_
          intro path _
          with_reducible refine isQueryBoundP_bind (n := 0) (m := 0) (by with_reducible exact hhash _) ?_
          intro checked _
          split_ifs <;> simp

/-- The unopened-tree test is invariant under agreement at tracked inputs. -/
theorem topUnopened_congr (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (tree : Fin (2 ^ layerHeight)) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) : TopUnopened x a top tree ↔ TopUnopened x b top tree := by
  have hr value : DeterministicSigning.Resolves a
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom tree)) value ↔
      DeterministicSigning.Resolves b
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom tree)) value :=
    ⟨resolves_tracked h (by with_reducible exact referenceTree_tracked x top _),
      resolves_tracked (fun q hq => (h q hq).symm)
        (by with_reducible exact referenceTree_tracked x top _)⟩
  simp only [TopUnopened, hr]

/-- Unopened top-chain values have the same tracked-cache dependence. -/
theorem unopenedTopTarget_eq (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (candidates : List (HiddenKey × Digest)) (n : ℕ) {a b : HashCache C}
    (h : ∀ q, Tracked q → a q = b q) :
    unopenedTopTarget prims x ((r, candidates), a, n) =
      unopenedTopTarget prims x ((r, candidates), b, n) := by
  simp only [unopenedTopTarget, SigningCostProof.finalOf, honestKey_eq prims x _ _ _ h,
    FinalState.key, topStep_eq h,
    topUnopened_congr x _ _ h, startsCached_congr x _ _ _ h]

/-- Candidate membership and each candidate's target ignore untracked cache entries. -/
theorem hiddenInputHit_congr (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (candidates : List (HiddenKey × Digest)) (n : ℕ) (target : HiddenKey → Option Digest)
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    HiddenInputHit x target ((r, candidates), a, n) ↔
      HiddenInputHit x target ((r, candidates), b, n) := by
  have ht : hiddenTarget x target a = hiddenTarget x target b := by
    funext key
    cases key with
    | opening lay e => exact cachedOpening_eq x _ h
    | bottomChain e l p => rfl
    | topChain b l p => rfl
  simp only [HiddenInputHit, ht]

/-- The complete input-side row can be reconstructed from any agreeing tracked cache. -/
theorem laneInputRow_congr (x : SigningSecurityProof.Keys3 C) (r : Result C)
    (candidates : List (HiddenKey × Digest)) (n : ℕ) (log : QueryLog (WorldSpec C))
    {a b : HashCache C} (h : ∀ q, Tracked q → a q = b q) :
    SigningLinkPaidProof.LaneInputRow prims x ((r, candidates), (a, n), log) ↔
      SigningLinkPaidProof.LaneInputRow prims x ((r, candidates), (b, n), log) := by
  simp only [SigningLinkPaidProof.LaneInputRow, Win, Charged, chargedOutput_congr prims x r n h,
    partialChainTarget_eq prims x r candidates n h, unopenedTopTarget_eq prims x r candidates n h,
    hiddenInputHit_congr x r candidates n _ h]

set_option linter.constructorNameAsVariable false in
/-- Every actual input-side row gives its hit in the observable call log. -/
theorem laneInputLogged : LaneInputLogged prims (C := C) := by
  intro A x w hw hrow
  have hl : (w.1.1, w.2) ∈ support (SigningCostProof.loggedRun prims A x) := by
    rw [← SigningUnchargedLoggedProof.jointRun_logged, support_map, Set.mem_image]
    with_reducible exact ⟨w, hw, rfl⟩
  have hcache := loggedRun_cacheFromLog prims A x _ (by with_reducible exact hl)
  have hrow' := (laneInputRow_congr prims x w.1.1 w.1.2 w.2.1.2 w.2.2 hcache).1 hrow
  exact hrow'.2.2

end ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.chainTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.chainTarget_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.referenceTree_tracked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.referenceTree_tracked

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.topUnopened_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.topUnopened_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.laneInputRow_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.laneInputRow_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.laneInputLogged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningLaneInputLoggedProof.laneInputLogged
