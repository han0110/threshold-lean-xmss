import ThresholdLeanXmssSecurity.Proof.SigningCompilerRealTables
import ThresholdLeanXmssSecurity.Proof.SigningCompilerCouplingUntil

/-!
# Visible observations of the real private tables

The visible cache records raw oracle answers. The private cache retains the
preloaded chain table, while term and mask slots are resolved separately.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncReal
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerRealTables SigningCompilerShare
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
attribute [local irreducible] grind SigningFlatEagerProof.baseGrind Queries
  SigningR1FixedProof.cachedExtra SigningOneRunProof.jointCachedExtra
  rawCarriedLogged rawKeyedSplitOracle rawKeyedSplitWorld rawTraceWorld rawTraceFlatWith
set_option linter.constructorNameAsVariable false

abbrev IsSlot (x : Keys3 C) (q : Query C) : Prop :=
  ∃ z, TprfSecurityProof.slotInput x.2.1 x.2.2 z = q

def Quiet (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (q : Query C) : Prop :=
  ¬IsSlot x q ∧ realCache x s pads noise q = none

def syncPrivate (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (priv visible : HashCache C) : HashCache C :=
  fun q => if Quiet x s pads noise q then visible q else priv q

structure RealPrivate (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × SigningCompilerShare.CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (priv visible : HashCache C) : Prop where
  preload : realCache x s pads noise ≤ priv
  quiet : ∀ q, Quiet x s pads noise q → priv q = visible q
  visible : ∀ q v, visible q = some v →
    (if h : IsSlot x q then some (realTable g rest h.choose) else priv q) = some v

theorem realPrivate_init (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × SigningCompilerShare.CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) :
    RealPrivate x s pads noise g rest (realCache x s pads noise) ∅ := by
  exact ⟨le_rfl, fun _ h => h.2, fun _ _ h => by cases h⟩

theorem installed_input (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (e : ChainNoiseIndex) :
    XmssSecurity.CappedChain.globalChainTableEdgeInput x.1 (installed s pads noise).2 e =
      (chainPending e).input x.1 (s (chainPending e).key) := by
  rcases e with ⟨l, e | b, p⟩ <;>
    simp [XmssSecurity.CappedChain.globalChainTableEdgeInput, installed,
      installHiddenCoordinates, XmssSecurity.CappedChain.chainStepDigit, p.isLt,
      chainPending, PendingInput.input, PendingInput.key,
      XmssSecurity.Concrete.CacheView.keyChainInput,
      XmssSecurity.Concrete.CacheView.chainInput, XmssSecurity.Concrete.CacheView.topChainInput]

theorem edge_input_injective (P : PublicParameter)
    (table : XmssSecurity.CappedChain.GlobalChainValueIndex → Digest) :
    Function.Injective (XmssSecurity.CappedChain.globalChainTableEdgeInput P table) := by
  intro a b h
  obtain ⟨hk, hl, hp, _⟩ :=
    (XmssSecurity.Concrete.CacheView.keyChainInput_eq_iff P _ _ _ _ _ _ _ _).mp h
  exact Prod.ext hl (Prod.ext hk hp)

theorem noise_interpret (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (e : ChainNoiseIndex) :
    realCache x s pads noise (.hash ((chainPending e).input x.1 (s (chainPending e).key))) =
      some ((pendingOutput (chainPending e) (noise e)).interpret s) := by
  rw [← installed_input x s pads noise e]
  change chainTableCache x.1 (installed s pads noise).2 (noiseHigh noise)
    (XmssSecurity.CappedChain.globalChainTableEdgeInput x.1 (installed s pads noise).2 e) = _
  have hex : ∃ a, XmssSecurity.CappedChain.globalChainTableEdgeInput x.1
      (installed s pads noise).2 a =
        XmssSecurity.CappedChain.globalChainTableEdgeInput x.1 (installed s pads noise).2 e := ⟨e, rfl⟩
  unfold chainTableCache
  rw [dif_pos hex, edge_input_injective x.1 (installed s pads noise).2 hex.choose_spec]
  congr 1
  rcases e with ⟨l, e | b, p⟩ <;> fin_cases p <;> rfl


section Observer
variable {x : Keys3 C} {s : HiddenKey → Digest} {pads : Point → Digest}
  {noise : ChainNoiseIndex → HashOutput} {g : C.Term × CPoint → HashOutput}
  {rest : RestSlot C → HashOutput} {priv vis : HashCache C}

theorem RealPrivate.observe_slot (h : RealPrivate x s pads noise g rest priv vis)
    (q : Query C) (hs : IsSlot x q) :
    RealPrivate x s pads noise g rest priv
      (vis.cacheQuery q (realTable g rest hs.choose)) := by
  refine ⟨h.preload, ?_, ?_⟩
  · intro z hz
    have hn : z ≠ q := fun he => hz.1 (he ▸ hs)
    rw [QueryCache.cacheQuery_of_ne _ _ hn]
    exact h.quiet z hz
  · intro z v hv
    by_cases he : z = q
    · subst z
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
      subst v
      rw [dif_pos hs]
    · rw [QueryCache.cacheQuery_of_ne _ _ he] at hv
      exact h.visible z v hv

theorem RealPrivate.observe_other (h : RealPrivate x s pads noise g rest priv vis)
    (q : Query C) (hs : ¬IsSlot x q) (r : HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle q).run priv)) :
    RealPrivate x s pads noise g rest r.2 (vis.cacheQuery q r.1) := by
  obtain ⟨hle, hq, hframe⟩ := randomOracle_support q priv r hr
  refine ⟨h.preload.trans hle, ?_, ?_⟩
  · intro z hz
    by_cases he : z = q
    · subst z; simpa using hq
    · rw [hframe z he, QueryCache.cacheQuery_of_ne _ _ he]
      exact h.quiet z hz
  · intro z v hv
    by_cases he : z = q
    · subst z
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
      subst v
      rw [dif_neg hs]
      exact hq
    · rw [QueryCache.cacheQuery_of_ne _ _ he] at hv
      have hold := h.visible z v hv
      split_ifs at hold ⊢ with hz
      · exact hold
      · rw [hframe z he]; exact hold

abbrev realImpl (x : Keys3 C) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) :=
  SigningGuessProof.privateRoImpl ∘ₛ resolveSlots x.2.1 x.2.2 (realTable g rest)

theorem realImpl_uniform (x : Keys3 C) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (n : unifSpec.Domain) (priv : HashCache C) :
    ((realImpl x g rest) (.inl n)).run priv =
      (fun a => (a, priv)) <$> query (spec := unifSpec) n := by
  simp [realImpl, resolveSlots, SigningGuessProof.privateRoImpl, unifFwdImpl]

theorem realImpl_slot (x : Keys3 C) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (q : Query C) (hs : IsSlot x q) (priv : HashCache C) :
    ((realImpl x g rest) (.inr q)).run priv = pure (realTable g rest hs.choose, priv) := by
  simp [realImpl, resolveSlots, hs]

theorem realImpl_other (x : Keys3 C) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (q : Query C) (hs : ¬IsSlot x q) (priv : HashCache C) :
    ((realImpl x g rest) (.inr q)).run priv =
      ((Query C →ₒ HashOutput).randomOracle q).run priv := by
  simp [realImpl, resolveSlots, hs, SigningGuessProof.privateRoImpl]

theorem realPrivate_observe (h : RealPrivate x s pads noise g rest priv vis)
    (t : (SigningGuessProof.SigningRawSpec C).Domain)
    (r : (((SigningGuessProof.SigningRawSpec C).Range t × HashCache C) × HashCache C))
    (hr : r ∈ support ((simulateQ (realImpl x g rest)
      ((SigningGuessProof.privateRoObserve t).run vis)).run priv)) :
    RealPrivate x s pads noise g rest r.2 r.1.2 := by
  rcases t with n | q
  · simp only [SigningGuessProof.privateRoObserve, StateT.run_mk, simulateQ_map,
      HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_map, realImpl_uniform, Functor.map_map, support_map, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact h
  · simp only [SigningGuessProof.privateRoObserve, StateT.run_mk, simulateQ_map,
      HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_map] at hr
    by_cases hs : IsSlot x q
    · rw [realImpl_slot x g rest q hs, map_pure, mem_support_pure_iff] at hr
      subst r
      exact h.observe_slot q hs
    · rw [realImpl_other x g rest q hs, support_map, Set.mem_image] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact h.observe_other q hs a ha


/-- Every raw program observed through the fixed observer preserves the relation. -/
theorem realPrivate_program {α : Type} (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α)
    (h : RealPrivate x s pads noise g rest priv vis)
    (r : (α × HashCache C) × HashCache C)
    (hr : r ∈ support ((simulateQ (realImpl x g rest)
      ((simulateQ SigningGuessProof.privateRoObserve oa).run vis)).run priv)) :
    RealPrivate x s pads noise g rest r.2 r.1.2 := by
  induction oa using OracleComp.inductionOn generalizing priv vis r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r; exact h
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨a, ha, hr⟩ := hr
    exact ih a.1.1 (realPrivate_observe h t a ha) r hr


end Observer


section QuietTransport
variable (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
  (noise : ChainNoiseIndex → HashOutput)

def QuietQ : (SigningGuessProof.SigningRawSpec C).Domain → Prop
  | .inl _ => True
  | .inr q => Quiet x s pads noise q

theorem syncPrivate_agrees (priv w : HashCache C) (q : Query C)
    (hq : Quiet x s pads noise q) : syncPrivate x s pads noise priv w q = w q := by
  simp [syncPrivate, hq]

theorem syncPrivate_eq (priv w : HashCache C)
    (h : ∀ q, Quiet x s pads noise q → priv q = w q) :
    syncPrivate x s pads noise priv w = priv := by
  funext q
  by_cases hq : Quiet x s pads noise q
  · simp [syncPrivate, hq, h q hq]
  · simp [syncPrivate, hq]

theorem syncPrivate_nested (priv w w' : HashCache C) :
    syncPrivate x s pads noise (syncPrivate x s pads noise priv w) w' =
      syncPrivate x s pads noise priv w' := by
  funext q; by_cases hq : Quiet x s pads noise q <;> simp [syncPrivate, hq]

theorem syncPrivate_cacheQuery (priv w : HashCache C) (q : Query C) (v : HashOutput)
    (hq : Quiet x s pads noise q) :
    syncPrivate x s pads noise priv (w.cacheQuery q v) =
      (syncPrivate x s pads noise priv w).cacheQuery q v := by
  funext z
  by_cases he : z = q
  · subst z; simp [syncPrivate, hq]
  · simp only [QueryCache.cacheQuery_of_ne _ _ he, syncPrivate]

theorem quiet_query (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SigningGuessProof.SigningRawSpec C).Domain) (ht : QuietQ x s pads noise t)
    (priv w : HashCache C) (h : ∀ q, Quiet x s pads noise q → priv q = w q) :
    ((realImpl x g rest) t).run priv =
      (fun r => (r.1, syncPrivate x s pads noise priv r.2)) <$>
        (SigningGuessProof.privateRoImpl t).run w := by
  rcases t with n | q
  · rw [realImpl_uniform]
    simp [SigningGuessProof.privateRoImpl, unifFwdImpl,
      syncPrivate_eq x s pads noise priv w h]
  · change Quiet x s pads noise q at ht
    rw [realImpl_other x g rest q ht.1]
    change _ = (fun r => (r.1, syncPrivate x s pads noise priv r.2)) <$>
      (((Query C →ₒ HashOutput).randomOracle q).run w)
    have he := h q ht
    cases hw : w q with
    | none =>
      rw [QueryImpl.withCaching_run_none _ (he.trans hw),
        QueryImpl.withCaching_run_none _ hw, Functor.map_map]
      congr 1
      funext v
      rw [syncPrivate_cacheQuery x s pads noise priv w q v ht,
        syncPrivate_eq x s pads noise priv w h]
    | some v =>
      rw [QueryImpl.withCaching_run_some _ (he.trans hw),
        QueryImpl.withCaching_run_some _ hw, map_pure,
        syncPrivate_eq x s pads noise priv w h]

/-- A quiet raw program has exactly the old single-cache law, with a private frame. -/
theorem quiet_program {α : Type} (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (oa : OracleComp (SigningGuessProof.SigningRawSpec C) α)
    (hq : Queries (QuietQ x s pads noise) oa) (priv w : HashCache C)
    (h : ∀ q, Quiet x s pads noise q → priv q = w q) :
    (simulateQ (realImpl x g rest) oa).run priv =
      (fun r => (r.1, syncPrivate x s pads noise priv r.2)) <$>
        (simulateQ SigningGuessProof.privateRoImpl oa).run w := by
  induction oa using OracleComp.inductionOn generalizing priv w with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure,
      syncPrivate_eq x s pads noise priv w h]
  | query_bind t next ih =>
    unfold Queries at hq
    have hb := (isQueryBound_query_bind_iff ..).mp hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    rw [quiet_query x s pads noise g rest t hb.1 priv w h, bind_map_left, map_bind]
    apply bind_congr
    intro r
    rw [ih r.1 (by unfold Queries; exact hb.2 r.1) _ r.2 (syncPrivate_agrees x s pads noise priv r.2)]
    simp only [syncPrivate_nested]

/-- Combine the quiet transport with an existing exact visible-state reification. -/
theorem quiet_rawStateLaw {σ α : Type} (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (cache : σ → HashCache C)
    (source : StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) α)
    (actual : StateT σ ProbComp α) (hlaw : RawStateLaw cache source actual)
    (st : σ) (hq : Queries (QuietQ x s pads noise) (source.run st))
    (priv : HashCache C) (h : ∀ q, Quiet x s pads noise q → priv q = cache st q) :
    (simulateQ (realImpl x g rest) (source.run st)).run priv =
      (fun r => (r, syncPrivate x s pads noise priv (cache r.2))) <$> actual.run st := by
  rw [quiet_program x s pads noise g rest _ hq priv (cache st) h, hlaw st,
    Functor.map_map]

end QuietTransport


theorem not_isSlot_hash (x : Keys3 C) (i : HashInput) : ¬IsSlot x (.hash i) := by
  rintro ⟨⟨T, p⟩ | z, h⟩ <;> cases h

theorem quiet_message (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (i : HashInput) (hi : IsMsg i) :
    Quiet x s pads noise (.hash i) := by
  refine ⟨not_isSlot_hash x i, ?_⟩
  change chainTableCache x.1 (installed s pads noise).2 (noiseHigh noise) i = none
  unfold chainTableCache
  apply dif_neg
  rintro ⟨e, he⟩
  rw [installed_input] at he
  exact PendingInput.not_isMsg x.1 (chainPending e) (s (chainPending e).key) (he ▸ hi)

theorem quiet_grind (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (lay : Layer) (e : KeyIndex)
    (message : HashInput) (base : Digest) (attempts trial : ℕ) :
    Queries (fun q : Query C => Quiet x s pads noise q)
      (simulateQ (fun i => (query (spec := Query C →ₒ HashOutput) (.hash i) :
        OracleComp (Query C →ₒ HashOutput) HashOutput))
        (grind x.1 lay e message base attempts trial)) := by
  induction attempts generalizing trial with
  | zero => simp only [grind, simulateQ_pure]; exact Queries.pure _
  | succ attempts ih =>
    simp only [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash,
      HasQuery.instOfMonadLift_query, simulateQ_bind, simulateQ_spec_query,
      bind_assoc, pure_bind]
    apply Queries.bind (Queries.query _ (quiet_message x s pads noise _
      (SigningLane2BridgeProof.isMsg_trialInput x.1 lay e message base trial)))
    intro answer
    cases Codeword.decode (truncateHash answer) with
    | none => exact ih (trial + 1)
    | some encoding => exact Queries.pure _

theorem quiet_baseGrind (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (e : KeyIndex) (message : Message)
    (answer : HashOutput) :
    Queries (fun q : Query C => Quiet x s pads noise q)
      (SigningFlatEagerProof.baseGrind x.1 e message answer) := by
  unfold SigningFlatEagerProof.baseGrind
  simpa only [simulateQ_map] using (quiet_grind x s pads noise bottomLayer e
    (bytesLE 32 message) (truncateHash answer) randomizerAttemptLimit 0).map (fun _ => ())

theorem quiet_cachedExtra (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (before after : SigningFlatProof.FlatState C)
    (t : (WorldSpec C).Domain) :
    Queries (fun q : Query C => Quiet x s pads noise q)
      (SigningR1FixedProof.cachedExtra x.2.1 x.1 before t after) := by
  unfold SigningR1FixedProof.cachedExtra
  split
  · unfold SigningFlatEagerProof.grindExtra
    split
    · split
      · split
        · exact quiet_baseGrind x s pads noise _ _ _
        · exact Queries.pure _
      · exact Queries.pure _
    · exact Queries.pure _
  · exact Queries.pure _

theorem realImpl_slotInput (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (z : TprfSecurityProof.Slot C) (priv : HashCache C) :
    ((realImpl x g rest) (.inr (TprfSecurityProof.slotInput x.2.1 x.2.2 z))).run priv =
      pure (realTable g rest z, priv) := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1) (not_not.mp (not_or.mp hkeys).2)
  have hs : IsSlot x (TprfSecurityProof.slotInput x.2.1 x.2.2 z) := ⟨z, rfl⟩
  rw [realImpl_slot x g rest _ hs, hi hs.choose_spec]

theorem realImpl_constrained (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (T : C.Term) (p : CPoint) (priv : HashCache C) :
    ((realImpl x g rest) (.inr (.prf (x.2.1 T) p.val))).run priv = pure (g (T, p), priv) := by
  simpa only [TprfSecurityProof.slotInput, realTable_constrained] using realImpl_slotInput x hkeys g rest (.inl (T, p.val)) priv

theorem realImpl_rest (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (z : RestSlot C) (priv : HashCache C) :
    ((realImpl x g rest) (.inr (TprfSecurityProof.slotInput x.2.1 x.2.2 z.val))).run priv =
      pure (rest z, priv) := by
  rw [realImpl_slotInput x hkeys g rest z.val priv, realTable_rest]

theorem realImpl_preload (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (priv vis : HashCache C)
    (h : RealPrivate x s pads noise g rest priv vis) (e : ChainNoiseIndex) :
    ((realImpl x g rest) (.inr (.hash ((chainPending e).input x.1 (s (chainPending e).key))))).run priv =
      pure ((pendingOutput (chainPending e) (noise e)).interpret s, priv) := by
  rw [realImpl_other x g rest _ (not_isSlot_hash x _)]
  exact QueryImpl.withCaching_run_some _ (h.preload (noise_interpret x s pads noise e))

theorem realPrivate_slotValue (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv vis : HashCache C) (h : RealPrivate x s pads noise g rest priv vis)
    (z : TprfSecurityProof.Slot C) (v : HashOutput)
    (hv : vis (TprfSecurityProof.slotInput x.2.1 x.2.2 z) = some v) :
    v = realTable g rest z := by
  have hi := TprfSecurityProof.slotInput_injective (not_not.mp (not_or.mp hkeys).1) (not_not.mp (not_or.mp hkeys).2)
  have hs : IsSlot x (TprfSecurityProof.slotInput x.2.1 x.2.2 z) := ⟨z, rfl⟩
  have he := h.visible _ v hv
  rw [dif_pos hs, hi hs.choose_spec] at he
  exact (Option.some.inj he).symm

/-- The opening value requires the explicit row-sum law of the chosen table. -/
theorem realPrivate_actualValue_of_sum (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv vis : HashCache C) (h : RealPrivate x s pads noise g rest priv vis)
    (hsum : ∀ e, SigningShareLazy.xorSum C.terms (fun T => truncateHash
      (g (T, ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩))) =
      s (.opening bottomLayer e)) (e : KeyIndex)
    (hc : SigningGuessProof.RandomizerCached x.2.1 vis e) :
    SigningGuessProof.cachedRandomizer x.2.1 vis e = s (.opening bottomLayer e) := by
  let data : DeferredState C := ⟨vis, fun _ => none, ∅, fun _ => none⟩
  rw [show vis = data.cache from rfl, cachedRandomizer_termSum, ← xorSum_terms]
  rw [← hsum e]
  apply congrArg (SigningShareLazy.xorSum C.terms)
  funext T
  obtain ⟨v, hv⟩ := hc T
  have he := realPrivate_slotValue x hkeys s pads noise g rest priv vis h
    (.inl (T, .randomizer bottomLayer e)) v hv
  rw [realTable_constrained g rest T ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩] at he
  simp only [cachedTerm, data, hv, Option.getD_some, he]

/-- The concrete eager fiber table has exactly the required opening aggregate. -/
theorem realPrivate_actualValue {B : Type} (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput)
    (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (priv vis : HashCache C)
    (h : RealPrivate x s pads noise
      (SigningShareLazy.fiberTable C.terms (SigningCompilerShare.NoFalse.tau s pads)
        (SigningShareLazy.init (B := B)) u) rest priv vis)
    (e : KeyIndex) (hc : SigningGuessProof.RandomizerCached x.2.1 vis e) :
    SigningGuessProof.cachedRandomizer x.2.1 vis e = s (.opening bottomLayer e) := by
  apply realPrivate_actualValue_of_sum x hkeys s pads noise _ rest priv vis h _ e hc
  intro e
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact (SigningShareLazy.fiberTable_sum C.terms terms_nodup mem_terms
    (SigningCompilerShare.NoFalse.tau s pads) (SigningShareLazy.init (B := B))
    (SigningShareLazy.good_init _ _ (Or.inl (List.ne_nil_of_mem (mem_terms T)))) u
    ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩).trans
      (SigningCompilerShare.NoFalse.tau_bottom_opening s pads e)


section HandlerPreservation
variable (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput)

/-- A stateful source preserves the visible/private relation at every supported result. -/
def RealPrivateLaw {σ α : Type} (cache : σ → HashCache C)
    (source : StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) α) : Prop :=
  ∀ st priv, RealPrivate x s pads noise g rest priv (cache st) →
    ∀ r ∈ support ((simulateQ (realImpl x g rest) (source.run st)).run priv),
      RealPrivate x s pads noise g rest r.2 (cache r.1.2)

variable {x s pads noise g rest}

theorem RealPrivateLaw.pure {σ α : Type} (cache : σ → HashCache C) (a : α) :
    RealPrivateLaw x s pads noise g rest cache (pure a) := by
  intro st priv h r hr
  simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
  subst r; exact h

theorem RealPrivateLaw.bind {σ α β : Type} (cache : σ → HashCache C)
    {oa : StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) α}
    (ha : RealPrivateLaw x s pads noise g rest cache oa)
    (next : α → StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C)) β)
    (hn : ∀ a, RealPrivateLaw x s pads noise g rest cache (next a)) :
    RealPrivateLaw x s pads noise g rest cache (oa >>= next) := by
  intro st priv h r hr
  simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha', hr⟩ := hr
  exact hn a.1.1 a.1.2 a.2 (ha st priv h a ha') r hr

theorem RealPrivateLaw.simulateQ {ι σ α : Type} {spec : OracleSpec ι}
    (cache : σ → HashCache C)
    (impl : QueryImpl spec (StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C))))
    (h : ∀ t, RealPrivateLaw x s pads noise g rest cache (impl t))
    (oa : OracleComp spec α) :
    RealPrivateLaw x s pads noise g rest cache (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact RealPrivateLaw.pure cache a
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact (h t).bind cache _ ih

theorem rawCarriedLogged_realPrivate (prims : Primitives) (t : (WorldSpec C).Domain) :
    RealPrivateLaw x s pads noise g rest (fun st => st.1.1.1) (rawCarriedLogged prims t) := by
  intro st priv h r hr
  simp only [rawCarriedLogged, StateT.run_mk, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact realPrivate_program (SigningGuessProof.signingRawWorld prims t) h a ha

theorem rawKeyedSplitOracle_realPrivate
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) (q : Query C) :
    RealPrivateLaw x s pads noise g rest (fun st => st.1.1) (rawKeyedSplitOracle keyOf q) := by
  intro st priv h r hr
  simp only [rawKeyedSplitOracle, StateT.run_mk, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact realPrivate_observe h (.inr q) a ha

theorem rawKeyedSplitWorld_realPrivate (prims : Primitives) (t : (WorldSpec C).Domain) :
    RealPrivateLaw x s pads noise g rest (fun st => st.1.1.1.1.1)
      (rawKeyedSplitWorld prims x t) := by
  intro st priv h r hr
  simp only [rawKeyedSplitWorld, StateT.run_mk, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hr
  obtain ⟨z, hz, hr⟩ := hr
  have hz' := rawCarriedLogged_realPrivate prims t (st.1.1.1, st.2) priv h z hz
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨y, hy, rfl⟩ := hr
  exact RealPrivateLaw.simulateQ (fun st => st.1.1)
    (rawKeyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1))
    (rawKeyedSplitOracle_realPrivate _) _ _ _ hz' y hy

theorem rawTraceWorld_realPrivate (prims : Primitives) (t : (WorldSpec C).Domain) :
    RealPrivateLaw x s pads noise g rest (fun st => st.1.1.1.1.1.1)
      (rawTraceWorld prims x t) := by
  intro st priv h r hr
  simp only [rawTraceWorld, StateT.run_mk, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact rawKeyedSplitWorld_realPrivate prims t (st.1.1, st.2) priv h a ha

/-- Any outer handler may update its own opening state; the trace cache is framed. -/
theorem rawTraceFlatWith_realPrivate {ι : Type} {spec : OracleSpec ι}
    (prims : Primitives)
    (outer : QueryImpl spec (StateT (SigningJointEagerProof.OpeningState C)
      (OracleComp (WorldSpec C)))) (t : ι) :
    RealPrivateLaw x s pads noise g rest (fun st => st.1.1.1.1.1.1)
      (rawTraceFlatWith prims x outer t) := by
  intro st priv h r hr
  simp only [rawTraceFlatWith, StateT.run_mk, simulateQ_map, StateT.run_map,
    support_map, Set.mem_image] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact RealPrivateLaw.simulateQ (fun st => st.1.1.1.1.1.1) (rawTraceWorld prims x)
    (rawTraceWorld_realPrivate prims) _ st priv h a ha

theorem realAdv_realPrivate (prims : Primitives) (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) :
    RealPrivateLaw x s pads noise g rest (fun st => st.1.1.1.1.1.1)
      (rawTraceFlatWith prims x (openingOracles x (SigningJointEagerProof.dealtOf x top)) t) :=
  rawTraceFlatWith_realPrivate prims _ t

/-- Fusion retains the same visible and private states as the nested interpretation. -/
theorem RealPrivateLaw.fuse {ι σ : Type} {spec : OracleSpec ι}
    (cache : σ → HashCache C)
    (inner : QueryImpl spec (StateT σ (OracleComp (SigningGuessProof.SigningRawSpec C))))
    (t : ι) (h : RealPrivateLaw x s pads noise g rest cache (inner t))
    (a : σ × HashCache C) (ha : RealPrivate x s pads noise g rest a.2 (cache a.1))
    (r : spec.Range t × (σ × HashCache C))
    (hr : r ∈ support ((SigningCompilerUntil.fuse inner (realImpl x g rest) t).run a)) :
    RealPrivate x s pads noise g rest r.2.2 (cache r.2.1) := by
  simp only [SigningCompilerUntil.fuse, StateT.run, support_map, Set.mem_image] at hr
  obtain ⟨b, hb, rfl⟩ := hr
  exact h a.1 a.2 ha b hb

theorem realAdv_preserves (prims : Primitives) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain)
    (a : SigningLaneUnionProof.TraceState C × HashCache C)
    (ha : RealPrivate x s pads noise g rest a.2 a.1.1.1.1.1.1.1)
    (r : (LocalSpec C + TsigSpec C).Range t ×
      (SigningLaneUnionProof.TraceState C × HashCache C))
    (hr : r ∈ support ((SigningCompilerUntil.fuse
      (rawTraceFlatWith prims x (openingOracles x (SigningJointEagerProof.dealtOf x top)))
      (realImpl x g rest) t).run a)) :
    RealPrivate x s pads noise g rest r.2.2 r.2.1.1.1.1.1.1.1 :=
  RealPrivateLaw.fuse _ _ t (realAdv_realPrivate prims top t) a ha r hr

theorem realWorld_preserves (prims : Primitives) (t : (WorldSpec C).Domain)
    (a : SigningLaneUnionProof.TraceState C × HashCache C)
    (ha : RealPrivate x s pads noise g rest a.2 a.1.1.1.1.1.1.1)
    (r : (WorldSpec C).Range t × (SigningLaneUnionProof.TraceState C × HashCache C))
    (hr : r ∈ support ((SigningCompilerUntil.fuse (rawTraceWorld prims x)
      (realImpl x g rest) t).run a)) :
    RealPrivate x s pads noise g rest r.2.2 r.2.1.1.1.1.1.1.1 :=
  RealPrivateLaw.fuse _ _ t (rawTraceWorld_realPrivate prims t) a ha r hr


/-- The old visible-state world law specializes directly to quiet calls. -/
theorem rawTraceWorld_quiet (prims : Primitives) (t : (WorldSpec C).Domain)
    (ht : ¬SigningHitLaneProof.IsProgram t) (st : SigningLaneUnionProof.TraceState C)
    (priv : HashCache C)
    (hq : Queries (QuietQ x s pads noise) ((rawTraceWorld prims x t).run st))
    (h : ∀ q, Quiet x s pads noise q → priv q = st.1.1.1.1.1.1 q) :
    (simulateQ (realImpl x g rest) ((rawTraceWorld prims x t).run st)).run priv =
      (fun r => (r, syncPrivate x s pads noise priv r.2.1.1.1.1.1.1)) <$>
        (SigningLaneUnionProof.traceWorld prims x t).run st :=
  quiet_rawStateLaw x s pads noise g rest _ _ _ (rawTraceWorld_law prims x t ht) st hq priv h

end HandlerPreservation

end ThresholdLeanXmssSecurity.SigningCompilerSyncReal

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncReal.noise_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncReal.noise_interpret

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realPrivate_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realPrivate_program

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncReal.quiet_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncReal.quiet_program

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realPrivate_actualValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realPrivate_actualValue

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realAdv_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realAdv_preserves

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realWorld_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncReal.realWorld_preserves
