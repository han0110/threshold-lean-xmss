import ThresholdLeanXmssSecurity.Proof.SigningOwnWalkHandlers

/-!
# The walk of round 2 and of the honest signature tail over the ledger

A round-2 request and the honest signature tail keep `WalkInv` and make no charged call
(`charges_round2`, `charges_tail`).

* The check of `c_e` and the base call carry the opening of the key. The key is bound and its tree
  is stored, so `treeCommit`, `commitTerms` and `ready` give a revealed opening.
* A canonical base call leaves a stale backend, or a cache that resolves the search
  (`base_step_trials`). A base call at another value after a check that passed leaves a second
  opening (`loose_base_second`). In each case the digest calls of the search are not charged
  (`walk_resolvedHash`).
* `WalkO` is the triple of `Walk` for O1 programs. Round 2 carries the signing state of the source
  through its steps with `KeepsSigning`, so the record of the signer meets `releasedBound`.
* The tail reveals the top chain values of its second build. That build gives a tree of
  `TopShape` (`walk_sourceBottomTree_shape`), so no reveal is a bottom opening.
* The tail runs at a key with `t` signers. At most `t - 1` operators are corrupt, so the key has a
  release record, and `releasedBound` binds the key to the message (`bound_of_signers`).
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnWalkRound2

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof SigningCompilerPotential
open SigningCompilerO1Clean SigningOwnLedger SigningOwnFree SigningOwnWalk SigningOwnWalkBuild
open SigningOwnForger SigningOwnWalkHandlers

variable {C : Committee}

attribute [local instance] Classical.propDecidable


set_option linter.constructorNameAsVariable false in
/-- A hash call leaves its answer in the cache. -/
theorem compilerImpl_hash_cached (P : PublicParameter) (seeds : C.Term → HashOutput) (q : Query C)
    (st : CompilerBackend C) (r : HashOutput × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds (.hash q)).run st)) : r.2.data.cache q = some r.1 := by
  obtain ⟨a, ha, _, -, hle, rfl⟩ := compilerImpl_hash_steps P seeds q st r hr
  exact hle (randomOracle_support q st.data.cache (a.1, a.2.cache)
    (deferred_hash_support q st.data a ha)).2.1

set_option linter.constructorNameAsVariable false in
/-- A canonical base call at a bound key with each term cached leaves a stale backend, or a cache
that resolves the search from its answer. The honest search then makes cache hits only. -/
theorem base_step_trials (P : PublicParameter) (seeds : C.Term → HashOutput)
    (st : CompilerBackend C × ℕ) (hreach : CompilerReachable P seeds st) (e : KeyIndex)
    (message : Message) (hbound : st.1.bound e = some message)
    (hprf : SigningGuessProof.RandomizerCached seeds st.1.data.cache e)
    (r : HashOutput × CompilerBackend C)
    (hr : r ∈ support ((compilerImpl P seeds (.hash (.hash (randomizerInput P bottomLayer e
      (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (littleEndianBytes 32 message))))).run
        st.1)) :
    r.2.trace.2 = true ∨
      DeterministicSigning.Resolves r.2.data.cache
        (SigningFlatEagerProof.baseGrind P e message r.1) () := by
  generalize hq : (Query.hash (randomizerInput P bottomLayer e
    (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (littleEndianBytes 32 message)) : Query C) = q
    at hr
  by_cases hstale : r.2.trace.2 = true
  · exact Or.inl hstale
  refine Or.inr ?_
  have hcache := compilerImpl_cache_le P seeds (.hash q) st.1 r hr
  have hreach' : CompilerReachable P seeds
      (r.2, st.2 + if deferredCounted (C := C) (.hash q) then 1 else 0) := by
    refine CompilerReachable.step (.hash q) st ((show DeferredSpec C (.hash q) from r.1), (r.2, _))
      hreach ?_
    simp only [countImpl, StateT.run_mk, support_map]
    exact ⟨r, hr, rfl⟩
  have hbound' : r.2.bound e = some message :=
    (congrFun (compilerImpl_bound_eq P seeds (.hash q) st.1 r hr (fun _ _ h => by cases h)) e).trans
      hbound
  have hsig : (compilerSigning st.1).bound e = some message := hbound
  have hrec : e ∈ r.2.trace.1.leafIndices := by
    obtain ⟨a, ha, b, hb, hra⟩ := compiler_hash_support P seeds q st.1 r hr
    have htrace := congrArg (fun r => r.2.trace) hra
    simp only at htrace
    cases hc : st.1.data.cache (.hash (randomizerInput P bottomLayer e
        (SigningGuessProof.cachedRandomizer seeds st.1.data.cache e) (littleEndianBytes 32 message))) with
    | none =>
        rw [htrace, ← hq, traceStepAt_fresh_base P seeds _ _ _ _ e message hprf hsig hc]
        simp [XmssSecurity.SigningCacheTrace.leafIndices]
        exact List.mem_append_right _ (List.mem_singleton_self e)
    | some answer =>
        by_cases hin : e ∈ st.1.trace.1.leafIndices
        · rw [htrace]
          simp only [XmssSecurity.SigningCacheTrace.leafIndices] at hin ⊢
          exact List.map_subset _ (SigningLane2TraceLinkProof.traceStepAt_mono seeds P _ b.2
            (compilerSigning st.1) _ st.1.trace).1 hin
        · exact absurd (compiler_stale_base P seeds st.1 e message hprf hbound answer hc hin q
            hq.symm r hr) hstale
  obtain ⟨answer, hans, hres⟩ := traced_trials P seeds r.2
    (CompilerReachable.entryBases P seeds _ hreach').1 (reachable_entryTrials P seeds _ hreach')
    e message hbound' hrec
  have hself := compilerImpl_hash_cached P seeds q st.1 r hr
  rw [← SigningGuessProof.cachedRandomizer_stable seeds _ _ e hcache hprf, hq, hself] at hans
  cases hans
  exact hres

/-- A base call at a bound key at a value other than the cached randomizer, after a commitment
check that passed, leaves a backend with a second opening. The honest search then makes no charged
call. -/
theorem loose_base_second (P : PublicParameter) (seeds : C.Term → HashOutput)
    (data : DeferredState C) (e : KeyIndex) (ρ : Digest) (v : HashOutput) (c : DeferredOutput)
    (hcheck : data.cache (.hash (commitmentInput P e ρ)) = some v)
    (hpending : data.pending (.commitment e) = some c) (hlow : c.low = .known (truncateHash v))
    (hprf : SigningGuessProof.RandomizerCached seeds data.cache e)
    (hne : ρ ≠ SigningGuessProof.cachedRandomizer seeds data.cache e) :
    SecondOpening P seeds data :=
  ⟨e, ρ, v, c, hcheck, hpending, hlow, hprf, hne⟩

section Search

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- The search of a hash program on the lazy `H`. -/
abbrev lazyRun {α : Type} (oa : OracleComp HashSpec α) : OracleComp (Query C →ₒ HashOutput) α :=
  simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa

theorem lazyRun_query_bind {α : Type} (x : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    lazyRun (C := C) (liftM (HashSpec.query x) >>= next) =
      liftM ((Query C →ₒ HashOutput).query (.hash x)) >>= fun a => lazyRun (next a) := by
  simp only [lazyRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

/-- The backend state is stale, has a second opening, or resolves the search `oa` from its cache.
A message digest call of the search is then not charged. -/
def SearchFree {α : Type} (oa : OracleComp HashSpec α) (st : LState C) : Prop :=
  st.1.1.1.trace.2 = true ∨ SecondOpening P seeds st.1.1.1.data ∨
    ∃ v, DeterministicSigning.Resolves st.1.1.1.data.cache (lazyRun oa) v

/-- A search whose trials the cache resolves, on a backend that is not stale and has no second
opening, makes only uncharged calls. A stale backend or a second opening also stops each charge. -/
theorem walk_resolvedHash {α : Type} (oa : OracleComp HashSpec α)
    (hq : XmssSecurity.Bridge.OnlyQueries (fun input => hiddenCandidate P input = none) oa) :
    Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧ SearchFree P seeds oa st) 0
      (fun _ => BaseInv P seeds none none)
      (simulateQ (fun input => sourceHash P seeds (.hash input)) oa) := by
  induction hq with
  | pure a =>
      simp only [simulateQ_pure]
      exact Walk.pure a fun _ _ h => h.1
  | query x hx next _ ih =>
      have hcall : Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧
          SearchFree P seeds (liftM (HashSpec.query x) >>= next) st) 0
          (fun a src st => BaseInv P seeds none none src st ∧ SearchFree P seeds (next a) st)
          (sourceHash P seeds (.hash x)) := by
        simp only [sourceHash]
        refine Walk.conseq (walk_call P seeds Q s (readyEx := none) (cachedEx := none)
          (.hash (.hash x)) (fun _ st => SearchFree P seeds (liftM (HashSpec.query x) >>= next) st)
          (fun _ _ h => by cases h) (fun _ _ h => by cases h) ?_
          (fun src st _ _ y hy => ready_plain P seeds _ (fun _ _ h => by cases h)
            (fun _ _ h => by cases h) src st y hy)
          (fun _ st _ _ y hy => commit_plain P seeds _ (fun _ h => by cases h)
            (fun _ _ h => by cases h) st y hy)) (fun _ _ h => h) ?_ le_rfl
        · intro src st _ hA
          rintro ⟨input, heq, ⟨c, hc, -⟩ | ⟨-, -, hnone, hst, -, hnso⟩⟩
          · cases heq
            rw [hx] at hc
            cases hc
          · cases heq
            rcases hA with h | h | ⟨v, hres⟩
            · rw [h] at hst
              cases hst
            · exact hnso h
            · rw [lazyRun_query_bind] at hres
              obtain ⟨b, hb, -⟩ := hres.query_inv
              rw [hb] at hnone
              cases hnone
        · rintro a src' st' ⟨hinv, st0, hA, y, hy, rfl, hst⟩
          refine ⟨hinv, ?_⟩
          have hle := compilerImpl_cache_le P seeds _ _ y hy
          rcases hA with h | h | ⟨v, hres⟩
          · left
            rw [hst]
            exact compilerImpl_stale P seeds _ _ h y hy
          · right; left
            rw [hst]
            exact secondOpening_mono P seeds hle (fun p v hp => compilerImpl_pending_keep P seeds _ _
              y hy (fun _ _ h => by cases h) p v hp) h
          · right; right
            rw [lazyRun_query_bind] at hres
            obtain ⟨b, hb, htail⟩ := hres.query_inv
            have hyc := compilerImpl_hash_cached P seeds _ _ y hy
            rw [hle hb] at hyc
            cases hyc
            rw [hst]
            exact ⟨v, htail.mono hle⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map]
      exact Walk.conseq (c := 0 + 0) (Walk.bind hcall ih) (fun _ _ h => h) (fun _ _ _ h => h)
        le_rfl

/-- The bottom search queries message digest inputs only, which carry no candidate. -/
theorem candidateFree_grind (e : KeyIndex) (message : HashInput) (base : Randomizer)
    (attempts trial : ℕ) :
    XmssSecurity.Bridge.OnlyQueries (fun input => hiddenCandidate P input = none)
      (grind P bottomLayer e message base attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      have hfree := hiddenCandidate_none_of_isMsg P _
        (byte23_msg P bottomLayer e (message ++ littleEndianBytes 16 (base + BitVec.ofNat digestBits trial)))
      refine ((XmssSecurity.Bridge.onlyQueries_query hfree).bind fun _ => .pure _).bind
        fun digest => ?_
      cases Codeword.decode digest with
      | some encoding => exact .pure _
      | none => exact ih _

/-- A program of the forger's PRF oracle that runs a hash program runs it through `sourceHash`. -/
theorem sourceRoProgram_tweakable (prims : Primitives) {α : Type} (oa : OracleComp HashSpec α) :
    sourceRoProgram prims P seeds (tweakable oa) =
      simulateQ (fun input => sourceHash P seeds (.hash input)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [sourceRoProgram, tweakable]
  | query_bind x next ih =>
      simp only [sourceRoProgram, tweakable, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map] at ih ⊢
      simp only [hashQuery, HasQuery.instOfMonadLift_query]
      congr 1
      funext a
      exact ih a

/-- A hash call at an input that the precondition makes uncharged. -/
theorem walk_inputCall (input : HashInput) (A : SourceState C → LState C → Prop)
    (hcharge : ∀ src st, BaseInv P seeds none none src st → A src st →
      ¬ownCharged P seeds (.hash (.hash input)) (st.1.1, st.1.2.1) st.2) :
    Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧ A src st) 0
      (fun y src' st' => BaseInv P seeds none none src' st' ∧ ∃ st, A src' st ∧
        ∃ x ∈ support ((compilerImpl P seeds (.hash (.hash input))).run st.1.1.1), y = x.1 ∧
          st'.1.1.1 = x.2)
      (sourceHash P seeds (.hash input)) := by
  simp only [sourceHash]
  exact walk_call P seeds Q s (.hash (.hash input)) A (fun _ _ h => by cases h)
    (fun _ _ h => by cases h) hcharge
    (fun src st _ _ y hy => ready_plain P seeds _ (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) src st y hy)
    (fun _ st _ _ y hy => commit_plain P seeds _ (fun _ h => by cases h)
      (fun _ _ h => by cases h) st y hy)

/-- A call at an input that carries the opening of a key with a revealed opening, and that is no
message digest input, is not charged. -/
theorem opening_not_charged (input : HashInput) (e : KeyIndex) (ρ : Digest)
    (hc : hiddenCandidate P input = some (.opening bottomLayer e, ρ)) (hmsg : ¬IsMsg input)
    (st : (CompilerBackend C × ℕ) × (HiddenKey → Option Digest)) (g : OwnGhost)
    (hrev : st.2 (.opening bottomLayer e) ≠ none) :
    ¬ownCharged P seeds (.hash (.hash input)) st g := by
  rintro ⟨input', heq, ⟨c, hc', hnone⟩ | ⟨hm, -⟩⟩
  · cases heq
    rw [hc] at hc'
    cases hc'
    exact hrev hnone
  · cases heq
    exact hmsg hm

/-- The opening of a key is revealed when the key is bound and has a commitment answer. -/
theorem opening_revealed {src : SourceState C} {st : LState C}
    (h : BaseInv P seeds none none src st) (e : KeyIndex) (hb : src.signing.bound e ≠ none)
    (hc : st.1.1.1.data.pending (.commitment e) ≠ none) :
    src.revealed (.opening bottomLayer e) ≠ none :=
  h.ready e (by simp) ⟨hb, fun T => Or.inl (h.commitTerms e hc T)⟩

end Search

section Codeword

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- The key is bound to the message, and its commitment answer has the low half `commitment`. -/
def Opened (commitment : Digest) (e : KeyIndex) (message : Message) (src : SourceState C)
    (st : LState C) : Prop :=
  src.signing.bound e = some message ∧
    ∃ c, st.1.1.1.data.pending (.commitment e) = some c ∧ c.low = .known commitment

/-- The codeword search of a signature at a key with a revealed opening makes no charged call. -/
theorem walk_signCodeword (prims : Primitives) (commitment : Digest) (e : KeyIndex)
    (message : Message) (ρ : Digest) :
    Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧
        Opened commitment e message src st) 0
      (fun _ => BaseInv P seeds none none)
      (sourceRoProgram prims P seeds (signCodeword P commitment e message ρ)) := by
  have horacle : ∀ input, simulateQ (fun input => sourceHash P seeds (.hash input))
      (Verification.oracleHashWithHash (m := OracleComp HashSpec) input) = sourceHash P seeds (.hash input) := by
    intro input
    simp [Verification.oracleHashWithHash, HasQuery.instOfMonadLift_query]
  have hopen : ∀ src (st : LState C), BaseInv P seeds none none src st →
      Opened commitment e message src st → st.1.2.1 (.opening bottomLayer e) ≠ none := by
    rintro src st h ⟨hb, c, hc, -⟩
    rw [← h.reveal]
    exact opening_revealed P seeds h e (by rw [hb]; simp) (by rw [hc]; simp)
  rw [signCodeword, sourceRoProgram_tweakable]
  simp only [simulateQ_bind, horacle]
  refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_inputCall P seeds Q s (commitmentInput P e ρ)
    (fun src st => Opened commitment e message src st) ?_) fun v => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  · intro src st h ho
    exact opening_not_charged P seeds _ e ρ (hiddenCandidate_commitmentInput P e ρ)
      (fun hm => by unfold IsMsg at hm; rw [byte23_commitment] at hm; cases hm) _ _
      (hopen src st h ho)
  split
  · simp only [simulateQ_pure]
    exact Walk.pure _ fun _ _ h => h.1
  · rename_i hpass
    have hpass' : truncateHash v = commitment := not_not.mp hpass
    simp only [simulateQ_bind, horacle]
    let A : SourceState C → LState C → Prop := fun src st => BaseInv P seeds none none src st ∧
      Opened commitment e message src st ∧ st.1.1.1.data.cache (.hash (commitmentInput P e ρ)) = some v
    refine Walk.conseq (c := 0 + 0) (Walk.bind (Walk.conseq (walk_inputCall P seeds Q s
      (randomizerInput P bottomLayer e ρ (littleEndianBytes 32 message)) A ?_) (fun _ _ h => ⟨h.1, h⟩)
      (Post' := fun y src st => BaseInv P seeds none none src st ∧
        SearchFree P seeds (grind P bottomLayer e (littleEndianBytes 32 message) (truncateHash y)
          randomizerAttemptLimit 0) st) ?_ le_rfl) fun y =>
      walk_resolvedHash P seeds Q s _ (candidateFree_grind P e _ _ _ _)) ?_
      (fun _ _ _ h => h) le_rfl
    · intro src st _ ha
      exact opening_not_charged P seeds _ e ρ (hiddenCandidate_randomizerInput P _ e ρ _)
        (fun hm => by unfold IsMsg at hm; rw [byte23_randomizer] at hm; cases hm) _ _
        (hopen src st ha.1 ha.2.1)
    · rintro y src' st' ⟨hinv, st0, ⟨hb0, ho, hcv⟩, x, hx, rfl, hst⟩
      refine ⟨hinv, ?_⟩
      have hrev := opening_revealed P seeds hb0 e (by rw [ho.1]; simp)
        (by rw [ho.2.choose_spec.1]; simp)
      have hprf := hb0.revealedCached e (by simp) hrev
      have hbound : st0.1.1.1.bound e = some message := (congrFun hb0.bound e).trans ho.1
      have hle := compilerImpl_cache_le P seeds _ _ x hx
      by_cases hρ : ρ = SigningGuessProof.cachedRandomizer seeds st0.1.1.1.data.cache e
      · subst hρ
        rcases base_step_trials P seeds st0.1.1 hb0.reachable e message hbound hprf x hx with
          hs | hres
        · left
          rw [hst]
          exact hs
        · right; right
          rw [SigningFlatEagerProof.baseGrind] at hres
          obtain ⟨w, hw, -⟩ := hres.of_map
          rw [hst]
          exact ⟨w, hw⟩
      · right; left
        obtain ⟨c, hc, hlow⟩ := ho.2
        rw [hst]
        exact secondOpening_mono P seeds hle (fun p w hp => compilerImpl_pending_keep P seeds _ _ x
          hx (fun _ _ h => by cases h) p w hp)
          (loose_base_second P seeds _ e ρ v c hcv hc (by rw [hlow, hpass']) hprf hρ)
    · rintro src st ⟨hinv, st0, ho, x, hx, rfl, hst⟩
      refine ⟨hinv, ?_, ?_⟩
      · obtain ⟨hb, c, hc, hlow⟩ := ho
        refine ⟨hb, c, ?_, hlow⟩
        rw [hst]
        exact compilerImpl_pending_keep P seeds _ _ x hx (fun _ _ h => by cases h) _ _ hc
      · rw [hst]
        exact compilerImpl_hash_cached P seeds _ _ x hx

end Codeword

section Units

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- A field that each answer of the oracles keeps stays along a run over the ledger. -/
theorem walk_keeps {α β : Type} {oa : SourceM C α} {Pre : SourceState C → LState C → Prop}
    {Post : α → SourceState C → LState C → Prop} {c : ℕ} {field : SourceState C → β} (v : β)
    (hk : SourceKeeps field oa) (h : Walk P seeds Q s Pre c Post oa) :
    Walk P seeds Q s (fun src st => Pre src st ∧ field src = v) c
      (fun a src st => Post a src st ∧ field src = v) oa := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq⟩ := h src st hp.1 r hr
  refine ⟨hl, hg, hq, ?_⟩
  rw [← hp.2]
  apply hk src r.1
  apply support_simulateQ_run'_subset (ownHybrid P seeds Q s) (oa.run src) st
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

/-- The commitment answer of a key with the low half of the commitment of a tree. -/
def TreeAt (e : KeyIndex) (tree : Option DeferredBottomTree) (st : LState C) : Prop :=
  ∀ t, tree = some t →
    ∃ c, st.1.1.1.data.pending (.commitment e) = some c ∧ c.low = .known (t.commitment e)

theorem TreeAt.grows {e : KeyIndex} {tree : Option DeferredBottomTree} {st st' : LState C}
    (hg : SigningOwnWalkBuild.Grows st st') (h : TreeAt e tree st) : TreeAt e tree st' := fun t ht => by
  obtain ⟨c, hc, hl⟩ := h t ht
  exact ⟨c, hg.pending _ _ hc, hl⟩

/-- The walk of `sourceBottomOnce` keeps `BaseInv` with no charged call, and a successful tree of
the key holds the low half of its commitment answer. -/
theorem walk_sourceBottomOnce_at (top : TopTree) (e : KeyIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun r src st => BaseInv P seeds none none src st ∧ TreeAt e r st)
      (sourceBottomOnce P seeds top (treeOf e)) := by
  have hk := bottomKey_treeOf e
  unfold sourceBottomOnce
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · rename_i r hr
    refine Walk.pure _ fun src st h => ⟨h.2, fun t ht => ?_⟩
    obtain ⟨rfl, h⟩ := h
    obtain ⟨c, hc, hl⟩ := h.treeCommit (treeOf e) (by rw [hr]; simp) ⟨e.val % 2 ^ layerHeight,
      Nat.mod_lt _ (by decide)⟩
    rw [hk] at hc hl
    exact ⟨c, hc, hl t (by rw [hr, ht])⟩
  · refine Walk.conseq (c := 0 + (0 + 0)) (Walk.bind (Walk.conseq (walk_sourceBottomTree_shape P
      seeds Q s top (treeOf e)) (fun _ _ h => h.2) (fun _ _ _ h => h) le_rfl) fun tree =>
      Walk.bind (Walk.modify (Post := fun _ src st => BaseInv P seeds none none src st ∧
        TreeAt e tree st) _ fun src st h => ⟨baseInv_store P seeds h.1.1 (treeOf e) tree h.1.2 h.2,
          fun t ht => ?_⟩) fun _ => Walk.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    obtain ⟨c, hc, hl⟩ := h.1.2 ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
    rw [hk] at hc hl
    exact ⟨c, hc, hl t ht⟩

end Units

section O1

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- A triple over the runs of an O1 source program. From each state of `Pre`, each run makes at
most `c` charged calls and ends in a state of `Post`. -/
def WalkO {α : Type} (Pre : SourceStateO1 C → LState C → Prop) (c : ℕ)
    (Post : α → SourceStateO1 C → LState C → Prop) (oa : SourceMO1 C α) : Prop :=
  ∀ src st, Pre src st → ∀ r ∈ support (runSourceL P seeds Q s oa src st),
    r.2.2.ledger ≤ st.2.ledger + c ∧ Post r.1.1 r.1.2 r.2

/-- An O1 source program keeps the signing state for each sequence of oracle answers. -/
def KeepsSigning {α : Type} (oa : SourceMO1 C α) : Prop :=
  ∀ src r, r ∈ support (oa.run src) → r.2.base.signing = src.base.signing

namespace WalkO

variable {P : PublicParameter} {seeds : C.Term → HashOutput} {Q : ℕ} {s : HiddenKey → Digest}

theorem conseq {α : Type} {oa : SourceMO1 C α} {Pre Pre' : SourceStateO1 C → LState C → Prop}
    {Post Post' : α → SourceStateO1 C → LState C → Prop} {c d : ℕ}
    (h : WalkO P seeds Q s Pre c Post oa) (hPre : ∀ src st, Pre' src st → Pre src st)
    (hPost : ∀ a src st, Post a src st → Post' a src st) (hcd : c ≤ d) :
    WalkO P seeds Q s Pre' d Post' oa := by
  intro src st hp r hr
  obtain ⟨hl, hq⟩ := h src st (hPre src st hp) r hr
  exact ⟨by omega, hPost _ _ _ hq⟩

theorem pure {α : Type} {Pre : SourceStateO1 C → LState C → Prop}
    {Post : α → SourceStateO1 C → LState C → Prop} (value : α)
    (h : ∀ src st, Pre src st → Post value src st) :
    WalkO P seeds Q s Pre 0 Post (Pure.pure value) := by
  intro src st hp r hr
  rw [runSourceL_pure, mem_support_pure_iff] at hr
  subst r
  exact ⟨Nat.le_add_right _ _, h src st hp⟩

theorem get {Pre : SourceStateO1 C → LState C → Prop} :
    WalkO P seeds Q s Pre 0 (fun a src st => a = src ∧ Pre src st)
      (MonadState.get : SourceMO1 C (SourceStateO1 C)) := by
  intro src st hp r hr
  rw [runSourceL_get, mem_support_pure_iff] at hr
  subst r
  exact ⟨Nat.le_add_right _ _, rfl, hp⟩

theorem modify {Pre : SourceStateO1 C → LState C → Prop}
    {Post : Unit → SourceStateO1 C → LState C → Prop} (f : SourceStateO1 C → SourceStateO1 C)
    (h : ∀ src st, Pre src st → Post () (f src) st) :
    WalkO P seeds Q s Pre 0 Post (modify f : SourceMO1 C Unit) := by
  intro src st hp r hr
  rw [runSourceL_modify, mem_support_pure_iff] at hr
  subst r
  exact ⟨Nat.le_add_right _ _, h src st hp⟩

theorem bind {α β : Type} {oa : SourceMO1 C α} {next : α → SourceMO1 C β}
    {Pre : SourceStateO1 C → LState C → Prop} {Mid : α → SourceStateO1 C → LState C → Prop}
    {Post : β → SourceStateO1 C → LState C → Prop} {c d : ℕ}
    (h : WalkO P seeds Q s Pre c Mid oa) (hn : ∀ a, WalkO P seeds Q s (Mid a) d Post (next a)) :
    WalkO P seeds Q s Pre (c + d) Post (oa >>= next) := by
  intro src st hp r hr
  rw [runSourceL_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨hla, hqa⟩ := h src st hp a ha
  obtain ⟨hlr, hqr⟩ := hn a.1.1 a.1.2 a.2 hqa r hr
  exact ⟨by omega, hqr⟩

/-- A triple of a base program gives a triple of its lift. -/
theorem liftBase {α : Type} {oa : SourceM C α} {Pre : SourceState C → LState C → Prop}
    {Post : α → SourceState C → LState C → Prop} {c : ℕ} (h : Walk P seeds Q s Pre c Post oa) :
    WalkO P seeds Q s (fun src st => Pre src.base st) c (fun a src st => Post a src.base st)
      (SigningLaneHybridCapO1Proof.liftBase oa) := by
  intro src st hp r hr
  rw [runSourceL_liftBase, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  obtain ⟨hl, -, hq⟩ := h src.base st hp a ha
  exact ⟨hl, hq⟩

theorem of_charges {α : Type} {oa : SourceMO1 C α} {c : ℕ}
    (h : SourceCharges P seeds Q s (fun _ => True) c oa) :
    WalkO P seeds Q s (fun src st => WalkInv P seeds src st) c
      (fun _ src st => WalkInv P seeds src st) oa := by
  intro src st hw r hr
  obtain ⟨hw', hl⟩ := h src st hw trivial r hr
  exact ⟨hl, hw'⟩

theorem to_charges {α : Type} {oa : SourceMO1 C α} {c : ℕ} {A : SourceStateO1 C → Prop}
    (h : WalkO P seeds Q s (fun src st => WalkInv P seeds src st ∧ A src) c
      (fun _ src st => WalkInv P seeds src st) oa) :
    SourceCharges P seeds Q s A c oa := by
  intro src st hw hp r hr
  obtain ⟨hl, hq⟩ := h src st ⟨hw, hp⟩ r hr
  exact ⟨hq, hl⟩

/-- A program that keeps the signing state keeps it along each run over the ledger. -/
theorem keeps {α : Type} {oa : SourceMO1 C α} {Pre : SourceStateO1 C → LState C → Prop}
    {Post : α → SourceStateO1 C → LState C → Prop} {c : ℕ} (sig : TsigState C)
    (hk : KeepsSigning oa) (h : WalkO P seeds Q s Pre c Post oa) :
    WalkO P seeds Q s (fun src st => Pre src st ∧ src.base.signing = sig) c
      (fun a src st => Post a src st ∧ src.base.signing = sig) oa := by
  intro src st hp r hr
  obtain ⟨hl, hq⟩ := h src st hp.1 r hr
  refine ⟨hl, hq, ?_⟩
  rw [← hp.2]
  apply hk src r.1
  apply support_simulateQ_run'_subset (ownHybrid P seeds Q s) (oa.run src) st
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

end WalkO

namespace KeepsSigning

theorem pure {α : Type} (value : α) : KeepsSigning (C := C) (Pure.pure value) := by
  intro src r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  rfl

theorem get : KeepsSigning (C := C) (MonadState.get : SourceMO1 C (SourceStateO1 C)) := by
  intro src r hr
  simp only [StateT.run_get, mem_support_pure_iff] at hr
  subst r
  rfl

theorem modify (f : SourceStateO1 C → SourceStateO1 C)
    (hf : ∀ src, (f src).base.signing = src.base.signing) :
    KeepsSigning (modify f : SourceMO1 C Unit) := by
  intro src r hr
  simp only [StateT.run_modify, mem_support_pure_iff] at hr
  subst r
  exact hf src

theorem bind {α β : Type} {oa : SourceMO1 C α} (h : KeepsSigning oa) (next : α → SourceMO1 C β)
    (hn : ∀ a, KeepsSigning (next a)) : KeepsSigning (oa >>= next) := by
  intro src r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact (hn a.1 a.2 r hr).trans (h src a ha)

theorem liftBase {α : Type} {oa : SourceM C α} (h : SourceKeeps SourceState.signing oa) :
    KeepsSigning (SigningLaneHybridCapO1Proof.liftBase oa) := by
  intro src r hr
  change r ∈ support ((fun r => (r.1, { src with base := r.2 })) <$> oa.run src.base) at hr
  rw [← bind_pure_comp] at hr
  obtain ⟨a, ha, hr⟩ := mem_support_bind_peel _ _ hr
  obtain rfl := eq_of_mem_support_pure _ hr
  exact h _ a ha

theorem mapM {α β : Type} (items : List α) (oa : α → SourceMO1 C β)
    (h : ∀ a ∈ items, KeepsSigning (oa a)) : KeepsSigning (items.mapM oa) := by
  induction items with
  | nil => exact KeepsSigning.pure []
  | cons a items ih =>
      rw [List.mapM_cons]
      exact (h a (List.mem_cons_self ..)).bind _ fun _ =>
        (ih fun b hb => h b (List.mem_cons_of_mem _ hb)).bind _ fun _ => KeepsSigning.pure _

theorem map {α β : Type} {oa : SourceMO1 C α} (h : KeepsSigning oa) (f : α → β) :
    KeepsSigning (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind _ fun _ => KeepsSigning.pure _

theorem sequenceFin {α : Type} : ∀ (n : ℕ) (oa : Fin n → SourceMO1 C α),
    (∀ i, KeepsSigning (oa i)) → KeepsSigning (OverPermutation.sequenceFin oa)
  | 0, _, _ => by simpa only [OverPermutation.sequenceFin] using KeepsSigning.pure _
  | n + 1, oa, h => by
      simp only [OverPermutation.sequenceFin]
      exact (h 0).bind _ fun _ => (sequenceFin n _ fun i => h i.succ).bind _ fun _ =>
        KeepsSigning.pure _

end KeepsSigning

theorem keepsSigning_sourceReleaseCovered (e : KeyIndex) (l : ChainIndex) :
    KeepsSigning (sourceReleaseCovered P seeds e l) := by
  unfold sourceReleaseCovered
  refine KeepsSigning.get.bind _ fun src0 => ?_
  split
  · exact KeepsSigning.liftBase ((sourceControl_sourceReleaseBottomSuffix P seeds e l _).comp
      Prod.fst)
  · exact KeepsSigning.pure ()

theorem keepsSigning_sourceReleaseKey (e : KeyIndex) :
    KeepsSigning (sourceReleaseKey P seeds e) := by
  unfold sourceReleaseKey
  exact (KeepsSigning.mapM _ _ fun l _ => keepsSigning_sourceReleaseCovered P seeds e l).bind _
    fun _ => KeepsSigning.pure ()

theorem charges_sourceReleaseCovered (e : KeyIndex) (l : ChainIndex) :
    SourceCharges P seeds Q s (fun _ => True) 0 (sourceReleaseCovered P seeds e l) := by
  unfold sourceReleaseCovered
  refine charges_get_bind P seeds Q s fun src0 => ?_
  split
  · exact SourceCharges.mono (charges_of_walk (walk_sourceReleaseBottomSuffix P seeds Q s e l _))
      (fun _ _ => trivial) le_rfl
  · exact SourceCharges.pure ()

theorem keepsSigning_round2Callback (prims : Primitives) (x : Keys3 C) (i : C.Party)
    (J : C.Quorum) (message : Message) (atThreshold : Bool) (p : Point) :
    KeepsSigning (SigningCompilerO1Slack.round2Callback prims x i J message atThreshold p) := by
  have hpart : KeepsSigning (SigningLaneHybridCapO1Proof.liftBase (sourcePart prims x i J p message)) :=
    KeepsSigning.liftBase ((sourceControl_sourcePart prims x i J p message).comp Prod.fst)
  unfold SigningCompilerO1Slack.round2Callback
  cases p with
  | chain lay key l pos =>
      unfold recordStart
      dsimp only
      refine KeepsSigning.bind (KeepsSigning.modify _ ?_) _ fun _ => ?_
      · intro _
        rfl
      split
      · exact (keepsSigning_sourceReleaseCovered x.1 x.2.1 _ _).bind _ fun _ => hpart
      · exact hpart
  | _ => exact hpart

theorem charges_round2Callback (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (i : C.Party) (J : C.Quorum) (message : Message) (atThreshold : Bool) (p : Point) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True) 0
      (SigningCompilerO1Slack.round2Callback prims x i J message atThreshold p) := by
  have hpart : SourceCharges x.1 x.2.1 Q s (fun _ => True) 0
      (SigningLaneHybridCapO1Proof.liftBase (sourcePart prims x i J p message)) := by
    unfold sourcePart
    exact charges_of_walk (walk_sourceEval x.1 x.2.1 Q s prims _ i J p message)
  unfold SigningCompilerO1Slack.round2Callback
  cases p with
  | chain lay key l pos =>
      unfold recordStart
      dsimp only
      refine SourceCharges.mono (c := 0 + 0) (SourceCharges.bind (SourceCharges.modify _ ?_) _
        fun _ => ?_) (fun _ h => h) le_rfl
      · exact fun src st h _ => walkInv_of_source h rfl rfl rfl
      split
      · exact SourceCharges.mono (c := 0 + 0) (SourceCharges.bind
          (charges_sourceReleaseCovered x.1 x.2.1 Q s _ _) _ fun _ => hpart) (fun _ h => h) le_rfl
      · exact hpart
  | _ => exact hpart

/-- The record of a signer at a key that is bound to the message keeps `WalkInv`. -/
theorem walkInv_release {src : SourceStateO1 C} {st : LState C} (h : WalkInv P seeds src st)
    (e : KeyIndex) (message : Message) (i : C.Party)
    (hb : src.base.signing.bound e = some message) :
    WalkInv P seeds { src with base := { src.base with signing := { src.base.signing with
      released := src.base.signing.released ++ [(e, message, i)] } } } st := by
  refine ⟨h.reveal, h.bound, h.ready, h.commitTerms, h.treeCommit, h.revealedCached, ?_,
    h.corruptBound, h.reachable, h.dirtySecond, h.storedTopShape⟩
  intro e' m' i' hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h.releasedBound e' m' i' hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact hb

/-- The codeword search and the chain parts of round 2 keep `WalkInv` and the signing state, and
make no charged call. -/
theorem walk_round2Values (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (i : C.Party) (J : C.Quorum) (tree : DeferredBottomTree) (e : KeyIndex)
    (message : Message) (parts : C.Party → Digest) (atThreshold : Bool)
    (hb : sig.bound e = some message) :
    WalkO x.1 x.2.1 Q s (fun src st => (BaseInv x.1 x.2.1 none none src.base st ∧
        TreeAt e (some tree) st) ∧ src.base.signing = sig) 0
      (fun _ src st => WalkInv x.1 x.2.1 src st ∧ src.base.signing = sig)
      (signRound2With (fun oa => SigningLaneHybridCapO1Proof.liftBase
        (sourceRoProgram prims x.1 x.2.1 oa))
        (SigningCompilerO1Slack.round2Callback prims x i J message atThreshold) x.1 J
        (tree.commitment e) e message parts) := by
  have hcode : Walk x.1 x.2.1 Q s (fun src st => (BaseInv x.1 x.2.1 none none src st ∧
      TreeAt e (some tree) st) ∧ src.signing = sig) 0
      (fun _ src st => BaseInv x.1 x.2.1 none none src st ∧ src.signing = sig)
      (sourceRoProgram prims x.1 x.2.1
        (signCodeword x.1 (tree.commitment e) e message (combine J parts))) := by
    refine Walk.conseq (walk_keeps x.1 x.2.1 Q s sig
      ((sourceControl_sourceRoProgram prims x.1 x.2.1 _).comp Prod.fst)
      (walk_signCodeword x.1 x.2.1 Q s prims (tree.commitment e) e message _)) ?_
      (fun _ _ _ h => h) le_rfl
    intro src st h
    exact ⟨⟨h.1.1, by rw [h.2]; exact hb, h.1.2 tree rfl⟩, h.2⟩
  unfold signRound2With
  refine WalkO.conseq (c := 0 + 0) (WalkO.bind (WalkO.liftBase hcode) fun r => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  rcases r with _ | ⟨randomness, encoding⟩
  · exact WalkO.pure _ fun src st h => ⟨(walkInv_iff x.1 x.2.1 src st).2 h.1, h.2⟩
  · refine WalkO.conseq (c := _ * 0 + 0) (WalkO.bind (WalkO.keeps sig ?_ (WalkO.of_charges
      (SourceCharges.sequenceFin _ _ fun l => ?_))) fun values =>
      WalkO.pure _ fun _ _ h => h) (fun src st h => ⟨(walkInv_iff x.1 x.2.1 src st).2 h.1, h.2⟩)
      (fun _ _ _ h => h) (by simp)
    · refine KeepsSigning.sequenceFin _ _ fun l => ?_
      split
      · exact (keepsSigning_round2Callback prims x i J message atThreshold _).map some
      · exact KeepsSigning.pure none
    · split
      · exact SourceCharges.map (charges_round2Callback prims x Q s i J message atThreshold _) some
      · exact SourceCharges.pure none

/-- Round 2 of the O1 source keeps `WalkInv` and makes no charged call. -/
theorem walk_round2 (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) :
    WalkO x.1 x.2.1 Q s (fun src st => WalkInv x.1 x.2.1 src st ∧ True) 0
      (fun _ src st => WalkInv x.1 x.2.1 src st)
      (sourceTsigO1 prims x top (.round2 i J e message parts)) := by
  rw [SigningCompilerO1Slack.sourceRound2O1_eq]
  refine WalkO.conseq (c := 0 + 0) (WalkO.bind WalkO.get fun src0 => ?_) (fun _ _ h => h)
    (fun _ _ _ h => h) le_rfl
  dsimp only
  split
  · exact WalkO.pure _ fun _ _ h => h.2.1
  · rename_i hg
    have hb : src0.base.signing.bound e = some message := by
      by_contra hne
      exact hg (Or.inr (Or.inr hne))
    have honce := walk_keeps x.1 x.2.1 Q s src0.base.signing
      (sourceSigning_sourceBottomOnce x.1 x.2.1 top (treeOf e))
      (walk_sourceBottomOnce_at x.1 x.2.1 Q s top e)
    refine WalkO.conseq (c := 0 + 0) (WalkO.bind (WalkO.liftBase honce) fun r => ?_) ?_
      (fun _ _ _ h => h) le_rfl
    · rcases r with _ | tree
      · exact WalkO.pure _ fun src st h => (walkInv_iff x.1 x.2.1 src st).2 h.1.1
      · have hpart : Walk x.1 x.2.1 Q s (fun src st => (BaseInv x.1 x.2.1 none none src st ∧
            TreeAt e (some tree) st) ∧ src.signing = src0.base.signing) 0
            (fun _ src st => (BaseInv x.1 x.2.1 none none src st ∧ TreeAt e (some tree) st) ∧
              src.signing = src0.base.signing)
            (sourcePart prims x i J (.randomizer bottomLayer e) message) := by
          unfold sourcePart
          exact walk_keeps x.1 x.2.1 Q s _ ((sourceControl_sourcePart prims x i J _ message).comp
            Prod.fst) (Walk.frame (TreeAt e (some tree)) (fun _ _ hg h => TreeAt.grows hg h)
              (walk_sourceEval x.1 x.2.1 Q s prims _ i J _ message))
        refine WalkO.conseq (c := 0 + (0 + 0)) (WalkO.bind (WalkO.liftBase hpart) fun own =>
          WalkO.bind (walk_round2Values prims x Q s src0.base.signing i J tree e message _ _ hb)
            fun r => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
        rcases r with _ | values
        · exact WalkO.pure _ fun src st h => h.1
        · have hmod : ∀ src st, WalkInv x.1 x.2.1 src st ∧ src.base.signing = src0.base.signing →
              WalkInv x.1 x.2.1 { src with base := { src.base with signing := { src.base.signing with
                released := src.base.signing.released ++ [(e, message, i)] } } } st :=
            fun src st h => walkInv_release x.1 x.2.1 h.1 e message i (by rw [h.2]; exact hb)
          dsimp only
          split
          · exact WalkO.conseq (c := 0 + (0 + 0)) (WalkO.bind (WalkO.keeps _
              (keepsSigning_sourceReleaseKey x.1 x.2.1 e)
              (WalkO.of_charges (charges_sourceReleaseKey x.1 x.2.1 Q s e))) fun _ => WalkO.bind
              (WalkO.modify (Post := fun _ src st => WalkInv x.1 x.2.1 src st) _ hmod) fun _ =>
              WalkO.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
          · exact WalkO.conseq (c := 0 + 0) (WalkO.bind
              (WalkO.modify (Post := fun _ src st => WalkInv x.1 x.2.1 src st) _ hmod) fun _ =>
              WalkO.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    · rintro src st ⟨rfl, hw, -⟩
      exact ⟨(walkInv_iff x.1 x.2.1 _ st).1 hw, rfl⟩

/-- A round-2 request makes at most one charged call, as `charges_oracle` states it at a round-2
request. It makes none. -/
theorem charges_round2 (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True)
      (if SigningOwnCounted (.inr (.round2 i J e message parts) : (LocalSpec C + TsigSpec C).Domain)
        then 1 else 0)
      (sourceOraclesO1 prims x top (.inr (.round2 i J e message parts))) := by
  refine SourceCharges.mono (c := 0 + (0 + 0)) ?_ (fun _ h => h) (Nat.zero_le _)
  unfold sourceOraclesO1
  exact SourceCharges.bind (WalkO.to_charges (walk_round2 prims x Q s top i J e message parts)) _
    fun _ => SourceCharges.bind (SourceCharges.modify _ fun src st h _ =>
      walkInv_of_source h rfl rfl rfl) _ fun _ => SourceCharges.pure _

end O1

section Tail

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- A key with `t` signers, at most `t - 1` of them corrupt, has a release record. So it is bound to
the message. -/
theorem bound_of_signers (sig : TsigState C) (e : KeyIndex) (message : Message)
    (hcorrupt : sig.corrupt.card ≤ C.t - 1) (hrel : SigningGuessProof.ReleasedBound sig)
    (hsigners : C.t ≤ (signersAt sig e message).card) : sig.bound e = some message := by
  have ht := C.one_le_t
  have hcard := Finset.card_union_le sig.corrupt
    ((sig.released.filter fun r => r.1 = e ∧ r.2.1 = message).map (·.2.2)).toFinset
  unfold signersAt at hsigners
  obtain ⟨i, hi⟩ : (((sig.released.filter fun r => r.1 = e ∧ r.2.1 = message).map
      (·.2.2)).toFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.union_empty] at hsigners
    omega
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨⟨e', m', i'⟩, ⟨hm, rfl, rfl⟩, -⟩ := hi
  exact hrel _ _ _ hm

/-- The reveals of the top chain values of a tree of `TopShape` make no charged call. -/
theorem walk_topValues (tree : DeferredBottomTree) (hshape : TopShape tree) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (OverPermutation.sequenceFin fun l => sourceRevealDigest (tree.topSignature.chainValue l)) := by
  refine Walk.conseq (Walk.sequenceFin (c := 0) _ _ _ fun l => ?_) (fun _ _ h => h)
    (fun _ _ _ h => h) (by simp)
  cases hv : tree.topSignature.chainValue l with
  | known value => exact Walk.pure _ fun _ _ h => h
  | secret k =>
      exact Walk.conseq (walk_sourceReveal P seeds Q s (readyEx := none) (cachedEx := none)
        (readyEx' := none) (cachedEx' := none) k (fun _ _ h => by cases h)
        (fun e _ => hshape l k hv e) (fun _ h => h) (fun _ _ => True) (fun _ _ _ _ => trivial))
        (fun _ _ h => ⟨h, trivial⟩) (fun _ _ _ h => h.1) le_rfl

/-- `walk_sourceBottomTree` at the key of a tree. -/
theorem walk_sourceBottomTree_at (top : TopTree) (e : KeyIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun r src st => BaseInv P seeds none none src st ∧ TreeAt e r st)
      (sourceBottomTree P seeds top (treeOf e)) := by
  refine Walk.conseq (walk_sourceBottomTree P seeds Q s top (treeOf e)) (fun _ _ h => h) ?_ le_rfl
  rintro r src st ⟨h, hr⟩
  refine ⟨h, fun t ht => ?_⟩
  obtain ⟨c, hc, hl⟩ := hr ⟨e.val % 2 ^ layerHeight, Nat.mod_lt _ (by decide)⟩
  rw [bottomKey_treeOf] at hc hl
  exact ⟨c, hc, hl t ht⟩

/-- Two triples of one program give the triple of the conjunction. -/
theorem walk_and {α : Type} {oa : SourceM C α} {Pre : SourceState C → LState C → Prop}
    {Post Post' : α → SourceState C → LState C → Prop} {c : ℕ}
    (h : Walk P seeds Q s Pre c Post oa) (h' : Walk P seeds Q s Pre c Post' oa) :
    Walk P seeds Q s Pre c (fun a src st => Post a src st ∧ Post' a src st) oa := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq⟩ := h src st hp r hr
  exact ⟨hl, hg, hq, (h' src st hp r hr).2.2⟩

/-- The honest signature tail at a key that is bound to the message makes no charged call, when the
second build gives a tree of `TopShape`. -/
theorem walk_honestSignature_of_shape (prims : Primitives) (x : Keys3 C) (Q : ℕ)
    (s : HiddenKey → Digest) (top : TopTree) (e : KeyIndex) (message : Message)
    (hshape : Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none) 0
      (fun r _ _ => ∀ tree, r = some tree → TopShape tree)
      (sourceBottomTree x.1 x.2.1 top (treeOf e))) :
    Walk x.1 x.2.1 Q s (fun src st => BaseInv x.1 x.2.1 none none src st ∧
        src.signing.bound e = some message) 0
      (fun _ => BaseInv x.1 x.2.1 none none) (sourceHonestSignature prims x top e message) := by
  suffices h : ∀ sig : TsigState C, sig.bound e = some message →
      Walk x.1 x.2.1 Q s (fun src st => BaseInv x.1 x.2.1 none none src st ∧ src.signing = sig) 0
        (fun _ => BaseInv x.1 x.2.1 none none) (sourceHonestSignature prims x top e message) by
    intro src st hp
    exact h src.signing hp.2 src st ⟨hp.1, rfl⟩
  intro sig hb
  have hbuild := walk_keeps x.1 x.2.1 Q s sig
    ((sourceControl_sourceBottomTree x.1 x.2.1 top (treeOf e)).comp Prod.fst)
    (walk_and x.1 x.2.1 Q s (walk_sourceBottomTree_at x.1 x.2.1 Q s top e) hshape)
  have hframe : ∀ (tree : DeferredBottomTree) {α : Type} (oa : SourceM C α),
      SourceKeeps (sourceControl (C := C)) oa →
      Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none) 0 (fun _ => BaseInv x.1 x.2.1 none none) oa →
      Walk x.1 x.2.1 Q s (fun src st => (BaseInv x.1 x.2.1 none none src st ∧
        TreeAt e (some tree) st) ∧ src.signing = sig) 0
        (fun _ src st => (BaseInv x.1 x.2.1 none none src st ∧ TreeAt e (some tree) st) ∧
          src.signing = sig) oa :=
    fun tree _ oa hk h => walk_keeps x.1 x.2.1 Q s sig (hk.comp Prod.fst)
      (Walk.frame (TreeAt e (some tree)) (fun _ _ hg h => TreeAt.grows hg h) h)
  unfold sourceHonestSignature
  refine Walk.conseq (c := 0 + 0) (Walk.bind hbuild fun r => ?_) (fun _ _ h => h)
    (fun _ _ _ h => h) le_rfl
  rcases r with _ | tree
  · exact Walk.pure _ fun _ _ h => h.1.1.1
  · refine Walk.assume x.1 x.2.1 Q s (TopShape tree) (fun _ _ h => h.1.2 tree rfl) fun hts => ?_
    have hrelease := hframe tree _ (sourceControl_sourceReleaseOpening x.1 x.2.1 e)
      (Walk.conseq (walk_sourceReleaseOpening x.1 x.2.1 Q s e)
        (fun _ _ h => BaseInv.weaken_ready x.1 x.2.1 h e) (fun _ _ _ h => h) le_rfl)
    have hopening := hframe tree _ (sourceControl_sourceRoProgram prims x.1 x.2.1 _)
      (walk_prfValue x.1 x.2.1 Q s prims x.2.1 (.randomizer bottomLayer e))
    refine Walk.conseq (c := 0 + (0 + (0 + 0))) (Walk.bind hrelease fun _ => Walk.bind hopening
      fun opening => Walk.bind (Walk.conseq (walk_signCodeword x.1 x.2.1 Q s prims
        (tree.commitment e) e message opening) (Pre' := fun src st => (BaseInv x.1 x.2.1 none none
          src st ∧ TreeAt e (some tree) st) ∧ src.signing = sig)
        (fun src st h => ⟨h.1.1, by rw [h.2]; exact hb, h.1.2 tree rfl⟩) (fun _ _ _ h => h)
        le_rfl) fun r => ?_) (fun src st (h : ((BaseInv x.1 x.2.1 none none src st ∧
          TreeAt e (some tree) st) ∧ ∀ t, some tree = some t → TopShape t) ∧ src.signing = sig) =>
          ⟨h.1.1, h.2⟩) (fun _ _ _ h => h) le_rfl
    rcases r with _ | ⟨randomness, encoding⟩
    · exact Walk.pure _ fun _ _ h => h
    · have hvalues : Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none) (chainCount * 0)
          (fun _ => BaseInv x.1 x.2.1 none none) (OverPermutation.sequenceFin fun l =>
            if (encoding l).val = 3 then Pure.pure (tree.cpk e l).2.2 else do
              sourceReleaseBottomSuffix x.1 x.2.1 e l (encoding l)
              let value ← sourceRoProgram prims x.1 x.2.1
                (prfValue x.2.1 (.chain bottomLayer e l (encoding l)))
              Pure.pure (if (encoding l).val = 0 then value else
                (if (encoding l).val = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ value)) :=
        Walk.sequenceFin _ _ _ fun l => by
          split
          · exact Walk.pure _ fun _ _ h => h
          · exact Walk.conseq (c := 0 + (0 + 0)) (Walk.bind
              (walk_sourceReleaseBottomSuffix x.1 x.2.1 Q s e l _) fun _ => Walk.bind
              (walk_prfValue x.1 x.2.1 Q s prims x.2.1 _) fun _ => Walk.pure _ fun _ _ h => h)
              (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
      exact Walk.conseq (c := chainCount * 0 + (0 + (0 + 0))) (Walk.bind hvalues fun _ =>
        Walk.bind (walk_hashProgram x.1 x.2.1 Q s _ (free_merklePath x.1 _ _ _)) fun _ =>
        Walk.bind (walk_topValues x.1 x.2.1 Q s tree hts) fun _ => Walk.pure _ fun _ _ h => h)
        (fun _ _ h => h) (fun _ _ _ h => h) (by simp)

set_option maxRecDepth 100000 in
/-- `charges_tail`, when the second build gives a tree of `TopShape`. -/
theorem charges_tail_of_shape (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (e : KeyIndex) (message : Message)
    (hshape : Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none) 0
      (fun r _ _ => ∀ tree, r = some tree → TopShape tree)
      (sourceBottomTree x.1 x.2.1 top (treeOf e))) :
    SourceCharges x.1 x.2.1 Q s
      (fun src => C.t ≤ (signersAt src.base.signing e message).card) 0
      (liftBase (sourceHonestSignature prims x top e message)) := by
  refine SourceCharges.liftBase fun src st hw hp r hr => ?_
  have hb := (walkInv_iff x.1 x.2.1 src st).1 hw
  obtain ⟨hl, -, hq⟩ := walk_honestSignature_of_shape prims x Q s top e message hshape src.base st
    ⟨hb, bound_of_signers _ e message hb.corruptBound hb.releasedBound hp⟩ r hr
  exact ⟨(walkInv_iff x.1 x.2.1 _ r.2).2 hq, hl⟩

/-- The honest-signature tail at a key with `t` signers makes no charged call. The key has a release
record, because at most `t - 1` operators are corrupt and `1 ≤ t`. So it is bound to the message,
and the base call of the tail is canonical. -/
theorem charges_tail (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (e : KeyIndex) (message : Message) :
    SourceCharges x.1 x.2.1 Q s
      (fun src => C.t ≤ (signersAt src.base.signing e message).card) 0
      (liftBase (sourceHonestSignature prims x top e message)) :=
  charges_tail_of_shape prims x Q s top e message (Walk.conseq
    (walk_sourceBottomTree_shape x.1 x.2.1 Q s top (treeOf e)) (fun _ _ h => h)
    (fun _ _ _ h => h.2) le_rfl)

end Tail

end ThresholdLeanXmssSecurity.SigningOwnWalkRound2

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.compilerImpl_hash_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.compilerImpl_hash_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.base_step_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.base_step_trials

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.loose_base_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.loose_base_second

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.lazyRun_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.lazyRun_query_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_resolvedHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_resolvedHash

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.candidateFree_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.candidateFree_grind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.sourceRoProgram_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.sourceRoProgram_tweakable

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_inputCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_inputCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.opening_not_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.opening_not_charged

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.opening_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.opening_revealed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_signCodeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_signCodeword

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_keeps

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.TreeAt.grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.TreeAt.grows

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_sourceBottomOnce_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_sourceBottomOnce_at

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.conseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.conseq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.get

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.modify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.liftBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.of_charges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.of_charges

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.to_charges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.to_charges

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.WalkO.keeps

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.get

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.modify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.liftBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.map

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.KeepsSigning.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.keepsSigning_sourceReleaseCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.keepsSigning_sourceReleaseCovered

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.keepsSigning_sourceReleaseKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.keepsSigning_sourceReleaseKey

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_sourceReleaseCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_sourceReleaseCovered

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.keepsSigning_round2Callback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.keepsSigning_round2Callback

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_round2Callback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_round2Callback

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walkInv_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walkInv_release

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_round2Values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_round2Values

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_round2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_round2

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_round2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_round2

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.bound_of_signers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.bound_of_signers


/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_topValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_topValues

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_sourceBottomTree_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_sourceBottomTree_at

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_and

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_honestSignature_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.walk_honestSignature_of_shape

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_tail_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_tail_of_shape

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkRound2.charges_tail
