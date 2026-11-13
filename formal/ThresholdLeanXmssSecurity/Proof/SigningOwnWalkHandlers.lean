import ThresholdLeanXmssSecurity.Proof.SigningOwnWalkBuild
import ThresholdLeanXmssSecurity.Proof.SigningOwnForger

/-!
# The walk of the oracle handlers over the ledger

A local call, a corruption, round 1 and a call of the verification keep `WalkInv`. Each makes at
most the charged calls that the own budget counts at its query.

* A local call makes one backend `.hash` call, and its charge is at most one (`charges_local`).
* A corruption and round 1 use the units of the base source. Their PRF and mask calls are no
  `.hash (.hash _)` call, so they make no charged call (`charges_corrupt`, `charges_round1`).
* Round 1 binds the key before it releases a ready opening. `baseInv_bind` treats the binding with
  an exception of `ready` at the key, and the release or the test of readiness closes it.
* A call of the verification makes one backend `.hash` call, and its charge is at most one
  (`charges_verify`).
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnWalkHandlers

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Clean SigningOwnLedger SigningOwnFree SigningOwnWalk SigningOwnWalkBuild
open SigningOwnForger

variable {C : Committee}

attribute [local instance] Classical.propDecidable

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

section Hash

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- A hash call that makes no key ready with no revealed opening. A charged call needs `1 ≤ c`. -/
theorem walk_hashCall (q : Query C) (A : SourceState C → LState C → Prop) (c : ℕ)
    (hc : ∀ input, q = .hash input → 1 ≤ c)
    (hready : ∀ src st, BaseInv P seeds none none src st → A src st →
      ∀ x ∈ support ((compilerImpl P seeds (.hash q)).run st.1.1.1), ∀ e,
        OpeningReady seeds x.2.data src.signing e →
          OpeningReady seeds st.1.1.1.data src.signing e ∨
            src.revealed (.opening bottomLayer e) ≠ none ∨ (none : Option KeyIndex) = some e) :
    Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧ A src st) c
      (fun _ => BaseInv P seeds none none) (liftM (deferredQuery (C := C) (.hash q))) := by
  refine Walk.conseq (walk_query P seeds Q s (.hash q) _ c (fun _ _ h => by cases h)
    (fun _ _ _ ⟨input, he, _⟩ => hc input (by injection he))) (fun _ _ h => h) ?_ le_rfl
  rintro y src' st' ⟨st, hp, x, hx, rfl, flag, rfl⟩
  exact baseInv_step P seeds hp.1 hx (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (hready _ _ hp.1 hp.2 x hx) (fun e he => commit_plain P seeds _ (fun _ h => by cases h)
      (fun _ _ h => by cases h) st x hx e he) flag

/-- `walk_sourceReleaseOpening` of `SigningOwnWalkBuild.lean`, which also states that the opening
is revealed at the end. -/
theorem walk_sourceReleaseOpening_revealed (e : KeyIndex) :
    Walk P seeds Q s (BaseInv P seeds (some e) none) 0
      (fun _ src st => BaseInv P seeds none none src st ∧
        src.revealed (.opening bottomLayer e) ≠ none)
      (sourceReleaseOpening P seeds e) := by
  unfold sourceReleaseOpening
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · let K : HiddenKey := .opening bottomLayer e
    let R : SourceState C → LState C → Prop := fun src _ => src.revealed K ≠ none
    have hplants : ∀ src1 : SourceState C, Walk P seeds Q s
        (fun src st => BaseInv P seeds none none src st ∧ R src st) 0
        (fun _ src st => BaseInv P seeds none none src st ∧ R src st)
        ((src1.allocated.filter fun p => decide (p.key = K)).mapM (sourcePlant P)) := by
      intro src1
      refine Walk.conseq (Walk.mapM (c := 0) _ (sourcePlant P) _ fun p hp => ?_) (fun _ _ h => h)
        (fun _ _ _ h => h) (by simp)
      have hk : p.key = K := of_decide_eq_true (List.mem_filter.mp hp).2
      exact Walk.conseq (walk_sourcePlant P seeds Q s p K)
        (fun _ _ h => ⟨h.1, fun _ _ => by rw [hk]; exact h.2, h.2⟩)
        (fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    refine Walk.conseq (c := 0 + (0 + (0 + (0 + (0 + 0))))) (Walk.bind (Walk.conseq
      (walk_sourceReveal P seeds Q s (readyEx := some e) (cachedEx := none) (readyEx' := none)
        (cachedEx' := some e) K ?_ ?_ ?_ (fun _ _ => True) (fun _ _ _ _ => trivial))
      (fun _ _ h => ⟨h.2, trivial⟩) (fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl) fun value =>
      Walk.bind (Walk.conseq (Post' := fun _ src st => BaseInv P seeds none none src st ∧ R src st)
        (walk_completePrf P seeds Q s (readyEx := none) (cachedEx := some e)
        (.randomizer bottomLayer e) value R (fun _ _ _ _ h => h) ?_) (fun _ _ h => h)
        (fun _ src st h => ⟨BaseInv.close_cached P seeds h.1 h.2.2, h.2.1⟩) le_rfl) fun ok =>
      Walk.bind (Walk.modify (Post := fun _ src st => BaseInv P seeds none none src st ∧ R src st) _
        fun src st h => ⟨BaseInv.of_source P seeds (src := src) h.1 rfl rfl rfl, h.2⟩) fun _ =>
      Walk.bind Walk.get fun src1 => Walk.bind (Walk.conseq (hplants src1) (fun _ _ h => h.2)
        (fun _ _ _ h => h) le_rfl) fun _ => Walk.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    · intro e' hne hre
      cases hre
      rfl
    · intro e' hne hke
      have he : e = e' := by
        simp only [K, HiddenKey.opening.injEq] at hke
        exact hke.2
      exact hne (by rw [he])
    · intro _ _
      simp
    · intro src st h e' he
      cases he
      exact h
  · rename_i hrev
    refine Walk.pure _ fun src st h => ?_
    obtain ⟨rfl, h⟩ := h
    refine ⟨baseInv_revealed P seeds h (.opening bottomLayer e) ?_ ?_ (fun _ _ => by simp), ?_⟩
    · simpa using hrev
    · intro e' _ hre
      cases hre
      rfl
    · simpa using hrev

/-- A hash call at a query that is no PRF query at a bottom randomizer keeps readiness. -/
theorem hash_ready_plain (q : Query C) (hq : ∀ seed e, q ≠ .prf seed (.randomizer bottomLayer e))
    (src : SourceState C) (st : LState C)
    (x : DeferredSpec C (.hash q) × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.hash q)).run st.1.1.1)) (e : KeyIndex)
    (h : OpeningReady seeds x.2.data src.signing e) :
    OpeningReady seeds st.1.1.1.data src.signing e ∨
      src.revealed (.opening bottomLayer e) ≠ none ∨ (none : Option KeyIndex) = some e :=
  ready_plain P seeds (.hash q) (fun _ _ h => by cases h) (fun _ e' h => hq _ e' h) src st x hx e h

/-- A hash call at the PRF query of a bottom randomizer that does not complete the key, by the test
`ReadyAfter` on the backend before the call, leaves the key unready. -/
theorem hash_not_ready (seed : HashOutput) (e : KeyIndex) (sig : TsigState C)
    (st : CompilerBackend C) (src : SourceState C) (hsig : src.signing = sig)
    (hn : ¬ReadyAfter seeds st.data sig e (.prf seed (.randomizer bottomLayer e)))
    (x : DeferredSpec C (.hash (.prf seed (.randomizer bottomLayer e))) × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.hash (.prf seed (.randomizer bottomLayer e)))).run
      st)) :
    ¬OpeningReady seeds x.2.data sig e := by
  intro h
  obtain ⟨T, hv, hc, hq⟩ := not_readyAfter_missing seeds st.data src e
    (.prf seed (.randomizer bottomLayer e)) (hsig ▸ h.1) (hsig ▸ hn)
  rcases h.2 T with hm | hm
  · rcases (compilerImpl_frame P seeds _ st x hx).1 T _ hm with hm | hm
    · exact hv hm
    · cases hm
  · rw [compilerImpl_prf_frame P seeds _ st x hx _ _ (fun h => hq h), hc] at hm
    cases hm

/-- `sourceHash` keeps `BaseInv`. A charged call needs `1 ≤ c`. -/
theorem walk_sourceHash (q : Query C) (c : ℕ) (hc : ∀ input, q = .hash input → 1 ≤ c) :
    Walk P seeds Q s (BaseInv P seeds none none) c (fun _ => BaseInv P seeds none none)
      (sourceHash P seeds q) := by
  by_cases hq : ∃ seed e, q = .prf seed (.randomizer bottomLayer e)
  · obtain ⟨seed, e, rfl⟩ := hq
    have hother : ∀ e', e' ≠ e → ∀ T, (Query.prf seed (.randomizer bottomLayer e) : Query C) ≠
        .prf (seeds T) (.randomizer bottomLayer e') := fun e' hne T h => by
      injection h with h1 h2
      injection h2 with h3 h4
      exact hne h4.symm
    unfold sourceHash
    dsimp only
    simp only [↓reduceIte]
    refine Walk.conseq (c := 0 + (0 + c)) (Walk.bind (walk_snapshot P seeds Q s (fun _ _ => True)
      (fun _ _ _ _ h => h)) fun y => Walk.bind Walk.get fun src0 => ?_)
      (fun _ _ h => ⟨h, trivial⟩) (fun _ _ _ h => h) (by omega)
    split
    · refine Walk.conseq (c := 0 + c) (Walk.bind (walk_sourceReleaseOpening_revealed P seeds Q s e)
        fun _ => walk_hashCall P seeds Q s _ (fun src _ => src.revealed (.opening bottomLayer e) ≠ none)
          c hc ?_) (fun _ _ h => BaseInv.weaken_ready P seeds h.2.1 e) (fun _ _ _ h => h) (by omega)
      intro src st _ hrev x hx e' hr
      by_cases he : e' = e
      · subst he
        exact Or.inr (Or.inl hrev)
      · exact Or.inl (openingReady_back P seeds _ _ x hx _ e' (fun _ h => by cases h)
          (fun T h => hother e' he T h) hr)
    · rename_i hn
      refine Walk.conseq (c := 0 + c) (Walk.bind (Walk.pure () fun _ _ h => h) fun _ =>
        walk_hashCall P seeds Q s _ (fun src st => src = src0 ∧ st.1.1.1.data = y) c hc ?_)
        (fun _ _ h => ⟨h.2.1, h.1.symm, h.2.2.2⟩) (fun _ _ _ h => h) (by omega)
      rintro src st _ ⟨rfl, hy⟩ x hx e' hr
      by_cases he : e' = e
      · subst he
        exact absurd hr (hash_not_ready P seeds seed e' src.signing st.1.1.1 src rfl
          (by rw [hy]; exact hn) x hx)
      · exact Or.inl (openingReady_back P seeds _ _ x hx _ e' (fun _ h => by cases h)
          (fun T h => hother e' he T h) hr)
  · have hplain : ∀ seed e, q ≠ .prf seed (.randomizer bottomLayer e) :=
      fun seed e h => hq ⟨seed, e, h⟩
    have hjp := Walk.conseq (walk_hashCall P seeds Q s q (fun _ _ => True) c hc
      (fun src st _ _ x hx e h => hash_ready_plain P seeds q hplain src st x hx e h))
      (fun _ _ h => ⟨h, trivial⟩) (fun _ _ _ h => h) le_rfl
    unfold sourceHash
    dsimp only
    split
    · rename_i seed lay e
      have hlay : lay ≠ bottomLayer := fun h => hq ⟨seed, e, by rw [h]⟩
      simp only [hlay, ↓reduceIte, pure_bind]
      exact hjp
    · simp only [pure_bind]
      exact hjp

/-- A map of a program that keeps an invariant. -/
theorem walk_map {α β : Type} {oa : SourceM C α} {I : SourceState C → LState C → Prop} {c : ℕ}
    (h : Walk P seeds Q s I c (fun _ => I) oa) (f : α → β) :
    Walk P seeds Q s I c (fun _ => I) (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact Walk.conseq (c := c + 0) (Walk.bind h fun _ => Walk.pure _ fun _ _ h => h)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- The part of an operator at a point makes no charged call. -/
theorem walk_sourceEval (prims : Primitives) (keys : Keys C) (i : C.Party) (J : C.Quorum)
    (p : Point) (message : Message) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceRoProgram prims P seeds (eval keys i J p message)) := by
  simp only [sourceRoProgram, eval, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  simp only [prf, hashQuery, HasQuery.instOfMonadLift_query, simulateQ_map, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map, sourceRo]
  exact Walk.conseq (c := _ * 0 + (_ * 0 + 0)) (Walk.bind (Walk.mapM _ _ _ fun T _ =>
    walk_map P seeds Q s (walk_sourceHash P seeds Q s _ 0 fun _ h => by cases h) _) fun _ =>
      Walk.bind (Walk.mapM _ _ _ fun j _ => walk_map P seeds Q s
        (walk_sourceHash P seeds Q s _ 0 fun _ h => by cases h) _) fun _ =>
      Walk.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (by simp)

/-- The binding of a key to a message that the key allows keeps `BaseInv`, with the exception of
`ready` at the key. -/
theorem baseInv_bind {src : SourceState C} {st : LState C} (h : BaseInv P seeds none none src st)
    (e : KeyIndex) (message : Message)
    (hfree : src.signing.bound e = none ∨ src.signing.bound e = some message)
    {x : Unit × CompilerBackend C}
    (hx : x ∈ support ((compilerImpl P seeds (.bindKey e message)).run st.1.1.1)) (flag : Bool) :
    BaseInv P seeds (some e) none
      { src with signing :=
        { src.signing with bound := Function.update src.signing.bound e (some message) } }
      (((x.2, st.1.1.2 + if deferredCounted (C := C) (.bindKey e message) then 1 else 0),
        st.1.2.1, flag), ownAux P seeds (.bindKey e message) (st.1.1, st.1.2.1) st.2) := by
  have hreach : CompilerReachable P seeds
      (x.2, st.1.1.2 + if deferredCounted (C := C) (.bindKey e message) then 1 else 0) := by
    refine CompilerReachable.step (.bindKey e message) st.1.1 (x.1, (x.2, _)) h.reachable ?_
    simp only [countImpl, StateT.run_mk, support_map]
    exact ⟨x, hx, rfl⟩
  simp only [compilerImpl, StateT.run] at hx
  subst hx
  refine ⟨h.reveal, ?_, fun e' hne hr => ?_, h.commitTerms, h.treeCommit, h.revealedCached, ?_,
    h.corruptBound, hreach, ?_⟩
  · change (if st.1.1.1.bound e = none then Function.update st.1.1.1.bound e (some message)
      else st.1.1.1.bound) = _
    rw [h.bound]
    rcases hfree with hb | hb
    · rw [if_pos hb]
    · rw [if_neg (by rw [hb]; simp)]
      funext e'
      by_cases he : e' = e
      · subst he
        simp [hb]
      · simp [Function.update_of_ne he]
  · have he : e' ≠ e := fun he => hne (by rw [he])
    refine h.ready e' (by simp) ⟨?_, hr.2⟩
    have := hr.1
    simpa [Function.update_of_ne he] using this
  · intro e' m' i' hm
    have hold := h.releasedBound e' m' i' hm
    by_cases he : e' = e
    · subst he
      rcases hfree with hb | hb
      · rw [hb] at hold
        cases hold
      · rw [hb] at hold
        cases hold
        simp
    · simpa [Function.update_of_ne he] using hold
  · intro hd
    change (st.2.dirty || decide (SecondOpening P seeds st.1.1.1.data)) = true at hd
    rcases Bool.or_eq_true_iff.mp hd with hd | hd
    · exact h.dirtySecond hd
    · exact of_decide_eq_true hd

/-- A pad call keeps a fact on the source. -/
theorem walk_pad_source (point : Point) (B : SourceState C → Prop) :
    Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧ B src) 0
      (fun _ src st => BaseInv P seeds none none src st ∧ B src)
      (liftM (deferredQuery (C := C) (.pad point))) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq, hsrc, -⟩ := plain_run P seeds Q s (.pad point)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) src st hp.1 r hr
  rw [hsrc]
  exact ⟨hl, hg, hq, hp.2⟩

/-- The release of a bottom chain suffix keeps `BaseInv` and makes no charged call. -/
theorem walk_sourceReleaseBottomSuffix (e : KeyIndex) (l : ChainIndex) (start : Digit) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceReleaseBottomSuffix P seeds e l start) := by
  unfold sourceReleaseBottomSuffix
  dsimp only
  let I : List XmssSecurity.ChainStep → SourceState C → LState C → Prop := fun done src st =>
    BaseInv P seeds none none src st ∧ ∀ p ∈ done, src.revealed (.bottomChain e l p) ≠ none
  have hupdate : ∀ (k k' : HiddenKey) (src : SourceState C) (v : Digest),
      src.revealed k' ≠ none → Function.update src.revealed k (some v) k' ≠ none := by
    intro k k' src v h
    by_cases he : k' = k
    · subst he
      simp
    · simpa only [Function.update_of_ne he] using h
  refine Walk.conseq (c := _ * 0 + (_ * 0 + 0)) (Walk.bind (Walk.mapM_prefix _ I _ []
    fun pre a post _ => ?_) fun _ => Walk.bind (Walk.mapM _ _ _ fun a ha => ?_) fun _ =>
      Walk.pure _ fun _ _ h => h.1) (fun _ _ h => ⟨h, fun _ hp => by cases hp⟩)
    (fun _ _ _ h => h) (by simp)
  · let B : SourceState C → Prop := fun src =>
      ∀ p ∈ pre ++ [a], src.revealed (.bottomChain e l p) ≠ none
    have hrest : ∀ (point : Point), (∀ e', point ≠ .randomizer bottomLayer e') → ∀ target,
        Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧ B src) 0
          (fun _ => I (pre ++ [a]))
          (do
            let ok ← liftM (completePrf seeds point target)
            modify fun (st : SourceState C) => { st with consistent := st.consistent && ok }) :=
      fun point hpt target => Walk.conseq (c := 0 + 0) (Walk.bind (walk_completePrf P seeds Q s
        (readyEx := none) (cachedEx := none) point target (fun src _ => B src)
        (fun _ _ _ _ h => h) (fun _ _ _ e' he => absurd he (hpt e'))) fun ok =>
          Walk.modify (Post := fun _ => I (pre ++ [a])) _ fun src st h =>
            ⟨BaseInv.of_source P seeds (src := src) h.1 rfl rfl rfl, h.2.1⟩)
        (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    have hB : ∀ src : SourceState C, (∀ p ∈ pre, src.revealed (.bottomChain e l p) ≠ none) →
        src.revealed (.bottomChain e l a) ≠ none → B src := fun src h1 h2 p hp =>
      (List.mem_append.mp hp).elim (h1 p) fun hp => by rw [List.mem_singleton.mp hp]; exact h2
    refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_sourceReveal P seeds Q s (readyEx := none)
      (cachedEx := none) (readyEx' := none) (cachedEx' := none) (.bottomChain e l a)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => h)
      (fun src _ => ∀ p ∈ pre, src.revealed (.bottomChain e l p) ≠ none)
      (fun src _ v h p hp => hupdate _ _ src v (h p hp))) fun value => ?_)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    split
    · exact Walk.conseq (c := 0 + 0) (Walk.bind (Walk.pure 0
        (Post := fun _ src st => BaseInv P seeds none none src st ∧ B src)
        fun src _ h => ⟨h.1, hB src h.2.1 h.2.2⟩) fun _ => hrest _ (fun _ h => by cases h) _)
        (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    · exact Walk.conseq (c := 0 + 0) (Walk.bind (walk_pad_source P seeds Q s _ B) fun _ =>
        hrest _ (fun _ h => by cases h) _) (fun src _ h => ⟨h.1, hB src h.2.1 h.2.2⟩)
        (fun _ _ _ h => h) le_rfl
  · intro src st hp r hr
    have hK := fun (K : HiddenKey) (hK : src.revealed K ≠ none) =>
      walk_sourcePlant P seeds Q s (.bottom e l a) K src st ⟨hp.1, (fun _ he => by cases he), hK⟩ r hr
    obtain ⟨hl, hg, hinv, -⟩ := hK _ (hp.2 a (by simpa using ha))
    exact ⟨hl, hg, hinv, fun p hp' => (hK _ (hp.2 p hp')).2.2.2.2⟩

/-- A corruption within the bound keeps `BaseInv`. -/
theorem baseInv_corrupt {src : SourceState C} {st : LState C} (h : BaseInv P seeds none none src st)
    (i : C.Party) (hcard : ¬C.t - 1 < (insert i src.signing.corrupt).card) :
    BaseInv P seeds none none
      { src with signing := { src.signing with corrupt := insert i src.signing.corrupt } } st :=
  ⟨h.reveal, h.bound, h.ready, h.commitTerms, h.treeCommit, h.revealedCached, h.releasedBound,
    Nat.le_of_not_lt hcard, h.reachable, h.dirtySecond⟩

/-- A read of the source state, with the read state in the precondition of the rest. -/
theorem charges_get_bind {α : Type} {Pre : SourceStateO1 C → Prop} {c : ℕ}
    {next : SourceStateO1 C → SourceMO1 C α}
    (h : ∀ src0, SourceCharges P seeds Q s (fun src => Pre src ∧ src = src0) c (next src0)) :
    SourceCharges P seeds Q s Pre c (get >>= next) := by
  intro src st hw hp r hr
  simp only [runSourceL_bind, runSourceL_get, pure_bind] at hr
  exact h src src st hw ⟨hp, rfl⟩ r hr

/-- The release of the chains of a key makes no charged call. -/
theorem charges_sourceReleaseKey (e : KeyIndex) :
    SourceCharges P seeds Q s (fun _ => True) 0 (sourceReleaseKey P seeds e) := by
  unfold sourceReleaseKey
  refine SourceCharges.mono (SourceCharges.bind (SourceCharges.mapM _ _ fun l _ => ?_) _
    fun _ => SourceCharges.pure ()) (fun _ h => h) (c := _ * 0 + 0) (by simp)
  unfold sourceReleaseCovered
  refine charges_get_bind P seeds Q s fun src0 => ?_
  split
  · exact SourceCharges.mono (charges_of_walk (walk_sourceReleaseBottomSuffix P seeds Q s e l _))
      (fun _ _ => trivial) le_rfl
  · exact SourceCharges.pure ()

end Hash

/-- `WalkInv` reads only the revealed secrets, the signing state and the trees of the source. -/
theorem walkInv_of_source {P : PublicParameter} {seeds : C.Term → HashOutput}
    {src src' : SourceStateO1 C} {st : LState C} (h : WalkInv P seeds src st)
    (hrev : src'.base.revealed = src.base.revealed) (hsig : src'.base.signing = src.base.signing)
    (htrees : src'.base.trees = src.base.trees) : WalkInv P seeds src' st :=
  (walkInv_iff P seeds src' st).2
    (BaseInv.of_source P seeds ((walkInv_iff P seeds src st).1 h) hrev hsig htrees)

/-- Round 1 of the base source keeps `BaseInv` and makes no charged call. -/
theorem walk_round1 (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) :
    Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none) 0 (fun _ => BaseInv x.1 x.2.1 none none)
      (sourceTsig prims x top (.round1 i J e message)) := by
  simp only [sourceTsig]
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · exact Walk.pure _ fun _ _ h => h.2
  · rename_i hg
    have hfree : src0.signing.bound e = none ∨ src0.signing.bound e = some message := by
      cases hb : src0.signing.bound e with
      | none => exact Or.inl rfl
      | some m =>
          simp only [breaksOneMessagePerKey, hb, Option.any_some, decide_eq_true_eq, not_or,
            not_not] at hg
          exact Or.inr (by rw [hg.2.2])
    have hpart : Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none) 0
        (fun _ => BaseInv x.1 x.2.1 none none)
        (some <$> sourcePart prims x i J (Point.randomizer bottomLayer e) message) := by
      unfold sourcePart
      exact walk_map x.1 x.2.1 Q s (walk_sourceEval x.1 x.2.1 Q s prims _ i J _ message) _
    let src1 : SourceState C := { src0 with signing :=
      { src0.signing with bound := Function.update src0.signing.bound e (some message) } }
    refine Walk.conseq (c := 0 + (0 + (0 + (0 + 0)))) (Walk.bind (Walk.modify
      (Post := fun _ src st => src = src1 ∧ BaseInv x.1 x.2.1 none none src0 st) _
      fun src st h => by obtain ⟨rfl, h⟩ := h; exact ⟨rfl, h⟩) fun _ =>
      Walk.bind (Walk.conseq (walk_query x.1 x.2.1 Q s (.bindKey e message) _ 0
        (fun _ _ h => by cases h) (fun _ _ _ hch => absurd hch
          (not_charged_of_ne x.1 x.2.1 _ (fun _ h => by cases h) _ _)))
        (fun _ _ h => h) (Post' := fun _ src st => BaseInv x.1 x.2.1 (some e) none src st ∧ True)
        ?_ le_rfl) fun _ =>
      Walk.bind (walk_snapshot x.1 x.2.1 Q s (readyEx := some e) (cachedEx := none)
        (fun _ _ => True) (fun _ _ _ _ h => h)) fun y =>
      Walk.bind Walk.get fun src2 => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    · rintro _ src' st' ⟨st, ⟨rfl, hinv⟩, xb, hxb, -, flag, rfl⟩
      exact ⟨baseInv_bind x.1 x.2.1 hinv e message hfree hxb flag, trivial⟩
    · split
      · exact Walk.conseq (c := 0 + 0) (Walk.bind (walk_sourceReleaseOpening x.1 x.2.1 Q s e)
          fun _ => hpart) (fun _ _ h => h.2.1) (fun _ _ _ h => h) le_rfl
      · rename_i hn
        refine Walk.conseq (c := 0 + 0) (Walk.bind (Walk.pure () fun _ _ h => h) fun _ => hpart)
          (fun src st h => ?_) (fun _ _ _ h => h) le_rfl
        obtain ⟨rfl, hinv, -, hy⟩ := h
        exact BaseInv.close_ready x.1 x.2.1 hinv fun hr => absurd (hy ▸ hr) hn

/-- A local call of the forger makes at most one charged call, and none at a uniform sample. -/
theorem charges_local (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (t : (LocalSpec C).Domain) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True)
      (if SigningOwnCounted (.inl t : (LocalSpec C + TsigSpec C).Domain) then 1 else 0)
      (sourceOraclesO1 prims x top (.inl t)) := by
  have hlocal : Walk x.1 x.2.1 Q s (BaseInv x.1 x.2.1 none none)
      (if SigningOwnCounted (.inl t : (LocalSpec C + TsigSpec C).Domain) then 1 else 0)
      (fun _ => BaseInv x.1 x.2.1 none none) (sourceLocal prims x t) := by
    cases t with
    | inl n =>
        exact Walk.conseq (walk_uniform x.1 x.2.1 Q s n) (fun _ _ h => h) (fun _ _ _ h => h)
          (Nat.zero_le _)
    | inr t =>
        cases t with
        | inl q =>
            exact Walk.conseq (walk_sourceHash x.1 x.2.1 Q s q 1 fun _ _ => le_rfl)
              (fun _ _ h => h) (fun _ _ _ h => h) (by simp [SigningOwnCounted])
        | inr inp =>
            exact Walk.conseq (c := 0 + 0) (Walk.bind (walk_sourceHash x.1 x.2.1 Q s _ 0
              fun _ h => by cases h) fun _ => Walk.pure _ fun _ _ h => h)
              (fun _ _ h => h) (fun _ _ _ h => h) (Nat.zero_le _)
  refine charges_of_walk ?_
  simp only [sourceOracles]
  exact Walk.conseq (c := 0 + (_ + (0 + 0))) (Walk.bind Walk.get fun _ =>
    Walk.bind (Walk.conseq hlocal (fun _ _ h => h.2) (fun _ _ _ h => h) le_rfl) fun _ =>
      Walk.bind (Walk.modify (Post := fun _ => BaseInv x.1 x.2.1 none none) _ fun src _ h =>
        BaseInv.of_source x.1 x.2.1 (src := src) h rfl rfl rfl) fun _ =>
      Walk.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (by simp)

/-- A corruption makes no charged call. -/
theorem charges_corrupt (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (i : C.Party) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True)
      (if SigningOwnCounted (.inr (.corrupt i) : (LocalSpec C + TsigSpec C).Domain) then 1 else 0)
      (sourceOraclesO1 prims x top (.inr (.corrupt i))) := by
  simp only [sourceOraclesO1, sourceTsigO1]
  refine SourceCharges.mono (SourceCharges.bind (c := 0) (charges_get_bind x.1 x.2.1 Q s
    fun src0 => ?_) _ fun value => SourceCharges.bind (SourceCharges.modify _
      fun _ _ h _ => walkInv_of_source h rfl rfl rfl) _ fun _ => SourceCharges.pure value)
    (fun _ h => h) (Nat.zero_le _)
  split
  · exact SourceCharges.pure _
  · rename_i hcard
    refine SourceCharges.mono (c := 0 + (_ * 0 + 0)) (SourceCharges.bind (SourceCharges.modify _
      fun src st h hp => ?_) _ fun _ => SourceCharges.bind (SourceCharges.mapM _ _ fun e _ =>
        charges_sourceReleaseKey x.1 x.2.1 Q s e) _ fun _ => SourceCharges.pure _)
      (fun _ h => h) (by simp)
    obtain ⟨-, rfl⟩ := hp
    exact (walkInv_iff x.1 x.2.1 _ st).2
      (baseInv_corrupt x.1 x.2.1 ((walkInv_iff x.1 x.2.1 _ st).1 h) i hcard)

/-- A round-1 request makes no charged call. -/
theorem charges_round1 (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True)
      (if SigningOwnCounted (.inr (.round1 i J e message) : (LocalSpec C + TsigSpec C).Domain)
        then 1 else 0)
      (sourceOraclesO1 prims x top (.inr (.round1 i J e message))) := by
  simp only [sourceOraclesO1, sourceTsigO1]
  exact SourceCharges.mono (SourceCharges.bind (charges_of_walk
    (walk_round1 prims x Q s top i J e message)) _ fun value =>
      SourceCharges.bind (SourceCharges.modify _ fun _ _ h _ => walkInv_of_source h rfl rfl rfl) _
        fun _ => SourceCharges.pure value) (fun _ h => h) (Nat.zero_le _)

/-- One call of the verification makes at most one charged call. -/
theorem charges_verify (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest) (st : SourceState C)
    (input : HashInput) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True) 1
      (liftBase (do
        let value ← sourceHash x.1 x.2.1 (.hash input)
        modify fun (s : SourceState C) => { s with candidates :=
          s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
        pure value : SourceM C HashOutput)) :=
  charges_of_walk (Walk.conseq (c := 1 + (0 + 0)) (Walk.bind
    (walk_sourceHash x.1 x.2.1 Q s _ 1 fun _ _ => le_rfl) fun _ =>
      Walk.bind (Walk.modify (Post := fun _ => BaseInv x.1 x.2.1 none none) _ fun src _ h =>
        BaseInv.of_source x.1 x.2.1 (src := src) h rfl rfl rfl) fun _ =>
      Walk.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl)

end ThresholdLeanXmssSecurity.SigningOwnWalkHandlers

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_hashCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_hashCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceReleaseOpening_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceReleaseOpening_revealed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.hash_ready_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.hash_ready_plain

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.hash_not_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.hash_not_ready

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceHash

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_map

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceEval

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.baseInv_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.baseInv_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_pad_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_pad_source

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceReleaseBottomSuffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_sourceReleaseBottomSuffix

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.baseInv_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.baseInv_corrupt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_get_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_get_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_sourceReleaseKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_sourceReleaseKey

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walkInv_of_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walkInv_of_source

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_round1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.walk_round1

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_local

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_corrupt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_round1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_round1

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkHandlers.charges_verify
