import ThresholdLeanXmssSecurity.Proof.TreeHops
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The stream-key bound after the derivation boundary

`TreeStreamKeyAfterDerivation` of `TreeHops.lean`, by the plan of its module doc, in three stages.

1. `afterDerivationAllowed`. After the boundary every free call is a sampling, a hash other
   than `.streamKey`, or a stream under the key that a row gives its name (`Allowed`). This is a walk
   of `ceremonyAfterSetup` (`POk.ceremonyAfterSetup`) carried through the execution (`executeRounds_ok`).
2. `TreeKeysApartBound`. At the boundary the key of a hidden name in a row differs from the
   key of every other name (`KeysApart`), up to `streamKeyError` and one prequery term.
3. `TreeKeyHitBound`. With the keys apart, the cache ends without the stream key of a hidden
   key of a row (`KeyHit`), up to the rest of `keySplit`.

With 1 and the keys apart, the ideal joint world keeps `JointInv` (`jointKeyWorld_run_inv`), so a raised
flag comes with a hit (`boundaryRun_bad`). `treeStreamKeyAfterDerivation_of_stages` sums the stages.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RowKeys

variable {C : Committee}

/-- Key `k` is the key of name `n` in the PRSS keys `keys` of operator `i`: a held term or a pair
with another operator. -/
def ValidKey (i : C.Party) (keys : PrssKeys C) : KeyName C → HashOutput → Prop
  | .term T, k => i ∈ C.holders T ∧ k = keys.term T
  | .pair p, k => ∃ j, ∃ h : j ≠ i, p = C.pairOf i j (Ne.symm h) ∧ k = keys.pair j
  | .parameter, _ => False

/-- Key `k` is the key of name `n` in some row of the reveal round. -/
def RowKey (rows : RevealRows C) (n : KeyName C) (k : HashOutput) : Prop :=
  ∃ i keys shared, rows i = some (keys, shared) ∧ ValidKey i keys n k

/-- A free call that the rows allow: a sampling, a hash other than a stream key, or a stream under
the key of its name in a row. -/
def Allowed (rows : RevealRows C) : (LocalSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.inl q) => ∀ k, q ≠ .streamKey k
  | .inr (.inr x) => RowKey rows x.1 x.2.1

/-- A free call that the rows do not allow. -/
def Unallowed (rows : RevealRows C) : (WorldSpec C).Domain → Prop
  | .inl _ => False
  | .inr t => ¬ Allowed rows t

/-- The key of a hidden name in a row differs from the key of every other name in every row. -/
def KeysApart (D : C.Coalition) (rows : RevealRows C) : Prop :=
  ∀ n k n' k', RowKey rows n k → Hidden D n → RowKey rows n' k' → n ≠ n' → k ≠ k'

/-- The cache holds the stream key of a hidden key of a row. -/
def KeyHit (D : C.Coalition) (rows : RevealRows C) (h : HashCache C) : Prop :=
  ∃ n k, RowKey rows n k ∧ Hidden D n ∧ h (.streamKey k) ≠ none

/-- The invariant of the ideal joint world after the boundary: each used key is the row key of its
hidden name and has a private answer, and a raised flag comes with a hit. -/
def JointInv (D : C.Coalition) (rows : RevealRows C) (s : KeyJointState C) : Prop :=
  (∀ k n, s.used k = some n → Hidden D n ∧ RowKey rows n k ∧ s.keys (n, k) ≠ none) ∧
    (s.bad = true → KeyHit D rows s.hash)

theorem keyHit_mono {D : C.Coalition} {rows : RevealRows C} {h h' : HashCache C} (hle : h ≤ h') :
    KeyHit D rows h → KeyHit D rows h' := by
  rintro ⟨n, k, hk, hn, hc⟩
  refine ⟨n, k, hk, hn, ?_⟩
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hc
  rw [hle hu]
  simp

/-- A hash query of a stream key caches it. -/
theorem hashAnswer_streamKey_cached (prims : Primitives) (k : HashOutput) (s : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims (.streamKey k)).run s), z.2 (.streamKey k) ≠ none := by
  intro z hz
  rw [hashAnswer_cached prims (by rintro ⟨_, h, _⟩; cases h) s z hz]
  simp

theorem onJointHash_support {α : Type} (m : StateT (HashCache C) ProbComp α) (s : KeyJointState C) :
    ∀ r ∈ support ((onJointHash m).run s), ∃ z ∈ support (m.run s.hash), r = (z.1, { s with hash := z.2 }) := by
  intro r hr
  simp only [onJointHash, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  exact ⟨z, hz, rfl⟩

/-- A step that only grows the public cache keeps the invariant, when its risk comes with a hit. -/
theorem jointInv_of_hash {D : C.Coalition} {rows : RevealRows C} {s : KeyJointState C}
    (hs : JointInv D rows s) (h' : HashCache C) (hle : s.hash ≤ h') (b : Bool)
    (hb : b = true → KeyHit D rows h') :
    JointInv D rows { s with hash := h', bad := s.bad || b } ∧ s.hash ≤ h' := by
  refine ⟨⟨hs.1, ?_⟩, hle⟩
  intro hbad
  simp only [Bool.or_eq_true] at hbad
  rcases hbad with h | h
  · exact keyHit_mono hle (hs.2 h)
  · exact hb h

theorem keyHit_of_used {D : C.Coalition} {rows : RevealRows C} {s : KeyJointState C}
    (hs : JointInv D rows s) {k : HashOutput} (hk : (s.used k).isSome = true) {h' : HashCache C}
    (hc : h' (.streamKey k) ≠ none) : KeyHit D rows h' := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨hh, hrow, -⟩ := hs.1 k n hn
  exact ⟨n, k, hrow, hh, hc⟩

/-- A counted hash keeps the invariant. -/
theorem jointInv_hash (prims : Primitives) {D : C.Coalition} {rows : RevealRows C} {s : KeyJointState C}
    (hs : JointInv D rows s) (q : Query C) (z : HashOutput × HashCache C)
    (hz : z ∈ support ((hashAnswer prims q).run s.hash)) (b : Bool)
    (hb : b = true → ∃ k, q = .streamKey k ∧ (s.used k).isSome = true) :
    JointInv D rows { s with hash := z.2, bad := s.bad || b } ∧ s.hash ≤ z.2 := by
  refine jointInv_of_hash hs z.2 (grows_hashAnswer prims q s.hash z hz) b fun h => ?_
  obtain ⟨k, rfl, hk⟩ := hb h
  exact keyHit_of_used hs hk (hashAnswer_streamKey_cached prims k s.hash z hz)

theorem prgAnswer_support (prims : Primitives) (x : PrgInput C) (h : HashCache C) :
    ∀ z ∈ support ((prgAnswer prims x).run h),
      ∃ w ∈ support ((hashAnswer prims (.streamKey x.2.1)).run h), z.2 = w.2 := by
  intro z hz
  simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

/-- A counted stream keeps the invariant. -/
theorem jointInv_stream (prims : Primitives) {D : C.Coalition} {rows : RevealRows C} {s : KeyJointState C}
    (hs : JointInv D rows s) (x : PrgInput C) (z : Bit × HashCache C)
    (hz : z ∈ support ((prgAnswer prims x).run s.hash)) (b : Bool)
    (hb : b = true → (s.used x.2.1).isSome = true) :
    JointInv D rows { s with hash := z.2, bad := s.bad || b } ∧ s.hash ≤ z.2 := by
  obtain ⟨w, hw, he⟩ := prgAnswer_support prims x s.hash z hz
  rw [he]
  refine jointInv_of_hash hs w.2 (grows_hashAnswer prims _ s.hash w hw) b fun h => ?_
  exact keyHit_of_used hs (hb h) (hashAnswer_streamKey_cached prims _ s.hash w hw)

/-- A programming of a stream key leaves it cached. -/
theorem programAnswer_streamKey_cached (k v : HashOutput) (h : HashCache C) :
    ∀ z ∈ support ((programAnswer (.streamKey k, v)).run h), z.2 (.streamKey k) ≠ none := by
  intro z hz
  by_cases hc : (h (.streamKey k)).isSome
  · have he : (programAnswer (C := C) (.streamKey k, v)).run h = pure (false, h) := by
      simp [programAnswer, hc]
    rw [he, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simpa [Option.isSome_iff_ne_none] using hc
  · have he : (programAnswer (C := C) (.streamKey k, v)).run h =
        pure (true, h.cacheQuery (.streamKey k) v) := by
      simp [programAnswer, hc]
    rw [he, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp

/-- One step of the ideal joint world on an allowed call keeps the invariant and grows the cache. -/
theorem jointKeyWorld_inv (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    (hg : KeysApart D rows) (t : (WorldSpec C).Domain) (ht : ¬ Unallowed rows t)
    (s : KeyJointState C) (hs : JointInv D rows s) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), JointInv D rows r.2 ∧ s.hash ≤ r.2.hash := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inl u))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact jointInv_of_hash hs z.2 (grows_localAnswer prims (.inl u) s.hash z hz) _ (by simp [keyJointRisk])
  · have hp' : p ∈ support ((onJointHash (hashAnswer prims q)).run s) := by
      rw [← jointHash_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine jointInv_hash prims hs q z hz _ fun hr => ?_
    cases q <;> simp [keyJointRisk] at hr ⊢
    exact hr
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inr (.inr x)))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact jointInv_stream prims hs x z hz _ (by simp [keyJointRisk])
  · have hp' : p ∈ support ((onJointHash (programAnswer (q, v))).run s) := by
      rw [← jointProgram_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine jointInv_of_hash hs z.2 (grows_programAnswer (q, v) s.hash z hz) _ fun hr => ?_
    cases q <;> simp [keyJointRisk] at hr
    exact keyHit_of_used hs hr (programAnswer_streamKey_cached _ v s.hash z hz)
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inl u))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact jointInv_of_hash hs z.2 (grows_localAnswer prims (.inl u) s.hash z hz) _ (by simp [keyJointRisk])
  · have hp' : p ∈ support ((onJointHash (hashAnswer prims q)).run s) := by
      rw [← jointHash_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine jointInv_hash prims hs q z hz _ fun hr => ?_
    simp only [Unallowed, Allowed, not_not] at ht
    cases q <;> simp [keyJointRisk] at hr
    exact absurd rfl (ht _)
  · simp only [Unallowed, Allowed, not_not] at ht
    by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, if_pos hh]
      rw [hc] at hp
      simp only [StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      rcases hk : s.keys (x.1, x.2.1) with _ | v
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = (do
            let v ← $ᵗ HashOutput
            pure (v, (⟨s.hash, s.keys.cacheQuery (x.1, x.2.1) v,
              (if (s.used x.2.1).isSome then s.used else Function.update s.used x.2.1 (some x.1)),
              s.bad⟩ : KeyJointState C))) := by
          simp [jointHidden, hk]
        rw [hrun] at hw
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
        obtain ⟨v, -, rfl⟩ := hw
        have hkeys : ∀ n k, s.keys (n, k) ≠ none →
            (s.keys.cacheQuery (x.1, x.2.1) v) (n, k) ≠ none := by
          intro n k h
          by_cases he : (n, k) = (x.1, x.2.1)
          · rw [he]; simp
          · rw [QueryCache.cacheQuery_of_ne _ _ he]; exact h
        refine ⟨⟨?_, ?_⟩, le_rfl⟩
        · intro k n hn
          dsimp only at hn ⊢
          by_cases hu : (s.used x.2.1).isSome
          · rw [if_pos hu] at hn
            obtain ⟨h1, h2, h3⟩ := hs.1 k n hn
            exact ⟨h1, h2, hkeys n k h3⟩
          · rw [if_neg hu] at hn
            by_cases hk' : k = x.2.1
            · subst hk'
              simp only [Function.update_self, Option.some.injEq] at hn
              subst hn
              exact ⟨hh, ht, by simp⟩
            · rw [Function.update_of_ne hk'] at hn
              obtain ⟨h1, h2, h3⟩ := hs.1 k n hn
              exact ⟨h1, h2, hkeys n k h3⟩
        · intro hb
          dsimp only at hb ⊢
          simp only [keyJointRisk, if_pos hh, hk, Option.isSome_none, Bool.not_false,
            Bool.true_and, Bool.or_eq_true] at hb
          rcases hb with hb | hb | hb
          · exact hs.2 hb
          · exact ⟨x.1, x.2.1, ht, hh, by simpa [Option.isSome_iff_ne_none] using hb⟩
          · obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hb
            obtain ⟨h1, h2, h3⟩ := hs.1 _ n' hn'
            by_cases hne : x.1 = n'
            · subst hne
              exact absurd hk h3
            · exact absurd rfl (hg _ _ _ _ ht hh h2 hne)
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = pure (v, s) := by
          simp [jointHidden, hk]
        rw [hrun, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact jointInv_of_hash hs s.hash le_rfl _ (by simp [keyJointRisk, hh, hk])
    · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inr (.inr x)))).run s) := by
        have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) =
            jointLocal prims false (.inr (.inr x)) := by
          simp only [jointKeyWorldCore, if_neg hh]
        rw [hc] at hp
        rw [← jointLocal_false]
        exact hp
      obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
      exact jointInv_stream prims hs x z hz _ (by simp [keyJointRisk, hh])

/-- A computation with only allowed free calls keeps the invariant in the ideal joint world. -/
theorem jointKeyWorld_run_inv (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    (hg : KeysApart D rows) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hoa : IsQueryBoundP oa (Unallowed rows) 0) (s : KeyJointState C) (hs : JointInv D rows s) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run s),
      JointInv D rows r.2 ∧ s.hash ≤ r.2.hash := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hs, le_rfl⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ Unallowed rows t := by
      rcases hoa.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    intro r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    have h₁ := jointKeyWorld_inv prims D rows hg t ht s hs p hp
    have hk : IsQueryBoundP (k p.1) (Unallowed rows) 0 := by
      have := hoa.2 p.1
      rwa [if_neg ht] at this
    have h₂ := ih p.1 hk p.2 h₁.1 r hr
    exact ⟨h₂.1, h₁.2.trans h₂.2⟩

end RowKeys

/-! ## Calls without a bad index -/

section NoBad

theorem qb0_simulateQ {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {p : ι → Prop}
    {q : ι' → Prop} [DecidablePred p] [DecidablePred q] (impl : QueryImpl spec (OracleComp spec'))
    (hstep : ∀ t, ¬ p t → IsQueryBoundP (impl t) q 0) {α : Type} (oa : OracleComp spec α)
    (h : IsQueryBoundP oa p 0) : IsQueryBoundP (simulateQ impl oa) q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ p t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    rw [simulateQ_query_bind]
    refine qb0_bind (hstep t ht) fun u => ih u ?_
    have := h.2 u
    rwa [if_neg ht] at this

theorem qb0_liftComp {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} [MonadLiftT (OracleQuery spec) (OracleQuery spec')]
    {p : ι → Prop} {q : ι' → Prop} [DecidablePred p] [DecidablePred q] {α : Type}
    (oa : OracleComp spec α) (h : IsQueryBoundP oa p 0)
    (hstep : ∀ t, ¬ p t → IsQueryBoundP (liftM (spec.query t) : OracleComp spec' _) q 0) :
    IsQueryBoundP (liftComp oa spec') q 0 :=
  qb0_simulateQ _ hstep oa h

theorem support_simulateQ_subset {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec (OracleComp spec')) {α : Type} (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro x hx
    rw [simulateQ_query_bind, support_bind, Set.mem_iUnion₂] at hx
    obtain ⟨u, -, hx⟩ := hx
    rw [support_bind, Set.mem_iUnion₂]
    exact ⟨u, by simp, ih u hx⟩

theorem qb0_false {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α) :
    IsQueryBoundP oa (fun _ => False) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simpa using ih u⟩

end NoBad

/-! ## The discipline of the honest program after setup -/

section Discipline

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β σ : Type}

/-- A call of `H` and `PRG` that operator `ctx` must not make: a hash of a stream key, or a stream
under another key than the key of its name. -/
def RoBad (ctx : Context C) : (RoSpec C).Domain → Prop
  | .inl q => ∃ k, q = .streamKey k
  | .inr x => ¬ ValidKey ctx.self ctx.prss x.1 x.2.1

/-- The bad calls of a program of operator `ctx`. -/
def PartyBad (ctx : Context C) : (PartySpec C E G).Domain → Prop
  | .inl (.inl (.inr t)) => RoBad ctx t
  | _ => False

def ROk (ctx : Context C) (oa : OracleComp (RoSpec C) α) : Prop := IsQueryBoundP oa (RoBad ctx) 0

def POk (ctx : Context C) (p : PartyM C E G α) : Prop :=
  IsQueryBoundP p.run (PartyBad (E := E) (G := G) ctx) 0

def SOk (ctx : Context C) (p : StateT σ (PartyM C E G) α) : Prop := ∀ s, POk ctx (p.run s)

variable {ctx : Context C}

theorem ROk.bind {oa : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    (h : ROk ctx oa) (hf : ∀ a, ROk ctx (f a)) : ROk ctx (oa >>= f) := qb0_bind h hf

theorem ROk.pure (a : α) : ROk ctx (pure a : OracleComp (RoSpec C) α) := by simp [ROk]

theorem ROk.map {oa : OracleComp (RoSpec C) α} (f : α → β) (h : ROk ctx oa) : ROk ctx (f <$> oa) := by
  simpa [ROk] using h

theorem ROk.mapM (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, ROk ctx (f a)) (xs : List α) :
    ROk ctx (xs.mapM f) := qb0_mapM f hf xs

theorem ROk.hashQuery (q : Query C) (hq : ∀ k, q ≠ .streamKey k) : ROk ctx (hashQuery q) := by
  unfold ROk ThresholdLeanXmss.hashQuery
  erw [isQueryBoundP_query_iff]
  rintro ⟨k, hk⟩
  exact absurd hk (hq k)

theorem ROk.stream (x : PrgInput C) (hx : ValidKey ctx.self ctx.prss x.1 x.2.1) :
    ROk ctx (query (spec := RoSpec C) (.inr x)) := by
  unfold ROk
  erw [isQueryBoundP_query_iff]
  intro h
  exact absurd hx h

theorem ROk.prgBits (name : KeyName C) (key : HashOutput) (hv : ValidKey ctx.self ctx.prss name key)
    (ρ idx count : ℕ) : ROk ctx (prgBits name key ρ idx count) := by
  unfold ThresholdLeanXmss.prgBits
  exact ROk.bind (ROk.mapM _ (fun position => ROk.stream (name, key, ρ, idx, position) hv) _)
    fun _ => ROk.pure _

theorem ROk.tweakable (oa : OracleComp HashSpec α) : ROk ctx (tweakable oa) := by
  unfold ThresholdLeanXmss.tweakable ROk
  refine qb0_simulateQ (p := fun _ => False) _ (fun t _ => ?_) oa (by
    induction oa using OracleComp.inductionOn with
    | pure a => simp
    | query_bind t k ih =>
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl not_false, fun u => by simpa using ih u⟩)
  exact ROk.hashQuery _ (fun k h => by cases h)

/-- The bad local calls of operator `ctx`. -/
def LocalBad (ctx : Context C) : (LocalSpec C).Domain → Prop
  | .inr t => RoBad ctx t
  | _ => False

theorem qb0_liftComp_local {oa : OracleComp (RoSpec C) α} (h : ROk ctx oa) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (LocalBad ctx) 0 := by
  refine qb0_liftComp oa h fun t ht => ?_
  erw [isQueryBoundP_query_iff]
  exact fun h' => (ht h').elim

theorem qb0_liftComp_party {oa : OracleComp (LocalSpec C) α} (h : IsQueryBoundP oa (LocalBad ctx) 0) :
    IsQueryBoundP (liftComp oa (PartySpec C E G)) (PartyBad (E := E) (G := G) ctx) 0 := by
  refine qb0_liftComp oa h fun t ht => ?_
  erw [isQueryBoundP_query_iff]
  intro h'
  rcases t with u | t
  · exact h'.elim
  · rcases t with q | x
    · exact (ht h').elim
    · exact (ht h').elim

theorem POk.pure (a : α) : POk (E := E) (G := G) ctx (pure a) := by simp [POk]

theorem POk.failure : POk (E := E) (G := G) (α := α) ctx failure := by
  simp [POk, OptionT.run_failure]

theorem POk.bind {p : PartyM C E G α} {f : α → PartyM C E G β} (h : POk ctx p)
    (hf : ∀ a, POk ctx (f a)) : POk ctx (p >>= f) := by
  unfold POk
  rw [OptionT.run_bind]
  refine qb0_bind h fun o => ?_
  cases o with
  | none => simp
  | some a => exact hf a

theorem POk.lift {oa : OracleComp (PartySpec C E G) α}
    (h : IsQueryBoundP oa (PartyBad (E := E) (G := G) ctx) 0) : POk ctx (OptionT.lift oa) := by
  unfold POk
  rw [OptionT.run_lift]
  exact qb0_bind h fun _ => by simp

theorem POk.oracleStep {oa : OracleComp (RoSpec C) α} (h : ROk ctx oa) :
    POk (E := E) (G := G) ctx (oracleStep oa) :=
  POk.lift (qb0_liftComp_party (qb0_liftComp_local h))

theorem POk.exchange (outbox : Mail C E) : POk (G := G) ctx (exchange outbox) := by
  unfold ThresholdLeanXmss.exchange
  refine POk.bind (POk.lift ?_) fun inbox => ?_
  · erw [isQueryBoundP_query_iff]
    exact fun h => h.elim
  · split_ifs
    · exact POk.failure
    · exact POk.pure _

theorem POk.require (c : Prop) : POk (E := E) (G := G) ctx (require c) := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact POk.pure _
  · exact POk.failure

theorem POk.map {p : PartyM C E G α} (f : α → β) (h : POk ctx p) : POk ctx (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact POk.bind h fun _ => POk.pure _

theorem POk.mapM (f : α → PartyM C E G β) (hf : ∀ a, POk ctx (f a)) :
    ∀ xs : List α, POk ctx (xs.mapM f)
  | [] => POk.pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact POk.bind (hf x) fun _ => POk.bind (POk.mapM f hf xs) fun _ => POk.pure _

theorem SOk.bind {p : StateT σ (PartyM C E G) α} {f : α → StateT σ (PartyM C E G) β}
    (h : SOk ctx p) (hf : ∀ a, SOk ctx (f a)) : SOk ctx (p >>= f) := by
  intro s
  rw [StateT.run_bind]
  exact POk.bind (h s) fun x => hf x.1 x.2

theorem SOk.pure (a : α) : SOk (σ := σ) (E := E) (G := G) ctx (pure a) := fun s => by
  rw [StateT.run_pure]; exact POk.pure _

theorem SOk.lift {p : PartyM C E G α} (h : POk ctx p) : SOk (σ := σ) ctx (StateT.lift p) := fun s => by
  rw [StateT.run_lift]
  exact POk.bind h fun _ => POk.pure _

theorem SOk.get : SOk (σ := σ) (E := E) (G := G) ctx get := fun s => by
  rw [StateT.run_get]; exact POk.pure _

theorem SOk.set (s' : σ) : SOk (E := E) (G := G) ctx (set s' : StateT σ (PartyM C E G) PUnit) := fun s => by
  rw [StateT.run_set]; exact POk.pure _

theorem SOk.modify (f : σ → σ) : SOk (E := E) (G := G) ctx (modify f : StateT σ (PartyM C E G) PUnit) := fun s => by
  rw [StateT.run_modify]; exact POk.pure _

theorem SOk.modifyGet (f : σ → α × σ) : SOk (E := E) (G := G) ctx (modifyGet f : StateT σ (PartyM C E G) α) := fun s => by
  rw [StateT.run_modifyGet]; exact POk.pure _

theorem SOk.map {p : StateT σ (PartyM C E G) α} (f : α → β) (h : SOk ctx p) : SOk ctx (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact SOk.bind h fun _ => SOk.pure _

theorem SOk.failure : SOk (σ := σ) (E := E) (G := G) (α := α) ctx (StateT.lift failure) :=
  SOk.lift POk.failure

theorem SOk.foldlM {γ : Type} (f : β → γ → StateT σ (PartyM C E G) β) (hf : ∀ b c, SOk ctx (f b c)) :
    ∀ (xs : List γ) (init : β), SOk ctx (xs.foldlM f init)
  | [], init => SOk.pure _
  | x :: xs, init => by
    rw [List.foldlM_cons]
    exact SOk.bind (hf init x) fun b => SOk.foldlM f hf xs b

theorem SOk.mapM (f : α → StateT σ (PartyM C E G) β) (hf : ∀ a, SOk ctx (f a)) :
    ∀ xs : List α, SOk ctx (xs.mapM f)
  | [] => SOk.pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact SOk.bind (hf x) fun _ => SOk.bind (SOk.mapM f hf xs) fun _ => SOk.pure _

/-- A codec that draws only under the key of its name. -/
def CodecOk {R : Type} (ctx : Context C) (codec : Codec C E R) : Prop :=
  ∀ name key ρ idx count, ValidKey ctx.self ctx.prss name key → ROk ctx (codec.draw name key ρ idx count)

theorem codecOk_bit : CodecOk (E := E) ctx bitCodec :=
  fun name key ρ idx count hv => ROk.prgBits name key hv ρ idx count

theorem codecOk_element [Field E] [Algebra Bit E] (K : Constants C E) : CodecOk ctx (elementCodec K) :=
  fun name key ρ idx count hv => ROk.bind (ROk.prgBits name key hv ρ idx _) fun _ => ROk.pure _

theorem SOk.prssRandomness {R : Type} [Zero R] (codec : Codec C E R) (hc : CodecOk ctx codec)
    (idx count : ℕ) : SOk (G := G) ctx (prssRandomness ctx codec idx count) := by
  unfold ThresholdLeanXmss.prssRandomness freshLabel
  refine SOk.bind (SOk.modifyGet _) fun ρ => ?_
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.mapM _ (fun T => ?_) _))) fun r => ?_
  · split_ifs with hT
    · exact hc _ _ _ _ _ ⟨hT, rfl⟩
    · exact ROk.pure _
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.mapM _ (fun j => ?_) _))) fun Z => SOk.pure _
  split_ifs with hj
  · exact ROk.pure _
  · exact hc _ _ _ _ _ ⟨j, hj, rfl, rfl⟩

section Gadgets

variable [Field E] [Algebra Bit E] (K : Constants C E)

theorem SOk.reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R)
    (v : ℕ → R) (count : ℕ) : SOk (G := G) ctx (reshare K ctx codec randomness v count) := by
  unfold ThresholdLeanXmss.reshare record
  exact SOk.bind (SOk.lift (POk.exchange _)) fun _ => SOk.bind (SOk.modify _) fun _ => SOk.pure _

theorem SOk.reshareCollector (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    SOk (G := G) ctx (reshareCollector K ctx randomness v count) := by
  unfold ThresholdLeanXmss.reshareCollector record
  exact SOk.bind (SOk.lift (POk.exchange _)) fun _ => SOk.bind (SOk.lift (POk.exchange _)) fun _ =>
    SOk.bind (SOk.modify _) fun _ => SOk.pure _

theorem SOk.reshareWith (mode : ReshareMode) (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    SOk (G := G) ctx (reshareWith K ctx mode randomness v count) := by
  cases mode
  · exact SOk.reshare K _ _ _ _
  · exact SOk.reshareCollector K _ _ _

theorem POk.openRep (v : Shares C Bit) (count : ℕ) : POk (G := G) ctx (openRep K ctx v count) := by
  unfold ThresholdLeanXmss.openRep
  refine POk.bind (POk.oracleStep (ROk.mapM _ (fun T => ROk.hashQuery _ fun k h => by cases h) _)) fun _ => ?_
  refine POk.bind (POk.exchange _) fun _ => ?_
  refine POk.bind (POk.oracleStep (ROk.mapM _ (fun T => ROk.hashQuery _ fun k h => by cases h) _)) fun _ => ?_
  exact POk.bind (POk.require _) fun _ => POk.pure _

theorem POk.openSh (v : ℕ → E) (count : ℕ) : POk (G := G) ctx (openSh K ctx v count) := by
  unfold ThresholdLeanXmss.openSh
  exact POk.bind (POk.exchange _) fun _ => POk.bind (POk.require _) fun _ => POk.pure _

theorem SOk.coinWith (randomness : PrssOutput C E) (count : ℕ) :
    SOk (G := G) ctx (coinWith K ctx randomness count) := by
  unfold ThresholdLeanXmss.coinWith
  exact SOk.bind (SOk.lift (POk.openSh K _ _)) fun _ => SOk.pure _

theorem SOk.compareDigests (salts : Shares C Bit) :
    SOk (E := E) (G := G) ctx (compareDigests ctx salts) := by
  unfold ThresholdLeanXmss.compareDigests
  refine SOk.bind SOk.get fun st => ?_
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.mapM _ (fun T => ?_) _))) fun _ => ?_
  · split_ifs
    · exact ROk.bind (ROk.hashQuery _ fun k h => by cases h) fun _ => ROk.hashQuery _ fun k h => by cases h
    · exact ROk.pure _
  exact SOk.bind (SOk.lift (POk.exchange _)) fun _ => SOk.lift (POk.require _)

/-- Check gadgets whose calls are all allowed. -/
def CheckOk (ctx : Context C) (gadgets : CheckGadgets C E G) : Prop :=
  (∀ n, SOk ctx (gadgets.coin n)) ∧ (∀ xs, SOk ctx (gadgets.extendMult xs)) ∧
    (∀ n, SOk ctx (gadgets.randElements n)) ∧ (∀ n, SOk ctx (gadgets.randBits n))

theorem SOk.coinKey {gadgets : CheckGadgets C E G} (hg : CheckOk ctx gadgets) :
    SOk ctx (coinKey K gadgets) := by
  unfold ThresholdLeanXmss.coinKey
  exact SOk.bind SOk.get fun _ => SOk.bind (hg.1 1) fun _ =>
    SOk.lift (POk.oracleStep (ROk.hashQuery _ fun k h => by cases h))

theorem SOk.expand (key : HashOutput) (count : ℕ) :
    SOk (G := G) ctx (ThresholdLeanXmss.expand K key count) := by
  unfold ThresholdLeanXmss.expand
  exact SOk.lift (POk.oracleStep (ROk.mapM _ (fun k => ROk.map _ (ROk.hashQuery _ fun k h => by cases h)) _))

theorem ROk.findChallenge (key : HashOutput) :
    ∀ tries index, ROk ctx (findChallenge K key tries index)
  | 0, _ => ROk.pure _
  | tries + 1, index => by
    unfold ThresholdLeanXmss.findChallenge
    refine ROk.bind (ROk.hashQuery _ fun k h => by cases h) fun h => ?_
    dsimp only
    rcases Classical.propDecidable (elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1) with hr | hr
    · exact ROk.findChallenge key tries (index + 1)
    · exact ROk.pure _

theorem SOk.challenge {gadgets : CheckGadgets C E G} (hg : CheckOk ctx gadgets) :
    SOk ctx (challenge K gadgets) := by
  unfold ThresholdLeanXmss.challenge
  refine SOk.bind (SOk.coinKey K hg) fun key => ?_
  refine SOk.bind (SOk.lift (POk.oracleStep (ROk.findChallenge K key _ _))) fun r => ?_
  split
  · exact SOk.pure _
  · exact SOk.failure

theorem SOk.check {gadgets : CheckGadgets C E G} (hg : CheckOk ctx gadgets) (tuples : List (Tuple C)) :
    SOk ctx (check K ctx gadgets tuples) := by
  unfold ThresholdLeanXmss.check
  dsimp only
  split_ifs
  · exact SOk.pure _
  refine SOk.bind (SOk.pure _) fun _ => ?_
  refine SOk.bind (SOk.coinKey K hg) fun key => ?_
  refine SOk.bind (SOk.expand K _ _) fun τ => ?_
  refine SOk.bind (SOk.lift (POk.require _)) fun _ => ?_
  refine SOk.bind (SOk.foldlM _ (fun x j => ?_) _ _) fun d₁ => ?_
  · exact SOk.bind (hg.2.1 _) fun _ => SOk.bind (SOk.challenge K hg) fun _ => SOk.pure _
  refine SOk.bind (SOk.foldlM _ (fun x j => ?_) _ _) fun d₂ => ?_
  · exact SOk.bind (hg.2.1 _) fun _ => SOk.bind (SOk.challenge K hg) fun _ => SOk.pure _
  refine SOk.bind (hg.2.2.1 _) fun w => ?_
  refine SOk.bind (hg.2.1 _) fun q => ?_
  refine SOk.bind (hg.2.2.2 _) fun salts => ?_
  refine SOk.bind (SOk.compareDigests _) fun _ => ?_
  refine SOk.bind (SOk.challenge K hg) fun r => ?_
  exact SOk.bind (SOk.lift (POk.openSh K _ _)) fun _ => SOk.lift (POk.require _)

theorem checkOk_real : CheckOk (G := G) ctx (realCheckGadgets K ctx) := by
  refine ⟨fun n => ?_, fun xs => ?_, fun n => ?_, fun n => ?_⟩
  · exact SOk.bind (SOk.prssRandomness _ (codecOk_element K) _ _) fun _ => SOk.coinWith K _ _
  · exact SOk.bind (SOk.prssRandomness _ (codecOk_element K) _ _) fun _ => SOk.reshare K _ _ _ _
  · exact SOk.prssRandomness _ (codecOk_element K) _ _
  · exact SOk.prssRandomness _ codecOk_bit _ _

/-- Run gadgets whose calls are all allowed. -/
def RunOk (ctx : Context C) (gadgets : RunGadgets C E G) : Prop :=
  (∀ x y n, SOk ctx (gadgets.mult x y n)) ∧ (∀ v n, SOk ctx (gadgets.rerand v n)) ∧
    (∀ xs, SOk ctx (gadgets.verify xs)) ∧ (∀ v n, SOk ctx (gadgets.output v n))

theorem runOk_real (mode : ReshareMode) : RunOk (G := G) ctx (realRunGadgets K ctx mode) := by
  refine ⟨fun x y n => ?_, fun v n => ?_, fun xs => ?_, fun v n => ?_⟩
  · exact SOk.bind (SOk.prssRandomness _ codecOk_bit _ _) fun _ => SOk.reshareWith K _ _ _ _
  · exact SOk.bind (SOk.prssRandomness _ codecOk_bit _ _) fun _ => SOk.reshare K _ _ _ _
  · exact SOk.check K (checkOk_real K) xs
  · exact SOk.lift (POk.openRep K _ _)

theorem SOk.runJobs {gadgets : RunGadgets C E G} (hg : RunOk ctx gadgets) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) : SOk ctx (runJobs K gadgets jobs inputs) := by
  unfold ThresholdLeanXmss.runJobs
  dsimp only
  refine SOk.bind (SOk.foldlM _ (fun x layer => ?_) _ _) fun d => ?_
  · exact SOk.bind (hg.1 _ _ _) fun _ => SOk.pure _
  exact SOk.bind (hg.2.1 _ _) fun _ => SOk.bind (hg.2.2.1 _) fun _ =>
    SOk.bind (hg.2.2.2 _ _) fun _ => SOk.pure _

end Gadgets

theorem ROk.flatMapM (f : α → OracleComp (RoSpec C) (List β)) (hf : ∀ a, ROk ctx (f a)) :
    ∀ xs : List α, ROk ctx (xs.flatMapM f)
  | [] => by simpa using ROk.pure (ctx := ctx) ([] : List β)
  | x :: xs => by
    rw [List.flatMapM_cons]
    exact ROk.bind (hf x) fun _ => ROk.bind (ROk.flatMapM f hf xs) fun _ => ROk.pure _

theorem POk.inputShares (job : Job) : POk (E := E) (G := G) ctx (inputShares ctx job) := by
  unfold ThresholdLeanXmss.inputShares
  refine POk.bind (POk.oracleStep (ROk.mapM _ (fun T => ?_) _)) fun _ => POk.pure _
  split_ifs
  · exact ROk.flatMapM _ (fun x => ROk.map _ (ROk.map _ (ROk.hashQuery _ fun k h => by cases h))) _
  · exact ROk.pure _

section Ceremony

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem SOk.ceremonyBatch (jobs : List Job) :
    SOk (G := G) ctx (ceremonyBatch K circuits settings ctx jobs) := by
  unfold ThresholdLeanXmssSecurity.ceremonyBatch
  refine SOk.bind SOk.get fun lk => ?_
  refine SOk.bind (SOk.lift (POk.mapM _ (fun job => POk.inputShares job) _)) fun inputs => ?_
  refine SOk.bind (SOk.lift (SOk.runJobs K (runOk_real K _) _ _ _)) fun out => ?_
  exact SOk.bind (SOk.set _) fun _ => SOk.pure _

theorem SOk.batched (size : ℕ) (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hrun : ∀ jobs, SOk ctx (run jobs)) (jobs : List Job) : SOk ctx (batched size run jobs) := by
  unfold ThresholdLeanXmss.batched
  exact SOk.bind (SOk.mapM _ hrun _) fun _ => SOk.pure _

theorem SOk.ceremonyOutput (parameter : PublicParameter)
    (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hrun : ∀ jobs, SOk ctx (run jobs)) (top : TopTree) (tree : Tree) :
    SOk ctx (ceremonyOutput (m := StateT σ (PartyM C E G))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter run top tree) := by
  have hl : ∀ {γ : Type} (oa : OracleComp HashSpec γ),
      SOk (σ := σ) ctx (StateT.lift (oracleStep (E := E) (G := G) (tweakable oa))) :=
    fun oa => SOk.lift (POk.oracleStep (ROk.tweakable oa))
  cases tree with
  | top =>
    unfold ThresholdLeanXmss.ceremonyOutput
    refine SOk.bind (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact SOk.pure _
    · dsimp only
      generalize merkleNode _ _ _ _ _ = M
      apply SOk.bind
      · exact hl _
      · intro _
        exact SOk.pure _
  | bottom b =>
    unfold ThresholdLeanXmss.ceremonyOutput
    dsimp only
    refine SOk.bind (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact SOk.pure _
    dsimp only
    generalize merkleNode _ _ _ _ _ = M
    refine SOk.bind (hl _) fun root => ?_
    generalize (truncateHash <$> Concrete.oracleHash _ : OracleComp HashSpec _) = M'
    refine SOk.bind (hl _) fun base => ?_
    generalize grind _ _ _ _ _ _ _ = M''
    refine SOk.bind (hl _) fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · exact SOk.pure _
    refine SOk.bind (hrun _) fun o' => ?_
    rcases o' with _ | values
    · exact SOk.pure _
    dsimp only
    generalize merklePath _ _ _ _ = P
    refine SOk.bind (hl _) fun path => ?_
    generalize (Concrete.layerRoot _ _ _ _ _ : OracleComp HashSpec _) = P'
    refine SOk.bind (hl _) fun topRoot => ?_
    split_ifs
    · exact SOk.pure _
    · exact SOk.pure _

/-- The honest program after setup makes only allowed calls. -/
theorem POk.ceremonyAfterSetup (top : TopTree) (tree : Tree) :
    POk (G := G) ctx (ceremonyAfterSetup K circuits settings ctx top tree) := by
  unfold ThresholdLeanXmssSecurity.ceremonyAfterSetup
  refine POk.bind ?_ fun o => ?_
  · rw [StateT.run'_eq]
    exact POk.map _ (SOk.ceremonyOutput _ _ (fun jobs => SOk.batched _ _
      (fun jobs => SOk.ceremonyBatch K circuits settings jobs) jobs) top tree (0, 0))
  · rcases o with _ | output
    · exact POk.failure
    · exact POk.pure _

end Ceremony

end Discipline

/-! ## The discipline in the execution -/

section Execution

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type}

/-- The local calls of an operator that the rows do not allow. -/
def PartyUnallowed (rows : RevealRows C) : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => ¬ Allowed rows t
  | _ => False

/-- A pending step whose continuations make only allowed calls. -/
def StepOk (rows : RevealRows C) : Step C E G α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, IsQueryBoundP (resume inbox) (PartyUnallowed (E := E) (G := G) rows) 0
  | .call _ resume => ∀ r, IsQueryBoundP (resume r) (PartyUnallowed (E := E) (G := G) rows) 0

theorem advance_ok (rows : RevealRows C) (p : OracleComp (PartySpec C E G) (Option α))
    (h : IsQueryBoundP p (PartyUnallowed (E := E) (G := G) rows) 0) :
    IsQueryBoundP (advance p) (fun t => ¬ Allowed rows t) 0 ∧
      ∀ s ∈ support (advance p), StepOk rows s := by
  induction p using OracleComp.inductionOn with
  | pure out =>
    refine ⟨by simp [advance_pure], fun s hs => ?_⟩
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ PartyUnallowed rows t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (PartyUnallowed rows) 0 := fun u => by
      have := h.2 u
      rwa [if_neg ht] at this
    rcases t with (u | outbox) | input
    · have e : advance (liftM (OracleSpec.query (spec := PartySpec C E G) (.inl (.inl u))) >>= k) =
          OracleComp.lift (OracleSpec.query (spec := LocalSpec C) u) >>= fun r => advance (k r) := rfl
      rw [e]
      refine ⟨?_, fun s hs => ?_⟩
      · erw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl ht, fun r => by simpa [if_neg ht] using (ih r (hk r)).1⟩
      · simp only [support_bind, Set.mem_iUnion] at hs
        obtain ⟨r, -, hs⟩ := hs
        exact (ih r (hk r)).2 s hs
    · have e : advance (liftM (OracleSpec.query (spec := PartySpec C E G) (.inl (.inr outbox))) >>= k) =
          pure (.wait outbox k) := rfl
      rw [e]
      refine ⟨by simp, fun s hs => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact hk
    · have e : advance (liftM (OracleSpec.query (spec := PartySpec C E G) (.inr input)) >>= k) =
          pure (.call input k) := rfl
      rw [e]
      refine ⟨by simp, fun s hs => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact hk

theorem mem_support_sequenceFin' {κ : Type} {spec : OracleSpec κ} {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α) (x : Fin n → α), x ∈ support (Concrete.sequenceFin f) →
      ∀ i, x i ∈ support (f i)
  | 0, f, x, _ => fun i => i.elim0
  | n + 1, f, x, hx => by
    simp only [Concrete.sequenceFin, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hx
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    intro i
    cases i using Fin.cases with
    | zero => exact ha
    | succ i => exact mem_support_sequenceFin' (fun i : Fin n => f i.succ) t ht i

theorem qb0_free_unallowed (rows : RevealRows C) {oa : OracleComp (LocalSpec C) α}
    (h : IsQueryBoundP oa (fun t => ¬ Allowed rows t) 0) : IsQueryBoundP (free oa) (Unallowed rows) 0 :=
  qb0_simulateQ _ (fun t ht => by
    erw [isQueryBoundP_query_iff]
    exact fun h' => absurd h' ht) oa h

theorem qb0_adversary_unallowed (rows : RevealRows C) (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) (Unallowed rows) 0 :=
  qb0_simulateQ _ (fun t _ => by
    erw [isQueryBoundP_query_iff]
    exact fun h' => h'.elim) _ (qb0_false _)

variable (rows : RevealRows C) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)

theorem stepRound_ok (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ j, StepOk rows (steps j)) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) (Unallowed rows) 0 ∧
      ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps), ∀ j, StepOk rows (r.2.1 j) := by
  unfold stepRound
  split_ifs with hc
  · obtain ⟨⟨i, -, hi⟩, -⟩ := hc
    obtain ⟨e, -⟩ := Option.isSome_iff_exists.mp hi
    exact e.elim
  · constructor
    · refine qb0_bind (qb0_adversary_unallowed _ _) fun x => ?_
      rcases x with ⟨st, sent⟩
      refine qb0_bind (isQueryBoundP_sequenceFin _ fun j => ?_) fun _ => by simp
      have hsj := hs j
      rcases hstep : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
      · simp
      · rw [hstep] at hsj
        dsimp only
        split_ifs
        · simp
        · exact qb0_free_unallowed rows (advance_ok rows _ (hsj _)).1
      · simp
    · intro r hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨⟨st, sent⟩, -, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨steps', hsteps', hr⟩ := hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      intro j
      have hm := mem_support_sequenceFin' _ steps' hsteps' j
      have hsj := hs j
      dsimp only at hm ⊢
      revert hm
      rcases hstep : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
      · intro hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        rw [hm]; exact trivial
      · rw [hstep] at hsj
        dsimp only
        split_ifs
        · intro hm
          simp only [support_pure, Set.mem_singleton_iff] at hm
          rw [hm]; exact trivial
        · intro hm
          exact (advance_ok rows _ (hsj _)).2 _ (support_simulateQ_subset _ _ hm)
      · intro hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        rw [hm]; exact trivial

theorem qb0_bind_support {ι' : Type} {spec : OracleSpec ι'} {p : ι' → Prop} [DecidablePred p] {γ δ : Type}
    {oa : OracleComp spec γ} {f : γ → OracleComp spec δ} (h : IsQueryBoundP oa p 0)
    (hf : ∀ a ∈ support oa, IsQueryBoundP (f a) p 0) : IsQueryBoundP (oa >>= f) p 0 := by
  simpa using isQueryBoundP_bind (m := 0) h hf

theorem executeRounds_ok :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      (∀ j, StepOk rows (steps j)) →
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps) (Unallowed rows) 0
  | 0, state, steps, _ => by simp [executeRounds]
  | fuel + 1, state, steps, hs => by
    rw [executeRounds_succ]
    split_ifs
    · simp
    · have h := stepRound_ok rows D A state steps hs
      exact qb0_bind_support h.1 fun r hr => executeRounds_ok fuel _ _ (h.2 r hr)

/-- A program of operator `ctx` makes only calls that the rows allow, when the rows give `ctx` its
keys. -/
theorem partyUnallowed_of_bad {ctx : Context C} {shared : List HashOutput}
    (hrow : rows ctx.self = some (ctx.prss, shared)) (t : (PartySpec C E G).Domain)
    (ht : PartyUnallowed rows t) : PartyBad ctx t := by
  rcases t with ((u | (q | x)) | outbox) | input
  · exact ht trivial
  · by_contra hk
    exact ht fun k hq => hk ⟨k, hq⟩
  · intro hv
    exact ht ⟨ctx.self, ctx.prss, shared, hrow, hv⟩
  · exact ht.elim
  · exact ht.elim

end Execution

theorem probEvent_pair_fst_le {α β : Type} (oa : ProbComp α) (f : α → ProbComp β) (P : α → Prop) :
    Pr[fun y => P y.1 | oa >>= fun r => (fun b => (r, b)) <$> f r] ≤ Pr[P | oa] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  rw [probEvent_map]
  split_ifs with h
  · exact mul_le_of_le_one_right' probEvent_le_one
  · simp [Function.comp_def, h]

/-! ## The stages of the stream-key bound -/

section KeyStages

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The rows of the reveal round, with no row when the round aborts. -/
def rowsOf (rows : Option (RevealRows C)) : RevealRows C := rows.getD fun _ => none

/-- The run of the ideal joint world after the boundary, paired with the result of the prefix. -/
def boundaryRun (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    ProbComp (((A.State × Option (RevealRows C)) × HashCache C) × (Bool × KeyJointState C)) :=
  worldRun prims (setupPrefix D A x z) >>= fun r => (fun y => (r, y)) <$>
    (simulateQ (jointKeyWorld prims D false) (afterDerivation K circuits settings top tree D A x Z r.1)).run
      (boundaryState r.2)

/-- Stage 1, the discipline. After the boundary every free call is allowed by the rows. -/
def AfterDerivationAllowed : Prop :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput) (r : A.State × Option (RevealRows C)),
    IsQueryBoundP (afterDerivation K circuits settings top tree D A x Z r) (Unallowed (rowsOf r.2)) 0

/-- Stage 2, the boundary collisions. The key of a hidden name in a row equals the key of another name
with probability at most `streamKeyError` and one prequery term. -/
def TreeKeysApartBound : Prop :=
  0 < settings.batchSize → ∀ (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)]).toReal ≤
      streamKeyError C + ((q * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256

/-- Stage 3, the hits. With the keys apart, the cache ends with the stream key of a hidden key of a
row with probability at most the rest of `keySplit`. -/
def TreeKeyHitBound : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    (Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash |
      boundaryRun prims K circuits settings top tree D A x z Z]).toReal ≤
      ((3 * q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 256

omit [Fintype E] [DecidableEq E] in
/-- Stage 1. After the boundary every free call is allowed by the rows. -/
theorem afterDerivationAllowed : AfterDerivationAllowed K circuits settings := by
  intro top tree D A x Z r
  rcases r with ⟨st, _ | rows⟩
  · exact qb0_adversary_unallowed _ _
  · have hr : rowsOf (some rows) = rows := rfl
    unfold afterDerivation
    rw [hr]
    dsimp only
    generalize ceremonyFuel circuits settings - 2 = n
    have h2 : ∀ i, StepOk rows (suspendStep (fun prss => (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree :
          PartyM C E RealSpec TreeOutput)) (prssFinishStep i (rows i))) := by
      intro i
      rcases hrow : rows i with _ | ⟨out, shared⟩
      · exact trivial
      · intro inbox
        unfold exchangeResume
        dsimp only
        split_ifs
        · simp
        · have hp : POk (G := RealSpec) (⟨i, x i, out⟩ : Context C)
              ((do require (∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0]); pure out) >>=
                fun prss => (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree :
                  PartyM C E RealSpec TreeOutput)) := by
            rw [bind_assoc]
            refine POk.bind (POk.require _) fun _ => ?_
            rw [pure_bind]
            exact POk.ceremonyAfterSetup K circuits settings top tree
          exact IsQueryBoundP.of_imp (partyUnallowed_of_bad rows (ctx := ⟨i, x i, out⟩) hrow) hp
    exact qb0_bind (executeRounds_ok rows D A n st _ h2) fun _ => qb0_adversary_unallowed _ _

omit [Fintype E] [DecidableEq E] in
/-- The boundary state satisfies the invariant. -/
theorem jointInv_boundaryState (D : C.Coalition) (rows : RevealRows C) (hash : HashCache C) :
    JointInv D rows (boundaryState hash) := by
  refine ⟨fun _ _ h => ?_, fun h => ?_⟩ <;> simp [boundaryState] at h

omit [Fintype E] [DecidableEq E] in
/-- On the support, a raised flag comes with keys that are not apart or with a hit. -/
theorem boundaryRun_bad (hAllowed : AfterDerivationAllowed K circuits settings) (top : TopTree)
    (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) :
    ∀ y ∈ support (boundaryRun prims K circuits settings top tree D A x z Z), y.2.2.bad = true →
      ¬ KeysApart D (rowsOf y.1.1.2) ∨
        (KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash) := by
  intro y hy hbad
  unfold boundaryRun at hy
  simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hy
  obtain ⟨r, -, w, hw, rfl⟩ := hy
  by_cases hg : KeysApart D (rowsOf r.1.2)
  · right
    refine ⟨hg, ?_⟩
    have h := jointKeyWorld_run_inv prims D (rowsOf r.1.2) hg _
      (hAllowed top tree D A x Z r.1) (boundaryState r.2) (jointInv_boundaryState D _ _) w hw
    exact h.1.2 hbad
  · exact Or.inl hg

omit [Fintype E] [DecidableEq E] in
/-- The stream-key bound after the derivation boundary from its three stages. -/
theorem treeStreamKeyAfterDerivation_of_stages (hAllowed : AfterDerivationAllowed K circuits settings)
    (hApart : TreeKeysApartBound (C := C) (E := E) prims circuits settings)
    (hHit : TreeKeyHitBound prims K circuits settings) :
    TreeStreamKeyAfterDerivation prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq
  have he : (worldRun prims (setupPrefix D A x z) >>= fun r =>
      (simulateQ (jointKeyWorld prims D false) (afterDerivation K circuits settings top tree D A x Z r.1)).run
        (boundaryState r.2)) = Prod.snd <$> boundaryRun prims K circuits settings top tree D A x z Z := by
    simp only [boundaryRun, map_bind, Functor.map_map, id_map']
  rw [he, probEvent_map]
  generalize hP : boundaryRun prims K circuits settings top tree D A x z Z = P
  have h1 : Pr[(fun r : Bool × KeyJointState C => r.2.bad = true) ∘ Prod.snd | P] ≤
      Pr[fun y => ¬ KeysApart D (rowsOf y.1.1.2) | P] +
        Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P] :=
    le_trans (probEvent_mono fun y hy hbad =>
      boundaryRun_bad prims K circuits settings hAllowed top tree D A x z Z y (hP ▸ hy) hbad)
      (probEvent_or_le _ _ _)
  have h2 : Pr[fun y => ¬ KeysApart D (rowsOf y.1.1.2) | P] ≤
      Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)] := by
    rw [← hP]
    exact probEvent_pair_fst_le _ _
      (fun r : (A.State × Option (RevealRows C)) × HashCache C => ¬ KeysApart D (rowsOf r.1.2))
  have hA := hApart hb D A x z Z q hx hq
  have hH := hHit hb top tree D A x z Z q hx hq
  rw [hP] at hH
  have hsum : ((q * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256 +
      ((3 * q * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 256 = keySplit C q := by
    unfold keySplit
    rw [← add_div]
    congr 1
    push_cast
    ring
  calc (Pr[(fun r : Bool × KeyJointState C => r.2.bad = true) ∘ Prod.snd | P]).toReal
      ≤ (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)] +
          Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P]).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
          (h1.trans (add_le_add h2 le_rfl))
    _ = (Pr[fun r => ¬ KeysApart D (rowsOf r.1.2) | worldRun prims (setupPrefix D A x z)]).toReal +
          (Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ KeyHit D (rowsOf y.1.1.2) y.2.2.hash | P]).toReal :=
        ENNReal.toReal_add probEvent_ne_top probEvent_ne_top
    _ ≤ _ := by
      rw [← hsum]
      linarith

omit [Fintype E] [DecidableEq E] in
/-- `TreeStreamKeyAfterDerivation`, with stage 1 proved and stages 2 and 3 open. -/
theorem treeStreamKeyAfterDerivation (hApart : TreeKeysApartBound (C := C) (E := E) prims circuits settings)
    (hHit : TreeKeyHitBound prims K circuits settings) :
    TreeStreamKeyAfterDerivation prims K circuits settings :=
  treeStreamKeyAfterDerivation_of_stages prims K circuits settings
    (afterDerivationAllowed K circuits settings) hApart hHit

/-- `TreeSecurityStatement` from the simulation hop and the two open stages of the key hop. -/
theorem treeSecurityOfSim (hApart : TreeKeysApartBound (C := C) (E := E) prims circuits settings)
    (hHit : TreeKeyHitBound prims K circuits settings)
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityFull prims K circuits settings
    (treeStreamKeyAfterDerivation prims K circuits settings hApart hHit) hSim

end KeyStages

/-- info: 'ThresholdLeanXmssSecurity.treeStreamKeyAfterDerivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStreamKeyAfterDerivation

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityOfSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityOfSim

end ThresholdLeanXmssSecurity
