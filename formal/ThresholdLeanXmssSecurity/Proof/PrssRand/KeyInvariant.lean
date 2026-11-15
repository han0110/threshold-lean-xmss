import ThresholdLeanXmssSecurity.Proof.Tree

/-!
# The invariant of the ideal joint world

`jointKeyWorld_run_inv` states that a raised flag of `jointKeyWorld` comes with a hit of a hidden key.
It needs that the keys of different names are apart and that each free stream uses a key of its name.

The text is a port of the section `RowKeys` of `Proof/TreeKey.lean` on the branch
`feature/lean4-proof-2`. A relation `key` between a name and a key value is in the place of the rows
of the reveal round.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee}


/-- A free call that the relation allows. It is a sampling, a hash other than a stream key, or a
stream under a key of its name. -/
def KeyAllowed (key : KeyName C → HashOutput → Prop) : (LocalSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.inl q) => ∀ k, q ≠ .streamKey k
  | .inr (.inr x) => key x.1 x.2.1

/-- A free call that the relation does not allow. -/
def Unallowed (key : KeyName C → HashOutput → Prop) : (WorldSpec C).Domain → Prop
  | .inl _ => False
  | .inr t => ¬ KeyAllowed key t

/-- A key of a hidden name differs from each key of every other name. -/
def KeysApart (D : C.Coalition) (key : KeyName C → HashOutput → Prop) : Prop :=
  ∀ n k n' k', key n k → Hidden D n → key n' k' → n ≠ n' → k ≠ k'

/-- The cache holds the stream key of a key of a hidden name. -/
def KeyHit (D : C.Coalition) (key : KeyName C → HashOutput → Prop) (h : HashCache C) : Prop :=
  ∃ n k, key n k ∧ Hidden D n ∧ h (.streamKey k) ≠ none

/-- The invariant of the ideal joint world. Each used key is a key of its hidden name and has a
private answer, and a raised flag comes with a hit. -/
def JointInv (D : C.Coalition) (key : KeyName C → HashOutput → Prop) (s : KeyJointState C) : Prop :=
  (∀ k n, s.used k = some n → Hidden D n ∧ key n k ∧ s.keys (n, k) ≠ none) ∧
    (s.bad = true → KeyHit D key s.hash)

theorem keyHit_mono {D : C.Coalition} {key : KeyName C → HashOutput → Prop} {h h' : HashCache C} (hle : h ≤ h') :
    KeyHit D key h → KeyHit D key h' := by
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
theorem jointInv_of_hash {D : C.Coalition} {key : KeyName C → HashOutput → Prop} {s : KeyJointState C}
    (hs : JointInv D key s) (h' : HashCache C) (hle : s.hash ≤ h') (b : Bool)
    (hb : b = true → KeyHit D key h') :
    JointInv D key { s with hash := h', bad := s.bad || b } ∧ s.hash ≤ h' := by
  refine ⟨⟨hs.1, ?_⟩, hle⟩
  intro hbad
  simp only [Bool.or_eq_true] at hbad
  rcases hbad with h | h
  · exact keyHit_mono hle (hs.2 h)
  · exact hb h

theorem keyHit_of_used {D : C.Coalition} {key : KeyName C → HashOutput → Prop} {s : KeyJointState C}
    (hs : JointInv D key s) {k : HashOutput} (hk : (s.used k).isSome = true) {h' : HashCache C}
    (hc : h' (.streamKey k) ≠ none) : KeyHit D key h' := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨hh, hrow, -⟩ := hs.1 k n hn
  exact ⟨n, k, hrow, hh, hc⟩

/-- A counted hash keeps the invariant. -/
theorem jointInv_hash (prims : Primitives) {D : C.Coalition} {key : KeyName C → HashOutput → Prop} {s : KeyJointState C}
    (hs : JointInv D key s) (q : Query C) (z : HashOutput × HashCache C)
    (hz : z ∈ support ((hashAnswer prims q).run s.hash)) (b : Bool)
    (hb : b = true → ∃ k, q = .streamKey k ∧ (s.used k).isSome = true) :
    JointInv D key { s with hash := z.2, bad := s.bad || b } ∧ s.hash ≤ z.2 := by
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
theorem jointInv_stream (prims : Primitives) {D : C.Coalition} {key : KeyName C → HashOutput → Prop} {s : KeyJointState C}
    (hs : JointInv D key s) (x : PrgInput C) (z : Bit × HashCache C)
    (hz : z ∈ support ((prgAnswer prims x).run s.hash)) (b : Bool)
    (hb : b = true → (s.used x.2.1).isSome = true) :
    JointInv D key { s with hash := z.2, bad := s.bad || b } ∧ s.hash ≤ z.2 := by
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
theorem jointKeyWorld_inv (prims : Primitives) (D : C.Coalition) (key : KeyName C → HashOutput → Prop)
    (hg : KeysApart D key) (t : (WorldSpec C).Domain) (ht : ¬ Unallowed key t)
    (s : KeyJointState C) (hs : JointInv D key s) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), JointInv D key r.2 ∧ s.hash ≤ r.2.hash := by
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
    simp only [Unallowed, KeyAllowed, not_not] at ht
    cases q <;> simp [keyJointRisk] at hr
    exact absurd rfl (ht _)
  · simp only [Unallowed, KeyAllowed, not_not] at ht
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
theorem jointKeyWorld_run_inv (prims : Primitives) (D : C.Coalition) (key : KeyName C → HashOutput → Prop)
    (hg : KeysApart D key) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hoa : IsQueryBoundP oa (Unallowed key) 0) (s : KeyJointState C) (hs : JointInv D key s) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run s),
      JointInv D key r.2 ∧ s.hash ≤ r.2.hash := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hs, le_rfl⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ Unallowed key t := by
      rcases hoa.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    intro r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    have h₁ := jointKeyWorld_inv prims D key hg t ht s hs p hp
    have hk : IsQueryBoundP (k p.1) (Unallowed key) 0 := by
      have := hoa.2 p.1
      rwa [if_neg ht] at this
    have h₂ := ih p.1 hk p.2 h₁.1 r hr
    exact ⟨h₂.1, h₁.2.trans h₂.2⟩


end ThresholdLeanXmssSecurity
