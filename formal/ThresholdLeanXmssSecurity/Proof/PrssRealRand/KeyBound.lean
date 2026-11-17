import ThresholdLeanXmssSecurity.Proof.PrssRand.Security
import ThresholdLeanXmssSecurity.Proof.PrssRand.KeyHop
import ThresholdLeanXmssSecurity.Proof.SeedGenFinish

/-!
# The stream-key bound of one PRSS setup with the calls of `Rand`

The stream-key event `probBad_streamKey` is the bad event of the joint key world. A private key has
a public use, a first use is already in the cache, or one hidden key has two names.

* `jointKeyWorld_false_run_inv` is the order-free form of the stream-key event. In the ideal joint
  world, a raised flag comes with a used key whose stream key is in the cache, or with one key under
  two hidden names. It holds for every computation and needs no relation of keys.
* `keyFlag` is the conservative flag on the view of `flagZ`. A live hidden key meets a log or a known
  key, or two hidden names share one key.
* `keyFlag_hiddenOverlay` and `prob_view_fresh_le` bound the flag with fresh hidden keys, when the
  fresh keys are sampled after the view.
* `prssRealRand_key` bounds the stream-key event of `prssRealRandGame` from two premises. The first
  is the coupling of the ideal joint world with the logged setup run and `flagZ`. The second is the
  law of the view, `prssRealRand_view`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Invariant

variable {C : Committee}

/-- The final state of the ideal joint world shows the stream-key event. A used key has its stream key
in the cache, or one key has a private answer under two hidden names. -/
def UsedHit (D : C.Coalition) (s : KeyJointState C) : Prop :=
  (∃ k n, s.used k = some n ∧ s.hash (.streamKey k) ≠ none) ∨
    ∃ n n' k, Hidden D n ∧ Hidden D n' ∧ n ≠ n' ∧ s.keys (n, k) ≠ none ∧ s.keys (n', k) ≠ none

/-- Each used key has a private answer under its hidden name, and a raised flag comes with `UsedHit`. -/
def FreeInv (D : C.Coalition) (s : KeyJointState C) : Prop :=
  (∀ k n, s.used k = some n → Hidden D n ∧ s.keys (n, k) ≠ none) ∧ (s.bad = true → UsedHit D s)

/-- The state `s'` keeps every entry of `s`. -/
def Extends (s s' : KeyJointState C) : Prop :=
  s.hash ≤ s'.hash ∧ (∀ x, s.keys x ≠ none → s'.keys x ≠ none) ∧ ∀ k n, s.used k = some n → s'.used k = some n

theorem Extends.refl (s : KeyJointState C) : Extends s s :=
  ⟨le_rfl, fun _ h => h, fun _ _ h => h⟩

theorem Extends.trans {s s' s'' : KeyJointState C} (h : Extends s s') (h' : Extends s' s'') : Extends s s'' :=
  ⟨h.1.trans h'.1, fun x hx => h'.2.1 x (h.2.1 x hx), fun k n hk => h'.2.2 k n (h.2.2 k n hk)⟩

theorem cache_ne_none_of_le {h h' : HashCache C} (hle : h ≤ h') {q : Query C} (hq : h q ≠ none) : h' q ≠ none := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hq
  rw [hle hu]
  exact Option.some_ne_none u

theorem UsedHit.mono {D : C.Coalition} {s s' : KeyJointState C} (h : Extends s s') : UsedHit D s → UsedHit D s' := by
  rintro (⟨k, n, hn, hc⟩ | ⟨n, n', k, hn, hn', hne, hk, hk'⟩)
  · exact Or.inl ⟨k, n, h.2.2 k n hn, cache_ne_none_of_le h.1 hc⟩
  · exact Or.inr ⟨n, n', k, hn, hn', hne, h.2.1 _ hk, h.2.1 _ hk'⟩

/-- A step that only grows the public cache keeps the invariant, when its risk comes with `UsedHit`. -/
theorem freeInv_of_hash {D : C.Coalition} {s : KeyJointState C} (hs : FreeInv D s) (h' : HashCache C)
    (hle : s.hash ≤ h') (b : Bool) (hb : b = true → ∃ k n, s.used k = some n ∧ h' (.streamKey k) ≠ none) :
    FreeInv D { s with hash := h', bad := s.bad || b } ∧ Extends s { s with hash := h', bad := s.bad || b } := by
  have he : Extends s { s with hash := h', bad := s.bad || b } := ⟨hle, fun _ h => h, fun _ _ h => h⟩
  refine ⟨⟨hs.1, fun hbad => ?_⟩, he⟩
  simp only [Bool.or_eq_true] at hbad
  rcases hbad with h | h
  · exact UsedHit.mono he (hs.2 h)
  · obtain ⟨k, n, hn, hc⟩ := hb h
    exact Or.inl ⟨k, n, hn, hc⟩

theorem used_of_isSome {s : KeyJointState C} {k : HashOutput} (hk : (s.used k).isSome = true) :
    ∃ n, s.used k = some n :=
  Option.isSome_iff_exists.mp hk

/-- A hash keeps the invariant. -/
theorem freeInv_hash (prims : Primitives) {D : C.Coalition} {s : KeyJointState C} (hs : FreeInv D s) (q : Query C)
    (z : HashOutput × HashCache C) (hz : z ∈ support ((hashAnswer prims q).run s.hash)) (b : Bool)
    (hb : b = true → ∃ k, q = .streamKey k ∧ (s.used k).isSome = true) :
    FreeInv D { s with hash := z.2, bad := s.bad || b } ∧ Extends s { s with hash := z.2, bad := s.bad || b } := by
  refine freeInv_of_hash hs z.2 (grows_hashAnswer prims q s.hash z hz) b fun h => ?_
  obtain ⟨k, rfl, hk⟩ := hb h
  obtain ⟨n, hn⟩ := used_of_isSome hk
  exact ⟨k, n, hn, hashAnswer_streamKey_cached prims k s.hash z hz⟩

/-- A stream on the public cache keeps the invariant. -/
theorem freeInv_stream (prims : Primitives) {D : C.Coalition} {s : KeyJointState C} (hs : FreeInv D s) (x : PrgInput C)
    (z : Bit × HashCache C) (hz : z ∈ support ((prgAnswer prims x).run s.hash)) (b : Bool)
    (hb : b = true → (s.used x.2.1).isSome = true) :
    FreeInv D { s with hash := z.2, bad := s.bad || b } ∧ Extends s { s with hash := z.2, bad := s.bad || b } := by
  obtain ⟨w, hw, he⟩ := prgAnswer_support prims x s.hash z hz
  rw [he]
  refine freeInv_of_hash hs w.2 (grows_hashAnswer prims _ s.hash w hw) b fun h => ?_
  obtain ⟨n, hn⟩ := used_of_isSome (hb h)
  exact ⟨x.2.1, n, hn, hashAnswer_streamKey_cached prims _ s.hash w hw⟩

/-- The first private answer of a hidden name keeps the invariant. -/
theorem freeInv_hidden_fresh {D : C.Coalition} {s : KeyJointState C} (hs : FreeInv D s) (x : PrgInput C)
    (hh : Hidden D x.1) (hk : s.keys (x.1, x.2.1) = none) (v : HashOutput) :
    let s' : KeyJointState C := ⟨s.hash, s.keys.cacheQuery (x.1, x.2.1) v,
      if (s.used x.2.1).isSome then s.used else Function.update s.used x.2.1 (some x.1), s.bad⟩
    FreeInv D { s' with bad := s.bad || keyJointRisk D (.inr (.inr (.inr x))) s } ∧
      Extends s { s' with bad := s.bad || keyJointRisk D (.inr (.inr (.inr x))) s } := by
  intro s'
  have hkeys : ∀ n k, s.keys (n, k) ≠ none → (s.keys.cacheQuery (x.1, x.2.1) v) (n, k) ≠ none := by
    intro n k h
    by_cases he : (n, k) = (x.1, x.2.1)
    · rw [he, QueryCache.cacheQuery_self]
      exact Option.some_ne_none v
    · rw [QueryCache.cacheQuery_of_ne _ _ he]
      exact h
  have hnew : (s.keys.cacheQuery (x.1, x.2.1) v) (x.1, x.2.1) ≠ none := by
    rw [QueryCache.cacheQuery_self]
    exact Option.some_ne_none v
  have hused : ∀ k n, s.used k = some n → s'.used k = some n := by
    intro k n hn
    by_cases hu : (s.used x.2.1).isSome
    · simp only [s', hu, ↓reduceIte]
      exact hn
    · simp only [s', hu, Bool.false_eq_true, ↓reduceIte]
      by_cases hk' : k = x.2.1
      · subst hk'
        rw [hn] at hu
        exact absurd rfl hu
      · rw [Function.update_of_ne hk']
        exact hn
  have he : Extends s { s' with bad := s.bad || keyJointRisk D (.inr (.inr (.inr x))) s } :=
    ⟨le_rfl, fun ⟨n, k⟩ h => hkeys n k h, hused⟩
  have hsome : ∃ n, s'.used x.2.1 = some n := by
    by_cases hu : (s.used x.2.1).isSome
    · simp only [s', hu, ↓reduceIte]
      exact used_of_isSome hu
    · simp only [s', hu, Bool.false_eq_true, ↓reduceIte, Function.update_self]
      exact ⟨x.1, rfl⟩
  refine ⟨⟨?_, ?_⟩, he⟩
  · intro k n hn
    by_cases hu : (s.used x.2.1).isSome
    · simp only [s', hu, ↓reduceIte] at hn
      obtain ⟨h1, h3⟩ := hs.1 k n hn
      exact ⟨h1, hkeys n k h3⟩
    · simp only [s', hu, Bool.false_eq_true, ↓reduceIte] at hn
      by_cases hk' : k = x.2.1
      · subst hk'
        simp only [Function.update_self, Option.some.injEq] at hn
        subst hn
        exact ⟨hh, hnew⟩
      · rw [Function.update_of_ne hk'] at hn
        obtain ⟨h1, h3⟩ := hs.1 k n hn
        exact ⟨h1, hkeys n k h3⟩
  · intro hb
    simp only [keyJointRisk, hh, ↓reduceIte, hk, Option.isSome_none, Bool.not_false, Bool.true_and,
      Bool.or_eq_true] at hb
    rcases hb with hb | hb | hb
    · exact UsedHit.mono he (hs.2 hb)
    · obtain ⟨n, hn⟩ := hsome
      exact Or.inl ⟨x.2.1, n, hn, by simpa only [s', Option.isSome_iff_ne_none] using hb⟩
    · obtain ⟨n', hn'⟩ := used_of_isSome hb
      obtain ⟨h1, h3⟩ := hs.1 _ n' hn'
      have hne : x.1 ≠ n' := by
        rintro rfl
        exact h3 hk
      exact Or.inr ⟨x.1, n', x.2.1, hh, h1, hne, hnew, hkeys n' x.2.1 h3⟩

/-- One step of the ideal joint world keeps the invariant. -/
theorem jointKeyWorld_false_inv (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : KeyJointState C) (hs : FreeInv D s) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), FreeInv D r.2 ∧ Extends s r.2 := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inl u))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact freeInv_of_hash hs z.2 (grows_localAnswer prims (.inl u) s.hash z hz) _
      (by simp only [keyJointRisk, Bool.false_eq_true, false_imp_iff])
  · have hp' : p ∈ support ((onJointHash (hashAnswer prims q)).run s) := by
      rw [← jointHash_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine freeInv_hash prims hs q z hz _ fun hr => ?_
    cases q <;> simp only [keyJointRisk, Bool.false_eq_true] at hr
    exact ⟨_, rfl, hr⟩
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inr (.inr x)))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact freeInv_stream prims hs x z hz _ fun hr => by simpa only [keyJointRisk] using hr
  · have hp' : p ∈ support ((onJointHash (programAnswer (q, v))).run s) := by
      rw [← jointProgram_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine freeInv_of_hash hs z.2 (grows_programAnswer (q, v) s.hash z hz) _ fun hr => ?_
    cases q <;> simp only [keyJointRisk, Bool.false_eq_true] at hr
    obtain ⟨n, hn⟩ := used_of_isSome hr
    exact ⟨_, n, hn, programAnswer_streamKey_cached _ v s.hash z hz⟩
  · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inl u))).run s) := by
      rw [← jointLocal_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    exact freeInv_of_hash hs z.2 (grows_localAnswer prims (.inl u) s.hash z hz) _
      (by simp only [keyJointRisk, Bool.false_eq_true, false_imp_iff])
  · have hp' : p ∈ support ((onJointHash (hashAnswer prims q)).run s) := by
      rw [← jointHash_false]; exact hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
    refine freeInv_hash prims hs q z hz _ fun hr => ?_
    cases q <;> simp only [keyJointRisk, Bool.false_eq_true] at hr
    exact ⟨_, rfl, hr⟩
  · by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
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
          simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk]
        rw [hrun] at hw
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
        obtain ⟨v, -, rfl⟩ := hw
        exact freeInv_hidden_fresh hs x hh hk v
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = pure (v, s) := by
          simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk]
        rw [hrun, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact freeInv_of_hash hs s.hash le_rfl _ (by simp only [keyJointRisk, hh, ↓reduceIte, hk, Option.isSome_some, Bool.not_true,
          Bool.false_and, Bool.false_eq_true, ne_eq, exists_and_right, IsEmpty.forall_iff])
    · have hp' : p ∈ support ((onJointHash (localAnswer prims (.inr (.inr x)))).run s) := by
        have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) =
            jointLocal prims false (.inr (.inr x)) := by
          simp only [jointKeyWorldCore, hh, ↓reduceIte]
        rw [hc] at hp
        rw [← jointLocal_false]
        exact hp
      obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp'
      exact freeInv_stream prims hs x z hz _ fun hr => by simpa only [keyJointRisk, hh, ↓reduceIte] using hr

/-- Every computation keeps the invariant in the ideal joint world. -/
theorem jointKeyWorld_false_run_inv (prims : Primitives) (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (s : KeyJointState C) (hs : FreeInv D s) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run s), FreeInv D r.2 ∧ Extends s r.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hs, Extends.refl s⟩
  | query_bind t k ih =>
    intro r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    have h₁ := jointKeyWorld_false_inv prims D t s hs p hp
    have h₂ := ih p.1 p.2 h₁.1 r hr
    exact ⟨h₂.1, h₁.2.trans h₂.2⟩

theorem freeInv_initial (D : C.Coalition) : FreeInv D (keyJointInitial (C := C)) :=
  ⟨fun _ _ h => absurd h (by simp only [keyJointInitial, reduceCtorEq, not_false_eq_true]),
    fun h => absurd h (by simp only [keyJointInitial, Bool.false_eq_true, not_false_eq_true])⟩

/-- The stream-key event of every game is at most the probability of `UsedHit` at the end of the ideal
joint world. -/
theorem probBad_streamKey_le_usedHit (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    probBad_streamKey prims D game ≤
      (Pr{let r ← (simulateQ (jointKeyWorld prims D false) game).run keyJointInitial}[UsedHit D r.2]).toReal := by
  rw [probBad_streamKey_eq_ideal]
  refine ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono_of_support _ _ _ fun r hr hb => ?_)
  exact (jointKeyWorld_false_run_inv prims D game keyJointInitial (freeInv_initial D) r hr).1.2 hb

end Invariant

section Flag

variable {C : Committee}

/-- What the flag distinguisher holds at its end. -/
structure FlagView (C : Committee) where
  log : List HashOutput
  out : C.Party → Option (Keys C)
  known : List HashOutput
  hashes : List HashOutput
  zlog : List HashOutput

/-- The key that operator `i` holds for the name `n`, when `n` is a name of `i`. -/
def heldKey (i : C.Party) (k : Keys C) : KeyName C → Option HashOutput
  | .parameter => none
  | .term T => if i ∈ C.holders T then some (k.seed T) else none
  | .pair p => if i = p.1.1 then some (k.pairKey p.1.2) else if i = p.1.2 then some (k.pairKey p.1.1) else none

/-- A live honest operator holds `key` for the hidden name `n`. -/
def HiddenKey (D : C.Coalition) (out : C.Party → Option (Keys C)) (n : KeyName C) (key : HashOutput) : Prop :=
  ∃ i k, i ∉ D.1 ∧ out i = some k ∧ Hidden D n ∧ heldKey i k n = some key

/-- The conservative flag. A hidden key of a live honest operator is in the log of the adversary,
in the known keys or in the log of the distinguisher, or it is a key of a second hidden name. -/
def KeyFlag (D : C.Coalition) (v : FlagView C) : Prop :=
  ∃ n key, HiddenKey D v.out n key ∧
    (key ∈ v.log ∨ key ∈ v.known ∨ key ∈ v.zlog ∨ ∃ n', n' ≠ n ∧ HiddenKey D v.out n' key)

def keyFlag (D : C.Coalition) (v : FlagView C) : Bool := decide (KeyFlag D v)

theorem pairOf_endpoints (p : C.Pair) (h : p.1.1 ≠ p.1.2) : C.pairOf p.1.1 p.1.2 h = p := by
  unfold Committee.pairOf
  simp only [p.2, ↓reduceDIte]

/-- With fresh hidden keys, each hidden key of a live honest operator is the fresh key of its name. -/
theorem heldKey_hiddenOverlay (D : C.Coalition) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (i : C.Party) (k : Keys C) (hi : i ∉ D.1) (n : KeyName C) (hn : Hidden D n) (key : HashOutput)
    (hk : heldKey i (seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i)) n = some key) :
    dealtKey seeds pairs n = some key := by
  rcases n with _ | T | p
  · simp only [heldKey, reduceCtorEq] at hk
  · simp only [Hidden] at hn
    by_cases hT : i ∈ C.holders T
    · simp only [heldKey, hT, ↓reduceIte, seedGenHiddenOverlay, hn, dealtKeys, Option.some.injEq] at hk
      simp only [dealtKey, hk]
    · simp only [heldKey, hT, ↓reduceIte, reduceCtorEq] at hk
  · simp only [Hidden] at hn
    have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    by_cases h1 : i = p.1.1
    · subst h1
      have hne' : p.1.2 ≠ p.1.1 := fun e => hne e.symm
      simp only [heldKey, ↓reduceIte, seedGenHiddenOverlay, hi, hn.2, or_self, dealtKeys, hne', dite_false,
        pairOf_endpoints p hne, Option.some.injEq] at hk
      simp only [dealtKey, hk]
    · by_cases h2 : i = p.1.2
      · subst h2
        simp only [heldKey, h1, ↓reduceIte, seedGenHiddenOverlay, hi, hn.1, or_self, dealtKeys, hne, dite_false,
          Option.some.injEq] at hk
        rw [pairOf_comm, pairOf_endpoints p hne] at hk
        simp only [dealtKey, hk]
      · simp only [heldKey, h1, h2, ↓reduceIte, reduceCtorEq] at hk

/-- A fresh hidden key is in `list`, or two hidden names have one fresh key. -/
def FreshEvent (D : C.Coalition) (r : (C.Term → HashOutput) × (C.Pair → HashOutput)) (list : List HashOutput) : Prop :=
  (∃ n key, Hidden D n ∧ dealtKey r.1 r.2 n = some key ∧ key ∈ list) ∨
    ∃ n n' key, Hidden D n ∧ n ≠ n' ∧ dealtKey r.1 r.2 n = some key ∧ dealtKey r.1 r.2 n' = some key

/-- The flag on the outputs of `seedGenHiddenZ` is an event of the fresh keys and the three lists.
A fresh hidden key is in the lists, or two hidden names have one fresh key. -/
theorem keyFlag_hiddenOverlay (D : C.Coalition) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (out : C.Party → Option (Keys C)) (log known hashes zlog : List HashOutput)
    (h : KeyFlag D ⟨log, fun i => (out i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i),
      known, hashes, zlog⟩) :
    FreshEvent D (seeds, pairs) (log ++ known ++ zlog) := by
  have hfresh : ∀ n key, HiddenKey D (fun i => (out i).map fun k =>
      seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i)) n key → Hidden D n ∧ dealtKey seeds pairs n = some key := by
    rintro n key ⟨i, k', hi, hk', hn, hkey⟩
    obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hk'
    exact ⟨hn, heldKey_hiddenOverlay D seeds pairs i k hi n hn key hkey⟩
  obtain ⟨n, key, hk, hl⟩ := h
  obtain ⟨hn, hd⟩ := hfresh n key hk
  rcases hl with hl | hl | hl | ⟨n', hne, hk'⟩
  · exact Or.inl ⟨n, key, hn, hd, by simp only [List.mem_append, hl, true_or]⟩
  · exact Or.inl ⟨n, key, hn, hd, by simp only [List.mem_append, hl, or_true, true_or]⟩
  · exact Or.inl ⟨n, key, hn, hd, by simp only [List.mem_append, hl, or_true]⟩
  · exact Or.inr ⟨n, n', key, hn, fun e => hne e.symm, hd, (hfresh n' key hk').2⟩

end Flag

section Fresh

open ENNReal

variable {C : Committee}

/-- The fresh dealt keys. -/
def freshKeys : ProbComp ((C.Term → HashOutput) × (C.Pair → HashOutput)) := do
  let term ← $ᵗ (C.Term → HashOutput)
  let pair ← $ᵗ (C.Pair → HashOutput)
  pure (term, pair)

/-- The fresh key of one name is in a fixed list with probability at most `|list| / 2^256`. -/
theorem prob_dealtKey_mem_le (n : KeyName C) (list : List HashOutput) :
    Pr{let r ← freshKeys (C := C)}[∃ key, dealtKey r.1 r.2 n = some key ∧ key ∈ list] ≤
      (list.length : ℝ≥0∞) / 2 ^ 256 := by
  have hcard : ∀ (v : Unit) s, s ∈ support (pure list.toFinset : ProbComp (Finset HashOutput)) →
      s.card ≤ list.length := by
    intro _ s hs
    rw [support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact List.toFinset_card_le list
  unfold freshKeys
  rcases n with _ | T | p
  · simp only [dealtKey, reduceCtorEq, false_and, exists_false, prEvent_false, zero_le]
  · simp only [dealtKey, Option.some.injEq, exists_eq_left']
    rw [((OracleComp.EvalDistEq.bind_bind_swap _ _ _)).prEvent_eq]
    apply prEvent_bind_le_of_forall_le_of_support
    intro pair _
    have h := prob_uniformTable_guess_le T (fun _ => ()) (fun _ _ => rfl) (fun _ => pure list.toFinset)
      list.length hcard
    simp only [map_pure, bind_pure_comp, prEvent_map, decide_eq_true_eq, List.mem_toFinset] at h ⊢
    exact h
  · simp only [dealtKey, Option.some.injEq, exists_eq_left']
    apply prEvent_bind_le_of_forall_le_of_support
    intro term _
    have h := prob_uniformTable_guess_le p (fun _ => ()) (fun _ _ => rfl) (fun _ => pure list.toFinset)
      list.length hcard
    simp only [map_pure, bind_pure_comp, prEvent_map, decide_eq_true_eq, List.mem_toFinset] at h ⊢
    exact h

/-- The bound of the fresh keys for a fixed list. A fresh hidden key is in a fixed list, or two hidden names have
one fresh key, with probability at most `k (|list| + k) / 2^256`, with `k = prssKeyCount C`. -/
theorem prob_fresh_event_le (D : C.Coalition) (list : List HashOutput) :
    Pr{let r ← freshKeys (C := C)}[FreshEvent D r list] ≤
      ((prssKeyCount C * (list.length + prssKeyCount C) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold FreshEvent
  let name : C.Term ⊕ C.Pair → KeyName C := Sum.elim .term .pair
  let names := Finset.univ.image name
  have hname : ∀ (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) n k,
      dealtKey term pair n = some k → n ∈ names := by
    intro term pair n k h
    rcases n with _ | T | p
    · simp only [dealtKey, reduceCtorEq] at h
    · exact Finset.mem_image.2 ⟨.inl T, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.2 ⟨.inr p, Finset.mem_univ _, rfl⟩
  have hcard : names.card ≤ prssKeyCount C := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_sum, card_term C, prssKeyCount, termCount]
    exact Nat.add_le_add_left (card_pair_le C) _
  have hlist : Pr{let r ← freshKeys (C := C)}[∃ n key, Hidden D n ∧ dealtKey r.1 r.2 n = some key ∧ key ∈ list] ≤
      ((prssKeyCount C * list.length : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    calc _ ≤ Pr{let r ← freshKeys (C := C)}[∃ n ∈ names, ∃ key, dealtKey r.1 r.2 n = some key ∧ key ∈ list] := by
          refine prEvent_mono _ _ _ fun r hr => ?_
          obtain ⟨n, key, -, hk, hl⟩ := hr
          exact ⟨n, hname _ _ _ _ hk, key, hk, hl⟩
      _ ≤ names.card * ((list.length : ℝ≥0∞) / 2 ^ 256) :=
          prEvent_exists_finset_le_card_mul _ _ _ fun n _ => prob_dealtKey_mem_le n list
      _ ≤ _ := by
          rw [← mul_div_assoc, Nat.cast_mul]
          gcongr
  have hequal := prob_dealt_keys_equal_le (C := C) D
  refine (prEvent_or_le _ _ _).trans ((add_le_add hlist hequal).trans (le_of_eq ?_))
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  congr 2
  ring

/-- The fresh keys are sampled after a list of length at most `β`. Then the event has probability at
most `prssRandHashError C β`. -/
theorem prob_view_fresh_le (D : C.Coalition) (view : ProbComp (List HashOutput)) (β : ℕ)
    (hlen : ∀ list ∈ support view, list.length ≤ β) :
    (Pr{let p ← (do let list ← view; let r ← freshKeys (C := C); pure (list, r))}[FreshEvent D p.2 p.1]).toReal ≤
      prssRandHashError C β := by
  have h : Pr{let p ← (do let list ← view; let r ← freshKeys (C := C); pure (list, r))}[FreshEvent D p.2 p.1] ≤
      ((prssKeyCount C * (β + prssKeyCount C) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    apply prEvent_bind_le_of_forall_le_of_support
    intro list hl
    simp only [bind_pure_comp, prEvent_map]
    refine (prob_fresh_event_le D list).trans ?_
    gcongr
    exact hlen list hl
  refine (ENNReal.toReal_mono (by simp only [ne_eq, ENNReal.div_eq_top, ENNReal.natCast_ne_top, false_and,
    pow_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, or_self, not_false_eq_true]) h).trans (le_of_eq ?_)
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat, prssRandHashError]

end Fresh

section Log

variable {C : Committee} {E : Type}

/-! ## The log of the adversary -/

/-- The key of a stream-key call or of a `PRG` call. -/
def streamKeyOf : (LocalSpec C).Domain → Option HashOutput
  | .inr (.inl (.streamKey k)) => some k
  | .inr (.inr x) => some x.2.1
  | _ => none

/-- Each call goes to the oracle, and its key goes to the log. -/
def logImpl : QueryImpl (LocalSpec C) (StateT (List HashOutput) (OracleComp (LocalSpec C))) := fun t => do
  let u ← StateT.lift (query (spec := LocalSpec C) t : OracleComp (LocalSpec C) _)
  modify fun log => (streamKeyOf t).toList ++ log
  pure u

theorem isQueryBoundP_logImpl (t : (LocalSpec C).Domain) (log : List HashOutput) :
    IsQueryBoundP ((logImpl t).run log) Counted (if Counted t then 1 else 0) := by
  simp only [logImpl, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_assoc,
    pure_bind, HasQuery.instOfMonadLift_query]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨?_, fun u => ?_⟩
  · by_cases h : Counted t
    · exact Or.inr (by simp only [h, ite_true, Nat.lt_add_one])
    · exact Or.inl h
  · by_cases h : Counted t
    · simp only [h, ite_true, Nat.sub_self]
      exact isQueryBoundP_pure _ _ 0
    · simp only [h, ite_false]
      exact isQueryBoundP_pure _ _ 0

theorem isQueryBoundP_simulateQ_logImpl {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) (log : List HashOutput) :
    IsQueryBoundP ((simulateQ logImpl oa).run log) Counted n :=
  IsQueryBoundP.simulateQ_run_StateT_of_step h (fun t s => isQueryBoundP_logImpl t s) log

/-- The adversary `A` with a log of its stream keys in its state. -/
def logAdversary (A : Adversary C E Unit PEmpty PEmpty) : Adversary C E Unit PEmpty PEmpty where
  State := A.State × List HashOutput
  start x z := (simulateQ logImpl (A.start x z)).run []
  round st sent := (simulateQ logImpl (A.round st.1 sent)).run st.2 >>= fun p => pure ((p.1.1, p.2), p.1.2)
  answer _ l := l.elim

/-! ## The flag distinguisher -/

/-- The keys of known names that operator `i` holds, one for each known term of `i` and each corrupt
operator. -/
def partyKnownKeys (D : C.Coalition) (i : C.Party) : Option (Keys C) → List HashOutput
  | none => []
  | some k => (C.terms.filterMap fun T => if KnownTo D.1 T ∧ i ∈ C.holders T then some (k.seed T) else none) ++
      C.parties.filterMap fun j => if j ∈ D.1 ∧ j ≠ i then some (k.pairKey j) else none

/-- The keys of known names that the live honest operators hold. -/
def liveKnownKeys (D : C.Coalition) (out : C.Party → Option (Keys C)) : List HashOutput :=
  C.parties.flatMap fun i => if i ∈ D.1 then [] else partyKnownKeys D i (out i)

theorem partyKnownKeys_length_le (D : C.Coalition) (i : C.Party) (o : Option (Keys C)) :
    (partyKnownKeys D i o).length ≤ termCount C + C.n := by
  cases o with
  | none => simp only [partyKnownKeys, List.length_nil, Nat.zero_le]
  | some k =>
    simp only [partyKnownKeys, List.length_append, Committee.parties]
    have h₁ := List.length_filterMap_le (fun T => if KnownTo D.1 T ∧ i ∈ C.holders T then some (k.seed T) else none)
      C.terms
    have h₂ := List.length_filterMap_le (fun j => if j ∈ D.1 ∧ j ≠ i then some (k.pairKey j) else none) C.parties
    simp only [check_terms_length, Committee.parties, List.length_finRange] at h₁ h₂
    simp only [termCount]
    omega

theorem liveKnownKeys_length_le (D : C.Coalition) (out : C.Party → Option (Keys C)) :
    (liveKnownKeys D out).length ≤ C.n * (termCount C + C.n) := by
  unfold liveKnownKeys
  rw [List.length_flatMap]
  have h := List.sum_le_length_nsmul (C.parties.map fun i => (if i ∈ D.1 then [] else partyKnownKeys D i (out i)).length)
    (termCount C + C.n) fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      by_cases hi : i ∈ D.1
      · simp only [hi, ite_true, List.length_nil, Nat.zero_le]
      · simp only [hi, ite_false]
        exact partyKnownKeys_length_le D i (out i)
  simpa only [List.length_map, Committee.parties, List.length_finRange, smul_eq_mul] using h

end Log

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

variable (prims : Primitives)

/-- The real run of `prssRealRandProtocol` with the distinguisher `Z`. -/
def prssRealRandGame (label : ℕ) (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E))) :
    OracleComp (WorldSpec C) Bool :=
  distinguish (realExecution D A noFunctionality setupRounds (prssRealRandProtocol K label calls) x z) Z

/-- `PRG` with no call. A hidden name reads the AES key of `aesKeys`. A known key reads its hash in
the list `known` and `hashes`. -/
def pureStreams (D : C.Coalition) (known hashes : List HashOutput) (aesKeys : KeyName C × HashOutput → Digest) :
    QueryImpl (RoSpec C) Id := fun t => match t with
  | .inl _ => (0 : HashOutput)
  | .inr x => if Hidden D x.1 then prims.aes.eval (aesKeys (x.1, x.2.1)) x.2.2
      else prims.aes.eval (truncateHash (((known.zip hashes).lookup x.2.1).getD 0)) x.2.2

/-- The flag distinguisher. -/
def flagZ (D : C.Coalition) (label : ℕ) (calls : List RandCall) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (List (RandOutput C E))) (flag : FlagView C → Bool) :
    Distinguisher C (logAdversary A).State (Keys C) := fun r => do
  let known := liveKnownKeys D r.2
  let hashes ← known.mapM fun k =>
    (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)
  let aesKeys ← liftComp ($ᵗ (KeyName C × HashOutput → Digest)) (LocalSpec C)
  let outputs : C.Party → Option (List (RandOutput C E)) := fun i => if i ∈ D.1 then none else
    (r.2 i).map fun k => simulateQ (pureStreams prims D known hashes aesKeys)
      (randStreams K prgBits (carrierPrssKeys k) i label calls)
  (simulateQ logImpl (Z (r.1.1, outputs))).run [] >>= fun p => pure (flag ⟨r.1.2, r.2, known, hashes, p.2⟩)

theorem isQueryBoundP_flagZ (D : C.Coalition) (label : ℕ) (calls : List RandCall)
    (A : Adversary C E Unit PEmpty PEmpty) (Z : Distinguisher C A.State (List (RandOutput C E)))
    (flag : FlagView C → Bool) (final : ℕ) (hz : ∀ r, IsQueryBoundP (Z r) Counted final)
    (r : (logAdversary A).State × (C.Party → Option (Keys C))) :
    IsQueryBoundP (flagZ K prims D label calls A Z flag r) Counted (C.n * (termCount C + C.n) + final) := by
  have hhash : IsQueryBoundP ((liveKnownKeys D r.2).mapM fun k =>
      (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput))
      Counted ((liveKnownKeys D r.2).length * 1) :=
    queryBound_mapM Counted _ 1 _ fun k _ => by
      rw [← bind_pure (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)]
      simp only [HasQuery.instOfMonadLift_query]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr Nat.one_pos, fun _ => isQueryBoundP_pure _ _ _⟩
  unfold flagZ
  refine (isQueryBoundP_bind hhash fun hashes _ => isQueryBoundP_liftComp_bind _ _ final fun aesKeys => ?_).mono ?_
  · exact (isQueryBoundP_bind (isQueryBoundP_simulateQ_logImpl _ final (hz _) []) fun p _ =>
      isQueryBoundP_pure Counted _ 0).mono (Nat.le_of_eq (Nat.add_zero final))
  · have h := liveKnownKeys_length_le D r.2
    omega

/-- The budget of the flag reduction. For every `flag`, the pair `logAdversary A` and `flagZ` makes
at most `q + C.n * (termCount C + C.n)` counted calls when `A` and `Z` make at most `q`. -/
theorem logAdversary_flagZ_bounded (D : C.Coalition) (label : ℕ) (calls : List RandCall) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (List (RandOutput C E))) (flag : FlagView C → Bool) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) :
    IsQueryBounded (logAdversary A) (flagZ K prims D label calls A Z flag) setupRounds
      (q + C.n * (termCount C + C.n)) := by
  obtain ⟨start, step, final, hsum, hs, hr, -, hz⟩ := hq
  refine ⟨start, step, C.n * (termCount C + C.n) + final, by omega, fun x z => ?_, fun st sent => ?_,
    fun _ l => l.elim, isQueryBoundP_flagZ K prims D label calls A Z flag final hz⟩
  · exact isQueryBoundP_simulateQ_logImpl _ start (hs x z) []
  · exact (isQueryBoundP_bind (isQueryBoundP_simulateQ_logImpl _ step (hr st.1 sent) st.2) fun p _ =>
      isQueryBoundP_pure Counted ((p.1.1, p.2), p.1.2) 0).mono (Nat.le_of_eq (Nat.add_zero step))

/-- The stream-key bound of the real run for one `flag`. `hflag` states that `flagZ` with `flag`
bounds the stream-key event of the real run. `hfresh` states the bound when the hidden keys of the
outputs are fresh. The budget is `logAdversary_flagZ_bounded`, and the change to fresh keys is
`setupHiddenFresh`. -/
theorem prssRealRand_key_of_flag (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E)))
    (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) (flag : FlagView C → Bool)
    (hflag : probBad_streamKey prims D (prssRealRandGame K label calls D A x z Z) ≤
      accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
          (flagZ K prims D label calls A Z flag)))
    (hfresh : accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
          (seedGenHiddenZ D (flagZ K prims D label calls A Z flag))) ≤
      prssRandHashError C (q + C.n * (termCount C + C.n))) :
    probBad_streamKey prims D (prssRealRandGame K label calls D A x z Z) ≤
      prssSetupHashError C (q + C.n * (termCount C + C.n)) / 2 + prssRandHashError C (q + C.n * (termCount C + C.n)) := by
  have h := setupHiddenFresh (C := C) (E := E) prims .prss D (logAdversary A) x z (flagZ K prims D label calls A Z flag) _
    (logAdversary_flagZ_bounded K prims D label calls A Z flag q hq)
  rw [setupHashError_prss] at h
  have h' := (le_abs_self _).trans h
  linarith

/-- The stream-key bound of the real run with the conservative flag `keyFlag`, from two premises.

* `husedHit_le_flag` is the coupling of the ideal joint world on the real run with the logged setup
  run and `flagZ`. With it, the premise `hflag` of `prssRealRand_key_of_flag` follows from
  `probBad_streamKey_le_usedHit`.
* `hflag_le_fresh` states that the fresh keys of `seedGenHiddenZ` can be sampled after a list of
  length at most `q + C.n * (termCount C + C.n)` that holds the log of the adversary, the known keys
  and the log of the distinguisher. With it, the premise `hfresh` follows from
  `prob_view_fresh_le`. -/
theorem prssRealRand_key (label : ℕ) (calls : List RandCall)
    (husedHit_le_flag : ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) x z Z,
      (Pr{let r ← (simulateQ (jointKeyWorld prims D false) (prssRealRandGame K label calls D A x z Z)).run keyJointInitial}[
          UsedHit D r.2]).toReal ≤
        accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
            (flagZ K prims D label calls A Z (keyFlag D))))
    (hflag_le_fresh : ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) x z Z q, IsQueryBounded A Z setupRounds q →
      ∃ view : ProbComp (List HashOutput), (∀ list ∈ support view, list.length ≤ q + C.n * (termCount C + C.n)) ∧
        accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
            (seedGenHiddenZ D (flagZ K prims D label calls A Z (keyFlag D)))) ≤
          (Pr{let p ← (do let list ← view; let r ← freshKeys (C := C); pure (list, r))}[
            FreshEvent D p.2 p.1]).toReal) :
    ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) x z Z q, IsQueryBounded A Z setupRounds q →
      probBad_streamKey prims D (prssRealRandGame K label calls D A x z Z) ≤
        prssSetupHashError C (q + C.n * (termCount C + C.n)) / 2 + prssRandHashError C (q + C.n * (termCount C + C.n)) := by
  intro D A x z Z q hq
  obtain ⟨view, hlen, hle⟩ := hflag_le_fresh D A x z Z q hq
  exact prssRealRand_key_of_flag K prims label calls D A x z Z q hq (keyFlag D)
    ((probBad_streamKey_le_usedHit prims D _).trans (husedHit_le_flag D A x z Z))
    (hle.trans (prob_view_fresh_le D view _ hlen))

end ThresholdLeanXmssSecurity
