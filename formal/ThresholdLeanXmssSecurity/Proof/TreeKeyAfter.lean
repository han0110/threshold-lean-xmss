import ThresholdLeanXmssSecurity.Proof.TreeKeyHit
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The hit of the stream key after the boundary

Part 2 of `TreeKeyHit.lean`, `TreeKeyAfterHitBound`, in two stages.

1. The aimed calls (`probEvent_afterHit_le_aimed`). With the keys apart, a free call after the
   boundary never caches the stream key of a hidden row key (`afterDerivationAllowed`). So a new hit
   comes with a counted call that can cache it (`AimedCall`). The flagged run then moves to the lazy
   AES-key world with its cache (`probEvent_aimed_eq_lazy`). There a swap of two hidden keys of the
   honest streams keeps the law, the flag and the hash cache (`evalDist_lazyAimed_rename`).
2. `TreeKeyAimedBound`. An aimed call needs the secrecy of the hidden keys after the boundary.
   The prefix calls stay in its bound, because a prefix call can query a hidden canonical input.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

open scoped ENNReal

section AimedCalls

variable {C : Committee}

/-- The inputs of `H` that a world call can cache in the ideal joint world. A free stream under a
hidden name uses a private key and caches nothing. -/
def Caches (D : C.Coalition) : (WorldSpec C).Domain → Query C → Prop
  | .inl (.inl (.inr (.inl q))), q' => q' = q
  | .inl (.inl (.inr (.inr x))), q' => q' = .streamKey x.2.1
  | .inl (.inr x), q' => q' = x.1
  | .inr (.inr (.inl q)), q' => q' = q
  | .inr (.inr (.inr x)), q' => ¬ Hidden D x.1 ∧ q' = .streamKey x.2.1
  | _, _ => False

/-- A counted call that can cache the stream key of a hidden key of a row. -/
def AimedCall (D : C.Coalition) (rows : RevealRows C) : (WorldSpec C).Domain → Prop
  | .inl t => ∃ n k, RowKey rows n k ∧ Hidden D n ∧ Caches D (.inl t) (.streamKey k)
  | .inr _ => False

theorem hashAnswer_other (prims : Primitives) (q : Query C) (s : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run s), ∀ q', q' ≠ q → z.2 q' = s q' := by
  intro z hz q' hq
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hf
    rw [hashAnswer_of_isFixed prims hm] at hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · rw [hashAnswer_of_not_isFixed prims hf] at hz
    exact (randomOracle_support q s z hz).2.2 q' hq

theorem programAnswer_other (x : Query C × HashOutput) (s : HashCache C) :
    ∀ z ∈ support ((programAnswer x).run s), ∀ q', q' ≠ x.1 → z.2 q' = s q' := by
  intro z hz q' hq
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact QueryCache.cacheQuery_of_ne _ _ hq

theorem unifAnswer_same (u : unifSpec.Domain) (s : HashCache C) :
    ∀ z ∈ support (((unifFwdImpl (Query C →ₒ HashOutput)) u).run s), z.2 = s := by
  intro z hz
  simp [unifFwdImpl] at hz
  obtain ⟨a, rfl⟩ := hz
  rfl

theorem prgAnswer_other (prims : Primitives) (x : PrgInput C) (s : HashCache C) :
    ∀ z ∈ support ((prgAnswer prims x).run s), ∀ q', q' ≠ .streamKey x.2.1 → z.2 q' = s q' := by
  intro z hz q' hq
  obtain ⟨w, hw, he⟩ := prgAnswer_support prims x s z hz
  rw [he]
  exact hashAnswer_other prims _ s w hw q' hq

theorem localAnswer_other (prims : Primitives) (t : (LocalSpec C).Domain) (s : HashCache C) :
    ∀ z ∈ support ((localAnswer prims t).run s), ∀ q',
      (∀ q, t = .inr (.inl q) → q' ≠ q) → (∀ x, t = .inr (.inr x) → q' ≠ .streamKey x.2.1) →
        z.2 q' = s q' := by
  intro z hz q' h1 h2
  rcases t with u | q | x
  · rw [unifAnswer_same u s z hz]
  · exact hashAnswer_other prims q s z hz q' (h1 q rfl)
  · exact prgAnswer_other prims x s z hz q' (h2 x rfl)

/-- One step of the ideal joint world changes the public cache only at an input that the call can
cache. -/
theorem jointKeyWorld_other (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : KeyJointState C) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), ∀ q', ¬ Caches D t q' →
      r.2.hash q' = s.hash q' := by
  intro r hr q' hq
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  dsimp only
  have hloc : ∀ t' (p : (LocalSpec C).Range t' × KeyJointState C),
      p ∈ support ((jointLocal prims false t').run s) →
      (∀ q, t' = .inr (.inl q) → q' ≠ q) → (∀ x, t' = .inr (.inr x) → q' ≠ .streamKey x.2.1) →
        p.2.hash q' = s.hash q' := by
    intro t' p hp h1 h2
    rw [jointLocal_false] at hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp
    exact localAnswer_other prims t' s.hash z hz q' h1 h2
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · exact hloc (.inl u) p hp (by simp) (by simp)
  · exact hloc (.inr (.inl q)) p hp (by rintro _ ⟨⟩; exact hq) (by simp)
  · exact hloc (.inr (.inr x)) p hp (by simp) (by rintro _ ⟨⟩; exact hq)
  · rw [show jointKeyWorldCore prims D false (.inl (.inr (q, v))) = jointProgram false (q, v) from rfl,
      jointProgram_false] at hp
    obtain ⟨z, hz, rfl⟩ := onJointHash_support _ s p hp
    exact programAnswer_other (q, v) s.hash z hz q' hq
  · exact hloc (.inl u) p hp (by simp) (by simp)
  · exact hloc (.inr (.inl q)) p hp (by rintro _ ⟨⟩; exact hq) (by simp)
  · by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, if_pos hh]
      rw [hc] at hp
      simp only [StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      rcases hk : s.keys (x.1, x.2.1) with _ | v
      · simp only [jointHidden, hk, StateT.run_mk, Bool.false_eq_true, if_false, support_bind,
          support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
        obtain ⟨v, -, rfl⟩ := hw
        rfl
      · simp only [jointHidden, hk, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        rfl
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) =
          jointLocal prims false (.inr (.inr x)) := by
        simp only [jointKeyWorldCore, if_neg hh]
      rw [hc] at hp
      exact hloc (.inr (.inr x)) p hp (by simp) (by rintro _ ⟨⟩; exact fun he => hq ⟨hh, he⟩)

/-- An allowed call that is not aimed keeps the cache free of the stream keys of hidden row keys. -/
theorem jointKeyWorld_noKeyHit (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    (hg : KeysApart D rows) (t : (WorldSpec C).Domain) (ht : ¬ Unallowed rows t)
    (ha : ¬ AimedCall D rows t) (s : KeyJointState C) (hs : ¬ KeyHit D rows s.hash) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), ¬ KeyHit D rows r.2.hash := by
  rintro r hr ⟨n, k, hk, hn, hc⟩
  refine hs ⟨n, k, hk, hn, ?_⟩
  rw [← jointKeyWorld_other prims D t s r hr (.streamKey k) ?_]
  · exact hc
  intro hcache
  rcases t with t | (u | q | x)
  · exact ha ⟨n, k, hk, hn, hcache⟩
  · exact hcache
  · simp only [Unallowed, Allowed, not_not] at ht
    exact ht k hcache.symm
  · simp only [Unallowed, Allowed, not_not] at ht
    obtain ⟨hh, he⟩ := hcache
    have hne : n ≠ x.1 := fun h => hh (h ▸ hn)
    exact hg n k x.1 x.2.1 hk hn ht hne (Query.streamKey.inj he)

/-- The ideal joint world that also flags an aimed call. -/
abbrev aimedImpl (prims : Primitives) (D : C.Coalition) (rows : RevealRows C) :
    QueryImpl (WorldSpec C) (StateT (KeyJointState C × Bool) ProbComp) :=
  flagImpl (jointKeyWorld prims D false) (fun t (_ : Unit) => AimedCall D rows t) ()

/-- With only allowed calls and the keys apart, a run with no aimed call keeps the cache free of the
stream keys of hidden row keys. -/
theorem aimedImpl_run_noKeyHit (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    (hg : KeysApart D rows) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hoa : IsQueryBoundP oa (Unallowed rows) 0) (s : KeyJointState C) (b : Bool) :
    ∀ r ∈ support ((simulateQ (aimedImpl prims D rows) oa).run (s, b)), r.2.2 = false →
      b = false ∧ (¬ KeyHit D rows s.hash → ¬ KeyHit D rows r.2.1.hash) := by
  induction oa using OracleComp.inductionOn generalizing s b with
  | pure a =>
    intro r hr hf
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hf, id⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ Unallowed rows t := by
      rcases hoa.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (Unallowed rows) 0 := fun u => by
      have := hoa.2 u
      rwa [if_neg ht] at this
    intro r hr hf
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion, flagImpl, StateT.run_mk, support_map,
      Set.mem_image] at hr
    obtain ⟨p, ⟨w, hw, rfl⟩, hr⟩ := hr
    obtain ⟨hb, hrest⟩ := ih w.1 (hk w.1) w.2 _ r hr hf
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    exact ⟨hb.1, fun hs => hrest (jointKeyWorld_noKeyHit prims D rows hg t ht hb.2 s hs w hw)⟩

/-- The flag forgets to the handler. -/
theorem evalDist_flagImpl_fst {κ σ S α : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (StateT σ ProbComp))
    (hit : κ → S → Prop) (secret : S) (oa : OracleComp spec α) (σ₀ : σ) (b : Bool) :
    𝒟[(fun r => (r.1, r.2.1)) <$> (simulateQ (flagImpl impl hit secret) oa).run (σ₀, b)] =
      𝒟[(simulateQ impl oa).run σ₀] := by
  have h := evalDist_simulateQ_state_projection (flagImpl impl hit secret) impl Prod.fst
    (fun t p => by simp [flagImpl, Functor.map_map]) oa (σ₀, b)
  exact h

/-- The lazy AES-key world that also flags an aimed call. -/
abbrev lazyAimedImpl (prims : Primitives) (D : C.Coalition) (rows : RevealRows C) :
    QueryImpl (WorldSpec C) (StateT ((HashCache C × KeyCache C) × Bool) ProbComp) :=
  flagImpl (lazyKeyWorld prims D) (fun t (_ : Unit) => AimedCall D rows t) ()

/-- The flagged ideal joint world projects to the flagged lazy AES-key world. -/
theorem evalDist_aimedImpl_projection (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    {α : Type} (oa : OracleComp (WorldSpec C) α) (s : KeyJointState C) (b : Bool) :
    𝒟[Prod.map id (fun p => (keyJointIdealProjection p.1, p.2)) <$>
        (simulateQ (aimedImpl prims D rows) oa).run (s, b)] =
      𝒟[(simulateQ (lazyAimedImpl prims D rows) oa).run (keyJointIdealProjection s, b)] := by
  refine evalDist_simulateQ_state_projection _ _ _ (fun t p => ?_) oa (s, b)
  have h := jointKeyWorld_false_query_projection prims D t p.1
  have hm := congrArg (fun d => (fun x => (x.1, (x.2, p.2 || decide (AimedCall D rows t)))) <$> d) h
  simp only [evalDist_map, Functor.map_map] at hm
  simp only [flagImpl, StateT.run_mk, evalDist_map, Functor.map_map]
  exact hm

/-- The swap of the hidden keys `a` and `b` in the flagged lazy state. -/
def aimedStateSwap (D : C.Coalition) (a b : HashOutput) (st : (HashCache C × KeyCache C) × Bool) :
    (HashCache C × KeyCache C) × Bool :=
  ((st.1.1, keyCacheSwap D a b st.1.2), st.2)

/-- A flagged call commutes with the swap of the hidden keys. -/
theorem lazyAimedImpl_query_rename (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    (a b : HashOutput) (q : (WorldSpec C).Domain) (st : (HashCache C × KeyCache C) × Bool) :
    Prod.map id (aimedStateSwap D a b) <$> (lazyAimedImpl prims D rows q).run st =
      (simulateQ (lazyAimedImpl prims D rows) (worldStreamRename D a b q)).run (aimedStateSwap D a b st) := by
  have h := lazyKeyWorld_query_rename prims D a b q st.1
  rcases q with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [worldStreamRename, hiddenQuery, simulateQ_spec_query] at h ⊢
  all_goals simp only [flagImpl, StateT.run_mk, Functor.map_map, aimedStateSwap]
  any_goals (rw [← h, Functor.map_map]; rfl)
  erw [simulateQ_spec_query] at h ⊢
  have h2 := congrArg (fun d => (fun y => (y.1, (y.2, st.2))) <$> d) h
  simp only [Functor.map_map] at h2
  convert h2 using 1
  · simp [aimedStateSwap, AimedCall]
  · simp [AimedCall, flagImpl]

/-- The flagged lazy AES-key world keeps its law and its flag under a swap of the hidden keys of the
honest streams. The hash cache stays the same. -/
theorem evalDist_lazyAimed_rename (prims : Primitives) (D : C.Coalition) (rows : RevealRows C)
    (a b : HashOutput) {α : Type} (game : OracleComp (WorldSpec C) α)
    (st : (HashCache C × KeyCache C) × Bool) :
    𝒟[Prod.map id (aimedStateSwap D a b) <$> (simulateQ (lazyAimedImpl prims D rows) game).run st] =
      𝒟[(simulateQ (lazyAimedImpl prims D rows) (simulateQ (worldStreamRename D a b) game)).run
        (aimedStateSwap D a b st)] := by
  rw [← QueryImpl.simulateQ_compose]
  apply evalDist_simulateQ_state_projection
  intro q state
  rw [QueryImpl.apply_compose, lazyAimedImpl_query_rename]

end AimedCalls

section AfterStages

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `boundaryRun` with a flag on the aimed calls after the boundary. -/
def aimedBoundaryRun (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ProbComp (((A.State × Option (RevealRows C)) × HashCache C) × (Bool × (KeyJointState C × Bool))) :=
  worldRun prims (setupPrefix D A x z) >>= fun r => (fun y => (r, y)) <$>
    (simulateQ (aimedImpl prims D (rowsOf r.1.2)) (afterDerivation K circuits settings top tree D A x Z r.1)).run
      (boundaryState r.2, false)

omit [Fintype E] [DecidableEq E] in
/-- With the keys apart and no boundary hit, a hit at the end comes with an aimed call. -/
theorem probEvent_afterHit_le_aimed (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧
        KeyHit D (rowsOf y.1.1.2) y.2.2.hash |
      boundaryRun prims K circuits settings top tree D A x z Z] ≤
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧ y.2.2.2 = true |
      aimedBoundaryRun prims K circuits settings top tree D A x z Z] := by
  unfold boundaryRun aimedBoundaryRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _
  rw [probEvent_map, probEvent_map]
  by_cases hr : KeysApart D (rowsOf r.1.2) ∧ ¬ KeyHit D (rowsOf r.1.2) r.2
  · set game := afterDerivation K circuits settings top tree D A x Z r.1
    have hl : Pr[fun y => KeyHit D (rowsOf r.1.2) y.2.hash |
        (simulateQ (jointKeyWorld prims D false) game).run (boundaryState r.2)] =
        Pr[fun y => KeyHit D (rowsOf r.1.2) y.2.hash |
          (fun w => (w.1, w.2.1)) <$> (simulateQ (aimedImpl prims D (rowsOf r.1.2)) game).run
            (boundaryState r.2, false)] := by
      rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_flagImpl_fst _ _ _ game _ false).symm]
    calc _ = Pr[fun y => KeyHit D (rowsOf r.1.2) y.2.hash |
          (simulateQ (jointKeyWorld prims D false) game).run (boundaryState r.2)] :=
          probEvent_congr' (fun y _ => by simp [hr]) rfl
      _ = _ := hl
      _ ≤ _ := by
        rw [probEvent_map]
        refine probEvent_mono fun w hw hk => ?_
        refine ⟨hr.1, hr.2, ?_⟩
        by_contra hf
        have := aimedImpl_run_noKeyHit prims D (rowsOf r.1.2) hr.1 game
          (afterDerivationAllowed K circuits settings top tree D A x Z r.1) _ false w hw
          (Bool.eq_false_iff.mpr hf)
        exact this.2 hr.2 hk
  · refine le_of_eq_of_le (probEvent_eq_zero fun y _ hy => hr ⟨hy.1, hy.2.1⟩) zero_le

/-- `aimedBoundaryRun` in the lazy AES-key world. -/
def lazyAimedBoundaryRun (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ProbComp (((A.State × Option (RevealRows C)) × HashCache C) ×
      (Bool × ((HashCache C × KeyCache C) × Bool))) :=
  worldRun prims (setupPrefix D A x z) >>= fun r => (fun y => (r, y)) <$>
    (simulateQ (lazyAimedImpl prims D (rowsOf r.1.2))
      (afterDerivation K circuits settings top tree D A x Z r.1)).run ((r.2, ∅), false)

omit [Fintype E] [DecidableEq E] in
/-- The aimed calls of the ideal joint world are those of the lazy AES-key world. -/
theorem probEvent_aimed_eq_lazy (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧ y.2.2.2 = true |
      aimedBoundaryRun prims K circuits settings top tree D A x z Z] =
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧ y.2.2.2 = true |
      lazyAimedBoundaryRun prims K circuits settings top tree D A x z Z] := by
  unfold aimedBoundaryRun lazyAimedBoundaryRun
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun r => ?_
  congr 1
  rw [probEvent_map, probEvent_map]
  have hb : keyJointIdealProjection (boundaryState r.2) = (r.2, (∅ : KeyCache C)) := by
    simp only [keyJointIdealProjection, boundaryState, Prod.mk.injEq, true_and]
    funext y
    rfl
  rw [← hb, ← probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_aimedImpl_projection prims D (rowsOf r.1.2) _ (boundaryState r.2) false), probEvent_map]
  rfl

/-- Stage 2, the secrecy (open). With the keys apart and no boundary hit, a counted call after the
boundary aims at a hidden key of a row with at most the probability of `TreeKeyAfterHitBound`. -/
def TreeKeyAimedBound : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (start step final : ℕ), DealtInputs D x →
    (∀ x z, IsQueryBoundP (A.start x z) Counted start) →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    (∀ r, IsQueryBoundP (Z r) Counted final) →
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ ¬ KeyHit D (rowsOf y.1.1.2) y.1.2 ∧ y.2.2.2 = true |
      lazyAimedBoundaryRun prims K circuits settings top tree D A x z Z] ≤
      (((start + (3 * (ceremonyFuel circuits settings - 2) + 2) * step + 3 * final) * prssKeyCount C +
        4 * prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

omit [Fintype E] [DecidableEq E] in
/-- Part 2 of the hits from the secrecy stage. -/
theorem treeKeyAfterHitBound_of_aimed (hAimed : TreeKeyAimedBound prims K circuits settings) :
    TreeKeyAfterHitBound prims K circuits settings := by
  intro hb top tree D A x z Z start step final hx hstart hround hfinal
  refine (probEvent_afterHit_le_aimed prims K circuits settings top tree D A x z Z).trans ?_
  rw [probEvent_aimed_eq_lazy]
  exact hAimed hb top tree D A x z Z start step final hx hstart hround hfinal

/-- `TreeSecurityStatement` from the simulation hop and the secrecy stage. -/
theorem treeSecurityOfSimAimed (hAimed : TreeKeyAimedBound prims K circuits settings)
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityOfSimOnly prims K circuits settings (treeKeyAfterHitBound_of_aimed prims K circuits settings hAimed) hSim

end AfterStages

/-- info: 'ThresholdLeanXmssSecurity.treeKeyAfterHitBound_of_aimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeKeyAfterHitBound_of_aimed

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityOfSimAimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityOfSimAimed

end ThresholdLeanXmssSecurity
