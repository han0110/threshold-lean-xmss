import ThresholdLeanXmssSecurity.Proof.PrssRealRand.ViewLaw

/-!
# The coupling of the ideal joint world with the logged setup run and `flagZ`

`prssRealRand_coupling` is the first premise of `prssRealRand_key`. In the ideal joint world, the
event `UsedHit` of the real game has at most the probability that the logged setup run with `flagZ`
accepts.

`viewGame` is the real game in its normal form with the log of the adversary and the log of `Z`. It
gives the view of the flag and the bit of `Z`. The proof has four steps.

1. `viewGame_erase` states that the real game is `viewGame` without its view.
2. `viewGame_usedHit` states that on each final state of `viewGame` in the ideal joint world, `UsedHit`
   gives `KeyFlag` on the view. It uses `keyFlag_of_usedHit` and the provenance facts.
3. `viewGame_keyWorldView` states that the view of `viewGame` in the ideal joint world has the law
   `keyWorldView`.
4. `viewLaw` gives the law of `keyWorldView`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Program

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The real game in its normal form, with the log of the adversary and the log of `Z`. It gives the
view of the flag and the bit of `Z`. The view has no hashes of the known keys, because `KeyFlag` does
not read them. -/
def viewGame (label : ℕ) (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E))) :
    OracleComp (WorldSpec C) (FlagView C × Bool) := do
  let r ← setupRun D (logAdversary A) x z
  let streams ← free (liveStreams K prgBits D r.2 label calls)
  let p ← worldRoles.adversary ((simulateQ logImpl (Z (r.1.1, streams))).run [])
  pure (⟨r.1.2, r.2, liveKnownKeys D r.2, [], p.2⟩, p.1)

end Program

section Facts

variable {C : Committee}

/-- On one final state of the ideal joint world and one view, `UsedHit` gives `KeyFlag`. The premises
are the invariant of the joint world and the provenance of the private answers and of the stream-key
cells. -/
theorem keyFlag_of_usedHit (D : C.Coalition) (s : KeyJointState C) (v : FlagView C) (hinv : FreeInv D s)
    (hkeys : ∀ n k, s.keys (n, k) ≠ none → HiddenKey D v.out n k)
    (hcells : ∀ k, s.hash (.streamKey k) ≠ none → k ∈ v.log ∨ k ∈ v.known ∨ k ∈ v.zlog)
    (h : UsedHit D s) : KeyFlag D v := by
  rcases h with ⟨k, n, hu, hc⟩ | ⟨n, n', k, -, -, hne, h1, h2⟩
  · have hk := hkeys n k (hinv.1 k n hu).2
    rcases hcells k hc with h' | h' | h'
    · exact ⟨n, k, hk, Or.inl h'⟩
    · exact ⟨n, k, hk, Or.inr (Or.inl h')⟩
    · exact ⟨n, k, hk, Or.inr (Or.inr (Or.inl h'))⟩
  · exact ⟨n, k, hkeys n k h1, Or.inr (Or.inr (Or.inr ⟨n', hne.symm, hkeys n' k h2⟩))⟩

end Facts

section KeyWorld

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

theorem keyWorld_apply_of_not (g : KeyName C × HashOutput → Digest) (t : (WorldSpec C).Domain)
    (ht : ¬ FreeHiddenStream D t) : keyWorld prims D g t = worldAnswer prims t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals try rfl
  simp only [FreeHiddenStream] at ht
  simp only [keyWorld, ht, ↓reduceIte]
  rfl

/-- A computation with no free stream call under a hidden name runs in the world with independent AES
keys as in the ordinary world. -/
theorem keyWorld_run_of_noHidden {α : Type} (g : KeyName C × HashOutput → Digest) (oa : OracleComp (WorldSpec C) α)
    (hoa : IsQueryBoundP oa (FreeHiddenStream D) 0) :
    simulateQ (keyWorld prims D g) oa = simulateQ (worldAnswer prims) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeHiddenStream D t := hoa.1.resolve_right (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (FreeHiddenStream D) 0 := fun u => by
      simpa only [ht, ↓reduceIte] using hoa.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      keyWorld_apply_of_not prims D g t ht]
    exact bind_congr fun u => ih u (hk u)

/-- The result of a computation in the ideal joint world from the initial state has the law of its
result in the world with an eager table of independent AES keys. -/
theorem jointKeyWorld_false_keyWorld {α : Type} (game : OracleComp (WorldSpec C) α) :
    (simulateQ (jointKeyWorld prims D false) game).run' keyJointInitial =ᵈ
      (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g => (simulateQ (keyWorld prims D g) game).run' ∅) := by
  have h := evalDist_lazyKeyWorld prims D game ∅ ∅
  simp only [tableExtending_empty] at h
  exact (jointKeyWorld_false_projection prims D game keyJointInitial).trans h

end KeyWorld

section Coupling

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (prims : Primitives)

/-- The real game is `viewGame` without its view. -/
theorem viewGame_erase (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    Prod.snd <$> viewGame K label calls D A x z Z = prssRealRandGame K label calls D A x z Z := by
  refine Eq.trans ?_ (distinguish_prssRealRand K label calls D A x z Z).symm
  have hE := logAdversaryErase D A x z
  simp only [setupRun] at hE
  rw [← hE]
  simp only [viewGame, setupRun, map_bind, map_pure, bind_map_left]
  refine bind_congr fun r => bind_congr fun streams => ?_
  conv_rhs => rw [← fst_map_run_logImpl (Z (r.1.1, streams)) [], worldRoles_adversary_map]
  rw [map_eq_bind_pure_comp]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- On each final state of `viewGame` in the ideal joint world, `UsedHit` gives `KeyFlag` on the
view. -/
theorem viewGame_usedHit (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) (viewGame K label calls D A x z Z)).run
        keyJointInitial), UsedHit D r.2 → KeyFlag D r.1.1 := by
  intro r hr
  have hinv := (jointKeyWorld_false_run_inv prims D _ keyJointInitial (freeInv_initial D) r hr).1
  simp only [viewGame, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
    support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hr
  obtain ⟨hSk, hSc⟩ := setupProvenance prims D A x z a ha
  obtain ⟨hLk, hLc⟩ := liveStreamsProvenance K prims label calls D a.1.2 a.2 b hb
  obtain ⟨hZk, hZc⟩ := loggedProvenance prims D _ _ [] b.2 c hc
  refine keyFlag_of_usedHit D _ _ hinv (fun n k hk => ?_) (fun k hk => ?_)
  · rw [hZk] at hk
    exact (hLk n k hk).resolve_left fun h => h (hSk _)
  · rcases hZc k hk with h | h
    · rcases hLc k h with h | h
      · exact Or.inl (hSc k h)
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

omit [Fintype E] [DecidableEq E] in
/-- The view of `viewGame` in the ideal joint world has the law `keyWorldView`. -/
theorem viewGame_keyWorldView (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    (fun r : FlagView C × Bool => r.1) <$>
        (simulateQ (jointKeyWorld prims D false) (viewGame K label calls D A x z Z)).run' keyJointInitial =ᵈ
      keyWorldView K prims label calls D A x z Z := by
  have heq : (fun r : FlagView C × Bool => r.1) <$> (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
      (simulateQ (keyWorld prims D g) (viewGame K label calls D A x z Z)).run' ∅) =
      keyWorldView K prims label calls D A x z Z := by
    unfold keyWorldView
    rw [map_bind]
    refine bind_congr fun g => ?_
    simp only [viewGame, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
      map_bind, map_pure, keyWorld_run_of_noHidden prims D g _ (setupNoHidden D (logAdversary A) x z),
      keyWorld_run_of_noHidden prims D g _ (isQueryBoundP_adversary_noHidden D _ 0), bind_map_left]
  rw [← heq]
  exact (jointKeyWorld_false_keyWorld prims D (viewGame K label calls D A x z Z)).map
    (fun r : FlagView C × Bool => r.1)

/-- The coupling of the ideal joint world with the logged setup run and `flagZ`. In the ideal joint
world, `UsedHit` at the end of the real game has at most the probability that the logged setup run with
`flagZ` accepts. It is the first premise of `prssRealRand_key`. -/
theorem prssRealRand_coupling (label : ℕ) (calls : List RandCall) :
    ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) x z Z,
      (Pr{let r ← (simulateQ (jointKeyWorld prims D false) (prssRealRandGame K label calls D A x z Z)).run keyJointInitial}[
          UsedHit D r.2]).toReal ≤
        accepts prims (distinguish (realExecution D (logAdversary A) noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
            (flagZ K prims D label calls A Z (keyFlag D))) := by
  intro D A x z Z
  have hleft :
      Pr{let r ← (simulateQ (jointKeyWorld prims D false)
                    (prssRealRandGame K label calls D A x z Z)).run keyJointInitial}[UsedHit D r.2] =
        Pr{let r ← (simulateQ (jointKeyWorld prims D false)
                      (viewGame K label calls D A x z Z)).run keyJointInitial}[UsedHit D r.2] := by
    rw [← viewGame_erase K label calls D A x z Z, simulateQ_map, StateT.run_map, prEvent_map]
  have hle :
      Pr{let r ← (simulateQ (jointKeyWorld prims D false)
                    (viewGame K label calls D A x z Z)).run keyJointInitial}[UsedHit D r.2] ≤
        Pr{let r ← (simulateQ (jointKeyWorld prims D false)
                      (viewGame K label calls D A x z Z)).run keyJointInitial}[KeyFlag D r.1.1] :=
    prEvent_mono_of_support _ _ _ (viewGame_usedHit K prims label calls D A x z Z)
  have hright :
      Pr{let r ← (simulateQ (jointKeyWorld prims D false)
                    (viewGame K label calls D A x z Z)).run keyJointInitial}[KeyFlag D r.1.1] =
        Pr{let v ← keyWorldView K prims label calls D A x z Z}[KeyFlag D v] := by
    rw [← (viewGame_keyWorldView K prims label calls D A x z Z).prEvent_eq (KeyFlag D), StateT.run'_eq,
      Functor.map_map, prEvent_map]
  rw [hleft]
  exact (ENNReal.toReal_mono (prEvent_ne_top _) (hle.trans_eq hright)).trans_eq (viewLaw K prims label calls D A x z Z)

end Coupling

end ThresholdLeanXmssSecurity
