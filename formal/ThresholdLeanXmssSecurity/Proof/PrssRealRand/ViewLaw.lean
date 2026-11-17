import ThresholdLeanXmssSecurity.Proof.PrssRealRand.Provenance
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.View
import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Observation

/-!
# The law of the view of the flag in the world with independent AES keys

`keyWorldView` is the view of the flag when the draws of the live honest operators read a table `g` of
AES keys under each hidden name. Its law is the law of the view of `flagZ`.

* `keyWorldFree` gives the free calls in the world with independent AES keys as the local calls under
  `keySubst`.
* `liveStreamsObsEq` is the lazy sampling step (BR93) in local form. For each table `g`, the draws with
  the hidden streams from `g` are the same for every observer as the hashes of the known keys and then
  the outputs of `flagZ`.
* `viewLocalLaw` is the law in the local oracles, and `viewLaw` is the law of `keyWorldView`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section KeyWorld

variable {C : Committee} (prims : Primitives)

/-- The local calls with each stream under a hidden name answered from the table `g` of AES keys. -/
def keySubst (D : C.Coalition) (g : KeyName C × HashOutput → Digest) :
    QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inr x) => if Hidden D x.1 then pure (prims.aes.eval (g (x.1, x.2.1)) x.2.2)
      else OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))
  | t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)

/-- One free call in the world with independent AES keys is the call under `keySubst` in the local
oracles. -/
theorem keyWorld_inr (D : C.Coalition) (g : KeyName C × HashOutput → Digest) (t : (LocalSpec C).Domain) :
    keyWorld prims D g (.inr t) = simulateQ (localAnswer prims) (keySubst prims D g t) := by
  rcases t with n | q | x <;> simp [keyWorld, keySubst]

/-- A free computation in the world with independent AES keys is the computation under `keySubst` in
the local oracles. -/
theorem keyWorldFree : ∀ (D : C.Coalition) (g : KeyName C × HashOutput → Digest) (β : Type)
    (ob : OracleComp (LocalSpec C) β),
    simulateQ (keyWorld prims D g) (free ob) = simulateQ (localAnswer prims) (simulateQ (keySubst prims D g) ob) := by
  intro D g β ob
  induction ob using OracleComp.inductionOn with
  | pure a => simp only [free_pure, simulateQ_pure]
  | query_bind t k ih =>
    simp only [free_bind, simulateQ_bind, ih]
    congr 1
    simp [free, keyWorld_inr]

end KeyWorld

section Local

variable {C : Committee} {E : Type}

/-- The setup run in the local oracles. It is `setupLocalGame` before its distinguisher. -/
def setupLocal (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) := do
  let state ← A.start (corruptInputs D x) z
  let steps ← startSteps localRoles D fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
  executeRounds localRoles D A noFunctionality setupRounds state steps

/-- The setup run in the ordinary world is the setup run in the local oracles. -/
theorem setupRun_local (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    simulateQ (worldAnswer prims) (setupRun D A x z) = simulateQ (localAnswer prims) (setupLocal D A x z) := by
  simp only [setupRun, setupLocal, realExecution, executePhase, simulateQ_bind, simulateQ_world_adversary,
    simulateQ_startSteps_real, simulateQ_executeRounds_real, seedGenMapRoles_world]

/-- The local game of the setup is `setupLocal` and then its distinguisher. -/
theorem setupLocalGame_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z' : Distinguisher C A.State (Keys C)) :
    setupLocalGame .prss D A x z Z' = setupLocal D A x z >>= Z' := by
  simp only [setupLocalGame, setupLocal, bind_assoc]

variable [Field E] [Algebra Bit E] (K : Constants C E) (prims : Primitives)

/-- The view of the flag in the world with independent AES keys. The table `g` of AES keys is sampled
first. The setup and `Z` run in the ordinary world, and the draws of the live honest operators read `g`
under each hidden name. -/
def keyWorldView (label : ℕ) (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E))) :
    ProbComp (FlagView C) :=
  ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g => do
    let a ← (simulateQ (worldAnswer prims) (setupRun D (logAdversary A) x z)).run ∅
    let b ← (simulateQ (keyWorld prims D g) (free (liveStreams K prgBits D a.1.2 label calls))).run a.2
    let c ← (simulateQ (worldAnswer prims)
      (worldRoles.adversary ((simulateQ logImpl (Z (a.1.1.1, b.1))).run []))).run' b.2
    pure ⟨a.1.1.2, a.1.2, liveKnownKeys D a.1.2, [], c.2⟩

/-- The view of the flag in the local oracles, with each stream under a hidden name answered from the
table `g` of AES keys. -/
def viewLocal (label : ℕ) (calls : List RandCall) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (List (RandOutput C E)))
    (g : KeyName C × HashOutput → Digest) : OracleComp (LocalSpec C) (FlagView C) := do
  let r ← setupLocal D (logAdversary A) x z
  let streams ← simulateQ (keySubst prims D g) (liveStreams K prgBits D r.2 label calls)
  let p ← (simulateQ logImpl (Z (r.1.1, streams))).run []
  pure ⟨r.1.2, r.2, liveKnownKeys D r.2, [], p.2⟩

/-- `keyWorldView` in the local oracles. -/
theorem keyWorldView_local (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    keyWorldView K prims label calls D A x z Z =
      (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
        (simulateQ (localAnswer prims) (viewLocal K prims label calls D A x z Z g)).run' ∅) := by
  unfold keyWorldView viewLocal
  refine bind_congr fun g => ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind,
    map_pure, setupRun_local, keyWorldFree prims D g, simulateQ_world_adversary, bind_map_left]

/-- `flagZ` is the hashes of the known keys, the sample of the table of AES keys, and then `Z` on
`flagOutputs`. -/
theorem flagZ_eq (D : C.Coalition) (label : ℕ) (calls : List RandCall) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (List (RandOutput C E))) (flag : FlagView C → Bool)
    (r : (logAdversary A).State × (C.Party → Option (Keys C))) :
    flagZ K prims D label calls A Z flag r = (do
      let hashes ← (liveKnownKeys D r.2).mapM fun k =>
        (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)
      let g ← liftComp ($ᵗ (KeyName C × HashOutput → Digest)) (LocalSpec C)
      let p ← (simulateQ logImpl (Z (r.1.1, flagOutputs K prims label calls D r.2 (liveKnownKeys D r.2) hashes g))).run []
      pure (flag ⟨r.1.2, r.2, liveKnownKeys D r.2, hashes, p.2⟩)) := rfl

end Local

section Draws

variable {C : Committee} (prims : Primitives)

/-- `keySubst` on the oracles of `H` and `PRG`. -/
def keySubstRo (D : C.Coalition) (g : KeyName C × HashOutput → Digest) :
    QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun t =>
  match t with
  | .inr x => if Hidden D x.1 then pure (prims.aes.eval (g (x.1, x.2.1)) x.2.2)
      else query (spec := RoSpec C) (.inr x)
  | .inl q => query (spec := RoSpec C) (.inl q)

/-- `keySubst` on a lifted computation of `H` and `PRG` is `keySubstRo`. -/
theorem keySubst_liftComp (D : C.Coalition) (g : KeyName C × HashOutput → Digest) {α : Type}
    (R : OracleComp (RoSpec C) α) :
    simulateQ (keySubst prims D g) (liftComp R (LocalSpec C)) =
      liftComp (simulateQ (keySubstRo prims D g) R) (LocalSpec C) := by
  induction R using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e, simulateQ_bind, simulateQ_query, simulateQ_bind, liftComp_bind]
    simp only [ih]
    congr 1
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases t with q | x
    · simp only [keySubst, keySubstRo, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      rfl
    · by_cases hx : Hidden D x.1
      · simp [keySubst, keySubstRo, hx]
      · simp [keySubst, keySubstRo, hx]
        rfl

/-- A call of `H`. -/
def HashCall : (RoSpec C).Domain → Prop
  | .inl _ => True
  | .inr _ => False

/-- With `H` fixed, a computation with no call of `H` under `keySubstRo` is the computation under each
`impl` that agrees on its `PRG` calls. -/
theorem fixed_keySubstRo (D : C.Coalition) (g : KeyName C × HashOutput → Digest) (h : Query C → HashOutput)
    (impl : QueryImpl (RoSpec C) Id) (Bad : (RoSpec C).Domain → Prop)
    (hagree : ∀ x : PrgInput C, ¬ Bad (.inr x) →
      ThresholdLeanXmssSecurity.D prims h (keySubstRo prims D g (.inr x)) = impl (.inr x))
    {α : Type} (R : OracleComp (RoSpec C) α) (hR : IsQueryBoundP R Bad 0) (hH : IsQueryBoundP R HashCall 0) :
    ThresholdLeanXmssSecurity.D prims h (simulateQ (keySubstRo prims D g) R) = simulateQ impl R := by
  induction R using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hR hH
    have ht : ThresholdLeanXmssSecurity.D prims h (keySubstRo prims D g t) = impl t := by
      rcases t with q | x
      · exact absurd hH.1 (by simp [HashCall])
      · exact hagree x (by simpa using hR.1)
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, D_bind,
      ht]
    have hb : ¬ Bad t := hR.1.resolve_right (lt_irrefl 0)
    have hc : ¬ HashCall t := hH.1.resolve_right (lt_irrefl 0)
    exact ih _ (by simpa [hb] using hR.2 (impl t)) (by simpa [hc] using hH.2 (impl t))

/-- The lookup of a key in the list of the keys and their values. -/
theorem lookup_zip_map {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) :
    ∀ (l : List α) (k : α), k ∈ l → (l.zip (l.map f)).lookup k = some (f k)
  | [], _, hk => absurd hk List.not_mem_nil
  | a :: l, k, hk => by
    by_cases e : k = a
    · subst e
      simp
    · have hl : k ∈ l := (List.mem_cons.1 hk).resolve_left e
      simp [List.lookup, beq_eq_false_iff_ne.2 e, lookup_zip_map f l k hl]

/-- The hashes of the keys `l` as one lifted computation of `H`. -/
theorem liftComp_mapM_streamKey (l : List HashOutput) :
    liftComp (l.mapM fun k => hashQuery (C := C) (.streamKey k)) (LocalSpec C) =
      l.mapM fun k => (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, ih]
    rfl

end Draws

section ObsEq

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (prims : Primitives)

/-- The draws of the live honest operators as one lifted computation of `H` and `PRG`. -/
theorem liveStreams_liftComp (D : C.Coalition) (out : C.Party → Option (Keys C)) (label : ℕ)
    (calls : List RandCall) :
    liveStreams K prgBits D out label calls = liftComp (OverPermutation.sequenceFin fun j =>
      if j ∈ D.1 then pure none else match out j with
        | some k => some <$> randStreams K prgBits (carrierPrssKeys k) j label calls
        | none => pure none) (LocalSpec C) := by
  unfold liveStreams
  refine Eq.trans ?_ (simulateQ_sequenceFin _ _).symm
  congr 1
  funext j
  split_ifs
  · simp
  · cases out j <;> simp [liftComp]

/-- The lazy sampling step in local form (BR93). For each table `g`, the draws with the hidden streams
from `g` are the same for every observer as the hashes of all known keys and then the outputs of
`flagZ`. The two sides ask `H` at different points, so the caches differ. -/
theorem liveStreamsObsEq : ∀ (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (out : C.Party → Option (Keys C)) (g : KeyName C × HashOutput → Digest),
    ObsEq prims
      (simulateQ (keySubst prims D g) (liveStreams K prgBits D out label calls))
      (((liveKnownKeys D out).mapM fun k =>
          (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)) >>=
        fun hashes => pure (flagOutputs K prims label calls D out (liveKnownKeys D out) hashes g)) := by
  intro label calls D out g
  rw [liveStreams_liftComp, keySubst_liftComp, ← liftComp_mapM_streamKey]
  refine (ObsEq.of_eq (bind_pure _).symm).trans (obsEq_hash prims _ _ _ _ fun h _ => ObsEq.of_eq ?_)
  congr 1
  rw [simulateQ_sequenceFin, D_sequenceFin, D_mapM]
  simp only [D_hashQuery]
  funext j
  unfold flagOutputs
  by_cases hj : j ∈ D.1
  · simp [hj, D_pure]
  · cases hk : out j with
    | none => simp [hj, D_pure]
    | some k =>
      simp only [hj, ite_false, simulateQ_map, D_map, Option.map_some]
      congr 1
      refine fixed_keySubstRo prims D g h _ (fun t => Unallowed (HeldBy D out) (.inr (.inr t))) (fun x hx => ?_) _
        (randStreamsAllowed K label calls D out j k hj hk)
        (isQueryBoundP_randStreams_zero K HashCall _ j (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) label calls)
      obtain ⟨i, ki, hi, hki, hkey⟩ : HeldBy D out x.1 x.2.1 := by simpa [Unallowed, KeyAllowed] using hx
      by_cases hn : Hidden D x.1
      · simp only [keySubstRo, pureStreams, hn, ite_true]
        rfl
      · simp only [keySubstRo, pureStreams, hn, ite_false]
        rw [lookup_zip_map _ _ _ (mem_liveKnownKeys_of_heldKey D out i hi ki hki x.1 hn x.2.1 hkey)]
        rfl

end ObsEq

section Law

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (prims : Primitives)

/-- The law of the view in the local oracles at one list of calls, from the lazy sampling step at that
list. The table `g` moves to the front, past the setup, and in `flagZ` past the hashes of the known
keys. -/
theorem viewLocalLaw_of_obsEq (label : ℕ) (calls : List RandCall)
    (h : ∀ (D : C.Coalition) (out : C.Party → Option (Keys C)) (g : KeyName C × HashOutput → Digest),
      ObsEq prims
        (simulateQ (keySubst prims D g) (liveStreams K prgBits D out label calls))
        (((liveKnownKeys D out).mapM fun k =>
            (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)) >>=
          fun hashes => pure (flagOutputs K prims label calls D out (liveKnownKeys D out) hashes g)))
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    Pr{let v ← (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
                  (simulateQ (localAnswer prims) (viewLocal K prims label calls D A x z Z g)).run' ∅)}[KeyFlag D v] =
      Pr{let y ← (simulateQ (localAnswer prims) (setupLocalGame .prss D (logAdversary A) x z
                    (flagZ K prims D label calls A Z (keyFlag D)))).run' ∅}[y = true] := by
  let W : (logAdversary A).State × (C.Party → Option (Keys C)) → (C.Party → Option (List (RandOutput C E))) →
      OracleComp (LocalSpec C) Bool := fun r streams =>
    (simulateQ logImpl (Z (r.1.1, streams))).run [] >>= fun p =>
      pure (keyFlag D ⟨r.1.2, r.2, liveKnownKeys D r.2, [], p.2⟩)
  let hashes : (logAdversary A).State × (C.Party → Option (Keys C)) → OracleComp (LocalSpec C) (List HashOutput) :=
    fun r => (liveKnownKeys D r.2).mapM fun k =>
      (query (spec := LocalSpec C) (.inr (.inl (.streamKey k))) : OracleComp (LocalSpec C) HashOutput)
  let sample := liftComp ($ᵗ (KeyName C × HashOutput → Digest)) (LocalSpec C)
  have hobs : ObsEq prims (keyFlag D <$> (sample >>= fun g => viewLocal K prims label calls D A x z Z g))
      (setupLocalGame .prss D (logAdversary A) x z (flagZ K prims D label calls A Z (keyFlag D))) := by
    have e1 : keyFlag D <$> (sample >>= fun g => viewLocal K prims label calls D A x z Z g) =
        sample >>= fun g => setupLocal D (logAdversary A) x z >>= fun r =>
          simulateQ (keySubst prims D g) (liveStreams K prgBits D r.2 label calls) >>= W r := by
      simp only [viewLocal, map_bind, map_pure, W]
    have e2 : ∀ r, flagZ K prims D label calls A Z (keyFlag D) r =
        hashes r >>= fun hs => sample >>= fun g =>
          W r (flagOutputs K prims label calls D r.2 (liveKnownKeys D r.2) hs g) := fun r => by
      rw [flagZ_eq]
      rfl
    rw [e1, setupLocalGame_eq]
    refine (SameRun.obsEq (sameRun_swap prims sample (setupLocal D (logAdversary A) x z) _)).trans ?_
    refine ObsEq.bind_right _ fun r => ?_
    rw [e2 r]
    refine ObsEq.trans ?_ (SameRun.obsEq (sameRun_swap prims (hashes r) sample
      fun hs g => W r (flagOutputs K prims label calls D r.2 (liveKnownKeys D r.2) hs g))).symm
    refine ObsEq.bind_right _ fun g => ?_
    have e3 : (hashes r >>= fun hs => W r (flagOutputs K prims label calls D r.2 (liveKnownKeys D r.2) hs g)) =
        (hashes r >>= fun hs => pure (flagOutputs K prims label calls D r.2 (liveKnownKeys D r.2) hs g)) >>= W r := by
      simp only [bind_assoc, pure_bind]
    rw [e3]
    exact (h D r.2 g).bind_left (W r)
  rw [← ObsEq.prob_eq hobs]
  have e : (simulateQ (localAnswer prims) (keyFlag D <$> (sample >>= fun g =>
      viewLocal K prims label calls D A x z Z g))).run' ∅ = keyFlag D <$> (($ᵗ (KeyName C × HashOutput → Digest)) >>=
        fun g => (simulateQ (localAnswer prims) (viewLocal K prims label calls D A x z Z g)).run' ∅) := by
    rw [map_eq_bind_pure_comp, bind_assoc, run'_localAnswer_liftComp_bind, map_bind]
    refine bind_congr fun g => ?_
    rw [← map_eq_bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
      Functor.map_map]
  rw [e, prEvent_map]
  exact prEvent_congr _ _ _ fun v => (decide_eq_true_iff).symm

/-- The law of the view in the local oracles. The view of `viewLocal` has the flag with the probability
that the local game of the setup with `flagZ` accepts. -/
theorem viewLocalLaw : ∀ (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))),
    Pr{let v ← (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
                  (simulateQ (localAnswer prims) (viewLocal K prims label calls D A x z Z g)).run' ∅)}[KeyFlag D v] =
      Pr{let y ← (simulateQ (localAnswer prims) (setupLocalGame .prss D (logAdversary A) x z
                    (flagZ K prims D label calls A Z (keyFlag D)))).run' ∅}[y = true] := fun label calls =>
  viewLocalLaw_of_obsEq K prims label calls (liveStreamsObsEq K prims label calls)

/-- The law of the view. The view in the world with independent AES keys has the flag with the
probability that the run of `flagZ` accepts. -/
theorem viewLaw : ∀ (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))),
    (Pr{let v ← keyWorldView K prims label calls D A x z Z}[KeyFlag D v]).toReal =
      accepts prims (distinguish (setupRun D (logAdversary A) x z) (flagZ K prims D label calls A Z (keyFlag D))) := by
  intro label calls D A x z Z
  rw [keyWorldView_local K prims, ← setupLocalGame_accepts]
  exact congrArg ENNReal.toReal (viewLocalLaw K prims label calls D A x z Z)

end Law

end ThresholdLeanXmssSecurity
