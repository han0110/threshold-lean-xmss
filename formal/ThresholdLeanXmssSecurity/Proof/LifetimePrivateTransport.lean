import ThresholdLeanXmssSecurity.Proof.LifetimeMasks

/-!
# Signing with private pair masks

Splitting the honest-pair mask cells commutes with signing requests whose PRF inputs are
already cached. The transport retains the answer, signing state, private mask table and
public cache. Injective pair keys distinguish private cells from all known-pair inputs.

The relation holds on every extension of the initial cache, so sequential masks and the
public codeword search compose. Cached PRF evaluations keep their values, while each mask
updates exactly one side of the split. The request proof follows the same authorization
and memoized-tree branches on both sides.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

set_option maxHeartbeats 1000000

namespace ThresholdLeanXmssSecurity.LifetimeMasks

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Run the private table and public oracle with a common association of their states. -/
def privateRun {α : Type} (prims : Primitives) {D : C.Coalition}
    (m : MaskM D α) (c : MaskCache D) (g : HashCache C) :
    ProbComp (α × MaskCache D × HashCache C) :=
  (fun r => (r.1.1, r.1.2, r.2)) <$>
    (simulateQ (localAnswer prims) (m.run c)).run g

theorem privateRun_pure {α : Type} (prims : Primitives) {D : C.Coalition}
    (a : α) (c : MaskCache D) (g : HashCache C) :
    privateRun prims (pure a) c g = pure (a, c, g) := by
  simp [privateRun, StateT.run_pure]

theorem privateRun_bind {α β : Type} (prims : Primitives) {D : C.Coalition}
    (m : MaskM D α) (k : α → MaskM D β) (c : MaskCache D) (g : HashCache C) :
    privateRun prims (m >>= k) c g =
      privateRun prims m c g >>= fun r => privateRun prims (k r.1) r.2.1 r.2.2 := by
  simp only [privateRun, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

theorem privateRun_lift {α : Type} (prims : Primitives) {D : C.Coalition}
    (m : OracleComp (RoSpec C) α) (c : MaskCache D) (g : HashCache C) :
    privateRun prims (StateT.lift (liftComp m (LocalSpec C))) c g =
      (fun r => (r.1, c, r.2)) <$> (simulateQ (roImpl prims) m).run g := by
  simp only [privateRun, StateT.run_lift, bind_pure_comp, simulateQ_map,
    simulateQ_localAnswer_liftComp, StateT.run_map, Functor.map_map]
  rfl

/-- Equality of the answer and split cache from every extension of a fixed initial cache. -/
def Transport {α : Type} (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (s : HashCache C)
    (m : OracleComp (RoSpec C) α) (n : MaskM D α) : Prop :=
  ∀ g, s ≤ g →
    Prod.map id (splitMasks D keys) <$> (simulateQ (roImpl prims) m).run g =
      privateRun prims n (splitMasks D keys g).1 (splitMasks D keys g).2

theorem transport_pure {α : Type} (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (s : HashCache C) (a : α) :
    Transport prims D keys s (pure a) (pure a) := by
  intro g _
  simp [privateRun_pure]

theorem Transport.bind {α β : Type} {prims : Primitives} {D : C.Coalition}
    {keys : C.Pair → HashOutput} {s : HashCache C}
    {m : OracleComp (RoSpec C) α} {n : MaskM D α}
    {k : α → OracleComp (RoSpec C) β} {l : α → MaskM D β}
    (h : Transport prims D keys s m n) (hk : ∀ a, Transport prims D keys s (k a) (l a)) :
    Transport prims D keys s (m >>= k) (n >>= l) := by
  intro g hg
  rw [simulateQ_bind, StateT.run_bind, map_bind, privateRun_bind, ← h g hg,
    bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro r hr
  exact hk r.1 r.2 (hg.trans (roRun_support prims m g r hr).1)

theorem Transport.map {α β : Type} {prims : Primitives} {D : C.Coalition}
    {keys : C.Pair → HashOutput} {s : HashCache C}
    {m : OracleComp (RoSpec C) α} {n : MaskM D α}
    (h : Transport prims D keys s m n) (f : α → β) :
    Transport prims D keys s (f <$> m) (f <$> n) := by
  simpa only [bind_pure_comp] using h.bind (fun a => transport_pure prims D keys s (f a))

theorem transport_mapM {α β : Type} {prims : Primitives} {D : C.Coalition}
    {keys : C.Pair → HashOutput} {s : HashCache C}
    (f : α → OracleComp (RoSpec C) β) (g : α → MaskM D β) :
    ∀ xs : List α, (∀ a ∈ xs, Transport prims D keys s (f a) (g a)) →
      Transport prims D keys s (xs.mapM f) (xs.mapM g)
  | [], _ => transport_pure prims D keys s []
  | a :: xs, h => by
    rw [List.mapM_cons, List.mapM_cons]
    exact (h a (by simp)).bind fun b =>
      (transport_mapM f g xs fun a ha => h a (by simp [ha])).bind fun bs =>
        transport_pure prims D keys s (b :: bs)

theorem transport_steady {α : Type} {prims : Primitives} {D : C.Coalition}
    {keys : C.Pair → HashOutput} {s : HashCache C}
    {m : OracleComp (RoSpec C) α} {a : α}
    (h : Steady s (simulateQ (roImpl prims) m) a) :
    Transport prims D keys s m (pure a) := by
  intro g hg
  rw [h g hg, map_pure, privateRun_pure]
  rfl

theorem splitMasks_update_public (D : C.Coalition) (keys : C.Pair → HashOutput)
    (g : HashCache C) (q : Query C) (v : HashOutput)
    (hq : ∀ s, maskInput D keys s ≠ q) :
    splitMasks D keys (g.cacheQuery q v) =
      ((splitMasks D keys g).1, (splitMasks D keys g).2.cacheQuery q v) := by
  apply Prod.ext
  · funext s
    exact QueryCache.cacheQuery_of_ne _ _ (hq s)
  · funext u
    by_cases hu : u = q
    · subst u
      rw [splitMasks_public D keys _ _ hq]
      simp
    · simp only [splitMasks, QueryCache.cacheQuery_of_ne _ _ hu]

theorem transport_hashQuery (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (s : HashCache C) (q : Query C)
    (hq : ∀ slot, maskInput D keys slot ≠ q) :
    Transport prims D keys s (hashQuery q)
      (StateT.lift (liftComp (hashQuery q) (LocalSpec C))) := by
  intro g _
  rw [privateRun_lift]
  have hquery : simulateQ (roImpl prims) (hashQuery q) = hashAnswer prims q := by
    simp [hashQuery, roImpl]
  rw [hquery]
  have hcache := splitMasks_public D keys g q hq
  by_cases hfixed : IsFixed q
  · obtain ⟨input, rfl, hfixed⟩ := hfixed
    rw [hashAnswer_of_isFixed prims hfixed]
    simp only [StateT.run_pure, map_pure]
    rfl
  · rw [hashAnswer_of_not_isFixed prims hfixed]
    cases hg : g _ with
    | some v =>
      rw [QueryImpl.withCaching_run_some _ hg,
        QueryImpl.withCaching_run_some _ (hcache.trans hg)]
      simp only [map_pure, Prod.map_apply, id_eq]
    | none =>
      rw [QueryImpl.withCaching_run_none _ hg,
        QueryImpl.withCaching_run_none _ (hcache.trans hg)]
      simp only [Functor.map_map, Prod.map_apply, id_eq,
        splitMasks_update_public D keys g _ _ hq]

theorem transport_pairMask (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (hinj : Function.Injective keys) (s : HashCache C)
    (p : C.Pair) (x : Point) (message : Message) (J : C.Quorum) :
    Transport prims D keys s (truncateHash <$> hashQuery (.mask (keys p) x message J))
      (pairMask D (fun p => keys p.1) p x message J) := by
  by_cases hp : KeygenHiddenPair D p
  · rw [pairMask_hidden D _ p hp]
    apply Transport.map
    intro g _
    have hquery : simulateQ (roImpl prims) (hashQuery (.mask (keys p) x message J)) =
        hashAnswer prims (.mask (keys p) x message J) := by simp [hashQuery, roImpl]
    rw [hquery]
    exact privateMask_real_run prims D keys hinj (⟨p, hp⟩, x, message, J) g
  · rw [pairMask_known D _ p hp]
    have h := (transport_hashQuery prims D keys s (.mask (keys p) x message J) ?_).map truncateHash
    · exact h
    · intro slot heq
      exact hp (hinj (Query.mask.inj heq).1 ▸ slot.1.2)

theorem transport_eval (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (hinj : Function.Injective keys) (s : HashCache C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (term : C.Term → Point → Digest) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message)
    (hs : PrfValueCached s seeds x) (ht : ∀ T, term T x = cachedPrf s (seeds T) x) :
    Transport prims D keys s (eval (dealtKeys parameter seeds keys i) i J x message)
      (privateEval D (fun p => keys p.1) term i J x message) := by
  have hterms : Steady s
      (simulateQ (roImpl prims) ((C.terms.filter (· ∈ L J i)).mapM
        fun T => prf ((dealtKeys parameter seeds keys i).seed T) x))
      ((C.terms.filter (· ∈ L J i)).map fun T => term T x) := by
    rw [simulateQ_list_mapM]
    apply steady_mapM
    intro T hT
    have hmem := List.mem_filter.mp hT
    have hholder := TprfCorrectnessProof.mem_holders_of_mem_L (of_decide_eq_true hmem.2)
    simp only [dealtKeys, if_pos hholder, ht T]
    exact steady_prf (hs T hmem.1)
  unfold eval privateEval
  have h := transport_steady (D := D) (keys := keys) hterms
  suffices hh : Transport prims D keys s _ (pure ((C.terms.filter (· ∈ L J i)).map
      fun T => term T x) >>= fun terms =>
        (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).mapM (fun j =>
          if h : j = i then pure 0 else
            pairMask D (fun p => keys p.1) (C.pairOf i j (Ne.symm h)) x message J) >>=
        fun masks => pure ((terms ++ masks).foldl (· ^^^ ·) 0)) by
    simpa only [pure_bind] using hh
  apply h.bind
  intro terms
  apply (transport_mapM _ _ _ ?_).bind
  · intro masks
    exact transport_pure prims D keys s _
  · intro j hj
    have hne : j ≠ i := (of_decide_eq_true (List.mem_filter.mp hj).2).2
    simp only [dealtKeys, dif_neg hne]
    exact transport_pairMask prims D keys hinj s (C.pairOf i j (Ne.symm hne)) x message J

theorem maskLift_pure {α : Type} (D : C.Coalition) (a : α) :
    (StateT.lift (pure a) : MaskM D α) = pure a := by
  ext c
  simp [StateT.run_lift]

theorem maskLift_bind {α β : Type} (D : C.Coalition)
    (m : OracleComp (LocalSpec C) α) (k : α → OracleComp (LocalSpec C) β) :
    (StateT.lift (m >>= k) : MaskM D β) =
      StateT.lift m >>= fun a => StateT.lift (k a) := by
  ext c
  simp [StateT.run_lift, StateT.run_bind]

theorem transport_tweakable {α : Type} (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (s : HashCache C) (m : OracleComp HashSpec α) :
    Transport prims D keys s (tweakable m)
      (StateT.lift (liftComp (tweakable (C := C) m) (LocalSpec C))) := by
  induction m using OracleComp.inductionOn with
  | pure a =>
    simpa only [tweakable_pure, liftComp_pure, maskLift_pure] using
      transport_pure prims D keys s a
  | query_bind q k ih =>
    rw [tweakable_bind, liftComp_bind, maskLift_bind]
    apply Transport.bind
    · simpa only [tweakable, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map] using
        transport_hashQuery prims D keys s (.hash q) (fun slot h => by cases h)
    · exact ih

theorem transport_sequenceFin {α : Type} {prims : Primitives} {D : C.Coalition}
    {keys : C.Pair → HashOutput} {s : HashCache C} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α) (g : Fin n → MaskM D α),
      (∀ i, Transport prims D keys s (f i) (g i)) →
      Transport prims D keys s (Concrete.sequenceFin f) (Concrete.sequenceFin g)
  | 0, _, _, _ => transport_pure prims D keys s _
  | n + 1, f, g, h =>
    (h 0).bind fun a => (transport_sequenceFin (fun i => f i.succ)
      (fun i => g i.succ) (fun i => h i.succ)).bind fun rest =>
      transport_pure prims D keys s (Fin.cases a rest : Fin (n + 1) → α)

theorem transport_signRound2With (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (s : HashCache C)
    (part : Point → OracleComp (RoSpec C) Digest) (privatePart : Point → MaskM D Digest)
    (parameter : PublicParameter) (J : C.Quorum) (commitment : Digest)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest)
    (h : ∀ l (p : Digit), p.val < chainLength - 1 →
      Transport prims D keys s (part (.chain bottomLayer e l p))
        (privatePart (.chain bottomLayer e l p))) :
    Transport prims D keys s
      (signRound2With (fun oa => oa) part parameter J commitment e message parts)
      (signRound2With (fun oa => StateT.lift (liftComp oa (LocalSpec C)))
        privatePart parameter J commitment e message parts) := by
  unfold signRound2With
  apply Transport.bind
  · unfold signCodeword
    exact transport_tweakable prims D keys s _
  · rintro (_ | ⟨randomness, encoding⟩)
    · exact transport_pure prims D keys s none
    · apply Transport.bind
      · apply transport_sequenceFin
        intro l
        split_ifs with hp
        · exact (h l _ hp).map some
        · exact transport_pure prims D keys s none
      · intro values
        exact transport_pure prims D keys s (some values)

theorem bottomOnce_pure_run {m : Type → Type} [Monad m] [LawfulMonad m]
    (dealt : Dealt C m) (b : Fin (2 ^ layerHeight)) (tree : Option BottomTree)
    (h : dealt.bottom b = pure tree) (st : TsigState C) :
    (bottomOnce dealt b).run st = pure (match st.trees b with
      | some stored => (stored, st)
      | none => (tree, { st with trees := Function.update st.trees b (some tree) })) := by
  unfold bottomOnce
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.trees b <;>
    simp [h, liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_pure]

theorem transport_tsigOracles (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (s : HashCache C)
    (realDealt : Dealt C (OracleComp (RoSpec C))) (privateDealt : Dealt C (MaskM D))
    (hparameter : realDealt.parameter = privateDealt.parameter)
    (htrees : ∀ b, ∃ tree, realDealt.bottom b = pure tree ∧ privateDealt.bottom b = pure tree)
    (q : TsigQuery C) (st : TsigState C) (hq : ∀ i, q ≠ .corrupt i)
    (hvalue : ∀ x, RequestPoint q x →
      Transport prims D keys s (realDealt.value x) (privateDealt.value x))
    (hpart : ∀ i J x message, RequestPoint q x →
      Transport prims D keys s (realDealt.part i J x message)
        (privateDealt.part i J x message)) :
    Transport prims D keys s
      ((tsigOracles (fun oa => oa) realDealt q).run st)
      ((tsigOracles (fun oa => StateT.lift (liftComp oa (LocalSpec C))) privateDealt q).run st) := by
  cases q with
  | corrupt i => exact (hq i rfl).elim
  | tree b =>
    obtain ⟨tree, ht₁, ht₂⟩ := htrees b
    simp only [tsigOracles, StateT.run_bind, bottomOnce_pure_run realDealt b tree ht₁,
      bottomOnce_pure_run privateDealt b tree ht₂, pure_bind]
    generalize (match st.trees b with
      | some stored => (stored, st)
      | none => (tree, { st with trees := Function.update st.trees b (some tree) })) = found
    rcases found with ⟨_ | tree, st'⟩
    · exact transport_pure prims D keys s _
    · simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_map,
        StateT.run_lift, bind_pure_comp, Functor.map_map]
      exact (hvalue _ rfl).map _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact transport_pure prims D keys s _
    · simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_bind,
        StateT.run_lift, StateT.run_set, StateT.run_map, pure_bind,
        bind_pure_comp, Functor.map_map]
      exact (hpart i J _ message rfl).map _
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · exact transport_pure prims D keys s _
    · obtain ⟨tree, ht₁, ht₂⟩ := htrees (treeOf e)
      simp only [StateT.run_bind, bottomOnce_pure_run realDealt _ tree ht₁,
        bottomOnce_pure_run privateDealt _ tree ht₂, pure_bind, hparameter]
      generalize (match st.trees (treeOf e) with
        | some stored => (stored, st)
        | none => (tree, { st with trees := Function.update st.trees (treeOf e) (some tree) })) = found
      rcases found with ⟨_ | tree, st'⟩
      · exact transport_pure prims D keys s _
      · simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_bind,
          StateT.run_lift, bind_assoc, pure_bind]
        apply (hpart i J _ message (.inl rfl)).bind
        intro own
        apply (transport_signRound2With prims D keys s _ _ _ _ _ _ _ _
          (fun l p hp => hpart i J _ message (.inr ⟨l, p, hp, rfl⟩))).bind
        intro result
        cases result <;>
          simp only [StateT.run_pure, StateT.run_modify, StateT.run_bind, pure_bind] <;>
          exact transport_pure prims D keys s _

/-- The lifetime dealer before the honest-world embedding. -/
def roSignerDealt (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (keys : C.Pair → HashOutput) (top : TopTree)
    (trees : Fin (2 ^ layerHeight) → Option BottomTree) : Dealt C (OracleComp (RoSpec C)) :=
  { dealtWith (fun oa => oa) parameter (dealtKeys parameter seeds keys) top (prfValue seeds) with
    bottom := fun b => pure (trees b) }

theorem signerDealt_simulate (prims : Primitives) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (keys : C.Pair → HashOutput) (top : TopTree)
    (trees : Fin (2 ^ layerHeight) → Option BottomTree) (q : TsigQuery C) (st : TsigState C) :
    simulateQ (worldAnswer prims)
      ((tsigOracles SigningCoreProof.honestLift
        (signerDealt parameter (dealtKeys parameter seeds keys) top trees seeds) q).run st) =
    simulateQ (roImpl prims)
      ((tsigOracles (fun oa => oa) (roSignerDealt parameter seeds keys top trees) q).run st) := by
  have h₁ := SeedHitProof.hom_tsigOracles (simulateQ' (worldAnswer prims))
    SigningCoreProof.honestLift (signerDealt parameter (dealtKeys parameter seeds keys) top trees seeds) q st
  have h₂ := SeedHitProof.hom_tsigOracles (simulateQ' (roImpl prims))
    (fun oa => oa) (roSignerDealt parameter seeds keys top trees) q st
  simp only [simulateQ'] at h₁ h₂
  rw [h₁, h₂]
  simp only [simulateQ_worldAnswer_honestLift, SeedHitProof.Dealt.hmap,
    signerDealt, roSignerDealt, dealtWith, simulateQ_pure]

/-- The private service transports the complete signing request and both resulting caches. -/
theorem privateSigningTransport : PrivateSigningTransport (C := C) := by
  intro prims D keys hinj parameter seeds top trees value term q st g hq hcached
  rw [signerDealt_simulate]
  have h : Transport prims D keys g
      ((tsigOracles (fun oa => oa) (roSignerDealt parameter seeds keys top trees) q).run st)
      ((privateOracles D (fun p => keys p.1) parameter top trees value term q).run st) := by
    apply transport_tsigOracles
    · rfl
    · exact fun b => ⟨trees b, rfl, rfl⟩
    · exact hq
    · intro x hx
      change Transport prims D keys g (prfValue seeds x) (pure (value x))
      rw [(hcached x hx).2.1]
      exact transport_steady (steady_prfValue (hcached x hx).1)
    · intro i J x message hx
      exact transport_eval prims D keys hinj g parameter seeds term i J x message
        (hcached x hx).1 (hcached x hx).2.2
  exact h g le_rfl

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.transport_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transport_eval

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.privateSigningTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms privateSigningTransport

end ThresholdLeanXmssSecurity.LifetimeMasks
