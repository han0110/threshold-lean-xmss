import ThresholdLeanXmssSecurity.Proof.PrssRand
import ThresholdLeanXmssSecurity.Proof.SeedGenSecurity

/-!
# The real PRSS streams with hidden keys

`streamWorld` answers each free stream call under a hidden name from a lazy uniform table. A
computation with no such call runs in `streamWorld` as in `worldAnswer`, and the table stays as it is
(`streamWorld_run_of_noHidden`). `executePhase_free` is the frame of a phase on the real network for
the free calls of a predicate. `probBad_streamKey_le_usedHit` bounds the stream-key event of each game
by the event `UsedHit` at the end of the ideal joint world. `KeysAgree` and `PairKeysAgree` state that
two honest operators with keys hold the same keys, and dealt keys agree (`keysAgree_of_dealt`).
-/

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Free stream calls -/

section Predicate

variable {C : Committee}

/-- A free stream call under a hidden name. -/
def FreeHiddenStream (D : C.Coalition) : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr x)) => Hidden D x.1
  | _ => False

/-- A free call that reads the hash cell of a stream key, namely a free hash of a stream key or a
free `PRG` call. -/
def FreeStreamKey : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inl (.streamKey _))) => True
  | .inr (.inr (.inr _)) => True
  | _ => False

/-- A free stream call under a hidden name reads the hash cell of a stream key. -/
theorem freeStreamKey_of_freeHiddenStream (D : C.Coalition) (t : (WorldSpec C).Domain)
    (h : FreeHiddenStream D t) : FreeStreamKey t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals first | exact h.elim | trivial

/-- The steps of the adversary and of the distinguisher are on the counted copy. So they make no free
call, for each computation. -/
theorem isQueryBoundP_adversary_noStreamKey {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) :
    IsQueryBoundP (worldRoles.adversary oa) (FreeStreamKey (C := C)) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

end Predicate

/-! ## The stream world on a computation with no hidden call -/

section Bridge

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

theorem streamWorld_apply_of_not (t : (WorldSpec C).Domain) (ht : ¬ FreeHiddenStream D t) :
    streamWorld prims D t = onHash (worldAnswer prims t) := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals try rfl
  simp only [FreeHiddenStream] at ht
  simp only [streamWorld, ht, ↓reduceIte]
  rfl

theorem onHash_run {α : Type} (m : StateT (HashCache C) ProbComp α) (h : HashCache C) (hc : HiddenCache C) :
    (onHash m).run (h, hc) = (fun r => (r.1, (r.2, hc))) <$> m.run h := rfl

/-- A computation with no free stream call under a hidden name runs in the stream world as in the
ordinary world, and the hidden table does not change. -/
theorem streamWorld_run_of_noHidden {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hoa : IsQueryBoundP oa (FreeHiddenStream D) 0) (h : HashCache C) (hc : HiddenCache C) :
    (simulateQ (streamWorld prims D) oa).run (h, hc) =
      (fun r => (r.1, (r.2, hc))) <$> (simulateQ (worldAnswer prims) oa).run h := by
  induction oa using OracleComp.inductionOn generalizing h with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeHiddenStream D t := by
      rcases hoa.1 with h' | h'
      · exact h'
      · exact absurd h' (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (FreeHiddenStream D) 0 := fun u => by
      simpa only [ht, ↓reduceIte] using hoa.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, streamWorld_apply_of_not prims D t ht, onHash_run, bind_map_left, map_bind]
    exact bind_congr fun r => ih r.1 (hk r.1) r.2

end Bridge

variable {C : Committee} {E : Type}

/-! ## The frame of a phase -/

section Frame

variable {ι : Type} {G : OracleSpec ι} {α : Type}

/-- A local call of an operator program that is a free call in `Q` on the world. -/
def PartyFree (Q : (WorldSpec C).Domain → Prop) : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => Q (.inr t)
  | _ => False

/-- The rest of a stopped program makes no local call in `Q`. -/
def StepFree (Q : (WorldSpec C).Domain → Prop) : Step C E G α → Prop
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyFree (E := E) (G := G) Q) 0
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyFree (E := E) (G := G) Q) 0

/-- If a continuation makes no call in `Q` on each value in `S`, then `oa` with that continuation makes no
call in `Q`. -/
def BindFree (Q : (WorldSpec C).Domain → Prop) {β : Type} (S : β → Prop) (oa : OracleComp (WorldSpec C) β) :
    Prop :=
  ∀ (γ : Type) (k : β → OracleComp (WorldSpec C) γ), (∀ b, S b → IsQueryBoundP (k b) Q 0) →
    IsQueryBoundP (oa >>= k) Q 0

variable (Q : (WorldSpec C).Domain → Prop) (hQ : ∀ t, ¬ Q (.inl (.inl t)))

include hQ in
/-- The steps of the adversary are on the counted copy. -/
theorem isQueryBoundP_adversary_free {β : Type} (oa : OracleComp (LocalSpec C) β) :
    IsQueryBoundP (worldRoles.adversary oa) Q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have hq : (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) = OracleComp.lift (OracleSpec.query t) := rfl
    rw [hq, adversary_bind, adversary_query, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (hQ t), fun u => by simpa only [hQ t, ite_false] using ih u⟩

theorem bindFree_pure {β : Type} (S : β → Prop) (b : β) (hb : S b) : BindFree Q S (pure b) :=
  fun _ k hk => by rw [pure_bind]; exact hk b hb

/-- Advancing a program on the free copy keeps the bound of its rest. -/
theorem bindFree_free_advance (oa : OracleComp (PartySpec C E G) (Option α))
    (h : IsQueryBoundP oa (PartyFree (E := E) (G := G) Q) 0) :
    BindFree Q (StepFree (E := E) (G := G) Q) (free (advance oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro γ k hk
    rw [advance_pure, free_pure, pure_bind]
    exact hk _ trivial
  | query_bind t f ih =>
    intro γ k hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · have hq : ¬ Q (.inr q) := h.1.resolve_right (lt_irrefl 0)
      have e : free (advance (liftM (OracleSpec.query (Sum.inl (Sum.inl q))) >>= f)) =
          (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>= fun u => free (advance (f u)) := by
        rw [show (liftM (OracleSpec.query (Sum.inl (Sum.inl q))) : OracleComp (PartySpec C E G) _) =
          OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl q))) from rfl,
          advance_query_bind, free_bind]
        rfl
      rw [e, bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl hq, fun u => by
        simpa only [hq, ite_false] using ih u (by simpa only [PartyFree, hq, ite_false] using h.2 u) _ k hk⟩
    · change IsQueryBoundP (free (pure (Step.wait outbox f)) >>= k) Q 0
      rw [free_pure, pure_bind]
      exact hk _ fun inbox => by simpa only [Nat.zero_sub, ite_self] using h.2 inbox
    · change IsQueryBoundP (free (pure (Step.call input f)) >>= k) Q 0
      rw [free_pure, pure_bind]
      exact hk _ fun out => by simpa only [Nat.zero_sub, ite_self] using h.2 out

theorem bindFree_sequenceFin {β : Type} (S : β → Prop) : ∀ {N : ℕ} (ms : Fin N → OracleComp (WorldSpec C) β),
    (∀ i, BindFree Q S (ms i)) → BindFree Q (fun bs => ∀ i, S (bs i)) (OverPermutation.sequenceFin ms)
  | 0, ms, _ => by
    intro γ k hk
    simp only [OverPermutation.sequenceFin, pure_bind]
    exact hk _ fun i => Fin.elim0 i
  | N + 1, ms, h => by
    intro γ k hk
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    exact h 0 _ _ fun b0 hb0 => bindFree_sequenceFin S (fun i : Fin N => ms i.succ) (fun i => h i.succ) _ _
      fun bs hbs => hk _ fun i => Fin.cases hb0 hbs i

variable {Ia L R O : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R)

include hQ in
theorem bindFree_stepRound (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α)
    (h : ∀ j, StepFree Q (steps j)) :
    BindFree Q (fun r => ∀ j, StepFree Q (r.2.1 j)) (stepRound worldRoles D A F state steps) := by
  intro γ k hk
  have hcall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
    rintro ⟨⟨i, -, hi⟩, -⟩
    cases hs : steps i with
    | done out => simp [hs, Step.callInput] at hi
    | wait out resume => simp [hs, Step.callInput] at hi
    | call input resume => exact input.elim
  unfold stepRound
  rw [ite_eq_right hcall]
  simp only [bind_assoc]
  refine isQueryBoundP_bind_zero _ _ (isQueryBoundP_adversary_free Q hQ _) fun result => ?_
  refine bindFree_sequenceFin Q (StepFree Q) _ (fun j => ?_) _ _ fun sts hsts => by
    rw [pure_bind]
    exact hk _ hsts
  have hj := h j
  split
  · exact bindFree_pure Q (StepFree Q) (Step.done _) trivial
  · rename_i resume hs
    rw [hs] at hj
    by_cases hD : j ∈ D.1
    · rw [ite_eq_left hD]
      exact bindFree_pure Q (StepFree Q) (Step.done _) trivial
    · rw [ite_eq_right hD, worldRoles_honest]
      exact bindFree_free_advance Q _ (hj _)
  · exact bindFree_pure Q (StepFree Q) (Step.done _) trivial

include hQ in
theorem executeRounds_free : ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α),
    (∀ j, StepFree Q (steps j)) → IsQueryBoundP (executeRounds worldRoles D A F fuel state steps) Q 0
  | 0, _, _, _ => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact bindFree_stepRound Q hQ D A F state steps h _ _ fun ⟨st, sts, _⟩ hr =>
        executeRounds_free fuel st sts hr

include hQ in
/-- A phase on the real network makes no free call in `Q`, when no honest program makes a local call
in `Q`. -/
theorem executePhase_free (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec PEmpty O) α)
    (hp : ∀ i, i ∉ D.1 → IsQueryBoundP (program i).run (PartyFree (E := E) (G := CallSpec PEmpty O) Q) 0) :
    IsQueryBoundP (executePhase worldRoles D A F fuel state program) Q 0 := by
  unfold executePhase startSteps
  refine bindFree_sequenceFin Q (StepFree Q) _ (fun i => ?_) _ _ fun sts hsts =>
    executeRounds_free Q hQ D A F fuel state sts hsts
  by_cases hi : i ∈ D.1
  · rw [ite_eq_left hi]
    exact bindFree_pure Q (StepFree Q) (Step.done _) trivial
  · rw [ite_eq_right hi, worldRoles_honest]
    exact bindFree_free_advance Q _ (hp i hi)

end Frame

/-! ## The program of the PRSS setup -/

section Program

variable {ι : Type} {G : OracleSpec ι}

section Closure

variable (p : (PartySpec C E G).Domain → Prop)

theorem isQueryBoundP_partyBind {β γ : Type} (x : PartyM C E G β) (f : β → PartyM C E G γ)
    (hx : IsQueryBoundP x.run p 0) (hf : ∀ b, IsQueryBoundP (f b).run p 0) :
    IsQueryBoundP (x >>= f).run p 0 := by
  rw [OptionT.run_bind, Option.elimM]
  refine isQueryBoundP_bind_zero _ _ hx fun o => ?_
  cases o with
  | none => exact isQueryBoundP_pure _ _ _
  | some b => exact hf b

theorem isQueryBoundP_partyPure {β : Type} (b : β) : IsQueryBoundP (pure b : PartyM C E G β).run p 0 := by
  rw [OptionT.run_pure]
  exact isQueryBoundP_pure _ _ _

theorem isQueryBoundP_require (condition : Prop) :
    IsQueryBoundP (require condition : PartyM C E G Unit).run p 0 := by
  unfold require
  split_ifs
  · exact isQueryBoundP_partyPure p ()
  · exact isQueryBoundP_pure _ _ _

theorem isQueryBoundP_exchange (hp : ∀ outbox, ¬ p (.inl (.inr outbox))) (outbox : Mail C E) :
    IsQueryBoundP (exchange outbox : PartyM C E G (Mail C E)).run p 0 := by
  unfold exchange
  refine isQueryBoundP_partyBind p _ _ ?_ fun inbox => ?_
  · rw [OptionT.run_lift]
    exact ⟨Or.inl (hp outbox), fun _ => trivial⟩
  · split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_partyPure p inbox

theorem isQueryBoundP_localStep {β : Type} (oa : OracleComp (LocalSpec C) β)
    (h : IsQueryBoundP oa (fun t => p (.inl (.inl t))) 0) :
    IsQueryBoundP (localStep oa : PartyM C E G β).run p 0 := by
  unfold localStep
  rw [OptionT.run_lift]
  refine isQueryBoundP_bind_zero _ _ ?_ fun _ => isQueryBoundP_pure _ _ _
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k : OracleComp (LocalSpec C) _) (PartySpec C E G) =
        (liftM ((PartySpec C E G).query (.inl (.inl t))) : OracleComp (PartySpec C E G) _) >>=
          fun u => liftComp (k u) _ := by
      rw [liftComp_bind]
      rcases t with n | x | x <;> rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => by
      simpa only [Nat.zero_sub, ite_self] using ih u (by simpa only [Nat.zero_sub, ite_self] using h.2 u)⟩

end Closure

/-- A cell of the setup domain of `phase`. -/
def SetupCell (phase : Phase) : Query C → Prop
  | .commit ph _ _ _ => ph = phase
  | .derive ph _ _ => ph = phase
  | .sharedKeys ph _ => ph = phase
  | _ => False

theorem isQueryBoundP_mapM_zero {κ β : Type} {S : OracleSpec κ} (r : κ → Prop) {δ : Type} (f : δ → OracleComp S β)
    (l : List δ) (h : ∀ x ∈ l, IsQueryBoundP (f x) r 0) : IsQueryBoundP (l.mapM f) r 0 := by
  simpa using queryBound_mapM r f 0 l h

end Program

end ThresholdLeanXmssSecurity

end

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

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

end ThresholdLeanXmssSecurity

end

noncomputable section

set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Two honest operators with keys hold the same key of each term that both hold. -/
def KeysAgree (D : C.Coalition) (out : C.Party → Option (Keys C)) : Prop :=
  ∀ (i j : C.Party) (T : C.Term), i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    ∀ ki ∈ out i, ∀ kj ∈ out j, ki.seed T = kj.seed T

/-- Two honest operators with keys hold the same key of their pair. -/
def PairKeysAgree (D : C.Coalition) (out : C.Party → Option (Keys C)) : Prop :=
  ∀ (i j : C.Party), i ∉ D.1 → j ∉ D.1 → i ≠ j → ∀ ki ∈ out i, ∀ kj ∈ out j, ki.pairKey j = kj.pairKey i

/-- Outputs that are dealt keys always agree. -/
theorem keysAgree_of_dealt (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (out : C.Party → Option (Keys C))
    (hout : ∀ i, ∀ k ∈ out i, k = dealtKeys parameter seeds pairs i) :
    KeysAgree D out ∧ PairKeysAgree D out := by
  constructor
  · intro i j T _ _ hi hj ki hki kj hkj
    rw [hout i ki hki, hout j kj hkj]
    simp only [dealtKeys, BitVec.ofNat_eq_ofNat, hi, ↓reduceIte, hj]
  · intro i j _ _ hij ki hki kj hkj
    rw [hout i ki hki, hout j kj hkj]
    have hji : j ≠ i := fun h => hij h.symm
    simp only [dealtKeys, hji, hij, dite_false]
    congr 1
    unfold Committee.pairOf
    rcases lt_trichotomy i j with h | h | h
    · simp only [h, ↓reduceDIte, not_lt_of_gt h]
    · exact absurd h hij
    · simp only [not_lt_of_gt h, ↓reduceDIte, h]

theorem distinguish_pure {σ O : Type} (oa : OracleComp (WorldSpec C) (σ × (C.Party → Option O)))
    (f : σ × (C.Party → Option O) → Bool) : distinguish oa (fun r => pure (f r)) = f <$> oa := by
  simp only [distinguish, worldRoles, liftComp_pure, counted, simulateQ_pure, map_eq_bind_pure_comp,
    Function.comp_def]

theorem accepts_map (prims : Primitives) {α : Type} (oa : OracleComp (WorldSpec C) α) (f : α → Bool) :
    accepts prims (f <$> oa) = (Pr{let r ← runWorld prims oa}[f r.1 = true]).toReal := by
  rw [accepts_eq_probOutput, probEvent_runWorld_fst prims oa fun r => f r = true, simulateQ_map,
    StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map, prEvent_map]

end ThresholdLeanXmssSecurity

end
