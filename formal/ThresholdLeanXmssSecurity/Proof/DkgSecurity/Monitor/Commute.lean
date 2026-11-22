import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.JointSetup
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops

/-!
# A call of the monitor commutes in `jointKeyWorld`

A call of the monitor is a free call of `H` on `.hash` or on `.prf`. In `jointKeyWorld prims D false`
it reads and writes one cell of the hash cache, which is no cell of a stream key, and it raises no
risk. `jointKeyWorld_monitorCommute` states that such a call commutes with each call that is no
programming call. `jointKeyWorld_monitorView` states that such a call keeps `privateView`, the part of
the state that `UsedHit` reads.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

open UsedHit (HashForm jointKeyWorld_hashForm jointLocal_false_eq)
open GameCount (MonitorCall SignCall)

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The part of the state of `jointKeyWorld` that `UsedHit` reads. It is the private answers, the
names of the used keys and the cells of the stream keys. -/
def privateView (s : KeyJointState C) : FullKeyCache C × (HashOutput → Option (KeyName C)) × (HashOutput → Option HashOutput) :=
  (s.keys, s.used, fun k => s.hash (.streamKey k))

theorem usedHit_iff_view {s s' : KeyJointState C} (h : privateView s = privateView s') :
    UsedHit D s ↔ UsedHit D s' := by
  simp only [privateView, Prod.mk.injEq] at h
  obtain ⟨hk, hu, hh⟩ := h
  have hh' : ∀ k, s.hash (.streamKey k) = s'.hash (.streamKey k) := fun k => congrFun hh k
  simp only [UsedHit, hk, hu, hh']

/-- A counted answer of `jointKeyWorld` is its local answer on the hash cache. -/
theorem jointKeyWorld_hashForm_counted (t : (LocalSpec C).Domain) :
    HashForm (jointKeyWorld prims D false (.inl (.inl t))) (localAnswer prims t) (keyJointRisk D (.inl (.inl t))) := by
  intro s
  have hcore : (jointKeyWorldCore prims D false (.inl (.inl t))).run s = (onJointHash (localAnswer prims t)).run s := by
    rw [← jointLocal_false_eq]
    rfl
  simp only [jointKeyWorld, StateT.run_mk, hcore, onJointHash, Functor.map_map]
  rfl

/-- The risk of a call reads no cell of the hash cache besides the cells of the stream keys, and not
the flag. -/
theorem keyJointRisk_hash (t : (WorldSpec C).Domain) (s : KeyJointState C) (c : HashCache C) (b : Bool)
    (hc : ∀ k, c (.streamKey k) = s.hash (.streamKey k)) :
    keyJointRisk D t { s with hash := c, bad := b } = keyJointRisk D t s := by
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · rfl
  · cases q <;> rfl
  · rfl
  · cases q <;> rfl
  · rfl
  · cases q <;> rfl
  · simp only [keyJointRisk, hc]

/-- A call of `H` on `.hash` or on `.prf` keeps each cell of a stream key. -/
theorem hashAnswer_streamKey {q : Query C} (hq : SignCall (C := C) (.inl q)) (c : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run c), ∀ k, z.2 (.streamKey k) = c (.streamKey k) := by
  intro z hz k
  have hne : (Query.streamKey k : Query C) ≠ q := by
    rintro rfl
    exact hq
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hf
    rw [hashAnswer_of_isFixed prims hm] at hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · rw [hashAnswer_of_not_isFixed prims hf] at hz
    exact (randomOracle_support q c z hz).2.2 _ hne

/-- The monitor call as an answer on the hash cache with no risk. -/
theorem jointKeyWorld_monitor_run {q : Query C} (hq : SignCall (C := C) (.inl q)) (s : KeyJointState C) :
    (jointKeyWorld prims D false (.inr (.inr (.inl q)))).run s =
      (fun z => (z.1, { s with hash := z.2 })) <$> (hashAnswer prims q).run s.hash := by
  rw [jointKeyWorld_hashForm prims D (.inr (.inl q)) (fun ⟨x, e, _⟩ => by simp at e) s]
  have hr : keyJointRisk D (.inr (.inr (.inl q))) s = false := by
    cases q <;> first | exact (hq : False).elim | rfl
  rw [hr, Bool.or_false]
  rfl

/-- A call of the monitor keeps `privateView`. -/
theorem jointKeyWorld_monitorView (t : (WorldSpec C).Domain) (ht : MonitorCall t) (s : KeyJointState C) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), privateView r.2 = privateView s := by
  rcases t with (_ | _) | (_ | q | _)
  all_goals try exact (ht : False).elim
  have hq : SignCall (C := C) (.inl q) := ht
  intro r hr
  rw [jointKeyWorld_monitor_run prims D hq, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  simp only [privateView]
  congr 2
  funext k
  exact hashAnswer_streamKey prims hq s.hash z hz k

/-- A call of the monitor commutes with an answer on the hash cache whose risk reads no cell of the
hash cache besides the cells of the stream keys. -/
theorem commutes_monitor_hashForm {q : Query C} (hq : SignCall (C := C) (.inl q)) {β : Type}
    {y : StateT (KeyJointState C) ProbComp β} {m : StateT (HashCache C) ProbComp β} {g : KeyJointState C → Bool}
    (hy : HashForm y m g) (hm : IsAtom m)
    (hg : ∀ s c, (∀ k, c (.streamKey k) = s.hash (.streamKey k)) → g { s with hash := c } = g s) :
    Commutes (jointKeyWorld prims D false (.inr (.inr (.inl q)))) y := by
  unfold HashForm at hy
  intro s
  have key := (commutes_of_isAtom (isAtom_hashAnswer prims q) hm s.hash).map
    (fun p : (HashOutput × β) × HashCache C => (p.1, ({ s with hash := p.2, bad := s.bad || g s } : KeyJointState C)))
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure] at key
  simp only [StateT.run_bind, StateT.run_pure, jointKeyWorld_monitor_run prims D hq, hy, bind_map_left]
  refine EvalDistEq.trans ?_ (key.trans ?_)
  · refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
    rw [hg s z.2 (hashAnswer_streamKey prims hq s.hash z hz)]
  · exact EvalDistEq.rfl

/-- The draw of a hidden answer on the private answers and the names of the used keys. -/
def hiddenDraw (x : KeyName C × HashOutput) (keys : FullKeyCache C) (used : HashOutput → Option (KeyName C)) :
    ProbComp (HashOutput × FullKeyCache C × (HashOutput → Option (KeyName C))) :=
  match keys x with
  | some v => pure (v, keys, used)
  | none => (fun v => (v, keys.cacheQuery x v,
      if (used x.2).isSome then used else Function.update used x.2 (some x.1))) <$> ($ᵗ HashOutput)

theorem jointHidden_run (x : KeyName C × HashOutput) (s : KeyJointState C) :
    (jointHidden false x).run s =
      (fun r => (r.1, { s with keys := r.2.1, used := r.2.2 })) <$> hiddenDraw x s.keys s.used := by
  simp only [jointHidden, StateT.run_mk, hiddenDraw]
  rcases s.keys x with _ | v
  · simp [map_eq_bind_pure_comp]
  · simp

/-- A hidden call of `PRG` on the free copy is a draw on the private answers. -/
theorem jointKeyWorld_hidden_run (x : PrgInput C) (hx : Hidden D x.1) (s : KeyJointState C) :
    (jointKeyWorld prims D false (.inr (.inr (.inr x)))).run s =
      (fun r => (prims.aes.eval (truncateHash r.1) x.2.2,
        ({ s with keys := r.2.1, used := r.2.2, bad := s.bad || keyJointRisk D (.inr (.inr (.inr x))) s } :
          KeyJointState C))) <$> hiddenDraw (x.1, x.2.1) s.keys s.used := by
  simp only [jointKeyWorld, StateT.run_mk, jointKeyWorldCore, hx, ite_true, StateT.run_bind, jointHidden_run,
    StateT.run_pure, bind_map_left, map_bind, map_pure]
  simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- A call of the monitor commutes with a hidden call of `PRG` on the free copy. -/
theorem commutes_monitor_hidden {q : Query C} (hq : SignCall (C := C) (.inl q)) (x : PrgInput C) (hx : Hidden D x.1) :
    Commutes (jointKeyWorld prims D false (.inr (.inr (.inl q)))) (jointKeyWorld prims D false (.inr (.inr (.inr x)))) := by
  intro s
  simp only [StateT.run_bind, StateT.run_pure, jointKeyWorld_monitor_run prims D hq, jointKeyWorld_hidden_run (prims := prims) (D := D) x hx,
    bind_map_left]
  refine EvalDistEq.trans ?_ (EvalDistEq.bind_bind_swap _ _ _)
  refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  have hr := keyJointRisk_hash D (.inr (.inr (.inr x))) s z.2 s.bad (hashAnswer_streamKey prims hq s.hash z hz)
  rw [hr]

/-- A call of the monitor commutes in `jointKeyWorld prims D false` with each call that is no
programming call. -/
theorem jointKeyWorld_monitorCommute (t t' : (WorldSpec C).Domain) (ht : MonitorCall t)
    (ht' : ¬ WorldProgramQuery t') :
    Commutes (jointKeyWorld prims D false t) (jointKeyWorld prims D false t') := by
  rcases t with (_ | _) | (_ | q | _)
  all_goals try exact (ht : False).elim
  have hq : SignCall (C := C) (.inl q) := ht
  have hg : ∀ t'' : (WorldSpec C).Domain, ∀ (s : KeyJointState C) (c : HashCache C),
      (∀ k, c (.streamKey k) = s.hash (.streamKey k)) → keyJointRisk D t'' { s with hash := c } = keyJointRisk D t'' s :=
    fun t'' s c hc => keyJointRisk_hash D t'' s c s.bad hc
  rcases t' with ((u | q' | x) | p) | (u | q' | x)
  · exact commutes_monitor_hashForm prims D hq (jointKeyWorld_hashForm_counted prims D _)
      (isAtom_localAnswer prims _) (hg _)
  · exact commutes_monitor_hashForm prims D hq (jointKeyWorld_hashForm_counted prims D _)
      (isAtom_localAnswer prims _) (hg _)
  · exact commutes_monitor_hashForm prims D hq (jointKeyWorld_hashForm_counted prims D _)
      (isAtom_localAnswer prims _) (hg _)
  · exact absurd trivial ht'
  · exact commutes_monitor_hashForm prims D hq (jointKeyWorld_hashForm prims D _ (fun ⟨_, e, _⟩ => by simp at e))
      (isAtom_localAnswer prims _) (hg _)
  · exact commutes_monitor_hashForm prims D hq (jointKeyWorld_hashForm prims D _ (fun ⟨_, e, _⟩ => by simp at e))
      (isAtom_localAnswer prims _) (hg _)
  · by_cases hx : Hidden D x.1
    · exact commutes_monitor_hidden prims D hq x hx
    · exact commutes_monitor_hashForm prims D hq (jointKeyWorld_hashForm prims D _ (fun ⟨_, e, h⟩ => by
        simp only [Sum.inr.injEq] at e
        exact hx (e ▸ h)))
        (isAtom_localAnswer prims _) (hg _)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.jointKeyWorld_monitorCommute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.jointKeyWorld_monitorCommute

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.jointKeyWorld_monitorView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.jointKeyWorld_monitorView
