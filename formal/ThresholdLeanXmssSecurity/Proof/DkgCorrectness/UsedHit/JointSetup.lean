import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Bottom

/-!
# The free setup calls of `jointKeyWorld` commute

`jointKeyWorld_setupCommute` states that a free call that `SetupLocal` allows, a private coin or a hash call
of the class `prssSetup`, commutes in `jointKeyWorld` with each free call. A coin keeps the state. A setup
hash call reads and writes only its own cell of the hash cache, which is no cell of a stream key, and no
risk of the world reads it.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- A computation that keeps the state commutes with each computation. -/
theorem commutes_of_keep {σ α β : Type} {x : StateT σ ProbComp α} (p : ProbComp α)
    (hx : ∀ s, x.run s = (fun a => (a, s)) <$> p) (y : StateT σ ProbComp β) : Commutes x y := by
  intro s
  simp only [StateT.run_bind, hx, bind_map_left, StateT.run_pure]
  exact EvalDistEq.bind_bind_swap _ _ _

/-- The free local answers of `jointKeyWorld` with no real key are the answers of `localAnswer` on the
hash cache. -/
theorem jointLocal_false_eq (t : (LocalSpec C).Domain) :
    jointLocal prims false t = onJointHash (localAnswer prims t) := by
  rcases t with u | q | x
  · rfl
  · refine StateT.ext fun s => ?_
    cases q <;> rfl
  · refine StateT.ext fun s => ?_
    simp only [jointLocal, onJointHash, jointHash, StateT.run_bind, StateT.run_mk, StateT.run_pure,
      bind_map_left, Bool.false_eq_true, ite_false]
    change _ = (fun r => (r.1, { s with hash := r.2 })) <$> (prgAnswer prims x).run s.hash
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind, map_pure]

/-- A free answer that runs `m` on the hash cache and raises the flag by `g`. -/
def HashForm {α : Type} (x : StateT (KeyJointState C) ProbComp α) (m : StateT (HashCache C) ProbComp α)
    (g : KeyJointState C → Bool) : Prop :=
  ∀ s, x.run s = (fun r => (r.1, { s with hash := r.2, bad := s.bad || g s })) <$> m.run s.hash

/-- A free answer of `jointKeyWorld` that is no hidden call of `PRG` is its local answer on the hash cache. -/
theorem jointKeyWorld_hashForm (t : (LocalSpec C).Domain) (ht : ¬ ∃ x, t = .inr (.inr x) ∧ Hidden D x.1) :
    HashForm (jointKeyWorld prims D false (.inr t)) (localAnswer prims t) (keyJointRisk D (.inr t)) := by
  intro s
  have hcore : (jointKeyWorldCore prims D false (.inr t)).run s = (onJointHash (localAnswer prims t)).run s := by
    rw [← jointLocal_false_eq]
    rcases t with u | q | x
    · rfl
    · rfl
    · have hx : ¬ Hidden D x.1 := fun h => ht ⟨x, rfl, h⟩
      simp only [jointKeyWorldCore, hx, ite_false]
  simp only [jointKeyWorld, StateT.run_mk, hcore, onJointHash, Functor.map_map]
  rfl

theorem mergeSetup_self (s : KeyJointState C) : mergeSetup s.hash s = s := by
  have hc : mergeCache s.hash s.hash = s.hash := by
    ext q : 1
    by_cases hq : setupCell q = true
    · exact mergeCache_read_setup hq _ _
    · exact mergeCache_read_other (by simpa using hq) _ _
  cases s
  simp only [mergeSetup] at hc ⊢
  rw [hc]

/-- A setup hash call on the free copy commutes with each computation that keeps the setup cells. -/
theorem commutes_setup_frames {q : Query C} (hq : queryClass q = .prssSetup) {β : Type}
    (y : StateT (KeyJointState C) ProbComp β) (hy : Frames y) :
    Commutes (jointKeyWorld prims D false (.inr (.inr (.inl q)))) y := by
  intro s
  unfold Frames at hy
  rw [← mergeSetup_self s]
  simp only [StateT.run_bind, StateT.run_pure, jointKeyWorld_setup_free prims D hq, hy, bind_map_left]
  exact EvalDistEq.bind_bind_swap _ _ _

/-- Two setup hash calls on the free copy commute. -/
theorem commutes_setup_setup {q q' : Query C} (hq : queryClass q = .prssSetup) (hq' : queryClass q' = .prssSetup) :
    Commutes (jointKeyWorld prims D false (.inr (.inr (.inl q)))) (jointKeyWorld prims D false (.inr (.inr (.inl q')))) := by
  intro s
  rw [← mergeSetup_self s]
  have key := (commutes_of_isAtom (isAtom_hashAnswer prims q) (isAtom_hashAnswer prims q') s.hash).map
    fun p : (HashOutput × HashOutput) × HashCache C => (p.1, mergeSetup p.2 s)
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure] at key
  simp only [StateT.run_bind, StateT.run_pure, jointKeyWorld_setup_free prims D hq, jointKeyWorld_setup_free prims D hq',
    bind_map_left]
  exact key

/-- A private coin or a setup hash call on the free copy, a first call that `SetupLocal` allows, commutes
with each free call in `jointKeyWorld`. The split at the end of the head moves the local work of the
start of the second setup before the local end of the head of later operators. -/
theorem jointKeyWorld_setupCommute (t t' : (LocalSpec C).Domain) (ht : SetupLocal t) :
    Commutes (jointKeyWorld prims D false (.inr t)) (jointKeyWorld prims D false (.inr t')) := by
  rcases t with u | q | x
  · obtain ⟨p, hp⟩ : ∃ p, localAnswer (C := C) prims (.inl u) = StateT.lift p := ⟨_, rfl⟩
    refine commutes_of_keep p (fun s => ?_) _
    rw [jointKeyWorld_hashForm prims D (.inl u) (fun ⟨x, e, _⟩ => by simp at e) s, hp]
    simp only [StateT.run_lift, map_bind, map_pure]
    have hr : keyJointRisk D (.inr (.inl u)) s = false := rfl
    rw [hr, Bool.or_false, map_eq_bind_pure_comp]
    rfl
  · have hq : queryClass q = .prssSetup := ht
    by_cases hs : ∃ q', t' = .inr (.inl q') ∧ queryClass q' = .prssSetup
    · obtain ⟨q', rfl, hq'⟩ := hs
      exact commutes_setup_setup prims D hq hq'
    · refine commutes_setup_frames prims D hq _ (frames_jointKeyWorld prims D _ ?_ ?_)
      · rintro h
        rcases t' with u' | q' | x' <;> simp_all [SetupQuery]
      · rintro h
        exact h
  · exact absurd ht id

/-! ## The start of a setup and the head of a bottom run -/

section Programs

variable {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Algebra Bit E] in
/-- The first free work of a program that starts with a PRSS setup makes only the calls that
`SetupLocal` allows. -/
theorem advance_prssSetup_bind {β : Type} (i : C.Party) (g : PrssKeys C → PartyM C E RealSpec β) :
    AllQueriesSatisfy (advance (prssSetup i >>= g).run) SetupLocal := by
  rw [advance_bind]
  have e : (advance (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run >>= continueStep g) =
      (advance (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run >>= fun step => pure (attachStep g step)) := by
    refine bind_congr_of_forall_mem_support _ fun step hstep => ?_
    refine continueStep_attach _ _ ?_
    rcases startsWithRound_prssSetup i step hstep with h | ⟨outbox, resume, h, _⟩ <;> rw [h] <;> rfl
  rw [e]
  refine allQueriesSatisfy_bind (advance_setup _ ?_) fun _ => allQueriesSatisfy_pure _ _
  rw [prssSetup_eq_map]
  exact (setupKeys_setup i).bind fun _ => SetupM.pure _

omit [Field E] [Algebra Bit E] in
/-- The first free work of a tail makes only the calls that `SetupLocal` allows. -/
theorem advance_headWith_tail (i : C.Party) (operator : OperatorState C) {β : Type}
    (tail : Keys C → TopTree → PrssKeys C → PartyM C E RealSpec β) :
    AllQueriesSatisfy (advance (match operator.keys, operator.top with
      | some keys, some top => prssSetup i >>= tail keys top
      | _, _ => (failure : PartyM C E RealSpec β)).run) SetupLocal := by
  split
  · exact advance_prssSetup_bind i _
  · rw [advance_run_failure]
    exact allQueriesSatisfy_pure _ _

/-- The first ceremony of a bottom run after its PRSS setup takes the rounds of its batches. -/
theorem runTimed_firstAfter [Fintype E] (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) (prss : PrssKeys C) :
    RunTimed (Fuel.batchesRounds circuits settings keys.parameter (bottomJobs b))
      (firstAfter K circuits settings i keys b prss) := by
  unfold firstAfter batchesWith
  rw [← Nat.add_zero (Fuel.batchesRounds circuits settings keys.parameter (bottomJobs b)),
    ← Nat.add_zero (Fuel.batchesRounds circuits settings keys.parameter (bottomJobs b))]
  refine ((runTimed_batches K circuits settings.mode _ keys.parameter _).bind fun outs => runTimed_pure _).bind
    fun o => ?_
  rcases o with _ | outputs
  · exact runTimed_pure _
  dsimp only
  generalize merkleNode keys.parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val = node
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun root => ?_
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun base => ?_
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · exact runTimed_pure _
  · exact runTimed_pure _

/-- The head of a bottom run takes the rounds of its first ceremony under the parameter of the keys. -/
theorem timed_headWith [Fintype E] (parameter : PublicParameter) (D : C.Coalition) (fresh : Option (FreshKeys C))
    (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (h : ∀ keys, operator.keys = some keys → keys.parameter = parameter) :
    Timed (CheckTiming.firstRounds circuits settings parameter (.bottom b))
      (headWith K circuits settings D fresh i operator b).run := by
  unfold headWith
  split
  · rename_i keys _ hk _
    rw [← h keys hk, CheckTiming.firstRounds, CheckTiming.firstJobs, ← CheckTiming.batchesRounds_eq,
      ← Nat.add_zero (Fuel.batchesRounds circuits settings keys.parameter (bottomJobs b))]
    refine (timed_prssSetup i).bind fun prss => ?_
    refine (runTimed_firstAfter K circuits settings i keys b _ (0, 0)).bind fun p => ?_
    rcases p with ⟨_ | x, st⟩
    · exact timed_failure 0
    · exact timed_pure _
  · exact timed_failure _

end Programs

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.jointKeyWorld_setupCommute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.jointKeyWorld_setupCommute

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.timed_headWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.timed_headWith
