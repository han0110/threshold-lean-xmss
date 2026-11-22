import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Stages

/-!
# Facts for the two stages of `DealerFirstForger`

* `worldDealer_replay` states that after a run of the top tree of the dealer, `worldDealer` gives the
  same dealer from each larger cache and changes no state.
* `worldAdversaryCall_run` states that a call of `A` in the world of the forger is `observe` with the
  log of the setup calls.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- After a run of the top tree of the dealer, `worldDealer` gives the dealer of that run from each
larger cache, and changes no state. -/
theorem worldDealer_replay (prims : Primitives) (D : C.Coalition) {σ : Type} (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (w : HashCache C × HiddenCache C)
    (z : Option TreeOutput × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (dealerTop parameter seeds)).run w))
    (w' : HashCache C × HiddenCache C) (hle : z.2.1 ≤ w'.1) (s : RealState C σ) :
    (simulateQ (streamWorld prims D) ((worldDealer (σ := σ) parameter seeds dealt).run s)).run w' =
      pure ((dealtWith (m := RealM C σ) realLift parameter dealt ((TreeOutput.topTree z.1).getD emptyTop)
        (fun x => realLift (prfValue seeds x)), s), w') := by
  have hsafe := dealerTop_safe (C := C) parameter seeds
  rw [worldDealer_run, simulateQ_map, StateT.run_map]
  unfold dealerTop at hsafe hz ⊢
  generalize Tree.top = tree at hsafe hz ⊢
  rw [streamWorld_safe hsafe, baseAnswer_freeLift] at hz ⊢
  rw [support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [replay_simulateQ (grows_roAnswer prims) (replays_roAnswer prims) _ w.1 y hy w'.1 hle]
  simp

theorem observe_bind {α β : Type} (oa : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β) :
    observe (oa >>= f) = observe oa >>= fun r => (fun r' => (r'.1, r.2 ++ r'.2)) <$> observe (f r.1) := by
  simp [observe, WriterT.run_bind]

theorem worldAdversaryCall_query (t : (LocalSpec C).Domain) (log : CallLog C) (st : TsigState C) :
    ((worldAdversaryCall t).run log).run st =
      (fun r => ((r.1, log ++ r.2.filter fun e => isSetupQuery e.1), st)) <$>
        observe (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) := by
  rcases t with n | q | x
  · simp [worldAdversaryCall, toWorld, StateT.run_lift, observe]
  · by_cases hq : isSetupQuery q = true
    · simp [worldAdversaryCall, toWorld, StateT.run_lift, observe, hq, hashQuery]
    · simp [worldAdversaryCall, toWorld, StateT.run_lift, observe, hq, hashQuery]
  · simp [worldAdversaryCall, toWorld, StateT.run_lift, observe]

/-- A call of `A` in the world of the forger is `observe`, with the setup calls of its log appended to
the log of the state. -/
theorem worldAdversaryCall_run {α : Type} (oa : OracleComp (LocalSpec C) α) (log : CallLog C)
    (st : TsigState C) :
    ((simulateQ worldAdversaryCall oa).run log).run st =
      (fun r => ((r.1, log ++ r.2.filter fun e => isSetupQuery e.1), st)) <$> observe oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp [observe]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rw [StateT.run_bind, StateT.run_bind, worldAdversaryCall_query, observe_bind]
    simp only [bind_map_left, map_bind, ih, Functor.map_map, List.filter_append, List.append_assoc]

/-- A call of an emulated operator in the world of the forger is a free call, with no change of the
state. -/
theorem worldHonestCall_run {α : Type} (oa : OracleComp (LocalSpec C) α) (log : CallLog C) (st : TsigState C) :
    ((simulateQ worldHonestCall oa).run log).run st = (fun a => ((a, log), st)) <$> free oa := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rw [StateT.run_bind, StateT.run_bind, free_bind]
    simp [worldHonestCall, toWorld, StateT.run_lift, ih, free]

theorem findSome?_filter_of {α β : Type} (f : α → Option β) (p : α → Bool) (h : ∀ x, p x = false → f x = none)
    (l : List α) : (l.filter p).findSome? f = l.findSome? f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a
    · simp [hp, ih, h a hp]
    · simp [hp, ih, List.findSome?_cons]

/-- The reveals that `extractReveal` reads are setup calls, so the log of the setup calls gives the
same reveals. -/
theorem extractReveal_filter {E : Type} (phase : Phase) (calls : CallLog C)
    (sent : C.Party → C.Party → Option (Msg E)) (j i : C.Party) :
    extractReveal phase (calls.filter fun e => isSetupQuery e.1) sent j i = extractReveal phase calls sent j i := by
  unfold extractReveal
  rw [findSome?_filter_of]
  rintro ⟨q, out⟩ hq
  cases q <;> simp_all [isSetupQuery]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.worldDealer_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.worldDealer_replay
