import ThresholdLeanXmssSecurity.Proof.Tree

/-!
# The PRSS streams from dealt keys, the simulator and the two runs

* `knownStreams` takes the receivers. It computes only the streams that an honest receiver computes
  in the real run. So the two runs make the same hash calls on the keys of the coalition.
* `prssRandSim` keeps the receivers that the adversary names, and gives them to `FrandCalls`.
* `honestStreams` is the list of the stream draws of the operators that draw. `advance_randCalls`,
  `realExecution_prssRand` and `idealExecution_FrandCalls` are the normal forms of the two runs.
* `dealtKey` is the dealt key of a name.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The simulator -/

/-- The streams of one call under the keys that the coalition knows and an honest receiver holds, at
the `count` positions. The terms have a corrupt holder and a holder that is an honest receiver.
Pair stream `(j, i)` is the stream of a corrupt operator `j` and an honest receiver `i`. -/
def knownStreams {R : Type} [Zero R] (D : C.Coalition) (receivers : Finset C.Party) (codec : Codec C E R)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (Shares C R × (C.Party → C.Party → ℕ → R)) := do
  let r ← C.terms.mapM fun T =>
    if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
      codec.draw (.term T) (term T) ρ idx count
    else pure fun _ => 0
  let Z ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
      let p := C.pairOf i j (fun e => h.2.1 (e ▸ h.1))
      codec.draw (.pair p) (pair p) ρ idx count
    else pure fun _ => 0
  pure (fun T g => if g < count then (r.getD (C.terms.idxOf T) fun _ => 0) g else 0,
    fun j i g => if g < count then ((Z.getD j.val []).getD i.val fun _ => 0) g else 0)

/-- The state of the simulator. It holds the state of the adversary, the dealt keys, the receivers,
the next round label, and the calls that `F_rand` did not leak yet. -/
structure PrssRandSimState (C : Committee) (σ : Type) where
  adversary : σ
  term : C.Term → HashOutput
  pair : C.Pair → HashOutput
  receivers : Finset C.Party
  label : ℕ
  calls : List RandCall

/-- The simulator. At its start it deals keys as `FprssKeys` does and gives the adversary the keys of
the corrupt operators. It keeps the receivers that the adversary names, and gives them to
`FrandCalls`. For each call of `F_rand` it replies with the streams under the keys of the coalition.
The simulator of GS20, Lemma 1, gives `F_rand` the shares of the corrupt parties in the same way. It
uses no key of a hidden term or pair. -/
def prssRandSim (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) :
    Simulator (C := C) (LocalSpec C) Unit RandLeak (RandReplies C E) A.State where
  State := PrssRandSimState C A.State
  start corrupt z := do
    let state ← A.start corrupt z
    let term ← liftComp ($ᵗ (C.Term → HashOutput)) _
    let pair ← liftComp ($ᵗ (C.Pair → HashOutput)) _
    let (state, receivers) ← A.answer state fun i =>
      if i ∈ D.1 then some (dealtPrssKeys term pair i) else none
    pure ⟨state, term, pair, receivers, label, calls⟩
  answer st l :=
    match l with
    | .inl () => pure (st, .inl st.receivers)
    | .inr _ =>
      match st.calls with
      | [] => pure (st, .inr (.inl (0, 0)))
      | .elements idx count :: rest => do
          let known ← liftComp
            (knownStreams D st.receivers (elementCodec K) st.term st.pair st.label idx count) _
          pure ({ st with label := st.label + 1, calls := rest }, .inr (.inl known))
      | .bits idx count :: rest => do
          let known ← liftComp
            (knownStreams D st.receivers (bitCodec (E := E)) st.term st.pair st.label idx count) _
          pure ({ st with label := st.label + 1, calls := rest }, .inr (.inr known))
  output st := pure st.adversary

/-! ## The two runs -/

section Runs

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)
  (Z : Distinguisher C A.State (List (RandOutput C E)))

/-- The real run in the `F_prssKeys`-hybrid model with its distinguisher. -/
def prssRandReal : OracleComp (WorldSpec C) Bool :=
  distinguish (realExecution D A FprssKeys prssRandRounds (prssRandProtocol K label calls) x z) Z

/-- The ideal run of `FrandCalls` with `prssRandSim` and the distinguisher. -/
def prssRandIdeal : OracleComp (WorldSpec C) Bool :=
  distinguish (idealExecution worldRoles.adversary D (FrandCalls calls) (prssRandSim K label calls D A) x z) Z

end Runs

/-! ## The real run -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The run of the dealer. It samples the keys on the free copy. The adversary answers the leak of
the keys of the corrupt operators with the receivers. -/
theorem runFunctionality_FprssKeys (D : C.Coalition) {Ia : Type}
    (A : Adversary C E Ia (C.Party → Option (PrssKeys C)) (Finset C.Party)) (st : A.State)
    (inputs : C.Party → Option Unit) (h : ∀ i, i ∉ D.1 → (inputs i).isSome) :
    runFunctionality worldRoles D A FprssKeys st inputs = (do
      let term ← free (liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C))
      let pair ← free (liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C))
      let a ← counted (liftComp (A.answer st fun i =>
        if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) (SimulatorSpec C))
      pure (a.1, fun i => if i ∉ D.1 ∧ i ∈ a.2 then some (dealtPrssKeys term pair i) else none)) := by
  unfold runFunctionality
  rw [if_neg (not_not.mpr h)]
  simp only [FprssKeys, sample, simulateQ_bind, simulateQ_leak, simulateQ_pure]
  rw [simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ (C.Term → HashOutput)),
    simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ (C.Pair → HashOutput))]
  simp [worldRoles, StateT.run_bind]
  refine bind_congr' _ fun term => bind_congr' _ fun pair => ?_
  erw [QueryImpl.add_apply_inr]
  simp [StateT.run_mk, Functor.map_map]

/-! ## The streams of the calls -/

/-- The PRSS outputs of operator `i` in one round, as `prssRandomness` computes them. `stream` gives
the stream of a key. -/
def prssStreams {R : Type} [Zero R] (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R))
    (prss : PrssKeys C) (i : C.Party) : OracleComp (RoSpec C) (PrssOutput C R) := do
  let r ← C.terms.mapM fun T => if i ∈ C.holders T then stream (.term T) (prss.term T) else pure fun _ => 0
  let Z ← C.parties.mapM fun j =>
    if h : j = i then pure fun _ => 0 else stream (.pair (C.pairOf i j (Ne.symm h))) (prss.pair j)
  pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)

/-- The output of one call of operator `i` at round label `ρ`, as `randCall` computes it. `bits`
gives the stream bits of a key. -/
def callStreams (K : Constants C E) (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit))
    (prss : PrssKeys C) (i : C.Party) (ρ : ℕ) : RandCall → OracleComp (RoSpec C) (RandOutput C E)
  | .elements idx count => (fun o => .inl (clipOutput count o)) <$> prssStreams (fun name key =>
      (fun b g => K.encode.symm fun e => b (elementBits * g + e)) <$> bits name key ρ idx (elementBits * count))
      prss i
  | .bits idx count => (fun o => .inr (clipOutput count o)) <$> prssStreams (fun name key =>
      bits name key ρ idx count) prss i

/-- The outputs of the calls of operator `i` from round label `ρ`. -/
def randStreams (K : Constants C E) (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit))
    (prss : PrssKeys C) (i : C.Party) : ℕ → List RandCall → OracleComp (RoSpec C) (List (RandOutput C E))
  | _, [] => pure []
  | ρ, call :: rest => do
      let o ← callStreams K bits prss i ρ call
      let os ← randStreams K bits prss i (ρ + 1) rest
      pure (o :: os)

/-- The calls of the operators of `drawers`, one operator after the other, with the dealt keys. In
the real run the operators that draw are the honest receivers. -/
def honestStreams (K : Constants C E) (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit))
    (drawers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (label : ℕ)
    (calls : List RandCall) : OracleComp (LocalSpec C) (C.Party → Option (List (RandOutput C E))) :=
  OverPermutation.sequenceFin fun j => if j ∈ drawers then
    some <$> liftComp (randStreams K bits (dealtPrssKeys term pair j) j label calls) (LocalSpec C)
  else pure none

/-- The dealt key of a name. -/
def dealtKey (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) : KeyName C → Option HashOutput
  | .parameter => none
  | .term T => some (term T)
  | .pair p => some (pair p)

/-- The operators that draw in the real run, namely the honest receivers. -/
def honestReceivers (D : C.Coalition) (receivers : Finset C.Party) : Finset C.Party :=
  receivers.filter (· ∉ D.1)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem oracleStep_map {ι : Type} {G : OracleSpec ι} {α β : Type} (f : α → β)
    (oa : OracleComp (RoSpec C) α) :
    oracleStep (C := C) (E := E) (G := G) (f <$> oa) = f <$> oracleStep oa := by
  simp only [oracleStep, localStep, liftComp_map]
  apply OptionT.ext
  simp [OptionT.run_map, OptionT.run_lift]

omit [Fintype E] [DecidableEq E] in
/-- One call is one oracle step of `callStreams` at the label of the state, and it moves the label. -/
private theorem randCall_run {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C)
    (call : RandCall) (st : RunState C) :
    (randCall (G := G) K ctx call).run st = (fun o => (o, { st with label := st.label + 1 })) <$>
      oracleStep (callStreams K prgBits ctx.prss ctx.self st.label call) := by
  cases call <;> simp [randCall, prssRandomness, freshLabel, callStreams, prssStreams, elementCodec,
    bitCodec, oracleStep_bind, oracleStep_map, StateT.run_bind, map_bind, Functor.map_map]

/-- The calls of one operator are local draws from the label of the state, and then the output. -/
theorem advance_randCalls {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C)
    (calls : List RandCall) (st : RunState C) :
    advance (C := C) (E := E) (G := G) ((calls.mapM (randCall K ctx)).run' st).run =
      (fun outputs => Step.done (some outputs)) <$>
        liftComp (randStreams K prgBits ctx.prss ctx.self st.label calls) (LocalSpec C) := by
  induction calls generalizing st with
  | nil => rfl
  | cons call rest ih =>
    simp only [List.mapM_cons, StateT.run'_eq, StateT.run_bind, randCall_run, map_bind, bind_map_left,
      advance_oracleStep_bind, randStreams, liftComp_bind, liftComp_pure]
    refine bind_congr fun b => ?_
    have h := advance_bind (G := G)
      ((rest.mapM (randCall K ctx)).run' { st with label := st.label + 1 }) (fun os => pure (b :: os))
    rw [ih] at h
    refine Eq.trans ?_ (h.trans ?_) <;>
      simp [StateT.run'_eq, continueStep, advance_pure, map_eq_bind_pure_comp]

omit [Fintype E] [DecidableEq E] in
/-- The program of one operator stops at the call of the dealer. Without keys it aborts, and with
keys it runs its calls. -/
theorem advance_prssRandProtocol (K : Constants C E) (label : ℕ) (calls : List RandCall) (i : C.Party) :
    advance (prssRandProtocol K label calls i ()).run = pure (.call () fun r => OptionT.run (
      match r with
      | some prss => (calls.mapM (randCall K { localContext i with prss := prss })).run' ⟨fun _ => [], label, 0⟩
      | none => failure)) := by
  unfold prssRandProtocol
  rw [advance_call]
  congr 2
  funext r
  cases r <;> rfl

section RealRun

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)

/-- The real run in normal form. The dealer samples the keys, the adversary names the receivers, and
each honest receiver draws its streams on the free copy. -/
theorem realExecution_prssRand :
    realExecution D A FprssKeys prssRandRounds (prssRandProtocol K label calls) x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let term ← free (liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C))
      let pair ← free (liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C))
      let a ← counted (liftComp (A.answer st fun i =>
        if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) (SimulatorSpec C))
      let outputs ← free (honestStreams K prgBits (honestReceivers D a.2) term pair label calls)
      pure (a.1, outputs)) := by
  obtain ⟨i0, hi0⟩ := exists_honest D
  simp only [realExecution, executePhase, startSteps, worldRoles, show ∀ i, x i = () from fun _ => rfl,
    advance_prssRandProtocol, free_pure]
  rw [sequenceFin_congr_pure _ _ (fun i => (apply_ite pure _ _ _).symm)]
  simp only [pure_bind]
  refine bind_congr' _ fun st => ?_
  rw [prssRandRounds, executeRounds, if_neg (by push Not; exact ⟨i0, hi0, by simp [hi0, Step.isDone]⟩)]
  rw [stepRound, if_pos ⟨⟨i0, hi0, by simp [hi0, Step.callInput]⟩, fun i hi => Or.inl (by simp [hi, Step.callInput])⟩]
  have hin : (fun i => if i ∈ D.1 then none else
      (if i ∈ D.1 then Step.done none else Step.call () fun r => (match r with
        | some prss => (calls.mapM (randCall K { localContext i with prss := prss })).run'
            ⟨fun _ => [], label, 0⟩
        | none => failure).run : Step C E (CallSpec Unit (PrssKeys C)) _).callInput) =
      fun i => if i ∈ D.1 then none else some () := by
    funext i; split_ifs <;> simp [Step.callInput]
  rw [hin]
  erw [runFunctionality_FprssKeys D A st _ (fun i hi => by simp [hi])]
  simp only [bind_assoc, pure_bind, honestStreams, free_sequenceFin]
  refine bind_congr' _ fun term => bind_congr' _ fun pair => bind_congr' _ fun a => ?_
  simp only [executeRounds]
  refine Eq.trans (congrArg (· >>= _) (congrArg OverPermutation.sequenceFin (funext fun j =>
    (?_ : _ = free (if j ∈ honestReceivers D a.2 then
      some <$> liftComp (randStreams K prgBits (dealtPrssKeys term pair j) j label calls) (LocalSpec C)
    else pure none) >>= fun r => pure (Step.done r))))) ?_
  · by_cases hj : j ∈ D.1
    · simp [hj, honestReceivers]
    by_cases ha : j ∈ a.2
    · simp only [hj, ha, ↓reduceIte, not_false_eq_true, and_self, honestReceivers, Finset.mem_filter]
      rw [advance_randCalls]
      simp [map_eq_bind_pure_comp, localContext]
    · simp [hj, ha, honestReceivers, advance_pure]
  · simp only [sequenceFin_bind_pure, bind_assoc, pure_bind, Step.output]

end RealRun

/-! ## The ideal run -/

section IdealRun

variable [SampleableType E] (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party)
  (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)

/-- One call of `F_rand` in the ideal run at round label `ρ`. The simulator computes the known
streams on the counted copy, and `F_rand` samples the fresh values on the free copy. -/
def idealCall (ρ : ℕ) : RandCall → OracleComp (WorldSpec C) (C.Party → Option (RandOutput C E))
  | .elements idx count => do
      let known ← counted (liftComp (liftComp
        (knownStreams D receivers (elementCodec K) term pair ρ idx count) (LocalSpec C)) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin count → E)) (LocalSpec C))
      pure fun i => (frandOut D count known.1 known.2 fresh freshPair i).map Sum.inl
  | .bits idx count => do
      let known ← counted (liftComp (liftComp
        (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C)) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin count → Bit)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin count → Bit)) (LocalSpec C))
      pure fun i => (frandOut D count known.1 known.2 fresh freshPair i).map Sum.inr

/-- The calls of `F_rand` in the ideal run, in order, from round label `ρ`. -/
def idealCalls : ℕ → List RandCall → OracleComp (WorldSpec C) (List (C.Party → Option (RandOutput C E)))
  | _, [] => pure []
  | ρ, call :: calls => do
      let output ← idealCall K D receivers term pair ρ call
      let outputs ← idealCalls (ρ + 1) calls
      pure (output :: outputs)

variable (label : ℕ) (calls : List RandCall)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)

/-- The oracles of the functionality in the ideal run with `prssRandSim`. -/
private def simImpl : QueryImpl (LocalSpec C + (RandLeak →ₒ RandReplies C E))
    (StateT (PrssRandSimState C A.State) (OracleComp (WorldSpec C))) :=
  QueryImpl.add ((fun t => (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) :
      StateT (PrssRandSimState C A.State) (OracleComp (WorldSpec C)) _)) :
        QueryImpl (LocalSpec C) (StateT (PrssRandSimState C A.State) (OracleComp (WorldSpec C))))
    ((fun (l : RandLeak) => (StateT.mk fun st => do
      let (st, r) ← worldRoles.adversary ((prssRandSim K label calls D A).answer st l)
      pure (r, st) : StateT (PrssRandSimState C A.State) (OracleComp (WorldSpec C)) (RandReplies C E))) :
        QueryImpl (RandLeak →ₒ RandReplies C E) (StateT (PrssRandSimState C A.State) (OracleComp (WorldSpec C))))

/-- One call of `F_rand` under `simImpl` is `idealCall`. -/
private theorem simImpl_call (s : PrssRandSimState C A.State) (call : RandCall) (rest : List RandCall)
    (hs : s.calls = call :: rest) :
    (simulateQ (simImpl K D label calls A) (simulateQ callLeaks (((Frand E).sum (Frand Bit)).run D
      fun i => Option.map (fun _ => call.input) (if i ∈ D.1 then none else some (x i))))).run s =
      (fun o => (o, { s with label := s.label + 1, calls := rest })) <$>
        idealCall K D s.receivers s.term s.pair s.label call := by
  have hl : ∀ (l : RandLeak), simImpl K D label calls A (.inr l) = StateT.mk fun st =>
      worldRoles.adversary ((prssRandSim K label calls D A).answer st l) >>= fun p => pure (p.2, p.1) :=
    fun _ => rfl
  -- Each case selects its side of the sum. Then both cases run the same steps.
  rcases call with ⟨idx, count⟩ | ⟨idx, count⟩
  focus
    have hleft : ∀ i, ∀ y ∈ Option.map (fun _ => (RandCall.elements idx count).input)
        (if i ∈ D.1 then none else some (x i)), y.isLeft := by
      intro i; by_cases hi : i ∈ D.1 <;> simp [hi, RandCall.input]
    have hin : (fun i => (Option.map (fun _ => (RandCall.elements idx count).input)
        (if i ∈ D.1 then none else some (x i))).bind Sum.getLeft?) =
        fun i => if i ∈ D.1 then none else some count := by
      funext i; by_cases hi : i ∈ D.1 <;> simp [hi, RandCall.input]
    simp only [Functionality.sum]
    rw [if_pos hleft]
    simp only [hin]
  pick_goal 2
  focus
    obtain ⟨i0, hi0⟩ := exists_honest D
    have hleft : ¬ ∀ i, ∀ y ∈ Option.map (fun _ => (RandCall.bits idx count).input)
        (if i ∈ D.1 then none else some (x i)), y.isLeft := fun h => by
      simpa [hi0, RandCall.input] using h i0
    have hright : ∀ i, ∀ y ∈ Option.map (fun _ => (RandCall.bits idx count).input)
        (if i ∈ D.1 then none else some (x i)), y.isRight := by
      intro i; by_cases hi : i ∈ D.1 <;> simp [hi, RandCall.input]
    have hin : (fun i => (Option.map (fun _ => (RandCall.bits idx count).input)
        (if i ∈ D.1 then none else some (x i))).bind Sum.getRight?) =
        fun i => if i ∈ D.1 then none else some count := by
      funext i; by_cases hi : i ∈ D.1 <;> simp [hi, RandCall.input]
    simp only [Functionality.sum]
    rw [if_neg hleft, if_pos hright]
    simp only [hin]
  all_goals
    simp only [simulateQ_map, StateT.run_map]
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    simp only [Frand, sample]
    have hc := firstInput_honest_const D count
    generalize firstInput (fun i => if i ∈ D.1 then none else some count) = c at hc ⊢
    subst hc
    simp only [simulateQ_bind, simulateQ_leak, simulateQ_pure]
    rw [simulateQ_liftComp_prob _ (fun t => rfl), simulateQ_liftComp_prob _ (fun t => rfl)]
    simp only [QueryImpl.apply_compose]
    erw [QueryImpl.add_apply_inr]
    simp only [simulateQ_bind, simulateQ_leak, QueryImpl.apply_compose]
    unfold callLeaks
    erw [QueryImpl.add_apply_inr]
    simp only [simulateQ_bind, simulateQ_leak, hl, StateT.run_bind, StateT.run_mk, prssRandSim, hs, worldRoles,
      idealCall, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure, pure_bind,
      simulateQ_pure, StateT.run_pure, map_bind, StateT.run_lift, map_pure]
    rfl

/-- The calls of `F_rand` under `simImpl` are `idealCalls`. -/
private theorem simImpl_calls (cs : List RandCall) (s : PrssRandSimState C A.State) (hs : s.calls = cs) :
    (simulateQ (simImpl K D label calls A) (cs.mapM fun call => simulateQ callLeaks
      (((Frand E).sum (Frand Bit)).run D
        fun i => Option.map (fun _ => call.input) (if i ∈ D.1 then none else some (x i))))).run s =
      (fun os => (os, { s with label := s.label + cs.length, calls := [] })) <$>
        idealCalls K D s.receivers s.term s.pair s.label cs := by
  induction cs generalizing s with
  | nil => cases s; subst hs; simp [idealCalls]
  | cons call rest ih =>
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      simImpl_call K D label calls A x s call rest hs, bind_map_left, idealCalls, map_bind]
    refine bind_congr fun o => ?_
    rw [ih _ rfl]
    simp only [bind_map_left, StateT.run_pure, map_pure, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1]

/-- The ideal run in normal form. The simulator deals the keys and gets the receivers at its start.
Then each call is one counted reply with the known streams and two free samples of `F_rand`. -/
theorem idealExecution_FrandCalls :
    idealExecution worldRoles.adversary D (FrandCalls calls) (prssRandSim K label calls D A) x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let term ← counted (liftComp (liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C)) (SimulatorSpec C))
      let pair ← counted (liftComp (liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C)) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st fun i =>
        if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) (SimulatorSpec C))
      let outputs ← idealCalls K D a.2 term pair label calls
      pure (a.1, fun i => if i ∉ D.1 ∧ i ∈ a.2 then outputs.mapM (· i) else none)) := by
  have h : idealExecution worldRoles.adversary D (FrandCalls calls) (prssRandSim K label calls D A) x z = (do
      let state ← worldRoles.adversary ((prssRandSim K label calls D A).start (corruptInputs D x) z)
      let p ← (simulateQ (simImpl K D label calls A)
        ((FrandCalls calls).run D fun i => if i ∈ D.1 then none else some (x i))).run state
      let out ← worldRoles.adversary ((prssRandSim K label calls D A).output p.2)
      pure (out, p.1)) := rfl
  rw [h]
  have hl : ∀ (l : RandLeak), simImpl K D label calls A (.inr l) = StateT.mk fun st =>
      worldRoles.adversary ((prssRandSim K label calls D A).answer st l) >>= fun p => pure (p.2, p.1) :=
    fun _ => rfl
  simp only [FrandCalls, simulateQ_bind, StateT.run_bind, simulateQ_leak, hl, StateT.run_mk, prssRandSim,
    worldRoles, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure, pure_bind,
    simulateQ_pure, StateT.run_pure]
  refine bind_congr' _ fun st => bind_congr' _ fun term => bind_congr' _ fun pair => bind_congr' _ fun a => ?_
  rw [simImpl_calls K D label calls A x calls _ rfl]
  simp

end IdealRun

end ThresholdLeanXmssSecurity
