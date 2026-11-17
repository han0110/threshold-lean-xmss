import ThresholdLeanXmssSecurity.Proof.PrssRealRand.NormalForm
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.NoHidden
import ThresholdLeanXmssSecurity.Proof.PrssRealRand.KeysAgree
import ThresholdLeanXmssSecurity.Proof.PrssRand.Streams
import ThresholdLeanXmssSecurity.Proof.SeedGenSecurity
import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# The stream hop of one PRSS setup with the calls of `Rand`

After the setup, the live honest operators draw their streams from their own keys. The ideal run
with `prssRealRandSimulator` emulates the same setup and replies with the known streams.

* `liveStreams_eq_honestStreams` states that the draws of the live honest operators are
  `honestStreams` with the dealt keys `termKeyOf` and `pairKeyOf`, when the keys of the honest
  operators agree.
* `idealExecution_prssRealRand` is the normal form of the ideal run with `prssRealRandSimulator`.
* `streamWorld_liveTail` states that the draws in `streamWorld` and the calls of `F_rand` on the
  hash cache have one law after a setup whose keys agree.
* `prssRealRand_streamHop` is the stream hop. The real run in `streamWorld` and the ideal run differ
  by at most `prssSetupHashError C q`, the bound of the event that the keys of the setup do not
  agree (`prssSetupKeysAgree`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## The keys of the live honest operators -/

section Keys

variable {C : Committee}

/-- The key of term `T` that the first honest holder with an output holds. -/
def termKeyOf (D : C.Coalition) (out : C.Party → Option (Keys C)) (T : C.Term) : HashOutput :=
  ((C.parties.find? fun i => i ∉ D.1 ∧ i ∈ C.holders T ∧ (out i).isSome).bind fun i => (out i).map (·.seed T)).getD 0

/-- Under `KeysAgree`, the key of each honest holder with an output is the key of the first one. -/
theorem seed_eq_termKeyOf (D : C.Coalition) (out : C.Party → Option (Keys C)) (hagree : KeysAgree D out)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (hT : i ∈ C.holders T) (k : Keys C) (hk : out i = some k) :
    k.seed T = termKeyOf D out T := by
  obtain ⟨j, hj, hjp⟩ : ∃ j, C.parties.find? (fun i => i ∉ D.1 ∧ i ∈ C.holders T ∧ (out i).isSome) = some j ∧
      (j ∉ D.1 ∧ j ∈ C.holders T ∧ (out j).isSome) := by
    cases hf : C.parties.find? (fun i => i ∉ D.1 ∧ i ∈ C.holders T ∧ (out i).isSome) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp only [hi, not_false_eq_true, hT, hk, Option.isSome_some, and_self,
          decide_true]) (hf i (by simp only [Committee.parties, List.mem_finRange]))
    | some j => exact ⟨j, rfl, by simpa only [Bool.decide_and, decide_not, Bool.decide_eq_true,
        Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        decide_eq_true_eq] using List.find?_some hf⟩
  obtain ⟨kj, hkj⟩ := Option.isSome_iff_exists.1 hjp.2.2
  rw [termKeyOf, hj, Option.bind_some, hkj, Option.map_some, Option.getD_some]
  exact hagree i j T hi hjp.1 hT hjp.2.1 k hk kj hkj

/-- The key of pair `p` that its first honest endpoint with an output holds. -/
def pairKeyOf (D : C.Coalition) (out : C.Party → Option (Keys C)) (p : C.Pair) : HashOutput :=
  if p.1.1 ∉ D.1 ∧ (out p.1.1).isSome then ((out p.1.1).map (·.pairKey p.1.2)).getD 0
  else ((out p.1.2).map (·.pairKey p.1.1)).getD 0

/-- The key of a pair of a live honest operator is `pairKeyOf`. The pair of two honest operators
needs `PairKeysAgree`. -/
theorem pairKey_eq_pairKeyOf (D : C.Coalition) (out : C.Party → Option (Keys C))
    (hpair : PairKeysAgree D out) (i j : C.Party) (hi : i ∉ D.1) (h : i ≠ j) (k : Keys C)
    (hk : out i = some k) :
    k.pairKey j = pairKeyOf D out (C.pairOf i j h) := by
  unfold pairKeyOf Committee.pairOf
  by_cases hij : i < j
  · simp only [hij, dite_true, hi, not_false_eq_true, hk, Option.isSome_some, and_self, ite_true,
      Option.map_some, Option.getD_some]
  · simp only [hij, dite_false]
    by_cases hj : j ∉ D.1 ∧ (out j).isSome
    · obtain ⟨kj, hkj⟩ := Option.isSome_iff_exists.1 hj.2
      rw [ite_eq_left_of_eq_true _ _ (eq_true hj), hkj, Option.map_some, Option.getD_some]
      exact hpair i j hi hj.1 h k hk kj hkj
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj), hk, Option.map_some, Option.getD_some]

/-- Under the agreement, the keys of a live honest operator are the dealt keys of `termKeyOf` and
`pairKeyOf` at each coordinate that its draws read. -/
theorem carrierPrssKeys_agree (D : C.Coalition) (out : C.Party → Option (Keys C))
    (hagree : KeysAgree D out) (hpair : PairKeysAgree D out) (i : C.Party) (hi : i ∉ D.1) (k : Keys C)
    (hk : out i = some k) :
    (∀ T, i ∈ C.holders T →
      (carrierPrssKeys k).term T = (dealtPrssKeys (termKeyOf D out) (pairKeyOf D out) i).term T) ∧
    (∀ j, j ≠ i → (carrierPrssKeys k).pair j = (dealtPrssKeys (termKeyOf D out) (pairKeyOf D out) i).pair j) :=
  ⟨fun T hT => by
    simp only [carrierPrssKeys, dealtPrssKeys, hT, ite_true]
    exact seed_eq_termKeyOf D out hagree i hi T hT k hk,
  fun j hj => by
    simp only [carrierPrssKeys, dealtPrssKeys, hj, dite_false]
    exact pairKey_eq_pairKeyOf D out hpair i j hi (Ne.symm hj) k hk⟩

/-- The live honest operators, namely the honest operators with an output of the setup. -/
def liveDrawers (D : C.Coalition) (out : C.Party → Option (Keys C)) : Finset C.Party :=
  Finset.univ.filter fun j => j ∉ D.1 ∧ (out j).isSome

theorem findSome?_ite_eq_find?_bind {α β : Type} (p : α → Prop) (f : α → Option β) (l : List α) :
    l.findSome? (fun a => if p a then f a else none) = (l.find? fun a => decide (p a ∧ (f a).isSome)).bind f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a
    · cases hf : f a with
      | none => simp only [List.findSome?_cons, hp, ite_true, hf, ih, List.find?_cons, Option.isSome_none,
          Bool.false_eq_true, and_false, decide_false]
      | some b => simp only [List.findSome?_cons, hp, ite_true, hf, List.find?_cons, Option.isSome_some, and_self,
          decide_true, Option.bind_some]
    · simp only [List.findSome?_cons, hp, ite_false, ih, List.find?_cons, false_and, decide_false]

/-- The term key of `prssRealRandSimulator` on the outputs of `prssSetup` is `termKeyOf` on the
outputs of `setupKeys .prss`. -/
theorem liveTermKey_carrier (D : C.Coalition) (out : C.Party → Option (Keys C)) (T : C.Term) :
    liveTermKey D (fun i => (out i).map carrierPrssKeys) T = termKeyOf D out T := by
  unfold liveTermKey termKeyOf
  have h := findSome?_ite_eq_find?_bind (fun i : C.Party => i ∉ D.1 ∧ i ∈ C.holders T)
    (fun i => (out i).map (·.seed T)) C.parties
  simp only [Option.map_map, Function.comp_def, carrierPrssKeys, Option.isSome_map, and_assoc] at h ⊢
  convert congrArg (·.getD 0) h

/-- The pair key of `prssRealRandSimulator` on the outputs of `prssSetup` is `pairKeyOf` on the
outputs of `setupKeys .prss`. -/
theorem livePairKey_carrier (D : C.Coalition) (out : C.Party → Option (Keys C)) (p : C.Pair) :
    livePairKey D (fun i => (out i).map carrierPrssKeys) p = pairKeyOf D out p := by
  unfold livePairKey pairKeyOf
  simp only [Option.isSome_map, Option.map_map, Function.comp_def, carrierPrssKeys]

/-- The honest operators among the operators with an output are the live drawers. -/
theorem honestReceivers_live (D : C.Coalition) (out : C.Party → Option (Keys C)) :
    honestReceivers D (Finset.univ.filter fun i => (out i).isSome) = liveDrawers D out := by
  ext i
  simp only [honestReceivers, liveDrawers, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

end Keys

/-! ## The draws of the live honest operators -/

section Draws

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [SampleableType E]

/-- Under the agreement, the draws of the live honest operators from their own keys are the draws
of `honestStreams` with the dealt keys of `termKeyOf` and `pairKeyOf`. -/
theorem liveStreams_eq_honestStreams (K : Constants C E)
    (bits : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit)) (D : C.Coalition)
    (out : C.Party → Option (Keys C)) (hagree : KeysAgree D out) (hpair : PairKeysAgree D out)
    (label : ℕ) (calls : List RandCall) :
    liveStreams K bits D out label calls =
      honestStreams K bits (liveDrawers D out) (termKeyOf D out) (pairKeyOf D out) label calls := by
  unfold liveStreams honestStreams
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp only [hj, ite_true, liveDrawers, Finset.mem_filter, Finset.mem_univ, not_true_eq_false,
      false_and, and_false, ite_false]
  · cases hk : out j with
    | none => simp only [hj, ite_false, liveDrawers, Finset.mem_filter, Finset.mem_univ, hk,
        Option.isSome_none, Bool.false_eq_true, and_false]
    | some k =>
      have hmem : j ∈ liveDrawers D out := by
        simp only [liveDrawers, Finset.mem_filter, Finset.mem_univ, hj, not_false_eq_true, hk,
          Option.isSome_some, and_self]
      obtain ⟨ht, hp⟩ := carrierPrssKeys_agree D out hagree hpair j hj k hk
      simp only [hj, ite_false, hmem, ite_true]
      rw [randStreams_congr K bits bits (carrierPrssKeys k) (dealtPrssKeys (termKeyOf D out) (pairKeyOf D out) j) j
        (fun T hT => by rw [ht T hT]) (fun i hi => by rw [hp i hi])]

end Draws

/-! ## The ideal run -/

section Ideal

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

section Calls

variable [SampleableType E] (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party)
  (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)

/-- One call of `F_rand` in the ideal run with `prssRealRandSimulator`, at round label `ρ`. The
simulator computes the known streams on the free copy, and `F_rand` samples the fresh values on the
free copy. -/
def idealCallFree (ρ : ℕ) : RandCall → OracleComp (WorldSpec C) (C.Party → Option (RandOutput C E))
  | .elements idx count => do
      let known ← free (liftComp (knownStreams D receivers (elementCodec K) term pair ρ idx count) (LocalSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin count → E)) (LocalSpec C))
      pure fun i => (frandOut D count known.1 known.2 fresh freshPair i).map Sum.inl
  | .bits idx count => do
      let known ← free (liftComp (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin count → Bit)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin count → Bit)) (LocalSpec C))
      pure fun i => (frandOut D count known.1 known.2 fresh freshPair i).map Sum.inr

/-- The calls of `F_rand` in the ideal run with `prssRealRandSimulator`, in order, from round label `ρ`. -/
def idealCallsFree : ℕ → List RandCall → OracleComp (WorldSpec C) (List (C.Party → Option (RandOutput C E)))
  | _, [] => pure []
  | ρ, call :: calls => do
      let output ← idealCallFree K D receivers term pair ρ call
      let outputs ← idealCallsFree (ρ + 1) calls
      pure (output :: outputs)

end Calls

variable [SampleableType E] (K : Constants C E) (D : C.Coalition) (label : ℕ) (calls : List RandCall)
  (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)

/-- One call of `F_rand` under the oracles of `prssRealRandSimulator` is `idealCallFree`, with the
receivers and the keys of the state of the simulator. -/
theorem simImplOf_prssRealRandSimulator_call (s : PrssRealRandState C A.State) (call : RandCall)
    (rest : List RandCall) (hs : s.calls = call :: rest) :
    (simulateQ (simImplOf (σ := PrssRealRandState C A.State)
      (fun st l => (prssRealRandSimulator K label calls D A).answer st l)) (simulateQ callLeaks
      (((Frand E).sum (Frand Bit)).run D
        fun i => Option.map (fun _ => call.input) (if i ∈ D.1 then none else some (x i))))).run s =
      (fun o => (o, { s with label := s.label + 1, calls := rest })) <$>
        idealCallFree K D (Finset.univ.filter fun i => (s.keys i).isSome) (liveTermKey D s.keys)
          (livePairKey D s.keys) s.label call := by
  rcases call with ⟨idx, count⟩ | ⟨idx, count⟩
  · refine (simImplOf_call D x (fun (st : PrssRealRandState C A.State) l =>
      (prssRealRandSimulator K label calls D A).answer st l) s { s with label := s.label + 1, calls := rest }
      (Sum.inl <$> free (liftComp
      (knownStreams D (Finset.univ.filter fun i => (s.keys i).isSome) (elementCodec K) (liveTermKey D s.keys)
        (livePairKey D s.keys) s.label idx count) (LocalSpec C)))
      (fun _ => by simp [prssRealRandSimulator, hs]) _).trans ?_
    simp [idealCallFree, idealCallOfReply, map_bind]
  · refine (simImplOf_call D x (fun (st : PrssRealRandState C A.State) l =>
      (prssRealRandSimulator K label calls D A).answer st l) s { s with label := s.label + 1, calls := rest }
      (Sum.inr <$> free (liftComp
      (knownStreams D (Finset.univ.filter fun i => (s.keys i).isSome) (bitCodec (E := E)) (liveTermKey D s.keys)
        (livePairKey D s.keys) s.label idx count) (LocalSpec C)))
      (fun _ => by simp [prssRealRandSimulator, hs]) _).trans ?_
    simp [idealCallFree, idealCallOfReply, map_bind]

/-- The calls of `F_rand` under the oracles of `prssRealRandSimulator` are `idealCallsFree`. -/
theorem simImplOf_prssRealRandSimulator_calls (cs : List RandCall) (s : PrssRealRandState C A.State)
    (hs : s.calls = cs) :
    (simulateQ (simImplOf (σ := PrssRealRandState C A.State)
      (fun st l => (prssRealRandSimulator K label calls D A).answer st l)) (cs.mapM fun call =>
      simulateQ callLeaks (((Frand E).sum (Frand Bit)).run D
        fun i => Option.map (fun _ => call.input) (if i ∈ D.1 then none else some (x i))))).run s =
      (fun os => (os, { s with label := s.label + cs.length, calls := [] })) <$>
        idealCallsFree K D (Finset.univ.filter fun i => (s.keys i).isSome) (liveTermKey D s.keys)
          (livePairKey D s.keys) s.label cs := by
  induction cs generalizing s with
  | nil => cases s; subst hs; simp [idealCallsFree]
  | cons call rest ih =>
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      simImplOf_prssRealRandSimulator_call K D label calls A x s call rest hs, bind_map_left, idealCallsFree,
      map_bind]
    refine bind_congr fun o => ?_
    rw [ih _ rfl]
    simp only [bind_map_left, StateT.run_pure, map_pure, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- The ideal run with `prssRealRandSimulator` is the start of `A`, the emulated PRSS setup, and then
the calls `idealCallsFree` under `liveTermKey` and `livePairKey`, with the operators that have keys as
the receivers. -/
theorem idealExecution_prssRealRand :
    idealExecution (fun oa => oa) D (FrandCalls calls) (prssRealRandSimulator K label calls D A) x z = (do
      let st ← worldRoles.adversary (A.start (corruptInputs D x) z)
      let r ← executePhase worldRoles D A noFunctionality setupRounds st fun i =>
        (prssSetup i : PartyM C E RealSpec (PrssKeys C))
      let outputs ← idealCallsFree K D (Finset.univ.filter fun i => (r.2 i).isSome) (liveTermKey D r.2)
        (livePairKey D r.2) label calls
      pure (r.1, fun i => if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (r.2 i).isSome) then
        outputs.mapM (· i) else none)) := by
  have h : idealExecution (fun oa => oa) D (FrandCalls calls) (prssRealRandSimulator K label calls D A) x z = (do
      let state ← (prssRealRandSimulator K label calls D A).start (corruptInputs D x) z
      let p ← (simulateQ (simImplOf (σ := PrssRealRandState C A.State)
          (fun st l => (prssRealRandSimulator K label calls D A).answer st l))
        ((FrandCalls calls).run D fun i => if i ∈ D.1 then none else some (x i))).run state
      let out ← (prssRealRandSimulator K label calls D A).output p.2
      pure (out, p.1)) := rfl
  rw [h]
  generalize himpl : simImplOf (σ := PrssRealRandState C A.State)
    (fun st l => (prssRealRandSimulator K label calls D A).answer st l) = impl
  have hl : ∀ (l : RandLeak), impl (.inr l) =
      StateT.mk fun st => (prssRealRandSimulator K label calls D A).answer st l >>= fun p => pure (p.2, p.1) :=
    fun _ => himpl ▸ rfl
  simp only [FrandCalls, simulateQ_bind, StateT.run_bind, simulateQ_leak, hl, StateT.run_mk,
    prssRealRandSimulator, bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure]
  refine bind_congr fun st => bind_congr fun r => ?_
  rw [← himpl, simImplOf_prssRealRandSimulator_calls K D label calls A x calls _ rfl]
  simp

end Ideal

/-! ## The draws against the calls of `F_rand` -/

section Tail

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [SampleableType E] (prims : Primitives)
  (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
  (pair : C.Pair → HashOutput)

attribute [local instance] inhabitedField

/-- On the ordinary oracle, a local computation on the free copy runs as on the counted copy. -/
theorem worldAnswer_free_eq_counted {α : Type} (oa : OracleComp (LocalSpec C) α) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (free oa)).run s =
      (simulateQ (worldAnswer prims) (counted (liftComp oa (SimulatorSpec C)))).run s := by
  rw [worldAnswer_counted_local, worldAnswer, simulateQ_free]

theorem worldAnswer_idealCallFree (ρ : ℕ) (call : RandCall) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (idealCallFree K D receivers term pair ρ call)).run s =
      (simulateQ (worldAnswer prims) (idealCall K D receivers term pair ρ call)).run s := by
  cases call <;> simp only [idealCallFree, idealCall, simulateQ_bind, StateT.run_bind] <;>
    rw [worldAnswer_free_eq_counted]

/-- On the ordinary oracle, the calls with the known streams on the free copy run as `idealCalls`. -/
theorem worldAnswer_idealCallsFree (ρ : ℕ) (calls : List RandCall) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (idealCallsFree K D receivers term pair ρ calls)).run s =
      (simulateQ (worldAnswer prims) (idealCalls K D receivers term pair ρ calls)).run s := by
  induction calls generalizing ρ s with
  | nil => rfl
  | cons call calls ih =>
    simp only [idealCallsFree, idealCalls, simulateQ_bind, StateT.run_bind, worldAnswer_idealCallFree, ih]

/-- Under the agreement, the draws of the live honest operators and `Z` in the stream world, from
every hash cache and the empty table, have the law of the calls `idealCallsFree` and `Z` on the
ordinary oracle. The keys are `termKeyOf D out` and `pairKeyOf D out`, and the receivers are the
operators with an output. -/
theorem streamWorld_liveTail (out : C.Party → Option (Keys C)) (hagree : KeysAgree D out)
    (hpair : PairKeysAgree D out) (label : ℕ) (calls : List RandCall) {σ : Type}
    (Z : σ × (C.Party → Option (List (RandOutput C E))) → OracleComp (LocalSpec C) Bool) (st : σ) (s : HashCache C) :
    Prod.fst <$> (simulateQ (streamWorld prims D)
        (free (liveStreams K prgBits D out label calls) >>= fun outputs =>
          worldRoles.adversary (Z (st, outputs)))).run (s, ∅) =ᵈ
      Prod.fst <$> (simulateQ (worldAnswer prims)
        (idealCallsFree K D (Finset.univ.filter fun i => (out i).isSome) (termKeyOf D out)
          (pairKeyOf D out) label calls >>= fun outputs =>
          worldRoles.adversary (Z (st, fun i =>
            if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (out i).isSome) then outputs.mapM (· i) else none)))).run s := by
  rw [liveStreams_eq_honestStreams K prgBits D out hagree hpair label calls, ← honestReceivers_live D out]
  refine (streamHop_tail prims K D _ (termKeyOf D out) (pairKeyOf D out) label calls Z st s).trans ?_
  simp only [simulateQ_bind, StateT.run_bind, worldAnswer_idealCallsFree]
  exact .rfl

end Tail

/-! ## The stream hop -/

section Hop

attribute [local irreducible] MonadAttach.support

/-- Two runs with one prefix `mx` differ by at most the probability of the event `bad` of the
prefix, when their tails give `P` with one probability outside `bad`. -/
theorem abs_prEvent_bind_sub_le {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β) (P : β → Prop)
    (bad : α → Prop) (h : ∀ a, ¬ bad a → Pr{let b ← f a}[P b] = Pr{let b ← g a}[P b]) :
    |(Pr{let b ← mx >>= f}[P b]).toReal - (Pr{let b ← mx >>= g}[P b]).toReal| ≤
      (Pr{let a ← mx}[bad a]).toReal := by
  have h₁ : Pr{let b ← mx >>= f}[P b] ≤ Pr{let b ← mx >>= g}[P b] + Pr{let a ← mx}[bad a] + 0 :=
    prEvent_bind_le_add_of_disagree le_rfl fun a _ ha => by rw [h a ha, add_zero]
  have h₂ : Pr{let b ← mx >>= g}[P b] ≤ Pr{let b ← mx >>= f}[P b] + Pr{let a ← mx}[bad a] + 0 :=
    prEvent_bind_le_add_of_disagree le_rfl fun a _ ha => by rw [h a ha, add_zero]
  rw [add_zero] at h₁ h₂
  have t₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h₁
  have t₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h₂
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at t₁ t₂
  rw [abs_le]
  constructor <;> linarith

variable {C : Committee} {E : Type}

/-- The keys of the honest operators of the setup run agree, but with the chance
`prssSetupHashError C q`. The run is on the ordinary oracle from the empty cache. The budget is the
budget of `A` with any distinguisher. -/
theorem setup_agree_bound (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) {O : Type} (Z : Distinguisher C A.State O) (q : ℕ)
    (hq : IsQueryBounded A Z setupRounds q) :
    (Pr{let a ← (simulateQ (worldAnswer prims) (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)).run ∅}[
      ¬ (KeysAgree D a.1.2 ∧ PairKeysAgree D a.1.2)]).toReal ≤ prssSetupHashError C q := by
  have hq' : IsQueryBounded A (fun _ => pure true : Distinguisher C A.State (Keys C)) setupRounds q := by
    obtain ⟨start, step, final, hsum, hs, hr, ha, -⟩ := hq
    exact ⟨start, step, 0, by omega, hs, hr, ha, fun _ => isQueryBoundP_pure _ _ _⟩
  have h := prssSetupKeysAgree (C := C) (E := E) prims D A x z q hq'
  have e := probEvent_runWorld_fst prims (realExecution D A noFunctionality setupRounds
    (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)
    (fun r => ¬ (KeysAgree D r.2 ∧ PairKeysAgree D r.2))
  rw [StateT.run'_eq, prEvent_map] at e
  rw [setupHashError_prss, e] at h
  exact h

variable [Field E] [Algebra Bit E] (K : Constants C E) (prims : Primitives)

attribute [local instance] inhabitedField

section Suffix

variable (label : ℕ) (calls : List RandCall) (D : C.Coalition) {σ : Type}
  (Z : σ × (C.Party → Option (List (RandOutput C E))) → OracleComp (LocalSpec C) Bool)

/-- The suffix of the real run after the setup. The live honest operators draw their streams in the
stream world, from the cache of the setup and the empty table, and then `Z` runs. -/
def realSuffix (a : (σ × (C.Party → Option (Keys C))) × HashCache C) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (streamWorld prims D)
    (free (liveStreams K prgBits D a.1.2 label calls) >>= fun outputs =>
      worldRoles.adversary (Z (a.1.1, outputs)))).run (a.2, ∅)

/-- The suffix of the ideal run after the setup. The calls `idealCallsFree` run on the ordinary
oracle, from the cache of the setup, and then `Z` runs. -/
def idealSuffix [SampleableType E] (a : (σ × (C.Party → Option (Keys C))) × HashCache C) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (worldAnswer prims)
    (idealCallsFree K D (Finset.univ.filter fun i => (a.1.2 i).isSome) (termKeyOf D a.1.2)
      (pairKeyOf D a.1.2) label calls >>= fun outputs =>
      worldRoles.adversary (Z (a.1.1, fun i =>
        if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (a.1.2 i).isSome) then outputs.mapM (· i) else none)))).run a.2

/-- After a setup whose keys agree, the two suffixes have one law. -/
theorem realSuffix_evalDistEq [SampleableType E] (a : (σ × (C.Party → Option (Keys C))) × HashCache C)
    (hagree : KeysAgree D a.1.2) (hpair : PairKeysAgree D a.1.2) :
    realSuffix K prims label calls D Z a =ᵈ idealSuffix K prims label calls D Z a :=
  streamWorld_liveTail prims K D a.1.2 hagree hpair label calls Z a.1.1 a.2

end Suffix

/-- The real run in the stream world is the run of `setupKeys .prss` on the ordinary oracle, and then
`realSuffix`. -/
theorem streamWorld_prssRealRandGame (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    (simulateQ (streamWorld prims D) (distinguish (realExecution D A noFunctionality setupRounds
        (prssRealRandProtocol K label calls) x z) Z)).run' (∅, ∅) =
      (simulateQ (worldAnswer prims) (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)).run ∅ >>=
        realSuffix K prims label calls D Z := by
  have : Fintype E := Fintype.ofEquiv _ K.encode.symm
  have h : (simulateQ (streamWorld prims D) (distinguish (realExecution D A noFunctionality setupRounds
        (prssRealRandProtocol K label calls) x z) Z)).run (∅, ∅) = _ :=
    simulateQ_prssRealRand K (streamWorld prims D) label calls D A x z Z (∅, ∅)
  rw [StateT.run'_eq, h, streamWorld_setup prims D A x z ∅ ∅]
  simp only [map_bind, bind_map_left]
  refine bind_congr fun a => ?_
  simp only [realSuffix, simulateQ_bind, StateT.run_bind, map_bind]

variable [SampleableType E]

/-- The ideal run is the run of `setupKeys .prss`, then the calls `idealCallsFree` with the keys
`termKeyOf` and `pairKeyOf` and the operators with an output. -/
theorem idealExecution_setupKeys (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux) :
    idealExecution (fun oa => oa) D (FrandCalls calls) (prssRealRandSimulator K label calls D A) x z =
      realExecution D A noFunctionality setupRounds
          (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z >>= fun r =>
        (fun outputs => (r.1, fun i => if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (r.2 i).isSome) then
          outputs.mapM (· i) else none)) <$>
          idealCallsFree K D (Finset.univ.filter fun i => (r.2 i).isSome) (termKeyOf D r.2)
            (pairKeyOf D r.2) label calls := by
  rw [idealExecution_prssRealRand]
  unfold realExecution
  rw [bind_assoc]
  refine bind_congr fun st => ?_
  rw [executePhase_prssSetup D A noFunctionality st, bind_map_left]
  refine bind_congr fun r => ?_
  simp only [Option.isSome_map, funext (liveTermKey_carrier D r.2), funext (livePairKey_carrier D r.2),
    map_eq_bind_pure_comp, Function.comp_def]

/-- The ideal game on the ordinary oracle is the run of `setupKeys .prss`, and then `idealSuffix`. -/
theorem worldAnswer_idealGame (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) :
    (simulateQ (worldAnswer prims) (distinguish (idealExecution (fun oa => oa) D (FrandCalls calls)
        (prssRealRandSimulator K label calls D A) x z) Z)).run' ∅ =
      (simulateQ (worldAnswer prims) (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z)).run ∅ >>=
        idealSuffix K prims label calls D Z := by
  unfold distinguish
  rw [idealExecution_setupKeys K label calls D A x z]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc, bind_map_left]
  refine bind_congr fun a => ?_
  simp only [idealSuffix, simulateQ_bind, StateT.run_bind, map_bind]

/-- The stream hop. The real run of `prssRealRandProtocol` in the stream world and the ideal run of
`FrandCalls calls` with `prssRealRandSimulator` differ by at most `prssSetupHashError C q`. The error
is the event that the keys of the setup do not agree. -/
theorem prssRealRand_streamHop (label : ℕ) (calls : List RandCall) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (List (RandOutput C E))) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    |(Pr{let b ← (simulateQ (streamWorld prims D) (distinguish (realExecution D A noFunctionality setupRounds
        (prssRealRandProtocol K label calls) x z) Z)).run' (∅, ∅)}[b = true]).toReal -
      accepts prims (distinguish (idealExecution (fun oa => oa) D (FrandCalls calls)
        (prssRealRandSimulator K label calls D A) x z) Z)| ≤ prssSetupHashError C q := by
  have hsuffix : ∀ a : (A.State × (C.Party → Option (Keys C))) × HashCache C,
      ¬ ¬ (KeysAgree D a.1.2 ∧ PairKeysAgree D a.1.2) →
      Pr{let b ← realSuffix K prims label calls D Z a}[b = true] =
        Pr{let b ← idealSuffix K prims label calls D Z a}[b = true] := fun a ha =>
    (realSuffix_evalDistEq K prims label calls D Z a (not_not.1 ha).1 (not_not.1 ha).2).prEvent_eq _
  rw [accepts_eq_probOutput, streamWorld_prssRealRandGame K prims, worldAnswer_idealGame K prims label calls D A x z Z]
  exact (abs_prEvent_bind_sub_le _ _ _ _ _ hsuffix).trans (setup_agree_bound prims D A x z Z q hq)

end Hop

end ThresholdLeanXmssSecurity
