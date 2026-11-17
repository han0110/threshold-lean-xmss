import ThresholdLeanXmssSecurity.Proof.SeedGen

/-!
# The games of the setups

This module holds the games of the security proof of a setup. The phase of a game names the setup,
the seed generation or the PRSS setup. The module also holds the query bounds of `seedGenSimulator`
and `prssSetupSimulator`, and the two ends of each claim.

* `SeedGenSecurityStatement` reduces to its distance half `SeedGenSecurityDistance`.
  `seedGenSimulator_queryBound` gives the query half.
* `setupCommonGame` is the common game of a setup. `setupCommonGame_seedGen_ideal` and
  `setupCommonGame_prss_ideal` give its ideal end for each phase.
* The other lemmas concern the games of the distance of a setup (CDG+18).
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

/-- The derivations of `P` in a setup, one in the seed generation and none in the PRSS setup. -/
def parameterCount (phase : Phase) : ℕ := if phase = .seedGen then 1 else 0

/-- The honest points of `H` in a setup of `phase`. -/
def setupSecrets (phase : Phase) (C : Committee) : ℕ :=
  C.n * (parameterCount phase + termCount C + C.n) + parameterCount phase + termCount C + C.n.choose 2 + C.n ^ 2

/-- The birthday bound of a setup of `phase`. -/
def setupHashError (phase : Phase) (C : Committee) (q : ℕ) : ℝ := ((q + setupSecrets phase C) ^ 2 : ℕ) / 2 ^ 256

/-- The programming queries of the simulator of a setup of `phase`. -/
def setupOverhead (phase : Phase) (C : Committee) : ℕ := parameterCount phase + termCount C + C.n ^ 2

theorem setupSecrets_seedGen (C : Committee) : setupSecrets .seedGen C = seedGenSecrets C := by
  simp [setupSecrets, parameterCount, seedGenSecrets]

theorem setupSecrets_prss (C : Committee) : setupSecrets .prss C = prssSetupSecrets C := by
  simp [setupSecrets, parameterCount, prssSetupSecrets]

theorem setupHashError_seedGen (C : Committee) (q : ℕ) : setupHashError .seedGen C q = seedGenHashError C q := by
  rw [setupHashError, setupSecrets_seedGen, seedGenHashError]

theorem setupHashError_prss (C : Committee) (q : ℕ) : setupHashError .prss C q = prssSetupHashError C q := by
  rw [setupHashError, setupSecrets_prss, prssSetupHashError]

attribute [local instance] Classical.propDecidable

section SeedGenSecurity

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The start of `seedGenSimulator` observes the start of `A`. -/
theorem seedGenSimulator_start (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (corrupt : C.Party → Option Unit) (z : Aux) :
    (seedGenSimulator D A).start corrupt z = (do
      let (state, log) ← observe (A.start corrupt z)
      pure ⟨state, log, corrupt⟩) := rfl

/-- The answer of `seedGenSimulator` in full. -/
theorem seedGenSimulator_answer (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (st : SimulatorState C Unit A.State) (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) :
    (seedGenSimulator D A).answer st (parameter, corrupt) = (do
      let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
      let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
      let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
      let log := st.log ++ calls
      let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
      let view := fun (i j : C.Party) =>
        if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
      let h₀ := firstHonest Finset.univ
      let high ← free (liftComp ($ᵗ HashOutput) _)
      let _ ← program (.derive .seedGen .parameter (C.parties.map fun j => (view h₀ j).parameter))
        (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
      let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
        | some j =>
          let i := firstHonest (C.holders T)
          program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
            (((corrupt j).map (·.seed T)).getD 0)
        | none => pure true
      let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
        if h : j ∈ D.1 ∧ i ∉ D.1 then
          let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
          program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
            (((corrupt j).map (·.pairKey i)).getD 0)
        else pure true
      let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
      pure (⟨state, log ++ rest, st.corrupt⟩, Finset.univ.filter fun i => (keys i).isSome)) := by
  simp only [seedGenSimulator, setupSimulator, ite_true, Option.map_map, bind_assoc]
  rfl

/-- The output of `seedGenSimulator` is the state of `A`. -/
theorem seedGenSimulator_output (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (st : SimulatorState C Unit A.State) : (seedGenSimulator D A).output st = pure st.adversary := rfl

/-- A simulation into the state of the ideal run whose local queries go to the free copy costs
nothing on a lifted sampling. -/
theorem costLe_stateT_liftComp {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ (t : (LocalSpec C).Domain) st,
      (impl (.inl t)).run st = (fun a => (a, st)) <$> free (OracleComp.lift (OracleSpec.query t)))
    (p : ProbComp α) : ∀ st, CostLe prims ((simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R)))).run st) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => intro st; exact CostLe.pure prims _
  | query_bind t k ih =>
    intro st
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have : simulateQ impl (liftComp (liftM (OracleSpec.query t) : ProbComp _) (LocalSpec C + (L →ₒ R))) =
        impl (.inl (.inl t)) := by
      rw [liftComp_query]
      exact (simulateQ_query _ _).trans (id_map _)
    rw [this]
    erw [himpl (.inl t) st]
    exact ((CostLe.map prims _ (CostLe.free prims _)).bind prims
      fun (p : unifSpec.Range t × σ) => ih p.1 p.2).mono prims (by simp)

/-- One answer of the simulator of a setup costs one round of the adversary, the programming queries,
and two more rounds. -/
theorem costLe_setupSimulator_answer (phase : Phase) {O L : Type}
    (setup : C.Party → Parts C → PartyM C E RealSpec O)
    (dealt : L → PublicParameter × (C.Party → Option (PrssKeys C)))
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (st : (setupSimulator phase setup dealt D A).State) (l : L) :
    CostLe prims ((setupSimulator phase setup dealt D A).answer st l)
      (step + (parameterCount phase + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) +
        (setupRounds - 1) * step)))) := by
  unfold setupSimulator
  dsimp only
  generalize dealt l = pc
  rcases pc with ⟨parameter, corrupt⟩
  dsimp only
  refine ((CostLe.free prims _).bind prims fun parts => ?_).mono prims (Nat.zero_add _).le
  refine ((CostLe.sequenceFin prims _ fun i => ?_).bind prims fun steps => ?_).mono prims (Nat.zero_add _).le
  · split_ifs
    · exact CostLe.pure prims _
    · exact CostLe.free prims _
  refine (CostLe.stepRound_observed prims D A step hround _ _).bind prims fun r => ?_
  rcases r with ⟨⟨state, steps, sent⟩, calls⟩
  dsimp only
  refine CostLe.bind prims (n := parameterCount phase) ?_ fun _ => ?_
  · cases phase
    · simp only [ite_true, parameterCount]
      exact ((CostLe.free prims _).bind prims fun high => CostLe.program prims _ _).mono prims (Nat.zero_add _).le
    · simp only [reduceCtorEq, ite_false, parameterCount]
      exact CostLe.pure prims _
  refine (CostLe.mapM prims _ 1 C.terms fun T _ => ?_).bind prims fun _ => ?_
  · split
    · exact CostLe.program prims _ _
    · exact (CostLe.pure prims _).mono prims (Nat.zero_le _)
  refine (CostLe.mapM prims _ (C.parties.length * 1) C.parties fun j _ =>
    CostLe.mapM prims _ 1 C.parties fun i _ => ?_).bind prims fun _ => ?_
  · by_cases hji : j ∈ D.1 ∧ i ∉ D.1
    · rw [dif_pos hji]; exact CostLe.program prims _ _
    · rw [dif_neg hji]; exact (CostLe.pure prims _).mono prims (Nat.zero_le _)
  refine ((CostLe.executeRounds_observed prims D A step hround (setupRounds - 1) _ _).bind prims fun r => ?_).mono
    prims (Nat.add_zero _).le
  rcases r with ⟨⟨state, keys⟩, rest⟩
  exact CostLe.pure prims _

theorem seedGenSimulator_queryBound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D FseedGen
      (seedGenSimulator D A) x z) Z)) (q + seedGenOverhead C) := by
  obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hstart : CostLe prims ((seedGenSimulator D A).start (corruptInputs D x) z) start :=
    ((CostLe.observe prims _ start (hs _ _)).bind prims fun _ => CostLe.pure prims _).mono prims (by simp)
  have hanswer := costLe_setupSimulator_answer prims .seedGen (seedGenWith (E := E) (G := RealSpec))
    (fun l : PublicParameter × (C.Party → Option (Keys C)) => (l.1, fun j => (l.2 j).map fun k => ⟨k.seed, k.pairKey⟩))
    D A step hr
  set M := step + (parameterCount .seedGen + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) +
    (setupRounds - 1) * step))) with hM
  refine CostLe.mono prims (CostLe.bind prims hstart (m := 0 + ((M + 0) + (0 + (0 + (0 + final))))) fun st => ?_) ?_
  · unfold FseedGen
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine (costLe_stateT_liftComp prims _ ?himpl _ st).bind prims fun p => ?_
    case himpl => intro t st; rfl
    refine (costLe_simulateQ_leak prims _ _ _ ?hl).bind prims fun r => ?_
    case hl => exact (hanswer _ _).bind prims fun _ => CostLe.pure prims _
    refine (CostLe.pure prims _).bind prims fun out => ?_
    refine (CostLe.pure prims _).bind prims fun o => ?_
    refine (CostLe.pure prims _).bind prims fun r' => ?_
    exact CostLe.of_counted prims _ _ (hz _)
  · have hterms : C.terms.length = C.n.choose (C.t - 1) := by
      rw [Committee.terms, Finset.length_toList, Finset.card_univ, card_term]
    have hparties : C.parties.length = C.n := by simp [Committee.parties]
    rw [hM, hterms, hparties]
    unfold seedGenOverhead termCount
    simp only [setupRounds, parameterCount, ite_true] at hsum ⊢
    nlinarith [hsum]

theorem prssSetupSimulator_queryBound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (PrssKeys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D FprssKeys
      (prssSetupSimulator D A) x z) Z)) (q + prssSetupOverhead C) := by
  obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hstart : CostLe prims ((prssSetupSimulator D A).start (corruptInputs D x) z) start :=
    ((CostLe.observe prims _ start (hs _ _)).bind prims fun _ => CostLe.pure prims _).mono prims (by simp)
  have hanswer := costLe_setupSimulator_answer prims .prss (prssSetupWith (E := E) (G := RealSpec))
    (fun corrupt : C.Party → Option (PrssKeys C) => ((0 : PublicParameter), corrupt)) D A step hr
  set M := step + (parameterCount .prss + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) +
    (setupRounds - 1) * step))) with hM
  refine CostLe.mono prims (CostLe.bind prims hstart (m := 0 + (0 + ((M + 0) + (0 + (0 + (0 + final)))))) fun st => ?_) ?_
  · unfold FprssKeys sample
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine (costLe_stateT_liftComp prims _ ?himpl _ st).bind prims fun p => ?_
    case himpl => intro t st; rfl
    refine (costLe_stateT_liftComp prims _ ?himpl' _ p.2).bind prims fun p' => ?_
    case himpl' => intro t st; rfl
    refine (costLe_simulateQ_leak prims _ _ _ ?hl).bind prims fun r => ?_
    case hl => exact (hanswer _ _).bind prims fun _ => CostLe.pure prims _
    refine (CostLe.pure prims _).bind prims fun out => ?_
    refine (CostLe.pure prims _).bind prims fun o => ?_
    refine (CostLe.pure prims _).bind prims fun r' => ?_
    exact CostLe.of_counted prims _ _ (hz _)
  · have hterms : C.terms.length = C.n.choose (C.t - 1) := by
      rw [Committee.terms, Finset.length_toList, Finset.card_univ, card_term]
    have hparties : C.parties.length = C.n := by simp [Committee.parties]
    rw [hM, hterms, hparties]
    unfold prssSetupOverhead termCount
    simp only [setupRounds, parameterCount, reduceCtorEq, ite_false] at hsum ⊢
    nlinarith [hsum]

/-- The distance half of `SeedGenSecurityStatement`. -/
def SeedGenSecurityDistance (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z) Z)| ≤
        seedGenHashError C q

/-- `SeedGenSecurityStatement` from its distance half. The query half is `seedGenSimulator_queryBound`. -/
theorem seedGenSecurity_of_distance (h : SeedGenSecurityDistance (C := C) (E := E) prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  fun D A x z Z q _ hq => ⟨seedGenSimulator_queryBound prims D A x z Z q hq, h D A x z Z q hq⟩

end SeedGenSecurity

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The complete private transcript of one round, used only to define bad events. -/
structure SeedGenRoundTrace (C : Committee) (E : Type) where
  queries : (WorldSpec C).QueryLog
  outgoing : C.Party → Mail C E
  sent : C.Party → Mail C E

structure SeedGenRealTrace (C : Committee) (E : Type) where
  start : (WorldSpec C).QueryLog
  honestStart : (WorldSpec C).QueryLog
  rounds : List (SeedGenRoundTrace C E)
  final : (WorldSpec C).QueryLog

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Programming a fresh random-oracle input inserts the prescribed answer. -/
theorem programAnswer_run_fresh {q : Query C} (hfixed : ¬ IsFixed q)
    (s : HashCache C) (hfresh : s q = none) (y : HashOutput) :
    (programAnswer (q, y)).run s = pure (true, s.cacheQuery q y) := by
  change ¬ (∃ input, q = .hash input ∧ MpcInput input) at hfixed
  simp [programAnswer, StateT.run_bind, StateT.run_get, hfixed, hfresh, StateT.run_set]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- A search returning a unique value finds it as soon as any matching entry is present. -/
theorem findSome_eq_of_unique {α β : Type} (f : α → Option β) (l : List α) (b : β)
    (hex : ∃ a ∈ l, f a = some b)
    (hunique : ∀ a ∈ l, ∀ b', f a = some b' → b' = b) : l.findSome? f = some b := by
  cases h : l.findSome? f with
  | none =>
    obtain ⟨a, ha, hf⟩ := hex
    have hn := List.findSome?_eq_none_iff.mp h a ha
    rw [hf] at hn
    contradiction
  | some b' =>
    obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
    rw [hunique a ha b' hf]

/-- If the actual opening was observed before the commitment was sent, and no other observed
opening has the same commitment, extraction returns exactly that opening. -/
theorem extractReveal_eq_of_unique (phase : Phase) (calls : CallLog C) (sent : C.Party → Mail C E)
    (j i : C.Party) (reveal : List HashOutput) (value : HashOutput)
    (hcall : (.commit phase j i reveal, value) ∈ calls)
    (hsent : [value] = Msg.hashesOf (sent j i))
    (hunique : ∀ reveal' value', (.commit phase j i reveal', value') ∈ calls →
      [value'] = Msg.hashesOf (sent j i) → reveal' = reveal) :
    extractReveal phase calls sent j i = reveal := by
  unfold extractReveal
  have h := findSome_eq_of_unique
    (fun (q, out) => match q with
      | .commit phase' j' i' opening =>
          if phase' = phase ∧ j' = j ∧ i' = i ∧ [out] = Msg.hashesOf (sent j i) then some opening else none
      | _ => none) calls reveal
    (by exact ⟨(.commit phase j i reveal, value), hcall, by simp [hsent]⟩)
    (by
      rintro ⟨q, out⟩ hmem opening hmatch
      cases q <;> simp only at hmatch
      all_goals try contradiction
      rename_i phase' j' i' opening'
      split_ifs at hmatch with hm
      obtain ⟨rfl, rfl, rfl, hout⟩ := hm
      exact (Option.some.inj hmatch).symm.trans (hunique opening' out hmem hout))
  exact congrArg (fun o : Option (List HashOutput) => o.getD []) h

/-- Every term has exactly `t` holders. -/
theorem seedGen_card_holders (C : Committee) (T : C.Term) : (C.holders T).card = C.t := by
  rw [Committee.holders, Finset.card_compl, Fintype.card_fin, T.2]
  have := C.one_le_t
  unfold Committee.n
  omega

/-- The honest sender's fields in a received reveal agree with the sampled fields. -/
theorem setupView_honest_sender (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (i j : C.Party) (hj : j ∉ D.1) :
    setupView phase i (parts i) (revealed i) j = honestView (E := E) phase parts i j := by
  by_cases hji : j = i
  · subst j; simp [setupView, honestView]
  · rw [honestView_ne _ _ hji]
    simp only [setupView, if_neg hji, hreceived i j hj hji]

def setupPairViewInput (phase : Phase) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (i : C.Party) (p : C.Pair) : Query C :=
  let view := setupView phase i (parts i) (revealed i)
  .derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem D_sharedQueries_at (prims : Primitives) (h : Query C → HashOutput)
    (phase : Phase) (i j : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    (D prims h (sharedQueries phase i keys)).getD j.val 0 =
      h (.sharedKeys phase ((sharedTerms i j).map keys.2.1)) := by
  simp only [sharedQueries, D_mapM, D_hashQuery]
  exact getD_parties _ _ j

/-- Equal honest echoes force all their shared seeds, and in the seed generation also equal
parameters, outside a collision at the two shared-key inputs. This does not require the echo sender
to receive an output. -/
theorem setup_echo_agreement (phase : Phase) (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hecho : echoOf phase ki (D prims h (sharedQueries phase i ki)) j =
      echoOf phase kj (D prims h (sharedQueries phase j kj)) i)
    (hnocollision :
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys (C := C) phase ((sharedTerms j i).map kj.2.1)) :
    (phase = .seedGen → ki.1 = kj.1) ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T := by
  have hs : (phase = .seedGen → ki.1 = kj.1) ∧
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) := by
    cases phase
    · simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq, and_true,
        D_sharedQueries_at] at hecho
      exact ⟨fun _ => hecho.1, hecho.2⟩
    · simp only [echoOf, reduceCtorEq, ite_false, List.nil_append, List.cons.injEq, and_true,
        D_sharedQueries_at] at hecho
      exact ⟨(fun hp => nomatch hp), hecho⟩
  refine ⟨hs.1, ?_⟩
  have hlists := (Query.sharedKeys.inj (hnocollision hs.2)).2
  rw [sharedTerms_comm j i] at hlists
  intro T hi hj
  apply List.map_eq_map_iff.mp hlists T
  simp [sharedTerms, Committee.terms, hi, hj]

/-- The accepting party's echo check compares it with every honest sender, including a sender
that aborts only after sending the echo. -/
theorem setup_echoCheck_agreement (phase : Phase) (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party) (hji : j ≠ i)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (received : Mail C E)
    (hsender : received j = some (.hashes (echoOf phase kj (D prims h (sharedQueries phase j kj)) i)))
    (hcheck : echoCheck phase i ki (D prims h (sharedQueries phase i ki)) received)
    (hnocollision :
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys (C := C) phase ((sharedTerms j i).map kj.2.1)) :
    (phase = .seedGen → ki.1 = kj.1) ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T := by
  apply setup_echo_agreement phase prims h i j ki kj _ hnocollision
  have heq := hcheck j hji
  simpa only [hsender, Msg.hashesOf] using heq.symm

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- An echo to a corrupt recipient contains only terms known to the coalition. -/
theorem seedGen_sharedTerms_known (D : C.Coalition) (i j : C.Party) (hj : j ∈ D.1)
    (T : C.Term) (hT : T ∈ sharedTerms i j) : KnownTo D.1 T := by
  have hm := (List.mem_filter.mp hT).2
  exact ⟨j, hj, (of_decide_eq_true hm).2⟩

/-- Changing only hidden seeds preserves every echo input sent to a corrupt recipient. -/
theorem setup_sharedInput_known (phase : Phase) (D : C.Coalition) (i j : C.Party) (hj : j ∈ D.1)
    (s s' : C.Term → HashOutput) (hs : ∀ T, KnownTo D.1 T → s T = s' T) :
    Query.sharedKeys (C := C) phase ((sharedTerms i j).map s) =
      Query.sharedKeys phase ((sharedTerms i j).map s') := by
  congr 1
  exact List.map_congr_left fun T hT => hs T (seedGen_sharedTerms_known D i j hj T hT)

/-- On two honest endpoints, the complete seed comparison reduces to known seeds when hidden
terms are internally consistent. This allows the dealer's hidden seeds to replace emulated ones. -/
theorem seedGen_sharedAgreement_iff_known (D : C.Coalition) (i j : C.Party)
    (s s' : C.Term → HashOutput)
    (hhidden : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → s T = s' T) :
    (∀ T, i ∈ C.holders T → j ∈ C.holders T → s T = s' T) ↔
      (∀ T, KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → s T = s' T) := by
  constructor
  · exact fun h T _ => h T
  · intro h T hi hj
    by_cases hknown : KnownTo D.1 T
    · exact h T hknown hi hj
    · exact hhidden T hknown hi hj

/-- Outside a collision, equality of honest echoes is exactly equality of the seeds shared by the
endpoints, and in the seed generation also of the full parameter. -/
theorem setup_echo_eq_iff (phase : Phase) (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hnocollision :
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj.2.1)) :
    (echoOf phase ki (D prims h (sharedQueries phase i ki)) j =
      echoOf phase kj (D prims h (sharedQueries phase j kj)) i) ↔
    ((phase = .seedGen → ki.1 = kj.1) ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T) := by
  constructor
  · exact fun heq => setup_echo_agreement phase prims h i j ki kj heq hnocollision
  · rintro ⟨hp, hs⟩
    have hmap : (sharedTerms i j).map ki.2.1 = (sharedTerms i j).map kj.2.1 :=
      List.map_congr_left fun T hT => by
        have hm := of_decide_eq_true (List.mem_filter.mp hT).2
        exact hs T hm.1 hm.2
    cases phase
    · simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq, and_true,
        D_sharedQueries_at, hp rfl, true_and]
      rw [sharedTerms_comm j i, hmap]
    · simp only [echoOf, reduceCtorEq, ite_false, List.nil_append, List.cons.injEq, and_true,
        D_sharedQueries_at]
      rw [sharedTerms_comm j i, hmap]

/-- Replacing coherent hidden seeds preserves the equality of two honest echoes. -/
theorem setup_echo_eq_hidden_invariant (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h h' : Query C → HashOutput) (i j : C.Party)
    (ki kj ki' kj' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hpi : ki.1 = ki'.1) (hpj : kj.1 = kj'.1)
    (hki : ∀ T, KnownTo coalition.1 T → ki.2.1 T = ki'.2.1 T)
    (hkj : ∀ T, KnownTo coalition.1 T → kj.2.1 T = kj'.2.1 T)
    (hhidden : ∀ T, ¬ KnownTo coalition.1 T → i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T)
    (hhidden' : ∀ T, ¬ KnownTo coalition.1 T → i ∈ C.holders T → j ∈ C.holders T → ki'.2.1 T = kj'.2.1 T)
    (hnocollision :
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj.2.1))
    (hnocollision' :
      h' (.sharedKeys phase ((sharedTerms i j).map ki'.2.1)) =
        h' (.sharedKeys phase ((sharedTerms j i).map kj'.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki'.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj'.2.1)) :
    (echoOf phase ki (D prims h (sharedQueries phase i ki)) j =
      echoOf phase kj (D prims h (sharedQueries phase j kj)) i) ↔
    (echoOf phase ki' (D prims h' (sharedQueries phase i ki')) j =
      echoOf phase kj' (D prims h' (sharedQueries phase j kj')) i) := by
  rw [setup_echo_eq_iff phase prims h i j ki kj hnocollision,
    setup_echo_eq_iff phase prims h' i j ki' kj' hnocollision',
    seedGen_sharedAgreement_iff_known coalition i j ki.2.1 kj.2.1 hhidden,
    seedGen_sharedAgreement_iff_known coalition i j ki'.2.1 kj'.2.1 hhidden', hpi, hpj]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro T
  apply forall_congr'
  intro hT
  rw [hki T hT, hkj T hT]

/-- The derived keys of an honest operator of the PRSS setup agree on the first key, which is `0`.
So a user of `setup_echo_agreement` has the equality of the first keys in each phase. -/
theorem setup_firstKey_agreement (phase : Phase) (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party) (vi vj : C.Party → Parts C)
    (hseed : phase = .seedGen → (D prims h (deriveKeys phase i vi)).1 = (D prims h (deriveKeys phase j vj)).1) :
    (D prims h (deriveKeys phase i vi)).1 = (D prims h (deriveKeys phase j vj)).1 := by
  cases phase
  · exact hseed rfl
  · rw [D_deriveKeys, D_deriveKeys]
    rfl

/-- Every hidden term uses the honest parts, in every holder's view, even when the corrupt
operators send inconsistent openings for other terms. -/
theorem setup_hiddenTerm_input (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (T : C.Term) (hhidden : ¬ KnownTo coalition.1 T) (i : C.Party) (hi : i ∈ C.holders T) :
    Query.derive (C := C) phase .term
      ((C.parties.filter (· ∈ C.holders T)).map fun j =>
        (setupView phase i (parts i) (revealed i) j).term T) =
      termInput phase parts T := by
  unfold termInput
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j ∈ C.holders T := of_decide_eq_true (List.mem_filter.mp hj).2
  have hjhonest : j ∉ coalition.1 := fun hc => hhidden ⟨j, hc, hjT⟩
  rw [setupView_honest_sender phase coalition parts revealed hreceived i j hjhonest]
  exact honestView_term phase parts hjT hi

/-- The actual derived hidden seed is common to all its honest holders. -/
theorem setup_hiddenTerm_derived (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (T : C.Term) (hhidden : ¬ KnownTo coalition.1 T) (i : C.Party) (hi : i ∈ C.holders T) :
    (D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i)))).2.1 T =
      h (termInput phase parts T) := by
  rw [D_deriveKeys]
  simp only [hi, if_true]
  rw [setup_hiddenTerm_input phase coalition parts revealed hreceived T hhidden i hi]

/-- The echo-round inbox, including the abort frame of any honest operator that failed earlier. -/
def setupEchoInbox (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Mail C E := fun j =>
  if j ∈ coalition.1 then sent j i else
  if active j then echoOutbox phase j (keys j) (D prims h (sharedQueries phase j (keys j))) i
  else some .abort

/-- The last local continuation of a setup makes no oracle calls. -/
theorem advance_setupEchoResume (phase : Phase) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (received : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun inbox =>
      require (echoCheck phase i keys shared inbox) >>= fun _ => pure (keysOf keys)) received) =
      pure (Step.done (if (C.parties.any fun j => Msg.isAbort (received j)) then none else
        if echoCheck phase i keys shared received then some (keysOf keys) else none)) := by
  unfold exchangeResume
  split_ifs with ha hc
  · rfl
  · rw [advance_require_bind, if_pos hc, advance_run_pure]
  · rw [advance_require_bind, if_neg hc]

/-- Aborts in the last inbox do not depend on the keys or the oracle table. -/
theorem setupEchoInbox_isAbort (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h h' : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i j : C.Party) :
    Msg.isAbort (setupEchoInbox phase prims coalition active sent h keys i j) =
      Msg.isAbort (setupEchoInbox phase prims coalition active sent h' keys' i j) := by
  unfold setupEchoInbox
  split_ifs <;> simp only [isAbort_echoOutbox]

/-- A setup step waiting for the echo, or the persistent abort of an earlier round. -/
def setupEchoStep (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Step C E RealSpec (Keys C) :=
  if i ∈ coalition.1 ∨ ¬ active i then .done none else
    .wait (echoOutbox phase i (keys i) (D prims h (sharedQueries phase i (keys i))))
      (exchangeResume fun inbox => require
        (echoCheck phase i (keys i) (D prims h (sharedQueries phase i (keys i))) inbox) >>=
        fun _ => pure (keysOf (keys i)))

/-- The concrete inbox used by `stepRound` is the echo inbox above. -/
theorem roundInbox_setupEchoStep (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (i : C.Party) :
    roundInbox coalition sent (setupEchoStep phase prims coalition active h keys) i =
      setupEchoInbox phase prims coalition active sent h keys i := by
  funext j
  unfold roundInbox setupEchoStep setupEchoInbox
  by_cases hj : j ∈ coalition.1
  · simp only [hj, if_true]
  · simp only [hj, false_or, if_false]
    by_cases ha : active j <;> simp [ha, Step.delivered]

/-- The possible output of the final local step. -/
def setupEchoOutput (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Option (Keys C) :=
  if i ∈ coalition.1 ∨ ¬ active i then none else
    let inbox := setupEchoInbox phase prims coalition active sent h keys i
    if C.parties.any fun j => Msg.isAbort (inbox j) then none else
      if echoCheck phase i (keys i) (D prims h (sharedQueries phase i (keys i))) inbox
      then some (keysOf (keys i)) else none

/-- One concrete echo round, with all honest local continuations reduced to pure outputs. -/
theorem stepRound_setupEchoStep (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    stepRound worldRoles coalition A noFunctionality state (setupEchoStep phase prims coalition active h keys) =
      (do
        let (state, sent) ← worldRoles.adversary (A.round state fun c i =>
          if c ∈ coalition.1 ∧ i ∉ coalition.1 then
            (setupEchoStep phase prims coalition active h keys i).outbox c else none)
        pure (state, (fun i => Step.done (setupEchoOutput phase prims coalition active sent h keys i)), sent)) := by
  unfold stepRound
  have hc : ¬ (∃ i, i ∉ coalition.1 ∧
      (setupEchoStep phase prims coalition active h keys (E := E) i).callInput.isSome) := by
    simp only [callInput_real, Option.isSome_none, Bool.false_eq_true, and_false, exists_false, not_false_eq_true]
  rw [if_neg (fun h => hc h.1)]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only
  trans (OverPermutation.sequenceFin (fun i =>
    (pure (Step.done (setupEchoOutput phase prims coalition active sent h keys i)) :
      OracleComp (WorldSpec C) (Step C E RealSpec (Keys C)))) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    by_cases hi : i ∈ coalition.1 ∨ ¬ active i
    · simp only [setupEchoStep, if_pos hi, setupEchoOutput]
    · have hih : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      rw [show setupEchoStep phase prims coalition active h keys (E := E) i = _ from if_neg hi]
      simp only [if_neg hih]
      change worldRoles.honest (advance (exchangeResume _
        (roundInbox coalition sent (setupEchoStep phase prims coalition active h keys) i))) = _
      rw [roundInbox_setupEchoStep, advance_setupEchoResume]
      simp only [worldRoles, free, setupEchoOutput, if_neg hi]
      exact simulateQ_pure _ _
  · rw [sequenceFin_pure, pure_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- A programming attempt at an already cached input leaves the cache unchanged. -/
theorem programAnswer_run_cached (q : Query C) (s : HashCache C) (y v : HashOutput)
    (hs : s q = some v) : (programAnswer (q, y)).run s = pure (false, s) := by
  simp [programAnswer, StateT.run_bind, StateT.run_get, hs, StateT.run_pure]

/-- A uniformly programmed value that is not retained. -/
def uniformProgram (q : Query C) : StateT (HashCache C) ProbComp Unit := do
  let y ← StateT.lift ($ᵗ HashOutput)
  let _ ← programAnswer (q, y)
  pure ()

/-- Even at a cached input, an unused uniform programming attempt has the same cache distribution
as an unused ordinary hash query. Freshness is needed only when the sampled value is retained. -/
theorem evalDist_uniformProgram (prims : Primitives) (q : Query C) (hq : ¬ IsFixed q)
    (s : HashCache C) :
    (uniformProgram q).run s =ᵈ
      (hashAnswer prims q >>= fun _ => pure ()).run s := by
  cases hs : s q with
  | none =>
    simp only [uniformProgram, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
      programAnswer_run_fresh hq s hs, StateT.run_pure]
    rw [hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ hs]
    rfl
  | some v =>
    simp only [uniformProgram, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
      programAnswer_run_cached q s _ v hs, StateT.run_pure,
      hashAnswer_run_cached prims hq hs]
    exact OracleComp.EvalDistEq.bind_const ($ᵗ HashOutput) _

/-- The discarded programming swap is valid before every cache-dependent continuation. -/
theorem evalDist_uniformProgram_bind (prims : Primitives) (q : Query C) (hq : ¬ IsFixed q)
    {α : Type} (k : StateT (HashCache C) ProbComp α) (s : HashCache C) :
    (uniformProgram q >>= fun _ => k).run s =ᵈ
      (hashAnswer prims q >>= fun _ => k).run s := by
  have h := evalDist_run_bind_of_eq (fun _ : Unit => k) s (evalDist_uniformProgram prims q hq s)
  simpa only [bind_assoc, pure_bind] using h

/-- A block of independent programming values. -/
def uniformPrograms : List (Query C) → StateT (HashCache C) ProbComp Unit
  | [] => pure ()
  | q :: qs => uniformProgram q >>= fun _ => uniformPrograms qs

/-- The uniform programming block is distributionally the corresponding block of discarded
ordinary queries, including the cache and every continuation. Inputs need not be distinct. -/
theorem evalDist_uniformPrograms_bind (prims : Primitives) (qs : List (Query C))
    (hq : ∀ q ∈ qs, ¬ IsFixed q) {α : Type} (k : StateT (HashCache C) ProbComp α)
    (s : HashCache C) :
    (uniformPrograms qs >>= fun _ => k).run s =ᵈ
      ((qs.mapM (hashAnswer prims)) >>= fun _ => k).run s := by
  induction qs generalizing s with
  | nil => simp [uniformPrograms]
  | cons q qs ih =>
    simp only [uniformPrograms, List.mapM_cons, bind_assoc, pure_bind]
    refine (evalDist_uniformProgram_bind prims q (hq q (List.mem_cons_self ..)) _ s).trans ?_
    apply evalDist_run_bind_congr
    intro _ s'
    exact ih (fun r hr => hq r (List.mem_cons_of_mem q hr)) s'

/-- The free random-oracle computations represented by a list of inputs. -/
theorem simulateQ_localAnswer_hashes (prims : Primitives) (qs : List (Query C)) :
    simulateQ (localAnswer prims) (liftComp (qs.mapM hashQuery) (LocalSpec C)) =
      qs.mapM (hashAnswer prims) := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, simulateQ_bind,
      simulateQ_pure, simulateQ_localAnswer_hash, ih]

/-- With no retained programming values, the entire block can be removed before any local
continuation. This includes arbitrary future counted adversary and distinguisher computations
once their counted/free wrappers have been erased. -/
theorem evalDist_uniformPrograms_prepend (prims : Primitives) (qs : List (Query C))
    (hq : ∀ q ∈ qs, ¬ IsFixed q) {α : Type} (k : OracleComp (LocalSpec C) α)
    (s : HashCache C) :
    (uniformPrograms qs >>= fun _ => simulateQ (localAnswer prims) k).run' s =ᵈ
      (simulateQ (localAnswer prims) k).run' s := by
  have h := evalDist_uniformPrograms_bind prims qs hq (simulateQ (localAnswer prims) k) s
  have hm := h.map Prod.fst
  simp only [← StateT.run'_eq] at hm
  refine hm.trans ?_
  rw [← simulateQ_localAnswer_hashes]
  rw [← simulateQ_bind]
  exact evalDist_run'_prepend prims _ k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity

def seedGenFullParameter (high : HashOutput) (parameter : PublicParameter) : HashOutput :=
  high >>> digestBits <<< digestBits ||| parameter.setWidth 256

theorem seedGenFullParameter_getLsbD (high : HashOutput) (parameter : PublicParameter)
    (i : ℕ) (hi : i < 256) :
    (seedGenFullParameter high parameter).getLsbD i =
      if i < digestBits then parameter.getLsbD i else high.getLsbD i := by
  simp only [seedGenFullParameter, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : i < digestBits
  · simp [h, hi]
  · have hp : parameter.getLsbD i = false := BitVec.getLsbD_of_ge parameter i (by exact Nat.le_of_not_gt h)
    simp [h, hp, hi, Nat.le_of_not_gt h]

theorem truncate_seedGenFullParameter (high : HashOutput) (parameter : PublicParameter) :
    truncateHash (seedGenFullParameter high parameter) = parameter := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [truncateHash, BitVec.getLsbD_extractLsb', Nat.zero_add]
  rw [seedGenFullParameter_getLsbD high parameter i (by
    unfold digestBits at hi; omega)]
  simp only [hi, if_pos, decide_true, Bool.true_and]
  rfl

theorem seedGenFullParameter_restore (high : HashOutput) (parameter : PublicParameter) :
    seedGenFullParameter (seedGenFullParameter high parameter) (truncateHash high) = high := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  refine (seedGenFullParameter_getLsbD _ _ i hi).trans ?_
  by_cases hl : i < digestBits
  · rw [if_pos hl]
    change (BitVec.extractLsb' 0 digestBits high).getLsbD i = high.getLsbD i
    simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hl, decide_true, Bool.true_and]
  · rw [if_neg hl, seedGenFullParameter_getLsbD high parameter i hi, if_neg hl]

/-- The parameter encoding swaps the low halves of a pair of uniform samples. -/
def seedGenParameterSwap (p : HashOutput × PublicParameter) : HashOutput × PublicParameter :=
  (seedGenFullParameter p.1 p.2, truncateHash p.1)

theorem seedGenParameterSwap_involutive : Function.Involutive seedGenParameterSwap := by
  intro p
  exact Prod.ext (seedGenFullParameter_restore p.1 p.2) (truncate_seedGenFullParameter p.1 p.2)

theorem evalDist_seedGenFullParameter_pair :
    ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
        ($ᵗ (HashOutput × PublicParameter))) =ᵈ $ᵗ HashOutput := by
  have h := SampleableType.map_uniformSample_evalDistEq_of_bijective
    seedGenParameterSwap_involutive.bijective
  calc ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
        ($ᵗ (HashOutput × PublicParameter)) : ProbComp HashOutput)
    _ = Prod.fst <$> (seedGenParameterSwap <$> ($ᵗ (HashOutput × PublicParameter))) := by
      rw [Functor.map_map]; rfl
    _ =ᵈ Prod.fst <$> ($ᵗ (HashOutput × PublicParameter)) := h.map _
    _ =ᵈ _ := by
      rw [SampleableType.uniformSample_prod_eq_bind]
      simp only [map_bind, map_pure]
      exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
        (by rw [bind_pure])

/-- The exact full-width parameter programmed by `seedGenSimulator` is uniform. -/
theorem evalDist_seedGenFullParameter :
    (do
      let parameter ← $ᵗ PublicParameter
      let high ← $ᵗ HashOutput
      pure (high >>> digestBits <<< digestBits ||| parameter.setWidth 256) : ProbComp HashOutput) =ᵈ
      $ᵗ HashOutput := by
  change (($ᵗ PublicParameter) >>= fun p => ($ᵗ HashOutput) >>= fun h => pure (seedGenFullParameter h p)) =ᵈ _
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  have he : ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
      ($ᵗ (HashOutput × PublicParameter))) =
      (($ᵗ HashOutput) >>= fun h => ($ᵗ PublicParameter) >>= fun p => pure (seedGenFullParameter h p)) := by
    change ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
      (Prod.mk <$> ($ᵗ HashOutput) <*> ($ᵗ PublicParameter))) = _
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp]
    rfl
  rw [← he]
  exact evalDist_seedGenFullParameter_pair

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Distinct coordinates of the dealer's uniform table may be sampled separately. -/
theorem evalDist_uniform_table_list {ι R : Type} [Finite ι] [DecidableEq ι]
    [Finite R] [Nonempty R] [SampleableType R] [SampleableType (ι → R)]
    (indices : List ι) (hnd : indices.Nodup) :
    ((fun f : ι → R => indices.map f) <$> ($ᵗ (ι → R))) =ᵈ
      (indices.mapM fun _ => $ᵗ R) := by
  induction indices with
  | nil =>
    simp only [List.map_nil, List.mapM_nil, map_eq_bind_pure_comp]
    exact OracleComp.EvalDistEq.bind_const _ _
  | cons i indices ih =>
    have hn := List.nodup_cons.mp hnd
    have hs := evalDistEq_uniformSample_bind_update (R := R) i
      (fun f : ι → R => (pure ((i :: indices).map f) : ProbComp (List R)))
    have hmap : ∀ (f : ι → R) (r : R), indices.map (Function.update f i r) = indices.map f := by
      intro f r
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun h => hn.1 (h ▸ hj)
      simp [hji]
    simp only [List.map_cons, Function.update_self, hmap] at hs
    simp only [List.map_cons, map_eq_bind_pure_comp, Function.comp_def]
    refine hs.symm.trans ?_
    simp only [List.mapM_cons]
    refine EvalDistEq.bind_right _ fun r => ?_
    have hr := (ih hn.2).map (List.cons r)
    simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hr

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Interpret both network roles through the same oracle implementation. -/
def seedGenMapRoles {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec)) : Roles C m :=
  ⟨fun oa => simulateQ impl (roles.adversary oa), fun oa => simulateQ impl (roles.honest oa)⟩

theorem simulateQ_stepRound_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ impl (stepRound roles coalition A noFunctionality state steps) =
      stepRound (seedGenMapRoles impl roles) coalition A noFunctionality state steps := by
  simp only [stepRound, callInput_real, Option.isSome_none, Bool.false_eq_true, and_false,
    exists_false, false_and, if_false]
  rw [simulateQ_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only
  rw [simulateQ_bind, simulateQ_sequenceFin]
  simp only [simulateQ_pure]
  congr 1
  congr 1
  funext i
  cases hs : steps i with
  | done out => simp
  | wait outbox resume =>
    by_cases hi : i ∈ coalition.1 <;> simp [hi, seedGenMapRoles]
  | call input resume => exact input.elim

theorem simulateQ_executeRounds_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec (Keys C)),
    simulateQ impl (executeRounds roles coalition A noFunctionality fuel state steps) =
      executeRounds (seedGenMapRoles impl roles) coalition A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · simp
    · rw [simulateQ_bind, simulateQ_stepRound_real]
      refine bind_congr fun r => ?_
      exact simulateQ_executeRounds_real impl roles coalition A fuel r.1 r.2.1

/-- Counted and free local computations have the same cache semantics after the counter is erased. -/
theorem seedGenMapRoles_world (prims : Primitives) :
    seedGenMapRoles (worldAnswer (C := C) prims) worldRoles =
      seedGenMapRoles (localAnswer prims) localRoles := by
  unfold seedGenMapRoles
  congr 1
  · funext β oa
    change simulateQ (worldAnswer prims) (counted (liftComp oa (SimulatorSpec C))) =
      simulateQ (localAnswer prims) oa
    rw [simulateQ_counted]
    unfold liftComp
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext t
    rcases t with t | (q | q) <;> exact (simulateQ_query _ _).trans (id_map _)
  · funext β oa
    exact simulateQ_free _ _ oa

/-- The real network's rounds may be studied on the single shared local cache. -/
theorem simulateQ_world_executeRounds (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ (worldAnswer prims) (executeRounds worldRoles coalition A noFunctionality fuel state steps) =
      simulateQ (localAnswer prims) (executeRounds localRoles coalition A noFunctionality fuel state steps) := by
  rw [simulateQ_executeRounds_real, seedGenMapRoles_world, ← simulateQ_executeRounds_real]

theorem simulateQ_startSteps_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (program : C.Party → PartyM C E RealSpec (Keys C)) :
    simulateQ impl (startSteps roles coalition program) =
      startSteps (seedGenMapRoles impl roles) coalition program := by
  unfold startSteps
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ coalition.1 <;> simp [hi, seedGenMapRoles]

theorem simulateQ_world_adversary (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa :=
  congrArg (fun roles : Roles C (StateT (HashCache C) ProbComp) => roles.adversary oa)
    (seedGenMapRoles_world prims)

/-- The real setup game after removing only the counted/free wrappers. -/
def setupLocalGame (phase : Phase) (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let steps ← startSteps localRoles coalition fun i => (setupKeys phase i : PartyM C E RealSpec (Keys C))
  let out ← executeRounds localRoles coalition A noFunctionality setupRounds state steps
  Z out

/-- The complete real game, including the distinguisher, runs on the one shared cache. -/
theorem simulateQ_setupReal_eq_local (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (worldAnswer prims)
      (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z) =
      simulateQ (localAnswer prims) (setupLocalGame phase coalition A x z Z) := by
  unfold distinguish realExecution executePhase setupLocalGame
  simp only [simulateQ_bind, simulateQ_world_adversary, simulateQ_startSteps_real,
    simulateQ_executeRounds_real, seedGenMapRoles_world, bind_assoc]

/-- In particular, the local game has exactly the acceptance probability of the real game. -/
theorem setupLocalGame_accepts (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    (Pr{let y ← (simulateQ (localAnswer prims) (setupLocalGame phase coalition A x z Z)).run' ∅}[y = true]).toReal =
      accepts prims (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  unfold accepts
  rw [← simulateQ_setupReal_eq_local, ← fst_map_runWorld, prEvent_map]

/-- An unused private draw changes neither an output nor the cache. -/
theorem sameRun_private_unused (prims : Primitives) {α β : Type} (p : ProbComp α) (b : β) :
    SameRun (C := C) prims (liftComp p (LocalSpec C) >>= fun _ => pure b) (pure b) := by
  intro s
  have hl : simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p :=
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, hl,
    unifFwdImpl.simulateQ_run, bind_map_left]
  exact OracleComp.EvalDistEq.bind_const p _

theorem SameRun.sequenceFin (prims : Primitives) {α : Type} {n : ℕ}
    (f g : Fin n → OracleComp (LocalSpec C) α) (h : ∀ i, SameRun prims (f i) (g i)) :
    SameRun prims (OverPermutation.sequenceFin f) (OverPermutation.sequenceFin g) := by
  induction n with
  | zero => exact SameRun.refl prims _
  | succ n ih =>
    simp only [OverPermutation.sequenceFin]
    apply (h 0).bind
    intro a
    apply (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)).bind
    intro rest
    exact SameRun.refl prims _

theorem advance_setupKeys_sampling (phase : Phase) (i : C.Party) :
    advance (setupKeys phase i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun parts =>
        advance (setupWith phase i parts : PartyM C E RealSpec (Keys C)).run :=
  advance_localStep_bind _ _

/-- Moving all private parts before the first commitments is valid for any coalition. The unused
parts of corrupt operators can be sampled too, as the explicit simulator does. -/
theorem sameRun_startSteps_setup_parts (phase : Phase) (prims : Primitives) (coalition : C.Coalition) :
    SameRun prims
      (startSteps localRoles coalition fun i => (setupKeys phase i : PartyM C E RealSpec (Keys C)))
      (do
        let parts ← OverPermutation.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
        startSteps localRoles coalition fun i => (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C))) := by
  let draws : C.Party → OracleComp (LocalSpec C) (Parts C) := fun _ => liftComp sampleParts (LocalSpec C)
  let next : C.Party → Parts C → OracleComp (LocalSpec C) (Step C E RealSpec (Keys C)) := fun i parts =>
    if i ∈ coalition.1 then pure (.done none) else advance (setupWith phase i parts : PartyM C E RealSpec (Keys C)).run
  have hlocal : ∀ i, SameRun prims
      (if i ∈ coalition.1 then pure (.done none) else advance (setupKeys phase i : PartyM C E RealSpec (Keys C)).run)
      (draws i >>= next i) := by
    intro i
    by_cases hi : i ∈ coalition.1
    · simpa only [draws, next, if_pos hi] using
        (sameRun_private_unused prims (sampleParts (C := C)) (Step.done (C := C) (E := E) (G := RealSpec) (none : Option (Keys C)))).symm
    · simp only [draws, next, if_neg hi, advance_setupKeys_sampling]
      exact SameRun.refl prims _
  have hseq := SameRun.sequenceFin prims _ _ hlocal
  change SameRun prims (OverPermutation.sequenceFin _) _
  refine hseq.trans ?_
  have hmove := sameRun_sequenceFin_dep prims draws next (fun _ _ step => step)
  simp only [bind_pure] at hmove
  change SameRun prims (OverPermutation.sequenceFin fun i => draws i >>= next i)
    (OverPermutation.sequenceFin draws >>= fun parts =>
      (OverPermutation.sequenceFin fun i => next i (parts i)) >>= pure) at hmove
  simpa only [bind_pure, draws, next, startSteps, localRoles] using hmove

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The commitment computation of the honest operators, with an empty entry for each corrupt one. -/
def setupInitialCommitments (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (C.Party → List HashOutput) :=
  OverPermutation.sequenceFin fun i => if i ∈ coalition.1 then pure [] else
    liftComp (commitQueries phase i (parts i)) (LocalSpec C)

def setupInitialSteps (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) : C.Party → Step C E RealSpec (Keys C) := fun i =>
  if i ∈ coalition.1 then .done none else setupStart phase i (parts i) (commitments i)

/-- The initial network state consists of waiting commit senders and corrupt dummy steps. -/
theorem startSteps_setupWith (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C) :
    startSteps localRoles coalition (fun i => (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C))) =
      setupInitialSteps phase coalition parts <$> setupInitialCommitments phase coalition parts := by
  unfold startSteps setupInitialCommitments
  have hl : (fun i => if i ∈ coalition.1 then pure (Step.done none) else
      localRoles.honest (advance (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C)).run)) =
      (fun i => (if i ∈ coalition.1 then pure [] else
        liftComp (commitQueries phase i (parts i)) (LocalSpec C)) >>= fun commits =>
        pure (if i ∈ coalition.1 then Step.done none else setupStart phase i (parts i) commits)) := by
    funext i
    by_cases hi : i ∈ coalition.1 <;> simp [hi, localRoles, advance_setupWith]
  rw [hl]
  rw [sequenceFin_bind_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Every allowed coalition has an honest operator. -/
theorem seedGen_exists_honest (coalition : C.Coalition) : ∃ i : C.Party, i ∉ coalition.1 := by
  by_contra hn
  push Not at hn
  have heq : coalition.1 = Finset.univ := Finset.ext fun i => by simp [hn i]
  have hc := coalition.2
  rw [heq, Finset.card_univ, Fintype.card_fin] at hc
  have ht := C.one_le_t
  unfold Committee.n at hc
  omega

/-- At the commit boundary the early-exit condition is false, so the real run takes exactly one
commit round before the remaining two rounds. -/
theorem executeRounds_setupInitialSteps (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    executeRounds localRoles coalition A noFunctionality setupRounds state
      (setupInitialSteps phase coalition parts commitments) =
    (do
      let (state, steps, _) ← stepRound localRoles coalition A noFunctionality state
        (setupInitialSteps phase coalition parts commitments)
      executeRounds localRoles coalition A noFunctionality (setupRounds - 1) state steps) := by
  change executeRounds localRoles coalition A noFunctionality (2 + 1) state _ = _
  rw [executeRounds, if_neg]
  · rfl
  · intro hd
    obtain ⟨i, hi⟩ := seedGen_exists_honest coalition
    have hh := hd i hi
    simpa only [setupInitialSteps, if_neg hi, setupStart, Step.isDone] using hh

/-- The real prefix through the commit round, retaining its private parts and corrupt messages. -/
def setupLocalCommitPrefix (phase : Phase) (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    OracleComp (LocalSpec C)
      ((C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E)) := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← OverPermutation.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let commitments ← setupInitialCommitments phase coalition parts
  let (state, steps, sent) ← stepRound localRoles coalition A noFunctionality state
    (setupInitialSteps phase coalition parts commitments)
  pure (parts, state, steps, sent)

/-- The continuation after the commit round includes the final distinguisher. -/
def seedGenLocalPostCommit (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C))
    (r : (C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E)) :
    OracleComp (LocalSpec C) Bool := do
  let out ← executeRounds localRoles coalition A noFunctionality (setupRounds - 1) r.2.1 r.2.2.1
  Z out

/-- The complete real game split at the simulator's programming boundary. -/
theorem sameRun_setupLocal_split (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SameRun prims (setupLocalGame phase coalition A x z Z)
      (setupLocalCommitPrefix phase coalition A x z >>= seedGenLocalPostCommit coalition A Z) := by
  unfold setupLocalGame setupLocalCommitPrefix seedGenLocalPostCommit
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro state
  refine ((sameRun_startSteps_setup_parts phase prims coalition).bind fun steps =>
    SameRun.refl prims (executeRounds localRoles coalition A noFunctionality setupRounds state steps >>= Z)).trans ?_
  simp only [bind_assoc]
  apply SameRun.bind_right
  intro parts
  rw [startSteps_setupWith, bind_map_left]
  apply SameRun.bind_right
  intro commitments
  rw [executeRounds_setupInitialSteps]
  simp only [bind_assoc]
  exact SameRun.refl prims _

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem simulateQ_stateT_free_sampling {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ (t : (LocalSpec C).Domain) st,
      (impl (.inl t)).run st = (fun a => (a, st)) <$> free (OracleComp.lift (OracleSpec.query t)))
    (p : ProbComp α) (st : σ) :
    (simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R)))).run st =
      (fun a => (a, st)) <$> free (liftComp p (LocalSpec C)) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have hq : simulateQ impl (liftComp (liftM (OracleSpec.query t) : ProbComp _)
        (LocalSpec C + (L →ₒ R))) = impl (.inl (.inl t)) := by
      rw [liftComp_query]
      exact (simulateQ_query _ _).trans (id_map _)
    rw [hq]
    erw [himpl (.inl t) st]
    simp only [bind_map_left, ih, liftComp_bind, free_bind, map_bind]
    rfl

theorem idealExecution_FseedGen {σ : Type} (D : C.Coalition)
    (S : Simulator (C := C) (WorldSpec C) Unit
      (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) σ)
    (x : C.Party → Unit) (z : Aux) :
    idealExecution (fun oa => oa) D FseedGen S x z = (do
      let st ← S.start (corruptInputs D x) z
      let (parameter, _, keys) ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let (st, receivers) ← S.answer st (parameter, fun i => if i ∈ D.1 then some (keys i) else none)
      let out ← S.output st
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ receivers then some (keys i) else none)) := by
  unfold idealExecution FseedGen
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro st
  rw [simulateQ_stateT_free_sampling _ (by intros; rfl)]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨parameter, seeds, keys⟩
  have hleak {σ' L R : Type}
      (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ' (OracleComp (WorldSpec C))))
      (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
    unfold leak
    exact (simulateQ_query _ _).trans (id_map _)
  rw [hleak]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  change ((S.answer st (parameter, fun i => if i ∈ D.1 then some (keys i) else none) >>=
    fun p => pure (p.2, p.1)) >>= fun p => S.output p.2 >>= fun out =>
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then some (keys i) else none)) = _
  simp only [bind_assoc, pure_bind]

/-- The parts of operator `j` in the view of the simulator at operator `i`. -/
def setupProgramView (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ D.1 then readReveal phase (extractReveal phase log sent j i) i j else parts j

def seedGenFirstHonest (D : C.Coalition) (S : Finset C.Party) : C.Party :=
  (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)

/-- The parameter of the dealer. Only the seed generation samples it. -/
def setupParameterSample : Phase → ProbComp PublicParameter
  | .seedGen => $ᵗ PublicParameter
  | .prss => pure 0

/-- The high bits of the programmed value of `P`. Only the seed generation samples them. -/
def setupHighSample : Phase → ProbComp HashOutput
  | .seedGen => $ᵗ HashOutput
  | .prss => pure 0

/-- The programming of `P`. Only the seed generation has it. -/
def programParameter : Phase → Query C → HashOutput → OracleComp (WorldSpec C) Bool
  | .seedGen, q, value => program q value
  | .prss, _, _ => pure true

/-- The simulator's complete programming block, including failed attempts. -/
def setupProgramBlock (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) (high : HashOutput) : OracleComp (WorldSpec C) Unit := do
  let view := setupProgramView phase D parts log sent
  let _ ← programParameter phase (.derive phase .parameter
    (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter))
    (seedGenFullParameter high parameter)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      let i := seedGenFirstHonest D (C.holders T)
      program (.derive phase .term
        ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
        (((corrupt j).map (·.seed T)).getD 0)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive phase .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
        (((corrupt j).map (·.pairKey i)).getD 0)
    else pure true
  pure ()

/-- The actual simulator with its emulated key values retained. -/
def setupEmulation (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (st : SimulatorState C Unit A.State) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) :
    OracleComp (WorldSpec C) (SimulatorState C Unit A.State × (C.Party → Option (Keys C))) := do
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
  let log := st.log ++ calls
  let high ← free (liftComp (setupHighSample phase) _)
  setupProgramBlock phase D parts log sent parameter corrupt high
  let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality
    (setupRounds - 1) state steps).run
  pure (⟨state, log ++ rest, st.corrupt⟩, keys)

theorem seedGenSimulator_answer_emulation (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (st : SimulatorState C Unit A.State)
    (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) :
    (seedGenSimulator D A).answer st (parameter, corrupt) =
      (fun r => (r.1, Finset.univ.filter fun i => (r.2 i).isSome)) <$>
        setupEmulation .seedGen D A st parameter corrupt := by
  simp only [seedGenSimulator, setupSimulator, setupEmulation, setupProgramBlock, setupProgramView,
    programParameter, setupHighSample, seedGenFirstHonest, seedGenFullParameter, ite_true, map_bind, map_pure,
    bind_assoc, pure_bind, Option.map_map]
  rfl

/-- The samples of the dealer of a setup of `phase`. -/
def setupDealerSamples (phase : Phase) :
    ProbComp (PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) := do
  let parameter ← setupParameterSample phase
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairs ← $ᵗ (C.Pair → HashOutput)
  pure (parameter, seeds, pairs)

/-- The start of the simulator of a setup. It is the same for each phase. -/
def setupSimulatorStart (A : Adversary C E Unit PEmpty PEmpty) (corrupt : C.Party → Option Unit) (z : Aux) :
    OracleComp (WorldSpec C) (SimulatorState C Unit A.State) := do
  let (state, log) ← observe (A.start corrupt z)
  pure ⟨state, log, corrupt⟩

/-- One common game retains both the emulated outputs and the dealer's keys. -/
def setupCommonGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Keys C)) × (C.Party → Keys C)) := do
  let st ← setupSimulatorStart A (corruptInputs D x) z
  let (parameter, seeds, pairs) ← free (liftComp (setupDealerSamples (C := C) phase) (LocalSpec C))
  let (st, emulated) ← setupEmulation phase D A st parameter fun i =>
    if i ∈ D.1 then some (dealtKeys parameter seeds pairs i) else none
  pure (st.adversary, emulated, dealtKeys parameter seeds pairs)

def seedGenIdealProjection {σ : Type*} (D : C.Coalition)
    (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => if i ∉ D.1 ∧ (r.2.1 i).isSome then some (r.2.2 i) else none)

/-- The ideal marginal of the seed generation is exactly the specified functionality and simulator,
for every run. -/
theorem setupCommonGame_seedGen_ideal (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    seedGenIdealProjection D <$> setupCommonGame .seedGen D A x z =
      idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z := by
  rw [idealExecution_FseedGen]
  unfold setupCommonGame setupDealerSamples setupParameterSample prawnsKeyGen
  simp only [map_bind, map_pure, liftComp_bind, liftComp_pure, free_bind, free_pure, bind_assoc, pure_bind]
  refine bind_congr fun st => ?_
  refine bind_congr fun parameter => ?_
  refine bind_congr fun seeds => ?_
  refine bind_congr fun pairs => ?_
  erw [seedGenSimulator_answer_emulation, bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨st', emulated⟩
  change pure (seedGenIdealProjection D (st'.adversary, emulated, dealtKeys parameter seeds pairs)) =
    (pure st'.adversary >>= fun out => pure (out, fun i =>
      if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (emulated i).isSome)
      then some (dealtKeys parameter seeds pairs i) else none))
  simp only [pure_bind, seedGenIdealProjection, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The keys of the PRSS setup from the keys of the carrier. -/
def carrierPrssKeys (k : Keys C) : PrssKeys C := ⟨k.seed, k.pairKey⟩

/-- The keys of the carrier from the keys of the PRSS setup, with the parameter `0`. -/
def carrierKeys (k : PrssKeys C) : Keys C := ⟨0, k.term, k.pair⟩

theorem carrierPrssKeys_dealtKeys (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (i : C.Party) :
    carrierPrssKeys (dealtKeys 0 term pair i) = dealtPrssKeys term pair i := rfl

theorem prssSetupWith_eq_map (i : C.Party) (own : Parts C) :
    (prssSetupWith i own : PartyM C E RealSpec (PrssKeys C)) = carrierPrssKeys <$> setupWith .prss i own := by
  simp only [prssSetupWith, setupWith, map_bind, map_pure]
  rfl

theorem prssSetup_eq_map (i : C.Party) :
    (prssSetup i : PartyM C E RealSpec (PrssKeys C)) = carrierPrssKeys <$> setupKeys .prss i := by
  simp only [prssSetup, setupKeys, setupWith, map_bind, map_pure]
  rfl

/-- The real run of the PRSS setup is the real run of the carrier setup under `carrierPrssKeys`. -/
theorem realExecution_prssSetup (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) :
    realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) x z =
      (fun r => (r.1, fun i => (r.2 i).map carrierPrssKeys)) <$> realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) x z := by
  unfold realExecution executePhase
  simp only [map_bind, prssSetup_eq_map]
  refine bind_congr fun state => ?_
  rw [startSteps_map worldRoles worldRoles_honest_map, bind_map_left]
  refine bind_congr fun steps => ?_
  exact executeRounds_map worldRoles worldRoles_honest_map D A noFunctionality carrierPrssKeys setupRounds state steps

/-- The normal form of the ideal run of `F_prssKeys`. It is `idealExecution_FseedGen` for the dealer
of the PRSS keys. -/
theorem idealExecution_FprssKeys {σ : Type} (D : C.Coalition)
    (S : Simulator (C := C) (WorldSpec C) Unit (C.Party → Option (PrssKeys C)) (Finset C.Party) σ)
    (x : C.Party → Unit) (z : Aux) :
    idealExecution (fun oa => oa) D FprssKeys S x z = (do
      let st ← S.start (corruptInputs D x) z
      let term ← free (liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C))
      let pair ← free (liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C))
      let (st, receivers) ← S.answer st fun i => if i ∈ D.1 then some (dealtPrssKeys term pair i) else none
      let out ← S.output st
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ receivers then some (dealtPrssKeys term pair i) else none)) := by
  unfold idealExecution FprssKeys sample
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro st
  rw [simulateQ_stateT_free_sampling _ (by intros; rfl)]
  simp only [bind_map_left]
  apply bind_congr
  intro term
  rw [simulateQ_stateT_free_sampling _ (by intros; rfl)]
  simp only [bind_map_left]
  apply bind_congr
  intro pair
  have hleak {σ' L R : Type}
      (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ' (OracleComp (WorldSpec C))))
      (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
    unfold leak
    exact (simulateQ_query _ _).trans (id_map _)
  rw [hleak]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  change ((S.answer st (fun i => if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) >>=
    fun p => pure (p.2, p.1)) >>= fun p => S.output p.2 >>= fun out =>
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then some (dealtPrssKeys term pair i) else none)) = _
  simp only [bind_assoc, pure_bind]

/-- The answer of the simulator of the PRSS setup is the emulation at `.prss`, under the map of the
outputs. -/
theorem prssSetupSimulator_answer_emulation (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (st : SimulatorState C Unit A.State) (corrupt : C.Party → Option (PrssKeys C)) :
    (prssSetupSimulator D A).answer st corrupt =
      (fun r => (r.1, Finset.univ.filter fun i => (r.2 i).isSome)) <$>
        setupEmulation .prss D A st 0 (fun j => (corrupt j).map carrierKeys) := by
  simp only [prssSetupSimulator, setupSimulator, reduceCtorEq, ite_false, setupEmulation, setupProgramBlock,
    setupProgramView, programParameter, setupHighSample, seedGenFirstHonest, liftComp_pure, free_pure, pure_bind,
    map_bind, bind_assoc, map_pure, prssSetupWith_eq_map, startSteps_map worldRoles worldRoles_honest_map,
    bind_map_left, Option.map_map, Function.comp_def, carrierKeys]
  refine bind_congr fun parts => ?_
  refine bind_congr fun steps => ?_
  rw [stepRound_map observedRoles observedRoles_honest_map, WriterT.run_map', bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨state, steps', sent⟩, calls⟩
  simp only [Prod.map, id]
  refine bind_congr fun _ => ?_
  refine bind_congr fun _ => ?_
  rw [executeRounds_map observedRoles observedRoles_honest_map, WriterT.run_map', bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨state', keys⟩, rest⟩
  simp only [Prod.map, id, Option.isSome_map]

/-- The ideal run of the PRSS setup is the ideal projection of the common game under
`carrierPrssKeys`. -/
theorem setupCommonGame_prss_ideal (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    (fun r => (r.1, fun i => (r.2 i).map carrierPrssKeys)) <$>
        (seedGenIdealProjection D <$> setupCommonGame .prss D A x z) =
      idealExecution (fun oa => oa) D FprssKeys (prssSetupSimulator D A) x z := by
  rw [idealExecution_FprssKeys]
  unfold setupCommonGame setupDealerSamples setupParameterSample
  simp only [map_bind, map_pure, liftComp_bind, liftComp_pure, free_bind, free_pure, bind_assoc, pure_bind]
  refine bind_congr fun st => ?_
  refine bind_congr fun seeds => ?_
  refine bind_congr fun pairs => ?_
  have hc : (fun j => (if j ∈ D.1 then some (dealtPrssKeys seeds pairs j) else none).map carrierKeys) =
      fun i => if i ∈ D.1 then some (dealtKeys 0 seeds pairs i) else none := by
    funext j
    split_ifs <;> rfl
  erw [prssSetupSimulator_answer_emulation, hc, bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨st', emulated⟩
  change pure _ = (pure st'.adversary >>= fun out => pure (out, fun i =>
    if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (emulated i).isSome)
    then some (dealtPrssKeys seeds pairs i) else none))
  simp only [pure_bind, seedGenIdealProjection, Finset.mem_filter, Finset.mem_univ, true_and]
  congr 2
  funext i
  split_ifs <;> rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Equality of unordered pairs preserves their endpoints, up to swapping. -/
theorem pairOf_eq_endpoints (i j i' j' : C.Party) (hij : i ≠ j) (hij' : i' ≠ j')
    (h : C.pairOf i j hij = C.pairOf i' j' hij') :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  have hv := congrArg Subtype.val h
  unfold Committee.pairOf at hv
  split_ifs at hv <;> simp only [Prod.mk.injEq] at hv
  · exact Or.inl hv
  · exact Or.inr hv
  · exact Or.inr ⟨hv.2, hv.1⟩
  · exact Or.inl ⟨hv.2, hv.1⟩

/-- A corrupt--honest pair has only one orientation in the simulator's nested loop. -/
theorem pairOf_cross_injective (D : C.Coalition) (i j i' j' : C.Party)
    (hj : j ∈ D.1) (hi : i ∉ D.1) (hj' : j' ∈ D.1) (hi' : i' ∉ D.1)
    (h : C.pairOf i j (fun e => hi (e ▸ hj)) =
      C.pairOf i' j' (fun e => hi' (e ▸ hj'))) : i = i' ∧ j = j' := by
  rcases pairOf_eq_endpoints i j i' j' _ _ h with he | he
  · exact he
  · exact (hi (he.1 ▸ hj')).elim

/-- The corrupt--honest ordered pairs, in exactly the order of the simulator's loops. -/
def seedGenCrossList (D : C.Coalition) : List (C.Party × C.Party) :=
  (C.parties.product C.parties).filter fun p => p.1 ∈ D.1 ∧ p.2 ∉ D.1

theorem seedGenCrossList_mem (D : C.Coalition) (p : C.Party × C.Party) :
    p ∈ seedGenCrossList D ↔ p.1 ∈ D.1 ∧ p.2 ∉ D.1 := by
  rcases p with ⟨j, i⟩
  simp [seedGenCrossList, Committee.parties, List.mem_product, List.mem_finRange]

def seedGenCrossPair (D : C.Coalition) (p : {p // p ∈ seedGenCrossList D}) : C.Pair :=
  C.pairOf p.1.2 p.1.1 (fun e => (seedGenCrossList_mem D p.1).mp p.2 |>.2
    (e ▸ ((seedGenCrossList_mem D p.1).mp p.2).1))

theorem seedGenCrossPair_injective (D : C.Coalition) : Function.Injective (seedGenCrossPair D) := by
  intro p q h
  apply Subtype.ext
  have hp := (seedGenCrossList_mem D p.1).mp p.2
  have hq := (seedGenCrossList_mem D q.1).mp q.2
  have he := pairOf_cross_injective D p.1.2 p.1.1 q.1.2 q.1.1 hp.1 hp.2 hq.1 hq.2 h
  exact Prod.ext he.2 he.1

def seedGenCrossCoordinates (D : C.Coalition) : List C.Pair :=
  (seedGenCrossList D).attach.map (seedGenCrossPair D)

theorem seedGenCrossCoordinates_nodup (D : C.Coalition) : (seedGenCrossCoordinates D).Nodup := by
  apply List.Nodup.map (seedGenCrossPair_injective D)
  apply List.Nodup.attach
  apply List.Nodup.filter
  exact List.Nodup.product (List.nodup_finRange _) (List.nodup_finRange _)

def seedGenKnownCoordinates (D : C.Coalition) : List C.Term :=
  C.terms.filter fun T => KnownTo D.1 T

theorem seedGenKnownCoordinates_nodup (D : C.Coalition) : (seedGenKnownCoordinates D).Nodup := by
  apply List.Nodup.filter
  exact Finset.nodup_toList _

theorem seedGenDealer_known_value (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (T : C.Term) (j : C.Party)
    (hj : j ∈ D.1) (hT : j ∈ C.holders T) :
    (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0) = seeds T := by
  simp [hj, dealtKeys, hT]

theorem seedGenDealer_cross_value (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (i j : C.Party)
    (h : j ∈ D.1 ∧ i ∉ D.1) :
    (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.pairKey i)).getD 0) =
      pairs (C.pairOf i j (fun e => h.2 (e ▸ h.1))) := by
  have hij : i ≠ j := fun e => h.2 (e ▸ h.1)
  simp only [if_pos h.1, Option.map_some, Option.getD_some, dealtKeys, dif_neg hij]
  congr 1
  unfold Committee.pairOf
  split_ifs with hji hijlt hijlt
  · exact (not_lt_of_ge (le_of_lt hji) hijlt).elim
  · rfl
  · rfl
  · exact (hij (le_antisymm (not_lt.mp hji) (not_lt.mp hijlt))).elim

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The cache after a programming attempt, whether or not it succeeds. -/
def programCache (q : Query C) (y : HashOutput) (s : HashCache C) : HashCache C :=
  if IsFixed q ∨ (s q).isSome then s else s.cacheQuery q y

theorem programAnswer_run_cache (q : Query C) (y : HashOutput) (s : HashCache C) :
    (programAnswer (q, y)).run s =
      pure (!(decide (IsFixed q ∨ (s q).isSome)), programCache q y s) := by
  unfold programAnswer programCache IsFixed
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp_all

def programValues : List (Query C) → List HashOutput → StateT (HashCache C) ProbComp Unit
  | q :: qs, y :: ys => programAnswer (q, y) >>= fun _ => programValues qs ys
  | _, _ => pure ()

theorem programValues_run_cons (q : Query C) (qs : List (Query C))
    (y : HashOutput) (ys : List HashOutput) (s : HashCache C) :
    (programValues (q :: qs) (y :: ys)).run s =
      (programValues qs ys).run (programCache q y s) := by
  simp only [programValues, StateT.run_bind, programAnswer_run_cache, pure_bind]

theorem sample_programValues_run (qs : List (Query C)) (s : HashCache C) :
    (qs.mapM (fun _ => ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun ys =>
      (programValues qs ys).run s) = (uniformPrograms qs).run s := by
  induction qs generalizing s with
  | nil => simp [programValues, uniformPrograms]
  | cons q qs ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, programValues_run_cons,
      uniformPrograms, StateT.run_bind, uniformProgram, StateT.run_lift,
      programAnswer_run_cache]
    apply bind_congr
    intro y
    exact ih _

/-- Sampling the dealer coordinates used by a block gives exactly independent programming values.
No condition is placed on the target inputs: they may repeat or already be cached. -/
theorem evalDist_table_programValues {ι : Type} [Finite ι] [DecidableEq ι]
    [SampleableType (ι → HashOutput)] (indices : List ι) (hnd : indices.Nodup)
    (inputs : ι → Query C) (s : HashCache C) :
    (do let table ← $ᵗ (ι → HashOutput)
        (programValues (indices.map inputs) (indices.map table)).run s) =ᵈ
      (uniformPrograms (indices.map inputs)).run s := by
  have h := evalDist_uniform_table_list (R := HashOutput) indices hnd
  calc
    _ = (((fun table : ι → HashOutput => indices.map table) <$> ($ᵗ (ι → HashOutput))) >>=
      fun ys => (programValues (indices.map inputs) ys).run s) := by rw [bind_map_left]
    _ =ᵈ ((indices.mapM fun _ => $ᵗ HashOutput) >>= fun ys =>
      (programValues (indices.map inputs) ys).run s) := h.bind_left _
    _ = _ := by
      have hm : (indices.map inputs).mapM (fun _ => ($ᵗ HashOutput : ProbComp HashOutput)) =
          indices.mapM (fun _ => ($ᵗ HashOutput : ProbComp HashOutput)) := by
        rw [List.mapM_map]; rfl
      rw [← hm, sample_programValues_run]

def tablePrograms {ι : Type} [SampleableType (ι → HashOutput)] (indices : List ι)
    (inputs : ι → Query C) : StateT (HashCache C) ProbComp Unit := do
  let table ← StateT.lift ($ᵗ (ι → HashOutput))
  programValues (indices.map inputs) (indices.map table)

theorem evalDist_tablePrograms {ι : Type} [Finite ι] [DecidableEq ι]
    [SampleableType (ι → HashOutput)] (indices : List ι) (hnd : indices.Nodup)
    (inputs : ι → Query C) (s : HashCache C) :
    (tablePrograms indices inputs).run s =ᵈ
      (uniformPrograms (indices.map inputs)).run s := by
  simp only [tablePrograms, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact evalDist_table_programValues indices hnd inputs s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

def seedGenEraseLog {α : Type} (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) :
    OracleComp (WorldSpec C) α := Prod.fst <$> p.run

theorem seedGenEraseLog_pure {α : Type} (a : α) : seedGenEraseLog (C := C) (pure a) = pure a := by
  simp [seedGenEraseLog]

theorem seedGenEraseLog_bind {α β : Type}
    (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (k : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β) :
    seedGenEraseLog (p >>= k) = seedGenEraseLog p >>= fun a => seedGenEraseLog (k a) := by
  simp [seedGenEraseLog, WriterT.run_bind, map_bind, Functor.map_map, bind_map_left]

theorem seedGenEraseLog_lift {α : Type} (p : OracleComp (WorldSpec C) α) :
    seedGenEraseLog (liftM p) = p := by
  simp [seedGenEraseLog, WriterT.run_liftM, Functor.map_map]

theorem seedGenEraseLog_sequenceFin {α : Type} : ∀ {n : ℕ}
    (p : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) α),
    seedGenEraseLog (OverPermutation.sequenceFin p) = OverPermutation.sequenceFin fun i => seedGenEraseLog (p i)
  | 0, p => by simp [OverPermutation.sequenceFin, seedGenEraseLog_pure]
  | n + 1, p => by
    simp only [OverPermutation.sequenceFin, seedGenEraseLog_bind, seedGenEraseLog_pure,
      seedGenEraseLog_sequenceFin]

theorem fst_observe {α : Type} (p : OracleComp (LocalSpec C) α) :
    Prod.fst <$> observe p = worldRoles.adversary p := by
  change seedGenEraseLog (simulateQ _ p) = _
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, seedGenEraseLog_pure, worldRoles_adversary_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, seedGenEraseLog_bind, ih]
    rw [show worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
      worldRoles.adversary (liftM (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a) by
        change counted (liftComp (liftM (OracleSpec.query t) >>= k) (SimulatorSpec C)) = _
        rw [liftComp_bind, counted_bind]
        rfl]
    congr 1
    rcases t with t | (q | x)
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      exact seedGenEraseLog_lift _
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      simp only [seedGenEraseLog_bind, seedGenEraseLog_lift, seedGenEraseLog_pure]
      simp [seedGenEraseLog, WriterT.run_tell, map_pure]
      rfl
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      exact seedGenEraseLog_lift _

theorem seedGenEraseLog_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    seedGenEraseLog (observedRoles.adversary p) = worldRoles.adversary p := fst_observe p

theorem seedGenEraseLog_honest {α : Type} (p : OracleComp (LocalSpec C) α) :
    seedGenEraseLog (observedRoles.honest p) = worldRoles.honest p := seedGenEraseLog_lift _

theorem seedGenEraseLog_stepRound {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    seedGenEraseLog (stepRound observedRoles D A noFunctionality state steps) =
      stepRound worldRoles D A noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  simp only [seedGenEraseLog_bind, seedGenEraseLog_adversary, seedGenEraseLog_pure,
    seedGenEraseLog_sequenceFin]
  apply bind_congr
  intro r
  congr 1
  congr 1
  funext j
  cases hs : steps j with
  | done out => exact seedGenEraseLog_pure _
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp [hj, seedGenEraseLog_pure]
    · simp [hj, seedGenEraseLog_honest]
  | call input resume => exact input.elim

theorem seedGenEraseLog_executeRounds {α : Type} (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α),
      seedGenEraseLog (executeRounds observedRoles D A noFunctionality fuel state steps) =
        executeRounds worldRoles D A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds, seedGenEraseLog_pure]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · exact seedGenEraseLog_pure _
    · simp only [seedGenEraseLog_bind, seedGenEraseLog_stepRound, seedGenEraseLog_executeRounds]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem discard_mapM_filter {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (xs : List α) (p : α → Bool) (f : α → m β) (b : β)
    (h : ∀ x ∈ xs, p x = false → f x = pure b) :
    (xs.mapM f >>= fun _ => pure ()) = ((xs.filter p).mapM f >>= fun _ => pure ()) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    cases hp : p x with
    | false =>
      rw [h x (List.mem_cons_self ..) hp]
      simp only [pure_bind, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      exact ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.mapM_cons, bind_assoc, pure_bind]
      apply bind_congr
      intro _
      exact ih (fun a ha => h a (List.mem_cons_of_mem x ha))

theorem discard_mapM_product {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → m γ) :
    (xs.mapM (fun x => ys.mapM (f x)) >>= fun _ => pure ()) =
      ((xs.product ys).mapM (fun p => f p.1 p.2) >>= fun _ => pure ()) := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih =>
    rw [show (x :: xs).product ys = ys.map (fun y => (x, y)) ++ xs.product ys from rfl]
    simp only [ List.mapM_append, List.mapM_map,
      List.mapM_cons, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr
    intro _
    exact ih

theorem seedGen_mapM_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (xs : List α) (f g : α → m β) (h : ∀ x ∈ xs, f x = g x) :
    xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

def setupTermProgrammingInput (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (T : C.Term) : Query C :=
  .derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
    (view (seedGenFirstHonest D (C.holders T)) k).term T)

def setupPairProgrammingInput (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (p : C.Pair) : Query C :=
  let i := if p.1.1 ∈ D.1 then p.1.2 else p.1.1
  .derive phase .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]

theorem setupPairProgrammingInput_cross (phase : Phase) (D : C.Coalition)
    (view : C.Party → C.Party → Parts C) (i j : C.Party) (h : j ∈ D.1 ∧ i ∉ D.1) :
    setupPairProgrammingInput phase D view (C.pairOf i j (fun e => h.2 (e ▸ h.1))) =
      .derive phase .pair
        [(view i (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.1).pair
            (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.2,
          (view i (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.2).pair
            (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.1] := by
  unfold setupPairProgrammingInput Committee.pairOf
  split_ifs <;> simp_all

theorem seedGenKnown_find (D : C.Coalition) (T : C.Term) :
    (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T).isSome ↔ KnownTo D.1 T := by
  simp [List.find?_isSome, Committee.parties, List.mem_finRange, KnownTo]

theorem setupProgramTerms_dealt (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    (C.terms.mapM (fun T => match C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (setupTermProgrammingInput phase D view T)
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0)
      | none => pure true) >>= fun _ => pure ()) =
    ((seedGenKnownCoordinates D).mapM (fun T =>
      program (setupTermProgrammingInput phase D view T) (seeds T)) >>= fun _ => pure ()) := by
  have he : (fun T => match C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (setupTermProgrammingInput phase D view T)
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0)
      | none => pure true) = (fun T => if KnownTo D.1 T then
        program (setupTermProgrammingInput phase D view T) (seeds T) else pure true) := by
    funext T
    cases hf : C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | none =>
      have hn : ¬ KnownTo D.1 T := by rw [← seedGenKnown_find, hf]; simp
      simp [hn]
    | some j =>
      have hj : j ∈ D.1 ∧ j ∈ C.holders T := by
        simpa only [decide_eq_true_eq] using List.find?_some hf
      simp only [if_pos (show KnownTo D.1 T from ⟨j, hj⟩),
        seedGenDealer_known_value D parameter seeds pairs T j hj.1 hj.2]
  rw [he, discard_mapM_filter C.terms (fun T => decide (KnownTo D.1 T)) _ true
    (by intro T _ h; simp_all)]
  congr 1
  apply seedGen_mapM_congr
  intro T hT
  exact if_pos (by simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hT).2)

theorem setupProgramPairs_coordinates (phase : Phase) (D : C.Coalition)
    (view : C.Party → C.Party → Parts C) (pairs : C.Pair → HashOutput) :
    (C.parties.mapM (fun j => C.parties.mapM (fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        program (setupPairProgrammingInput phase D view (C.pairOf i j (fun e => h.2 (e ▸ h.1))))
          (pairs (C.pairOf i j (fun e => h.2 (e ▸ h.1))))
      else pure true)) >>= fun _ => pure ()) =
    ((seedGenCrossCoordinates D).mapM (fun p =>
      program (setupPairProgrammingInput phase D view p) (pairs p)) >>= fun _ => pure ()) := by
  rw [discard_mapM_product]
  let f : C.Party × C.Party → OracleComp (WorldSpec C) Bool := fun p =>
    if h : p.1 ∈ D.1 ∧ p.2 ∉ D.1 then
      program (setupPairProgrammingInput phase D view (C.pairOf p.2 p.1 (fun e => h.2 (e ▸ h.1))))
        (pairs (C.pairOf p.2 p.1 (fun e => h.2 (e ▸ h.1))))
    else pure true
  change ((C.parties.product C.parties).mapM f >>= fun _ => pure ()) = _
  rw [discard_mapM_filter _ (fun p => decide (p.1 ∈ D.1 ∧ p.2 ∉ D.1)) f true
    (by intro p _ h; simp_all [f])]
  unfold seedGenCrossCoordinates
  rw [List.mapM_map]
  have hm : ((seedGenCrossList D).attach.mapM (fun p =>
        program (setupPairProgrammingInput phase D view (seedGenCrossPair D p))
          (pairs (seedGenCrossPair D p)))) = (seedGenCrossList D).mapM f := by
    rw [List.mapM_subtype (g := f) (by
      intro p hp
      have hd := (seedGenCrossList_mem D p).mp hp
      simp only [f, dif_pos hd, seedGenCrossPair])]
    simp
  change ((seedGenCrossList D).mapM f >>= fun _ => pure ()) = _
  simpa only [Function.comp_def] using congrArg (fun p : OracleComp (WorldSpec C) (List Bool) => p >>= fun _ => pure ()) hm.symm

/-- The full actual programming block on a dealer leak is an attempt at `P`, followed by one
attempt per known term and one per corrupt--honest pair. Only the seed generation has the attempt
at `P`. -/
theorem setupProgramBlock_dealt (phase : Phase) (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput) :
    setupProgramBlock phase D parts log sent parameter
      (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high = (do
      let view := setupProgramView phase D parts log sent
      let _ ← programParameter phase (.derive phase .parameter
        (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter))
        (seedGenFullParameter high parameter)
      let _ ← (seedGenKnownCoordinates D).mapM fun T =>
        program (setupTermProgrammingInput phase D view T) (seeds T)
      let _ ← (seedGenCrossCoordinates D).mapM fun p =>
        program (setupPairProgrammingInput phase D view p) (pairs p)
      pure ()) := by
  unfold setupProgramBlock
  apply bind_congr
  intro _
  let view := setupProgramView phase D parts log sent
  have hp := setupProgramPairs_coordinates phase D view pairs
  have hpair : (C.parties.mapM (fun j => C.parties.mapM (fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        program (.derive phase .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.pairKey i)).getD 0)
      else pure true)) >>= fun _ => pure ()) =
      ((seedGenCrossCoordinates D).mapM (fun p =>
        program (setupPairProgrammingInput phase D view p) (pairs p)) >>= fun _ => pure ()) := by
    rw [← hp]
    congr 1
    apply seedGen_mapM_congr
    intro j _
    apply seedGen_mapM_congr
    intro i _
    by_cases h : j ∈ D.1 ∧ i ∉ D.1
    · simp only [dif_pos h, seedGenDealer_cross_value D parameter seeds pairs i j h,
        setupPairProgrammingInput_cross phase D view i j h]
    · simp only [dif_neg h]
  change (_ >>= fun _ => _ ) = (_ >>= fun _ => _)
  conv_lhs => arg 2; ext; rw [hpair]
  have ht := setupProgramTerms_dealt phase D view parameter seeds pairs
  have he := congrArg (fun p : OracleComp (WorldSpec C) Unit => p >>= fun _ =>
    (seedGenCrossCoordinates D).mapM (fun p => program (setupPairProgrammingInput phase D view p) (pairs p))
      >>= fun _ => pure ()) ht
  simp only [bind_assoc, pure_bind] at he
  convert he using 1 <;> rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Private sampling commutes with any independent computation on the oracle cache. -/
theorem commutes_private_stateT {σ α β : Type} (p : ProbComp α) (m : StateT σ ProbComp β) :
    Commutes (StateT.lift p) m := by
  intro s
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem simulateQ_world_program (prims : Primitives) (q : Query C) (y : HashOutput) :
    simulateQ (worldAnswer prims) (program q y) = programAnswer (q, y) := by
  unfold program
  rw [simulateQ_counted]
  exact (simulateQ_query _ _).trans (id_map _)

theorem simulateQ_programValues (prims : Primitives) {ι : Type}
    (indices : List ι) (inputs : ι → Query C) (values : ι → HashOutput) :
    simulateQ (worldAnswer prims)
      (indices.mapM (fun i => program (inputs i) (values i)) >>= fun _ => pure ()) =
      programValues (indices.map inputs) (indices.map values) := by
  induction indices with
  | nil => simp [programValues, simulateQ_pure]
  | cons i indices ih =>
    simp only [List.mapM_cons, List.map_cons, bind_assoc, pure_bind, simulateQ_bind,
      simulateQ_world_program, programValues, ih]

/-- The simulator's high/low parameter encoding is a uniform programming value, with its cache. -/
theorem evalDist_parameterProgramming (q : Query C) (s : HashCache C) :
    ((do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let high ← StateT.lift ($ᵗ HashOutput)
      let _ ← programAnswer (q, seedGenFullParameter high parameter)
      pure () : StateT (HashCache C) ProbComp Unit)).run s =ᵈ
      (uniformProgram q).run s := by
  let p : ProbComp HashOutput := do
    let parameter ← $ᵗ PublicParameter
    let high ← $ᵗ HashOutput
    pure (seedGenFullParameter high parameter)
  have hp : p =ᵈ $ᵗ HashOutput := evalDist_seedGenFullParameter
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
    uniformProgram, StateT.run_pure]
  change (p >>= fun y => (programAnswer (q, y)).run s >>= fun r => pure ((), r.2)) =ᵈ _
  exact hp.bind_left _

/-- The actual independent dealer samples followed by the simulator's programming block. -/
def setupDealerPrograms (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    StateT (HashCache C) ProbComp Unit := do
  let parameter ← StateT.lift (setupParameterSample phase)
  let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
  let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
  let high ← StateT.lift (setupHighSample phase)
  simulateQ (worldAnswer prims) (setupProgramBlock phase D parts log sent parameter
    (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high)

def seedGenParameterProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C) : Query C :=
  .derive .seedGen .parameter (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter)

def parameterProgram (q : Query C) (parameter : PublicParameter) : StateT (HashCache C) ProbComp Unit := do
  let high ← StateT.lift ($ᵗ HashOutput)
  let _ ← programAnswer (q, seedGenFullParameter high parameter)
  pure ()

/-- The programming input of `P`. Only the seed generation has it. -/
def setupParameterInputs (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C) : List (Query C) :=
  if phase = .seedGen then
    [.derive phase .parameter (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter)]
  else []

/-- The programs of `P` with a uniform value. Only the seed generation has one. -/
def setupParameterPrograms (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C) :
    StateT (HashCache C) ProbComp Unit :=
  match phase with
  | .seedGen => do
    let parameter ← StateT.lift ($ᵗ PublicParameter)
    parameterProgram (seedGenParameterProgrammingInput D view) parameter
  | .prss => pure ()

theorem setupDealerPrograms_seedGen_expand (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    setupDealerPrograms .seedGen prims D parts log sent = (do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      let view := setupProgramView .seedGen D parts log sent
      parameterProgram (seedGenParameterProgrammingInput D view) parameter
      programValues ((seedGenKnownCoordinates D).map (setupTermProgrammingInput .seedGen D view))
        ((seedGenKnownCoordinates D).map seeds)
      programValues ((seedGenCrossCoordinates D).map (setupPairProgrammingInput .seedGen D view))
        ((seedGenCrossCoordinates D).map pairs)) := by
  unfold setupDealerPrograms
  simp only [setupProgramBlock_dealt, setupParameterSample, setupHighSample, programParameter]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro seeds
  apply bind_congr
  intro pairs
  simp only [parameterProgram, seedGenParameterProgrammingInput, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_world_program, simulateQ_pure]
  apply bind_congr
  intro high
  apply bind_congr
  intro _
  rw [← simulateQ_programValues prims (seedGenKnownCoordinates D),
    ← simulateQ_programValues prims (seedGenCrossCoordinates D)]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]

theorem setupDealerPrograms_prss_expand (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    setupDealerPrograms .prss prims D parts log sent = (do
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      let view := setupProgramView .prss D parts log sent
      programValues ((seedGenKnownCoordinates D).map (setupTermProgrammingInput .prss D view))
        ((seedGenKnownCoordinates D).map seeds)
      programValues ((seedGenCrossCoordinates D).map (setupPairProgrammingInput .prss D view))
        ((seedGenCrossCoordinates D).map pairs)) := by
  have hlift : ∀ {α : Type} (a : α), (StateT.lift (pure a) : StateT (HashCache C) ProbComp α) = pure a :=
    fun _ => rfl
  unfold setupDealerPrograms
  simp only [setupProgramBlock_dealt, setupParameterSample, setupHighSample, programParameter, hlift,
    pure_bind]
  apply bind_congr
  intro seeds
  apply bind_congr
  intro pairs
  simp only [simulateQ_bind, simulateQ_pure]
  rw [← simulateQ_programValues prims (seedGenKnownCoordinates D),
    ← simulateQ_programValues prims (seedGenCrossCoordinates D)]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]

/-- The dealer tables can be delayed until their own programming blocks. -/
theorem evalDist_setupDealerPrograms_reorder (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) (s : HashCache C) :
    (setupDealerPrograms phase prims D parts log sent).run s =ᵈ
    ((do
      let view := setupProgramView phase D parts log sent
      setupParameterPrograms phase D view
      tablePrograms (seedGenKnownCoordinates D) (setupTermProgrammingInput phase D view)
      tablePrograms (seedGenCrossCoordinates D) (setupPairProgrammingInput phase D view)
      : StateT (HashCache C) ProbComp Unit)).run s := by
  cases phase
  · rw [setupDealerPrograms_seedGen_expand]
    simp only [setupParameterPrograms, bind_assoc]
    apply evalDist_run_bind_congr
    intro parameter s'
    let view := setupProgramView .seedGen D parts log sent
    let pp := parameterProgram (seedGenParameterProgrammingInput D view) parameter
    let kt := (seedGenKnownCoordinates D).map (setupTermProgrammingInput .seedGen D view)
    let kp := (seedGenCrossCoordinates D).map (setupPairProgrammingInput .seedGen D view)
    let ts (seeds : C.Term → HashOutput) := programValues kt ((seedGenKnownCoordinates D).map seeds)
    let ps (pairs : C.Pair → HashOutput) := programValues kp ((seedGenCrossCoordinates D).map pairs)
    change ((do
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      pp
      ts seeds
      ps pairs) : StateT (HashCache C) ProbComp Unit).run s' =ᵈ _
    refine EvalDistEq.trans (my := ((do
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      pp
      ts seeds
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      ps pairs) : StateT (HashCache C) ProbComp Unit).run s') ?_ ?_
    · apply evalDist_run_bind_congr
      intro seeds s''
      simpa only [bind_assoc] using
        (commutes_private_stateT ($ᵗ (C.Pair → HashOutput)) (pp >>= fun _ => ts seeds)).bind
          (fun pairs _ => ps pairs) s''
    · simpa only [tablePrograms, bind_assoc, pp, ts, ps, kt, kp, view] using
        (commutes_private_stateT ($ᵗ (C.Term → HashOutput)) pp).bind
          (fun seeds _ => ts seeds >>= fun _ => StateT.lift ($ᵗ (C.Pair → HashOutput)) >>= ps) s'
  · rw [setupDealerPrograms_prss_expand]
    simp only [setupParameterPrograms, pure_bind]
    let view := setupProgramView .prss D parts log sent
    let kt := (seedGenKnownCoordinates D).map (setupTermProgrammingInput .prss D view)
    let kp := (seedGenCrossCoordinates D).map (setupPairProgrammingInput .prss D view)
    let ts (seeds : C.Term → HashOutput) := programValues kt ((seedGenKnownCoordinates D).map seeds)
    let ps (pairs : C.Pair → HashOutput) := programValues kp ((seedGenCrossCoordinates D).map pairs)
    change ((do
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      ts seeds
      ps pairs) : StateT (HashCache C) ProbComp Unit).run s =ᵈ _
    refine EvalDistEq.trans (my := ((do
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      ts seeds
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      ps pairs) : StateT (HashCache C) ProbComp Unit).run s) ?_ ?_
    · apply evalDist_run_bind_congr
      intro seeds s''
      simpa only [bind_assoc] using
        (commutes_private_stateT ($ᵗ (C.Pair → HashOutput)) (ts seeds)).bind (fun pairs _ => ps pairs) s''
    · simp only [tablePrograms, bind_assoc, ts, ps, kt, kp, view]
      rfl

theorem uniformPrograms_append (xs ys : List (Query C)) :
    uniformPrograms (xs ++ ys) = (uniformPrograms xs >>= fun _ => uniformPrograms ys) := by
  induction xs with
  | nil => simp [uniformPrograms]
  | cons x xs ih => simp [uniformPrograms, ih, bind_assoc]

/-- The programming inputs of the simulator of a setup of `phase`. -/
def setupProgrammingInputs (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C) : List (Query C) :=
  setupParameterInputs phase D view ++
    (seedGenKnownCoordinates D).map (setupTermProgrammingInput phase D view) ++
    (seedGenCrossCoordinates D).map (setupPairProgrammingInput phase D view)

theorem setupProgrammingInputs_not_fixed (phase : Phase) (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (q : Query C) (hq : q ∈ setupProgrammingInputs phase D view) : ¬ IsFixed q := by
  simp only [setupProgrammingInputs, setupParameterInputs, List.mem_append, List.mem_map] at hq
  rcases hq with (hq | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩
  · split_ifs at hq
    · rw [List.mem_singleton] at hq
      subst hq
      simp [IsFixed]
    · simp at hq
  · simp [IsFixed, setupTermProgrammingInput]
  · simp [IsFixed, setupPairProgrammingInput]

/-- After forgetting the dealer values, the exact simulator block has the cache distribution
of independent uniform programming at its actual inputs. -/
theorem evalDist_setupDealerPrograms (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) (s : HashCache C) :
    (setupDealerPrograms phase prims D parts log sent).run s =ᵈ
      (uniformPrograms (setupProgrammingInputs phase D (setupProgramView phase D parts log sent))).run s := by
  have hparameter : ∀ (view : C.Party → C.Party → Parts C) (k : Unit → StateT (HashCache C) ProbComp Unit),
      (setupParameterPrograms phase D view >>= k).run s =ᵈ
        (uniformPrograms (setupParameterInputs phase D view) >>= k).run s := by
    intro view k
    cases phase
    · simpa only [setupParameterPrograms, parameterProgram, setupParameterInputs, ite_true, uniformPrograms,
        seedGenParameterProgrammingInput, bind_assoc, pure_bind] using
        evalDist_run_bind_of_eq k s (evalDist_parameterProgramming (seedGenParameterProgrammingInput D view) s)
    · rfl
  refine (evalDist_setupDealerPrograms_reorder phase prims D parts log sent s).trans ?_
  let view := setupProgramView phase D parts log sent
  let kt := (seedGenKnownCoordinates D).map (setupTermProgrammingInput phase D view)
  let kp := (seedGenCrossCoordinates D).map (setupPairProgrammingInput phase D view)
  refine EvalDistEq.trans (my := ((do
    setupParameterPrograms phase D view
    uniformPrograms kt
    uniformPrograms kp) : StateT (HashCache C) ProbComp Unit).run s) ?_ ?_
  · apply evalDist_run_bind_congr
    intro _ s''
    refine (evalDist_run_bind_of_eq
      (fun _ : Unit => tablePrograms (seedGenCrossCoordinates D) (setupPairProgrammingInput phase D view)) s''
      (evalDist_tablePrograms (seedGenKnownCoordinates D) (seedGenKnownCoordinates_nodup D)
        (setupTermProgrammingInput phase D view) s'')).trans ?_
    apply evalDist_run_bind_congr
    intro _ s'''
    exact evalDist_tablePrograms (seedGenCrossCoordinates D) (seedGenCrossCoordinates_nodup D)
      (setupPairProgrammingInput phase D view) s'''
  · simpa only [setupProgrammingInputs, uniformPrograms_append, bind_assoc, view, kt, kp] using
      hparameter view (fun _ => uniformPrograms kt >>= fun _ => uniformPrograms kp)

/-- Exact erasure of the specified simulator's dealer programming, before any local continuation.
It is valid for every cache and extracted view, including failed extraction or programming. -/
theorem evalDist_setupDealerPrograms_prepend (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    {α : Type} (k : OracleComp (LocalSpec C) α) (s : HashCache C) :
    (setupDealerPrograms phase prims D parts log sent >>= fun _ =>
      simulateQ (localAnswer prims) k).run' s =ᵈ
      (simulateQ (localAnswer prims) k).run' s := by
  have he := evalDist_run_bind_of_eq (fun _ : Unit => simulateQ (localAnswer prims) k) s
    (evalDist_setupDealerPrograms phase prims D parts log sent s)
  have hm := he.map Prod.fst
  simp only [StateT.run'_eq]
  refine hm.trans ?_
  simpa only [StateT.run'_eq] using evalDist_uniformPrograms_prepend prims
    (setupProgrammingInputs phase D (setupProgramView phase D parts log sent))
    (setupProgrammingInputs_not_fixed phase D _) k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem simulateQ_world_sample (prims : Primitives) {α : Type} (p : ProbComp α) :
    simulateQ (worldAnswer prims) (free (C := C) (liftComp p (LocalSpec C))) = StateT.lift p := by
  rw [simulateQ_free]
  change simulateQ (unifFwdImpl (Query C →ₒ HashOutput) + _) (liftComp p (LocalSpec C)) = _
  rw [QueryImpl.simulateQ_add_liftComp_left]
  funext s
  change (simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p).run s =
    p >>= fun a => pure (a, s)
  rw [unifFwdImpl.simulateQ_run]
  exact map_eq_bind_pure_comp (m := ProbComp) _ _

/-- The unobserved real execution with all private parts sampled before the commits. -/
def setupPartsWorldGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) Bool := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) (LocalSpec C))
  let steps ← startSteps worldRoles D fun i => (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C))
  let (state, steps, _) ← stepRound worldRoles D A noFunctionality state steps
  let out ← executeRounds worldRoles D A noFunctionality (setupRounds - 1) state steps
  worldRoles.adversary (Z out)

theorem simulateQ_setupPartsWorldGame (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (worldAnswer prims) (setupPartsWorldGame phase D A x z Z) =
      simulateQ (localAnswer prims)
        (setupLocalCommitPrefix phase D A x z >>= seedGenLocalPostCommit D A Z) := by
  unfold setupPartsWorldGame setupLocalCommitPrefix seedGenLocalPostCommit
  simp only [simulateQ_bind, bind_assoc, pure_bind, simulateQ_world_adversary,
    simulateQ_world_executeRounds]
  apply bind_congr
  intro state
  rw [simulateQ_free, liftComp_sequenceFin]
  apply bind_congr
  intro parts
  rw [simulateQ_startSteps_real, seedGenMapRoles_world, ← simulateQ_startSteps_real,
    startSteps_setupWith, simulateQ_map, bind_map_left]
  apply bind_congr
  intro commitments
  rw [simulateQ_stepRound_real, seedGenMapRoles_world, ← simulateQ_stepRound_real]

/-- The parts-first game has exactly the real acceptance probability. -/
theorem setupPartsWorldGame_accepts (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (setupPartsWorldGame phase D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  have hp : accepts prims (setupPartsWorldGame phase D A x z Z) =
      (Pr{let y ← (simulateQ (worldAnswer prims) (setupPartsWorldGame phase D A x z Z)).run' ∅}[y = true]).toReal := by
    rw [← fst_map_runWorld]
    unfold accepts
    rw [prEvent_map]
  rw [hp, simulateQ_setupPartsWorldGame]
  have he := (sameRun_setupLocal_split phase prims D A x z Z).run'_eq
  exact (congrArg ENNReal.toReal (he.symm.prEvent_eq _)).trans (setupLocalGame_accepts phase prims D A x z Z)

abbrev SeedGenObservedCommitData (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :=
  (C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E) × CallLog C

def setupObservedCommit (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) :
    OracleComp (WorldSpec C) (SeedGenObservedCommitData D A) := do
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (setupWith phase i (parts i) : PartyM C E RealSpec (Keys C))
  let (r, calls) ← (stepRound observedRoles D A noFunctionality state steps).run
  pure (parts, r.1, r.2.1, r.2.2, calls)

def seedGenObservedPost (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) : OracleComp (WorldSpec C) Bool := do
  let (out, _) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
  worldRoles.adversary (Z out)

theorem seedGenObservedPost_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    seedGenObservedPost D A Z state steps = (do
      let out ← executeRounds worldRoles D A noFunctionality (setupRounds - 1) state steps
      worldRoles.adversary (Z out)) := by
  unfold seedGenObservedPost
  rw [← seedGenEraseLog_executeRounds D A (setupRounds - 1) state steps]
  simp only [seedGenEraseLog, bind_map_left]

theorem simulateQ_seedGenObservedPost (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (Z : Distinguisher C A.State (Keys C))
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ (worldAnswer prims) (seedGenObservedPost D A Z state steps) =
      simulateQ (localAnswer prims) (do
        let out ← executeRounds localRoles D A noFunctionality (setupRounds - 1) state steps
        Z out) := by
  rw [seedGenObservedPost_eq]
  simp only [simulateQ_bind, simulateQ_world_executeRounds, simulateQ_world_adversary]

def setupObservedPartsGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) Bool := do
  let (state, _) ← observe (A.start (corruptInputs D x) z)
  let r ← setupObservedCommit phase D A state
  seedGenObservedPost D A Z r.2.1 r.2.2.1

theorem setupObservedPartsGame_eq (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    setupObservedPartsGame phase D A x z Z = setupPartsWorldGame phase D A x z Z := by
  unfold setupObservedPartsGame setupPartsWorldGame setupObservedCommit
  simp only [bind_assoc, pure_bind, seedGenObservedPost_eq]
  rw [← fst_observe (A.start (corruptInputs D x) z), bind_map_left]
  apply bind_congr
  intro st
  apply bind_congr
  intro parts
  apply bind_congr
  intro steps
  rw [← seedGenEraseLog_stepRound D A st.1 steps]
  simp only [seedGenEraseLog, bind_map_left]

def seedGenEmulatedProjection {σ : Type*} (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) := (r.1, r.2.1)

def setupCommonEmulatedGame (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) Bool :=
  distinguish (seedGenEmulatedProjection <$> setupCommonGame phase D A x z) Z

/-- Exact normal form of the common game's emulated-output marginal. -/
theorem setupCommonEmulatedGame_expand (phase : Phase) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    setupCommonEmulatedGame phase D A x z Z = (do
      let (state, log) ← observe (A.start (corruptInputs D x) z)
      let (parameter, seeds, pairs) ← free (liftComp (setupDealerSamples phase (C := C)) (LocalSpec C))
      let r ← setupObservedCommit phase D A state
      let high ← free (liftComp (setupHighSample phase) (LocalSpec C))
      setupProgramBlock phase D r.1 (log ++ r.2.2.2.2) r.2.2.2.1 parameter
        (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high
      seedGenObservedPost D A Z r.2.1 r.2.2.1) := by
  unfold setupCommonEmulatedGame distinguish setupCommonGame setupEmulation
    setupObservedCommit seedGenObservedPost setupDealerSamples setupSimulatorStart
  simp only [map_bind, map_pure, bind_map_left, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure, seedGenEmulatedProjection]

/-- Congruence for output distributions under an arbitrary cache-state prefix. -/
theorem evalDist_stateT_run'_bind_congr {σ α β : Type} (p : StateT σ ProbComp α)
    (f g : α → StateT σ ProbComp β)
    (h : ∀ a s, (f a).run' s =ᵈ (g a).run' s) (s : σ) :
    (p >>= f).run' s =ᵈ (p >>= g).run' s := by
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  refine EvalDistEq.bind_right _ fun r => ?_
  exact h r.1 r.2

/-- The common game's emulated-output marginal is exactly the real game, including the final
oracle-aided distinguisher. This statement does not require a good-event assumption. -/
theorem evalDist_setupCommonEmulatedGame (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (setupCommonEmulatedGame phase D A x z Z)).run' s =ᵈ
      (simulateQ (worldAnswer prims) (setupPartsWorldGame phase D A x z Z)).run' s := by
  rw [setupCommonEmulatedGame_expand, ← setupObservedPartsGame_eq]
  unfold setupObservedPartsGame
  simp only [simulateQ_bind, simulateQ_world_sample]
  apply evalDist_stateT_run'_bind_congr
  rintro ⟨state, log⟩ s₁
  let stageRun := simulateQ (worldAnswer prims) (setupObservedCommit phase D A state)
  let afterProgram := fun (dealer : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput))
      (r : SeedGenObservedCommitData D A) => (do
    let high ← StateT.lift (setupHighSample phase)
    simulateQ (worldAnswer prims) (setupProgramBlock phase D r.1 (log ++ r.2.2.2.2) r.2.2.2.1 dealer.1
      (fun j => if j ∈ D.1 then some (dealtKeys dealer.1 dealer.2.1 dealer.2.2 j) else none) high)
    simulateQ (worldAnswer prims) (seedGenObservedPost D A Z r.2.1 r.2.2.1))
  have hs := (commutes_private_stateT (setupDealerSamples phase (C := C)) stageRun).bind afterProgram s₁
  have hs' := hs.map Prod.fst
  rw [← StateT.run'_eq, ← StateT.run'_eq] at hs'
  refine hs'.trans ?_
  apply evalDist_stateT_run'_bind_congr
  intro r s₂
  dsimp only [afterProgram]
  simp only [simulateQ_seedGenObservedPost]
  simpa only [setupDealerPrograms, setupDealerSamples, StateT.run'_eq, StateT.run_bind,
    StateT.run_lift, bind_assoc, pure_bind, map_bind] using
    evalDist_setupDealerPrograms_prepend phase prims D r.1 (log ++ r.2.2.2.2) r.2.2.2.1
      (do
        let out ← executeRounds localRoles D A noFunctionality (setupRounds - 1) r.2.1 r.2.2.1
        Z out) s₂

/-- Exact real acceptance of the common game's emulated-output projection. -/
theorem setupCommonGame_real_accepts (phase : Phase) (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (setupCommonEmulatedGame phase D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (setupKeys phase i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  rw [← setupPartsWorldGame_accepts phase prims D A x z Z]
  have he := congrArg ENNReal.toReal
    ((evalDist_setupCommonEmulatedGame phase prims D A x z Z ∅).prEvent_eq (· = true))
  simpa only [← fst_map_runWorld, prEvent_map, accepts] using he

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem seedGenFirstHonest_spec (coalition : C.Coalition) (S : Finset C.Party)
    (hex : ∃ i ∈ S, i ∉ coalition.1) : seedGenFirstHonest coalition S ∈ S ∧ seedGenFirstHonest coalition S ∉ coalition.1 := by
  have hs : (C.parties.find? fun i => i ∈ S ∧ i ∉ coalition.1).isSome := by
    simpa only [List.find?_isSome, Committee.parties, List.mem_finRange, true_and, decide_eq_true_eq] using hex
  unfold seedGenFirstHonest
  cases hf : C.parties.find? (fun i => i ∈ S ∧ i ∉ coalition.1) with
  | none => rw [hf] at hs; contradiction
  | some i =>
    simpa only [Option.getD_some, decide_eq_true_eq] using List.find?_some hf

theorem seedGen_honest_holder (coalition : C.Coalition) (T : C.Term) : ∃ i ∈ C.holders T, i ∉ coalition.1 := by
  by_contra hn
  have hs : C.holders T ⊆ coalition.1 := by
    intro i hi
    by_contra hd
    exact hn ⟨i, hi, hd⟩
  have hc := Finset.card_le_card hs
  rw [seedGen_card_holders] at hc
  have hd := coalition.2
  have ht := C.one_le_t
  omega

theorem seedGenFirstHonest_univ (coalition : C.Coalition) : seedGenFirstHonest coalition Finset.univ ∉ coalition.1 :=
  (seedGenFirstHonest_spec coalition Finset.univ (by
    obtain ⟨i, hi⟩ := seedGen_exists_honest coalition
    exact ⟨i, Finset.mem_univ _, hi⟩)).2

theorem seedGenFirstHonest_holder (coalition : C.Coalition) (T : C.Term) :
    seedGenFirstHonest coalition (C.holders T) ∈ C.holders T ∧
      seedGenFirstHonest coalition (C.holders T) ∉ coalition.1 :=
  seedGenFirstHonest_spec coalition _ (seedGen_honest_holder coalition T)

/-- When extraction matches the actual corrupt openings, all fields used in an honest derivation
match the simulator's extracted view. The unused fields need not match. -/
theorem setup_derived_programView (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (hextract : ∀ j, j ∈ coalition.1 → extractReveal phase log sent j i = Msg.hashesOf (revealed i j))
    (h : Query C → HashOutput) :
    D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i))) =
      D prims h (deriveKeys phase i (setupProgramView phase coalition parts log sent i)) := by
  have corrupt (j : C.Party) (hj : j ∈ coalition.1) :
      setupView phase i (parts i) (revealed i) j = setupProgramView phase coalition parts log sent i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp only [setupView, if_neg hji, setupProgramView, if_pos hj, hextract j hj]
  have parameter (hphase : phase = .seedGen) (j : C.Party) :
      (setupView phase i (parts i) (revealed i) j).parameter =
        (setupProgramView phase coalition parts log sent i j).parameter := by
    subst hphase
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender .seedGen coalition parts revealed hreceived i j hj, honestView_parameter]
      simp [setupProgramView, hj]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party) (hjT : j ∈ C.holders T) :
      (setupView phase i (parts i) (revealed i) j).term T =
        (setupProgramView phase coalition parts log sent i j).term T := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender phase coalition parts revealed hreceived i j hj,
        honestView_term phase parts hjT hiT]
      simp [setupProgramView, hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (setupView phase i (parts i) (revealed i) a).pair b =
        (setupProgramView phase coalition parts log sent i a).pair b := by
    by_cases ha : a ∈ coalition.1
    · rw [corrupt a ha]
    · rw [setupView_honest_sender phase coalition parts revealed hreceived i a ha,
        honestView_pair phase parts hab]
      simp [setupProgramView, ha]
  rw [D_deriveKeys, D_deriveKeys]
  apply Prod.ext
  · dsimp only
    split_ifs with hphase
    · apply congrArg h
      apply congrArg (Query.derive phase .parameter)
      apply List.map_congr_left
      intro j _
      exact parameter hphase j
    · rfl
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive phase .term)
        apply List.map_congr_left
        intro j hj
        exact term T hiT j (by simpa using (List.mem_filter.mp hj).2)
      · simp [hiT]
    · funext j
      by_cases hji : j = i
      · simp [hji]
      · simp only [dif_neg hji]
        have hp := pairOf_left_or_right i j (Ne.symm hji)
        apply congrArg h
        apply congrArg (Query.derive phase .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

theorem seedGenCrossCoordinates_cross_mem (coalition : C.Coalition) (i j : C.Party)
    (hj : j ∈ coalition.1) (hi : i ∉ coalition.1) :
    C.pairOf i j (fun e => hi (e ▸ hj)) ∈ seedGenCrossCoordinates coalition := by
  apply List.mem_map.mpr
  have hm : (j, i) ∈ seedGenCrossList coalition := (seedGenCrossList_mem coalition (j, i)).mpr ⟨hj, hi⟩
  exact ⟨⟨(j, i), hm⟩, List.mem_attach _ _, rfl⟩

/-- Successful programming plus the accepting party's honest echo agreements fixes every
parameter, known term and corrupt--honest pair key to the dealer's value. -/
theorem setup_known_outputs_of_programmed (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (view : C.Party → C.Party → Parts C) (h : Query C → HashOutput)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (high : HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hderive : ∀ j, j ∉ coalition.1 → keys j = D prims h (deriveKeys phase j (view j)))
    (hparameter : ∀ q ∈ setupParameterInputs phase coalition view, h q = seedGenFullParameter high parameter)
    (hzero : phase = .prss → parameter = 0)
    (hterm : ∀ T, KnownTo coalition.1 T → h (setupTermProgrammingInput phase coalition view T) = seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates coalition, h (setupPairProgrammingInput phase coalition view p) = pairs p)
    (i : C.Party) (hi : i ∉ coalition.1)
    (hagree : ∀ j, j ∉ coalition.1 →
      (keys i).1 = (keys j).1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T →
        (keys i).2.1 T = (keys j).2.1 T) :
    (keysOf (keys i)).parameter = parameter ∧
      (∀ T, KnownTo coalition.1 T → (keysOf (keys i)).seed T = (dealtKeys parameter seeds pairs i).seed T) ∧
      (∀ j, j ∈ coalition.1 → (keysOf (keys i)).pairKey j = (dealtKeys parameter seeds pairs i).pairKey j) := by
  constructor
  · have he := (hagree (seedGenFirstHonest coalition Finset.univ) (seedGenFirstHonest_univ coalition)).1
    change truncateHash (keys i).1 = parameter
    rw [he, hderive _ (seedGenFirstHonest_univ coalition), D_deriveKeys]
    dsimp only
    split_ifs with hphase
    · subst hphase
      rw [hparameter _ (List.mem_singleton_self _), truncate_seedGenFullParameter]
    · cases phase
      · exact absurd rfl hphase
      · rw [hzero rfl]
        rfl
  constructor
  · intro T hT
    by_cases hiT : i ∈ C.holders T
    · have href := seedGenFirstHonest_holder coalition T
      have he := (hagree (seedGenFirstHonest coalition (C.holders T)) href.2).2 T hiT href.1
      change (keys i).2.1 T = (if i ∈ C.holders T then seeds T else 0)
      rw [if_pos hiT, he, hderive _ href.2, D_deriveKeys]
      simp only [if_pos href.1]
      exact hterm T hT
    · change (keys i).2.1 T = (if i ∈ C.holders T then seeds T else 0)
      rw [hderive i hi, D_deriveKeys]
      simp [hiT]
  · intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hm := seedGenCrossCoordinates_cross_mem coalition i j hj hi
    have hp := hpair (C.pairOf i j (Ne.symm hji)) hm
    rw [setupPairProgrammingInput_cross phase coalition view i j ⟨hj, hi⟩] at hp
    change (keys i).2.2 j = (if h : j = i then 0 else pairs (C.pairOf i j (Ne.symm h)))
    rw [hderive i hi, D_deriveKeys]
    simp only [dif_neg hji]
    exact hp

/-- The derivation input of a pair of honest operators uses just their original pair parts. -/
theorem setup_hiddenPair_input (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (p : C.Pair) (hp : p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1)
    (i : C.Party) (hi : p.1.1 = i ∨ p.1.2 = i) :
    setupPairViewInput phase parts revealed i p = pairInput phase parts p := by
  unfold setupPairViewInput pairInput
  dsimp only
  rw [setupView_honest_sender phase coalition parts revealed hreceived i p.1.1 hp.1,
    setupView_honest_sender phase coalition parts revealed hreceived i p.1.2 hp.2,
    honestView_pair phase parts hi, honestView_pair phase parts hi.symm]

/-- The actual hidden pair key is the oracle value at its canonical raw-parts input. -/
theorem setup_hiddenPair_derived (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (i j : C.Party) (hi : i ∉ coalition.1) (hj : j ∉ coalition.1) (hji : j ≠ i) :
    (D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i)))).2.2 j =
      h (pairInput phase parts (C.pairOf i j (Ne.symm hji))) := by
  rw [D_deriveKeys]
  simp only [dif_neg hji]
  change h (setupPairViewInput phase parts revealed i (C.pairOf i j (Ne.symm hji))) = _
  apply congrArg h
  apply setup_hiddenPair_input phase coalition parts revealed hreceived
  · unfold Committee.pairOf
    split_ifs <;> exact ⟨by assumption, by assumption⟩
  · exact pairOf_left_or_right i j (Ne.symm hji)

def setupHybridSeeds (phase : Phase) (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (seeds : C.Term → HashOutput) : C.Term → HashOutput :=
  fun T => if KnownTo coalition.1 T then seeds T else h (termInput phase parts T)

def setupHybridPairs (phase : Phase) (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (pairs : C.Pair → HashOutput) : C.Pair → HashOutput :=
  fun p => if p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1 then h (pairInput phase parts p) else pairs p

/-- Under extraction, successful programming, and the accepting party's honest agreements,
its entire key is one dealing. Only the hidden seeds and honest--honest pairs still use raw oracle
values; every exposed coordinate is the dealer's value. -/
theorem setup_output_eq_hybrid_dealing (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent revealed : C.Party → Mail C E)
    (h : Query C → HashOutput) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (hextract : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      extractReveal phase log sent j i = Msg.hashesOf (revealed i j))
    (hderive : ∀ i, i ∉ coalition.1 →
      keys i = D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i))))
    (hparameter : ∀ q ∈ setupParameterInputs phase coalition (setupProgramView phase coalition parts log sent),
      h q = seedGenFullParameter high parameter)
    (hzero : phase = .prss → parameter = 0)
    (hterm : ∀ T, KnownTo coalition.1 T →
      h (setupTermProgrammingInput phase coalition (setupProgramView phase coalition parts log sent) T) = seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates coalition,
      h (setupPairProgrammingInput phase coalition (setupProgramView phase coalition parts log sent) p) = pairs p)
    (i : C.Party) (hi : i ∉ coalition.1)
    (hagree : ∀ j, j ∉ coalition.1 →
      (keys i).1 = (keys j).1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T →
        (keys i).2.1 T = (keys j).2.1 T) :
    keysOf (keys i) = dealtKeys parameter (setupHybridSeeds phase coalition h parts seeds)
      (setupHybridPairs phase coalition h parts pairs) i := by
  have hprogramView : ∀ j, j ∉ coalition.1 →
      keys j = D prims h (deriveKeys phase j (setupProgramView phase coalition parts log sent j)) := by
    intro j hj
    exact (hderive j hj).trans (setup_derived_programView phase prims coalition parts log sent revealed j hj
      hreceived (fun k hk => hextract j k hj hk) h)
  have hk := setup_known_outputs_of_programmed phase prims coalition _ h parameter seeds pairs high keys
    hprogramView hparameter hzero hterm hpair i hi hagree
  unfold keysOf dealtKeys
  congr 1
  · exact hk.1
  · funext T
    by_cases hiT : i ∈ C.holders T
    · simp only [if_pos hiT]
      by_cases hT : KnownTo coalition.1 T
      · rw [setupHybridSeeds, if_pos hT]
        simpa only [keysOf, dealtKeys, if_pos hiT] using hk.2.1 T hT
      · rw [setupHybridSeeds, if_neg hT, hderive i hi]
        exact setup_hiddenTerm_derived phase prims coalition h parts revealed hreceived T hT i hiT
    · rw [if_neg hiT, hderive i hi, D_deriveKeys]
      simp [hiT]
  · funext j
    by_cases hji : j = i
    · rw [hderive i hi, D_deriveKeys]
      simp [hji]
    · simp only [dif_neg hji]
      by_cases hj : j ∈ coalition.1
      · have hn : ¬ ((C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
            (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1) := by
          unfold Committee.pairOf
          split_ifs <;> simp_all
        rw [setupHybridPairs, if_neg hn]
        simpa only [keysOf, dealtKeys, dif_neg hji] using hk.2.2 j hj
      · have hh : (C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
            (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1 := by
          unfold Committee.pairOf
          split_ifs <;> exact ⟨by assumption, by assumption⟩
        rw [setupHybridPairs, if_pos hh, hderive i hi]
        exact setup_hiddenPair_derived phase prims coalition h parts revealed hreceived i j hi hj hji

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Canonical raw-parts derivation inputs, indexed by the model's existing key names. -/
def setupNamedInput (phase : Phase) (parts : C.Party → Parts C) : KeyName C → Query C
  | .parameter => parameterInput parts
  | .term T => termInput phase parts T
  | .pair p => pairInput phase parts p

def seedGenNames (C : Committee) : List (KeyName C) := (Finset.univ : Finset (KeyName C)).toList

theorem setupNamedInput_not_fixed (phase : Phase) (parts : C.Party → Parts C) (name : KeyName C) :
    ¬ IsFixed (setupNamedInput phase parts name) := by
  cases name <;> simp [setupNamedInput, parameterInput, termInput, pairInput, IsFixed]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The commit-round continuation only checks abort frames and prepares the reveal. -/
theorem advance_setupCommitResume (phase : Phase) (i : C.Party) (own : Parts C) (committed : Mail C E) :
    advance (exchangeResume (setupRound1 phase i own) committed) =
      pure (if C.parties.any (fun j => Msg.isAbort (committed j)) then .done none else
        .wait (revealOutbox phase i own) (exchangeResume fun revealed =>
          setupRest phase i own committed revealed >>= fun keys => pure (keysOf keys))) := by
  unfold exchangeResume
  split_ifs
  · rfl
  · exact advance_exchange_bind _ _

/-- The inboxes at the commit boundary, including all corrupt abort frames. -/
def setupCommitInbox (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (sent : C.Party → Mail C E) : C.Party → Mail C E :=
  roundInbox coalition sent (setupInitialSteps phase coalition parts commitments)

/-- The actual network state after the commit round. -/
def setupRevealSteps (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) : C.Party → Step C E RealSpec (Keys C) := fun i =>
  if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then .done none else
    .wait (revealOutbox phase i (parts i)) (exchangeResume fun revealed =>
      setupRest phase i (parts i) (committed i) revealed >>= fun keys => pure (keysOf keys))

/-- The first network step computes no hashes after the adversary's commit messages. -/
theorem stepRound_setupInitialSteps (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    stepRound localRoles coalition A noFunctionality state
        (setupInitialSteps phase coalition parts commitments) = (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        commitOutbox i (commitments i) c else none
      pure (st, setupRevealSteps phase coalition parts (setupCommitInbox phase coalition parts commitments sent), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (setupInitialSteps phase coalition parts commitments (E := E) i).outbox c else none) =
      (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then commitOutbox i (commitments i) c else none) := by
    funext c i
    split_ifs with hc
    · simp only [setupInitialSteps, if_neg hc.2, setupStart, Step.outbox]
    · rfl
  rw [hmsg]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (OverPermutation.sequenceFin (fun j =>
    (pure (setupRevealSteps phase coalition parts (setupCommitInbox phase coalition parts commitments sent) j) :
      OracleComp (LocalSpec C) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext j
    by_cases hj : j ∈ coalition.1
    · simp [setupInitialSteps, setupRevealSteps, hj]
    · simp only [setupInitialSteps, if_neg hj, setupStart]
      rw [advance_setupCommitResume]
      simp only [setupRevealSteps, hj, false_or, setupCommitInbox, roundInbox]
      rfl
  · rw [sequenceFin_pure, pure_bind]

/-- The inbox before the honest opening checks. -/
def setupRevealInbox (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) (sent : C.Party → Mail C E) : C.Party → Mail C E :=
  roundInbox coalition sent (setupRevealSteps phase coalition parts committed)

/-- If one honest operator passed the abort-frame check at reveal, all honest operators sent
reveals in that round. This includes senders that fail their own opening checks afterwards. -/
theorem setupRevealInbox_all_honest (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (setupRevealInbox phase coalition parts committed sent i j)) = false) :
    ∀ k j, j ∉ coalition.1 → j ≠ k →
      Msg.hashesOf (setupRevealInbox phase coalition parts committed sent k j) = revealTo phase (parts j) j k := by
  intro k j hj hjk
  have hno := List.any_eq_false.mp ha j (List.mem_finRange j)
  by_cases hb : (C.parties.any fun l => Msg.isAbort (committed j l)) = true
  · have hstep : setupRevealSteps phase coalition parts committed j = .done none := by
      simp only [setupRevealSteps, hb, or_true, if_true]
    have hr := roundInbox_abort coalition sent (setupRevealSteps phase coalition parts committed) i j hj hstep
    change ¬ Msg.isAbort (roundInbox coalition sent (setupRevealSteps phase coalition parts committed) i j) = true at hno
    rw [hr] at hno
    exact (hno rfl).elim
  · simp only [setupRevealInbox, roundInbox, setupRevealSteps,
      hj, hb, Bool.false_eq_true, false_or, if_false, Step.delivered, revealOutbox, if_neg (Ne.symm hjk), Msg.hashesOf]

abbrev SeedGenEchoData (C : Committee) :=
  (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) × List HashOutput

/-- Everything the honest reveal continuation computes, before waiting for the echo round. -/
def setupRevealCompute (phase : Phase) (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    OracleComp (LocalSpec C) (Option (SeedGenEchoData C)) := do
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then return none
  let opens ← liftComp (openQueries phase i revealed) (LocalSpec C)
  if ¬ openCheck phase i own committed revealed opens then return none
  let keys ← liftComp (deriveKeys phase i (setupView phase i own revealed)) (LocalSpec C)
  let shared ← liftComp (sharedQueries phase i keys) (LocalSpec C)
  pure (some (keys, shared))

/-- An echo step carrying the actual values and the actual shared-key hash answers. -/
def setupEchoDataStep (phase : Phase) (i : C.Party) : Option (SeedGenEchoData C) → Step C E RealSpec (Keys C)
  | none => .done none
  | some (keys, shared) => .wait (echoOutbox phase i keys shared) (exchangeResume fun received =>
      require (echoCheck phase i keys shared received) >>= fun _ => pure (keysOf keys))

/-- Exact expansion of the honest reveal continuation, with both abort tests. -/
theorem advance_setupRevealResume (phase : Phase) (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun revealed =>
      setupRest phase i own committed revealed >>= fun keys => pure (keysOf keys)) revealed) =
      setupEchoDataStep phase i <$> setupRevealCompute phase i own committed revealed := by
  unfold exchangeResume setupRevealCompute
  split_ifs with ha
  · rfl
  · rw [advance_setupRest]
    simp only [map_bind]
    refine bind_congr fun opens => ?_
    split_ifs with ho
    · simp only [map_bind, map_pure, setupEchoDataStep, pure_bind]
    · rfl

/-- All honest computations between the reveal and echo boundaries. -/
def setupRevealComputations (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) : OracleComp (LocalSpec C) (C.Party → Option (SeedGenEchoData C)) :=
  OverPermutation.sequenceFin fun i =>
    if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then pure none else
      setupRevealCompute phase i (parts i) (committed i) (setupRevealInbox phase coalition parts committed sent i)

/-- Exact reduction of the second round, retaining all honest echo data. -/
theorem stepRound_setupRevealSteps (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) :
    stepRound localRoles coalition A noFunctionality state (setupRevealSteps phase coalition parts committed) =
    (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (setupRevealSteps phase coalition parts committed i).outbox c else none
      let data ← setupRevealComputations phase coalition parts committed sent
      pure (st, (fun i => setupEchoDataStep phase i (data i)), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (OverPermutation.sequenceFin (fun i =>
    (if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then pure none else
      setupRevealCompute phase i (parts i) (committed i) (setupRevealInbox phase coalition parts committed sent i)) >>=
      fun v => pure (setupEchoDataStep phase i v)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    by_cases hi : i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j))
    · simp only [setupRevealSteps, if_pos hi, pure_bind, setupEchoDataStep]
    · have hc : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      rw [show setupRevealSteps phase coalition parts committed i = _ from if_neg hi]
      simp only [if_neg hi, if_neg hc]
      change advance (exchangeResume _ (setupRevealInbox phase coalition parts committed sent i)) = _
      rw [advance_setupRevealResume, map_eq_bind_pure_comp]
      rfl
  · rw [sequenceFin_bind_pure]
    simp only [bind_assoc, pure_bind, setupRevealComputations]

/-- The echo continuation has no free hash queries, even when some operators aborted. -/
theorem stepRound_setupEchoDataSteps (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (data : C.Party → Option (SeedGenEchoData C)) :
    stepRound localRoles coalition A noFunctionality state (fun i => setupEchoDataStep phase i (data i)) =
    (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (setupEchoDataStep phase i (data i)).outbox c else none
      pure (st, (fun i => Step.done (match data i with
        | none => none
        | some (keys, shared) => if i ∈ coalition.1 then none else
          let inbox := roundInbox coalition sent (fun j => setupEchoDataStep phase j (data j)) i
          if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
            if echoCheck phase i keys shared inbox then some (keysOf keys) else none)), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (OverPermutation.sequenceFin (fun i => (pure (Step.done (match data i with
        | none => none
        | some (keys, shared) => if i ∈ coalition.1 then none else
          let inbox := roundInbox coalition sent (fun j => setupEchoDataStep phase j (data j)) i
          if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
            if echoCheck phase i keys shared inbox then some (keysOf keys) else none)) :
      OracleComp (LocalSpec C) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    cases hd : data i with
    | none => rfl
    | some v =>
      rcases v with ⟨keys, shared⟩
      by_cases hi : i ∈ coalition.1
      · simp only [setupEchoDataStep, if_pos hi]
      · simp only [setupEchoDataStep, if_neg hi]
        exact advance_setupEchoResume phase i keys shared _
  · rw [sequenceFin_pure, pure_bind]

def setupEchoDataOutput (phase : Phase) (coalition : C.Coalition) (data : C.Party → Option (SeedGenEchoData C))
    (sent : C.Party → Mail C E) (i : C.Party) : Option (Keys C) :=
  match data i with
  | none => none
  | some (keys, shared) => if i ∈ coalition.1 then none else
      let inbox := roundInbox coalition sent (fun j => setupEchoDataStep phase j (data j)) i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if echoCheck phase i keys shared inbox then some (keysOf keys) else none

/-- The complete last round after its honest work has already been computed. -/
def setupFinishLocal (phase : Phase) (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (data : C.Party → Option (SeedGenEchoData C)) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → data i = none then pure (state, fun _ => none) else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (setupEchoDataStep phase i (data i)).outbox c else none
    pure (st, setupEchoDataOutput phase coalition data sent)

theorem executeRounds_setupEchoDataSteps_one (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (data : C.Party → Option (SeedGenEchoData C)) :
    executeRounds localRoles coalition A noFunctionality 1 state (fun i => setupEchoDataStep phase i (data i)) =
      setupFinishLocal phase coalition A state data := by
  have hd : (∀ i, i ∉ coalition.1 → (setupEchoDataStep phase (E := E) i (data i)).isDone) ↔
      ∀ i, i ∉ coalition.1 → data i = none := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    cases data i <;> simp [setupEchoDataStep, Step.isDone]
  rw [executeRounds]
  simp only [hd, setupFinishLocal]
  split_ifs with ha
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    cases data i <;> rfl
  · rw [stepRound_setupEchoDataSteps]
    simp only [bind_assoc, pure_bind, executeRounds, Step.output]
    rfl

/-- The remaining two rounds, with every early-exit and abort test explicit. -/
def setupPostCommitLocal (phase : Phase) (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true then
    pure (state, fun _ => none)
  else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (setupRevealSteps phase coalition parts committed i).outbox c else none
    let data ← setupRevealComputations phase coalition parts committed sent
    setupFinishLocal phase coalition A st data

theorem executeRounds_setupRevealSteps_two (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) :
    executeRounds localRoles coalition A noFunctionality 2 state (setupRevealSteps phase coalition parts committed) =
      setupPostCommitLocal phase coalition A state parts committed := by
  have hd : (∀ i, i ∉ coalition.1 → (setupRevealSteps phase coalition parts committed i).isDone) ↔
      ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    simp only [setupRevealSteps, hi, false_or]
    split_ifs <;> simp_all [Step.isDone]
  rw [executeRounds]
  simp only [hd, setupPostCommitLocal]
  split_ifs with ha
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    unfold setupRevealSteps
    split_ifs <;> rfl
  · rw [stepRound_setupRevealSteps]
    simp only [bind_assoc, pure_bind, executeRounds_setupEchoDataSteps_one]

/-- A fully split local game: start, commit, reveal, echo and final distinguish. -/
def setupNormalizedLocalGame (phase : Phase) (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← OverPermutation.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let commitments ← setupInitialCommitments phase coalition parts
  let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (commitments i) c else none
  let r ← setupPostCommitLocal phase coalition A st parts (setupCommitInbox phase coalition parts commitments sent)
  Z r

/-- The complete real game has the explicit three-round normal form, including arbitrary aborts. -/
theorem sameRun_setupLocal_normalized (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SameRun prims (setupLocalGame phase coalition A x z Z) (setupNormalizedLocalGame phase coalition A x z Z) := by
  refine (sameRun_setupLocal_split phase prims coalition A x z Z).trans (SameRun.of_eq ?_)
  simp only [setupLocalCommitPrefix, seedGenLocalPostCommit, setupNormalizedLocalGame,
    stepRound_setupInitialSteps, bind_assoc, pure_bind]
  change _ = _
  simp only [setupRounds, Nat.reduceSub, executeRounds_setupRevealSteps_two]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- All random-oracle inputs of one local query; a PRG call includes its internal hash. -/
def seedGenLocalHashInputs : (LocalSpec C).Domain → List (Query C)
  | .inl _ => []
  | .inr (.inl q) => [q]
  | .inr (.inr x) => [.streamKey x.2.1]

/-- Instrument a local computation without changing any of its oracle answers. -/
def seedGenHashLog {α : Type} (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (α × List (Query C)) :=
  (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend (fun t _ => seedGenLocalHashInputs t)) oa).run

@[simp] theorem seedGenHashLog_pure {α : Type} (a : α) :
    seedGenHashLog (C := C) (pure a) = pure (a, []) := rfl

theorem seedGenHashLog_fst {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> seedGenHashLog oa = oa := by
  unfold seedGenHashLog
  rw [QueryImpl.fst_map_run_withTraceAppend]
  simp

theorem seedGenHashLog_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) :
    seedGenHashLog (oa >>= k) = (do
      let (a, l) ← seedGenHashLog oa
      let (b, r) ← seedGenHashLog (k a)
      pure (b, l ++ r)) := by
  simp [seedGenHashLog, simulateQ_bind, WriterT.run_bind]

theorem seedGenHashLog_hash (q : Query C) :
    seedGenHashLog (liftComp (hashQuery q) (LocalSpec C)) =
      (fun y => (y, [q])) <$> liftComp (hashQuery q) (LocalSpec C) := by
  change (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend
    (fun t _ => seedGenLocalHashInputs t))
    (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))).run = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  rfl

/-- Syntactic support of an instrumented computation, including arbitrary oracle answers. -/
def SeedGenUsesOnly {α : Type} (Q : Query C → Prop) (oa : OracleComp (LocalSpec C) α) : Prop :=
  ∀ r ∈ support (seedGenHashLog oa), ∀ q ∈ r.2, Q q

theorem SeedGenUsesOnly.pure {α : Type} (Q : Query C → Prop) (a : α) :
    SeedGenUsesOnly Q (pure a) := by
  simp [SeedGenUsesOnly]

theorem SeedGenUsesOnly.mono {α : Type} {P Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    (h : SeedGenUsesOnly P oa) (hp : ∀ q, P q → Q q) : SeedGenUsesOnly Q oa :=
  fun r hr q hq => hp q (h r hr q hq)

theorem SeedGenUsesOnly.bind {α β : Type} {Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    {k : α → OracleComp (LocalSpec C) β} (h : SeedGenUsesOnly Q oa)
    (hk : ∀ a, SeedGenUsesOnly Q (k a)) : SeedGenUsesOnly Q (oa >>= k) := by
  intro r hr q hq
  rw [seedGenHashLog_bind] at hr
  simp only [support_bind, Set.mem_iUnion, Prod.exists, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, l, hal, b, t, hbt, rfl⟩ := hr
  rcases List.mem_append.mp hq with hq | hq
  · exact h (a, l) hal q hq
  · exact hk a (b, t) hbt q hq

theorem SeedGenUsesOnly.map {α β : Type} {Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    (h : SeedGenUsesOnly Q oa) (f : α → β) : SeedGenUsesOnly Q (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a => SeedGenUsesOnly.pure Q (f a)

theorem SeedGenUsesOnly.hash {Q : Query C → Prop} (q : Query C) (hq : Q q) :
    SeedGenUsesOnly Q (liftComp (hashQuery q) (LocalSpec C)) := by
  intro r hr q' hq'
  rw [seedGenHashLog_hash] at hr
  rw [support_map, Set.mem_image] at hr
  rcases hr with ⟨y, _, rfl⟩
  simpa using List.mem_singleton.mp hq' ▸ hq

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The points query test includes the internal hash of a counted PRG call. -/
def SeedGenTouches (points : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q ∈ seedGenLocalHashInputs t, points q

/-- Stop a local computation immediately before its first points query. -/
def seedGenAvoid (points : Query C → Prop) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (Option α) :=
  (simulateQ (fun t => (if SeedGenTouches points t then failure else
    OptionT.lift (OracleComp.lift (OracleSpec.query t)) : OptionT (OracleComp (LocalSpec C)) _)) oa).run

@[simp] theorem seedGenAvoid_pure (points : Query C → Prop) {α : Type} (a : α) :
    seedGenAvoid points (pure a) = pure (some a) := rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

def SeedGenGoodLog (points : Query C → Prop) (l : List (Query C)) : Prop := ∀ q ∈ l, ¬ points q

@[simp] theorem seedGenGoodLog_append (points : Query C → Prop) (l r : List (Query C)) :
    SeedGenGoodLog points (l ++ r) ↔ SeedGenGoodLog points l ∧ SeedGenGoodLog points r := by
  simp [SeedGenGoodLog, List.mem_append, or_imp, forall_and]

@[simp] theorem seedGenGoodLog_local (points : Query C → Prop) (t : (LocalSpec C).Domain) :
    SeedGenGoodLog points (seedGenLocalHashInputs t) ↔ ¬ SeedGenTouches points t := by
  simp [SeedGenGoodLog, SeedGenTouches]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Only raw derivation inputs of hidden names are excluded. Echo inputs remain unrestricted. -/
def SetupHiddenInput (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C) (q : Query C) : Prop :=
  ∃ name, Hidden coalition name ∧ setupNamedInput phase parts name = q

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The deterministic reveal result under a fixed oracle, with both actual abort tests. -/
def setupRevealDataFixed (phase : Phase) (prims : Primitives) (h : Query C → HashOutput) (i : C.Party)
    (own : Parts C) (committed revealed : Mail C E) : Option (SeedGenEchoData C) :=
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then none else
    if openCheck phase i own committed revealed (D prims h (openQueries phase i revealed)) then
      let keys := D prims h (deriveKeys phase i (setupView phase i own revealed))
      some (keys, D prims h (sharedQueries phase i keys))
    else none

theorem simulateQ_fixedLocal_setupRevealCompute (phase : Phase) (prims : Primitives) (h : Query C → HashOutput)
    (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    simulateQ (fixedLocal prims h) (setupRevealCompute phase i own committed revealed) =
      pure (setupRevealDataFixed phase prims h i own committed revealed) := by
  unfold setupRevealCompute setupRevealDataFixed
  by_cases ha : (C.parties.any fun j => Msg.isAbort (revealed j)) = true
  · simp only [if_pos ha, simulateQ_pure]
  · simp only [if_neg ha, pure_bind, simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind]
    by_cases ho : openCheck phase i own committed revealed (D prims h (openQueries phase i revealed))
    · simp only [ho, not_true_eq_false, if_false, if_true, pure_bind, simulateQ_bind,
        simulateQ_fixedLocal_liftComp, simulateQ_pure]
    · simp only [ho, not_false_eq_true, if_true, if_false, simulateQ_pure]

def setupRevealAllFixed (phase : Phase) (prims : Primitives) (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    C.Party → Option (SeedGenEchoData C) := fun i =>
  if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then none else
    setupRevealDataFixed phase prims h i (parts i) (committed i) (setupRevealInbox phase coalition parts committed sent i)

theorem simulateQ_fixedLocal_setupRevealComputations (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (setupRevealComputations phase coalition parts committed sent) =
      pure (setupRevealAllFixed phase prims coalition h parts committed sent) := by
  rw [setupRevealComputations, simulateQ_sequenceFin]
  trans OverPermutation.sequenceFin (fun i => (pure (setupRevealAllFixed phase prims coalition h parts committed sent i) : ProbComp _))
  · congr 1
    funext i
    unfold setupRevealAllFixed
    split_ifs
    · rfl
    · exact simulateQ_fixedLocal_setupRevealCompute phase prims h i (parts i) (committed i) _
  · exact sequenceFin_pure _

/-- A successful echo output supplies the actual inbox checks and its honest key value. -/
theorem setupEchoDataOutput_some (phase : Phase) (coalition : C.Coalition) (data : C.Party → Option (SeedGenEchoData C))
    (sent : C.Party → Mail C E) (i : C.Party) (key : Keys C)
    (ho : setupEchoDataOutput phase coalition data sent i = some key) :
    i ∉ coalition.1 ∧ ∃ keys shared,
      data i = some (keys, shared) ∧ key = keysOf keys ∧
      (C.parties.any fun j => Msg.isAbort (roundInbox coalition sent (fun j => setupEchoDataStep phase j (data j)) i j)) = false ∧
      echoCheck phase i keys shared (roundInbox coalition sent (fun j => setupEchoDataStep phase j (data j)) i) := by
  unfold setupEchoDataOutput at ho
  cases hd : data i with
  | none => simp only [hd] at ho; contradiction
  | some v =>
    rcases v with ⟨keys, shared⟩
    simp only [hd] at ho
    split_ifs at ho with hi hb hc <;> try contradiction
    refine ⟨hi, keys, shared, rfl, (Option.some.inj ho).symm, ?_, hc⟩
    exact Bool.eq_false_iff.mpr hb

/-- Every honest operator reached its echo step if any honest output survives. -/
theorem setupEchoDataOutput_all_some (phase : Phase) (coalition : C.Coalition)
    (data : C.Party → Option (SeedGenEchoData C)) (sent : C.Party → Mail C E)
    (i : C.Party) (key : Keys C) (ho : setupEchoDataOutput phase coalition data sent i = some key) :
    ∀ j, j ∉ coalition.1 → (data j).isSome := by
  obtain ⟨_, keys, shared, _, _, ha, _⟩ := setupEchoDataOutput_some phase coalition data sent i key ho
  intro j hj
  cases hd : data j with
  | some v => rfl
  | none =>
    have hn := List.any_eq_false.mp ha j (List.mem_finRange j)
    simp only [roundInbox, if_neg hj, hd, setupEchoDataStep, Step.delivered, Msg.isAbort] at hn
    exact (hn trivial).elim

/-- A non-aborting deterministic reveal supplies its actual derived keys and shared hashes. -/
theorem setupRevealAllFixed_some (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E)
    (i : C.Party) (ha : (setupRevealAllFixed phase prims coalition h parts committed sent i).isSome) :
    let revealed := setupRevealInbox phase coalition parts committed sent
    let keys := D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i)))
    setupRevealAllFixed phase prims coalition h parts committed sent i =
      some (keys, D prims h (sharedQueries phase i keys)) ∧
    (C.parties.any fun j => Msg.isAbort (revealed i j)) = false := by
  unfold setupRevealAllFixed setupRevealDataFixed at ha ⊢
  dsimp only
  split_ifs with hi hr hc <;> simp_all

/-- Outside the stated shared-hash collision event, acceptance gives the honest agreements
required by output identification. -/
theorem setupRevealAllFixed_output_agreement (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent echoSent : C.Party → Mail C E)
    (i : C.Party) (key : Keys C)
    (ho : setupEchoDataOutput phase coalition (setupRevealAllFixed phase prims coalition h parts committed sent) echoSent i = some key)
    (hn : ∀ j, j ∉ coalition.1 →
      let revealed := setupRevealInbox phase coalition parts committed sent
      let ki := D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i)))
      let kj := D prims h (deriveKeys phase j (setupView phase j (parts j) (revealed j)))
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj.2.1)) :
    let revealed := setupRevealInbox phase coalition parts committed sent
    let keys := fun j => D prims h (deriveKeys phase j (setupView phase j (parts j) (revealed j)))
    i ∉ coalition.1 ∧ key = keysOf (keys i) ∧
    (∀ k j, j ∉ coalition.1 → j ≠ k → Msg.hashesOf (revealed k j) = revealTo phase (parts j) j k) ∧
    ∀ j, j ∉ coalition.1 → (keys i).1 = (keys j).1 ∧
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → (keys i).2.1 T = (keys j).2.1 T := by
  let data := setupRevealAllFixed phase prims coalition h parts committed sent
  let revealed := setupRevealInbox phase coalition parts committed sent
  let keys := fun j => D prims h (deriveKeys phase j (setupView phase j (parts j) (revealed j)))
  have hall := setupEchoDataOutput_all_some phase coalition data echoSent i key ho
  obtain ⟨hi, ki, si, hdi, hkey, _, hcheck⟩ := setupEchoDataOutput_some phase coalition data echoSent i key ho
  have hdf (j : C.Party) (hj : j ∉ coalition.1) :
      data j = some (keys j, D prims h (sharedQueries phase j (keys j))) :=
    (setupRevealAllFixed_some phase prims coalition h parts committed sent j (hall j hj)).1
  have he := Option.some.inj (hdi.symm.trans (hdf i hi))
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp he
  refine ⟨hi, hkey, setupRevealInbox_all_honest phase coalition parts committed sent i
    (setupRevealAllFixed_some phase prims coalition h parts committed sent i (hall i hi)).2, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · refine (fun hagree => ⟨setup_firstKey_agreement phase prims h i j _ _ hagree.1, hagree.2⟩)
      (setup_echoCheck_agreement phase prims h i j hji (keys i) (keys j) _ ?_ hcheck (hn j hj))
    simp only [roundInbox, if_neg hj, hdf j hj, setupEchoDataStep, Step.delivered,
      echoOutbox, if_neg (Ne.symm hji)]

/-- Complete output identification for the concrete reveal and echo execution. The protocol's
successful output supplies honest delivery, derivation and agreement facts automatically. -/
theorem setupRevealEcho_output_eq_hybrid (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (committed sent echoSent commitSent : C.Party → Mail C E) (log : CallLog C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput)
    (hextract : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      extractReveal phase log commitSent j i = Msg.hashesOf (setupRevealInbox phase coalition parts committed sent i j))
    (hparameter : ∀ q ∈ setupParameterInputs phase coalition (setupProgramView phase coalition parts log commitSent),
      h q = seedGenFullParameter high parameter)
    (hzero : phase = .prss → parameter = 0)
    (hterm : ∀ T, KnownTo coalition.1 T →
      h (setupTermProgrammingInput phase coalition (setupProgramView phase coalition parts log commitSent) T) = seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates coalition,
      h (setupPairProgrammingInput phase coalition (setupProgramView phase coalition parts log commitSent) p) = pairs p)
    (i : C.Party) (key : Keys C)
    (ho : setupEchoDataOutput phase coalition (setupRevealAllFixed phase prims coalition h parts committed sent) echoSent i = some key)
    (hn : ∀ j, j ∉ coalition.1 →
      let revealed := setupRevealInbox phase coalition parts committed sent
      let ki := D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i)))
      let kj := D prims h (deriveKeys phase j (setupView phase j (parts j) (revealed j)))
      h (.sharedKeys phase ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys phase ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) phase ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys phase ((sharedTerms j i).map kj.2.1)) :
    key = dealtKeys parameter (setupHybridSeeds phase coalition h parts seeds)
      (setupHybridPairs phase coalition h parts pairs) i := by
  obtain ⟨hi, hkey, hreceived, hagree⟩ :=
    setupRevealAllFixed_output_agreement phase prims coalition h parts committed sent echoSent i key ho hn
  rw [hkey]
  exact setup_output_eq_hybrid_dealing phase prims coalition parts log commitSent _ h parameter seeds pairs high
    (fun j => D prims h (deriveKeys phase j
      (setupView phase j (parts j) (setupRevealInbox phase coalition parts committed sent j))))
    hreceived hextract (fun _ _ => rfl) hparameter hzero hterm hpair i hi hagree

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- A transcript whose queries are unchanged by any shift of a hidden private coordinate. -/
def SeedGenPrivateInvariant {α : Type} (coalition : C.Coalition) (f : (C.Party → Parts C) → α) : Prop :=
  (∀ a T, ¬ KnownTo coalition.1 T → ∀ c parts,
    f (shiftAt a (some T) none c parts) = f parts) ∧
  (∀ p : C.Pair, p.1.1 ∉ coalition.1 → p.1.2 ∉ coalition.1 → ∀ c parts,
    f (shiftAt p.1.1 none (some p.1.2) c parts) = f parts)

def seedGenDeriveHead : Query C → HashOutput
  | .derive _ _ values => values.headD 0
  | _ => 0

/-- Sample the private parts and then an arbitrary randomized transcript. -/
def seedGenPartsKernel {α : Type} (K : (C.Party → Parts C) → ProbComp α) :
    ProbComp ((C.Party → Parts C) × α) := do
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let out ← K parts
  pure (parts, out)

/-- Private-coordinate shifts preserve the complete joint law of the parts and invariant transcript. -/
theorem evalDist_seedGenPartsKernel_shift {α : Type} (K : (C.Party → Parts C) → ProbComp α)
    (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput)
    (hK : ∀ parts, K (shiftAt a term pair c parts) = K parts) :
    ((fun p => (shiftAt a term pair c p.1, p.2)) <$> seedGenPartsKernel K) =ᵈ seedGenPartsKernel K := by
  have he : (fun p => (shiftAt a term pair c p.1, p.2)) <$> seedGenPartsKernel K =
      (do let parts ← shiftAt a term pair c <$> OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))
          let out ← K parts
          pure (parts, out)) := by
    simp only [seedGenPartsKernel, map_bind, map_pure, bind_map_left, hK]
  rw [he]
  exact (evalDist_shiftAt a term pair c).bind_left _

/-- A transcript that is invariant under one hidden coordinate has exactly the uniform guessing
probability at that coordinate. This includes arbitrarily adaptive randomized computations. -/
theorem probEvent_seedGenPartsKernel_coordinate {α : Type}
    (K : (C.Party → Parts C) → ProbComp α) (X : (C.Party → Parts C) → HashOutput)
    (Y : α → HashOutput) (a : C.Party) (term : Option C.Term) (pair : Option C.Party)
    (hX : ∀ c parts, X (shiftAt a term pair c parts) = X parts ^^^ c)
    (hK : ∀ c parts, K (shiftAt a term pair c parts) = K parts) :
    Pr{let p ← seedGenPartsKernel K}[X p.1 = Y p.2] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have huniform : ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K) =ᵈ $ᵗ HashOutput := by
    apply evalDist_eq_uniform_of_probOutput_eq
    intro u v
    have hshift : ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K) =ᵈ
        ((fun d => d ^^^ (u ^^^ v)) <$> ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K)) := by
      calc ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K : ProbComp HashOutput)
        _ =ᵈ ((fun p => X p.1 ^^^ Y p.2) <$>
          ((fun p => (shiftAt a term pair (u ^^^ v) p.1, p.2)) <$> seedGenPartsKernel K) : ProbComp HashOutput) :=
            ((evalDist_seedGenPartsKernel_shift K a term pair (u ^^^ v) (hK _)).map _).symm
        _ = _ := by
          rw [Functor.map_map, Functor.map_map]
          congr 2
          funext p
          simp only [hX, BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) (Y p.2)]
    have hu : u = v ^^^ (u ^^^ v) := by
      rw [BitVec.xor_comm u v, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have he := prEvent_map_injective ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K)
      (xor_bijective (u ^^^ v)).1 v
    rw [← hu] at he
    exact (hshift.prEvent_eq _).trans he
  have he : Pr{let p ← seedGenPartsKernel K}[X p.1 = Y p.2] =
      Pr{let z ← (fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K}[z = 0] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ fun _ => BitVec.xor_eq_zero_iff.symm
  rw [he, huniform.prEvent_eq, SampleableType.prEvent_uniformSample_eq_singleton]

/-- The one-point bound for a transcript sampled adaptively, rather than a fixed proposed query. -/
theorem probEvent_setupHiddenInput_kernel_one (phase : Phase) {α : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (hinv : SeedGenPrivateInvariant coalition K)
    (target : α → Query C) :
    Pr{let p ← seedGenPartsKernel K}[SetupHiddenInput phase coalition p.1 (target p.2)] ≤
      ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have ht (T : C.Term) :
      Pr{let p ← seedGenPartsKernel K}[¬ KnownTo coalition.1 T ∧ termInput phase p.1 T = target p.2] ≤
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    by_cases hh : ¬ KnownTo coalition.1 T
    · obtain ⟨a, rest, ha⟩ := exists_first_holder T
      calc
        _ ≤ Pr{let p ← seedGenPartsKernel K}[(p.1 a).term T = seedGenDeriveHead (target p.2)] := by
          refine prEvent_mono _ _ _ fun p hp => ?_
          rw [← hp.2]
          simp [termInput, ha, seedGenDeriveHead]
        _ = _ := probEvent_seedGenPartsKernel_coordinate K (fun parts => (parts a).term T)
          (fun r => seedGenDeriveHead (target r)) a (some T) none
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.1 a T hh)
    · simp [hh]
  have hp (pair : C.Pair) :
      Pr{let p ← seedGenPartsKernel K}[pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧
        pairInput phase p.1 pair = target p.2] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    by_cases hh : pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1
    · calc
        _ ≤ Pr{let p ← seedGenPartsKernel K}[(p.1 pair.1.1).pair pair.1.2 = seedGenDeriveHead (target p.2)] := by
          refine prEvent_mono _ _ _ fun p hp => ?_
          rw [← hp.2.2]
          simp [pairInput, seedGenDeriveHead]
        _ = _ := probEvent_seedGenPartsKernel_coordinate K (fun parts => (parts pair.1.1).pair pair.1.2)
          (fun r => seedGenDeriveHead (target r)) pair.1.1 none (some pair.1.2)
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.2 pair hh.1 hh.2)
    · have he : ∀ p : (C.Party → Parts C) × α, ¬ (pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧ pairInput phase p.1 pair = target p.2) :=
        fun _ h => hh ⟨h.1, h.2.1⟩
      simp only [he, prEvent_false, zero_le]
  have hm : ∀ p : (C.Party → Parts C) × α, SetupHiddenInput phase coalition p.1 (target p.2) →
      (∃ T ∈ (Finset.univ : Finset C.Term), ¬ KnownTo coalition.1 T ∧ termInput phase p.1 T = target p.2) ∨
      (∃ pair ∈ (Finset.univ : Finset C.Pair), pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧
        pairInput phase p.1 pair = target p.2) := by
    rintro p ⟨name, hn, he⟩
    cases name with
    | parameter => exact hn.elim
    | term T => exact Or.inl ⟨T, Finset.mem_univ _, hn, he⟩
    | pair pair => exact Or.inr ⟨pair, Finset.mem_univ _, hn.1, hn.2, he⟩
  refine (prEvent_mono _ _ _ (fun p => hm p)).trans ((prEvent_or_le _ _ _).trans ?_)
  calc
    _ ≤ (∑ _T : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        (∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
      add_le_add ((prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun T _ => ht T))
        ((prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun p _ => hp p))
    _ = _ := by simp [add_mul]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

abbrev SeedGenFiniteSpec (Ω : Type) := unifSpec + ((Ω →ₒ HashOutput) + ((Ω × HashOutput) →ₒ Bool))
abbrev SeedGenFiniteCache (Ω : Type) := (Ω →ₒ HashOutput).QueryCache

def seedGenFiniteProgram {Ω : Type} [DecidableEq Ω] (x : Ω × HashOutput) :
    StateT (SeedGenFiniteCache Ω) ProbComp Bool := fun cache =>
  if (cache x.1).isSome then pure (false, cache)
  else pure (true, cache.cacheQuery x.1 x.2)

def seedGenFiniteEager {Ω : Type} [DecidableEq Ω] (h : Ω → HashOutput) :
    QueryImpl (SeedGenFiniteSpec Ω) (StateT (SeedGenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + ((QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp)) + seedGenFiniteProgram (Ω := Ω))

def seedGenFiniteLazy {Ω : Type} [DecidableEq Ω] :
    QueryImpl (SeedGenFiniteSpec Ω) (StateT (SeedGenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + ((Ω →ₒ HashOutput).randomOracle + seedGenFiniteProgram (Ω := Ω))

/-- Once a cell is cached, its unused eager-table value cannot affect any future computation,
including an adaptive programming attempt. -/
theorem seedGenFiniteEager_congr {Ω α : Type} [DecidableEq Ω]
    (oa : OracleComp (SeedGenFiniteSpec Ω) α) (h g : Ω → HashOutput) :
    ∀ cache : SeedGenFiniteCache Ω, (∀ q, cache q = none → h q = g q) →
      (simulateQ (seedGenFiniteEager h) oa).run cache =
        (simulateQ (seedGenFiniteEager g) oa).run cache := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; rfl
  | query_bind t k ih =>
    intro cache he
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q | x
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ (seedGenFiniteEager h) (k p.1)).run p.2) =
        (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ (seedGenFiniteEager g) (k p.1)).run p.2)
      simp only [bind_map_left]
      exact bind_congr fun y => ih y cache he
    · change (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _ =
        (QueryImpl.withCaching (fun q => pure (g q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _
      cases hc : cache q with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hc, QueryImpl.withCaching_run_none _ hc]
        simp only [map_pure, pure_bind, he q hc]
        apply ih
        intro q' hq'
        by_cases hn : q' = q
        · subst q'; simp at hq'
        · exact he q' (by simpa [QueryCache.cacheQuery, hn] using hq')
      | some y =>
        rw [QueryImpl.withCaching_run_some _ hc, QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind]
        exact ih y cache he
    · change seedGenFiniteProgram x cache >>= _ = seedGenFiniteProgram x cache >>= _
      unfold seedGenFiniteProgram
      split_ifs
      · simp only [pure_bind]; exact ih false cache he
      · simp only [pure_bind]
        apply ih
        intro q' hq'
        by_cases hn : q' = x.1
        · subst q'; simp at hq'
        · exact he q' (by simpa [QueryCache.cacheQuery, hn] using hq')

/-- The eager and lazy programmable worlds have exactly the same joint result/cache law.
The occupancy cache is kept separately, so eager sampling does not make programming fail. -/
theorem evalDist_seedGenFiniteEager {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (oa : OracleComp (SeedGenFiniteSpec Ω) α) :
    ∀ cache : SeedGenFiniteCache Ω,
      (simulateQ seedGenFiniteLazy oa).run cache =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput); (simulateQ (seedGenFiniteEager h) oa).run cache) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro cache
    simp only [simulateQ_pure, StateT.run_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q | x
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ seedGenFiniteLazy (k p.1)).run p.2) =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput);
              ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
                fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ (seedGenFiniteEager h) (k p.1)).run p.2)
      simp only [bind_map_left]
      refine (EvalDistEq.bind_right _ fun y => ih y cache).trans ?_
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    · change (((Ω →ₒ HashOutput).randomOracle q).run cache >>= _) =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput);
              (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _)
      cases hc : cache q with
      | some y =>
        simp only [randomOracle, QueryImpl.withCaching_run_some _ hc, pure_bind]
        exact ih y cache
      | none =>
        simp only [randomOracle, QueryImpl.withCaching_run_none _ hc, bind_map_left, map_pure, pure_bind]
        change (($ᵗ HashOutput) >>= fun y => (simulateQ seedGenFiniteLazy (k y)).run (cache.cacheQuery q y)) =ᵈ _
        refine (EvalDistEq.bind_right _ fun y => ih y (cache.cacheQuery q y)).trans ?_
        let cont := fun h : Ω → HashOutput =>
          (simulateQ (seedGenFiniteEager h) (k (h q))).run (cache.cacheQuery q (h q))
        have he (y : HashOutput) (h : Ω → HashOutput) :
            (simulateQ (seedGenFiniteEager h) (k y)).run (cache.cacheQuery q y) =
              cont (Function.update h q y) := by
          dsimp only [cont]
          rw [Function.update_self]
          apply seedGenFiniteEager_congr
          intro q' hq'
          by_cases hn : q' = q
          · subst q'; simp at hq'
          · simp [Function.update_of_ne hn]
        simp_rw [he, Function.update_eq_self]
        exact seedGenUniform_update_bind q cont
    · change (seedGenFiniteProgram x cache >>= _) =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput); seedGenFiniteProgram x cache >>= _)
      unfold seedGenFiniteProgram
      split_ifs
      · simp only [pure_bind]; exact ih false cache
      · simp only [pure_bind]; exact ih true (cache.cacheQuery x.1 x.2)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Every underlying hash input, including a PRG's hash and a programming attempt. -/
def seedGenWorldHashInputs : (WorldSpec C).Domain → Finset (Query C)
  | .inl (.inl t) => (seedGenLocalHashInputs t).toFinset
  | .inl (.inr x) => {x.1}
  | .inr t => (seedGenLocalHashInputs t).toFinset

/-- Syntactic coverage of every possible branch by a finite hash-input domain. -/
inductive SeedGenWorldCovered (S : Finset (Query C)) {α : Type} : OracleComp (WorldSpec C) α → Prop
  | pure (a : α) : SeedGenWorldCovered S (pure a)
  | query_bind (t : (WorldSpec C).Domain) (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α)
      (ht : seedGenWorldHashInputs t ⊆ S) (hk : ∀ y, SeedGenWorldCovered S (k y)) :
      SeedGenWorldCovered S (OracleComp.lift (OracleSpec.query t) >>= k)

theorem SeedGenWorldCovered.mono {S T : Finset (Query C)} {α : Type}
    {oa : OracleComp (WorldSpec C) α} (h : SeedGenWorldCovered S oa) (hst : S ⊆ T) :
    SeedGenWorldCovered T oa := by
  induction h with
  | pure a => exact .pure a
  | query_bind t k ht hk ih => exact .query_bind t k (ht.trans hst) ih

/-- Finite answer ranges give a finite envelope even for an arbitrarily adaptive world program. -/
theorem seedGenWorldCovered_exists {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∃ S : Finset (Query C), SeedGenWorldCovered S oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨∅, .pure a⟩
  | query_bind t k ih =>
    have hi : Finite ((WorldSpec C).Range t) := by
      rcases t with (n | q | x) | x | (n | q | x) <;> infer_instance
    letI := Fintype.ofFinite ((WorldSpec C).Range t)
    choose S hS using ih
    refine ⟨seedGenWorldHashInputs t ∪ Finset.univ.biUnion S, .query_bind t k ?_ ?_⟩
    · exact Finset.subset_union_left
    · intro y
      apply (hS y).mono
      intro q hq
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, hq⟩)

def seedGenRestrictCache (S : Finset (Query C)) (cache : HashCache C) : SeedGenFiniteCache S :=
  QueryCache.ofFn fun q => cache q.1

theorem seedGenRestrictCache_update (S : Finset (Query C)) (cache : HashCache C)
    (q : Query C) (hq : q ∈ S) (y : HashOutput) :
    seedGenRestrictCache S (cache.cacheQuery q y) =
      (seedGenRestrictCache S cache).cacheQuery ⟨q, hq⟩ y := by
  refine QueryCache.ext fun q' => ?_
  by_cases he : q'.1 = q
  · have he' : q' = ⟨q, hq⟩ := Subtype.ext he
    subst q'
    simp [seedGenRestrictCache]
  · have he' : q' ≠ ⟨q, hq⟩ := fun h => he (congrArg Subtype.val h)
    simp [seedGenRestrictCache, QueryCache.cacheQuery, he, he']

/-- Translation to a finite domain keeps fixed `Th` calls deterministic. -/
def seedGenFiniteHash (prims : Primitives) (S : Finset (Query C)) (q : Query C) :
    OracleComp (SeedGenFiniteSpec S) HashOutput :=
  match q with
  | .hash input => if MpcInput input then pure (prims.Th input) else
      if hq : q ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0
  | _ => if hq : q ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0

def seedGenFiniteLocal (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (LocalSpec C) (OracleComp (SeedGenFiniteSpec S)) :=
  (fun n : ℕ => OracleComp.lift ((SeedGenFiniteSpec S).query (.inl n)) : QueryImpl unifSpec (OracleComp (SeedGenFiniteSpec S))) +
    (seedGenFiniteHash prims S + fun x : PrgInput C => do
      let y ← seedGenFiniteHash prims S (.streamKey x.2.1)
      pure (prims.aes.eval (truncateHash y) x.2.2))

def seedGenFiniteProgramming (S : Finset (Query C)) (x : Query C × HashOutput) :
    OracleComp (SeedGenFiniteSpec S) Bool :=
  if IsFixed x.1 then pure false else
    if hx : x.1 ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inr (⟨x.1, hx⟩, x.2)))) else pure false

def seedGenFiniteWorld (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (WorldSpec C) (OracleComp (SeedGenFiniteSpec S)) :=
  seedGenFiniteLocal prims S + seedGenFiniteProgramming S + seedGenFiniteLocal prims S

/-- A hash call's exact joint answer/cache law survives restriction to its finite domain. -/
theorem seedGenFiniteHash_run (prims : Primitives) (S : Finset (Query C))
    (q : Query C) (hq : q ∈ S) (cache : HashCache C) :
    (fun r : HashOutput × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (hashAnswer prims q).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteHash prims S q)).run (seedGenRestrictCache S cache) := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    rw [hashAnswer_of_isFixed prims hi]
    simp [seedGenFiniteHash, hi, seedGenRestrictCache]
  · have ht : seedGenFiniteHash prims S q = OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) := by
      cases q <;> simp_all [seedGenFiniteHash, IsFixed]
    rw [ht, hashAnswer_of_not_isFixed prims hf]
    erw [simulateQ_spec_query]
    change _ <$> ((Query C →ₒ HashOutput).randomOracle q).run cache =
      ((S →ₒ HashOutput).randomOracle ⟨q, hq⟩).run (seedGenRestrictCache S cache)
    cases hc : cache q with
    | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc,
        QueryImpl.withCaching_run_none _ (show seedGenRestrictCache S cache ⟨q, hq⟩ = none from hc)]
      simp only [Functor.map_map, seedGenRestrictCache_update S cache q hq]
      rfl
    | some y =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc,
        QueryImpl.withCaching_run_some _ (show seedGenRestrictCache S cache ⟨q, hq⟩ = some y from hc)]
      rfl

/-- The finite translation also preserves private sampling and internal PRG hashes. -/
theorem seedGenFiniteLocal_run (prims : Primitives) (S : Finset (Query C))
    (t : (LocalSpec C).Domain) (ht : ∀ q ∈ seedGenLocalHashInputs t, q ∈ S) (cache : HashCache C) :
    (fun r : (LocalSpec C).Range t × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (localAnswer prims t).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteLocal prims S t)).run (seedGenRestrictCache S cache) := by
  rcases t with n | q | x
  · change _ <$> (fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _) = _
    simp only [Functor.map_map]
    rfl
  · exact seedGenFiniteHash_run prims S q (ht q (by simp [seedGenLocalHashInputs])) cache
  · change _ <$> (prgAnswer prims x).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
      simulateQ_bind, simulateQ_pure]
    rw [← seedGenFiniteHash_run prims S (.streamKey x.2.1)
      (ht _ (by simp [seedGenLocalHashInputs])) cache, bind_map_left]

/-- Fresh-only programming, including its returned success bit, is preserved. -/
theorem seedGenFiniteProgramming_run (S : Finset (Query C))
    (x : Query C × HashOutput) (hx : x.1 ∈ S) (cache : HashCache C) :
    (fun r : Bool × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (programAnswer x).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteProgramming S x)).run (seedGenRestrictCache S cache) := by
  rw [programAnswer_run_cache]
  unfold seedGenFiniteProgramming programCache
  by_cases hf : IsFixed x.1
  · simp [hf]
  · simp only [hf, false_or, if_false, dif_pos hx]
    erw [simulateQ_spec_query]
    change _ = seedGenFiniteProgram (⟨x.1, hx⟩, x.2) (seedGenRestrictCache S cache)
    unfold seedGenFiniteProgram
    by_cases hc : (cache x.1).isSome
    · simp [seedGenRestrictCache, hc]
    · simp [seedGenRestrictCache, hc]
      exact seedGenRestrictCache_update S cache x.1 hx x.2

/-- Both oracle copies and programming use the same restricted cache. -/
theorem seedGenFiniteWorld_run (prims : Primitives) (S : Finset (Query C))
    (t : (WorldSpec C).Domain) (ht : seedGenWorldHashInputs t ⊆ S) (cache : HashCache C) :
    (fun r : (WorldSpec C).Range t × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (worldAnswer prims t).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteWorld prims S t)).run (seedGenRestrictCache S cache) := by
  rcases t with t | t
  · rcases t with t | x
    · exact seedGenFiniteLocal_run prims S t (fun q hq => ht (by simpa [seedGenWorldHashInputs] using hq)) cache
    · exact seedGenFiniteProgramming_run S x (ht (by simp [seedGenWorldHashInputs])) cache
  · exact seedGenFiniteLocal_run prims S t (fun q hq => ht (by simpa [seedGenWorldHashInputs] using hq)) cache

/-- The finite translation preserves complete executions, not just individual oracle calls. -/
theorem seedGenFiniteWorld_simulate_run (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hc : SeedGenWorldCovered S oa) :
    ∀ cache : HashCache C,
      (fun r : α × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
          (simulateQ (worldAnswer prims) oa).run cache =
        (simulateQ seedGenFiniteLazy (simulateQ (seedGenFiniteWorld prims S) oa)).run
          (seedGenRestrictCache S cache) := by
  induction hc with
  | pure a => intro cache; rfl
  | query_bind t k ht hk ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← seedGenFiniteWorld_run prims S t ht cache, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

/-- Full lazy-to-eager conversion for a programmable world, from every initial cache. -/
theorem evalDist_seedGenWorld_eager (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hc : SeedGenWorldCovered S oa)
    (cache : HashCache C) :
    (simulateQ (worldAnswer prims) oa).run' cache =ᵈ
      (do let h ← $ᵗ (S → HashOutput);
            (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteWorld prims S) oa)).run'
              (seedGenRestrictCache S cache)) := by
  have he := congrArg (Functor.map Prod.fst) (seedGenFiniteWorld_simulate_run prims S oa hc cache)
  simp only [Functor.map_map] at he
  change (simulateQ (worldAnswer prims) oa).run' cache =
    (simulateQ seedGenFiniteLazy (simulateQ (seedGenFiniteWorld prims S) oa)).run'
      (seedGenRestrictCache S cache) at he
  rw [he, StateT.run'_eq]
  refine ((evalDist_seedGenFiniteEager _ _).map _).trans ?_
  simp only [StateT.run'_eq]
  rw [map_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The fixed total oracle represented by a finite table; the MPC domains still use `Th`. -/
def seedGenFiniteTotal (prims : Primitives) (S : Finset (Query C)) (h : S → HashOutput)
    (q : Query C) : HashOutput :=
  match q with
  | .hash input => if MpcInput input then prims.Th input else
      if hq : q ∈ S then h ⟨q, hq⟩ else 0
  | _ => if hq : q ∈ S then h ⟨q, hq⟩ else 0

/-- Reading a table value into the occupancy cache leaves the overlaid total function unchanged. -/
theorem seedGenTableExtending_read {Ω : Type} [DecidableEq Ω] (cache : SeedGenFiniteCache Ω)
    (h : Ω → HashOutput) (q : Ω) :
    tableExtending (cache.cacheQuery q (tableExtending cache h q)) h = tableExtending cache h := by
  rw [tableExtending_cacheQuery, Function.update_eq_self]

/-- An eager hash step preserves the total oracle, although it records occupancy for later
programming attempts. -/
theorem seedGenFiniteHash_eager_step (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) (q : Query C) (cache : SeedGenFiniteCache S) :
    ∃ cache',
      (simulateQ (seedGenFiniteEager h) (seedGenFiniteHash prims S q)).run cache =
        pure (seedGenFiniteTotal prims S (tableExtending cache h) q, cache') ∧
      tableExtending cache' h = tableExtending cache h := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    exact ⟨cache, by simp [seedGenFiniteHash, seedGenFiniteTotal, hi], rfl⟩
  · have hred : seedGenFiniteHash prims S q =
        if hq : q ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0 := by
      cases q <;> simp_all [seedGenFiniteHash, IsFixed]
    have hv : seedGenFiniteTotal prims S (tableExtending cache h) q =
        if hq : q ∈ S then tableExtending cache h ⟨q, hq⟩ else 0 := by
      cases q <;> simp_all [seedGenFiniteTotal, IsFixed]
    rw [hred, hv]
    by_cases hq : q ∈ S
    · rw [dif_pos hq, dif_pos hq]
      erw [simulateQ_spec_query]
      change ∃ cache',
        (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (S →ₒ HashOutput) ProbComp)
          ⟨q, hq⟩).run cache = pure (tableExtending cache h ⟨q, hq⟩, cache') ∧ _
      cases hc : cache ⟨q, hq⟩ with
      | none =>
        refine ⟨cache.cacheQuery ⟨q, hq⟩ (h ⟨q, hq⟩), ?_, ?_⟩
        · rw [QueryImpl.withCaching_run_none _ hc]
          simp [tableExtending, hc]
        · simpa only [tableExtending, hc, Option.getD_none] using seedGenTableExtending_read cache h ⟨q, hq⟩
      | some y =>
        refine ⟨cache, ?_, rfl⟩
        rw [QueryImpl.withCaching_run_some _ hc]
        simp [tableExtending, hc]
    · exact ⟨cache, by simp [hq], rfl⟩

/-- After the last programming block, the whole adaptive local computation sees one fixed
oracle. Private honest hashes do not change that oracle or restrict later legitimate queries. -/
theorem seedGenFiniteLocal_eager_fixed (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ cache : SeedGenFiniteCache S,
      (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S) oa)).run' cache =
        simulateQ (fixedLocal prims (seedGenFiniteTotal prims S (tableExtending cache h))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; rfl
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rcases t with n | q | x
    · change ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        (fun p : unifSpec.Range n × SeedGenFiniteCache S =>
          Prod.fst <$> (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S) (k p.1))).run p.2) = _
      rw [bind_map_left]
      apply bind_congr
      intro y
      exact ih y cache
    · obtain ⟨cache', he, ht⟩ := seedGenFiniteHash_eager_step prims S h q cache
      change (simulateQ (seedGenFiniteEager h) (seedGenFiniteHash prims S q)).run cache >>= _ = _
      rw [he, pure_bind]
      change (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S)
        (k (seedGenFiniteTotal prims S (tableExtending cache h) q)))).run' cache' = _
      rw [ih, ht]
      rfl
    · obtain ⟨cache', he, ht⟩ := seedGenFiniteHash_eager_step prims S h (.streamKey x.2.1) cache
      change (simulateQ (seedGenFiniteEager h) (seedGenFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run cache >>= _ = _
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, he, pure_bind]
      change (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S)
        (k (prims.aes.eval (truncateHash (seedGenFiniteTotal prims S (tableExtending cache h)
          (.streamKey x.2.1))) x.2.2)))).run' cache' = _
      rw [ih, ht]
      rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The number of actual programming attempts; it does not depend on the transcript. -/
def seedGenProgrammingCount (coalition : C.Coalition) : ℕ :=
  1 + (seedGenKnownCoordinates coalition).length + (seedGenCrossCoordinates coalition).length

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Erase only private coordinates that no corrupt recipient receives. -/
def seedGenExposedParts (coalition : C.Coalition) (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => ⟨(parts i).parameter,
    fun T => if KnownTo coalition.1 T then (parts i).term T else 0,
    fun j => if i ∈ coalition.1 ∨ j ∈ coalition.1 then (parts i).pair j else 0⟩

theorem seedGenExposedParts_privateInvariant (coalition : C.Coalition) :
    SeedGenPrivateInvariant coalition (seedGenExposedParts coalition) := by
  constructor
  · intro a T hh c parts
    funext i
    change Parts.mk _ _ _ = Parts.mk _ _ _
    congr 1
    · simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext U
      by_cases hU : KnownTo coalition.1 U
      · have hne : T ≠ U := fun he => hh (he ▸ hU)
        by_cases hi : i = a <;> simp [hU, shiftAt, shiftParts, hne, hi]
      · simp [seedGenExposedParts, hU]
    · funext j
      simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
  · intro p ha hb c parts
    funext i
    change Parts.mk _ _ _ = Parts.mk _ _ _
    congr 1
    · simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext T
      simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext j
      by_cases hi : i = p.1.1
      · subst i
        by_cases hj : j = p.1.2
        · subst j; simp [seedGenExposedParts, ha, hb]
        · simp [seedGenExposedParts, shiftAt, shiftParts, Ne.symm hj]
      · simp [seedGenExposedParts, shiftAt, hi]

theorem setupExposedParts_reveal (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (i j : C.Party) (hj : j ∈ coalition.1) :
    revealTo phase (seedGenExposedParts coalition parts i) i j = revealTo phase (parts i) i j := by
  simp only [revealTo, seedGenExposedParts, hj, or_true, if_true]
  congr 2
  apply List.map_congr_left
  intro T hT
  simp [seedGen_sharedTerms_known coalition i j hj T hT]

/-- Commit-round aborts depend only on the corrupt messages, including self messages. -/
def seedGenCommitAborted (coalition : C.Coalition) (sent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ coalition.1 then Msg.isAbort (sent j i) else false

theorem setupCommitInbox_aborted (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (setupCommitInbox phase coalition parts commitments sent i j)) =
      seedGenCommitAborted coalition sent i := by
  unfold seedGenCommitAborted
  apply congrArg (fun f => C.parties.any f)
  funext j
  by_cases hj : j ∈ coalition.1
  · simp [setupCommitInbox, roundInbox, hj]
  · simp [setupCommitInbox, roundInbox, setupInitialSteps, hj, setupStart,
      Step.delivered, isAbort_commitOutbox]

/-- The real reveal inbox expressed without private commitment digests. -/
def setupReferenceRevealInbox (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i j : C.Party) : Option (Msg E) :=
  if j ∈ coalition.1 then revealSent j i else
    if seedGenCommitAborted coalition commitSent j then some .abort else
      revealOutbox phase j (parts j) i

theorem setupRevealInbox_reference (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (commitSent revealSent : C.Party → Mail C E) :
    setupRevealInbox phase coalition parts (setupCommitInbox phase coalition parts commitments commitSent) revealSent =
      setupReferenceRevealInbox phase coalition parts commitSent revealSent := by
  funext i j
  simp only [setupRevealInbox, roundInbox, setupRevealSteps, setupCommitInbox_aborted,
    setupReferenceRevealInbox]
  by_cases hj : j ∈ coalition.1
  · simp [hj]
  · simp only [hj, false_or, if_false]
    split_ifs <;> rfl

/-- Once the reveal round has no abort, only corrupt openings need checking. -/
theorem setupOpenCheck_corrupt_iff (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (ha : (C.parties.any fun j => Msg.isAbort
      (setupReferenceRevealInbox phase coalition parts commitSent revealSent i j)) = false) :
    let commitments := fun j => D prims h (commitQueries phase j (parts j))
    let committed := setupCommitInbox phase coalition parts commitments commitSent
    let revealed := setupReferenceRevealInbox phase coalition parts commitSent revealSent
    openCheck phase i (parts i) (committed i) (revealed i)
      (D prims h (openQueries phase i (revealed i))) ↔
      ∀ j, j ∈ coalition.1 →
        (Msg.hashesOf (revealSent j i)).length = (revealTo phase (parts i) j i).length ∧
        [h (.commit phase j i (Msg.hashesOf (revealSent j i)))] = Msg.hashesOf (commitSent j i) := by
  dsimp only
  have hreceived := setupRevealInbox_all_honest phase coalition parts
    (setupCommitInbox phase coalition parts (fun j => D prims h (commitQueries phase j (parts j))) commitSent)
    revealSent i (by simpa only [setupRevealInbox_reference] using ha)
  rw [setupRevealInbox_reference] at hreceived
  simp only [openCheck, openQueries, D_mapM, D_hashQuery, getD_parties]
  constructor
  · intro ho j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simpa only [setupReferenceRevealInbox, if_pos hj, setupCommitInbox, roundInbox] using ho j hji
  · intro ho j hji
    by_cases hj : j ∈ coalition.1
    · simpa only [setupReferenceRevealInbox, if_pos hj, setupCommitInbox, roundInbox] using ho j hj
    · rw [hreceived i j hj hji]
      constructor
      · cases phase <;> simp [revealTo]
      · simp only [setupCommitInbox, roundInbox, if_neg hj, setupInitialSteps, if_neg hj,
          setupStart, Step.delivered, commitOutbox, if_neg (Ne.symm hji), Msg.hashesOf,
          D_commitQueries, getD_parties]

/-- Honest parts together with the actual corrupt openings, without unused read fields. -/
def setupCorruptView (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ coalition.1 then readReveal phase (Msg.hashesOf (revealed i j)) i j else parts j

theorem setup_derived_corruptView (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (h : Query C → HashOutput) :
    D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i))) =
      D prims h (deriveKeys phase i (setupCorruptView phase coalition parts revealed i)) := by
  have corrupt (j : C.Party) (hj : j ∈ coalition.1) :
      setupView phase i (parts i) (revealed i) j = setupCorruptView phase coalition parts revealed i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp only [setupView, if_neg hji, setupCorruptView, if_pos hj]
  have parameter (hphase : phase = .seedGen) (j : C.Party) :
      (setupView phase i (parts i) (revealed i) j).parameter =
        (setupCorruptView phase coalition parts revealed i j).parameter := by
    subst hphase
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender .seedGen coalition parts revealed hreceived i j hj, honestView_parameter]
      simp [setupCorruptView, hj]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party) (hjT : j ∈ C.holders T) :
      (setupView phase i (parts i) (revealed i) j).term T =
        (setupCorruptView phase coalition parts revealed i j).term T := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender phase coalition parts revealed hreceived i j hj,
        honestView_term phase parts hjT hiT]
      simp [setupCorruptView, hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (setupView phase i (parts i) (revealed i) a).pair b =
        (setupCorruptView phase coalition parts revealed i a).pair b := by
    by_cases ha : a ∈ coalition.1
    · rw [corrupt a ha]
    · rw [setupView_honest_sender phase coalition parts revealed hreceived i a ha,
        honestView_pair phase parts hab]
      simp [setupCorruptView, ha]
  rw [D_deriveKeys, D_deriveKeys]
  apply Prod.ext
  · dsimp only
    split_ifs with hphase
    · apply congrArg h
      apply congrArg (Query.derive phase .parameter)
      apply List.map_congr_left
      intro j _
      exact parameter hphase j
    · rfl
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive phase .term)
        apply List.map_congr_left
        intro j hj
        exact term T hiT j (by simpa using (List.mem_filter.mp hj).2)
      · simp [hiT]
    · funext j
      by_cases hji : j = i
      · simp [hji]
      · simp only [dif_neg hji]
        have hp := pairOf_left_or_right i j (Ne.symm hji)
        apply congrArg h
        apply congrArg (Query.derive phase .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

/-- Replace the hidden derived keys by an independently named table. -/
def seedGenMaskKeys (coalition : C.Coalition) (table : KeyName C → HashOutput) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) :=
  (keys.1, fun T => if KnownTo coalition.1 T then keys.2.1 T else
    if i ∈ C.holders T then table (.term T) else 0,
   fun j => if hj : j = i then 0 else
     if i ∈ coalition.1 ∨ j ∈ coalition.1 then keys.2.2 j
     else table (.pair (C.pairOf i j (Ne.symm hj))))

/-- The reference derivation uses the actual corrupt openings. -/
def setupReferenceKeys (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :=
  seedGenMaskKeys coalition table i
    (D prims h (deriveKeys phase i (setupCorruptView phase coalition parts revealed i)))

theorem setupReferenceKeys_exposed (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :
    setupReferenceKeys phase prims coalition h table (seedGenExposedParts coalition parts) revealed i =
      setupReferenceKeys phase prims coalition h table parts revealed i := by
  have hp (j : C.Party) :
      (setupCorruptView phase coalition (seedGenExposedParts coalition parts) revealed i j).parameter =
        (setupCorruptView phase coalition parts revealed i j).parameter := by
    unfold setupCorruptView
    split_ifs <;> rfl
  have ht (T : C.Term) (hT : KnownTo coalition.1 T) (j : C.Party) :
      (setupCorruptView phase coalition (seedGenExposedParts coalition parts) revealed i j).term T =
        (setupCorruptView phase coalition parts revealed i j).term T := by
    unfold setupCorruptView
    split_ifs <;> simp [seedGenExposedParts, hT]
  have hpair (a b : C.Party) (hab : a ∈ coalition.1 ∨ b ∈ coalition.1) :
      (setupCorruptView phase coalition (seedGenExposedParts coalition parts) revealed i a).pair b =
        (setupCorruptView phase coalition parts revealed i a).pair b := by
    unfold setupCorruptView
    split_ifs <;> simp [seedGenExposedParts, hab]
  simp only [setupReferenceKeys, seedGenMaskKeys, D_deriveKeys]
  apply Prod.ext
  · simp only [hp]
  · apply Prod.ext
    · funext T
      by_cases hT : KnownTo coalition.1 T
      · simp only [if_pos hT, ht T hT]
      · simp only [if_neg hT]
    · funext j
      by_cases hj : j = i
      · simp [hj]
      · simp only [dif_neg hj]
        by_cases hc : i ∈ coalition.1 ∨ j ∈ coalition.1
        · simp only [if_pos hc]
          have hab : (C.pairOf i j (Ne.symm hj)).1.1 ∈ coalition.1 ∨
              (C.pairOf i j (Ne.symm hj)).1.2 ∈ coalition.1 := by
            unfold Committee.pairOf
            split_ifs <;> simp_all [or_comm]
          simp only [hpair _ _ hab, hpair _ _ hab.symm]
        · simp only [if_neg hc]

/-- The reveal abort test, independent of every honest private part. -/
def seedGenReferenceRevealAborted (coalition : C.Coalition)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ coalition.1 then Msg.isAbort (revealSent j i)
    else seedGenCommitAborted coalition commitSent j

theorem setupReferenceRevealInbox_aborted (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (setupReferenceRevealInbox phase coalition parts commitSent revealSent i j)) =
      seedGenReferenceRevealAborted coalition commitSent revealSent i := by
  unfold seedGenReferenceRevealAborted
  apply congrArg (fun f => C.parties.any f)
  funext j
  unfold setupReferenceRevealInbox
  by_cases hj : j ∈ coalition.1
  · simp [hj]
  · simp only [if_neg hj]
    cases hb : seedGenCommitAborted coalition commitSent j <;>
      simp [hb, revealOutbox, Msg.isAbort]

/-- The length of a reveal. It has the part of `P` only in the seed generation. -/
theorem length_revealTo (phase : Phase) (c : Parts C) (i j : C.Party) :
    (revealTo phase c i j).length = parameterCount phase + (sharedTerms i j).length + 1 := by
  cases phase <;> simp [revealTo, parameterCount, Nat.add_comm]

/-- Check each actual corrupt opening against its earlier commitment and expected length. -/
def setupReferenceOpenCheck (phase : Phase) (coalition : C.Coalition) (h : Query C → HashOutput)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Prop :=
  ∀ j, j ∈ coalition.1 →
    (Msg.hashesOf (revealSent j i)).length = parameterCount phase + (sharedTerms j i).length + 1 ∧
    [h (.commit phase j i (Msg.hashesOf (revealSent j i)))] = Msg.hashesOf (commitSent j i)

/-- Concrete reference data for the echo round. Only hidden derivations are replaced. -/
def setupReferenceData (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (i : C.Party) : Option (SeedGenEchoData C) :=
  if i ∈ coalition.1 ∨ seedGenCommitAborted coalition commitSent i then none else
    if seedGenReferenceRevealAborted coalition commitSent revealSent i then none else
      if setupReferenceOpenCheck phase coalition h commitSent revealSent i then
        let keys := setupReferenceKeys phase prims coalition h table parts (fun i j => revealSent j i) i
        some (keys, D prims h (sharedQueries phase i keys))
      else none

theorem setupReferenceData_exposed (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) :
    setupReferenceData phase prims coalition h table (seedGenExposedParts coalition parts) commitSent revealSent =
      setupReferenceData phase prims coalition h table parts commitSent revealSent := by
  funext i
  simp only [setupReferenceData, setupReferenceKeys_exposed]

/-- Masking the actual reveal computation gives exactly the concrete reference data. -/
theorem setupRevealAllFixed_mask (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    let committed := setupCommitInbox phase coalition parts
      (fun j => D prims h (commitQueries phase j (parts j))) commitSent
    Option.map (fun data : SeedGenEchoData C =>
      let keys := seedGenMaskKeys coalition table i data.1
      (keys, D prims h (sharedQueries phase i keys)))
      (setupRevealAllFixed phase prims coalition h parts committed revealSent i) =
        setupReferenceData phase prims coalition h table parts commitSent revealSent i := by
  dsimp only
  unfold setupRevealAllFixed setupReferenceData
  rw [setupCommitInbox_aborted]
  by_cases hi : i ∈ coalition.1 ∨ seedGenCommitAborted coalition commitSent i = true
  · simp only [if_pos hi, Option.map_none]
  · simp only [if_neg hi, setupRevealDataFixed, setupRevealInbox_reference,
      setupReferenceRevealInbox_aborted]
    by_cases ha : seedGenReferenceRevealAborted coalition commitSent revealSent i = true
    · simp only [if_pos ha, Option.map_none]
    · simp only [if_neg ha]
      have hi' : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      have ha' : (C.parties.any fun j => Msg.isAbort
          (setupReferenceRevealInbox phase coalition parts commitSent revealSent i j)) = false := by
        rw [setupReferenceRevealInbox_aborted]
        exact Bool.eq_false_iff.mpr ha
      have hc := setupOpenCheck_corrupt_iff phase prims coalition h parts commitSent revealSent i hi' ha'
      dsimp only at hc
      have hl (j : C.Party) : (revealTo phase (parts i) j i).length =
          parameterCount phase + (sharedTerms j i).length + 1 := length_revealTo phase (parts i) j i
      simp only [hl] at hc
      change _ ↔ setupReferenceOpenCheck phase coalition h commitSent revealSent i at hc
      rw [hc]
      split_ifs with ho
      · simp only [Option.map_some]
        have hreceived := setupRevealInbox_all_honest phase coalition parts
          (setupCommitInbox phase coalition parts (fun j => D prims h (commitQueries phase j (parts j))) commitSent)
          revealSent i (by simpa only [setupRevealInbox_reference] using ha')
        rw [setupRevealInbox_reference] at hreceived
        rw [setup_derived_corruptView phase prims coalition parts _ i hi' hreceived h]
        have hv : setupCorruptView phase coalition parts
            (setupReferenceRevealInbox phase coalition parts commitSent revealSent) i =
              setupCorruptView phase coalition parts (fun i j => revealSent j i) i := by
          funext j
          unfold setupCorruptView
          split_ifs with hj
          · simp only [setupReferenceRevealInbox, if_pos hj]
          · rfl
        rw [hv]
        rfl
      · rfl

/-- A consistent named table leaves the actual hidden derivations unchanged. -/
theorem setupMaskKeys_actual (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo phase (parts j) j i)
    (htable : ∀ name, Hidden coalition name → table name = h (setupNamedInput phase parts name))
    (i : C.Party) (hi : i ∉ coalition.1) :
    seedGenMaskKeys coalition table i
      (D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i)))) =
        D prims h (deriveKeys phase i (setupView phase i (parts i) (revealed i))) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext T
    by_cases hT : KnownTo coalition.1 T
    · simp [seedGenMaskKeys, hT]
    · simp only [seedGenMaskKeys, if_neg hT]
      by_cases hiT : i ∈ C.holders T
      · rw [if_pos hiT, htable (.term T) hT,
          setup_hiddenTerm_derived phase prims coalition h parts revealed hreceived T hT i hiT]
        rfl
      · simp [hiT, D_deriveKeys]
  · funext j
    by_cases hji : j = i
    · subst j; simp [seedGenMaskKeys, D_deriveKeys]
    · simp only [seedGenMaskKeys, dif_neg hji]
      by_cases hj : j ∈ coalition.1
      · simp [hj]
      · simp only [hi, hj, or_self, if_false]
        rw [setup_hiddenPair_derived phase prims coalition h parts revealed hreceived i j hi hj hji]
        apply htable
        change (C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
          (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1
        unfold Committee.pairOf
        split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- The fixed-oracle actual reveal equals the reference when the named table records its
hidden derivations. Abort and opening failures are included in the equality. -/
theorem setupRevealAllFixed_reference (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (htable : ∀ name, Hidden coalition name → table name = h (setupNamedInput phase parts name))
    (commitSent revealSent : C.Party → Mail C E) :
    setupRevealAllFixed phase prims coalition h parts
      (setupCommitInbox phase coalition parts (fun j => D prims h (commitQueries phase j (parts j))) commitSent)
      revealSent = setupReferenceData phase prims coalition h table parts commitSent revealSent := by
  funext i
  rw [← setupRevealAllFixed_mask phase prims coalition h table parts commitSent revealSent i]
  let committed := setupCommitInbox phase coalition parts
    (fun j => D prims h (commitQueries phase j (parts j))) commitSent
  change setupRevealAllFixed phase prims coalition h parts committed revealSent i = _
  cases hd : setupRevealAllFixed phase prims coalition h parts committed revealSent i with
  | none => rfl
  | some data =>
    have hi : i ∉ coalition.1 := by
      intro hc
      simp [setupRevealAllFixed, hc] at hd
    have ha : (setupRevealAllFixed phase prims coalition h parts committed revealSent i).isSome := by
      simp only [hd, Option.isSome_some]
    obtain ⟨he, hb⟩ := setupRevealAllFixed_some phase prims coalition h parts committed revealSent i ha
    have hr := setupRevealInbox_all_honest phase coalition parts committed revealSent i hb
    have hv := Option.some.inj (hd.symm.trans he)
    simp only [hv, Option.map_some, setupMaskKeys_actual phase prims coalition h table parts _ hr htable i hi]

/-- The complete corrupt-facing reveal view, retaining honest commit aborts. -/
def setupReferenceRevealView (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent : C.Party → Mail C E) (c i : C.Party) : Option (Msg E) :=
  if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    if seedGenCommitAborted coalition commitSent i then none else revealOutbox phase i (parts i) c
  else none

theorem setupRevealSteps_view_reference (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (commitSent : C.Party → Mail C E) :
    (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (setupRevealSteps phase coalition parts (setupCommitInbox phase coalition parts commitments commitSent) i).outbox c
      else none) = setupReferenceRevealView phase coalition parts commitSent := by
  funext c i
  unfold setupReferenceRevealView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, setupRevealSteps, hc.2, false_or, setupCommitInbox_aborted]
    split_ifs <;> rfl
  · simp only [if_neg hc]

theorem setupReferenceRevealView_exposed (phase : Phase) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent : C.Party → Mail C E) :
    setupReferenceRevealView phase coalition (seedGenExposedParts coalition parts) commitSent =
      setupReferenceRevealView phase coalition parts commitSent := by
  funext c i
  unfold setupReferenceRevealView
  split_ifs with hc hb
  · rfl
  · simp only [revealOutbox, setupExposedParts_reveal phase coalition parts i c hc.1]
  · rfl

/-- The reference executes the actual adversary and actual final echo check. -/
def setupReferencePostCommit (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → seedGenCommitAborted coalition commitSent i = true then
    pure (state, fun _ => none)
  else do
    let (st, sent) ← A.round state (setupReferenceRevealView phase coalition parts commitSent)
    setupFinishLocal phase coalition A st (setupReferenceData phase prims coalition h table parts commitSent sent)

theorem setupReferencePostCommit_exposed (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    setupReferencePostCommit phase prims coalition h table A state (seedGenExposedParts coalition parts) commitSent =
      setupReferencePostCommit phase prims coalition h table A state parts commitSent := by
  simp only [setupReferencePostCommit, setupReferenceRevealView_exposed, setupReferenceData_exposed]

/-- Exact connection to both actual remaining rounds in the fixed-oracle representation. -/
theorem simulateQ_setupPostCommit_reference (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (htable : ∀ name, Hidden coalition name → table name = h (setupNamedInput phase parts name))
    (commitSent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (setupPostCommitLocal phase coalition A state parts
      (setupCommitInbox phase coalition parts (fun j => D prims h (commitQueries phase j (parts j))) commitSent)) =
      simulateQ (fixedLocal prims h) (setupReferencePostCommit phase prims coalition h table A state parts commitSent) := by
  simp only [setupPostCommitLocal, setupCommitInbox_aborted, setupReferencePostCommit]
  split_ifs with ha
  · rfl
  · rw [setupRevealSteps_view_reference]
    simp only [simulateQ_bind]
    apply bind_congr
    intro r
    rcases r with ⟨st, sent⟩
    rw [simulateQ_fixedLocal_setupRevealComputations, pure_bind,
      setupRevealAllFixed_reference phase prims coalition h table parts htable]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Actual honest commitments as seen by the corrupted recipients, under a fixed oracle. -/
def setupFixedCommitView (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (c i : C.Party) : Option (Msg E) :=
  if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (D prims h (commitQueries phase i (parts i))) c else none

theorem setupFixedCommitView_exposed (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    setupFixedCommitView phase (E := E) prims coalition h (seedGenExposedParts coalition parts) =
      setupFixedCommitView phase prims coalition h parts := by
  funext c i
  unfold setupFixedCommitView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, commitOutbox, D_commitQueries, getD_parties,
      setupExposedParts_reveal phase coalition parts i c hc.1]
  · simp only [if_neg hc]

/-- Full reference execution, with the original adversary, distinguisher, and abort behavior. -/
def setupReferenceLocalGame (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) : OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let (st, sent) ← A.round state (setupFixedCommitView phase prims coalition h parts)
  let r ← setupReferencePostCommit phase prims coalition h table A st parts sent
  Z r

theorem setupReferenceLocalGame_exposed (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    setupReferenceLocalGame phase prims coalition h table A x z Z (seedGenExposedParts coalition parts) =
      setupReferenceLocalGame phase prims coalition h table A x z Z parts := by
  simp only [setupReferenceLocalGame, setupFixedCommitView_exposed, setupReferencePostCommit_exposed]

/-- Private-coordinate independence is proved for the whole adaptive reference execution. -/
theorem setupReferenceLocalGame_privateInvariant (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SeedGenPrivateInvariant coalition (setupReferenceLocalGame phase prims coalition h table A x z Z) := by
  have he := setupReferenceLocalGame_exposed phase prims coalition h table A x z Z
  have hinv := seedGenExposedParts_privateInvariant coalition
  constructor
  · intro a T hT c parts
    rw [← he (shiftAt a (some T) none c parts), hinv.1 a T hT c parts, he parts]
  · intro p ha hb c parts
    rw [← he (shiftAt p.1.1 none (some p.1.2) c parts), hinv.2 p ha hb c parts, he parts]

theorem setupFinishLocal_queryBound (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (state : A.State) (data : C.Party → Option (SeedGenEchoData C)) :
    IsQueryBoundP (setupFinishLocal phase coalition A state data) Counted step := by
  unfold setupFinishLocal
  split_ifs
  · exact isQueryBoundP_pure Counted _ step
  · simpa using isQueryBoundP_bind (hr state _) (fun r _ => isQueryBoundP_pure Counted
      (r.1, setupEchoDataOutput phase coalition data r.2) 0)

theorem setupReferencePostCommit_queryBound (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (state : A.State) (parts : C.Party → Parts C) (sent : C.Party → Mail C E) :
    IsQueryBoundP (setupReferencePostCommit phase prims coalition h table A state parts sent) Counted (2 * step) := by
  unfold setupReferencePostCommit
  split_ifs
  · exact isQueryBoundP_pure Counted _ _
  · simpa only [two_mul] using isQueryBoundP_bind (hr state _)
      (fun r _ => setupFinishLocal_queryBound phase coalition A step hr r.1 _)

/-- The reference consumes only the original adversary/distinguisher budget. -/
theorem setupReferenceLocalGame_queryBound (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (parts : C.Party → Parts C) :
    IsQueryBoundP (setupReferenceLocalGame phase prims coalition h table A x z Z parts) Counted q := by
  obtain ⟨start, step, final, htotal, hs, hr, _, hz⟩ := hq
  unfold setupReferenceLocalGame
  have hb := isQueryBoundP_bind (hs (corruptInputs coalition x) z) (fun state _ =>
    isQueryBoundP_bind (hr state (setupFixedCommitView phase prims coalition h parts)) (fun r _ =>
      isQueryBoundP_bind (setupReferencePostCommit_queryBound phase prims coalition h table A step hr r.1 parts r.2)
        (fun out _ => hz out)))
  apply hb.mono
  simp only [setupRounds] at htotal
  omega

theorem seedGenHashLog_query (t : (LocalSpec C).Domain) :
    seedGenHashLog (OracleComp.lift ((LocalSpec C).query t)) =
      (fun u => (u, seedGenLocalHashInputs t)) <$> OracleComp.lift ((LocalSpec C).query t) := by
  simp only [seedGenHashLog, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  simp [QueryImpl.withTraceAppend_apply, QueryImpl.id', WriterT.run_bind, map_eq_bind_pure_comp]

/-- Random inputs in the transcript correspond exactly to counted calls, including PRG. -/
theorem seedGenLocalHashInputs_counted (t : (LocalSpec C).Domain) :
    ((seedGenLocalHashInputs t).filter fun q => ¬ IsFixed q).length = if Counted t then 1 else 0 := by
  rcases t with t | (q | x)
  · simp [seedGenLocalHashInputs, Counted]
  · cases q with
    | hash input =>
      have hf : IsFixed (Query.hash (C := C) input) ↔ MpcInput input := by simp [IsFixed]
      by_cases hm : MpcInput input <;> simp [seedGenLocalHashInputs, Counted, List.filter_cons, hf, hm]
    | _ => simp [seedGenLocalHashInputs, Counted, IsFixed]
  · simp [seedGenLocalHashInputs, Counted, IsFixed]

/-- A syntactic query budget bounds the logged random inputs, regardless of answers. -/
theorem seedGenHashLog_random_length_le {α : Type} (oa : OracleComp (LocalSpec C) α)
    (n : ℕ) (hq : IsQueryBoundP oa Counted n) (r : α × List (Query C))
    (hr : r ∈ support (seedGenHashLog oa)) :
    (r.2.filter fun q => ¬ IsFixed q).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure a =>
    simp only [seedGenHashLog_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [seedGenHashLog_bind, seedGenHashLog_query] at hr
    simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
      support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, l, ⟨v, _, he⟩, a, rest, hk, hr⟩ := hr
    cases he
    cases hr
    have hrest := ih u _ (hq.2 u) (a, rest) hk
    simp only [List.filter_append, List.length_append, seedGenLocalHashInputs_counted]
    split_ifs at hrest ⊢ with ht <;> simp_all <;> omega

/-- A fixed-oracle interpretation cannot add a new syntactic output. -/
theorem seedGenFixedLocal_support_subset (prims : Primitives) (h : Query C → HashOutput)
    {α : Type} (oa : OracleComp (LocalSpec C) α) :
    support (simulateQ (fixedLocal prims h) oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro r hr
    rw [simulateQ_bind] at hr
    rcases (mem_support_bind_iff _ _ _).mp hr with ⟨u, _, hu⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query t u, ih u hu⟩

/-- Log every adversarial and distinguisher query in the reference execution. -/
def setupReferenceKernel (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    ProbComp (Bool × List (Query C)) :=
  simulateQ (fixedLocal prims h)
    (seedGenHashLog (setupReferenceLocalGame phase prims coalition h table A x z Z parts))

theorem setupReferenceKernel_privateInvariant (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SeedGenPrivateInvariant coalition (setupReferenceKernel phase prims coalition h table A x z Z) := by
  have hi := setupReferenceLocalGame_privateInvariant phase prims coalition h table A x z Z
  constructor
  · intro a T hT c parts
    unfold setupReferenceKernel
    rw [hi.1 a T hT c parts]
  · intro p ha hb c parts
    unfold setupReferenceKernel
    rw [hi.2 p ha hb c parts]

theorem setupReferenceKernel_random_length_le (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (parts : C.Party → Parts C) (r : Bool × List (Query C))
    (hr : r ∈ support (setupReferenceKernel phase prims coalition h table A x z Z parts)) :
    (r.2.filter fun v => ¬ IsFixed v).length ≤ q :=
  seedGenHashLog_random_length_le _ q
    (setupReferenceLocalGame_queryBound phase prims coalition h table A x z Z q hq parts) r
    (seedGenFixedLocal_support_subset prims h _ hr)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The reference reaches echo precisely when these actual abort and opening checks pass. -/
def setupReferenceActive (phase : Phase) (coalition : C.Coalition) (h : Query C → HashOutput)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Prop :=
  i ∉ coalition.1 ∧ seedGenCommitAborted coalition commitSent i = false ∧
    seedGenReferenceRevealAborted coalition commitSent revealSent i = false ∧
    setupReferenceOpenCheck phase coalition h commitSent revealSent i

theorem setupReferenceData_active (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    setupReferenceData phase prims coalition h table parts commitSent revealSent i =
      if setupReferenceActive phase coalition h commitSent revealSent i then
        let keys := setupReferenceKeys phase prims coalition h table parts (fun i j => revealSent j i) i
        some (keys, D prims h (sharedQueries phase i keys)) else none := by
  unfold setupReferenceData setupReferenceActive
  split_ifs <;> simp_all

theorem setupReferenceKeys_known (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) (T : C.Term)
    (hT : KnownTo coalition.1 T) :
    (setupReferenceKeys phase prims coalition h left parts revealed i).2.1 T =
      (setupReferenceKeys phase prims coalition h right parts revealed i).2.1 T := by
  simp only [setupReferenceKeys, seedGenMaskKeys, if_pos hT]

theorem setupReferenceKeys_coherent (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i j : C.Party) (T : C.Term)
    (hT : ¬ KnownTo coalition.1 T) (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) :
    (setupReferenceKeys phase prims coalition h table parts revealed i).2.1 T =
      (setupReferenceKeys phase prims coalition h table parts revealed j).2.1 T := by
  simp only [setupReferenceKeys, seedGenMaskKeys, if_neg hT, if_pos hi, if_pos hj]

theorem setupReferenceKeys_shared_corrupt (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i c : C.Party)
    (hc : c ∈ coalition.1) :
    h (.sharedKeys phase ((sharedTerms i c).map
      (setupReferenceKeys phase prims coalition h left parts revealed i).2.1)) =
      h (.sharedKeys phase ((sharedTerms i c).map
        (setupReferenceKeys phase prims coalition h right parts revealed i).2.1)) := by
  apply congrArg h
  exact setup_sharedInput_known phase coalition i c hc _ _
    (setupReferenceKeys_known phase prims coalition h left right parts revealed i)

theorem setupReferenceData_echoStep (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    setupEchoDataStep phase (E := E) i (setupReferenceData phase prims coalition h table parts commitSent revealSent i) =
      setupEchoStep phase prims coalition (setupReferenceActive phase coalition h commitSent revealSent) h
        (setupReferenceKeys phase prims coalition h table parts (fun i j => revealSent j i)) i := by
  rw [setupReferenceData_active]
  unfold setupEchoStep
  by_cases ha : setupReferenceActive phase coalition h commitSent revealSent i
  · have hi := ha.1
    simp [ha, hi, setupEchoDataStep]
  · simp [ha, setupEchoDataStep]

/-- Corrupt recipients see identical echo messages for every independent hidden table. -/
theorem setupReferenceData_visible (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (i c : C.Party) (hc : c ∈ coalition.1) :
    (setupEchoDataStep phase (E := E) i (setupReferenceData phase prims coalition h left parts commitSent revealSent i)).outbox c =
      (setupEchoDataStep phase (E := E) i (setupReferenceData phase prims coalition h right parts commitSent revealSent i)).outbox c := by
  simp only [setupReferenceData_active]
  split_ifs with ha
  · simp only [setupEchoDataStep, Step.outbox, echoOutbox]
    congr 2
    have hs := setupReferenceKeys_shared_corrupt phase prims coalition h left right parts
      (fun i j => revealSent j i) i c hc
    simp only [echoOf, D_sharedQueries_at, hs]
    rfl
  · rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The real simulator's observed commit round makes no honest hash calls after delivery. -/
theorem stepRound_setupInitialSteps_observed (phase : Phase) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    stepRound observedRoles coalition A noFunctionality state
        (setupInitialSteps phase coalition parts commitments) = (do
      let (st, sent) ← observedRoles.adversary (A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        commitOutbox i (commitments i) c else none)
      pure (st, setupRevealSteps phase coalition parts (setupCommitInbox phase coalition parts commitments sent), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (setupInitialSteps phase coalition parts commitments (E := E) i).outbox c else none) =
      (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then commitOutbox i (commitments i) c else none) := by
    funext c i
    split_ifs with hc
    · simp only [setupInitialSteps, if_neg hc.2, setupStart, Step.outbox]
    · rfl
  rw [hmsg]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [observedRoles]
  trans (OverPermutation.sequenceFin (fun j =>
    (pure (setupRevealSteps phase coalition parts (setupCommitInbox phase coalition parts commitments sent) j) :
      WriterT (CallLog C) (OracleComp (WorldSpec C)) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext j
    by_cases hj : j ∈ coalition.1
    · simp [setupInitialSteps, setupRevealSteps, hj]
    · simp only [setupInitialSteps, if_neg hj, setupStart]
      rw [advance_setupCommitResume]
      simp only [setupRevealSteps, hj, false_or, setupCommitInbox, roundInbox]
      simp only [free_pure, liftM_pure]
      rfl
  · rw [sequenceFin_pure, pure_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem simulateQ_fixedLocal_private (prims : Primitives) (h : Query C → HashOutput)
    {α : Type} (oa : ProbComp α) :
    simulateQ (fixedLocal prims h) (liftComp oa (LocalSpec C)) = oa := by
  rw [fixedLocal, QueryImpl.simulateQ_add_liftComp_left]
  exact simulateQ_id' oa

def setupFixedInitialCommitments (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) : C.Party → List HashOutput :=
  fun i => if i ∈ coalition.1 then [] else D prims h (commitQueries phase i (parts i))

theorem simulateQ_fixedLocal_setupInitialCommitments (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (setupInitialCommitments phase coalition parts) =
      pure (setupFixedInitialCommitments phase prims coalition h parts) := by
  rw [setupInitialCommitments, simulateQ_sequenceFin]
  trans OverPermutation.sequenceFin (fun i => (pure (setupFixedInitialCommitments phase prims coalition h parts i) : ProbComp _))
  · congr 1
    funext i
    unfold setupFixedInitialCommitments
    split_ifs
    · rfl
    · exact simulateQ_fixedLocal_liftComp (prims := prims) h _
  · exact sequenceFin_pure _

theorem setupFixedInitialCommitments_inbox (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (sent : C.Party → Mail C E) :
    setupCommitInbox phase coalition parts (setupFixedInitialCommitments phase prims coalition h parts) sent =
      setupCommitInbox phase coalition parts (fun j => D prims h (commitQueries phase j (parts j))) sent := by
  funext i j
  unfold setupCommitInbox roundInbox
  by_cases hj : j ∈ coalition.1
  · simp only [if_pos hj]
  · simp only [if_neg hj, setupInitialSteps, if_neg hj, setupFixedInitialCommitments]

theorem setupFixedInitialCommitments_view (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      commitOutbox (E := E) i (setupFixedInitialCommitments phase prims coalition h parts i) c else none) =
      setupFixedCommitView phase prims coalition h parts := by
  funext c i
  unfold setupFixedCommitView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, setupFixedInitialCommitments, if_neg hc.2]
  · simp only [if_neg hc]

/-- The whole normalized game equals the concrete reference with the actual hidden oracle
values. The sampling order of `A.start` and honest parts is exchanged only at the distribution level. -/
theorem evalDist_setupNormalized_fixed_reference (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (fixedLocal prims h) (setupNormalizedLocalGame phase coalition A x z Z) =ᵈ
      (do
        let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
        simulateQ (fixedLocal prims h)
          (setupReferenceLocalGame phase prims coalition h (fun name => h (setupNamedInput phase parts name)) A x z Z parts)) := by
  simp only [setupNormalizedLocalGame, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_fixedLocal_private, simulateQ_fixedLocal_setupInitialCommitments, pure_bind]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun parts => ?_
  simp only [setupReferenceLocalGame, simulateQ_bind]
  refine EvalDistEq.bind_right _ fun state => ?_
  rw [setupFixedInitialCommitments_view]
  refine EvalDistEq.bind_right _ ?_
  rintro ⟨st, sent⟩
  dsimp only
  rw [setupFixedInitialCommitments_inbox,
    simulateQ_setupPostCommit_reference phase prims coalition h (fun name => h (setupNamedInput phase parts name))
      A st parts (fun _ _ => rfl) sent]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The vector of honest private parts has a finite type, despite its function fields. -/
theorem seedGenParts_finite (C : Committee) : Finite (Parts C) := by
  apply Finite.of_injective (fun p : Parts C => (p.parameter, p.term, p.pair))
  intro p q hp
  cases p
  cases q
  simpa only [Prod.mk.injEq, Parts.mk.injEq] using hp

/-- All canonical named inputs, for every possible sampled parts vector. This finite set is
only an oracle domain; its cardinality never appears in the security estimate. -/
def setupAllNamedInputs (phase : Phase) (C : Committee) : Finset (Query C) :=
  letI : Finite (Parts C) := seedGenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  Finset.univ.biUnion fun parts : C.Party → Parts C =>
    (seedGenNames C).toFinset.image (setupNamedInput phase parts)

theorem setupAllNamedInputs_mem (phase : Phase) (parts : C.Party → Parts C) (name : KeyName C) :
    setupNamedInput phase parts name ∈ setupAllNamedInputs phase C := by
  letI : Finite (Parts C) := seedGenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  unfold setupAllNamedInputs
  apply Finset.mem_biUnion.mpr
  refine ⟨parts, Finset.mem_univ _, Finset.mem_image.mpr ⟨name, ?_, rfl⟩⟩
  simp [seedGenNames]

/-- A canonical input in the enlarged domain reads an actual sampled cell, never the fallback. -/
theorem setupFiniteTotal_named (phase : Phase) (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) (parts : C.Party → Parts C) (name : KeyName C)
    (hn : setupNamedInput phase parts name ∈ S) :
    seedGenFiniteTotal prims S h (setupNamedInput phase parts name) = h ⟨setupNamedInput phase parts name, hn⟩ := by
  cases name <;>
    simp [seedGenFiniteTotal, setupNamedInput, parameterInput, termInput, pairInput] at hn ⊢ <;>
    simp [hn]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Exchange the finite oracle cells at canonical hidden inputs with the independent dealer
coordinates. Every other oracle cell and every exposed dealer coordinate stays fixed. -/
def setupFiniteHiddenSwap (phase : Phase) (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) :
    (S → HashOutput) × (KeyName C → HashOutput) :=
  (fun q => if hh : SetupHiddenInput phase coalition parts q.val then p.2 (Classical.choose hh) else p.1 q,
   fun name => if Hidden coalition name then p.1 ⟨setupNamedInput phase parts name, hmem name⟩ else p.2 name)

theorem setupFiniteHiddenSwap_cell (phase : Phase) (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (hinj : Function.Injective (setupNamedInput phase parts))
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (name : KeyName C) (hh : Hidden coalition name) :
    (setupFiniteHiddenSwap phase coalition S parts hmem p).1 ⟨setupNamedInput phase parts name, hmem name⟩ = p.2 name := by
  have hp : SetupHiddenInput phase coalition parts (setupNamedInput phase parts name) := ⟨name, hh, rfl⟩
  simp only [setupFiniteHiddenSwap, dif_pos hp]
  have he : Classical.choose hp = name := hinj (Classical.choose_spec hp).2
  rw [he]

theorem setupFiniteHiddenSwap_off (phase : Phase) (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (q : S)
    (hq : ¬ SetupHiddenInput phase coalition parts q.val) :
    (setupFiniteHiddenSwap phase coalition S parts hmem p).1 q = p.1 q := by
  simp only [setupFiniteHiddenSwap, dif_neg hq]

theorem setupFiniteHiddenSwap_dealer_known (phase : Phase) (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (name : KeyName C) (hh : ¬ Hidden coalition name) :
    (setupFiniteHiddenSwap phase coalition S parts hmem p).2 name = p.2 name := by
  simp only [setupFiniteHiddenSwap, if_neg hh]

/-- Distinct canonical names make the exchange between oracle and dealer an involution. -/
theorem setupFiniteHiddenSwap_involutive (phase : Phase) (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (hinj : Function.Injective (setupNamedInput phase parts)) :
    Function.Involutive (setupFiniteHiddenSwap phase coalition S parts hmem) := by
  intro p
  apply Prod.ext
  · funext q
    by_cases hq : SetupHiddenInput phase coalition parts q.val
    · obtain ⟨name, hh, he⟩ := hq
      have hq' : q = ⟨setupNamedInput phase parts name, hmem name⟩ := Subtype.ext he.symm
      rw [hq', setupFiniteHiddenSwap_cell phase coalition S parts hmem hinj _ name hh]
      simp only [setupFiniteHiddenSwap, if_pos hh]
    · rw [setupFiniteHiddenSwap_off phase coalition S parts hmem _ q hq,
        setupFiniteHiddenSwap_off phase coalition S parts hmem _ q hq]
  · funext name
    by_cases hh : Hidden coalition name
    · change (if Hidden coalition name then
        (setupFiniteHiddenSwap phase coalition S parts hmem p).1 ⟨setupNamedInput phase parts name, hmem name⟩
        else (setupFiniteHiddenSwap phase coalition S parts hmem p).2 name) = p.2 name
      rw [if_pos hh, setupFiniteHiddenSwap_cell phase coalition S parts hmem hinj p name hh]
    · rw [setupFiniteHiddenSwap_dealer_known phase coalition S parts hmem _ name hh,
        setupFiniteHiddenSwap_dealer_known phase coalition S parts hmem _ name hh]

/-- The complete joint law of the eager oracle and independent dealer is preserved. -/
theorem evalDist_setupFiniteHiddenSwap (phase : Phase) (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (hinj : Function.Injective (setupNamedInput phase parts)) :
    (setupFiniteHiddenSwap phase coalition S parts hmem <$>
      ($ᵗ ((S → HashOutput) × (KeyName C → HashOutput)))) =ᵈ
      $ᵗ ((S → HashOutput) × (KeyName C → HashOutput)) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective
    (setupFiniteHiddenSwap_involutive phase coalition S parts hmem hinj).bijective

/-- The total oracles agree away from canonical hidden inputs, including all fixed Th calls. -/
theorem setupFiniteHiddenSwap_total_off (phase : Phase) (prims : Primitives) (coalition : C.Coalition)
    (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ name, setupNamedInput phase parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (q : Query C)
    (hq : ¬ SetupHiddenInput phase coalition parts q) :
    seedGenFiniteTotal prims S (setupFiniteHiddenSwap phase coalition S parts hmem p).1 q =
      seedGenFiniteTotal prims S p.1 q := by
  have he (hm : q ∈ S) :
      (setupFiniteHiddenSwap phase coalition S parts hmem p).1 ⟨q, hm⟩ = p.1 ⟨q, hm⟩ :=
    setupFiniteHiddenSwap_off phase coalition S parts hmem p _ hq
  cases q <;> simp only [seedGenFiniteTotal] <;> split_ifs <;> first | apply he | rfl

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

variable {C : Committee} {E : Type} (prims : Primitives)

end ThresholdLeanXmssSecurity
