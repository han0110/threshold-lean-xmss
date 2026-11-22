import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HeadLaw

/-!
# The head of a bottom tree at the cut, `HeadCover` and `CutState`

`headCover` proves `HeadCover` and `cutState_of_support` proves `CutState` from `CeremonySupport`.
Both use the law of the head, `bottomCut_split`, and the support of the search, `headPhase_support`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

/-! ## `HeadCover` -/

section Cover

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- Wrong outputs read the keys of the honest operators only. -/
theorem wrongOutputs_congr_keys (D : C.Coalition) {keys keys' : C.Party → Option (Keys C)}
    (h : ∀ i, i ∉ D.1 → keys i = keys' i) (jobs : List Job) (cache : HashCache C) (outputs : List (List Bit)) :
    WrongOutputs prims circuits D keys jobs cache outputs ↔ WrongOutputs prims circuits D keys' jobs cache outputs := by
  unfold WrongOutputs
  rw [gameSeeds_congr D h, gameParameter_congr D h]

omit [Fintype E] [DecidableEq E] in
/-- Each honest program of the head starts with a round, the first exchange of the first PRSS setup,
or it aborts at once. -/
theorem startsWithRound_bottomHead (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ) (i : C.Party) :
    StartsWithRound (CheckTiming.bottomHead K circuits settings i (s.operators i) b) := by
  rw [bottomHead_eq]
  exact startsWithRound_bind _ _ (startsWithRound_ceremonyProgram K circuits settings i _)

omit [DecidableEq E] in
/-- The head is the first ceremony and the search as a phase with no round, so `HeadCover` holds. -/
theorem headCover : HeadCover prims K circuits settings := by
  intro D net b s world n htimed
  by_cases hdead : ∃ i, i ∉ D.1 ∧ aliveKeys s i = none
  · obtain ⟨i₀, hi₀, hnone⟩ := hdead
    have hfail : CheckTiming.bottomHead K circuits settings i₀ (s.operators i₀) b = failure := by
      rw [bottomHead_eq]
      simp [ceremonyProgram, firstStart, hnone]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hw => ?_]
    · exact bot_le
    obtain ⟨i, hi, x, hx, -⟩ := hw.1
    have hno := phase_dead_noOutput prims D net n s.adversary _ i₀ hi₀ hfail
      (fun i _ => startsWithRound_bottomHead K circuits settings b s i) world z hz i hi
    rw [hno] at hx
    exact absurd hx (by simp)
  push Not at hdead
  have hkeys : ∀ i, i ∉ D.1 → (s.operators i).keys = (firstStart b s).keys i := fun i hi => by
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (hdead i hi)
    simp only [firstStart, hk]
    exact aliveKeys_some s i k hk
  rw [(bottomCut_split prims K circuits settings D net b s world n htimed).prEvent_eq]
  refine (probEvent_bind_le_split (fun r => WrongCeremony prims circuits D (firstStart b s) r ∧ ¬ GlobalEvent r.2)
    (fun _ => False) 0 fun r hr => ?_).trans (by simp)
  by_cases hP : WrongCeremony prims circuits D (firstStart b s) r ∧ ¬ GlobalEvent r.2
  · rw [ite_eq_left hP]
    exact (prEvent_le_one _).trans le_self_add
  rw [ite_eq_right hP, prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hE => hP ?_]
  · simp
  obtain ⟨-, hstep, hproj, -⟩ := headPhase_support prims D net b s r.1.1 r.1.2 r.2 z hz
  obtain ⟨⟨i, hi, x, hx, hwrong⟩, hglobal⟩ := hE
  obtain ⟨o, ho, hxo, -⟩ := hproj i hi x hx
  refine ⟨⟨i, hi, o, ho, ?_⟩, fun h => hglobal ((globalEvent_hashStep hstep).2 h)⟩
  rw [wrongOutputs_sameOffHash prims circuits D _ _ hstep.2.1, wrongOutputs_congr_keys prims circuits D hkeys,
    hxo] at hwrong
  exact hwrong

end Cover

/-! ## `CutState` -/

section State

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- Two honest operators with keys of the first ceremony from consistent keys have one parameter
of the head. -/
theorem headParameter_eq (D : C.Coalition) (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ)
    (hseeds : seedsDiffer D (firstStart b s).keys = false) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1)
    (ki kj : Keys C) (hki : aliveKeys s i = some ki) (hkj : aliveKeys s j = some kj) :
    headParameter s i = headParameter s j := by
  unfold headParameter
  rw [aliveKeys_some s i ki hki, aliveKeys_some s j kj hkj]
  simp only [Option.map_some, Option.getD_some]
  unfold seedsDiffer at hseeds
  rw [decide_eq_false_iff_not] at hseeds
  by_contra hne
  exact hseeds ⟨i, j, ki, kj, hi, hj, hki, hkj, Or.inl hne⟩

omit [DecidableEq E] in
/-- `CutState` from the support part of the lemma of one ceremony. -/
theorem cutState_of_support (support : CeremonySupport prims K circuits settings) :
    CutState prims K circuits settings := by
  intro D net step hstep ℓ b s world n htimed hready z hz
  rw [support_eq_of_evalDistEq (bottomCut_split prims K circuits settings D net b s world n htimed),
    mem_support_bind_iff] at hz
  obtain ⟨r, hr, hz⟩ := hz
  obtain ⟨-, hdead, ⟨hfit, hprov⟩, hagree⟩ := support D net step n hstep ℓ (firstStart b s) world
    (admissible_of_protocol circuits settings b (fun _ => digit 0) _ (Or.inr (Or.inl rfl))) hready r hr
  obtain ⟨-, hmove, hproj, hsame⟩ := headPhase_support prims D net b s r.1.1 r.1.2 r.2 z hz
  refine ⟨ledgerFits_hashStep hmove hfit, hiddenProvenance_hashStep hmove hprov,
    fun hglobal i j xi xj hi hj hxi hxj => ?_⟩
  have hglobal' : ¬ GlobalEvent r.2 := fun h => hglobal ((globalEvent_hashStep hmove).2 h)
  obtain ⟨oi, hoi, -⟩ := hproj i hi xi hxi
  obtain ⟨oj, hoj, -⟩ := hproj j hj xj hxj
  have halive : ∀ k, k ∉ D.1 → ∃ kk, aliveKeys s k = some kk := fun k hk => by
    by_contra hnone
    have h := hdead ⟨k, hk, Option.eq_none_iff_forall_ne_some.2 fun kk hkk => hnone ⟨kk, hkk⟩⟩ i hi
    rw [hoi] at h
    exact absurd h (by simp)
  obtain ⟨ki, hki⟩ := halive i hi
  obtain ⟨kj, hkj⟩ := halive j hj
  have hij : r.1.2 i = r.1.2 j := by rw [hoi, hoj, hagree hglobal' i j oi oj hi hj hoi hoj]
  have h := hsame i j hi hj hij (headParameter_eq D b s hready.1 i j hi hj ki kj hki hkj)
  rw [hxi, hxj] at h
  exact Option.some.inj h

omit [DecidableEq E] in
/-- `CutState` for each primitive, from the support part of the lemma of one ceremony. -/
theorem cutState_of_supports (support : ∀ prims, CeremonySupport prims K circuits settings) :
    ∀ prims, CutState prims K circuits settings :=
  fun prims => cutState_of_support prims K circuits settings (support prims)

end State

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.headCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.headCover

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutState_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutState_of_support

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutState_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutState_of_supports
