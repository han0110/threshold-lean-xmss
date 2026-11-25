import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CompHit

/-!
# The counts on the support of the runs of the seed steps

* `measure_bind_le` is a general count. A measure on the world state grows by at most one at each
  call of a predicate `P` and by none at each other call. Then along `oa >>= f` with at most `n` calls
  of `P`, each end state of `oa` leaves a bound `m` of calls for `f`, and the measure grew by at most
  `n - m`. `measure_le` is the case of one program.
* `log_prefix_suffix` bounds the log at the end of the prefix in `loggedWorld` and a suffix in a world
  that logs as `loggedWorld` does, by the count of the counted calls of the two together.
* `compLog` proves `CompLog`. `compWorld` adds to the log as `loggedWorld` does.
* `logged_seedGenShape` bounds the counted calls of each seed generation of the normal shape with free
  local steps, and `logged_prefix_suffixOf` gives the budget `q` for the prefix and such a suffix.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_mapM
  noCall_sequenceFin)
open PFunctor.FreeM (cost)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## A measure on the world state -/

section Measure

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (g : W → ℕ∞)
  (P : (WorldSpec C).Domain → Prop)

/-- A measure on the state that grows by at most one at a call of `P` and by none at another call.
Along `oa >>= f` with at most `n` calls of `P`, each end state `x` of `oa` leaves a bound `m` for
`f x.1`, and the measure grew by at most `n - m`. -/
theorem measure_bind_le (step : ∀ t w, ∀ z ∈ support ((impl t).run w), g z.2 ≤ g w + if P t then 1 else 0)
    {α β : Type} (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β) :
    ∀ (n : ℕ), IsQueryBoundP (oa >>= f) P n → ∀ (w : W), ∀ x ∈ support ((simulateQ impl oa).run w),
      ∃ m : ℕ, g x.2 + m ≤ g w + n ∧ IsQueryBoundP (f x.1) P m := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n hn w x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨n, le_rfl, by simpa using hn⟩
  | query_bind t k ih =>
    intro n hn w x hx
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at hn
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hx
    obtain ⟨r, hr, hx⟩ := hx
    have h1 := step t w r hr
    by_cases ht : P t
    · have hpos := hn.1.resolve_left (not_not.2 ht)
      obtain ⟨m, hm, hf⟩ := ih r.1 (n - 1) (by simpa [ht] using hn.2 r.1) r.2 x hx
      simp only [ht, ↓reduceIte] at h1
      refine ⟨m, ?_, hf⟩
      calc g x.2 + m ≤ g r.2 + (n - 1 : ℕ) := hm
        _ ≤ g w + 1 + (n - 1 : ℕ) := add_le_add h1 le_rfl
        _ = g w + n := by
          rw [add_assoc]
          congr 1
          norm_cast
          omega
    · obtain ⟨m, hm, hf⟩ := ih r.1 n (by simpa [ht] using hn.2 r.1) r.2 x hx
      simp only [ht, ↓reduceIte, add_zero] at h1
      exact ⟨m, hm.trans (add_le_add h1 le_rfl), hf⟩

/-- `measure_bind_le` for one program. -/
theorem measure_le (step : ∀ t w, ∀ z ∈ support ((impl t).run w), g z.2 ≤ g w + if P t then 1 else 0)
    {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ (n : ℕ), IsQueryBoundP oa P n → ∀ (w : W), ∀ z ∈ support ((simulateQ impl oa).run w), g z.2 ≤ g w + n := by
  intro n hn w z hz
  obtain ⟨m, hm, -⟩ := measure_bind_le impl g P step oa pure n (by simpa using hn) w z hz
  exact le_self_add.trans hm

end Measure

/-! ## The log of a world -/

section Log

/-- The length of the log grows by at most one at a call of `Logged` in a world that adds the cells of
`countedCells` to the log. -/
theorem logLength_step {W : Type} (impl : QueryImpl (WorldSpec C) (StateT (W × List (Query C)) ProbComp))
    (h : ∀ t w, ∀ r ∈ support ((impl t).run w), r.2.2 = w.2 ++ countedCells t) :
    ∀ t w, ∀ z ∈ support ((impl t).run w),
      ((z.2.2.length : ℕ) : ℕ∞) ≤ ((w.2.length : ℕ) : ℕ∞) + if Logged t then 1 else 0 := by
  intro t w z hz
  have hc := countedCells_length_le t
  rw [h t w z hz, List.length_append]
  by_cases ht : Logged t
  · simp only [ht, ↓reduceIte] at hc ⊢
    exact_mod_cast Nat.add_le_add_left hc _
  · simp only [ht, ↓reduceIte] at hc ⊢
    simp [Nat.le_zero.1 hc]

variable (prims : Primitives) (D : C.Coalition)

theorem compWorld_log (parts : C.Party → Parts C) (seed : C.Term → HashOutput) (t : (WorldSpec C).Domain)
    (w : LogState C) : ∀ r ∈ support ((compWorld prims D parts seed t).run w), r.2.2 = w.2 ++ countedCells t := by
  intro r hr
  rcases t with ((n | q | x) | p) | (n | q | x)
  rotate_left 5
  · simp only [compWorld] at hr
    split at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp [countedCells]
    · exact loggedWorld_log prims D _ w r hr
  all_goals exact loggedWorld_log prims D _ w r hr

end Log

/-! ## The split of the budget of the game -/

section Split

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- The prefix and the suffix with no emulated run make together at most `q` calls of `Logged`. -/
theorem dealtParts_bound (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    IsQueryBoundP (dealtPrefix D A >>= fun x =>
      (fun y => (x.2.2, y)) <$> dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x) Logged q := by
  have h := LoggedCount.logged_dealtRun K circuits settings runLimit D ⟨true, fun _ => 0⟩ (fun _ => rfl) A q bounded
  rw [← snd_dealtPartsRun, isQueryBoundP_map_iff, dealtPartsRun_split] at h
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A measure that grows by at most one at a call of `Logged` in `loggedWorld` along the prefix leaves
a bound `m` for the suffix, and grew by at most `q - m`. -/
theorem prefix_split (D : C.Coalition) (A : DkgTsigAdversary C E) {β : Type}
    (suf : PrefixOut C A.net.State → OracleComp (WorldSpec C) β) (q : ℕ)
    (bound : IsQueryBoundP (dealtPrefix D A >>= suf) Logged q) (g : LogState C → ℕ∞)
    (step : ∀ t w, ∀ z ∈ support ((loggedWorld prims D t).run w), g z.2 ≤ g w + if Logged t then 1 else 0) :
    ∀ x ∈ support ((simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])),
      ∃ m : ℕ, g x.2 + m ≤ g ((∅, ∅), []) + q ∧ IsQueryBoundP (suf x.1) Logged m :=
  fun x hx => measure_bind_le (loggedWorld prims D) g Logged step _ _ q bound _ x hx

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run of the prefix in `loggedWorld` and of a suffix in a world that adds `countedCells` to the
log, with at most `q` calls of `Logged` in all, ends with at most `q` cells in the log. -/
theorem log_prefix_suffix (D : C.Coalition) (A : DkgTsigAdversary C E) {β : Type}
    (suf : PrefixOut C A.net.State → OracleComp (WorldSpec C) β) (q : ℕ)
    (bound : IsQueryBoundP (dealtPrefix D A >>= suf) Logged q)
    (world : PrefixOut C A.net.State → QueryImpl (WorldSpec C) (StateT (LogState C) ProbComp))
    (hworld : ∀ y t w, ∀ r ∈ support ((world y t).run w), r.2.2 = w.2 ++ countedCells t)
    (x : PrefixOut C A.net.State × LogState C)
    (hx : x ∈ support ((simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])))
    (z : β × LogState C) (hz : z ∈ support ((simulateQ (world x.1) (suf x.1)).run x.2)) : z.2.2.length ≤ q := by
  obtain ⟨m, hm, hf⟩ := prefix_split prims D A suf q bound (fun w => ((w.2.length : ℕ) : ℕ∞))
    (logLength_step (loggedWorld prims D) (loggedWorld_log prims D)) x hx
  have h2 := measure_le (world x.1) (fun w => ((w.2.length : ℕ) : ℕ∞)) Logged
    (logLength_step _ (hworld x.1)) _ m hf x.2 z hz
  have h3 := h2.trans hm
  simp only [List.length_nil, Nat.cast_zero, zero_add] at h3
  exact_mod_cast h3

omit [Fintype E] [DecidableEq E] in
theorem compLog : CompLog prims K circuits settings runLimit := by
  intro D A q bounded r hr
  simp only [compRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨x, hx, seed, -, z, hz, rfl⟩ := hr
  have hz' : ((x.1.2.2, z.1), z.2) ∈ support ((simulateQ (compWorld prims D x.1.2.2 seed)
      ((fun y => (x.1.2.2, y)) <$> dealtSuffix K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1)).run x.2) := by
    rw [simulateQ_map, StateT.run_map, support_map]
    exact ⟨z, hz, rfl⟩
  exact log_prefix_suffix prims D A _ q (dealtParts_bound K circuits settings runLimit D A q bounded)
    (fun y => compWorld prims D y.2.2 seed) (fun y => compWorld_log prims D y.2.2 seed) x hx _ hz'

/-! ## The budget of a seed generation of the normal shape -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A round of `levelRound` makes the calls of one round of the adversary and then the calls of the
rest `cont`. -/
theorem logged_levelRound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step c : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step) {X Y β : Type} (fuel : ℕ)
    (state : net.State) (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (hcont : ∀ f s d', IsQueryBoundP (cont f s d') Logged (f * step + c)) :
    IsQueryBoundP (levelRound D net fuel state d out next cont) Logged (fuel * step + c) := by
  cases fuel with
  | zero => exact (noCall_iff _ _).1 (noCall_pure _ _) |>.mono (Nat.zero_le _)
  | succ fuel =>
    rw [levelRound]
    by_cases h1 : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left h1]
      exact (noCall_iff _ _).1 (noCall_pure _ _) |>.mono (Nat.zero_le _)
    rw [ite_eq_right h1]
    refine (isQueryBoundP_bind (logged_adversary _ step (hround _ _)) fun r _ => ?_).mono
      (show step + (fuel * step + c) ≤ (fuel + 1) * step + c by rw [Nat.succ_mul]; omega)
    by_cases h2 : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left h2]
      exact (noCall_iff _ _).1 (noCall_pure _ _) |>.mono (Nat.zero_le _)
    rw [ite_eq_right h2]
    refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (noCall_sequenceFin _ _ fun j => ?_))
      fun d' _ => hcont fuel r.1 d').mono (Nat.zero_add _).le
    split_ifs <;> (try split) <;> first | exact noCall_pure _ _ | exact logged_free _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem noLogged_programBlock (D : C.Coalition) (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    NoCall Logged (programBlock D log sent parameter dealt parts) := by
  unfold programBlock
  refine noCall_bind _ (logged_free _) fun _ => noCall_bind _ (logged_program _ _) fun _ =>
    noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
      noCall_bind _ (noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_) fun _ => noCall_pure _ _
  · split
    · exact logged_program _ _
    · exact noCall_pure _ _
  · split
    · exact logged_program _ _
    · exact noCall_pure _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The commit calls of the honest operators are free calls. -/
theorem noLogged_commitDrawsAt (D : C.Coalition) (commitAt : C.Party → C.Party → Query C) :
    NoCall Logged (commitDrawsAt D commitAt) := by
  unfold commitDrawsAt
  refine noCall_sequenceFin _ _ fun i => ?_
  split_ifs
  · exact noCall_pure _ _
  · exact logged_free _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation of the normal shape makes the calls of the `setupRounds` rounds of the
adversary. The commit calls `draws` and the local steps make no counted call. -/
theorem logged_seedGenShape (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (net.round state sent) HashCall step) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (draws : OracleComp (WorldSpec C) (C.Party → List HashOutput)) (hdraws : NoCall Logged draws)
    (next : (C.Party → Mail C E) → C.Party → Mail C E → OracleComp (LocalSpec C) (Option (SeedGenEchoData C)))
    (outEcho : C.Party → SeedGenEchoData C → Mail C E)
    (echoStep : C.Party → SeedGenEchoData C → Mail C E → OracleComp (LocalSpec C) (Option (Keys C))) :
    IsQueryBoundP (draws >>= fun commitments =>
      observe (net.round state (commitMail D commitments)) >>= fun r =>
      programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
      levelRound D net (setupRounds - 1) r.1.1 (revealReady (commitInbox D commitments r.1.2))
        (fun i _ => revealOutbox .seedGen i (parts i))
        (fun i _ inbox => next (commitInbox D commitments r.1.2) i inbox) fun f2 s2 d2 =>
      levelRound D net f2 s2 d2 outEcho echoStep fun _ s3 d3 =>
      pure (s3, fun j => if j ∈ D.1 then none else d3 j)) Logged (setupRounds * step) := by
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 hdraws) fun commitments _ => ?_).mono
    (Nat.zero_add _).le
  refine (isQueryBoundP_bind (logged_observe _ _ (hround _ _)) fun r _ => ?_).mono
    (show step + (0 + ((setupRounds - 1) * step + 0)) ≤ setupRounds * step by simp [setupRounds]; omega)
  refine isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (noLogged_programBlock _ _ _ _ _ _)) fun _ _ => ?_
  refine logged_levelRound D net step 0 hround _ _ _ _ _ _ fun f2 s2 d2 => ?_
  exact logged_levelRound D net step 0 hround _ _ _ _ _ _ fun _ _ _ =>
    (noCall_iff _ _).1 (noCall_pure _ _) |>.mono (Nat.zero_le _)

/-- The suffix of the game with the seed generation `sg`. -/
def suffixOf (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (sg : OracleComp (WorldSpec C) (A.net.State × (C.Party → Option (Keys C)))) :
    OracleComp (WorldSpec C) (RunOut C) := do
  let (state, emu) ← sg
  let keys := fun i => (emu i).map fun _ => x.2.1.2.2 i
  let win ← (secRest K circuits settings runLimit m D A x.2.1.1 x.2.1.2.1 x.2.1.2.2 emu).run' (startState D state keys)
  pure (win, x.2.1.1, x.2.1.2.1, x.2.1.2.2, emu)

omit [Fintype E] [DecidableEq E] in
/-- A suffix with a seed generation of at most `setupRounds * step` counted calls makes at most the
calls of the rounds of the adversary and of `forge`. -/
theorem logged_suffixOf (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) HashCall step)
    (hforge : ∀ pk top, cost (forgeCharge (callCharge HashCall)) (A.forge pk top) ≤ (forge : ℕ∞))
    (x : PrefixOut C A.net.State) (sg : OracleComp (WorldSpec C) (A.net.State × (C.Party → Option (Keys C))))
    (hsg : IsQueryBoundP sg Logged (setupRounds * step)) :
    IsQueryBoundP (suffixOf K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x sg) Logged
      (setupRounds * step + ((dkgTsigRounds circuits settings runLimit - setupRounds) * step + forge)) := by
  unfold suffixOf
  refine isQueryBoundP_bind hsg fun p _ => ?_
  rw [← cost_callCharge_le_iff]
  refine (cost_bind_le_add (m := 0) ?_ fun _ => cost_pure_le _ _ _).trans (le_of_eq (add_zero _))
  rw [StateT.run'_eq, cost_map_eq]
  have h := LoggedCount.rcost_secRest K circuits settings runLimit D step ⟨true, fun _ => 0⟩ (fun _ => rfl) A hround forge
    hforge x.2.1.1 x.2.1.2.1 x.2.1.2.2 p.2 (startState D p.1 fun i => (p.2 i).map fun _ => x.2.1.2.2 i)
  refine h.trans (le_of_eq ?_)
  change (step : ℕ∞) + ((forge : ℕ∞) + ((FirstCounts.remaining runLimit
    (fun _ => treeFuel circuits settings * step + step) (fun _ => 0) : ℕ) : ℕ∞)) = _
  rw [← remaining_start]
  push_cast
  ring

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem round_bound (A : DkgTsigAdversary C E) (step : ℕ)
    (hround : ∀ st sent, QueryCostAtMost (A.net.round st sent) ownCost step) :
    ∀ st sent, IsQueryBoundP (A.net.round st sent) HashCall step := fun st sent =>
  isQueryBoundP_of_queryCostAtMost (hround st sent) LoggedCount.hashCall_ownCost

omit [Fintype E] [DecidableEq E] in
/-- The prefix and a suffix with a seed generation of at most `setupRounds * step` counted calls make
at most `q` counted calls for an adversary with the budget `q`. -/
theorem logged_prefix_suffixOf (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q)
    (sg : PrefixOut C A.net.State → OracleComp (WorldSpec C) (A.net.State × (C.Party → Option (Keys C))))
    (hsg : ∀ step, (∀ state sent, IsQueryBoundP (A.net.round state sent) HashCall step) →
      ∀ x, IsQueryBoundP (sg x) Logged (setupRounds * step)) :
    IsQueryBoundP (dealtPrefix D A >>= fun x =>
      suffixOf K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (sg x)) Logged q := by
  obtain ⟨start, step, forge, hsum, hstart, hround, hforge⟩ := bounded
  have hstart' : ∀ x z, IsQueryBoundP (A.net.start x z) HashCall start := fun x z =>
    isQueryBoundP_of_queryCostAtMost (hstart x z) LoggedCount.hashCall_ownCost
  have hround' := round_bound A step hround
  have hforge' : ∀ pk top, cost (forgeCharge (callCharge HashCall)) (A.forge pk top) ≤ (forge : ℕ∞) :=
    fun pk top => (PFunctor.FreeM.cost_mono LoggedCount.forgeCharge_le_forgeCost _).trans
      ((queryCostAtMost_iff_cost_le _ _ _).1 (hforge pk top))
  unfold dealtPrefix
  simp only [bind_assoc, pure_bind]
  refine (isQueryBoundP_bind (m := setupRounds * step +
    ((dkgTsigRounds circuits settings runLimit - setupRounds) * step + forge)) (logged_observe _ _ (hstart' _ _))
      fun a _ => ?_).mono
    (by have := budget_arith circuits settings runLimit start step forge q hsum; omega)
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_free _)) fun b _ => ?_).mono
    (Nat.zero_add _).le
  refine (isQueryBoundP_bind (n := 0) ((noCall_iff _ _).1 (logged_free _)) fun parts _ => ?_).mono
    (Nat.zero_add _).le
  exact logged_suffixOf K circuits settings runLimit D A step forge hround' hforge' _ _ (hsg step hround' _)

end Split

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compLog
