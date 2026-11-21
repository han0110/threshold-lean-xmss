import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepCommitPad
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepRename
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.CountProgram

/-!
# The commit side `CommitShift` from the pad of the honest pair cells

The family of the honest pair cells of the suffix `suffixAt x commitAt termAt` is `pairFamily D commitAt`.
Its index `(i, j, b)` has two honest operators. With `b = false` it is the commit cell `commitAt i j`, and
with `b = true` it is the open cell `.commit i j []` of an operator for itself.

* `noCall_suffixAt` states that the suffix makes no programming call at a cell of the family and no
  free call at a commitment cell between two honest operators off the family.
* `desWorld_family` states that on such a program `desWorld` of the family is `pairWorld`.
* `commitShift_of_pad` gives `CommitShift` from `wp_shared_eq_des` and the pad invariance of the
  suffix on the shifted parts.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_mono noCall_bind noCall_pure
  noCall_mapM noCall_sequenceFin noCall_query noCall_map)
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## The family of the honest pair cells -/

section Family

variable (D : C.Coalition)

/-- The index of a cell of the family, two honest operators and a tag for the open cell for itself. -/
abbrev PairIndex (C : Committee) (D : C.Coalition) := {p : C.Party × C.Party × Bool // p.1 ∉ D.1 ∧ p.2.1 ∉ D.1}

/-- The honest pair cells of the suffix with the commit cells `commitAt`. -/
def pairFamily (commitAt : C.Party → C.Party → Query C) (p : PairIndex C D) : Query C :=
  if p.1.2.2 then .commit .seedGen p.1.1 p.1.2.1 [] else commitAt p.1.1 p.1.2.1

/-- A commit cell family with a nonempty reveal for each pair. -/
def CommitShape (commitAt : C.Party → C.Party → Query C) : Prop :=
  ∀ i j, ∃ r, r ≠ [] ∧ commitAt i j = .commit .seedGen i j r

theorem commitShape_commitAddress (parts : C.Party → Parts C) : CommitShape (commitAddress parts) :=
  fun _ _ => ⟨_, revealTo_ne_nil _ _ _ _, rfl⟩

theorem pairFamily_injective {commitAt : C.Party → C.Party → Query C} (h : CommitShape commitAt) :
    Function.Injective (pairFamily D commitAt) := by
  rintro ⟨⟨i, j, b⟩, hp⟩ ⟨⟨i', j', b'⟩, hp'⟩ e
  obtain ⟨r, hr, hc⟩ := h i j
  obtain ⟨r', hr', hc'⟩ := h i' j'
  simp only [pairFamily] at e
  cases b <;> cases b' <;> simp only [Bool.false_eq_true, ite_false, ite_true, hc, hc', Query.commit.injEq,
    true_and] at e
  · obtain ⟨rfl, rfl, -⟩ := e
    rfl
  · exact absurd e.2.2 hr
  · exact absurd e.2.2.symm hr'
  · obtain ⟨rfl, rfl, -⟩ := e
    rfl

theorem pairFamily_pairCell (commitAt : C.Party → C.Party → Query C) (h : CommitShape commitAt) (p : PairIndex C D) :
    PairCell D (pairFamily D commitAt p) := by
  obtain ⟨⟨i, j, b⟩, hi, hj⟩ := p
  obtain ⟨r, -, hc⟩ := h i j
  cases b
  · exact ⟨i, j, r, hi, hj, by simp [pairFamily, hc]⟩
  · exact ⟨i, j, [], hi, hj, by simp [pairFamily]⟩

theorem inFamily_commitAt {commitAt : C.Party → C.Party → Query C} {i j : C.Party} (hi : i ∉ D.1) (hj : j ∉ D.1) :
    InFamily (pairFamily D commitAt) (commitAt i j) :=
  ⟨⟨(i, j, false), hi, hj⟩, by simp [pairFamily]⟩

theorem inFamily_self {commitAt : C.Party → C.Party → Query C} {i : C.Party} (hi : i ∉ D.1) :
    InFamily (pairFamily D commitAt) (.commit .seedGen i i []) :=
  ⟨⟨(i, i, true), hi, hi⟩, by simp [pairFamily]⟩

end Family

/-! ## The calls of the suffix at the family -/

section Calls

variable (D : C.Coalition) (Fam : Query C → Prop)

/-- A programming call at a cell of `Fam`, or a free call at a commitment cell between two honest
operators off `Fam`. -/
def OffCall : (WorldSpec C).Domain → Prop := fun t =>
  (∃ p, t = .inl (.inr p) ∧ Fam p.1) ∨ (∃ q, t = .inr (.inr (.inl q)) ∧ PairCell D q ∧ ¬ Fam q)

theorem noCall_counted_lift {α : Type} (oa : OracleComp (LocalSpec C) α) :
    NoCall (OffCall D Fam) (counted (liftComp oa (SimulatorSpec C))) := by
  change NoCall (OffCall D Fam) (worldRoles.adversary oa)
  rw [noCall_iff]
  induction oa using OracleComp.inductionOn with
  | pure a => simp [worldRoles, counted]
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    have ht : ¬ OffCall D Fam (.inl (.inl t)) := by
      rintro (⟨p, e, -⟩ | ⟨q, e, -⟩) <;> cases e
    rw [e, ThresholdLeanXmssSecurity.adversary_query, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht, fun u => by simpa [ht] using ih u⟩

theorem noCall_program (q : Query C) (v : HashOutput) (hq : ¬ Fam q) : NoCall (OffCall D Fam) (program q v) := by
  unfold program counted
  rw [simulateQ_spec_query]
  refine noCall_query _ _ ?_
  rintro (⟨p, e, hp⟩ | ⟨q', e, -⟩)
  · cases e
    exact hq hp
  · cases e

theorem noCall_free_ro {α : Type} (X : OracleComp (RoSpec C) α)
    (h : NoCall (fun t : (RoSpec C).Domain => ∃ q, t = .inl q ∧ PairCell D q ∧ ¬ Fam q) X) :
    NoCall (OffCall D Fam) (free (liftComp X (LocalSpec C))) := by
  rw [noCall_iff] at h ⊢
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ ∃ q, t = .inl q ∧ PairCell D q ∧ ¬ Fam q := h.1.resolve_right (by omega)
    have ht' : ¬ OffCall D Fam (.inr (.inr t)) := by
      rintro (⟨p, e, -⟩ | ⟨q, e, hq⟩)
      · cases e
      · cases e
        exact ht ⟨q, rfl, hq⟩
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inr t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht', fun u => by simpa [ht'] using ih u (by simpa [ht] using h.2 u)⟩

theorem noCall_free_prob {α : Type} (X : ProbComp α) : NoCall (OffCall D Fam) (free (liftComp X (LocalSpec C))) := by
  rw [noCall_iff]
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have ht' : ¬ OffCall D Fam (.inr (.inl t)) := by
      rintro (⟨p, e, -⟩ | ⟨q, e, -⟩) <;> cases e
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht', fun u => by simpa [ht'] using ih u⟩

theorem noCall_hashQuery_ro (q : Query C) (hq : PairCell D q → Fam q) :
    NoCall (fun t : (RoSpec C).Domain => ∃ q, t = .inl q ∧ PairCell D q ∧ ¬ Fam q) (hashQuery q) := by
  unfold hashQuery
  refine noCall_query _ _ ?_
  rintro ⟨q', e, hp, hf⟩
  cases e
  exact hf (hq hp)

theorem noCall_levelRound (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type} (fuel : ℕ) (state : net.State)
    (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β)))
    (hnext : ∀ j x inbox, NoCall (OffCall D Fam) (free (next j x inbox)))
    (hcont : ∀ f s d', NoCall (OffCall D Fam) (cont f s d')) :
    NoCall (OffCall D Fam) (levelRound D net fuel state d out next cont) := by
  cases fuel with
  | zero => exact noCall_pure _ _
  | succ fuel =>
    rw [levelRound]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left hall]
      exact noCall_pure _ _
    rw [ite_eq_right hall]
    refine noCall_bind _ (noCall_counted_lift D Fam _) fun r => ?_
    by_cases hpart : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left hpart]
      exact noCall_pure _ _
    rw [ite_eq_right hpart]
    refine noCall_bind _ (noCall_sequenceFin _ _ fun j => ?_) fun d' => hcont _ _ _
    by_cases hj : j ∈ D.1
    · simp only [hj, ite_true]
      exact noCall_pure _ _
    · simp only [hj, ite_false]
      rcases d j with _ | x
      · exact noCall_pure _ _
      · dsimp only
        split_ifs
        · exact noCall_pure _ _
        · exact hnext _ _ _

theorem noCall_or {ι' α : Type} {spec : OracleSpec ι'} (p q : ι' → Prop) (oa : OracleComp spec α) (hp : NoCall p oa)
    (hq : NoCall q oa) : NoCall (fun t => p t ∨ q t) oa := by
  rw [noCall_iff] at hp hq ⊢
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp hq ⊢
    have hp' : ¬ p t := hp.1.resolve_right (by omega)
    have hq' : ¬ q t := hq.1.resolve_right (by omega)
    refine ⟨Or.inl (by tauto), fun u => ?_⟩
    have h := ih u (by simpa [hp'] using hp.2 u) (by simpa [hq'] using hq.2 u)
    simpa [hp', hq'] using h

end Calls

section Suffix

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
theorem noCall_secRest_off (Fam : Query C → Prop) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (st : RealState C A.net.State) :
    NoCall (OffCall D Fam) ((secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A parameter seeds dealt emu).run' st) := by
  have hprog : DkgCorrectnessProof.UsedHit.NoProg
      (secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A parameter seeds dealt emu) :=
    DkgCorrectnessProof.UsedHit.NoProg.bind
      (DkgSecurityProof.noProg_secRuns K circuits settings runLimit D _ (fun _ => rfl) A.net parameter seeds dealt emu
        .top runLimit)
      fun _ => DkgSecurityProof.noProg_secSigning K circuits settings runLimit D _ (fun _ => rfl) A parameter seeds
        dealt emu
  have h1 := noCall_map _ Prod.fst (hprog st)
  have h2 := noCall_secRest_seedGenCell K circuits settings runLimit D ⟨true, fun _ => 0⟩ (fun _ => rfl) A parameter
    seeds dealt emu st
  rw [StateT.run'_eq]
  refine noCall_mono _ (fun t ht => ?_) (noCall_or _ _ _ h1 (by rw [StateT.run'_eq] at h2; exact h2))
  rcases ht with ⟨p, rfl, -⟩ | ⟨q, rfl, ⟨i, j, r, -, -, rfl⟩, -⟩
  · exact Or.inl trivial
  · exact Or.inr ⟨_, rfl, rfl⟩

theorem pairCell_commitAt_family {commitAt : C.Party → C.Party → Query C} (hshape : CommitShape commitAt) (i j : C.Party)
    (h : PairCell D (commitAt i j)) : InFamily (pairFamily D commitAt) (commitAt i j) := by
  obtain ⟨r, -, hc⟩ := hshape i j
  obtain ⟨i', j', r', hi, hj, e⟩ := h
  rw [hc] at e
  simp only [Query.commit.injEq, true_and] at e
  obtain ⟨rfl, rfl, -⟩ := e
  exact inFamily_commitAt D hi hj

theorem not_family_of_not_commit {commitAt : C.Party → C.Party → Query C} (hshape : CommitShape commitAt) {q : Query C}
    (hq : ∀ i j r, q ≠ .commit .seedGen i j r) : ¬ InFamily (pairFamily D commitAt) q := by
  intro hf
  rcases hf with ⟨⟨⟨i, j, b⟩, hi, hj⟩, e⟩
  obtain ⟨r, -, hc⟩ := hshape i j
  cases b
  · exact hq i j r (by rw [← e]; simp [pairFamily, hc])
  · exact hq i j [] (by rw [← e]; simp [pairFamily])

omit [Fintype E] [DecidableEq E] in
/-- The suffix makes no programming call at a cell of the family and no free call at a commitment cell
between two honest operators off the family. -/
theorem noCall_suffixAt (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (commitAt : C.Party → C.Party → Query C) (hshape : CommitShape commitAt)
    (termAt : C.Party → Mail C E → C.Term → Query C) (hterm : ∀ i inbox T, ¬ PairCell D (termAt i inbox T)) :
    NoCall (OffCall D (InFamily (pairFamily D commitAt)))
      (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x commitAt termAt) := by
  have hderive : ∀ kind l, ¬ PairCell D (Query.derive .seedGen kind l) := fun _ _ ⟨_, _, _, _, _, h⟩ => by cases h
  have hshared : ∀ l, ¬ PairCell D (Query.sharedKeys .seedGen l) := fun _ ⟨_, _, _, _, _, h⟩ => by cases h
  unfold suffixAt seedGenAt
  simp only [bind_assoc]
  refine noCall_bind _ ?_ fun commitments => noCall_bind _ ?_ fun r => noCall_bind _ ?_ fun _ => ?_
  · unfold commitDrawsAt
    refine noCall_sequenceFin _ _ fun i => ?_
    split_ifs
    · exact noCall_pure _ _
    · exact noCall_free_ro D _ _ (noCall_mapM _ _ _ fun j =>
        noCall_hashQuery_ro D _ _ (pairCell_commitAt_family D hshape i j))
  · rw [observe_eq]
    exact noCall_counted_lift D _ _
  · rw [programBlock_eq_view]
    unfold programBlockView
    refine noCall_bind _ (noCall_free_prob D _ _) fun high => noCall_bind _ (noCall_program D _ _ _
      (not_family_of_not_commit D hshape fun _ _ _ h => by cases h)) fun _ =>
      noCall_bind _ ?_ fun _ => noCall_bind _ ?_ fun _ => noCall_pure _ _
    · refine noCall_mapM _ _ _ fun T => ?_
      split
      · exact noCall_program D _ _ _ (not_family_of_not_commit D hshape fun _ _ _ h => by cases h)
      · exact noCall_pure _ _
    · refine noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_
      split_ifs
      · exact noCall_program D _ _ _ (not_family_of_not_commit D hshape fun _ _ _ h => by cases h)
      · exact noCall_pure _ _
  · refine noCall_bind _ ?_ fun y => ?_
    · refine noCall_levelRound D _ A.net _ _ _ _ _ _ (fun j u inbox => ?_) fun f2 s2 d2 =>
        noCall_levelRound D _ A.net _ _ _ _ _ _ (fun j u inbox => by simp only [echoNext, free_pure]; exact noCall_pure _ _)
          fun _ _ _ => noCall_pure _ _
      unfold revealNextAt
      rw [ThresholdLeanXmssSecurity.free_bind]
      refine noCall_bind _ (noCall_free_ro D _ _ (noCall_mapM _ _ _ fun k => noCall_hashQuery_ro D _ _ fun hp => ?_))
        fun opens => ?_
      · split_ifs at hp ⊢ with hk
        · by_cases hkD : k ∈ D.1
          · rw [openAddress_corrupt _ _ _ _ _ hkD] at hp
            obtain ⟨_, _, _, hk', -, e⟩ := hp
            simp only [Query.commit.injEq, true_and] at e
            exact absurd (e.1 ▸ hkD) hk'
          · have hki : k = j := hk.resolve_left hkD
            subst hki
            rw [openAddress_self _ _ _ _ hkD]
            exact inFamily_self D hkD
        · exact pairCell_commitAt_family D hshape k j hp
      · split_ifs
        · simp only [ThresholdLeanXmssSecurity.free_bind, free_pure]
          refine noCall_bind _ (noCall_free_ro D _ _ ?_) fun keys =>
            noCall_bind _ (noCall_free_ro D _ _ (noCall_mapM _ _ _ fun j' =>
              noCall_hashQuery_ro D _ _ fun hp => absurd hp (hshared _))) fun _ => noCall_pure _ _
          unfold deriveAt
          refine noCall_bind _ (noCall_hashQuery_ro D _ _ fun hp => absurd hp (hderive _ _)) fun _ =>
            noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ =>
            noCall_bind _ (noCall_mapM _ _ _ fun j' => ?_) fun _ => noCall_pure _ _
          · split_ifs
            · exact noCall_hashQuery_ro D _ _ fun hp => absurd hp (hterm _ _ _)
            · exact noCall_pure _ _
          · split_ifs
            · exact noCall_pure _ _
            · exact noCall_hashQuery_ro D _ _ fun hp => absurd hp (hderive _ _)
        · simp only [free_pure]
          exact noCall_pure _ _
    · rcases y with ⟨state, emu⟩
      exact noCall_bind _ (noCall_secRest_off K circuits settings runLimit D _ A _ _ _ _ _) fun _ => noCall_pure _ _

end Suffix

/-! ## The glue to `CommitShift` -/

section Glue

variable (prims : Primitives) (D : C.Coalition)

theorem desWorld_flagAt (X : Query C) (t : (WorldSpec C).Domain) (s : PairState C) :
    (fun r => (r.1, (r.2.1, r.2.2.2))) <$> (desWorld prims D (fun _ => False) (TouchAt X) t).run s =
      (flagAt prims D X t).run (s.1, s.2.2) := by
  by_cases hf : ∃ q, t = .inr (.inr (.inl q))
  · obtain ⟨q, rfl⟩ := hf
    rw [desWorld_free prims D _ _ not_false, Functor.map_map]
    simp only [flagAt, StateT.run_mk]
    congr 1
    funext r
    have h : decide (TouchAt X (.inr (.inr (.inl q)) : (WorldSpec C).Domain)) = false := decide_eq_false id
    rw [h, Bool.or_false]
  · push Not at hf
    rw [desWorld_other prims D _ _ t hf, Functor.map_map]
    rfl

theorem desWorld_family (Fam : Query C → Prop) (hFam : ∀ q, Fam q → PairCell D q) (P : (WorldSpec C).Domain → Prop)
    (t : (WorldSpec C).Domain) (ht : ¬ OffCall D Fam t) : desWorld prims D Fam P t = desWorld prims D (PairCell D) P t := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  by_cases hq : Fam q
  · simp only [desWorld, hq, hFam q hq, ite_true]
  · have hp : ¬ PairCell D q := fun hp => ht (Or.inr ⟨q, rfl, hp, hq⟩)
    simp only [desWorld, hq, hp, ite_false]

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The pad of the honest pair cells does not change the suffix on the shifted parts. -/
def ShiftPad : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput), ¬ KnownTo D.1 T → ∀ π : PairIndex C D → HashOutput,
    simulateQ (padCells (pairFamily D (commitAddress (shiftBy T δ x.2.2))) π)
        (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress (shiftBy T δ x.2.2))
          (termAddress D (shiftBy T δ x.2.2))) =
      suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress (shiftBy T δ x.2.2))
        (termAddress D (shiftBy T δ x.2.2))

omit [Fintype E] [DecidableEq E] in
/-- `ShiftPad` gives `CommitShift`, with one law of the flag in the two runs. -/
theorem commitShift_of_pad (pad : ShiftPad K circuits settings runLimit) :
    CommitShift prims K circuits settings runLimit := by
  intro D A T δ hT
  refine le_of_eq ?_
  unfold shiftRun pairShiftRun
  rw [DkgSecurityProof.prEvent_bind_wp, DkgSecurityProof.prEvent_bind_wp]
  refine congrArg _ (funext fun x => ?_)
  simp only [bind_pure_comp, prEvent_map]
  set X := hiddenInput (shiftBy T δ x.1.2.2) T
  set Pr' := suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.1 (commitAddress (shiftBy T δ x.1.2.2))
    (termAddress D (shiftBy T δ x.1.2.2))
  set b := (x.2.1.1 X).isSome
  have hshape := commitShape_commitAddress (shiftBy T δ x.1.2.2)
  have hnc := noCall_suffixAt K circuits settings runLimit D A x.1 _ hshape (termAddress D (shiftBy T δ x.1.2.2))
    (fun _ _ _ ⟨_, _, _, _, _, h⟩ => by cases h)
  have hmap := run_map_state _ _ (fun s : PairState C => (s.1, s.2.2)) (desWorld_flagAt prims D X) Pr' (x.2, ∅, b)
  have hfix : ∀ p, ¬ IsFixed (pairFamily D (commitAddress (shiftBy T δ x.1.2.2)) p) := by
    rintro p ⟨_, h, _⟩
    unfold pairFamily at h
    split at h <;> simp [commitAddress] at h
  have hstream : ∀ p k, pairFamily D (commitAddress (shiftBy T δ x.1.2.2)) p ≠ .streamKey k := by
    intro p k h
    unfold pairFamily at h
    split at h <;> simp [commitAddress] at h
  have hmap' : (fun r => (r.1, (r.2.1, r.2.2.2))) <$>
      (simulateQ (desWorld prims D (fun _ => False) (TouchAt X)) Pr').run ((x.2, ∅, b) : PairState C) =
      (simulateQ (flagAt prims D X) Pr').run (x.2, b) := hmap
  rw [prEvent_eq_wp_indicator, prEvent_eq_wp_indicator, ← hmap', wp_map, pairWorld_eq_desWorld,
    ← simulateQ_congr_of_noCall _ _ _ (fun t ht => desWorld_family prims D _
      (fun q ⟨p, hp⟩ => hp ▸ pairFamily_pairCell D _ hshape p) (TouchAt X) t ht) Pr' hnc]
  exact wp_shared_eq_des prims D (pairFamily D _) (TouchAt X) (pairFamily_injective D hshape) hfix hstream
    (fun _ f => if f = true then 1 else 0) Pr'
    (noCall_mono _ (fun t ⟨p, e, hp⟩ => Or.inl ⟨p, e, hp⟩) hnc) (pad D A x.1 T δ hT) x.2 b

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.commitShift_of_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.commitShift_of_pad
