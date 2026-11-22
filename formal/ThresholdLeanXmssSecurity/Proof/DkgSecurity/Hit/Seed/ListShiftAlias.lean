import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.ListShiftSafe

/-!
# The bound of the alias from the law of the round-2 mail

`listAliasBound_of_shift` proves `ListAliasBound` from `MidShiftLaw`.

* `MidShiftLaw` states that in `listMidRun` the joint law of the round-2 mail of the adversary and
  the parts does not change when the term parts of a hidden term `T'` move by a fixed shift `c`. The
  mail is chosen on a view that holds no part of `T'`.
* For an honest `j`, a known `T` and a hidden `T'`, the derive address of `T` at `j` reads the mail
  and the parts of `T`, and the shift of `T'` does not change it. A uniform shift makes
  `hiddenInput parts T'` uniform, so the two meet with probability at most `2^-(256 t)`
  (`probEvent_hiddenInput_eq_le`). The union over the at most `n k h` triples gives `aliasCost D`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- A probability `p` that is at most the probability of `event v` in one run for each `v`, where for
each result of the run the event has probability at most `ε` over `v`, is at most `ε`. -/
theorem prEvent_le_of_mean {V Y : Type} (vd : ProbComp V) (run : ProbComp Y) (event : V → Y → Prop) (p ε : ℝ≥0∞)
    (step : ∀ v, p ≤ Pr{let y ← run}[event v y]) (each : ∀ y ∈ support run, Pr{let v ← vd}[event v y] ≤ ε) :
    p ≤ ε := by
  have h₁ : p ≤ wp vd (fun v => wp run (fun y => if event v y then 1 else 0)) := by
    calc p = wp vd (fun _ => p) := (wp_const _ p).symm
      _ ≤ _ := wp_mono _ fun v => (step v).trans_eq (prEvent_eq_wp_indicator _ _)
  refine h₁.trans ?_
  rw [DkgSecurityProof.wp_swap]
  refine (wp_mono_of_support run fun y hy => ?_).trans_eq (wp_const run _)
  rw [← prEvent_eq_wp_indicator]
  exact each y hy

/-- The derive address of a term reads the inbox only at the corrupt senders. -/
theorem termAddress_inbox (D : C.Coalition) (parts : C.Party → Parts C) (j : C.Party) (inbox inbox' : Mail C E)
    (T : C.Term) (h : ∀ k, k ∈ D.1 → inbox k = inbox' k) :
    termAddress D parts j inbox T = termAddress D parts j inbox' T := by
  unfold termAddress normView
  congr 1
  refine List.map_congr_left fun k _ => ?_
  split_ifs with hk
  · rw [h k hk]
  · rfl

/-- The alias of the honest operator `j`, the known term `T` and the hidden term `T'` on the round-2
mail `o.1` and the parts `o.2`. -/
def AliasAt (D : C.Coalition) (j : C.Party) (T T' : C.Term)
    (o : Option (C.Party → C.Party → Option (Msg E)) × (C.Party → Parts C)) : Prop :=
  ∃ s, o.1 = some s ∧ termAddress D o.2 j (fun k => s k j) T = hiddenInput o.2 T'

theorem midAlias_imp (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (parts : C.Party → Parts C)
    (w : ListMid C E net.State) (h : MidAlias D net parts w) :
    ∃ p ∈ (Finset.univ ×ˢ knownTerms D ×ˢ hiddenTerms D : Finset (C.Party × C.Term × C.Term)),
      AliasAt D p.1 p.2.1 p.2.2 (w.2.2.map Prod.snd, parts) := by
  unfold MidAlias at h
  rcases hw : w.2.2 with _ | r2
  · rw [hw] at h
    exact h.elim
  · rw [hw] at h
    obtain ⟨j, -, T, hT, -, T', hT', heq⟩ := h
    refine ⟨(j, T, T'), by simp [knownTerms, hiddenTerms, hT, hT'], r2.2, by simp, ?_⟩
    rw [← heq]
    refine termAddress_inbox D parts j _ _ T fun k hk => ?_
    simp [levelInbox, hk]

theorem hiddenInput_shiftAll_comm (T' : C.Term) (parts parts' : C.Party → Parts C) :
    hiddenInput (shiftAll T' (fun k => (parts' k).term T') parts) T' =
      hiddenInput (shiftAll T' (fun k => (parts k).term T') parts') T' := by
  unfold hiddenInput
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp [shiftAll, shiftParts, BitVec.xor_comm]

/-- For fixed parts and a fixed cell, a uniform shift of the term parts of `T'` meets the cell with
probability at most `2^-(256 t)`. -/
theorem probEvent_shift_hiddenInput_le (T' : C.Term) (parts : C.Party → Parts C) (L : Query C) :
    Pr{let parts' ← partsDraw C}[L = hiddenInput (shiftAll T' (fun k => (parts' k).term T') parts) T'] ≤
      ((Fintype.card HashOutput : ℝ≥0∞) ^ C.t)⁻¹ := by
  calc _ = Pr{let p ← partsDraw C}[hiddenInput (shiftAll T' (fun k => (parts k).term T') p) T' = L] := by
        simp only [hiddenInput_shiftAll_comm T' parts, @eq_comm _ L]
    _ = Pr{let p ← shiftAll T' (fun k => (parts k).term T') <$> partsDraw C}[hiddenInput p T' = L] :=
        (prEvent_map (partsDraw C) (shiftAll T' (fun k => (parts k).term T')) (fun p => hiddenInput p T' = L)).symm
    _ = Pr{let p ← partsDraw C}[hiddenInput p T' = L] := (evalDist_shiftAll T' _).prEvent_eq _
    _ ≤ _ := probEvent_hiddenInput_eq_le T' L

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives)

/-- The round-2 mail of the adversary in the result of `listMidRun`, if round 2 takes place. -/
def midMail {σ : Type} (m : (PrefixOut C σ × LogState C) × (C.Term → HashOutput) × (ListMid C E σ × LogState C)) :
    Option (C.Party → C.Party → Option (Msg E)) :=
  m.2.2.1.2.2.map Prod.snd

/-- The law of the round-2 mail and the parts. In the list run up to the call of the adversary in
round 2, the joint law of the round-2 mail and the parts does not change when the term parts of a
hidden term `T'` move by a fixed shift `c`. The parts of `T'` enter the run before that call only
through the commit cells of two honest holders of `T'`. Their answers reach only the honest receiver,
and a counted call at such a cell sees a uniform answer whether or not the cell holds a commitment.
The statement is on the whole run from the empty start. -/
def MidShiftLaw : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (T' : C.Term), ¬ KnownTo D.1 T' → ∀ c : C.Party → HashOutput,
    (fun m => (midMail m, shiftAll T' c m.1.1.2.2)) <$> listMidRun prims D A =ᵈ
      (fun m => (midMail m, m.1.1.2.2)) <$> listMidRun prims D A

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The alias of one triple has probability at most `2^-(256 t)`. -/
theorem probEvent_aliasAt_le (law : MidShiftLaw (C := C) (E := E) prims) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (j : C.Party) {T T' : C.Term} (hT : KnownTo D.1 T) (hT' : ¬ KnownTo D.1 T') :
    Pr{let m ← listMidRun prims D A}[AliasAt D j T T' (midMail m, m.1.1.2.2)] ≤
      ((Fintype.card HashOutput : ℝ≥0∞) ^ C.t)⁻¹ := by
  have hne : T ≠ T' := fun e => hT' (e ▸ hT)
  refine prEvent_le_of_mean (partsDraw C) (listMidRun prims D A)
    (fun parts' m => AliasAt D j T T' (midMail m, shiftAll T' (fun k => (parts' k).term T') m.1.1.2.2)) _ _
    (fun parts' => le_of_eq ?_) (fun m _ => ?_)
  · have h := (law D A T' hT' (fun k => (parts' k).term T')).prEvent_eq (AliasAt D j T T')
    rw [prEvent_map, prEvent_map] at h
    exact h.symm
  · rcases hm : midMail m with _ | s
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun parts' _ h => ?_) bot_le
      obtain ⟨s, hs, -⟩ := h
      simp at hs
    · refine le_trans (prEvent_mono _ _ _ fun parts' h => ?_)
        (probEvent_shift_hiddenInput_le T' m.1.1.2.2 (termAddress D m.1.1.2.2 j (fun k => s k j) T))
      obtain ⟨s', hs', heq⟩ := h
      simp only [Option.some.injEq] at hs'
      subst hs'
      rw [← heq]
      exact termAddress_congr D _ _ j _ T fun k _ _ =>
        (SeedNormal.shiftAll_term_ne _ _ (fun k => (parts' k).term T') m.1.1.2.2 k hne).symm

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `MidShiftLaw` gives `ListAliasBound`. -/
theorem listAliasBound_of_shift (law : MidShiftLaw (C := C) (E := E) prims) :
    ListAliasBound (C := C) (E := E) prims := by
  intro D A
  have h1 := prEvent_exists_finset_le_card_mul (Finset.univ ×ˢ knownTerms D ×ˢ hiddenTerms D) (listMidRun prims D A)
    (fun p m => AliasAt D p.1 p.2.1 p.2.2 (midMail m, m.1.1.2.2)) (ε := ((Fintype.card HashOutput : ℝ≥0∞) ^ C.t)⁻¹)
    fun p hp => by
      simp only [Finset.mem_product, knownTerms, hiddenTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact probEvent_aliasAt_le prims law D A p.1 hp.1 hp.2
  refine (prEvent_mono _ _ _ fun m h => midAlias_imp D A.net m.1.1.2.2 m.2.2.1 h).trans (h1.trans_eq ?_)
  have hcard : (Fintype.card HashOutput : ℝ≥0∞) = 2 ^ 256 := by
    simp
    norm_num
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin, hcard, aliasCost, div_eq_mul_inv,
    ← pow_mul]
  push_cast
  ring

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listAliasBound_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listAliasBound_of_shift
