import ThresholdLeanXmssSecurity.Proof.Check
import ThresholdLeanXmssSecurity.Proof.MainStages

/-!
# The schedule of the check of a batch

`scheduled` is a wrapper of the adversary with a schedule counter in its state. `liveSet` and
`PartialOut` give the honest operators with an output after a call, and the tails move a step of the
live operators into a reply, and `roundScheduled` adds tails to the rounds. The challenge search of
the wrapper and the digest round after a partial start follow. `roundPhase_full` is the normal form of a round of all honest operators.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkGP

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## Live sets -/

/-- The honest operators with an output. They are the live operators of the next phase. -/
def liveSet {β : Type} (D : C.Coalition) (out : C.Party → Option β) : Finset C.Party :=
  Finset.univ.filter fun i => i ∉ D.1 ∧ (out i).isSome

/-- A partial abort. An honest operator has no output, and an honest operator has one. -/
def PartialOut {β : Type} (D : C.Coalition) (out : C.Party → Option β) : Prop :=
  (∃ i ∉ D.1, out i = none) ∧ ∃ i ∉ D.1, (out i).isSome

theorem liveSet_congr {β γ : Type} (D : C.Coalition) (out : C.Party → Option β) (out' : C.Party → Option γ)
    (h : ∀ i ∉ D.1, (out i).isSome = (out' i).isSome) : liveSet D out = liveSet D out' := by
  unfold liveSet
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨hi, (h i hi) ▸ hs⟩
  · rintro ⟨hi, hs⟩
    exact ⟨hi, (h i hi).symm ▸ hs⟩

theorem partialOut_congr {β γ : Type} (D : C.Coalition) (out : C.Party → Option β) (out' : C.Party → Option γ)
    (h : ∀ i ∉ D.1, (out i).isSome = (out' i).isSome) : PartialOut D out ↔ PartialOut D out' := by
  unfold PartialOut
  constructor
  · rintro ⟨⟨i, hi, hn⟩, j, hj, hs⟩
    refine ⟨⟨i, hi, ?_⟩, j, hj, (h j hj) ▸ hs⟩
    have := h i hi
    rw [hn, Option.isSome_none] at this
    exact Option.not_isSome_iff_eq_none.1 (by rw [← this]; decide)
  · rintro ⟨⟨i, hi, hn⟩, j, hj, hs⟩
    refine ⟨⟨i, hi, ?_⟩, j, hj, (h j hj).symm ▸ hs⟩
    have := h i hi
    rw [hn, Option.isSome_none] at this
    exact Option.not_isSome_iff_eq_none.1 (by rw [this]; decide)

/-- The honest receivers that a leak `l` and a reply `r` name. -/
def receivers {L R : Type} (D : C.Coalition) (names : L → R → C.Party → Prop) (l : L) (r : R) :
    C.Party → Option Unit :=
  fun i => if i ∉ D.1 ∧ names l r i then some () else none

/-! ## The wrapper with a schedule counter -/

/-- The wrapper of a batch. Its state is the state of `W` and the position `n` of the next call in the
public schedule. For the leak of call `n` it replies with `sims n`. If the reply names some honest
receivers and not all, it then runs `tails n` on these receivers. -/
@[reducible] def scheduled {Ia L R : Type} (D : C.Coalition) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State) : Adversary C E Ia L R where
  State := W.State × ℕ
  start x z := (fun s => (s, 0)) <$> W.start x z
  round s m := (fun r => ((r.1, s.2), r.2)) <$> W.round s.1 m
  answer s l := do
    let a ← sims s.2 s.1 l
    if PartialOut D (receivers D names l a.2) then
      (fun st' => ((st', s.2 + 1), a.2)) <$> tails s.2 (liveSet D (receivers D names l a.2)) a.1
    else pure ((a.1, s.2 + 1), a.2)

/-- No tail. -/
def noTails {σ : Type} : ℕ → Finset C.Party → σ → OracleComp (LocalSpec C) σ := fun _ _ s => pure s

/-! ## The phase of one call -/

/-- The program after a call. -/
def ofOption {ι : Type} {G : OracleSpec ι} {α : Type} : Option α → PartyM C E G α
  | some z => pure z
  | none => failure

/-- One call of a functionality. The program keeps the output that `extract` reads. -/
def callProg {I O α : Type} (x : I) (extract : O → Option α) : PartyM C E (CallSpec I O) α :=
  call x >>= fun r => ofOption (r.bind extract)

/-- A phase of one call, from a start with all operators. -/
def callPhase {Ia I O L R α : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (st : A.State) (inp : C.Party → I) (extract : C.Party → O → Option α) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option α)) :=
  executePhase localRoles D A F fuel st fun i => callProg (inp i) (extract i)

theorem advance_ofOption {ι : Type} {G : OracleSpec ι} {α : Type} (o : Option α) :
    advance (ofOption (C := C) (E := E) (G := G) o).run = pure (.done o) := by
  cases o with
  | some z => exact advance_run_pure z
  | none => exact advance_run_failure

section Phase

variable {Ia I O L R α P X : Type} (D : C.Coalition) (F : Functionality C I O L R) (inp : C.Party → I)
  (extract : C.Party → O → Option α) (pre : OracleComp (LocalSpec C) P) (lk : P → L)
  (samp : P → R → OracleComp (LocalSpec C) X) (outF : P → R → X → C.Party → Option O)

/-- The phase of one call is the part before the leak, one reply of the adversary, and the samples of
the functionality after the leak. -/
theorem callPhase_eq (A : Adversary C E Ia L R)
    (hF : ∀ st, runFunctionality localRoles D A F st (fun i => if i ∈ D.1 then none else some (inp i)) =
      pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x => pure (a.1, outF p a.2 x))
    (fuel : ℕ) (st : A.State) :
    callPhase D A F (fuel + 1) st inp extract =
      pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x =>
        pure (a.1, fun j => if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j)) := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  have hstart : startSteps localRoles D (fun i => callProg (C := C) (E := E) (inp i) (extract i)) =
      pure fun i => if i ∈ D.1 then .done none else
        .call (inp i) fun r => (ofOption (r.bind (extract i))).run := by
    unfold startSteps
    refine stages_sequenceFin_eq_pure _ _ fun i => ?_
    by_cases hi : i ∈ D.1
    · simp only [hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte, localRoles]
      rfl
  unfold callPhase executePhase
  rw [hstart, pure_bind, executeRounds,
    ite_eq_right (fun hall => by simpa only [Step.isDone, hi₀, ↓reduceIte] using hall i₀ hi₀)]
  unfold stepRound
  rw [ite_eq_left ⟨⟨i₀, hi₀, by simp only [Step.callInput, hi₀, ↓reduceIte, Option.isSome_some]⟩, fun i hi => by simp only [Step.callInput, hi, ↓reduceIte, Option.isSome_some, Step.isDone_call, or_false]⟩]
  have hin : (fun i => if i ∈ D.1 then none else
      ((if i ∈ D.1 then .done none else .call (inp i) fun r => (ofOption (r.bind (extract i))).run :
        Step C E (CallSpec I O) α)).callInput) = fun i => if i ∈ D.1 then none else some (inp i) := by
    funext i
    by_cases hi : i ∈ D.1 <;> simp only [hi, ↓reduceIte, Step.callInput]
  rw [hin, hF]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun p => bind_congr fun a => bind_congr fun x => ?_
  rw [stages_sequenceFin_eq_pure _
    (fun j => Step.done (if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j))) (fun j => ?_), pure_bind]
  · rw [stages_executeRounds_allDone D A F fuel a.1
      (fun j => Step.done (if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j))) fun _ => trivial]
    rfl
  · by_cases hj : j ∈ D.1
    · simp only [hj, ↓reduceIte]
    · simp only [hj, ↓reduceIte, localRoles]
      exact advance_ofOption _

/-- The tail inside the reply to the call is the tail after the phase of this call. The
samples of the functionality after the leak and the tail commute, by lazy sampling. The statement
holds for every functionality of this form, for every block simulator `sims`, every tail and every
position `k` of the schedule. -/
theorem callPhase_tail (prims : Primitives) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State)
    (hF : ∀ (A : Adversary C E Ia L R) st,
      runFunctionality localRoles D A F st (fun i => if i ∈ D.1 then none else some (inp i)) =
        pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x => pure (a.1, outF p a.2 x))
    (hnames : ∀ p r x, ∀ j ∉ D.1, ((outF p r x j).bind (extract j)).isSome ↔ names (lk p) r j)
    (fuel : ℕ) (st : W.State) (k : ℕ) :
    SameRun prims
      (callPhase D (scheduled D W sims names tails) F (fuel + 1) (st, k) inp extract)
      (callPhase D (scheduled D W sims names noTails) F (fuel + 1) (st, k) inp extract >>= fun r =>
        if PartialOut D r.2 then (fun s' => ((s', r.1.2), r.2)) <$> tails k (liveSet D r.2) r.1.1
        else pure r) := by
  rw [callPhase_eq D F inp extract pre lk samp outF _ (hF _), callPhase_eq D F inp extract pre lk samp outF _ (hF _)]
  rw [bind_assoc]
  refine SameRun.bind_right _ fun p => ?_
  dsimp only [scheduled]
  rw [bind_assoc, bind_assoc, bind_assoc]
  refine SameRun.bind_right _ fun a => ?_
  have hsome : ∀ x, ∀ j ∉ D.1,
      (if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j)).isSome =
        (receivers D names (lk p) a.2 j).isSome := fun x j hj => by
    unfold receivers
    by_cases hn : names (lk p) a.2 j
    · simp only [hj, ↓reduceIte, not_false_eq_true, true_and, hn, Option.isSome_some]
      exact (hnames p a.2 x j hj).2 hn
    · simp only [hj, ↓reduceIte, not_false_eq_true, true_and, hn, Option.isSome_none]
      exact Bool.eq_false_iff.2 fun h => hn ((hnames p a.2 x j hj).1 h)
  by_cases hp : PartialOut D (receivers D names (lk p) a.2)
  · have hp' : ∀ x, PartialOut D (fun j => if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j)) :=
      fun x => (partialOut_congr D _ _ (hsome x)).2 hp
    have hl : ∀ x, liveSet D (fun j => if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j)) =
        liveSet D (receivers D names (lk p) a.2) := fun x => liveSet_congr D _ _ (hsome x)
    simp only [hp, hp', hl, ↓reduceIte, noTails, pure_bind, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply]
    exact sameRun_swap prims _ _ _
  · have hp' : ∀ x, ¬ PartialOut D (fun j => if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j)) :=
      fun x h => hp ((partialOut_congr D _ _ (hsome x)).1 h)
    simp only [hp, ↓reduceIte, pure_bind]
    rw [bind_assoc]
    simp only [pure_bind, hp', ↓reduceIte]
    exact SameRun.refl prims _

end Phase

end ThresholdLeanXmssSecurity.RealNetworkGP

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkGP

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## A phase after a partial abort that starts with a round -/

section PartialRound

variable {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- The run after a partial abort, with a round first. -/
theorem executeRounds_partialRound (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none)
    (h : ∀ i ∉ D.1, steps i = .done none ∨ ∃ outbox resume, steps i = .wait outbox resume ∧
      ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none))
    (hab : ∃ i ∉ D.1, steps i = .done none) :
    executeRounds localRoles D A F (fuel + 1) st steps =
      if ∀ i ∉ D.1, (steps i).isDone then pure (st, fun _ => none) else
        A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) >>= fun r =>
          pure (r.1, fun _ => none) := by
  by_cases hdone : ∀ i ∉ D.1, (steps i).isDone
  · rw [executeRounds, ite_eq_left hdone, ite_eq_left hdone]
    congr 2
    funext i
    by_cases hi : i ∈ D.1
    · simp only [Step.output, hD i hi]
    · rcases h i hi with h' | ⟨outbox, resume, h', -⟩
      · simp only [Step.output, h']
      · have := hdone i hi
        rw [h'] at this
        exact this.elim
  · rw [executeRounds, ite_eq_right hdone, ite_eq_right hdone]
    obtain ⟨i₀, hi₀, hdone₀⟩ := hab
    have hnocall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
        ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
      rintro ⟨⟨i, hi, hc⟩, -⟩
      rcases h i hi with h' | ⟨outbox, resume, h', -⟩ <;> simp only [Step.callInput, h', Option.isSome_none, Bool.false_eq_true] at hc
    unfold stepRound
    rw [ite_eq_right hnocall]
    simp only [localRoles, bind_assoc]
    refine bind_congr fun r => ?_
    rw [stages_sequenceFin_eq_pure _ (fun _ => Step.done none) (fun j => ?_), pure_bind, pure_bind]
    · exact stages_executeRounds_done D A F fuel r.1 _ fun _ => rfl
    by_cases hj : j ∈ D.1
    · simp only [hD j hj]
    · rcases h j hj with h' | ⟨outbox, resume, h', hres⟩
      · simp only [h']
      · simp only [h', hj, ite_false]
        exact hres _ ⟨i₀, by simp only [hi₀, ↓reduceIte, hdone₀, delivered_done_none]⟩

/-- The run of a phase after a partial abort, whose live programs start with a round. A program of a live
operator is `prog i v`, which sends `out i v` and then rejects an abort frame. -/
theorem roundPhase_partial {β V : Type} (prog : C.Party → V → PartyM C E (CallSpec I O) β)
    (out : C.Party → V → Mail C E) (cont : C.Party → V → Mail C E → PartyM C E (CallSpec I O) β)
    (hadv : ∀ i v, advance (prog i v).run = pure (.wait (out i v) (exchangeResume (cont i v))))
    (fuel : ℕ) (st : A.State) (inputs : C.Party → Option V) (hp : PartialOut D inputs) :
    executePhase localRoles D A F (fuel + 1) st (fun i => (inputs i).elim failure (prog i)) =
      A.round st (fun c i => if c ∈ D.1 ∧ i ∈ liveSet D inputs then
        (inputs i).elim none fun v => out i v c else none) >>= fun r => pure (r.1, fun _ => none) := by
  let step : C.Party → Step C E (CallSpec I O) β := fun i =>
    if i ∈ D.1 then .done none else
      match inputs i with
      | none => .done none
      | some v => .wait (out i v) (exchangeResume (cont i v))
  have hstart : startSteps localRoles D (fun i => (inputs i).elim failure (prog i)) = pure step := by
    unfold startSteps
    refine stages_sequenceFin_eq_pure _ _ fun i => ?_
    by_cases hi : i ∈ D.1
    · simp only [step, hi, ↓reduceIte]
    · simp only [step, hi, ↓reduceIte, localRoles]
      cases hx : inputs i with
      | none => exact advance_run_failure
      | some v => exact hadv i v
  unfold executePhase
  rw [hstart, pure_bind]
  obtain ⟨⟨i₀, hi₀, hnone⟩, i₁, hi₁, hsome⟩ := hp
  rw [executeRounds_partialRound D A F fuel st step
    (fun i hi => by simp only [step, hi, ↓reduceIte])
    (fun i hi => by
      simp only [step, hi, ↓reduceIte]
      cases inputs i with
      | none => exact Or.inl rfl
      | some v =>
        refine Or.inr ⟨_, _, rfl, fun inbox ⟨k, hk⟩ => ?_⟩
        have hany : (C.parties.any fun j => Msg.isAbort (inbox j)) = true :=
          List.any_eq_true.2 ⟨k, List.mem_finRange k, by simp only [Msg.isAbort, hk]⟩
        simp only [exchangeResume, hany, ite_true, advance_pure])
    ⟨i₀, hi₀, by simp only [step, hi₀, ↓reduceIte, hnone]⟩]
  have hnot : ¬ ∀ i ∉ D.1, (step i).isDone := fun hall => by
    have h := hall i₁ hi₁
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
    simp only [step, hi₁, ↓reduceIte, hv] at h
    exact h
  rw [ite_eq_right hnot]
  congr 2
  funext c i
  unfold liveSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hc : c ∈ D.1
  · by_cases hi : i ∈ D.1
    · simp only [hc, hi, not_true_eq_false, and_false, ↓reduceIte, false_and]
    · cases hx : inputs i with
      | none => simp only [hc, hi, not_false_eq_true, and_self, ↓reduceIte, Step.outbox, hx, Option.isSome_none, Bool.false_eq_true, and_false, step]
      | some v => simp only [hc, hi, not_false_eq_true, and_self, ↓reduceIte, Step.outbox, hx, Option.isSome_some, Option.elim_some, step]
  · simp only [hc, false_and, ↓reduceIte]

end PartialRound

/-- Two uniform samples keep their distribution under a translation. -/
theorem evalDist_translate {α β δ : Type} [AddGroup α] [AddGroup β] [SampleableType α] [SampleableType β]
    (F : α → β → ProbComp δ) (a : α) (b : β) :
    (do let x ← $ᵗ α; let y ← $ᵗ β; F x y) =ᵈ (do let x ← $ᵗ α; let y ← $ᵗ β; F (x + a) (y + b)) :=
  (evalDist_bind_congr_all _ fun x => (evalDist_bind_add_uniform b (F x)).symm).trans
    (evalDist_bind_add_uniform a (fun x => do let y ← $ᵗ β; F x (y + b))).symm

/-! ## The tail of a peer reshare over any codec -/

section Peer

variable [Field E] [Algebra Bit E] {M : Type} [Field M] [SampleableType M]

/-- The messages of a peer reshare do not depend on the inputs (GS20, Lemma 4), over any codec. -/
theorem sameRun_realMsgs {γ : Type} (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (codec : Codec C E M) (count : ℕ) (known : Shares C M) (knownPairs : C.Party → C.Party → ℕ → M)
    (v : C.Party → ℕ → M) (X : (C.Party → C.Party → Option (Msg E)) → OracleComp (LocalSpec C) γ) :
    SameRun prims
      (do
        let fresh ← liftComp ($ᵗ (C.Term → Fin count → M)) (LocalSpec C)
        let freshPair ← liftComp ($ᵗ (C.Pair → Fin count → M)) (LocalSpec C)
        X (realMsgs K D codec known knownPairs fresh freshPair v))
      (do
        let fresh ← liftComp ($ᵗ (C.Term → Fin count → M)) (LocalSpec C)
        let freshPair ← liftComp ($ᵗ (C.Pair → Fin count → M)) (LocalSpec C)
        X (realMsgs K D codec known knownPairs fresh freshPair fun _ _ => 0)) := by
  obtain ⟨T0, p, hpiv⟩ := exists_pivot K D
  intro s
  simp only [simulateQ_bind, StateT.run_bind, run_liftComp_prob, bind_map_left]
  refine (evalDist_translate _ (termShift K D T0 p v 0) (pairShift p (pairDelta K D T0 p v 0))).trans ?_
  simp only [realMsgs_shift K D codec known knownPairs _ _ hpiv v 0]
  exact .rfl

end Peer

end ThresholdLeanXmssSecurity.RealNetworkGP

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

section Live

/-- The honest operators with an output. They are the live operators of the next phase. -/
def liveSet {β : Type} (D : C.Coalition) (out : C.Party → Option β) : Finset C.Party :=
  Finset.univ.filter fun i => i ∉ D.1 ∧ (out i).isSome

/-- A partial abort. An honest operator has no output, and an honest operator has one. -/
def PartialOut {β : Type} (D : C.Coalition) (out : C.Party → Option β) : Prop :=
  (∃ i ∉ D.1, out i = none) ∧ ∃ i ∉ D.1, (out i).isSome

/-- The honest receivers that a leak `l` and a reply `r` name. -/
def receivers {L R : Type} (D : C.Coalition) (names : L → R → C.Party → Prop) (l : L) (r : R) :
    C.Party → Option Unit :=
  fun i => if i ∉ D.1 ∧ names l r i then some () else none

/-- The honest operators that a predicate `P` names. -/
def survivors (D : C.Coalition) (P : C.Party → Prop) : C.Party → Option Unit :=
  fun i => if i ∉ D.1 ∧ P i then some () else none

end Live

section Wrapper

/-- The wrapper with tails in its replies and in its rounds. -/
@[reducible] def roundScheduled {Ia L R : Type} (D : C.Coalition) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State)
    (surv : ℕ → (C.Party → C.Party → Option (Msg E)) → (C.Party → C.Party → Option (Msg E)) → C.Party → Prop)
    (rtails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State) : Adversary C E Ia L R where
  State := W.State × ℕ
  start x z := (fun s => (s, 0)) <$> W.start x z
  round s m := do
    let r ← W.round s.1 m
    if PartialOut D (survivors D (surv s.2 m r.2)) then
      (fun st' => ((st', s.2), r.2)) <$> rtails s.2 (liveSet D (survivors D (surv s.2 m r.2))) r.1
    else pure ((r.1, s.2), r.2)
  answer s l := do
    let a ← sims s.2 s.1 l
    if PartialOut D (receivers D names l a.2) then
      (fun st' => ((st', s.2 + 1), a.2)) <$> tails s.2 (liveSet D (receivers D names l a.2)) a.1
    else pure ((a.1, s.2 + 1), a.2)

/-- The adversary `W` with other leaks and replies. `roundScheduled` reads only its start and its
rounds. -/
def relabel {Ia L R L' R' : Type} (W : Adversary C E Ia L R) (reply : L' → R') : Adversary C E Ia L' R' where
  State := W.State
  start := W.start
  round := W.round
  answer s l := pure (s, reply l)

/-- The adversary `W` with a memory `M` that only the parts of the wrapper read and write. -/
def withMemory {Ia L R : Type} (W : Adversary C E Ia L R) (M : Type) (m0 : M) : Adversary C E Ia L R where
  State := W.State × M
  start x z := (fun s => (s, m0)) <$> W.start x z
  round s m := (fun r => ((r.1, s.2), r.2)) <$> W.round s.1 m
  answer s l := (fun r => ((r.1, s.2), r.2)) <$> W.answer s.1 l

end Wrapper

section Check

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The check of the tuples `x i` from the state of a batch at its check. -/
def checkAt (K : Constants C E) (L tg : ℕ) (x : C.Party → List (Tuple C)) (i : C.Party) :
    PartyM C E (CheckSpec C E) Unit :=
  (check K (localContext i) (hybridCheckBuildingBlocks K i) (x i)).run' ⟨filledHistory K i (x i), L, tg⟩

/-- The labels of one check, an upper bound. -/
def checkLabels (n : ℕ) : ℕ := 2 * halvings n + 5

/-- The tables of the drawn values of one check. Each draw over `E` has two positions, and the one draw
over bits has 256 (`check`). -/
structure DrawTables (C : Committee) (E : Type) (m : ℕ) where
  freshE : Fin m → C.Term → Fin 2 → E
  freshPairE : Fin m → C.Pair → Fin 2 → E
  freshB : C.Term → Fin 256 → Bit
  freshPairB : C.Pair → Fin 256 → Bit

/-- The drawn PRSS output over `E` of operator `i` at position `k` of the check, as `frandShare`. -/
def drawnE {m : ℕ} (D : C.Coalition) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (tables : DrawTables C E m) (k : ℕ) (i : C.Party) : PrssOutput C E :=
  if h : k < m then frandShare D 2 (knownE k).1 (knownE k).2 (tables.freshE ⟨k, h⟩) (tables.freshPairE ⟨k, h⟩) i
  else (fun _ _ => 0, fun _ _ => 0)

/-- The building blocks of the real check, `realCheckBuildingBlocks`, with each PRSS output a drawn
value. A draw is local, so a live operator after a partial start still sends its next round. -/
def drawnCheckBuildingBlocks {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : DrawTables C E m) (i : C.Party) :
    CheckBuildingBlocks C E RealSpec where
  coin count := do
    let ρ ← freshLabel
    coinWith K (localContext i) (drawnE D knownE tables (ρ - L) i) count
  extendMult products := do
    let ρ ← freshLabel
    reshare K (localContext i) (elementCodec K) (drawnE D knownE tables (ρ - L) i)
      (fun g => match products[g]? with | some p => productShare K (localContext i) p | none => 0)
      products.length
  randElements _ := do
    let ρ ← freshLabel
    pure (drawnE D knownE tables (ρ - L) i)
  randBits _ := do
    let _ ← freshLabel
    pure (frandShare D 256 knownB.1 knownB.2 tables.freshB tables.freshPairB i)

/-- The real check on drawn values. -/
def drawnCheckAt {m : ℕ} (K : Constants C E) (D : C.Coalition) (L tg : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : DrawTables C E m)
    (x : C.Party → List (Tuple C)) (i : C.Party) : PartyM C E RealSpec Unit :=
  (check K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB tables i) (x i)).run'
    ⟨filledHistory K i (x i), L, tg⟩

/-- The tables of one check, drawn uniformly. -/
def drawTables (m : ℕ) : OracleComp (LocalSpec C) (DrawTables C E m) := do
  let freshE ← liftComp ($ᵗ (Fin m → C.Term → Fin 2 → E)) (LocalSpec C)
  let freshPairE ← liftComp ($ᵗ (Fin m → C.Pair → Fin 2 → E)) (LocalSpec C)
  let freshB ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
  let freshPairB ← liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C)
  pure ⟨freshE, freshPairE, freshB, freshPairB⟩

/-- The histories of the known terms at the honest operators. The digest tail needs them for the known
columns (`digestTail`). In a batch they follow from the replies of the wrapper to the
calls before the check. -/
def knownHist (K : Constants C E) (D : C.Coalition) (x : C.Party → List (Tuple C)) : C.Party → C.Term → List Bit :=
  fun i T => if i ∉ D.1 ∧ KnownTo D.1 T then filledHistory K i (x i) T else []

/-- The error of the step from the real check on drawn values to the check under the wrapper. -/
def c1Error (C : Committee) (step q seen n : ℕ) : ℝ :=
  ((C.terms.length * (seen + 4 * checkRounds n * step + q + (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256

end Check

end ThresholdLeanXmssSecurity.RealNetworkV3

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkE1r
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The library `relabel` preserves the start and every round of the real
adversary. The input of a real functionality is empty. No reply is used. -/
def checkAdversary {Ia L R : Type} (A : Adversary C E Ia L R) :
    Adversary C E Ia PEmpty PEmpty :=
  RealNetworkV3.relabel A PEmpty.elim

end ThresholdLeanXmssSecurity.RealNetworkE1r

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkRC

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- The wrapper runs `oa` and its tail `T`. The live operators then run `oa` again and
continue with `rest`. This is the run where only the live operators run `oa`, before the tail. -/
theorem sameRun_repeat (prims : Primitives) {γ σ δ : Type} (oa : OracleComp (RoSpec C) γ)
    (T : γ → OracleComp (LocalSpec C) σ) (rest : γ → σ → OracleComp (LocalSpec C) δ) :
    SameRun prims
      (do
        let c ← liftComp oa (LocalSpec C)
        let s ← T c
        let c' ← liftComp oa (LocalSpec C)
        rest c' s)
      (do
        let c ← liftComp oa (LocalSpec C)
        let s ← T c
        rest c s) := by
  refine (SameRun.bind_right _ fun c =>
    sameRun_swap prims (T c) (liftComp oa (LocalSpec C)) fun s c' => rest c' s).trans ?_
  exact sameRun_ro_dup prims oa fun c c' => T c >>= fun s => rest c' s

variable [Field E] [Algebra Bit E]

/-- The search of the wrapper makes no digest call. -/
lemma wrapperChallenge_no_digest [Fintype E] [DecidableEq E] [SampleableType E] (K : Constants C E) (tag label : ℕ) (values : List E) :
    IsQueryBoundP (liftComp (challengeQuery K tag label values) (LocalSpec C)) DigestQuery 0 := by
  simp only [challengeQuery, liftComp_bind]
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (hashQuery_no_digest _ (by simp only [DigestQuery, digestSaltProjection, Option.isSome_none,
      Bool.false_eq_true, not_false_eq_true]))
    fun key _ => findChallenge_no_digest K key challengeTries 0

end ThresholdLeanXmssSecurity.RealNetworkRC

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkRC

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- The honest operators with an input. -/
def liveSet {β : Type} (D : C.Coalition) (out : C.Party → Option β) : Finset C.Party :=
  Finset.univ.filter fun i => i ∉ D.1 ∧ (out i).isSome

/-- A partial abort. -/
def PartialOut {β : Type} (D : C.Coalition) (out : C.Party → Option β) : Prop :=
  (∃ i ∉ D.1, out i = none) ∧ ∃ i ∉ D.1, (out i).isSome

/-! ## A phase after a partial abort that starts with a round -/

section PartialRound

variable {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

/-- The run after a partial abort, with a round first. -/
theorem executeRounds_partialRound (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (hD : ∀ i ∈ D.1, steps i = .done none)
    (h : ∀ i ∉ D.1, steps i = .done none ∨ ∃ outbox resume, steps i = .wait outbox resume ∧
      ∀ inbox : Mail C E, (∃ k, inbox k = some .abort) → advance (resume inbox) = pure (.done none))
    (hab : ∃ i ∉ D.1, steps i = .done none) :
    executeRounds localRoles D A F (fuel + 1) st steps =
      if ∀ i ∉ D.1, (steps i).isDone then pure (st, fun _ => none) else
        A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) >>= fun r =>
          pure (r.1, fun _ => none) := by
  by_cases hdone : ∀ i ∉ D.1, (steps i).isDone
  · rw [executeRounds, ite_eq_left hdone, ite_eq_left hdone]
    congr 2
    funext i
    by_cases hi : i ∈ D.1
    · simp only [Step.output, hD i hi]
    · rcases h i hi with h' | ⟨outbox, resume, h', -⟩
      · simp only [Step.output, h']
      · have := hdone i hi
        rw [h'] at this
        exact this.elim
  · rw [executeRounds, ite_eq_right hdone, ite_eq_right hdone]
    obtain ⟨i₀, hi₀, hdone₀⟩ := hab
    have hnocall : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
        ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := by
      rintro ⟨⟨i, hi, hc⟩, -⟩
      rcases h i hi with h' | ⟨outbox, resume, h', -⟩ <;> simp only [Step.callInput, h', Option.isSome_none, Bool.false_eq_true] at hc
    unfold stepRound
    rw [ite_eq_right hnocall]
    simp only [localRoles, bind_assoc]
    refine bind_congr fun r => ?_
    rw [stages_sequenceFin_eq_pure _ (fun _ => Step.done none) (fun j => ?_), pure_bind, pure_bind]
    · exact stages_executeRounds_done D A F fuel r.1 _ fun _ => rfl
    by_cases hj : j ∈ D.1
    · simp only [hD j hj]
    · rcases h j hj with h' | ⟨outbox, resume, h', hres⟩
      · simp only [h']
      · simp only [h', hj, ite_false]
        exact hres _ ⟨i₀, by simp only [hi₀, ↓reduceIte, hdone₀, delivered_done_none]⟩

/-- The run of a phase after a partial abort, whose live programs start with a round. A program of a live
operator is `prog i v`, which sends `out i v` and then rejects an abort frame. -/
theorem roundPhase_partial {β V : Type} (prog : C.Party → V → PartyM C E (CallSpec I O) β)
    (out : C.Party → V → Mail C E) (cont : C.Party → V → Mail C E → PartyM C E (CallSpec I O) β)
    (hadv : ∀ i v, advance (prog i v).run = pure (.wait (out i v) (exchangeResume (cont i v))))
    (fuel : ℕ) (st : A.State) (inputs : C.Party → Option V) (hp : PartialOut D inputs) :
    executePhase localRoles D A F (fuel + 1) st (fun i => (inputs i).elim failure (prog i)) =
      A.round st (fun c i => if c ∈ D.1 ∧ i ∈ liveSet D inputs then
        (inputs i).elim none fun v => out i v c else none) >>= fun r => pure (r.1, fun _ => none) := by
  let step : C.Party → Step C E (CallSpec I O) β := fun i =>
    if i ∈ D.1 then .done none else
      match inputs i with
      | none => .done none
      | some v => .wait (out i v) (exchangeResume (cont i v))
  have hstart : startSteps localRoles D (fun i => (inputs i).elim failure (prog i)) = pure step := by
    unfold startSteps
    refine stages_sequenceFin_eq_pure _ _ fun i => ?_
    by_cases hi : i ∈ D.1
    · simp only [step, hi, ↓reduceIte]
    · simp only [step, hi, ↓reduceIte, localRoles]
      cases hx : inputs i with
      | none => exact advance_run_failure
      | some v => exact hadv i v
  unfold executePhase
  rw [hstart, pure_bind]
  obtain ⟨⟨i₀, hi₀, hnone⟩, i₁, hi₁, hsome⟩ := hp
  rw [executeRounds_partialRound D A F fuel st step
    (fun i hi => by simp only [step, hi, ↓reduceIte])
    (fun i hi => by
      simp only [step, hi, ↓reduceIte]
      cases inputs i with
      | none => exact Or.inl rfl
      | some v =>
        refine Or.inr ⟨_, _, rfl, fun inbox ⟨k, hk⟩ => ?_⟩
        have hany : (C.parties.any fun j => Msg.isAbort (inbox j)) = true :=
          List.any_eq_true.2 ⟨k, List.mem_finRange k, by simp only [Msg.isAbort, hk]⟩
        simp only [exchangeResume, hany, ite_true, advance_pure])
    ⟨i₀, hi₀, by simp only [step, hi₀, ↓reduceIte, hnone]⟩]
  have hnot : ¬ ∀ i ∉ D.1, (step i).isDone := fun hall => by
    have h := hall i₁ hi₁
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
    simp only [step, hi₁, ↓reduceIte, hv] at h
    exact h
  rw [ite_eq_right hnot]
  congr 2
  funext c i
  unfold liveSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hc : c ∈ D.1
  · by_cases hi : i ∈ D.1
    · simp only [hc, hi, not_true_eq_false, and_false, ↓reduceIte, false_and]
    · cases hx : inputs i with
      | none => simp only [hc, hi, not_false_eq_true, and_self, ↓reduceIte, Step.outbox, hx, Option.isSome_none, Bool.false_eq_true, and_false, step]
      | some v => simp only [hc, hi, not_false_eq_true, and_self, ↓reduceIte, Step.outbox, hx, Option.isSome_some, Option.elim_some, step]
  · simp only [hc, false_and, ↓reduceIte]

end PartialRound

/-! ## The digest round in columns -/

section Columns

/-- The digest of term `T` at operator `i`. Only a live holder computes it. -/
def liveCol (live : C.Party → Prop) (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (T : C.Term) (i : C.Party) : OracleComp (LocalSpec C) HashOutput :=
  if live i ∧ i ∈ C.holders T then
    liftComp (oneDigestQuery (C := C) (vector 256 (salts i T)) (hist i T)) (LocalSpec C)
  else pure 0

lemma lift_row_live (live : C.Party → Prop) (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (i : C.Party) (hi : live i) (ts : List C.Term) :
    liftComp (ts.mapM fun T => if i ∈ C.holders T then
      oneDigestQuery (C := C) (vector 256 (salts i T)) (hist i T) else pure 0) (LocalSpec C) =
      ts.mapM (fun T => liveCol live salts hist T i) := by
  induction ts with
  | nil => simp only [List.mapM_nil, liftComp_pure]
  | cons T ts ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, ih]
    have hh : liftComp (if i ∈ C.holders T then
        oneDigestQuery (C := C) (vector 256 (salts i T)) (hist i T) else pure 0) (LocalSpec C) =
        liveCol live salts hist T i := by
      by_cases ht : i ∈ C.holders T
      · simp only [liveCol, ht, hi, and_self, ↓reduceIte]
      · simp only [liveCol, ht, and_false, ↓reduceIte, liftComp_pure]
    rw [hh]

lemma row_not_live (live : C.Party → Prop) (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (i : C.Party) (hi : ¬ live i) :
    C.terms.mapM (fun T => liveCol live salts hist T i) = pure (C.terms.map fun _ => (0 : HashOutput)) := by
  have hc : (fun T => liveCol live salts hist T i) = fun _ => pure 0 := by
    funext T
    simp only [liveCol, hi, false_and, ↓reduceIte]
  rw [hc, List.mapM_pure]

/-- The columns of a list of terms. -/
def colsRun (col : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) :
    List C.Term → OracleComp (LocalSpec C) (List (DigestColumn C))
  | [] => pure []
  | T :: Ts => do
    let c ← col T
    let cs ← colsRun col Ts
    pure (c :: cs)

lemma queryColumns_colsRun (f : C.Party → C.Term → OracleComp (LocalSpec C) HashOutput) (Ts : List C.Term) :
    queryColumns f Ts =
      colsRun (fun T => OverPermutation.sequenceFin fun i => f i T) Ts >>= fun cs => pure (digestRows cs) := by
  induction Ts with
  | nil => simp only [queryColumns, colsRun, pure_bind]; rfl
  | cons T Ts ih =>
    simp only [queryColumns, colsRun, ih, bind_assoc, pure_bind]
    rfl

lemma colsRun_sameRun (prims : Primitives) (col col' : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (Ts : List C.Term) (h : ∀ T ∈ Ts, SameRun prims (col T) (col' T)) :
    SameRun prims (colsRun col Ts) (colsRun col' Ts) := by
  induction Ts with
  | nil => exact SameRun.refl prims _
  | cons T Ts ih =>
    exact (h T List.mem_cons_self).bind fun c =>
      (ih fun U hU => h U (List.mem_cons_of_mem T hU)).bind fun cs => SameRun.refl prims _

/-- The columns of a list `Ts` from the columns of the terms with `P`, with zero elsewhere. -/
def liveCols (P : C.Term → Prop) : List C.Term → List (DigestColumn C) → List (DigestColumn C)
  | [], _ => []
  | T :: Ts, cs => if P T then cs.headD (fun _ => 0) :: liveCols P Ts cs.tail else (fun _ => 0) :: liveCols P Ts cs

lemma colsRun_filter {β : Type} (P : C.Term → Prop) (col : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hz : ∀ T, ¬ P T → col T = pure fun _ => 0) (Ts : List C.Term)
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) β) :
    (colsRun col Ts >>= k) = (colsRun col (Ts.filter fun T => decide (P T)) >>= fun cs => k (liveCols P Ts cs)) := by
  induction Ts generalizing k with
  | nil => simp only [colsRun, pure_bind, List.filter_nil, liveCols]
  | cons T Ts ih =>
    by_cases hT : P T
    · simp only [colsRun, List.filter_cons, hT, decide_true, ↓reduceIte, bind_assoc, pure_bind, liveCols,
        List.headD_cons, List.tail_cons]
      refine bind_congr fun c => ?_
      exact ih fun cs => k (c :: cs)
    · simp only [colsRun, List.filter_cons, hT, decide_false, Bool.false_eq_true, ↓reduceIte, hz T hT,
        bind_assoc, pure_bind, liveCols]
      exact ih fun cs => k ((fun _ => 0) :: cs)

/-- A column at the live operators only. -/
def maskCol (live : C.Party → Prop) (c : DigestColumn C) : DigestColumn C := fun i => if live i then c i else 0

lemma maskCol_maskCol (live : C.Party → Prop) (c : DigestColumn C) :
    maskCol live (maskCol live c) = maskCol live c := by
  funext i
  by_cases hi : live i <;> simp only [maskCol, hi, ↓reduceIte]

lemma colsRun_mixed {β : Type} (D : C.Coalition) (live : C.Party → Prop)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) (hist : C.Term → List Bit)
    (table : C.Term → Fin 256 → Bit) (col : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (Ts : List C.Term)
    (hcol : ∀ T ∈ Ts, col T = if KnownTo D.1 T then known T else
      liftComp (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) (LocalSpec C) >>= fun d =>
        pure (maskCol live (digestColumnValues D T d)))
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) β) :
    (colsRun col Ts >>= fun cs => k (cs.map (maskCol live))) =
      mixedTableDigests D known hist table Ts (fun cs => k (cs.map (maskCol live))) := by
  induction Ts generalizing k with
  | nil => simp only [colsRun, pure_bind, List.map_nil, mixedTableDigests]
  | cons T Ts ih =>
    have hT := hcol T List.mem_cons_self
    have ih' := fun k' => ih (fun U hU => hcol U (List.mem_cons_of_mem T hU)) k'
    simp only [colsRun, bind_assoc, pure_bind, List.map_cons, mixedTableDigests]
    by_cases hk : KnownTo D.1 T
    · simp only [hT, hk, ↓reduceIte]
      refine bind_congr fun c => ?_
      exact ih' fun cs => k (maskCol live c :: cs)
    · simp only [hT, hk, ↓reduceIte, bind_assoc, pure_bind, maskCol_maskCol]
      refine bind_congr fun d => ?_
      exact ih' fun cs => k (maskCol live (digestColumnValues D T d) :: cs)

lemma mixedGhostDigests_bind {α β : Type} (D : C.Coalition)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) (Ts : List C.Term)
    (k : List (DigestColumn C) → OracleComp (LocalSpec C) α) (tail : α → OracleComp (LocalSpec C) β) :
    (mixedGhostDigests D known Ts k >>= tail) = mixedGhostDigests D known Ts (fun cs => k cs >>= tail) := by
  induction Ts generalizing k with
  | nil => rfl
  | cons T Ts ih =>
    simp only [mixedGhostDigests]
    by_cases hT : KnownTo D.1 T <;> simp only [hT, ↓reduceIte, bind_assoc]
    all_goals exact bind_congr fun c => ih _

end Columns

/-! ## The real phase and the tail -/

section Phase

/-- `compareDigests_run'` for any functionality. -/
theorem compareDigests_run'_any {I O α : Type} (i : C.Party) (salts : Shares C Bit)
    (f : Unit → RunM C E (CallSpec I O) α) (st : RunState C) :
    (compareDigests (localContext i) salts >>= f).run' st =
      oracleStep (digestQuery i salts st.history) >>= fun ds =>
        exchange (digestOutbox (E := E) i ds) >>= fun inbox =>
          require (DigestsAgree (E := E) i ds inbox) >>= fun _ => (f ()).run' st := by
  simp only [compareDigests, bind_assoc]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind, map_bind]
  rfl

/-- The histories of the live operators. -/
def histOf (inputs : C.Party → Option (RunState C)) : C.Party → C.Term → List Bit :=
  fun i => ((inputs i).map RunState.history).getD fun _ => []

/-- The digest round on the real network from the states `inputs` of the live operators, with the salts
`salts` and the continuation `f`. -/
def realDigestPhase {I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (salts : C.Party → Shares C Bit)
    (inputs : C.Party → Option (RunState C)) (f : C.Party → Unit → RunM C E (CallSpec I O) α) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option α)) :=
  executePhase localRoles D A F fuel st fun i =>
    (inputs i).elim failure fun hs => (compareDigests (localContext i) (salts i) >>= f i).run' hs

/-- The program of a live operator after its digests `ds`. -/
def digestAfter {I O α : Type} (inputs : C.Party → Option (RunState C))
    (f : C.Party → Unit → RunM C E (CallSpec I O) α) (i : C.Party) (ds : List HashOutput) :
    PartyM C E (CallSpec I O) α :=
  (inputs i).elim failure fun hs => exchange (digestOutbox (E := E) i ds) >>= fun inbox =>
    require (DigestsAgree (E := E) i ds inbox) >>= fun _ => (f i ()).run' hs

/-- The digest messages of the live operators `live` to the coalition. -/
def digestMsgs (D : C.Coalition) (live : Finset C.Party) (rows : C.Party → List HashOutput) :
    C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∈ live then digestOutbox i (rows i) c else none

lemma mem_liveSet {β : Type} (D : C.Coalition) (out : C.Party → Option β) (i : C.Party) :
    i ∈ liveSet D out ↔ i ∉ D.1 ∧ (out i).isSome := by
  simp only [liveSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The real digest round after a partial abort. The live operators compute their digest rows, the
adversary gets one step on their messages, and every operator aborts. -/
theorem realDigestPhase_partial (prims : Primitives) {I O L R Ia α : Type} (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (salts : C.Party → Shares C Bit) (inputs : C.Party → Option (RunState C)) (hp : PartialOut D inputs)
    (f : C.Party → Unit → RunM C E (CallSpec I O) α) :
    SameRun prims (realDigestPhase D A F (fuel + 1) st salts inputs f)
      (do
        let v ← OverPermutation.sequenceFin fun i =>
          C.terms.mapM fun T => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i
        let r ← A.round st (digestMsgs D (liveSet D inputs) v)
        pure (r.1, fun _ => none)) := by
  have hprog : ∀ i ∉ D.1,
      ((inputs i).elim failure fun hs => (compareDigests (localContext i) (salts i) >>= f i).run' hs) =
        localStep (C.terms.mapM fun T => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i) >>=
          digestAfter inputs f i := by
    intro i hi
    cases hx : inputs i with
    | none =>
      have hl : i ∉ liveSet D inputs := by
        simp only [mem_liveSet, hx, Option.isSome_none, Bool.false_eq_true, and_false, not_false_eq_true]
      rw [row_not_live _ salts _ i hl]
      simp only [Option.elim_none, localStep, liftComp_pure, OptionT.lift_pure, pure_bind, digestAfter, hx]
    | some hs =>
      have hl : i ∈ liveSet D inputs := by
        simp only [mem_liveSet, hx, Option.isSome_some, and_true]
        exact hi
      have hh : histOf inputs i = hs.history := by
        simp only [histOf, hx, Option.map_some, Option.getD_some]
      rw [Option.elim_some, compareDigests_run'_any, ← lift_row_live _ salts _ i hl C.terms, hh]
      unfold digestAfter
      simp only [hx, Option.elim_some]
      rfl
  unfold realDigestPhase
  rw [executePhase_congr_honest D A F (fuel + 1) st _ _ hprog]
  refine (executePhase_local_fallback prims D A F (fuel + 1) st _ (fun _ => C.terms.map fun _ => 0)
    (digestAfter inputs f)).trans ?_
  have hseq : (fun i => if i ∈ D.1 then pure (C.terms.map fun _ => (0 : HashOutput)) else
      C.terms.mapM fun T => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i) =
      fun i => C.terms.mapM fun T => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i := by
    funext i
    by_cases hi : i ∈ D.1
    · have hl : i ∉ liveSet D inputs := fun h => ((mem_liveSet D inputs i).1 h).1 hi
      simp only [hi, ↓reduceIte, row_not_live _ salts _ i hl]
    · simp only [hi, ↓reduceIte]
  rw [hseq]
  refine SameRun.bind_right _ fun v => SameRun.of_eq ?_
  change executePhase localRoles D A F (fuel + 1) st (fun i => (inputs i).elim failure fun hs =>
    exchange (digestOutbox (E := E) i (v i)) >>= fun inbox =>
      require (DigestsAgree (E := E) i (v i) inbox) >>= fun _ => (f i ()).run' hs) = _
  rw [roundPhase_partial D A F
    (fun i hs => exchange (digestOutbox (E := E) i (v i)) >>= fun inbox =>
      require (DigestsAgree (E := E) i (v i) inbox) >>= fun _ => (f i ()).run' hs)
    (fun i _ => digestOutbox i (v i))
    (fun i hs inbox => require (DigestsAgree (E := E) i (v i) inbox) >>= fun _ => (f i ()).run' hs)
    (fun i hs => advance_exchange_bind _ _) fuel st inputs hp]
  congr 2
  funext c i
  unfold digestMsgs
  by_cases h : c ∈ D.1 ∧ i ∈ liveSet D inputs
  · obtain ⟨hs, hx⟩ := Option.isSome_iff_exists.1 ((mem_liveSet D inputs i).1 h.2).2
    simp only [h, and_self, ↓reduceIte, hx, Option.elim_some]
  · simp only [h, ↓reduceIte]

/-- A term whose column the tail gives. The coalition knows it, or a live operator holds it. -/
def Present (D : C.Coalition) (live : Finset C.Party) (T : C.Term) : Prop :=
  KnownTo D.1 T ∨ ∃ i ∈ live, i ∈ C.holders T

/-- The column of term `T` in the form of `mixedTableDigests`. -/
def colFull (D : C.Coalition) (live : Finset C.Party) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hist : C.Term → List Bit) (table : C.Term → Fin 256 → Bit) (T : C.Term) :
    OracleComp (LocalSpec C) (DigestColumn C) :=
  if KnownTo D.1 T then known T
  else if ∃ i ∈ live, i ∈ C.holders T then
    liftComp (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) (LocalSpec C) >>= fun d =>
      pure (maskCol (· ∈ live) (digestColumnValues D T d))
  else pure fun _ => 0

/-- The live holders of a hidden term make one pair of hash calls. A hidden term with no live holder
makes none. -/
theorem liveCol_sameRun (prims : Primitives) (D : C.Coalition) (inputs : C.Party → Option (RunState C))
    (salts : C.Party → Shares C Bit) (table : C.Term → Fin 256 → Bit) (hist : C.Term → List Bit)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hsalt : ∀ T, ¬ KnownTo D.1 T → ∀ i ∉ D.1, i ∈ C.holders T → vector 256 (salts i T) = List.ofFn (table T))
    (hhist : ∀ T, ¬ KnownTo D.1 T → ∀ i ∉ D.1, ∀ hs, i ∈ C.holders T → inputs i = some hs → hs.history T = hist T)
    (hknown : ∀ T, KnownTo D.1 T →
      OverPermutation.sequenceFin (fun i => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i) = known T)
    (T : C.Term) :
    SameRun prims (OverPermutation.sequenceFin fun i => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i)
      (colFull D (liveSet D inputs) known hist table T) := by
  by_cases hk : KnownTo D.1 T
  · rw [colFull, ite_eq_left hk, hknown T hk]
    exact SameRun.refl prims _
  by_cases he : ∃ i ∈ liveSet D inputs, i ∈ C.holders T
  · have hc : (fun i => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i) = fun i =>
        if i ∈ liveSet D inputs ∧ i ∈ C.holders T then
          liftComp (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) (LocalSpec C) else pure 0 := by
      funext i
      unfold liveCol
      by_cases h : i ∈ liveSet D inputs ∧ i ∈ C.holders T
      · obtain ⟨hi, hsome⟩ := (mem_liveSet D inputs i).1 h.1
        obtain ⟨hs, hx⟩ := Option.isSome_iff_exists.1 hsome
        simp only [h, and_self, ↓reduceIte, hsalt T hk i hi h.2, histOf, hx, Option.map_some,
          Option.getD_some, hhist T hk i hi hs h.2 hx]
      · simp only [h, ↓reduceIte]
    rw [hc]
    obtain ⟨i₀, hi₀, ht₀⟩ := he
    refine (SameRun.of_eq ?_).trans ((sameRun_sequenceFin_selected prims (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) 0
      (fun i => i ∈ liveSet D inputs ∧ i ∈ C.holders T) ⟨i₀, hi₀, ht₀⟩).trans (SameRun.of_eq ?_))
    · refine congrArg OverPermutation.sequenceFin (funext fun i => ?_)
      by_cases h : i ∈ liveSet D inputs ∧ i ∈ C.holders T <;> simp only [h, ↓reduceIte]
    rw [colFull, ite_eq_right hk, ite_eq_left ⟨i₀, hi₀, ht₀⟩]
    refine bind_congr fun d => ?_
    congr 1
    funext i
    unfold maskCol digestColumnValues
    by_cases hl : i ∈ liveSet D inputs
    · have hi := ((mem_liveSet D inputs i).1 hl).1
      by_cases ht : i ∈ C.holders T <;> simp only [hl, ht, hi, and_self, and_false, not_false_eq_true,
        ↓reduceIte]
    · simp only [hl, false_and, ↓reduceIte]
  · have hc : (fun i => liveCol (· ∈ liveSet D inputs) salts (histOf inputs) T i) = fun _ => pure 0 := by
      funext i
      unfold liveCol
      have h : ¬ (i ∈ liveSet D inputs ∧ i ∈ C.holders T) := fun h => he ⟨i, h.1, h.2⟩
      simp only [h, ↓reduceIte]
    rw [hc, sequenceFin_pure, colFull, ite_eq_right hk, ite_eq_right he]
    exact SameRun.refl prims _

lemma digestRows_liveCols_mask (P : C.Term → Prop) (live : Finset C.Party) (i : C.Party) (hi : i ∈ live) :
    ∀ (Ts : List C.Term) (cs : List (DigestColumn C)),
      digestRows (liveCols P Ts (cs.map (maskCol (· ∈ live)))) i = digestRows (liveCols P Ts cs) i
  | [], _ => rfl
  | T :: Ts, cs => by
    by_cases hT : P T
    · cases cs with
      | nil =>
        simp only [liveCols, hT, ↓reduceIte, List.map_nil, digestRows, List.map_cons]
      | cons c cs =>
        have ih := digestRows_liveCols_mask P live i hi Ts cs
        simp only [digestRows] at ih
        simp only [liveCols, hT, ↓reduceIte, List.map_cons, List.headD_cons, List.tail_cons, digestRows,
          maskCol, hi, ih]
    · have ih := digestRows_liveCols_mask P live i hi Ts cs
      simp only [digestRows] at ih
      simp only [liveCols, hT, ↓reduceIte, digestRows, List.map_cons, ih]

lemma digestMsgs_mask (D : C.Coalition) (P : C.Term → Prop) (live : Finset C.Party) (cs : List (DigestColumn C)) :
    digestMsgs (E := E) D live (digestRows (liveCols P C.terms (cs.map (maskCol (· ∈ live))))) =
      digestMsgs D live (digestRows (liveCols P C.terms cs)) := by
  funext c i
  unfold digestMsgs
  by_cases h : c ∈ D.1 ∧ i ∈ live
  · simp only [h, and_self, ↓reduceIte, digestRows_liveCols_mask P live i h.2]
  · simp only [h, ↓reduceIte]

/-- The tail of the digest round in the wrapper. For each hidden term with a live holder it samples one
fresh digest. It runs the known columns `known`, and it gives the adversary the messages of the live
operators `live`. -/
def digestTail {Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (live : Finset C.Party)
    (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C)) (st : A.State) :
    OracleComp (LocalSpec C) A.State :=
  mixedGhostDigests D known (C.terms.filter fun T => decide (Present D live T)) fun cs => do
    let r ← A.round st (digestMsgs D live (digestRows (liveCols (Present D live) C.terms
      (cs.map (maskCol (· ∈ live))))))
    pure r.1

/-- The digest round after a partial abort is the tail of the wrapper up to the event that a
digest call hits a fresh salt. The bound holds for every continuation `tail` with at most `q` digest
calls, and for every cache whose digest salts are in `seen`. -/
theorem realDigestPhase_partial_hide (prims : Primitives) {I O L R Ia α β : Type} (D : C.Coalition)
    (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ) (st : A.State)
    (salts : (C.Term → Fin 256 → Bit) → C.Party → Shares C Bit)
    (inputs : C.Party → Option (RunState C)) (hp : PartialOut D inputs)
    (f : C.Party → Unit → RunM C E (CallSpec I O) α)
    (hist : C.Term → List Bit) (known : C.Term → OracleComp (LocalSpec C) (DigestColumn C))
    (hsalt : ∀ table T, ¬ KnownTo D.1 T → ∀ i ∉ D.1, i ∈ C.holders T →
      vector 256 (salts table i T) = List.ofFn (table T))
    (hhist : ∀ T, ¬ KnownTo D.1 T → ∀ i ∉ D.1, ∀ hs, i ∈ C.holders T → inputs i = some hs →
      hs.history T = hist T)
    (hknown : ∀ table T, KnownTo D.1 T → OverPermutation.sequenceFin
      (fun i => liveCol (· ∈ liveSet D inputs) (salts table) (histOf inputs) T i) = known T)
    (p : ℕ) (hbound : ∀ T, KnownTo D.1 T → IsQueryBoundP (known T) DigestQuery p)
    (step : ℕ) (hr : ∀ st sent, IsQueryBoundP (A.round st sent) DigestQuery step)
    (tail : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β)
    (q : ℕ) (hq : ∀ st', IsQueryBoundP (tail (st', fun _ => none)) DigestQuery q)
    (cache : HashCache C) (seen : Finset (List Bit)) (hc : DigestSaltsCovered cache seen) :
    letI : MeasurableSpace β := ⊤
    measureTVDist ((simulateQ (localAnswer prims) (do
        let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
        let out ← realDigestPhase D A F (fuel + 1) st (salts table) inputs f
        tail out)).run' cache)
      ((simulateQ (localAnswer prims) (do
        let st' ← digestTail D A (liveSet D inputs) known st
        tail (st', fun _ => none))).run' cache) ≤
      ((C.terms.length * (seen.card + (step + q) + (p + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256 := by
  let : MeasurableSpace β := ⊤
  let Ts := C.terms.filter fun T => decide (Present D (liveSet D inputs) T)
  let k : List (DigestColumn C) → OracleComp (LocalSpec C) β := fun cs => do
    let r ← A.round st (digestMsgs D (liveSet D inputs) (digestRows (liveCols (Present D (liveSet D inputs))
      C.terms cs)))
    tail (r.1, fun _ => none)
  have hz : ∀ table T, ¬ Present D (liveSet D inputs) T →
      colFull D (liveSet D inputs) known hist table T = pure fun _ => 0 := by
    intro table T hT
    rw [colFull, ite_eq_right fun h => hT (Or.inl h), ite_eq_right fun h => hT (Or.inr h)]
  have hcol : ∀ table, ∀ T ∈ Ts, colFull D (liveSet D inputs) known hist table T =
      if KnownTo D.1 T then known T else
        liftComp (oneDigestQuery (C := C) (List.ofFn (table T)) (hist T)) (LocalSpec C) >>= fun d =>
          pure (maskCol (· ∈ liveSet D inputs) (digestColumnValues D T d)) := by
    intro table T hT
    have hP : Present D (liveSet D inputs) T := of_decide_eq_true (List.mem_filter.1 hT).2
    by_cases hk : KnownTo D.1 T
    · rw [colFull, ite_eq_left hk, ite_eq_left hk]
    · rw [colFull, ite_eq_right hk, ite_eq_right hk, ite_eq_left (hP.resolve_left hk)]
  have hsame : ∀ table, SameRun prims
      (do
        let out ← realDigestPhase D A F (fuel + 1) st (salts table) inputs f
        tail out)
      (mixedTableDigests D known hist table Ts fun cs => k (cs.map (maskCol (· ∈ liveSet D inputs)))) := by
    intro table
    refine ((realDigestPhase_partial prims D A F fuel st (salts table) inputs hp f).bind
      fun out => SameRun.refl prims (tail out)).trans ?_
    simp only [bind_assoc, pure_bind]
    refine ((sameRun_queryColumns prims (fun i T => liveCol (· ∈ liveSet D inputs) (salts table)
      (histOf inputs) T i) C.terms).bind fun v => SameRun.refl prims _).trans ?_
    rw [queryColumns_colsRun, bind_assoc]
    simp only [pure_bind]
    refine ((colsRun_sameRun prims _ (colFull D (liveSet D inputs) known hist table) C.terms
      fun T _ => liveCol_sameRun prims D inputs (salts table) table hist known (hsalt table) hhist
        (hknown table) T).bind fun cs => SameRun.refl prims _).trans (SameRun.of_eq ?_)
    rw [colsRun_filter (Present D (liveSet D inputs)) _ (hz table) C.terms,
      ← colsRun_mixed D (· ∈ liveSet D inputs) known hist table _ Ts (hcol table) k]
    refine bind_congr fun cs => ?_
    simp only [k, digestMsgs_mask]
  have he := (SameRun.bind_right (liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)) hsame) cache
  have he' := he.map Prod.fst
  simp only [← StateT.run'_eq] at he'
  rw [measureTVDist, he'.evalDist_eq]
  have hghost : (do
      let st' ← digestTail D A (liveSet D inputs) known st
      tail (st', fun _ => none)) =
      mixedGhostDigests D known Ts fun cs => k (cs.map (maskCol (· ∈ liveSet D inputs))) := by
    rw [digestTail, mixedGhostDigests_bind]
    simp only [bind_assoc, pure_bind, k]
    rfl
  rw [hghost]
  refine (mixedTableDigests_hide prims D known hist p hbound Ts ((Finset.nodup_toList _).filter _) cache seen
    hc _ (step + q) fun cs => isQueryBoundP_bind (hr _ _) fun r _ => hq r.1).trans ?_
  have hlen : Ts.length ≤ C.terms.length := List.length_filter_le _ _
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.mul_le_mul hlen (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) _)

end Phase

end ThresholdLeanXmssSecurity.RealNetworkRC

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1q

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- The phase of one round with all honest operators. Operator `i` sends `out i`, and its output is
`res i` of its inbox. An abort frame in the inbox makes it abort. -/
theorem roundPhase_full {I O L R Ia β : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (prog : C.Party → PartyM C E (CallSpec I O) β) (out : C.Party → Mail C E)
    (res : C.Party → Mail C E → Option β)
    (hprog : ∀ i, i ∉ D.1 → prog i = exchange (out i) >>= fun inbox => OptionT.mk (pure (res i inbox)))
    (fuel : ℕ) (st : A.State) :
    executePhase localRoles D A F (fuel + 1) st prog =
      A.round st (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then out i c else none) >>= fun b =>
        pure (b.1, fun i => if i ∈ D.1 then none else
          let inbox : Mail C E := fun k => if k ∈ D.1 then b.2 k i else out k i
          if anyAbort inbox then none else res i inbox) := by
  obtain ⟨i₀, hi₀⟩ := main_honest_exists D
  let step : C.Party → Step C E (CallSpec I O) β := fun i =>
    if i ∈ D.1 then .done none else .wait (out i) (exchangeResume fun inbox => OptionT.mk (pure (res i inbox)))
  have hstart : startSteps localRoles D prog = pure step := by
    unfold startSteps
    refine stages_sequenceFin_eq_pure _ _ fun i => ?_
    by_cases hi : i ∈ D.1
    · simp only [step, hi, ↓reduceIte]
    · simp only [step, hi, ↓reduceIte, localRoles]
      rw [hprog i hi, advance_exchange_bind]
  unfold executePhase
  rw [hstart, pure_bind, executeRounds,
    ite_eq_right (fun hall => by simpa only [Step.isDone, hi₀, ↓reduceIte, step] using hall i₀ hi₀)]
  unfold stepRound
  rw [ite_eq_right (fun h => by
    obtain ⟨⟨i, hi, hc⟩, -⟩ := h
    simp only [Step.callInput, hi, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, step] at hc)]
  simp only [localRoles, bind_assoc]
  have hm : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (step i).outbox c else none) =
      fun c i => if c ∈ D.1 ∧ i ∉ D.1 then out i c else none := by
    funext c i
    by_cases hc : c ∈ D.1 ∧ i ∉ D.1
    · simp only [hc, and_self, ↓reduceIte, step, not_false_eq_true, Step.outbox]
    · simp only [hc, ↓reduceIte]
  rw [hm]
  refine bind_congr fun b => ?_
  rw [stages_sequenceFin_eq_pure _ (fun j => Step.done (if j ∈ D.1 then none else
      let inbox : Mail C E := fun k => if k ∈ D.1 then b.2 k j else out k j
      if anyAbort inbox then none else res j inbox)) (fun j => ?_), pure_bind, pure_bind]
  · refine (stages_executeRounds_allDone D A F fuel b.1 _ ?_).trans rfl
    exact fun _ => trivial
  · by_cases hj : j ∈ D.1
    · simp only [step, hj, ↓reduceIte]
    · have hin : (fun k => if k ∈ D.1 then b.2 k j else (step k).delivered j) =
          fun k => if k ∈ D.1 then b.2 k j else out k j := by
        funext k
        by_cases hk : k ∈ D.1
        · simp only [hk, ↓reduceIte]
        · simp only [hk, ↓reduceIte, step, Step.delivered]
      simp only [step, hj, ↓reduceIte]
      rw [hin]
      simp only [exchangeResume, anyAbort]
      split_ifs with hab <;> simp only [hab, ↓reduceIte] <;> rfl

end ThresholdLeanXmssSecurity.RealNetworkC1q

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkGP.callPhase_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkGP.callPhase_tail

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkRC.sameRun_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkRC.sameRun_repeat

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkRC.wrapperChallenge_no_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkRC.wrapperChallenge_no_digest

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkRC.realDigestPhase_partial_hide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkRC.realDigestPhase_partial_hide

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1q.roundPhase_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1q.roundPhase_full
