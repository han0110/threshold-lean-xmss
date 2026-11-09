import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-!
# The gadgets

`CoinStatement` and `CoinCompletenessStatement` follow GS20, Lemma 3. `MultStatement` follows GS20,
Lemma 4, in both reshare modes. `ExtendMultStatement` follows GS20, Lemma 5.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
variable {C : Committee} {E : Type}
attribute [local instance] Classical.propDecidable

@[simp] theorem Step.isDone_call {ι : Type} {G : OracleSpec ι} {α : Type} (input : ι) (k) :
    (Step.call (C := C) (E := E) (G := G) (α := α) input k).isDone = False := rfl
@[simp] theorem Step.isDone_wait {ι : Type} {G : OracleSpec ι} {α : Type} (o : Mail C E) (k) :
    (Step.wait (C := C) (E := E) (G := G) (α := α) o k).isDone = False := rfl
@[simp] theorem Step.isDone_done {ι : Type} {G : OracleSpec ι} {α : Type} (o : Option α) :
    (Step.done (C := C) (E := E) (G := G) o).isDone = True := rfl
@[simp] theorem Step.callInput_call {ι : Type} {G : OracleSpec ι} {α : Type} (input : ι) (k) :
    (Step.call (C := C) (E := E) (G := G) (α := α) input k).callInput = some input := rfl
@[simp] theorem Step.callInput_wait {ι : Type} {G : OracleSpec ι} {α : Type} (o : Mail C E) (k) :
    (Step.wait (C := C) (E := E) (G := G) (α := α) o k).callInput = none := rfl
@[simp] theorem Step.callInput_done {ι : Type} {G : OracleSpec ι} {α : Type} (o : Option α) :
    (Step.done (C := C) (E := E) (G := G) o).callInput = none := rfl
@[simp] theorem Step.output_done {ι : Type} {G : OracleSpec ι} {α : Type} (o : Option α) :
    (Step.done (C := C) (E := E) (G := G) o).output = o := rfl
@[simp] theorem Step.outbox_wait {ι : Type} {G : OracleSpec ι} {α : Type} (o : Mail C E) (k) :
    (Step.wait (C := C) (E := E) (G := G) (α := α) o k).outbox = o := rfl
@[simp] theorem Step.delivered_wait {ι : Type} {G : OracleSpec ι} {α : Type} (o : Mail C E) (k) :
    (Step.wait (C := C) (E := E) (G := G) (α := α) o k).delivered = o := rfl
@[simp] theorem Step.outbox_done {ι : Type} {G : OracleSpec ι} {α : Type} (o : Option α) :
    (Step.done (C := C) (E := E) (G := G) o).outbox = fun _ => none := rfl

theorem simulateQ_liftComp_prob {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ t, impl (.inl t) = StateT.lift (free (OracleComp.lift (OracleSpec.query t))))
    (p : ProbComp α) :
    simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R))) = StateT.lift (free (liftComp p (LocalSpec C))) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [free]; rfl
  | query_bind t oa ih =>
    rw [liftComp_bind, liftComp_bind, simulateQ_bind, free_bind]
    simp only [ih]
    rw [show ∀ {α β : Type} (x : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β), (StateT.lift (x >>= f) : StateT σ _ β) = StateT.lift x >>= fun a => StateT.lift (f a) from fun x f => by ext s; simp [StateT.lift]]
    congr 1
    erw [simulateQ_query]
    change (fun x => x) <$> impl (Sum.inl (Sum.inl t)) = _
    rw [id_map', himpl]
    rfl

theorem simulateQ_leak {σ L R : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C)))) (l : L) :
    simulateQ impl (leak (C := C) l) = impl (.inr l) := by
  unfold leak
  erw [simulateQ_query]
  simp

theorem simulateQ_leak_add {σ L R : Type} (f : QueryImpl (LocalSpec C) (StateT σ (OracleComp (WorldSpec C))))
    (g : QueryImpl (L →ₒ R) (StateT σ (OracleComp (WorldSpec C)))) (l : L) :
    simulateQ (f + g) (leak (C := C) l) = g l := by
  rw [simulateQ_leak]; rfl

/-- The outputs of `F_rand`. -/
def frandOut {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin count → R) (freshPair : C.Pair → Fin count → R) :
    C.Party → Option (PrssOutput C R) := fun i =>
  if i ∈ D.1 then none
  else some (fun T => if i ∈ C.holders T then
      (if KnownTo D.1 T then known T else fun g => if h : g < count then fresh T ⟨g, h⟩ else 0) else fun _ => 0,
    fun j => if h : i = j then fun _ => 0 else if j ∈ D.1 then knownPairs j i
      else fun g => if h' : g < count then freshPair (C.pairOf i j h) ⟨g, h'⟩ else 0)

theorem runFunctionality_Frand (R : Type) [AddCommGroup R] [SampleableType R] (D : C.Coalition) {Ia : Type}
    (A : Adversary C E Ia Unit (Shares C R × (C.Party → C.Party → ℕ → R))) (st : A.State)
    (inputs : C.Party → Option ℕ) (h : ∀ i, i ∉ D.1 → (inputs i).isSome) :
    runFunctionality worldRoles D A (Frand R) st inputs = (do
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin (firstInput inputs) → R)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin (firstInput inputs) → R)) (LocalSpec C))
      pure (a.1, frandOut D (firstInput inputs) a.2.1 a.2.2 fresh freshPair)) := by
  unfold runFunctionality
  rw [if_neg (not_not.mpr h)]
  simp only [Frand, sample, simulateQ_bind, simulateQ_leak]
  rw [simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ _), simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ _)]
  simp [worldRoles, StateT.run_bind]
  erw [QueryImpl.add_apply_inr]
  simp only [StateT.run_mk, bind_map_left]
  rfl

theorem bind_congr' {m : Type → Type} [Monad m] {α β : Type} (x : m α) {f g : α → m β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by rw [funext h]

theorem exists_honest (D : C.Coalition) : ∃ i, i ∉ D.1 := by
  by_contra hne
  push Not at hne
  have h1 : (Finset.univ : Finset C.Party) ⊆ D.1 := fun i _ => hne i
  have h2 := Finset.card_le_card h1
  have := D.2; have := C.one_le_t
  simp [Committee.n] at h2; omega

theorem sequenceFin_congr_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} {n : ℕ}
    (g : Fin n → m α) (f : Fin n → α) (h : ∀ i, g i = pure (f i)) : Concrete.sequenceFin g = pure f := by
  rw [show g = fun i => pure (f i) from funext h, sequenceFin_pure]

/-- The PRSS output of `F_rand` at an honest operator. -/
def frandShare {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin count → R) (freshPair : C.Pair → Fin count → R)
    (i : C.Party) : PrssOutput C R :=
  (fun T => if i ∈ C.holders T then
      (if KnownTo D.1 T then known T else fun g => if h : g < count then fresh T ⟨g, h⟩ else 0) else fun _ => 0,
    fun j => if h : i = j then fun _ => 0 else if j ∈ D.1 then knownPairs j i
      else fun g => if h' : g < count then freshPair (C.pairOf i j h) ⟨g, h'⟩ else 0)

theorem frandOut_eq {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin count → R) (freshPair : C.Pair → Fin count → R) :
    frandOut D count known knownPairs fresh freshPair =
      fun i => if i ∈ D.1 then none else some (frandShare D count known knownPairs fresh freshPair i) := rfl

variable {I O R : Type} [AddCommGroup R] [SampleableType R]

/-- One round of the real run when every honest operator waits. -/
theorem executeRounds_wait {Ih Oh Lh Rh α : Type} (D : C.Coalition) (A : Adversary C E I Lh Rh)
    (F : Functionality C Ih Oh Lh Rh) (n : ℕ) (st : A.State) (o : C.Party → Mail C E)
    (k : C.Party → Mail C E → OracleComp (PartySpec C E (CallSpec Ih Oh)) (Option α)) :
    executeRounds worldRoles D A F (n + 1) st (fun j => if j ∈ D.1 then Step.done none else Step.wait (o j) (k j)) =
      (do
        let b ← counted (liftComp (A.round st fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then o i c' else none)
          (SimulatorSpec C))
        let steps ← Concrete.sequenceFin fun j => if j ∈ D.1 then pure (Step.done none) else
          free (advance (k j fun k' => if k' ∈ D.1 then b.2 k' j else o k' j))
        executeRounds worldRoles D A F n b.1 steps) := by
  obtain ⟨i0, hi0⟩ := exists_honest D
  rw [executeRounds, if_neg (by push Not; exact ⟨i0, hi0, by simp [hi0]⟩)]
  rw [stepRound, if_neg (by push Not; intro _; exact ⟨i0, hi0, by simp [hi0]⟩)]
  have hs : ∀ j, (if j ∈ D.1 then Step.done none else Step.wait (o j) (k j) :
      Step C E (CallSpec Ih Oh) α).outbox = if j ∈ D.1 then fun _ => none else o j := fun j => by
    split_ifs <;> rfl
  have hd : ∀ j, j ∉ D.1 → (if j ∈ D.1 then Step.done none else Step.wait (o j) (k j) :
      Step C E (CallSpec Ih Oh) α).delivered = o j := fun j hj => by
    rw [if_neg hj]; rfl
  simp only [hs, bind_assoc, pure_bind]
  have hm : (fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then (if i ∈ D.1 then (fun _ => none) else o i) c' else none) =
      fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then o i c' else none := by
    funext c' i; split_ifs <;> simp_all
  rw [hm]
  refine bind_congr' _ fun b => ?_
  refine congrArg (· >>= _) (congrArg Concrete.sequenceFin (funext fun j => ?_))
  by_cases hj : j ∈ D.1
  · simp only [hj, if_true]
  · simp only [hj, if_false, worldRoles]
    congr 3; funext k'; by_cases hk : k' ∈ D.1 <;> simp [hk, hd]

/-- The real run of a protocol with one call to `F_rand` and one round. -/
theorem realExecution_frand2 (D : C.Coalition) (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R)))
    (program : C.Party → I → PartyM C E (CallSpec ℕ (PrssOutput C R)) O)
    (callIn : C.Party → I → ℕ)
    (resume : C.Party → I → Option (PrssOutput C R) → OracleComp (PartySpec C E (CallSpec ℕ (PrssOutput C R))) (Option O))
    (out : C.Party → I → PrssOutput C R → Mail C E)
    (cont : C.Party → I → PrssOutput C R → Mail C E → OracleComp (PartySpec C E (CallSpec ℕ (PrssOutput C R))) (Option O))
    (res : C.Party → I → PrssOutput C R → Mail C E → Option O)
    (h1 : ∀ i xi, advance (program i xi).run = pure (.call (callIn i xi) (resume i xi)))
    (h2 : ∀ i xi o, advance (resume i xi (some o)) = pure (.wait (out i xi o) (cont i xi o)))
    (h3 : ∀ i xi o inbox, advance (cont i xi o inbox) = pure (.done (res i xi o inbox)))
    (x : C.Party → I) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (callIn i (x i))
    realExecution D A (Frand R) 2 program x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → R)) (LocalSpec C))
      let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
      let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then out i (x i) (rnd i) c' else none)
        (SimulatorSpec C))
      pure (b.1, fun i => if i ∈ D.1 then none else
        res i (x i) (rnd i) fun k => if k ∈ D.1 then b.2 k i else out k (x k) (rnd k) i)) := by
  intro c
  obtain ⟨i0, hi0⟩ := exists_honest D
  simp only [realExecution, executePhase, startSteps]
  rw [sequenceFin_congr_pure _ (fun i => if i ∈ D.1 then Step.done none else Step.call (callIn i (x i)) (resume i (x i)))
    (fun i => by split_ifs <;> simp [worldRoles, h1, free]; rfl)]
  simp only [pure_bind]
  show counted _ >>= _ = counted _ >>= _
  congr 1; funext st
  rw [executeRounds, if_neg (by push Not; exact ⟨i0, hi0, by simp [hi0]⟩)]
  rw [stepRound, if_pos ⟨⟨i0, hi0, by simp [hi0]⟩, fun i hi => Or.inl (by simp [hi])⟩]
  have hin : (fun i => if i ∈ D.1 then none else
      (if i ∈ D.1 then Step.done none else Step.call (callIn i (x i)) (resume i (x i)) :
        Step C E (CallSpec ℕ (PrssOutput C R)) O).callInput) =
      fun i => if i ∈ D.1 then none else some (callIn i (x i)) := by
    funext i; split_ifs <;> simp
  rw [hin, runFunctionality_Frand R D A st _ (fun i hi => by simp [hi])]
  simp only [bind_assoc, pure_bind]
  simp only [c]
  refine bind_congr' _ fun a => ?_
  refine bind_congr' _ fun fresh => ?_
  refine bind_congr' _ fun freshPair => ?_
  rw [sequenceFin_congr_pure _ (fun j => if j ∈ D.1 then Step.done none else
      Step.wait (out j (x j) (frandShare D c a.2.1 a.2.2 fresh freshPair j))
        (cont j (x j) (frandShare D c a.2.1 a.2.2 fresh freshPair j)))
    (fun j => by
      by_cases hj : j ∈ D.1
      · simp only [hj, if_true]
      · simp only [hj, if_false, frandOut_eq, worldRoles]; rw [h2]; rfl)]
  simp only [pure_bind]
  rw [executeRounds_wait]
  refine bind_congr' _ fun b => ?_
  rw [sequenceFin_congr_pure _ (fun j => if j ∈ D.1 then Step.done none else
      Step.done (res j (x j) (frandShare D c a.2.1 a.2.2 fresh freshPair j)
        fun k' => if k' ∈ D.1 then b.2 k' j else out k' (x k') (frandShare D c a.2.1 a.2.2 fresh freshPair k') j))
    (fun j => by
      by_cases hj : j ∈ D.1
      · simp only [hj, if_true]
      · simp only [hj, if_false]; rw [h3]; rfl)]
  simp only [pure_bind, executeRounds]
  congr 2; funext i; split_ifs <;> rfl

theorem advance_call {ι : Type} {G : OracleSpec ι} {α : Type} (input : ι) (f : G input → PartyM C E G α) :
    advance (C := C) (E := E) (call input >>= f).run = pure (.call input fun r => (f r).run) := rfl

theorem advance_round {ι : Type} {G : OracleSpec ι} {α : Type} (outbox : Mail C E) (f : Mail C E → PartyM C E G α) :
    advance (C := C) (E := E) (G := G) (OptionT.lift (OracleComp.lift
      (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inr outbox)))) >>= f).run =
      pure (.wait outbox fun r => (f r).run) := rfl

theorem advance_exchange {ι : Type} {G : OracleSpec ι} {α : Type} (outbox : Mail C E) (f : Mail C E → PartyM C E G α) :
    advance (C := C) (E := E) (G := G) (exchange outbox >>= f).run = pure (.wait outbox fun r =>
      (if C.parties.any fun j => Msg.isAbort (r j) then failure else f r).run) := by
  unfold exchange
  rw [bind_assoc]
  refine (advance_round (C := C) (E := E) (G := G) outbox _).trans ?_
  congr 2; funext r
  split <;> simp

theorem evalDist_sum_uniform {D R : Type} [Fintype D] [DecidableEq D] [AddCommGroup R]
    [SampleableType R] [SampleableType (D → R)] (T0 : D) :
    𝒟[((fun f => ∑ T, f T) <$> ($ᵗ (D → R)) : ProbComp R)] = 𝒟[$ᵗ R] := by
  have hu := evalDist_uniformSample_bind_update (D := D) (R := R) T0
  rw [evalDist_map, ← hu, ← evalDist_map]
  simp only [map_bind, map_pure]
  have hs : ∀ (u : R) (g : D → R), ∑ T, Function.update g T0 u T = u + ∑ T ∈ Finset.univ.erase T0, g T := by
    intro u g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T0), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun T hT => Function.update_of_ne (Finset.ne_of_mem_erase hT) _ _
  simp only [hs]
  rw [evalDist_bind_bind_swap]
  have : ∀ g : D → R, 𝒟[(do let u ← $ᵗ R; pure (u + ∑ T ∈ Finset.univ.erase T0, g T) : ProbComp R)] = 𝒟[$ᵗ R] := by
    intro g
    rw [show (do let u ← $ᵗ R; pure (u + ∑ T ∈ Finset.univ.erase T0, g T) : ProbComp R) =
      ((· + ∑ T ∈ Finset.univ.erase T0, g T) <$> ($ᵗ R)) from by simp [map_eq_bind_pure_comp]]
    exact evalDist_add_right_uniform R _
  rw [evalDist_bind]
  simp only [this]
  rw [← evalDist_bind]
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
section Field
variable [Field E] [Algebra Bit E]
open Polynomial

theorem charTwo : CharP E 2 := charP_of_injective_algebraMap (algebraMap Bit E).injective 2

/-- The first `t` operators. -/
abbrev firstParties (C : Committee) : Finset C.Party := Finset.univ.filter fun l : C.Party => l.val < C.t

theorem card_firstParties : (firstParties C).card = C.t := by
  have ht : C.t ≤ C.n := by simp only [Committee.n]; have := C.one_le_t; omega
  rw [firstParties, Fin.card_filter_val_lt]; omega

/-- A polynomial of degree at most `t - 1` is the interpolation of its values at the first `t` points. -/
theorem eval_eq_lagrangeFirst (K : Constants C E) (V : Polynomial E) (hV : V.natDegree ≤ C.t - 1) (x : E) :
    V.eval x = ∑ l ∈ firstParties C, lagrangeFirst K x l * V.eval (K.point l) := by
  have hdeg : V.degree < (firstParties C).card := by
    rw [card_firstParties]
    exact (degree_le_of_natDegree_le hV).trans_lt (by have := C.one_le_t; exact_mod_cast (by omega : C.t - 1 < C.t))
  conv_lhs => rw [Lagrange.eq_interpolate (K.point.injective.injOn) hdeg]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, Lagrange.eval_basis_eq_prod, lagrangeFirst]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- `Conv` of a replicated sharing is a Shamir sharing of degree `t - 1` of the same value (CDI05). -/
theorem conv_poly (K : Constants C E) (y : C.Term → E) :
    ∃ V : Polynomial E, V.natDegree ≤ C.t - 1 ∧ V.eval 0 = ∑ T, y T ∧
      ∀ i, (∑ T ∈ Finset.univ.filter (i ∈ C.holders ·), psi K T i * y T) = V.eval (K.point i) := by
  classical
  haveI := charTwo (E := E)
  refine ⟨∑ T, Polynomial.C (y T) * ∏ j ∈ T.1, (X + Polynomial.C (K.point j)) * Polynomial.C (K.point j)⁻¹,
    ?_, ?_, fun i => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun T _ =>
      (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    calc ∑ j ∈ T.1, ((X + Polynomial.C (K.point j)) * Polynomial.C (K.point j)⁻¹).natDegree
        ≤ ∑ _j ∈ T.1, 1 := Finset.sum_le_sum (f := fun j =>
          ((X + Polynomial.C (K.point j)) * Polynomial.C (K.point j)⁻¹).natDegree) fun j _ =>
          (natDegree_mul_C_le _ _).trans (natDegree_X_add_C _).le
      _ = C.t - 1 := by simp [T.2]
  · simp [eval_finsetSum, eval_prod, K.point_ne_zero]
  · simp only [psi, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X, ← div_eq_mul_inv]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    split_ifs with hi
    · ring
    · have hiT : i ∈ T.1 := by simpa [Committee.holders] using hi
      rw [Finset.prod_eq_zero hiT (by rw [CharTwo.add_self_eq_zero, zero_div]), mul_zero]

/-- The share of operator `j` in the view of operator `i` in `OpenSh`. -/
def openShare (i : C.Party) (v : ℕ → E) (inbox : Mail C E) (j : C.Party) (g : ℕ) : E :=
  if j = i then v g else Msg.elementAt (inbox j) g

def openOut (i : C.Party) (v : ℕ → E) (count : ℕ) : Mail C E :=
  fun j => if j = i then none else some (.elements (vector count v))

def openRes (K : Constants C E) (i : C.Party) (v : ℕ → E) (count : ℕ) (inbox : Mail C E) : Option (ℕ → E) :=
  @ite _ (∀ j : C.Party, ∀ g < count, openShare i v inbox j g =
      ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K (K.point j) l * openShare i v inbox l g)
    (Classical.propDecidable _)
    (some fun g => ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * openShare i v inbox l g)
    none

theorem openSh_eq {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    openSh (G := G) K ctx v count = exchange (openOut ctx.self v count) >>= fun inbox =>
      OptionT.mk (pure (openRes K ctx.self v count inbox)) := by
  unfold openSh openRes require
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  dsimp only [openShare]
  split <;> rfl

theorem coinWith_run' {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C) (o : PrssOutput C E) (c : ℕ) :
    (coinWith (G := G) K ctx o c).run' startRun = exchange (openOut ctx.self (conv K ctx o.1) c) >>= fun inbox =>
      OptionT.mk (pure ((openRes K ctx.self (conv K ctx o.1) c inbox).map (vector c))) := by
  unfold coinWith
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_lift, openSh_eq]
  simp only [bind_assoc, pure_bind, map_bind, StateT.run_pure, map_pure]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  cases h : openRes K ctx.self (conv K ctx o.1) c inbox <;> rfl
end Field

theorem runWorld_free_bind (prims : Primitives) {α β : Type} (p : ProbComp α) (k : α → OracleComp (WorldSpec C) β) :
    runWorld prims (free (liftComp p (LocalSpec C)) >>= k) = p >>= fun a => runWorld prims (k a) := by
  unfold runWorld
  rw [simulateQ_bind, WriterT.run_bind, StateT.run'_eq, StateT.run_bind, world_free_liftComp]
  simp only [bind_map_left, map_bind, one_mul, StateT.run'_eq]
  refine bind_congr' _ fun a => ?_
  simp only [StateT.run_map, Functor.map_map]

theorem runWorld_pure (prims : Primitives) {β : Type} (b : β) : runWorld (C := C) prims (pure b) = pure (b, 0) := rfl

theorem counted_liftComp_query (t : unifSpec.Domain) :
    counted (C := C) (liftComp (liftComp (liftM (unifSpec.query t) : ProbComp _) (LocalSpec C)) (SimulatorSpec C)) =
      (liftM ((WorldSpec C).query (.inl (.inl (.inl t)))) : OracleComp (WorldSpec C) _) := rfl

theorem world_inl_inl_inl (prims : Primitives) (t : unifSpec.Domain) (s : HashCache C) :
    (simulateQ (world prims) (liftM ((WorldSpec C).query (.inl (.inl (.inl t)))) : OracleComp (WorldSpec C) _)).run.run s =
      (fun a => ((a, 1), s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
  rw [simulateQ_query]
  simp only [world, QueryImpl.withAddCost_apply, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  erw [QueryImpl.add_apply_inl, QueryImpl.add_apply_inl]
  simp [localAnswer, unifFwdImpl]

theorem world_counted_liftComp (prims : Primitives) {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (world prims) (counted (C := C) (liftComp (liftComp p (LocalSpec C)) (SimulatorSpec C)))).run.run s =
      (fun a => ((a, 1), s)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa ih =>
    rw [liftComp_bind, liftComp_bind, counted_bind, simulateQ_bind, counted_liftComp_query]
    simp only [WriterT.run_bind, StateT.run_bind]
    erw [world_inl_inl_inl]
    simp only [bind_map_left, one_mul]
    rw [map_bind]
    congr 1; funext a
    rw [StateT.run_map, ih]
    simp

variable (prims : Primitives)

/-- Two computations with the same distribution in the world from every cache. -/
def WEq {α : Type} (oa ob : OracleComp (WorldSpec C) α) : Prop :=
  ∀ s, 𝒟[(simulateQ (world prims) oa).run.run s] = 𝒟[(simulateQ (world prims) ob).run.run s]

theorem WEq.refl {α : Type} (oa : OracleComp (WorldSpec C) α) : WEq prims oa oa := fun _ => rfl

theorem WEq.trans {α : Type} {oa ob oc : OracleComp (WorldSpec C) α} (h1 : WEq prims oa ob) (h2 : WEq prims ob oc) :
    WEq prims oa oc := fun s => (h1 s).trans (h2 s)

theorem WEq.symm {α : Type} {oa ob : OracleComp (WorldSpec C) α} (h : WEq prims oa ob) : WEq prims ob oa :=
  fun s => (h s).symm

theorem world_run_bind {α β : Type} (oa : OracleComp (WorldSpec C) α) (k : α → OracleComp (WorldSpec C) β)
    (s : HashCache C) :
    (simulateQ (world prims) (oa >>= k)).run.run s = (simulateQ (world prims) oa).run.run s >>= fun p =>
      (fun q => ((q.1.1, p.1.2 * q.1.2), q.2)) <$> (simulateQ (world prims) (k p.1.1)).run.run p.2 := by
  rw [simulateQ_bind, WriterT.run_bind, StateT.run_bind]
  refine bind_congr' _ fun p => ?_
  rw [StateT.run_map]

theorem WEq.bind_left {α β : Type} {oa ob : OracleComp (WorldSpec C) α} (h : WEq prims oa ob)
    (k : α → OracleComp (WorldSpec C) β) : WEq prims (oa >>= k) (ob >>= k) := fun s => by
  rw [world_run_bind, world_run_bind, evalDist_bind, evalDist_bind, h s]

theorem WEq.bind_right {α β : Type} (oa : OracleComp (WorldSpec C) α) {k k' : α → OracleComp (WorldSpec C) β}
    (h : ∀ a, WEq prims (k a) (k' a)) : WEq prims (oa >>= k) (oa >>= k') := fun s => by
  rw [world_run_bind, world_run_bind, evalDist_bind, evalDist_bind]
  congr 1; funext p
  rw [evalDist_map, evalDist_map, h p.1.1 p.2]

theorem WEq.of_eq {α : Type} {oa ob : OracleComp (WorldSpec C) α} (h : oa = ob) : WEq prims oa ob := h ▸ WEq.refl _ _

theorem world_run_free_bind {α β : Type} (p : ProbComp α) (k : α → OracleComp (WorldSpec C) β) (s : HashCache C) :
    (simulateQ (world prims) (free (liftComp p (LocalSpec C)) >>= k)).run.run s =
      p >>= fun a => (simulateQ (world prims) (k a)).run.run s := by
  rw [world_run_bind, world_free_liftComp]
  simp only [bind_map_left, one_mul]
  refine bind_congr' _ fun a => ?_
  simp

/-- A free sample commutes with any computation. -/
theorem WEq.free_swap {α β γ : Type} (p : ProbComp α) (ob : OracleComp (WorldSpec C) β)
    (k : α → β → OracleComp (WorldSpec C) γ) :
    WEq prims (free (liftComp p (LocalSpec C)) >>= fun a => ob >>= k a)
      (ob >>= fun b => free (liftComp p (LocalSpec C)) >>= fun a => k a b) := fun s => by
  rw [world_run_free_bind, world_run_bind]
  simp only [world_run_bind, world_free_liftComp, bind_map_left, one_mul, Functor.map_map, map_bind]
  rw [evalDist_bind_bind_swap]

/-- A sample on the counted copy is a free sample. -/
theorem WEq.counted_sample {α : Type} (p : ProbComp α) :
    WEq prims (counted (C := C) (liftComp (liftComp p (LocalSpec C)) (SimulatorSpec C))) (free (liftComp p (LocalSpec C))) :=
  fun s => by rw [world_counted_liftComp, world_free_liftComp]

/-- Free samples with the same distribution. -/
theorem WEq.free_dist {α β : Type} (p p' : ProbComp α) (h : 𝒟[p] = 𝒟[p']) (k : α → OracleComp (WorldSpec C) β) :
    WEq prims (free (liftComp p (LocalSpec C)) >>= k) (free (liftComp p' (LocalSpec C)) >>= k) := fun s => by
  rw [world_run_free_bind, world_run_free_bind, evalDist_bind, evalDist_bind, h]

theorem free_liftComp_merge {α β γ : Type} (p : ProbComp α) (q : ProbComp β) (k : α → β → OracleComp (WorldSpec C) γ) :
    (free (liftComp p (LocalSpec C)) >>= fun a => free (liftComp q (LocalSpec C)) >>= k a) =
      free (liftComp (do let a ← p; let b ← q; pure (a, b)) (LocalSpec C)) >>= fun ab => k ab.1 ab.2 := by
  simp only [liftComp_bind, free_bind, bind_assoc, liftComp_pure]
  rfl

theorem accepts_eq_of_WEq {oa ob : OracleComp (WorldSpec C) Bool} (h : WEq prims oa ob) :
    accepts prims oa = accepts prims ob := by
  unfold accepts runWorld
  rw [StateT.run'_eq, StateT.run'_eq]
  erw [probEvent_map, probEvent_map, probEvent_def, probEvent_def, h ∅]

theorem CostLe.counted_sample {α : Type} (p : ProbComp α) :
    CostLe prims (counted (C := C) (liftComp (liftComp p (LocalSpec C)) (SimulatorSpec C))) 0 := fun s r hr => by
  rw [world_counted_liftComp] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨a, -, rfl⟩ := hr; simp

section Coin
variable [Field E] [Algebra Bit E] [SampleableType E]

/-- Some operator sent an abort frame. -/
def anyAbort (inbox : Mail C E) : Bool := C.parties.any fun j => Msg.isAbort (inbox j)

/-- The output of `Coin` at operator `i` from its PRSS output and its inbox. -/
def coinRes (K : Constants C E) (i : C.Party) (c : ℕ) (o : PrssOutput C E) (inbox : Mail C E) : Option (List E) :=
  if anyAbort inbox then none else
    (openRes K (localContext i).self (conv K (localContext i) o.1) c inbox).map (vector c)

/-- The message of `Coin` from operator `i`. -/
def coinOut (K : Constants C E) (i : C.Party) (c : ℕ) (o : PrssOutput C E) : Mail C E :=
  openOut (localContext i).self (conv K (localContext i) o.1) c

theorem realExecution_coin (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E ℕ Unit (Shares C E × (C.Party → C.Party → ℕ → E))) (x : C.Party → ℕ) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (x i)
    realExecution D A (Frand E) coinRounds (coinProtocol K) x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → E)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → E)) (LocalSpec C))
      let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
      let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
        coinOut K i (x i) (rnd i) c' else none) (SimulatorSpec C))
      pure (b.1, fun i => if i ∈ D.1 then none else
        coinRes K i (x i) (rnd i) fun k => if k ∈ D.1 then b.2 k i else coinOut K k (x k) (rnd k) i)) :=
  realExecution_frand2 D A (coinProtocol K) (fun _ c => c)
    (fun i c r => OptionT.run (match r with
      | some randomness => (coinWith K (localContext i) randomness c).run' startRun
      | _ => failure))
    (fun i c o => coinOut K i c o)
    (fun i c o inbox => OptionT.run (if anyAbort inbox then failure else OptionT.mk (pure
      ((openRes K (localContext i).self (conv K (localContext i) o.1) c inbox).map (vector c)))))
    (fun i c o inbox => coinRes K i c o inbox)
    (fun i c => by
      unfold coinProtocol; rw [advance_call]; congr 2; funext r; cases r <;> rfl)
    (fun i c o => by
      show advance (OptionT.run ((coinWith K (localContext i) o c).run' startRun)) = _
      rw [coinWith_run']; exact advance_exchange _ _)
    (fun i c o inbox => by unfold coinRes; split <;> rfl) x z

theorem idealExecution_Fcoin {κ σ : Type} {S : OracleSpec κ}
    (lift : ∀ {β : Type}, OracleComp S β → OracleComp (WorldSpec C) β) (D : C.Coalition)
    (Sim : Simulator (C := C) S ℕ (List E) (Finset C.Party) σ) (x : C.Party → ℕ) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (x i)
    idealExecution lift D (Fcoin (E := E)) Sim x z = (do
      let st ← lift (Sim.start (corruptInputs D x) z)
      let values ← free (liftComp ($ᵗ (Fin c → E)) (LocalSpec C))
      let a ← lift (Sim.answer st (List.ofFn values))
      let out ← lift (Sim.output a.1)
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ a.2 then some (List.ofFn values) else none)) := by
  intro c
  unfold idealExecution
  simp only [Fcoin, sample, simulateQ_bind, simulateQ_leak_add]
  rw [simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ _)]
  simp [StateT.run_bind]
  rfl

end Coin

section CoinOpen
variable [Field E] [Algebra Bit E]

/-- The term values of `F_rand` at position `g`, each fresh term from its table. -/
def freshAt {count : ℕ} (fresh : C.Term → Fin count → E) (g : ℕ) (T : C.Term) : E :=
  if h : g < count then fresh T ⟨g, h⟩ else 0

theorem vector_getD {R : Type} [Zero R] (count : ℕ) (v : ℕ → R) (g : ℕ) (hg : g < count) :
    (vector count v).getD g 0 = v g := by
  simp [vector, hg]

/-- The `OpenSh` of a consistent Shamir sharing outputs its value. -/
theorem openRes_of_poly (K : Constants C E) (i : C.Party) (c : ℕ) (V : ℕ → Polynomial E)
    (hV : ∀ g, (V g).natDegree ≤ C.t - 1) (v : ℕ → E) (inbox : Mail C E)
    (hshare : ∀ j, ∀ g < c, openShare i v inbox j g = (V g).eval (K.point j)) :
    openRes K i v c inbox = some fun g => ∑ l ∈ firstParties C, lagrangeFirst K 0 l * openShare i v inbox l g := by
  unfold openRes
  rw [if_pos]
  intro j g hg
  rw [hshare j g hg, eval_eq_lagrangeFirst K (V g) (hV g)]
  exact Finset.sum_congr rfl fun l _ => by rw [hshare l g hg]

end CoinOpen

section CoinHonest
variable [Field E] [Algebra Bit E]

theorem conv_frandShare (K : Constants C E) {c : ℕ} (D : C.Coalition) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (fresh : C.Term → Fin c → E) (freshPair : C.Pair → Fin c → E)
    (j : C.Party) (g : ℕ) :
    conv K (localContext j) (frandShare D c known knownPairs fresh freshPair j).1 g =
      ∑ T ∈ Finset.univ.filter (j ∈ C.holders ·),
        psi K T j * (if KnownTo D.1 T then known T g else freshAt fresh g T) := by
  unfold conv frandShare
  refine Finset.sum_congr rfl fun T hT => ?_
  have hj : j ∈ C.holders T := (Finset.mem_filter.mp hT).2
  simp only [localContext, hj, if_true]
  split_ifs <;> rfl

theorem coinRes_honest (K : Constants C E) (c : ℕ) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (fresh : C.Term → Fin c → E) (freshPair : C.Pair → Fin c → E)
    (b : C.Party → C.Party → Option (Msg E)) (i : C.Party) :
    coinRes K i c (frandShare noCoalition c known knownPairs fresh freshPair i)
      (fun k => if k ∈ noCoalition.1 then b k i else
        coinOut K k c (frandShare noCoalition c known knownPairs fresh freshPair k) i) =
      some (List.ofFn fun g => ∑ T, fresh T g) := by
  have hD : ∀ k : C.Party, k ∉ (noCoalition : C.Coalition).1 := fun k => by simp [noCoalition]
  have hK : ∀ T : C.Term, ¬ KnownTo (noCoalition : C.Coalition).1 T := fun T => by simp [KnownTo, noCoalition]
  choose V hVdeg hV0 hVeval using fun g => conv_poly K (freshAt fresh g)
  have hconv : ∀ j g, conv K (localContext j) (frandShare noCoalition c known knownPairs fresh freshPair j).1 g =
      (V g).eval (K.point j) := fun j g => by
    rw [conv_frandShare, ← hVeval g j]
    exact Finset.sum_congr rfl fun T _ => by rw [if_neg (hK T)]
  have hshare : ∀ j, ∀ g < c, openShare (localContext i).self
      (conv K (localContext i) (frandShare noCoalition c known knownPairs fresh freshPair i).1)
      (fun k => if k ∈ noCoalition.1 then b k i else
        coinOut K k c (frandShare noCoalition c known knownPairs fresh freshPair k) i) j g = (V g).eval (K.point j) := by
    intro j g hg
    simp only [openShare, hD, if_false, coinOut, openOut]
    split_ifs with h1 h2
    · subst h1; exact hconv _ g
    · exact absurd h2.symm h1
    · show (vector c _).getD g 0 = _; rw [vector_getD _ _ g hg]; exact hconv j g
  unfold coinRes
  rw [if_neg (by simp [anyAbort, hD, coinOut, openOut, Msg.isAbort]), openRes_of_poly K _ c V hVdeg _ _ hshare]
  simp only [Option.map_some, vector, List.ofFn_eq_map]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_finRange]
  intro g h1 h2
  have hg : g < c := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [Finset.sum_congr rfl fun l _ => by rw [hshare l g hg], ← eval_eq_lagrangeFirst K (V g) (hVdeg g), hV0]
  exact Finset.sum_congr rfl fun T _ => by simp [freshAt, hg]

theorem coinRes_honest' (K : Constants C E) (c : ℕ) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (fresh : C.Term → Fin c → E) (freshPair : C.Pair → Fin c → E)
    (i : C.Party) :
    coinRes K i c (frandShare noCoalition c known knownPairs fresh freshPair i)
      (fun k => coinOut K k c (frandShare noCoalition c known knownPairs fresh freshPair k) i) =
      some (List.ofFn fun g => ∑ T, fresh T g) := by
  convert coinRes_honest K c known knownPairs fresh freshPair (fun _ _ => none) i using 3
  simp [noCoalition]

end CoinHonest

/-- A fixed term, the first `t - 1` operators. -/
def someTerm (C : Committee) : C.Term :=
  ⟨Finset.univ.filter fun l : C.Party => l.val < C.t - 1, by
    rw [Fin.card_filter_val_lt]; simp only [Committee.n]; omega⟩

theorem evalDist_uniform_bind_const {α β : Type} [SampleableType α] (mx : ProbComp β) :
    𝒟[($ᵗ α >>= fun _ => mx : ProbComp β)] = 𝒟[mx] := by
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]

theorem counted_pure {α : Type} (a : α) : counted (C := C) (pure a) = pure a := rfl

theorem firstInput_honest_const {I : Type} [Inhabited I] (D : C.Coalition) (c : I) :
    firstInput (fun i => if i ∈ D.1 then none else some c) = c := by
  obtain ⟨i0, hi0⟩ := exists_honest D
  unfold firstInput
  have hmem : c ∈ C.parties.filterMap (fun i => if i ∈ D.1 then none else some c) :=
    List.mem_filterMap.mpr ⟨i0, by simp [Committee.parties], by simp [hi0]⟩
  obtain ⟨d, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hl, List.headD_cons]
  have hd : d ∈ C.parties.filterMap (fun i => if i ∈ D.1 then none else some c) := by rw [hl]; simp
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hd
  split_ifs at hj <;> simp_all

section CoinRobust
variable [Field E] [Algebra Bit E]
open Polynomial

/-- The interpolation of `t` values at the first `t` points. -/
theorem eval_interpolate_first (K : Constants C E) (share : C.Party → E) (x : E) :
    (Lagrange.interpolate (firstParties C) K.point share).eval x =
      ∑ l ∈ firstParties C, lagrangeFirst K x l * share l := by
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, Lagrange.eval_basis_eq_prod, lagrangeFirst]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem card_honest_ge (D : C.Coalition) : C.t ≤ (Finset.univ.filter fun j : C.Party => j ∉ D.1).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ) (fun j : C.Party => j ∈ D.1)
  have hD : (Finset.univ.filter fun j : C.Party => j ∈ D.1).card = D.1.card := by
    congr 1; ext j; simp
  have := D.2; have := C.one_le_t
  simp only [Finset.card_univ, Fintype.card_fin, Committee.n] at h
  omega

/-- Two polynomials of degree below `t` that agree at the honest points are equal. -/
theorem poly_eq_of_honest (K : Constants C E) (D : C.Coalition) (P V : Polynomial E)
    (hP : P.degree < C.t) (hV : V.degree < C.t) (h : ∀ j, j ∉ D.1 → P.eval (K.point j) = V.eval (K.point j)) :
    P = V := by
  haveI : DecidableEq E := Classical.decEq E
  have hs : ((Finset.univ.filter fun j : C.Party => j ∉ D.1).image K.point).card =
      (Finset.univ.filter fun j : C.Party => j ∉ D.1).card :=
    Finset.card_image_of_injective _ K.point.injective
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((Finset.univ.filter fun j : C.Party => j ∉ D.1).image K.point) ?_ ?_
  · calc (P - V).degree ≤ max P.degree V.degree := degree_sub_le _ _
      _ < C.t := max_lt hP hV
      _ ≤ _ := by rw [hs]; exact_mod_cast card_honest_ge D
  · intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact h j (Finset.mem_filter.mp hj).2

theorem degree_lt_of_natDegree (V : Polynomial E) (hV : V.natDegree ≤ C.t - 1) : V.degree < C.t :=
  (degree_le_of_natDegree_le hV).trans_lt (by have := C.one_le_t; exact_mod_cast (by omega : C.t - 1 < C.t))

/-- The term values of `F_rand` at position `g`. -/
def frandAt {count : ℕ} (D : C.Coalition) (known : Shares C E) (fresh : C.Term → Fin count → E) (g : ℕ)
    (T : C.Term) : E :=
  if KnownTo D.1 T then known T g else freshAt fresh g T

/-- `OpenSh` is robust. An honest operator outputs the value of the honest Shamir sharing or aborts. -/
theorem coinRes_robust (K : Constants C E) (D : C.Coalition) (c : ℕ) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (fresh : C.Term → Fin c → E) (freshPair : C.Pair → Fin c → E)
    (b : C.Party → C.Party → Option (Msg E)) (i : C.Party) (hi : i ∉ D.1) :
    coinRes K i c (frandShare D c known knownPairs fresh freshPair i)
        (fun k => if k ∈ D.1 then b k i else coinOut K k c (frandShare D c known knownPairs fresh freshPair k) i) = none ∨
      coinRes K i c (frandShare D c known knownPairs fresh freshPair i)
        (fun k => if k ∈ D.1 then b k i else coinOut K k c (frandShare D c known knownPairs fresh freshPair k) i) =
        some (List.ofFn fun g : Fin c => ∑ T, frandAt D known fresh g T) := by
  choose V hVdeg hV0 hVeval using fun g : ℕ => conv_poly K (frandAt D known fresh g)
  have hconv : ∀ j g, conv K (localContext j) (frandShare D c known knownPairs fresh freshPair j).1 g =
      (V g).eval (K.point j) := fun j g => by
    rw [conv_frandShare, ← hVeval g j]; rfl
  set inbox : Mail C E := fun k => if k ∈ D.1 then b k i else
    coinOut K k c (frandShare D c known knownPairs fresh freshPair k) i
  set v := conv K (localContext i) (frandShare D c known knownPairs fresh freshPair i).1
  have hhonest : ∀ j, j ∉ D.1 → ∀ g < c, openShare (localContext i).self v inbox j g = (V g).eval (K.point j) := by
    intro j hj g hg
    simp only [openShare, inbox, hj, if_false, coinOut, openOut]
    split_ifs with h1 h2
    · subst h1; exact hconv _ g
    · exact absurd h2.symm h1
    · show (vector c _).getD g 0 = _; rw [vector_getD _ _ g hg]; exact hconv j g
  unfold coinRes
  by_cases hab : anyAbort inbox = true
  · exact Or.inl (if_pos hab)
  rw [if_neg hab]
  unfold openRes
  rcases Classical.em (∀ j : C.Party, ∀ g < c, openShare (localContext i).self v inbox j g =
      ∑ l ∈ firstParties C, lagrangeFirst K (K.point j) l * openShare (localContext i).self v inbox l g) with hcond | hcond
  · right
    rw [if_pos hcond]
    simp only [Option.map_some, vector, List.ofFn_eq_map, Option.some.injEq]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_finRange]
    intro g h1 h2
    have hg : g < c := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
    have hPV : Lagrange.interpolate (firstParties C) K.point (fun l => openShare (localContext i).self v inbox l g) =
        V g := by
      refine poly_eq_of_honest K D _ _ ?_ (degree_lt_of_natDegree _ (hVdeg g)) fun j hj => ?_
      · have := Lagrange.degree_interpolate_lt (r := fun l => openShare (localContext i).self v inbox l g)
          (K.point.injective.injOn (s := firstParties C))
        rwa [card_firstParties] at this
      · rw [eval_interpolate_first, ← hcond j g hg, hhonest j hj g hg]
    rw [← eval_interpolate_first, hPV, hV0]
    rfl
  · left; rw [if_neg hcond]; rfl

end CoinRobust

section CoinSim
variable [Field E] [Algebra Bit E]

theorem lackedTerm_spec (D : C.Coalition) : ∃ T, lackedTerm D.1 = some T ∧ ¬ KnownTo D.1 T := by
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq D.2 (by simp [Committee.n]; omega)
  have hunk : ¬ KnownTo D.1 ⟨T, hT⟩ := by
    rintro ⟨j, hj, hjh⟩
    exact (by simpa [Committee.holders] using hjh : j ∉ T) (hDT hj)
  cases h : lackedTerm D.1 with
  | none =>
    exfalso
    have := List.find?_eq_none.mp h ⟨T, hT⟩ (by simp [Committee.terms])
    exact this (by simpa using hunk)
  | some T' =>
    exact ⟨T', rfl, by simpa using List.find?_some h⟩

/-- The fresh terms of the simulated `F_rand`, with the lacked term set so that the terms sum to `v`. -/
def adjust (D : C.Coalition) {n : ℕ} (known : Shares C E) (fresh' : C.Term → Fin n → E) (v : Fin n → E) :
    C.Term → Fin n → E := fun T =>
  if lackedTerm D.1 = some T then fun g => v g - ∑ T' ∈ Finset.univ.erase T,
    (if KnownTo D.1 T' then known T' g else fresh' T' g)
  else fresh' T

theorem sum_frandAt_adjust (D : C.Coalition) {n : ℕ} (known : Shares C E) (fresh' : C.Term → Fin n → E)
    (v : Fin n → E) (g : Fin n) : ∑ T, frandAt D known (adjust D known fresh' v) g T = v g := by
  obtain ⟨T0, hT0, hunk⟩ := lackedTerm_spec D
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T0)]
  have h1 : frandAt D known (adjust D known fresh' v) g T0 = v g - ∑ T' ∈ Finset.univ.erase T0,
      (if KnownTo D.1 T' then known T' g else fresh' T' g) := by
    simp [frandAt, hunk, freshAt, adjust, hT0, g.2]
  have h2 : ∀ T ∈ Finset.univ.erase T0, frandAt D known (adjust D known fresh' v) g T =
      if KnownTo D.1 T then known T g else fresh' T g := fun T hT => by
    have hne : lackedTerm D.1 ≠ some T := by rw [hT0]; simpa using (Finset.ne_of_mem_erase hT).symm
    simp [frandAt, freshAt, adjust, hne, g.2]
  rw [h1, Finset.sum_congr rfl h2, sub_add_cancel]

theorem adjust_eq_update (D : C.Coalition) {n : ℕ} (known : Shares C E) (fresh' : C.Term → Fin n → E)
    (v : Fin n → E) (T0 : C.Term) (hT0 : lackedTerm D.1 = some T0) :
    adjust D known fresh' v = Function.update fresh' T0 (v - fun g : Fin n => ∑ T' ∈ Finset.univ.erase T0,
      (if KnownTo D.1 T' then known T' g else fresh' T' g)) := by
  funext T
  by_cases h : T = T0
  · subst h; simp [adjust, hT0]; rfl
  · have hne : lackedTerm D.1 ≠ some T := by rw [hT0]; simpa using Ne.symm h
    simp [adjust, hne, Function.update_of_ne h]

/-- The simulated fresh terms are uniform. -/
theorem dist_adjust [SampleableType E] (D : C.Coalition) (known : Shares C E) {n : ℕ} {γ : Type}
    (f : (C.Term → Fin n → E) → ProbComp γ) :
    𝒟[do let v ← $ᵗ (Fin n → E); let fresh' ← $ᵗ (C.Term → Fin n → E); f (adjust D known fresh' v)] =
      𝒟[$ᵗ (C.Term → Fin n → E) >>= f] := by
  obtain ⟨T0, hT0, -⟩ := lackedTerm_spec D
  simp only [adjust_eq_update D known _ _ T0 hT0]
  rw [evalDist_bind_bind_swap]
  have hshift : ∀ fresh' : C.Term → Fin n → E,
      𝒟[do let v ← $ᵗ (Fin n → E); f (Function.update fresh' T0 (v - fun g : Fin n => ∑ T' ∈ Finset.univ.erase T0,
        (if KnownTo D.1 T' then known T' g else fresh' T' g)))] =
      𝒟[do let u ← $ᵗ (Fin n → E); f (Function.update fresh' T0 u)] := fun fresh' => by
    refine evalDist_ext fun z => ?_
    simp only [sub_eq_add_neg]
    exact probOutput_bind_add_right_uniform (Fin n → E) _ (fun u => f (Function.update fresh' T0 u)) z
  rw [evalDist_bind]; simp only [hshift]; rw [← evalDist_bind]
  rw [evalDist_bind_bind_swap]
  have hu := evalDist_uniformSample_bind_update (D := C.Term) (R := Fin n → E) T0
  rw [show (do let u ← $ᵗ (Fin n → E); let fresh' ← $ᵗ (C.Term → Fin n → E); f (Function.update fresh' T0 u)) =
      (do let u ← $ᵗ (Fin n → E); let fresh' ← $ᵗ (C.Term → Fin n → E); pure (Function.update fresh' T0 u)) >>= f by
    simp [bind_assoc]]
  rw [evalDist_bind, hu, ← evalDist_bind]

end CoinSim

section CoinClaims
variable [Field E] [Algebra Bit E]

theorem coinCompleteness (prims : Primitives) (K : Constants C E) [SampleableType E] :
    CoinCompletenessStatement prims K := by
  intro x hx
  obtain ⟨c, rfl⟩ : ∃ c, x = fun _ => c := by
    obtain ⟨i0, -⟩ := exists_honest (noCoalition : C.Coalition)
    exact ⟨x i0, funext fun i => hx i i0 (by simp [noCoalition]) (by simp [noCoalition])⟩
  rw [realExecution_coin, idealExecution_Fcoin]
  simp only [honestAdversary, honestSimulator, liftComp_pure, counted_pure, pure_bind]
  have hcc := firstInput_honest_const (noCoalition : C.Coalition) c
  generalize firstInput (fun i => if i ∈ (noCoalition : C.Coalition).1 then none else some c) = c' at hcc ⊢
  subst hcc
  have hD : ∀ k : C.Party, k ∉ (noCoalition : C.Coalition).1 := fun k => by simp [noCoalition]
  simp only [runWorld_free_bind, runWorld_pure, hD, if_false, not_false_eq_true, true_and,
    Finset.mem_univ, map_bind, map_pure, coinRes_honest', if_true]
  refine le_of_eq ((tvDist_eq_zero_iff _ _).2 ?_)
  have hsum : ∀ a : C.Term → Fin c' → E, (List.ofFn fun g => ∑ T, a T g) = List.ofFn (∑ T, a T) := fun a => by
    congr 1; funext g; rw [Finset.sum_apply]
  simp only [hsum]
  rw [evalDist_bind]
  simp only [evalDist_uniform_bind_const]
  rw [← evalDist_bind]
  rw [show ($ᵗ (C.Term → Fin c' → E) >>= fun a => pure fun _ => some (List.ofFn (∑ T, a T)) :
      ProbComp (C.Party → Option (List E))) =
      (fun v => fun _ => some (List.ofFn v)) <$> ((fun f => ∑ T, f T) <$> ($ᵗ (C.Term → Fin c' → E))) by
    simp [map_eq_bind_pure_comp]]
  rw [evalDist_map, evalDist_sum_uniform (someTerm C), ← evalDist_map]
  simp [map_eq_bind_pure_comp]

end CoinClaims

theorem firstInput_eq_of_same {I : Type} [Inhabited I] (D : C.Coalition) (y : C.Party → I)
    (h : ∀ i j, i ∉ D.1 → j ∉ D.1 → y i = y j) (i : C.Party) (hi : i ∉ D.1) :
    firstInput (fun j => if j ∈ D.1 then none else some (y j)) = y i := by
  rw [show (fun j => if j ∈ D.1 then none else some (y j)) = fun j => if j ∈ D.1 then none else some (y i) from
    funext fun j => by
      by_cases hj : j ∈ D.1
      · simp [hj]
      · simp [hj, h j i hj hi]]
  exact firstInput_honest_const D (y i)

section CoinSecurity
variable [Field E] [Algebra Bit E] [SampleableType E]

/-- The reply of the coin simulator to the leak `vals` of `F_coin`, with the count `n`. It runs the
adversary on `F_rand` with the lacked term set so that the terms sum to `vals`, sends the honest
shares of `OpenSh`, and names the honest operators whose `OpenSh` does not abort. -/
def coinSimAnswer (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E ℕ Unit (Shares C E × (C.Party → C.Party → ℕ → E))) (n : ℕ) (vals : List E)
    (st : A.State) : OracleComp (LocalSpec C) (A.State × Finset C.Party) := do
  let a ← A.answer st ()
  let fresh' ← liftComp ($ᵗ (C.Term → Fin n → E)) (LocalSpec C)
  let freshPair ← liftComp ($ᵗ (C.Pair → Fin n → E)) (LocalSpec C)
  let rnd := frandShare D n a.2.1 a.2.2 (adjust D a.2.1 fresh' fun g => vals.getD g.val 0) freshPair
  let b ← A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then coinOut K i n (rnd i) c' else none
  pure (b.1, Finset.univ.filter fun i => i ∉ D.1 ∧
    (coinRes K i n (rnd i) fun k => if k ∈ D.1 then b.2 k i else coinOut K k n (rnd k) i).isSome)

/-- The simulator of `Coin` (GS20, Lemma 3). -/
def coinSim (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E ℕ Unit (Shares C E × (C.Party → C.Party → ℕ → E))) :
    Simulator (C := C) (LocalSpec C) ℕ (List E) (Finset C.Party) A.State where
  State := A.State
  start := A.start
  answer st vals := coinSimAnswer K D A vals.length vals st
  output st := pure st

/-- The round of `OpenSh` and the distinguisher, from the PRSS outputs of `F_rand`. -/
def coinTail (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E ℕ Unit (Shares C E × (C.Party → C.Party → ℕ → E))) (Z : Distinguisher C A.State (List E))
    (c : ℕ) (a : A.State × Shares C E × (C.Party → C.Party → ℕ → E)) (fresh : C.Term → Fin c → E)
    (freshPair : C.Pair → Fin c → E) : OracleComp (WorldSpec C) Bool := do
  let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
  let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then coinOut K i c (rnd i) c' else none)
    (SimulatorSpec C))
  counted (liftComp (Z (b.1, fun i => if i ∈ D.1 then none else
    coinRes K i c (rnd i) fun k => if k ∈ D.1 then b.2 k i else coinOut K k c (rnd k) i)) (SimulatorSpec C))

theorem getD_ofFn_eq {n : ℕ} (v : Fin n → E) : (fun g : Fin n => (List.ofFn v).getD g.val 0) = v := by
  funext g; simp [List.getD_eq_getElem?_getD]

/-- The simulated fresh terms replace the real ones. -/
theorem WEq.adjust (prims : Primitives) (D : C.Coalition) (known : Shares C E) {n : ℕ} {β : Type}
    (L : (C.Term → Fin n → E) → OracleComp (WorldSpec C) β) :
    WEq prims (free (liftComp ($ᵗ (Fin n → E)) (LocalSpec C)) >>= fun v =>
        free (liftComp ($ᵗ (C.Term → Fin n → E)) (LocalSpec C)) >>= fun f' => L (adjust D known f' v))
      (free (liftComp ($ᵗ (C.Term → Fin n → E)) (LocalSpec C)) >>= L) := fun s => by
  rw [world_run_free_bind, world_run_free_bind]
  simp only [world_run_free_bind]
  exact dist_adjust D known fun fr => (simulateQ (world prims) (L fr)).run.run s

theorem coinSecurity (prims : Primitives) (K : Constants C E) : CoinStatement prims K := by
  intro D A
  refine ⟨coinSim K D A, fun x z Z q hx hq => ⟨?_, ?_⟩⟩
  · obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
    simp only [coinRounds, extendMultRounds, multRounds] at hsum
    apply hasHashQueryBound_of_costLe
    unfold distinguish
    rw [idealExecution_Fcoin]
    simp only [coinSim, worldRoles, coinSimAnswer, liftComp_bind, counted_bind, bind_assoc, liftComp_pure,
      counted_pure, pure_bind]
    exact CostLe.mono prims (CostLe.bind prims (CostLe.of_counted prims _ _ (hs _ _)) fun st =>
      CostLe.bind prims (CostLe.free_sample prims _) fun v =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (ha _ _)) fun a =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun f' =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun fp =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (hr _ _)) fun b =>
      CostLe.of_counted prims _ _ (hz _)) (by omega)
  · suffices h : WEq prims (distinguish (realExecution D A (Frand E) coinRounds (coinProtocol K) x z) Z)
        (distinguish (idealExecution worldRoles.adversary D Fcoin (coinSim K D A) x z) Z) by
      rw [accepts_eq_of_WEq prims h, sub_self, abs_zero]
    unfold distinguish
    rw [realExecution_coin, idealExecution_Fcoin]
    simp only [coinSim, worldRoles, List.length_ofFn]
    have hxc := firstInput_eq_of_same D x hx
    generalize firstInput (fun i => if i ∈ D.1 then none else some (x i)) = c at hxc ⊢
    simp only [coinSimAnswer, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure, pure_bind]
    refine WEq.symm prims (WEq.bind_right prims _ fun st => ?_)
    refine WEq.trans prims (WEq.free_swap prims _ _ _) (WEq.bind_right prims _ fun a => ?_)
    refine WEq.trans prims (WEq.bind_right prims _ fun v => (WEq.counted_sample prims _).bind_left prims _) ?_
    refine WEq.trans prims (WEq.bind_right prims _ fun v => WEq.bind_right prims _ fun f' =>
      (WEq.counted_sample prims _).bind_left prims _) ?_
    refine WEq.trans prims (WEq.of_eq prims ?_) (WEq.trans prims (WEq.adjust prims D a.2.1
      (fun fresh => free (liftComp ($ᵗ (C.Pair → Fin c → E)) (LocalSpec C)) >>= fun fp => coinTail K D A Z c a fresh fp))
      (WEq.of_eq prims ?_))
    · refine bind_congr' _ fun v => bind_congr' _ fun f' => bind_congr' _ fun fp => ?_
      unfold coinTail
      simp only [getD_ofFn_eq]
      refine bind_congr' _ fun b => ?_
      refine congrArg (fun o => counted (liftComp (Z (b.1, o)) (SimulatorSpec C))) (funext fun i => ?_)
      by_cases hi : i ∈ D.1
      · simp [hi]
      · rcases coinRes_robust K D c a.2.1 a.2.2 (adjust D a.2.1 f' v) fp b.2 i hi with h | h
        · simp [hi, h]
        · simp only [sum_frandAt_adjust] at h
          simp [hi, h]
    · refine bind_congr' _ fun fresh => bind_congr' _ fun fp => ?_
      unfold coinTail
      dsimp only
      have hm : (fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then coinOut K i c (frandShare D c a.2.1 a.2.2 fresh fp i) c'
          else none) = (fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
            coinOut K i (x i) (frandShare D c a.2.1 a.2.2 fresh fp i) c' else none) := by
        funext c' i
        by_cases h : c' ∈ D.1 ∧ i ∉ D.1
        · rw [if_pos h, if_pos h, ← hxc i h.2]
        · rw [if_neg h, if_neg h]
      rw [hm]
      refine bind_congr' _ fun b => ?_
      refine congrArg (fun o => counted (liftComp (Z (b.1, o)) (SimulatorSpec C))) (funext fun i => ?_)
      by_cases hi : i ∈ D.1
      · simp [hi]
      · simp only [hi, if_false, ← hxc i hi]
        congr 1; funext k
        by_cases hk : k ∈ D.1
        · simp [hk]
        · simp [hk, ← hxc k hk]

end CoinSecurity

section Reshare
variable [Field E] [Algebra Bit E]

/-- The value `u_i` that operator `i` sends in a peer reshare. -/
def reshareU {R : Type} [Field R] (K : Constants C E) (ctx : Context C) (r : Shares C R) (Zs : C.Party → ℕ → R)
    (v : ℕ → R) : ℕ → R := fun g => v g + ∑ j ∈ Finset.univ.erase ctx.self, Zs j g +
  ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = ctx.self), r T g

/-- The messages of a peer reshare. -/
def reshareOut {R : Type} [Field R] (K : Constants C E) (ctx : Context C) (codec : Codec C E R) (r : Shares C R)
    (Zs : C.Party → ℕ → R) (v : ℕ → R) (count : ℕ) : Mail C E := fun j =>
  if j ≠ ctx.self ∧ j ∈ C.holders (K.filled ctx.self) then some (codec.pack (vector count (reshareU K ctx r Zs v)))
  else none

/-- The output of a peer reshare. -/
def reshareZ {R : Type} [Field R] (K : Constants C E) (ctx : Context C) (codec : Codec C E R) (r : Shares C R)
    (Zs : C.Party → ℕ → R) (v : ℕ → R) (count : ℕ) (inbox : Mail C E) : Shares C R := fun T g =>
  if ctx.self ∉ C.holders T ∨ count ≤ g then 0
  else if T ∈ filledTerms K then
    ∑ j ∈ Finset.univ.filter (K.filled · = T),
      if j = ctx.self then reshareU K ctx r Zs v g else codec.unpack (inbox j) g
  else r T g

theorem reshare_run' {ι : Type} {G : OracleSpec ι} {R : Type} [Field R] (K : Constants C E) (ctx : Context C)
    (codec : Codec C E R) (r : Shares C R) (Zs : C.Party → ℕ → R) (v : ℕ → R) (count : ℕ) (st : RunState C) :
    (reshare (G := G) K ctx codec (r, Zs) v count).run' st =
      exchange (reshareOut K ctx codec r Zs v count) >>= fun inbox =>
        pure (reshareZ K ctx codec r Zs v count inbox) := by
  unfold reshare
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_lift]
  simp only [bind_assoc, pure_bind, map_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  simp [record, StateT.run_bind]
  unfold reshareZ reshareU
  simp

end Reshare

theorem world_support_const {α : Type} (prims : Primitives) (oa : OracleComp (WorldSpec C) α) (b : Bool)
    (s : HashCache C) : ∀ r ∈ support ((simulateQ (world prims) (oa >>= fun _ => pure b)).run.run s), r.1.1 = b := by
  intro r hr
  obtain ⟨p, -, q, hq, rfl⟩ := mem_support_world_bind prims _ _ s r hr
  change q ∈ support (pure ((b, 1), p.2) : ProbComp _) at hq
  simp at hq; subst hq; rfl

theorem accepts_const {α : Type} (prims : Primitives) (oa : OracleComp (WorldSpec C) α) (b : Bool) :
    accepts prims (oa >>= fun _ => pure b) = if b then 1 else 0 := by
  unfold accepts runWorld
  rw [StateT.run'_eq]
  erw [probEvent_map]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [probEvent_eq_zero fun r hr => by
      simp [world_support_const prims oa false ∅ r hr]]
    rfl
  · simp only [if_true]
    rw [(probEvent_eq_one_iff).2 ⟨by simp, fun r hr => by simp [world_support_const prims oa true ∅ r hr]⟩]
    rfl

section MultPeer
variable [Field E] [Algebra Bit E]

theorem realExecution_multPeer (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Shares C Bit × Shares C Bit × ℕ) Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (x : C.Party → Shares C Bit × Shares C Bit × ℕ) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (x i).2.2
    realExecution D A (Frand Bit) (1 + ReshareMode.peer.rounds) (multProtocol K .peer) x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → Bit)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → Bit)) (LocalSpec C))
      let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
      let out := fun i => reshareOut K (localContext i) bitCodec (rnd i).1 (rnd i).2
        (mulRep K (localContext i) (x i).1 (x i).2.1) (x i).2.2
      let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then out i c' else none)
        (SimulatorSpec C))
      pure (b.1, fun i => if i ∈ D.1 then none else
        let inbox : Mail C E := fun k => if k ∈ D.1 then b.2 k i else out k i
        if anyAbort inbox then none else some (reshareZ K (localContext i) bitCodec (rnd i).1 (rnd i).2
          (mulRep K (localContext i) (x i).1 (x i).2.1) (x i).2.2 inbox))) :=
  realExecution_frand2 D A (multProtocol K .peer) (fun _ xi => xi.2.2)
    (fun i xi r => OptionT.run (match r with
      | some randomness => (reshareWith K (localContext i) .peer randomness
          (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2).run' startRun
      | _ => failure))
    (fun i xi o => reshareOut K (localContext i) bitCodec o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2)
    (fun i xi o inbox => OptionT.run (if anyAbort inbox then failure else
      pure (reshareZ K (localContext i) bitCodec o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox)))
    (fun i xi o inbox => if anyAbort inbox then none else
      some (reshareZ K (localContext i) bitCodec o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox))
    (fun i xi => by
      rcases xi with ⟨x, y, c⟩
      unfold multProtocol; rw [advance_call]; congr 2; funext r; cases r <;> rfl)
    (fun i xi o => by
      rcases o with ⟨r, Zs⟩
      show advance (OptionT.run ((reshare K (localContext i) bitCodec (r, Zs)
        (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2).run' startRun)) = _
      rw [reshare_run']; exact advance_exchange _ _)
    (fun i xi o inbox => by split <;> rfl) x z

end MultPeer

section ExtendMult
variable [Field E] [Algebra Bit E] [SampleableType E]

/-- The additive shares of the inner products of operator `i`. -/
def productValues (K : Constants C E) (i : C.Party) (products : List (Product C E)) : ℕ → E :=
  fun g => match products[g]? with | some p => productShare K (localContext i) p | none => 0

theorem realExecution_extendMult (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (List (Product C E)) Unit (Shares C E × (C.Party → C.Party → ℕ → E)))
    (x : C.Party → List (Product C E)) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (x i).length
    realExecution D A (Frand E) extendMultRounds (extendMultProtocol K) x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → E)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → E)) (LocalSpec C))
      let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
      let out := fun i => reshareOut K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2
        (productValues K i (x i)) (x i).length
      let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then out i c' else none)
        (SimulatorSpec C))
      pure (b.1, fun i => if i ∈ D.1 then none else
        let inbox : Mail C E := fun k => if k ∈ D.1 then b.2 k i else out k i
        if anyAbort inbox then none else some (reshareZ K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2
          (productValues K i (x i)) (x i).length inbox))) :=
  realExecution_frand2 D A (extendMultProtocol K) (fun _ xi => xi.length)
    (fun i xi r => OptionT.run (match r with
      | some randomness => (reshare K (localContext i) (elementCodec K) randomness
          (productValues K i xi) xi.length).run' startRun
      | _ => failure))
    (fun i xi o => reshareOut K (localContext i) (elementCodec K) o.1 o.2 (productValues K i xi) xi.length)
    (fun i xi o inbox => OptionT.run (if anyAbort inbox then failure else
      pure (reshareZ K (localContext i) (elementCodec K) o.1 o.2 (productValues K i xi) xi.length inbox)))
    (fun i xi o inbox => if anyAbort inbox then none else
      some (reshareZ K (localContext i) (elementCodec K) o.1 o.2 (productValues K i xi) xi.length inbox))
    (fun i xi => by
      unfold extendMultProtocol; rw [advance_call]; congr 2; funext r; cases r <;> rfl)
    (fun i xi o => by
      rcases o with ⟨r, Zs⟩
      show advance (OptionT.run ((reshare K (localContext i) (elementCodec K) (r, Zs)
        (productValues K i xi) xi.length).run' startRun)) = _
      rw [reshare_run']; exact advance_exchange _ _)
    (fun i xi o inbox => by split <;> rfl) x z

end ExtendMult

section PeerSim
variable [Field E] [Algebra Bit E]

/-- The first honest holder of a term, the reference view of the simulator. -/
def refHolder (D : C.Coalition) (T : C.Term) : C.Party :=
  ((C.parties.filter fun i => i ∈ C.holders T ∧ i ∉ D.1).head?).getD ⟨0, by
    simp only [Committee.n]; have := C.one_le_t; omega⟩

/-- The reply of the peer-reshare simulator to a leak with count `n`. It runs the adversary on a
simulated `F_rand` and on the messages of honest operators with zero inputs, names the honest operators
that do not abort, takes each term from its first honest holder, the offsets from the other holders,
and the additive attack as the sum of the simulated terms. -/
def peerSimAnswer {I R : Type} [Field R] [SampleableType R] (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R))) (codec : Codec C E R) (n : ℕ)
    (st : A.State) :
    OracleComp (LocalSpec C) (A.State × ((ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party)) := do
  let a ← A.answer st ()
  let fresh' ← liftComp ($ᵗ (C.Term → Fin n → R)) (LocalSpec C)
  let freshPair' ← liftComp ($ᵗ (C.Pair → Fin n → R)) (LocalSpec C)
  let rnd := frandShare D n a.2.1 a.2.2 fresh' freshPair'
  let out := fun i => reshareOut K (localContext i) codec (rnd i).1 (rnd i).2 (fun _ => 0) n
  let b ← A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then out i c' else none
  let inbox := fun i k => if k ∈ D.1 then b.2 k i else out k i
  let zf := fun i => reshareZ K (localContext i) codec (rnd i).1 (rnd i).2 (fun _ => 0) n (inbox i)
  let known : Shares C R := fun T => zf (refHolder D T) T
  pure (b.1, (fun g => ∑ T, known T g, known, fun i T g => zf i T g - known T g,
    Finset.univ.filter fun i => i ∉ D.1 ∧ anyAbort (inbox i) = false))

/-- The simulator of a peer reshare (GS20, Lemmas 4 and 5). -/
def peerSim {I Lk R : Type} [Field R] [SampleableType R] (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R))) (codec : Codec C E R)
    (count : Lk → ℕ) :
    Simulator (C := C) (LocalSpec C) I Lk ((ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party)
      A.State where
  State := A.State
  start := A.start
  answer st l := peerSimAnswer K D A codec (count l) st
  output st := pure st

end PeerSim

section MultPeerClaim
variable [Field E] [Algebra Bit E]

/-- The coupling of `MultStatement` in peer mode. The real run and the run of `peerSim` agree. -/
def MultPeerCoupling (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (D : C.Coalition)
    (A : Adversary C E (Shares C Bit × Shares C Bit × ℕ) Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (x : C.Party → Shares C Bit × Shares C Bit × ℕ) (z : Aux) (Z : Distinguisher C A.State (Shares C Bit)),
    SameCount D (fun i => (x i).2.2) →
    WEq prims (distinguish (realExecution D A (Frand Bit) (1 + ReshareMode.peer.rounds) (multProtocol K .peer) x z) Z)
      (distinguish (idealExecution worldRoles.adversary D (FmultBit K .peer) (peerSim K D A bitCodec (·.1)) x z) Z)

theorem multPeer_of_coupling (prims : Primitives) (K : Constants C E) (h : MultPeerCoupling prims K) :
    SecurelyComputes prims (multProtocol K .peer) (1 + ReshareMode.peer.rounds) (Frand Bit) (FmultBit K .peer)
      (fun D x => SameCount D fun i => (x i).2.2) 0 fun _ => 0 := by
  intro D A
  refine ⟨peerSim K D A bitCodec (·.1), fun x z Z q hx hq => ⟨?_, ?_⟩⟩
  · obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
    apply hasHashQueryBound_of_costLe
    unfold distinguish idealExecution
    simp only [FmultBit, Fmult, sample, simulateQ_bind, simulateQ_leak_add, simulateQ_pure, bind_assoc]
    rw [simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ _)]
    simp only [StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_mk, bind_assoc, pure_bind, worldRoles,
      liftComp_pure, counted_pure, map_bind, bind_map_left]
    simp only [peerSim, peerSimAnswer, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure, pure_bind,
      map_bind, bind_map_left, map_pure]
    exact CostLe.mono prims (CostLe.bind prims (CostLe.of_counted prims _ _ (hs _ _)) fun st =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (ha _ _)) fun a =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun f' =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun fp =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (hr _ _)) fun b =>
      CostLe.bind prims (CostLe.free_sample prims _) fun fr =>
      CostLe.of_counted prims _ _ (hz _)) (by simp only [ReshareMode.rounds] at hsum; omega)
  · rw [accepts_eq_of_WEq prims (h D A x z Z hx), sub_self, abs_zero]

end MultPeerClaim

section ExtendMultClaim
variable [Field E] [Algebra Bit E]
variable [SampleableType E]

/-- The count of the inner products, from the leak of `F_extendMult` to the corrupt operators. -/
def leakCount (l : C.Party → List (Product C E)) : ℕ := (C.parties.map fun c => (l c).length).foldl max 0

/-- The coupling of `ExtendMultStatement`. The real run and the run of `peerSim` agree. -/
def ExtendMultCoupling (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (D : C.Coalition)
    (A : Adversary C E (List (Product C E)) Unit (Shares C E × (C.Party → C.Party → ℕ → E)))
    (x : C.Party → List (Product C E)) (z : Aux) (Z : Distinguisher C A.State (Shares C E)),
    ShamirInputs K D x →
    WEq prims (distinguish (realExecution D A (Frand E) extendMultRounds (extendMultProtocol K) x z) Z)
      (distinguish (idealExecution worldRoles.adversary D (FextendMult K) (peerSim K D A (elementCodec K) leakCount) x z) Z)

theorem extendMult_of_coupling (prims : Primitives) (K : Constants C E) (h : ExtendMultCoupling prims K) :
    ExtendMultStatement prims K := by
  intro D A
  refine ⟨peerSim K D A (elementCodec K) leakCount, fun x z Z q hx hq => ⟨?_, ?_⟩⟩
  · obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
    simp only [coinRounds, extendMultRounds, multRounds] at hsum
    apply hasHashQueryBound_of_costLe
    unfold distinguish idealExecution
    simp only [FextendMult, Fmult, sample, simulateQ_bind, simulateQ_leak_add, simulateQ_pure, bind_assoc]
    rw [simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ _)]
    simp only [StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_mk, bind_assoc, pure_bind, worldRoles,
      liftComp_pure, counted_pure, map_bind, bind_map_left]
    simp only [peerSim, peerSimAnswer, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure, pure_bind,
      map_bind, bind_map_left, map_pure]
    exact CostLe.mono prims (CostLe.bind prims (CostLe.of_counted prims _ _ (hs _ _)) fun st =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (ha _ _)) fun a =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun f' =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun fp =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (hr _ _)) fun b =>
      CostLe.bind prims (CostLe.free_sample prims _) fun fr =>
      CostLe.of_counted prims _ _ (hz _)) (by omega)
  · rw [accepts_eq_of_WEq prims (h D A x z Z hx), sub_self, abs_zero]

end ExtendMultClaim

section ShiftDist

theorem evalDist_bind_add_uniform {α β : Type} [AddGroup α] [SampleableType α] (m : α) (f : α → ProbComp β) :
    𝒟[(do let y ← $ᵗ α; f (y + m))] = 𝒟[(do let y ← $ᵗ α; f y)] :=
  evalDist_ext fun z => probOutput_bind_add_right_uniform α m f z

theorem evalDist_bind_congr_all {α β : Type} (mx : ProbComp α) {f g : α → ProbComp β} (h : ∀ a, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  rw [evalDist_bind, evalDist_bind]; congr 1; funext a; exact h a

/-- A translation `τ w` of two uniform samples, averaged over a uniform `w`, moves a third sample by `W0`. -/
theorem evalDist_shift {α β γ δ : Type} [AddGroup α] [AddGroup β] [AddGroup γ]
    [SampleableType α] [SampleableType β] [SampleableType γ]
    (F : α → β → ProbComp δ) (G : α → β → γ → ProbComp δ) (τ : γ → α × β) (W0 : α → β → γ)
    (h : ∀ w x y, F (x + (τ w).1) (y + (τ w).2) = G x y (w + W0 x y)) :
    𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; F x y] = 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y w] := by
  have h1 : ∀ w, 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; F x y] =
      𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; G x y (w + W0 x y)] := fun w => by
    simp only [← h w]
    rw [evalDist_bind_add_uniform (τ w).1 (fun x => do let y ← $ᵗ β; F x (y + (τ w).2))]
    exact evalDist_bind_congr_all _ fun x => (evalDist_bind_add_uniform (τ w).2 (F x)).symm
  calc 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; F x y]
      = 𝒟[do let w ← $ᵗ γ; let x ← $ᵗ α; let y ← $ᵗ β; F x y] := (evalDist_uniform_bind_const _).symm
    _ = 𝒟[do let w ← $ᵗ γ; let x ← $ᵗ α; let y ← $ᵗ β; G x y (w + W0 x y)] := evalDist_bind_congr_all _ h1
    _ = 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y (w + W0 x y)] := by
        rw [evalDist_bind_bind_swap]
        exact evalDist_bind_congr_all _ fun x => evalDist_bind_bind_swap _ _ _
    _ = 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y w] :=
        evalDist_bind_congr_all _ fun x => evalDist_bind_congr_all _ fun y => evalDist_bind_add_uniform (W0 x y) (G x y)

end ShiftDist

section PeerValues
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

/-- Term `T` of `F_rand` at position `g`. -/
def randVal (D : C.Coalition) {c : ℕ} (known : Shares C R) (fresh : C.Term → Fin c → R) (g : ℕ) (T : C.Term) : R :=
  if KnownTo D.1 T then known T g else if h : g < c then fresh T ⟨g, h⟩ else 0

/-- The pair stream `Z_jk` of `F_rand` at position `g`. -/
def pairVal (D : C.Coalition) {c : ℕ} (knownPairs : C.Party → C.Party → ℕ → R) (freshPair : C.Pair → Fin c → R)
    (j k : C.Party) (g : ℕ) : R :=
  if h : j = k then 0 else if k ∈ D.1 then knownPairs k j g else
    if h' : g < c then freshPair (C.pairOf j k h) ⟨g, h'⟩ else 0

/-- `u_j` of a peer reshare at position `g`. -/
def uVal (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (j : C.Party) (g : ℕ) : R :=
  v j g + ∑ k ∈ Finset.univ.erase j, pairVal D knownPairs freshPair j k g +
    ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = j), randVal D known fresh g T

/-- Term `T` after a peer reshare in the view of operator `i`, where corrupt `j` sends `sent j i`. -/
def termVal (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) (T : C.Term) (g : ℕ) : R :=
  if T ∈ filledTerms K then ∑ j ∈ Finset.univ.filter (K.filled · = T),
      (if j ∈ D.1 then codec.unpack (sent j i) g else uVal K D known knownPairs fresh freshPair v j g)
  else randVal D known fresh g T

theorem frandShare_fst (D : C.Coalition) {c : ℕ} (known : Shares C R) (knownPairs : C.Party → C.Party → ℕ → R)
    (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R) (i : C.Party) (T : C.Term) (g : ℕ)
    (hi : i ∈ C.holders T) : (frandShare D c known knownPairs fresh freshPair i).1 T g = randVal D known fresh g T := by
  simp only [frandShare, hi, if_true, randVal]
  split_ifs <;> simp_all

theorem frandShare_snd (D : C.Coalition) {c : ℕ} (known : Shares C R) (knownPairs : C.Party → C.Party → ℕ → R)
    (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R) (j k : C.Party) (g : ℕ) :
    (frandShare D c known knownPairs fresh freshPair j).2 k g = pairVal D knownPairs freshPair j k g := by
  simp only [frandShare, pairVal]
  split_ifs <;> simp_all

theorem reshareU_frandShare (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (j : C.Party) (g : ℕ) :
    reshareU K (localContext j) (frandShare D c known knownPairs fresh freshPair j).1
      (frandShare D c known knownPairs fresh freshPair j).2 (v j) g = uVal K D known knownPairs fresh freshPair v j g := by
  unfold reshareU uVal
  simp only [localContext, frandShare_snd]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' := (Finset.mem_filter.mp hT).2
  exact frandShare_fst D known knownPairs fresh freshPair j T g (hT'.2 ▸ K.owner_held T)

/-- The codec reads back what it packs. -/
def CodecRoundTrip (codec : Codec C E R) : Prop :=
  ∀ (l : List R) (g : ℕ), codec.unpack (some (codec.pack l)) g = l.getD g 0 ∧ Msg.isAbort (some (codec.pack l)) = false

theorem bitCodec_roundTrip : CodecRoundTrip (C := C) (E := E) bitCodec := fun l g => ⟨rfl, rfl⟩

theorem elementCodec_roundTrip (K : Constants C E) : CodecRoundTrip (elementCodec K) := fun l g => ⟨rfl, rfl⟩

theorem reshareZ_frandShare (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (g : ℕ) :
    let rnd := frandShare D c known knownPairs fresh freshPair
    reshareZ K (localContext i) codec (rnd i).1 (rnd i).2 (v i) c
        (fun k => if k ∈ D.1 then sent k i else reshareOut K (localContext k) codec (rnd k).1 (rnd k).2 (v k) c i) T g =
      if i ∉ C.holders T ∨ c ≤ g then 0 else termVal K D codec known knownPairs fresh freshPair v sent i T g := by
  intro rnd
  unfold reshareZ termVal
  simp only [localContext]
  split_ifs with h1 h2
  · rfl
  · push Not at h1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjT := (Finset.mem_filter.mp hj).2
    by_cases hji : j = i
    · subst hji; simp only [if_true, hi, if_false]; exact reshareU_frandShare K D known knownPairs fresh freshPair v j g
    · simp only [hji, if_false]
      by_cases hjD : j ∈ D.1
      · simp [hjD]
      · simp only [hjD, if_false, reshareOut, localContext]
        rw [if_pos ⟨Ne.symm hji, hjT ▸ h1.1⟩, (hcodec _ g).1, vector_getD _ _ g h1.2]
        exact reshareU_frandShare K D known knownPairs fresh freshPair v j g
  · push Not at h1
    exact frandShare_fst D known knownPairs fresh freshPair i T g h1.1

/-- An honest inbox of a peer reshare aborts only on an abort frame of a corrupt operator. -/
theorem anyAbort_reshareOut (K : Constants C E) (D : C.Coalition) (codec : Codec C E R) (hcodec : CodecRoundTrip codec)
    (rnd : C.Party → PrssOutput C R) (v : C.Party → ℕ → R) (c : ℕ) (sent : C.Party → Option (Msg E)) (i : C.Party) :
    anyAbort (fun k => if k ∈ D.1 then sent k else reshareOut K (localContext k) codec (rnd k).1 (rnd k).2 (v k) c i) =
      anyAbort (fun k => if k ∈ D.1 then sent k else none) := by
  unfold anyAbort
  congr 1; funext k
  by_cases hk : k ∈ D.1
  · simp [hk]
  · simp only [hk, if_false, reshareOut]
    split_ifs
    · exact (hcodec _ 0).2
    · rfl

end PeerValues

section PeerSum
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

/-- Each pair stream enters the sum of all honest `u_j` twice. -/
theorem sum_pairs_eq_zero [CharP R 2] (S : Finset C.Party) (f : C.Pair → R) :
    ∑ j ∈ S, ∑ k ∈ S, (if h : j = k then 0 else f (C.pairOf j k h)) = 0 := by
  set a : C.Party → C.Party → R := fun j k => if h : j = k then 0 else f (C.pairOf j k h)
  have hsym : ∀ j k, a j k = a k j := fun j k => by
    simp only [a]
    by_cases h : j = k
    · subst h; rfl
    · rw [dif_neg h, dif_neg (Ne.symm h), pairOf_comm]
  have hsplit : ∀ j k, a j k = (if j < k then a j k else 0) + (if k < j then a j k else 0) := fun j k => by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst h; simp [a]
    · simp [h, not_lt.mpr h.le]
  change ∑ j ∈ S, ∑ k ∈ S, a j k = 0
  simp only [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hsplit j k, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j k => if k < j then a j k else 0)]
  simp only [hsym _ _]
  exact CharTwo.add_self_eq_zero _

/-- The additive attack of a peer reshare: the corrupt pair streams, the unfilled terms with a corrupt
owner, and the values that corrupt fillers send to the reference holders. -/
def advVal (K : Constants C E) (D : C.Coalition) (codec : Codec C E R) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (ref : C.Term → C.Party)
    (g : ℕ) : R :=
  ∑ j ∈ Finset.univ.filter (· ∉ D.1), ∑ k ∈ D.1, knownPairs k j g +
    ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∈ D.1), known T g +
    ∑ k ∈ D.1, codec.unpack (sent k (ref (K.filled k))) g

/-- The terms after a peer reshare share the honest inputs plus the additive attack (GS20, Lemma 4). -/
theorem sum_termVal [CharP R 2] (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R)
    (known : Shares C R) (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R)
    (freshPair : C.Pair → Fin c → R) (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E))
    (ref : C.Term → C.Party) (g : ℕ) :
    ∑ T, termVal K D codec known knownPairs fresh freshPair v sent (ref T) T g =
      ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g + advVal K D codec known knownPairs sent ref g := by
  set u := uVal K D known knownPairs fresh freshPair v
  set rv := randVal D known fresh g
  have hfill : ∑ T ∈ filledTerms K, ∑ j ∈ Finset.univ.filter (K.filled · = T),
      (if j ∈ D.1 then codec.unpack (sent j (ref T)) g else u j g) =
      ∑ j, if j ∈ D.1 then codec.unpack (sent j (ref (K.filled j))) g else u j g := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := filledTerms K) (g := K.filled)
      (fun j _ => by simp [filledTerms])]
    refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.mp hj).2]
  have hpairs : ∑ j ∈ Finset.univ.filter (· ∉ D.1), ∑ k ∈ Finset.univ.erase j, pairVal D knownPairs freshPair j k g =
      ∑ j ∈ Finset.univ.filter (· ∉ D.1), ∑ k ∈ D.1, knownPairs k j g := by
    have h1 : ∀ j ∈ Finset.univ.filter (· ∉ D.1), ∑ k ∈ Finset.univ.erase j, pairVal D knownPairs freshPair j k g =
        ∑ k ∈ D.1, knownPairs k j g + ∑ k ∈ Finset.univ.filter (· ∉ D.1),
          (if h : j = k then 0 else (fun pr => if h' : g < c then freshPair pr ⟨g, h'⟩ else 0) (C.pairOf j k h)) := by
      intro j hj
      have hjD := (Finset.mem_filter.mp hj).2
      rw [Finset.sum_erase _ (by simp [pairVal])]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ D.1)]
      congr 1
      · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [pairVal]
        rw [dif_neg (fun h : j = k => hjD (h ▸ hk)), if_pos hk]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hkD := (Finset.mem_filter.mp hk).2
        simp only [pairVal]
        split_ifs <;> rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
      sum_pairs_eq_zero (C := C) _ (fun pr => if h' : g < c then freshPair pr ⟨g, h'⟩ else 0), add_zero]
  have hown : ∑ j ∈ Finset.univ.filter (· ∉ D.1),
      ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = j), rv T =
      ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∉ D.1), rv T := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∉ D.1))
      (t := Finset.univ.filter (· ∉ D.1)) (g := K.owner) (fun T hT => by simp at hT ⊢; exact hT.2)]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr ?_ fun _ _ => rfl
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    constructor
    · rintro ⟨hT, rfl⟩; exact ⟨⟨hT, hj⟩, rfl⟩
    · rintro ⟨⟨hT, -⟩, rfl⟩; exact ⟨hT, rfl⟩
  have hu : ∑ j ∈ Finset.univ.filter (· ∉ D.1), u j g =
      ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g + ∑ j ∈ Finset.univ.filter (· ∉ D.1), ∑ k ∈ D.1, knownPairs k j g +
        ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∉ D.1), rv T := by
    simp only [u, uVal, Finset.sum_add_distrib, hpairs]
    rw [hown]
  have hunf : ∑ T ∈ Finset.univ.filter (· ∉ filledTerms K), rv T =
      ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∉ D.1), rv T +
        ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∈ D.1), known T g := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun T => K.owner T ∈ D.1), add_comm]
    simp only [Finset.filter_filter]
    congr 1
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT' := (Finset.mem_filter.mp hT).2
    simp only [rv, randVal]
    have hk : KnownTo D.1 T := ⟨K.owner T, hT'.2, K.owner_held T⟩
    rw [if_pos hk]
  have hsplit : ∑ j, (if j ∈ D.1 then codec.unpack (sent j (ref (K.filled j))) g else u j g) =
      ∑ k ∈ D.1, codec.unpack (sent k (ref (K.filled k))) g + ∑ j ∈ Finset.univ.filter (· ∉ D.1), u j g := by
    rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  unfold termVal
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, hfill, hsplit, hu]
  change _ + ∑ T ∈ Finset.univ.filter (· ∉ filledTerms K), rv T = _
  rw [hunf]
  unfold advVal
  have h2 : ∀ a : R, a + a = 0 := CharTwo.add_self_eq_zero
  linear_combination h2 (∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T ∉ D.1), rv T)

end PeerSum

section PeerShift
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

/-- The pair streams that move `δ k` into `u_k` for each `k ≠ p`, through the pair of `k` and `p`. -/
def pairShift {M : Type} [Zero M] (p : C.Party) (δ : C.Party → M) (pr : C.Pair) : M :=
  if pr.1.1 = p then δ pr.1.2 else if pr.1.2 = p then δ pr.1.1 else 0

theorem pairShift_pairOf {M : Type} [Zero M] (p : C.Party) (δ : C.Party → M) (i j : C.Party) (h : i ≠ j) :
    pairShift p δ (C.pairOf i j h) = if i = p then δ j else if j = p then δ i else 0 := by
  unfold pairShift Committee.pairOf
  split_ifs <;> simp_all

theorem randVal_add (D : C.Coalition) {c : ℕ} (known : Shares C R) (fresh Δ : C.Term → Fin c → R) (g : ℕ)
    (hg : g < c) (T : C.Term) :
    randVal D known (fresh + Δ) g T = randVal D known fresh g T + (if KnownTo D.1 T then 0 else Δ T ⟨g, hg⟩) := by
  unfold randVal
  split_ifs <;> simp

theorem pairVal_add (D : C.Coalition) {c : ℕ} (knownPairs : C.Party → C.Party → ℕ → R)
    (freshPair q : C.Pair → Fin c → R) (j k : C.Party) (g : ℕ) (hg : g < c) :
    pairVal D knownPairs (freshPair + q) j k g = pairVal D knownPairs freshPair j k g +
      (if h : j = k then 0 else if k ∈ D.1 then 0 else q (C.pairOf j k h) ⟨g, hg⟩) := by
  unfold pairVal
  split_ifs <;> simp

/-- `u_j` after a translation of the terms by `Δ` and of the pair streams by `pairShift p δ`. -/
theorem uVal_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh Δ : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (p : C.Party) (hp : p ∉ D.1) (δ : C.Party → Fin c → R) (hδ : ∀ k ∈ D.1, δ k = 0)
    (v : C.Party → ℕ → R) (j : C.Party) (hj : j ∉ D.1) (g : ℕ) (hg : g < c) :
    uVal K D known knownPairs (fresh + Δ) (freshPair + pairShift p δ) v j g =
      uVal K D known knownPairs fresh freshPair (fun _ _ => 0) j g + v j g +
        (if j = p then ∑ k ∈ Finset.univ.erase p, δ k ⟨g, hg⟩ else δ j ⟨g, hg⟩) +
        ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = j),
          (if KnownTo D.1 T then 0 else Δ T ⟨g, hg⟩) := by
  have hextra : ∑ k ∈ Finset.univ.erase j,
      (if h : j = k then 0 else if k ∈ D.1 then 0 else pairShift p δ (C.pairOf j k h) ⟨g, hg⟩) =
      if j = p then ∑ k ∈ Finset.univ.erase p, δ k ⟨g, hg⟩ else δ j ⟨g, hg⟩ := by
    have hterm : ∀ k ∈ Finset.univ.erase j,
        (if h : j = k then 0 else if k ∈ D.1 then 0 else pairShift p δ (C.pairOf j k h) ⟨g, hg⟩) =
        if j = p then δ k ⟨g, hg⟩ else if k = p then δ j ⟨g, hg⟩ else 0 := by
      intro k hk
      rw [dif_neg (Finset.ne_of_mem_erase hk).symm, pairShift_pairOf]
      by_cases hkD : k ∈ D.1
      · have hkp : k ≠ p := fun h => hp (h ▸ hkD)
        simp [hkD, hδ k hkD, hkp]
      · simp only [hkD, if_false]
        split_ifs <;> rfl
    rw [Finset.sum_congr rfl hterm]
    split_ifs with hjp
    · subst hjp; rfl
    · rw [Finset.sum_ite_eq']
      simp [Ne.symm hjp]
  unfold uVal
  simp only [pairVal_add D knownPairs freshPair _ j _ g hg, randVal_add D known fresh Δ g hg,
    Finset.sum_add_distrib, hextra]
  ring

end PeerShift

section FmultIdeal
variable {R : Type} [Field R] [SampleableType R]

/-- The outputs of `F_mult` from the reply of the simulator and the fresh terms. -/
def fmultOut {In : Type} [Inhabited In] (D : C.Coalition) (count : In → ℕ)
    (filled : In → C.Term → ℕ → Option C.Party) (share : C.Party → In → ℕ → R) (inputs : C.Party → Option In)
    (reply : (ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party)
    (fresh : C.Term → Fin (count (firstInput inputs)) → R) : C.Party → Option (Shares C R) :=
  let width := count (firstInput inputs)
  let base : Shares C R := fun T g =>
    if KnownTo D.1 T then reply.2.1 T g else if h : g < width then fresh T ⟨g, h⟩ else 0
  let product := fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), ((inputs i).map fun x => share i x g).getD 0
  let z : Shares C R := fun T g => if lackedTerm D.1 = some T then
    product g + reply.1 g - ∑ T' ∈ Finset.univ.erase T, base T' g else base T g
  fun i => if i ∈ D.1 ∨ i ∉ reply.2.2.2 then none else
    some fun T g => if i ∈ C.holders T ∧ g < width then
      z T g + (if ∃ j ∈ D.1, filled (firstInput inputs) T g = some j then reply.2.2.1 i T g else 0) else 0

theorem idealExecution_Fmult {In Lk σ : Type} [Inhabited In] (D : C.Coalition) (count : In → ℕ)
    (filled : In → C.Term → ℕ → Option C.Party) (share : C.Party → In → ℕ → R)
    (view : Finset C.Party → (C.Party → Option In) → Lk)
    (Sim : Simulator (C := C) (LocalSpec C) In Lk ((ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party) σ)
    (x : C.Party → In) (z : Aux) :
    let inputs := fun i => if i ∈ D.1 then none else some (x i)
    idealExecution worldRoles.adversary D (Fmult count filled share view) Sim x z = (do
      let st ← counted (liftComp (Sim.start (corruptInputs D x) z) (SimulatorSpec C))
      let ans ← counted (liftComp (Sim.answer st (view D.1 inputs)) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin (count (firstInput inputs)) → R)) (LocalSpec C))
      let out ← counted (liftComp (Sim.output ans.1) (SimulatorSpec C))
      pure (out, fmultOut D count filled share inputs ans.2 fresh)) := by
  intro inputs
  unfold idealExecution
  simp only [Fmult, sample, simulateQ_bind, simulateQ_leak_add]
  rw [simulateQ_liftComp_prob _ (fun _ => rfl) ($ᵗ _)]
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_lift, StateT.run_mk, bind_assoc, pure_bind, worldRoles,
    map_bind, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  rfl

end FmultIdeal

section PeerCore
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

theorem exists_honest_holder (D : C.Coalition) (T : C.Term) : ∃ i, i ∈ C.holders T ∧ i ∉ D.1 := by
  have hcard : D.1.card < (C.holders T).card := by
    rw [Committee.holders, Finset.card_compl, T.2, Fintype.card_fin]
    have := D.2; have := C.one_le_t; simp only [Committee.n]; omega
  obtain ⟨i, hi, hiD⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨i, hi, hiD⟩

theorem refHolder_spec (D : C.Coalition) (T : C.Term) : refHolder D T ∈ C.holders T ∧ refHolder D T ∉ D.1 := by
  obtain ⟨i, hi, hiD⟩ := exists_honest_holder D T
  have hmem : i ∈ C.parties.filter fun i => i ∈ C.holders T ∧ i ∉ D.1 :=
    List.mem_filter.mpr ⟨by simp [Committee.parties], by simp [hi, hiD]⟩
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have ha : a ∈ C.parties.filter fun i => i ∈ C.holders T ∧ i ∉ D.1 := by rw [hl]; simp
  unfold refHolder
  rw [hl, List.head?_cons, Option.getD_some]
  simpa using (List.mem_filter.mp ha).2

theorem filler_peer_corrupt (K : Constants C E) (D : C.Coalition) (T : C.Term) (g : ℕ) :
    (∃ j ∈ D.1, filler K .peer T g = some j) ↔ ∃ j ∈ D.1, K.filled j = T := by
  simp only [filler]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by simpa using List.find?_some h⟩
  · rintro ⟨j, hj, rfl⟩
    have hs : (C.parties.find? (K.filled · = K.filled j)).isSome := by
      rw [List.find?_isSome]; exact ⟨j, by simp [Committee.parties], by simp⟩
    obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.mp hs
    have := K.filled.injective (by simpa using List.find?_some hj')
    exact ⟨j, hj, by rw [hj', this]⟩

/-- A term with no corrupt filler has the same value in every honest view. -/
theorem termVal_viewer (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent sent' : C.Party → C.Party → Option (Msg E)) (i i' : C.Party) (T : C.Term) (g : ℕ)
    (hT : ¬ ∃ j ∈ D.1, K.filled j = T) :
    termVal K D codec known knownPairs fresh freshPair v sent i T g =
      termVal K D codec known knownPairs fresh freshPair v sent' i' T g := by
  unfold termVal
  split_ifs
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjD : j ∉ D.1 := fun h => hT ⟨j, h, (Finset.mem_filter.mp hj).2⟩
    simp [hjD]
  · rfl

end PeerCore

section PeerTranslation
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

/-- What the translation for `w` adds to `u_j`, namely `w` on the term `T_j` if no corrupt operator holds it. -/
def targetShift (K : Constants C E) (D : C.Coalition) {c : ℕ} (w : C.Term → Fin c → R) (j : C.Party) : Fin c → R :=
  if KnownTo D.1 (K.filled j) then 0 else w (K.filled j)

/-- The translation of the unfilled hidden terms other than `T0` by `w`. -/
def termShift0 (K : Constants C E) (D : C.Coalition) (T0 : C.Term) {c : ℕ} (w : C.Term → Fin c → R) (T : C.Term) :
    Fin c → R :=
  if T ∉ filledTerms K ∧ ¬ KnownTo D.1 T ∧ T ≠ T0 then w T else 0

/-- What a translation `Δ` of the terms adds to `u_j` through the terms that `j` owns. -/
def ownShift (K : Constants C E) (D : C.Coalition) {c : ℕ} (Δ : C.Term → Fin c → R) (j : C.Party) : Fin c → R :=
  ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = j), if KnownTo D.1 T then 0 else Δ T

/-- The pair-stream translation for `u_j`, for each honest `j ≠ p`. -/
def pairDelta (K : Constants C E) (D : C.Coalition) (T0 : C.Term) (p : C.Party) {c : ℕ} (v : C.Party → ℕ → R)
    (w : C.Term → Fin c → R) (j : C.Party) : Fin c → R :=
  if j ∈ D.1 ∨ j = p then 0 else
    targetShift K D w j - (fun g => v j g.val) - ownShift K D (termShift0 K D T0 w) j

/-- The term translation: `termShift0`, and on an unfilled `T0` the rest of the change of `u_p`. -/
def termShift (K : Constants C E) (D : C.Coalition) (T0 : C.Term) (p : C.Party) {c : ℕ} (v : C.Party → ℕ → R)
    (w : C.Term → Fin c → R) (T : C.Term) : Fin c → R :=
  termShift0 K D T0 w T + if T0 ∉ filledTerms K ∧ T = T0 then
    targetShift K D w p - (fun g => v p g.val) - ownShift K D (termShift0 K D T0 w) p -
      ∑ k ∈ Finset.univ.erase p, pairDelta K D T0 p v w k
  else 0

theorem uVal_termShift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (p : C.Party) (hp : p ∉ D.1)
    (hpf : T0 ∈ filledTerms K → K.filled p = T0) (hpo : T0 ∉ filledTerms K → K.owner T0 = p)
    (v : C.Party → ℕ → R) (w : C.Term → Fin c → R) (j : C.Party) (hj : j ∉ D.1) (hjT : K.filled j ≠ T0)
    (g : ℕ) (hg : g < c) :
    uVal K D known knownPairs (fresh + termShift K D T0 p v w) (freshPair + pairShift p (pairDelta K D T0 p v w)) v j g =
      uVal K D known knownPairs fresh freshPair (fun _ _ => 0) j g + targetShift K D w j ⟨g, hg⟩ := by
  set γ := targetShift K D w p - (fun g => v p g.val) - ownShift K D (termShift0 K D T0 w) p -
      ∑ k ∈ Finset.univ.erase p, pairDelta K D T0 p v w k
  have hown : ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = j),
      (if KnownTo D.1 T then 0 else termShift K D T0 p v w T ⟨g, hg⟩) =
      ownShift K D (termShift0 K D T0 w) j ⟨g, hg⟩ + if T0 ∉ filledTerms K ∧ K.owner T0 = j then γ ⟨g, hg⟩ else 0 := by
    have hsplit : ∀ T, (if KnownTo D.1 T then 0 else termShift K D T0 p v w T ⟨g, hg⟩) =
        (if KnownTo D.1 T then 0 else termShift0 K D T0 w T) ⟨g, hg⟩ +
          if T = T0 then (if T0 ∉ filledTerms K then γ ⟨g, hg⟩ else 0) else 0 := fun T => by
      unfold termShift
      by_cases hk : KnownTo D.1 T
      · have hne : T ≠ T0 := fun h => hT0 (h ▸ hk)
        simp [hk, hne]
      · by_cases hT : T = T0
        · subst hT
          by_cases hf : T ∈ filledTerms K <;> simp [hk, hf, γ]
        · simp [hk, hT]
    rw [Finset.sum_congr rfl fun T _ => hsplit T, Finset.sum_add_distrib, Finset.sum_ite_eq']
    unfold ownShift
    rw [Finset.sum_apply]
    congr 1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> tauto
  have hδ : ∀ k ∈ D.1, pairDelta K D T0 p v w k = 0 := fun k hk => by simp [pairDelta, hk]
  rw [uVal_shift K D known knownPairs fresh _ freshPair p hp _ hδ v j hj g hg, hown]
  by_cases hf : T0 ∈ filledTerms K
  · have hjp : j ≠ p := fun h => hjT (h ▸ hpf hf)
    simp only [hjp, if_false, hf, not_true_eq_false, false_and, add_zero, pairDelta, hj, false_or]
    simp only [Pi.sub_apply]
    ring
  · by_cases hjp : j = p
    · subst hjp
      simp only [if_true, hf, not_false_eq_true, hpo hf, and_self, γ, Finset.sum_apply, Pi.sub_apply]
      ring
    · have hoj : ¬ K.owner T0 = j := fun h => hjp (h.symm.trans (hpo hf))
      simp only [hjp, if_false, hoj, and_false, add_zero, pairDelta, hj, false_or, Pi.sub_apply]
      ring

end PeerTranslation

section PeerPointwise
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

theorem termVal_filled (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (i j : C.Party) (g : ℕ) :
    termVal K D codec known knownPairs fresh freshPair v sent i (K.filled j) g =
      if j ∈ D.1 then codec.unpack (sent j i) g else uVal K D known knownPairs fresh freshPair v j g := by
  have hfib : Finset.univ.filter (K.filled · = K.filled j) = {j} := by
    ext k; simp [K.filled.injective.eq_iff]
  unfold termVal
  rw [if_pos (by simp [filledTerms]), hfib, Finset.sum_singleton]

theorem termVal_unfilled (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) (T : C.Term) (g : ℕ)
    (hT : T ∉ filledTerms K) :
    termVal K D codec known knownPairs fresh freshPair v sent i T g = randVal D known fresh g T := by
  unfold termVal; rw [if_neg hT]

/-- The setting of the translation: the lacked term `T0` and the pivot `p`. -/
structure Pivot (K : Constants C E) (D : C.Coalition) (T0 : C.Term) (p : C.Party) : Prop where
  lacked : lackedTerm D.1 = some T0
  hidden : ¬ KnownTo D.1 T0
  honest : p ∉ D.1
  filled : T0 ∈ filledTerms K → K.filled p = T0
  owner : T0 ∉ filledTerms K → K.owner T0 = p

theorem exists_pivot (K : Constants C E) (D : C.Coalition) : ∃ T0 p, Pivot K D T0 p := by
  obtain ⟨T0, hT0, hk⟩ := lackedTerm_spec D
  by_cases hf : T0 ∈ filledTerms K
  · obtain ⟨p, -, hp⟩ := Finset.mem_map.mp hf
    exact ⟨T0, p, hT0, hk, fun hD => hk ⟨p, hD, hp ▸ K.filled_held p⟩, fun _ => hp, fun h => absurd hf h⟩
  · exact ⟨T0, K.owner T0, hT0, hk, fun hD => hk ⟨_, hD, K.owner_held T0⟩, fun h => absurd h hf, fun _ => rfl⟩

/-- A term other than `T0` after the translation for `w`. -/
theorem termVal_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    {T0 : C.Term} {p : C.Party} (hpiv : Pivot K D T0 p) (v : C.Party → ℕ → R) (w : C.Term → Fin c → R)
    (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) (T : C.Term) (hT : T ≠ T0) (g : ℕ) (hg : g < c) :
    termVal K D codec known knownPairs (fresh + termShift K D T0 p v w)
        (freshPair + pairShift p (pairDelta K D T0 p v w)) v sent i T g =
      termVal K D codec known knownPairs fresh freshPair (fun _ _ => 0) sent i T g +
        if KnownTo D.1 T then 0 else w T ⟨g, hg⟩ := by
  by_cases hf : T ∈ filledTerms K
  · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hf
    rw [termVal_filled, termVal_filled]
    by_cases hj : j ∈ D.1
    · have hk : KnownTo D.1 (K.filled j) := ⟨j, hj, K.filled_held j⟩
      simp [hj, hk]
    · simp only [hj, if_false]
      rw [uVal_termShift K D known knownPairs fresh freshPair T0 hpiv.hidden p hpiv.honest hpiv.filled hpiv.owner
        v w j hj hT g hg]
      unfold targetShift
      split_ifs <;> simp
  · rw [termVal_unfilled _ _ _ _ _ _ _ _ _ _ _ _ hf, termVal_unfilled _ _ _ _ _ _ _ _ _ _ _ _ hf,
      randVal_add D known fresh _ g hg]
    congr 1
    unfold termShift termShift0
    by_cases hk : KnownTo D.1 T
    · simp [hk]
    · simp [hk, hf, hT]

/-- The reply of the peer-reshare simulator, from its `F_rand` samples and the corrupt messages. -/
def peerReply (K : Constants C E) (D : C.Coalition) (codec : Codec C E R) {n : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin n → R) (freshPair : C.Pair → Fin n → R)
    (sent : C.Party → C.Party → Option (Msg E)) : (ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party :=
  let rnd := frandShare D n known knownPairs fresh freshPair
  let out := fun i => reshareOut K (localContext i) codec (rnd i).1 (rnd i).2 (fun _ => 0) n
  let inbox := fun i k => if k ∈ D.1 then sent k i else out k i
  let zf := fun i => reshareZ K (localContext i) codec (rnd i).1 (rnd i).2 (fun _ => 0) n (inbox i)
  let known' : Shares C R := fun T => zf (refHolder D T) T
  (fun g => ∑ T, known' T g, known', fun i T g => zf i T g - known' T g,
    Finset.univ.filter fun i => i ∉ D.1 ∧ anyAbort (inbox i) = false)

theorem peerSimAnswer_eq {I : Type} [SampleableType R] (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R))) (codec : Codec C E R) (n : ℕ)
    (st : A.State) :
    peerSimAnswer K D A codec n st = (do
      let a ← A.answer st ()
      let fresh ← liftComp ($ᵗ (C.Term → Fin n → R)) (LocalSpec C)
      let freshPair ← liftComp ($ᵗ (C.Pair → Fin n → R)) (LocalSpec C)
      let rnd := frandShare D n a.2.1 a.2.2 fresh freshPair
      let b ← A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
        reshareOut K (localContext i) codec (rnd i).1 (rnd i).2 (fun _ => 0) n c' else none
      pure (b.1, peerReply K D codec a.2.1 a.2.2 fresh freshPair b.2)) := rfl

/-- The outputs of `F_mult` with the width `c`. -/
def idealOut (D : C.Coalition) {c : ℕ} (filled : C.Term → ℕ → Option C.Party) (product : ℕ → R)
    (reply : (ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party) (fresh : C.Term → Fin c → R) :
    C.Party → Option (Shares C R) :=
  let base : Shares C R := fun T g =>
    if KnownTo D.1 T then reply.2.1 T g else if h : g < c then fresh T ⟨g, h⟩ else 0
  let z : Shares C R := fun T g => if lackedTerm D.1 = some T then
    product g + reply.1 g - ∑ T' ∈ Finset.univ.erase T, base T' g else base T g
  fun i => if i ∈ D.1 ∨ i ∉ reply.2.2.2 then none else
    some fun T g => if i ∈ C.holders T ∧ g < c then
      z T g + (if ∃ j ∈ D.1, filled T g = some j then reply.2.2.1 i T g else 0) else 0

/-- The messages of the honest operators to the corrupt ones in a peer reshare. -/
def realMsgs (K : Constants C E) (D : C.Coalition) (codec : Codec C E R) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) : C.Party → C.Party → Option (Msg E) :=
  let rnd := frandShare D c known knownPairs fresh freshPair
  fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then reshareOut K (localContext i) codec (rnd i).1 (rnd i).2 (v i) c c' else none

/-- The outputs of the honest operators in a peer reshare. -/
def realOut (K : Constants C E) (D : C.Coalition) (codec : Codec C E R) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) : C.Party → Option (Shares C R) :=
  let rnd := frandShare D c known knownPairs fresh freshPair
  let out := fun i => reshareOut K (localContext i) codec (rnd i).1 (rnd i).2 (v i) c
  fun i => if i ∈ D.1 then none else
    let inbox : Mail C E := fun k => if k ∈ D.1 then sent k i else out k i
    if anyAbort inbox then none else some (reshareZ K (localContext i) codec (rnd i).1 (rnd i).2 (v i) c inbox)

end PeerPointwise

section PeerMain
variable [Field E] [Algebra Bit E] {R : Type} [Field R]

theorem reshareZ_frandShare' (K : Constants C E) (D : C.Coalition) {c : ℕ} (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    (v : C.Party → ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (g : ℕ) :
    reshareZ K (localContext i) codec (frandShare D c known knownPairs fresh freshPair i).1
        (frandShare D c known knownPairs fresh freshPair i).2 (v i) c
        (fun k => if k ∈ D.1 then sent k i else reshareOut K (localContext k) codec
          (frandShare D c known knownPairs fresh freshPair k).1 (frandShare D c known knownPairs fresh freshPair k).2
          (v k) c i) T g =
      if i ∉ C.holders T ∨ c ≤ g then 0 else termVal K D codec known knownPairs fresh freshPair v sent i T g :=
  reshareZ_frandShare K D codec hcodec known knownPairs fresh freshPair v sent i hi T g

/-- After the translation for `w`, the honest messages to the corrupt operators are those of zero inputs. -/
theorem realMsgs_shift (K : Constants C E) (D : C.Coalition) (codec : Codec C E R) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    {T0 : C.Term} {p : C.Party} (hpiv : Pivot K D T0 p) (v : C.Party → ℕ → R) (w : C.Term → Fin c → R) :
    realMsgs K D codec known knownPairs (fresh + termShift K D T0 p v w)
        (freshPair + pairShift p (pairDelta K D T0 p v w)) v =
      realMsgs K D codec known knownPairs fresh freshPair (fun _ _ => 0) := by
  funext c' i
  unfold realMsgs
  split_ifs with h
  · unfold reshareOut
    split_ifs with h2
    · have hk : KnownTo D.1 (K.filled i) := ⟨c', h.1, h2.2⟩
      have hT : K.filled i ≠ T0 := fun he => hpiv.hidden (he ▸ hk)
      congr 2
      refine List.map_congr_left fun g hg => ?_
      have hg' : g < c := List.mem_range.mp hg
      rw [reshareU_frandShare, reshareU_frandShare (v := fun _ _ => 0),
        uVal_termShift K D known knownPairs fresh freshPair T0 hpiv.hidden p hpiv.honest hpiv.filled hpiv.owner
          v w i h.2 hT g hg']
      simp [targetShift, hk]
    · rfl
  · rfl

/-- After the translation for `w`, the honest outputs are those of `F_mult` on the simulator reply and
the fresh terms `w` plus the simulated hidden terms. -/
theorem realOut_shift [CharP R 2] (K : Constants C E) (D : C.Coalition) (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) {c : ℕ} (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin c → R) (freshPair : C.Pair → Fin c → R)
    {T0 : C.Term} {p : C.Party} (hpiv : Pivot K D T0 p) (v : C.Party → ℕ → R) (w : C.Term → Fin c → R)
    (filled : C.Term → ℕ → Option C.Party) (hfilled : ∀ T g, (∃ j ∈ D.1, filled T g = some j) ↔ ∃ j ∈ D.1, K.filled j = T)
    (product : ℕ → R) (hproduct : ∀ g, product g = ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
    (sent : C.Party → C.Party → Option (Msg E)) :
    realOut K D codec known knownPairs (fresh + termShift K D T0 p v w)
        (freshPair + pairShift p (pairDelta K D T0 p v w)) v sent =
      idealOut D filled product (peerReply K D codec known knownPairs fresh freshPair sent)
        (w + fun T g => termVal K D codec known knownPairs fresh freshPair (fun _ _ => 0) (fun _ _ => none)
          (refHolder D T) T g.val) := by
  funext i
  unfold realOut idealOut peerReply
  dsimp only
  by_cases hi : i ∈ D.1
  · simp [hi]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, anyAbort_reshareOut K D codec hcodec]
  by_cases hab : anyAbort (fun k => if k ∈ D.1 then sent k i else none) = true
  · simp [hi, hab]
  simp only [hi, if_false, hab, false_or, Finset.mem_filter, Finset.mem_univ, true_and, not_false_eq_true,
    Bool.not_eq_true, Bool.eq_false_iff.mpr hab, and_self, not_true_eq_false, Option.some.injEq]
  simp only [Bool.false_eq_true, if_false, Option.some.injEq]
  funext T g
  have href : ∀ T, refHolder D T ∉ D.1 := fun T => (refHolder_spec D T).2
  have hrefh : ∀ T, refHolder D T ∈ C.holders T := fun T => (refHolder_spec D T).1
  rw [reshareZ_frandShare' K D codec hcodec known knownPairs _ _ v sent i hi T g]
  by_cases hTg : i ∈ C.holders T ∧ g < c
  swap
  · rw [if_neg hTg, if_pos (by rw [not_and_or, not_lt] at hTg; exact hTg)]
  have hcg : ¬ c ≤ g := Nat.not_le.mpr hTg.2
  rw [if_pos hTg, if_neg (by simp [hTg.1, hcg])]
  have hz := reshareZ_frandShare' K D codec hcodec known knownPairs fresh freshPair (fun _ _ => 0) sent
  simp only [hz _ (href _), hz _ hi, hrefh, hTg.1, not_true_eq_false, false_or, hcg, if_false, dif_pos hTg.2,
    Pi.add_apply]
  have hshift := termVal_shift K D codec known knownPairs fresh freshPair hpiv v w sent
  have hbase : ∀ T', T' ≠ T0 → (if KnownTo D.1 T' then
      termVal K D codec known knownPairs fresh freshPair (fun _ _ => 0) sent (refHolder D T') T' g else
      w T' ⟨g, hTg.2⟩ + termVal K D codec known knownPairs fresh freshPair (fun _ _ => 0) (fun _ _ => none)
        (refHolder D T') T' g) =
      termVal K D codec known knownPairs (fresh + termShift K D T0 p v w)
        (freshPair + pairShift p (pairDelta K D T0 p v w)) v sent (refHolder D T') T' g := by
    intro T' hT'
    rw [hshift (refHolder D T') T' hT' g hTg.2]
    split_ifs with hk
    · rw [add_zero]
    · have hnf : ¬ ∃ j ∈ D.1, K.filled j = T' := fun ⟨j, hj, hjT⟩ => hk ⟨j, hj, hjT ▸ K.filled_held j⟩
      rw [termVal_viewer K D codec known knownPairs fresh freshPair _ (fun _ _ => none) sent, add_comm]
      exact hnf
  by_cases hT : T = T0
  · subst hT
    have hnf : ¬ ∃ j ∈ D.1, K.filled j = T := fun ⟨j, hj, hjT⟩ => hpiv.hidden ⟨j, hj, hjT ▸ K.filled_held j⟩
    rw [if_pos hpiv.lacked, if_neg (fun h => hnf ((hfilled T g).1 h)), add_zero,
      Finset.sum_congr rfl (fun T' hT' => hbase T' (Finset.ne_of_mem_erase hT'))]
    have hs1 := sum_termVal K D codec known knownPairs (fresh + termShift K D T p v w)
      (freshPair + pairShift p (pairDelta K D T p v w)) v sent (refHolder D) g
    have hs0 := sum_termVal K D codec known knownPairs fresh freshPair (fun _ _ => 0) sent (refHolder D) g
    simp only [Finset.sum_const_zero, zero_add] at hs0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T)] at hs1
    rw [termVal_viewer K D codec known knownPairs _ _ v sent sent i (refHolder D T) T g hnf, hs0, hproduct]
    linear_combination hs1
  · rw [if_neg (fun h => hT (Option.some.inj (h.symm.trans hpiv.lacked))), hbase T hT]
    by_cases hcf : ∃ j ∈ D.1, K.filled j = T
    · obtain ⟨j, hj, hjT⟩ := hcf
      have hk : KnownTo D.1 T := ⟨j, hj, hjT ▸ K.filled_held j⟩
      rw [if_pos ((hfilled T g).2 ⟨j, hj, hjT⟩), hshift i T hT g hTg.2, hshift (refHolder D T) T hT g hTg.2]
      simp only [if_pos hk, add_zero]
      ring
    · rw [if_neg (fun h => hcf ((hfilled T g).1 h)), add_zero]
      exact termVal_viewer K D codec known knownPairs _ _ v sent sent i (refHolder D T) T g hcf

end PeerMain

section PeerCoupling
variable [Field E] [Algebra Bit E] {R : Type} [Field R] [CharP R 2] [SampleableType R]

/-- The run of a peer reshare after `F_rand` and the run of `F_mult` with the simulator agree (GS20,
Lemmas 4 and 5). -/
theorem peer_coupling (prims : Primitives) (K : Constants C E) (D : C.Coalition) (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) {I : Type} (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R)))
    (Z : Distinguisher C A.State (Shares C R)) (start : OracleComp (WorldSpec C) A.State) (c : ℕ)
    (v : C.Party → ℕ → R) (filled : C.Term → ℕ → Option C.Party)
    (hfilled : ∀ T g, (∃ j ∈ D.1, filled T g = some j) ↔ ∃ j ∈ D.1, K.filled j = T)
    (product : ℕ → R) (hproduct : ∀ g, product g = ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g) :
    WEq prims
      (do
        let st ← start
        let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → R)) (LocalSpec C))
        let b ← counted (liftComp (A.round a.1 (realMsgs K D codec a.2.1 a.2.2 fresh freshPair v)) (SimulatorSpec C))
        counted (liftComp (Z (b.1, realOut K D codec a.2.1 a.2.2 fresh freshPair v b.2)) (SimulatorSpec C)))
      (do
        let st ← start
        let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → R)) (LocalSpec C))
        let freshF ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let b ← counted (liftComp (A.round a.1 (realMsgs K D codec a.2.1 a.2.2 fresh freshPair (fun _ _ => 0)))
          (SimulatorSpec C))
        counted (liftComp (Z (b.1, idealOut D filled product (peerReply K D codec a.2.1 a.2.2 fresh freshPair b.2)
          freshF)) (SimulatorSpec C))) := by
  obtain ⟨T0, p, hpiv⟩ := exists_pivot K D
  refine WEq.bind_right prims _ fun st => WEq.bind_right prims _ fun a => fun s => ?_
  simp only [world_run_free_bind]
  refine evalDist_shift _ _ (fun w => (termShift K D T0 p v w, pairShift p (pairDelta K D T0 p v w)))
    (fun fresh freshPair T g => termVal K D codec a.2.1 a.2.2 fresh freshPair (fun _ _ => 0) (fun _ _ => none)
      (refHolder D T) T g.val) fun w fresh freshPair => ?_
  dsimp only
  rw [realMsgs_shift K D codec a.2.1 a.2.2 fresh freshPair hpiv v w]
  simp only [realOut_shift K D codec hcodec a.2.1 a.2.2 fresh freshPair hpiv v w filled hfilled product hproduct]

end PeerCoupling

section MultPeerProof
variable [Field E] [Algebra Bit E]

theorem firstInput_honest {I : Type} [Inhabited I] (D : C.Coalition) (x : C.Party → I) :
    ∃ j, j ∉ D.1 ∧ firstInput (fun i => if i ∈ D.1 then none else some (x i)) = x j := by
  obtain ⟨i0, hi0⟩ := exists_honest D
  unfold firstInput
  have hmem : x i0 ∈ C.parties.filterMap (fun i => if i ∈ D.1 then none else some (x i)) :=
    List.mem_filterMap.mpr ⟨i0, by simp [Committee.parties], by simp [hi0]⟩
  obtain ⟨d, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hl, List.headD_cons]
  have hd : d ∈ C.parties.filterMap (fun i => if i ∈ D.1 then none else some (x i)) := by rw [hl]; simp
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hd
  by_cases hjD : j ∈ D.1
  · simp [hjD] at hj
  · exact ⟨j, hjD, by simpa [hjD] using hj.symm⟩

/-- The simulator samples on the counted copy are free samples, and the fresh terms of `F_mult` move
before the round. -/
theorem WEq.sim_samples (prims : Primitives) {α β γ δ ε : Type} (p : ProbComp α) (q : ProbComp β) (r : ProbComp γ)
    (ob : α → β → OracleComp (WorldSpec C) δ) (k : α → β → δ → γ → OracleComp (WorldSpec C) ε) :
    WEq prims (counted (liftComp (liftComp p (LocalSpec C)) (SimulatorSpec C)) >>= fun a =>
        counted (liftComp (liftComp q (LocalSpec C)) (SimulatorSpec C)) >>= fun b =>
        ob a b >>= fun d => free (liftComp r (LocalSpec C)) >>= fun c => k a b d c)
      (free (liftComp p (LocalSpec C)) >>= fun a => free (liftComp q (LocalSpec C)) >>= fun b =>
        free (liftComp r (LocalSpec C)) >>= fun c => ob a b >>= fun d => k a b d c) := by
  refine WEq.trans prims ((WEq.counted_sample prims p).bind_left prims _) ?_
  refine WEq.trans prims (WEq.bind_right prims _ fun a => (WEq.counted_sample prims q).bind_left prims _) ?_
  exact WEq.bind_right prims _ fun a => WEq.bind_right prims _ fun b => WEq.symm prims (WEq.free_swap prims _ _ _)

theorem fmultOut_eq {R : Type} [Field R] {In : Type} [Inhabited In] (D : C.Coalition) (count : In → ℕ)
    (filled : In → C.Term → ℕ → Option C.Party) (share : C.Party → In → ℕ → R) (inputs : C.Party → Option In)
    (reply : (ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party)
    (fresh : C.Term → Fin (count (firstInput inputs)) → R) :
    fmultOut D count filled share inputs reply fresh = idealOut D (filled (firstInput inputs))
      (fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), ((inputs i).map fun x => share i x g).getD 0) reply fresh := rfl

theorem multPeerCoupling (prims : Primitives) (K : Constants C E) : MultPeerCoupling prims K := by
  intro D A x z Z hx
  obtain ⟨j0, hj0, hfirst⟩ := firstInput_honest D x
  have hxc : ∀ i, i ∉ D.1 → (x i).2.2 = (x j0).2.2 := fun i hi => hx i j0 hi hj0
  unfold distinguish
  rw [realExecution_multPeer]
  have hc := firstInput_eq_of_same D (fun i => (x i).2.2) hx j0 hj0
  generalize firstInput (fun i => if i ∈ D.1 then none else some (x i).2.2) = c at hc ⊢
  subst hc
  unfold FmultBit
  rw [idealExecution_Fmult]
  simp only [peerSim, peerSimAnswer_eq, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure,
    pure_bind, worldRoles, fmultOut_eq]
  rw [hfirst]
  refine WEq.trans prims (WEq.of_eq prims ?hreal) (WEq.trans prims (peer_coupling prims K D bitCodec bitCodec_roundTrip A Z
    (counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))) (x j0).2.2
    (fun i => mulRep K (localContext i) (x i).1 (x i).2.1) (filler K .peer) (fun T g => filler_peer_corrupt K D T g)
    (fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), (((fun i => if i ∈ D.1 then none else some (x i)) i).map
      fun y => mulRep K (localContext i) y.1 y.2.1 g).getD 0) ?hprod) ?hideal)
  case hprod =>
    intro g
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [(Finset.mem_filter.mp hi).2]
  case hreal =>
    refine bind_congr' _ fun st => bind_congr' _ fun a => bind_congr' _ fun fresh => bind_congr' _ fun fp => ?_
    have hm : (fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
        reshareOut K (localContext i) bitCodec (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp i).1
          (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp i).2 (mulRep K (localContext i) (x i).1 (x i).2.1) (x i).2.2 c'
        else none) = realMsgs K D bitCodec a.2.1 a.2.2 fresh fp (fun i => mulRep K (localContext i) (x i).1 (x i).2.1) := by
      funext c' i
      unfold realMsgs
      split_ifs with h
      · rw [hxc i h.2]
      · rfl
    rw [hm]
    refine bind_congr' _ fun b => ?_
    congr 3
    refine Prod.ext rfl (funext fun i => ?_)
    unfold realOut
    by_cases hi : i ∈ D.1
    · simp [hi]
    have hin : (fun k => if k ∈ D.1 then b.2 k i else
        reshareOut K (localContext k) bitCodec (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp k).1
          (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp k).2 (mulRep K (localContext k) (x k).1 (x k).2.1) (x k).2.2 i) =
        fun k => if k ∈ D.1 then b.2 k i else
        reshareOut K (localContext k) bitCodec (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp k).1
          (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp k).2 (mulRep K (localContext k) (x k).1 (x k).2.1) (x j0).2.2 i := by
      funext k
      by_cases hk : k ∈ D.1
      · simp [hk]
      · simp only [hk, if_false, hxc k hk]
    simp only [hi, if_false]
    rw [hin, hxc i hi]
  case hideal =>
    exact WEq.symm prims (WEq.bind_right prims _ fun st => WEq.bind_right prims _ fun a =>
      WEq.sim_samples prims _ _ _ _ _)

end MultPeerProof

section PeerCouplingEmpty
variable [Field E] [Algebra Bit E] {R : Type} [Field R] [CharP R 2] [SampleableType R]

/-- A free uniform sample that nothing reads drops out. -/
theorem WEq.drop_sample (prims : Primitives) {α β : Type} [SampleableType α] (ob : OracleComp (WorldSpec C) β) :
    WEq prims (free (liftComp ($ᵗ α) (LocalSpec C)) >>= fun _ => ob) ob := fun s => by
  rw [world_run_free_bind]
  exact evalDist_uniform_bind_const _

theorem realMsgs_empty (K : Constants C E) (D : C.Coalition) (hD : D.1 = ∅) (codec : Codec C E R) {n : ℕ}
    (known : Shares C R) (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin n → R)
    (freshPair : C.Pair → Fin n → R) (v : C.Party → ℕ → R) :
    realMsgs K D codec known knownPairs fresh freshPair v = fun _ _ => none := by
  funext c' i; simp [realMsgs, hD]

/-- With no corrupt operator, the outputs of `F_mult` do not depend on the simulator samples. -/
theorem idealOut_empty (K : Constants C E) (D : C.Coalition) (hD : D.1 = ∅) (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) {n c : ℕ} (known : Shares C R) (knownPairs : C.Party → C.Party → ℕ → R)
    (fresh : C.Term → Fin n → R) (freshPair : C.Pair → Fin n → R) (filled : C.Term → ℕ → Option C.Party)
    (product : ℕ → R) (sent : C.Party → C.Party → Option (Msg E)) (freshF : C.Term → Fin c → R) :
    idealOut D filled product (peerReply K D codec known knownPairs fresh freshPair sent) freshF =
      idealOut D filled product (fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, Finset.univ) freshF := by
  have hk : ∀ T, ¬ KnownTo D.1 T := fun T ⟨j, hj, _⟩ => by simp [hD] at hj
  have hd : ∀ g, ∑ T, reshareZ K (localContext (refHolder D T)) codec
      (frandShare D n known knownPairs fresh freshPair (refHolder D T)).1
      (frandShare D n known knownPairs fresh freshPair (refHolder D T)).2 (fun _ => 0) n
      (fun k => if k ∈ D.1 then sent k (refHolder D T) else reshareOut K (localContext k) codec
        (frandShare D n known knownPairs fresh freshPair k).1 (frandShare D n known knownPairs fresh freshPair k).2
        (fun _ => 0) n (refHolder D T)) T g = 0 := by
    intro g
    have hz := reshareZ_frandShare' K D codec hcodec known knownPairs fresh freshPair (fun _ _ => 0) sent
    simp only [hz _ (refHolder_spec D _).2, (refHolder_spec D _).1, not_true_eq_false, false_or]
    by_cases hg : n ≤ g
    · simp [hg]
    · simp only [hg, if_false]
      rw [sum_termVal]
      simp [advVal, hD]
  have hmem : ∀ k, k ∉ D.1 := fun k => by simp [hD]
  have hab : ∀ i, anyAbort (fun k => if k ∈ D.1 then sent k i else (none : Option (Msg E))) = false :=
    fun i => by simp [anyAbort, hmem, Msg.isAbort]
  funext i
  unfold idealOut peerReply
  dsimp only
  simp only [hd, anyAbort_reshareOut K D codec hcodec]
  simp only [hab, hmem, hk, false_or, Finset.mem_filter,
    Finset.mem_univ, true_and, not_false_eq_true, and_self, not_true_eq_false, if_false, false_and,
    exists_false, add_zero]
  simp [anyAbort, Msg.isAbort]

end PeerCouplingEmpty

section PeerCouplingCount
variable [Field E] [Algebra Bit E] {R : Type} [Field R] [CharP R 2] [SampleableType R]

theorem ideal_empty (prims : Primitives) (K : Constants C E) (D : C.Coalition) (hD : D.1 = ∅) (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) {I : Type} (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R)))
    (Z : Distinguisher C A.State (Shares C R)) (a : A.State × Shares C R × (C.Party → C.Party → ℕ → R)) (n c : ℕ)
    (filled : C.Term → ℕ → Option C.Party) (product : ℕ → R) :
    WEq prims
      (do
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin n → R)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin n → R)) (LocalSpec C))
        let freshF ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let b ← counted (liftComp (A.round a.1 (realMsgs K D codec a.2.1 a.2.2 fresh freshPair (fun _ _ => 0)))
          (SimulatorSpec C))
        counted (liftComp (Z (b.1, idealOut D filled product (peerReply K D codec a.2.1 a.2.2 fresh freshPair b.2)
          freshF)) (SimulatorSpec C)))
      (do
        let freshF ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let b ← counted (liftComp (A.round a.1 fun _ _ => none) (SimulatorSpec C))
        counted (liftComp (Z (b.1, idealOut D filled product (fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, Finset.univ)
          freshF)) (SimulatorSpec C))) := by
  simp only [realMsgs_empty K D hD, idealOut_empty K D hD codec hcodec]
  exact WEq.trans prims (WEq.drop_sample prims _) (WEq.drop_sample prims _)

/-- `peer_coupling` with the count `n` of the simulator, which is the width unless no operator is corrupt. -/
theorem peer_coupling_count (prims : Primitives) (K : Constants C E) (D : C.Coalition) (codec : Codec C E R)
    (hcodec : CodecRoundTrip codec) {I : Type} (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R)))
    (Z : Distinguisher C A.State (Shares C R)) (start : OracleComp (WorldSpec C) A.State) (c n : ℕ)
    (hn : n = c ∨ D.1 = ∅) (v : C.Party → ℕ → R) (filled : C.Term → ℕ → Option C.Party)
    (hfilled : ∀ T g, (∃ j ∈ D.1, filled T g = some j) ↔ ∃ j ∈ D.1, K.filled j = T)
    (product : ℕ → R) (hproduct : ∀ g, product g = ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g) :
    WEq prims
      (do
        let st ← start
        let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → R)) (LocalSpec C))
        let b ← counted (liftComp (A.round a.1 (realMsgs K D codec a.2.1 a.2.2 fresh freshPair v)) (SimulatorSpec C))
        counted (liftComp (Z (b.1, realOut K D codec a.2.1 a.2.2 fresh freshPair v b.2)) (SimulatorSpec C)))
      (do
        let st ← start
        let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin n → R)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin n → R)) (LocalSpec C))
        let freshF ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
        let b ← counted (liftComp (A.round a.1 (realMsgs K D codec a.2.1 a.2.2 fresh freshPair (fun _ _ => 0)))
          (SimulatorSpec C))
        counted (liftComp (Z (b.1, idealOut D filled product (peerReply K D codec a.2.1 a.2.2 fresh freshPair b.2)
          freshF)) (SimulatorSpec C))) := by
  rcases hn with rfl | hD
  · exact peer_coupling prims K D codec hcodec A Z start n v filled hfilled product hproduct
  refine WEq.trans prims (peer_coupling prims K D codec hcodec A Z start c v filled hfilled product hproduct)
    (WEq.bind_right prims _ fun st => WEq.bind_right prims _ fun a => ?_)
  exact WEq.trans prims (ideal_empty prims K D hD codec hcodec A Z a c c filled product)
    (WEq.symm prims (ideal_empty prims K D hD codec hcodec A Z a n c filled product))

end PeerCouplingCount

section ExtendMultProof
variable [Field E] [Algebra Bit E] [SampleableType E]

theorem foldl_max_le (L : ℕ) : ∀ (l : List ℕ) (acc : ℕ), acc ≤ L → (∀ a ∈ l, a ≤ L) → l.foldl max acc ≤ L
  | [], _, h, _ => h
  | b :: l, acc, h, hl => foldl_max_le L l _ (max_le h (hl b (by simp))) fun a ha => hl a (by simp [ha])

theorem le_foldl_max_acc : ∀ (l : List ℕ) (acc : ℕ), acc ≤ l.foldl max acc ∧ ∀ a ∈ l, a ≤ l.foldl max acc
  | [], _ => ⟨le_rfl, by simp⟩
  | b :: l, acc => by
    obtain ⟨h1, h2⟩ := le_foldl_max_acc l (max acc b)
    refine ⟨(le_max_left _ _).trans h1, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (le_max_right _ _).trans h1
    · exact h2 a ha

/-- The count that `F_extendMult` leaks is the width when some operator is corrupt. -/
theorem leakCount_eq (D : C.Coalition) (hD : D.1.Nonempty) (l : C.Party → List (Product C E)) (L : ℕ)
    (hl : ∀ c, (l c).length = if c ∈ D.1 then L else 0) : leakCount l = L := by
  obtain ⟨c0, hc0⟩ := hD
  unfold leakCount
  refine le_antisymm (foldl_max_le L _ 0 (Nat.zero_le _) fun a ha => ?_) ?_
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    rw [hl c]; split_ifs <;> omega
  · have := (le_foldl_max_acc (C.parties.map fun c => (l c).length) 0).2 (l c0).length
      (List.mem_map.mpr ⟨c0, by simp [Committee.parties], rfl⟩)
    rwa [hl c0, if_pos hc0] at this

attribute [local instance] inhabitedField in
/-- The leak of `F_extendMult`. -/
def extendView (K : Constants C E) (D : Finset C.Party) (inputs : C.Party → Option (List (Product C E))) :
    C.Party → List (Product C E) := fun c =>
  if c ∉ D then [] else (firstInput inputs).zipIdx.map fun (p, g) =>
    let entry := fun i => (inputs i).bind (·[g]?)
    match p with
    | .replicated _ _ count =>
        .replicated (knownView D count (reconstruct fun i => (entry i).map (·.replicatedParts.1)))
          (knownView D count (reconstruct fun i => (entry i).map (·.replicatedParts.2))) count
    | .shamir _ _ count =>
        .shamir (fun k => if k < count then
            interpolate K D (fun i => (((entry i).map (·.shamirParts.1)).getD fun _ => 0) k) (K.point c) else 0)
          (fun k => if k < count then
            interpolate K D (fun i => (((entry i).map (·.shamirParts.2)).getD fun _ => 0) k) (K.point c) else 0)
          count

attribute [local instance] inhabitedField in
theorem FextendMult_eq (K : Constants C E) : FextendMult K = Fmult List.length (fun _ => filler K .peer)
    (fun i products g => match products[g]? with | some p => productShare K (localContext i) p | none => 0)
    (extendView K) := rfl

theorem extendMultCoupling (prims : Primitives) (K : Constants C E) : ExtendMultCoupling prims K := by
  intro D A x z Z hx
  obtain ⟨j0, hj0, hfirst⟩ := firstInput_honest D x
  have hlen : ∀ i j, i ∉ D.1 → j ∉ D.1 → (x i).length = (x j).length := fun i j hi hj => by
    simpa using congrArg List.length (hx.1 i j hi hj)
  have hxc : ∀ i, i ∉ D.1 → (x i).length = (x j0).length := fun i hi => hlen i j0 hi hj0
  haveI : CharP E 2 := charTwo
  unfold distinguish
  rw [realExecution_extendMult]
  have hc := firstInput_eq_of_same D (fun i => (x i).length) hlen j0 hj0
  generalize firstInput (fun i => if i ∈ D.1 then none else some (x i).length) = c at hc ⊢
  subst hc
  rw [FextendMult_eq, idealExecution_Fmult]
  simp only [peerSim, peerSimAnswer_eq, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure,
    pure_bind, worldRoles, fmultOut_eq]
  rw [hfirst]
  have hn : leakCount (extendView K D.1 fun i => if i ∈ D.1 then none else some (x i)) = (x j0).length ∨ D.1 = ∅ := by
    rcases D.1.eq_empty_or_nonempty with hD | hD
    · exact Or.inr hD
    refine Or.inl (leakCount_eq D hD _ _ fun c => ?_)
    unfold extendView
    by_cases hc : c ∈ D.1 <;> simp [hc, hfirst]
  refine WEq.trans prims (WEq.of_eq prims ?hreal) (WEq.trans prims (peer_coupling_count prims K D (elementCodec K)
    (elementCodec_roundTrip K) A Z (counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C)))
    (x j0).length (leakCount (extendView K D.1 fun i => if i ∈ D.1 then none else some (x i))) hn
    (fun i => productValues K i (x i)) (filler K .peer) (fun T g => filler_peer_corrupt K D T g)
    (fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), (((fun i => if i ∈ D.1 then none else some (x i)) i).map
      fun products => (match products[g]? with | some p => productShare K (localContext i) p | none => 0)).getD 0)
    ?hprod) ?hideal)
  case hprod =>
    intro g
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [(Finset.mem_filter.mp hi).2, if_false, Option.map_some, Option.getD_some]
    rfl
  case hreal =>
    refine bind_congr' _ fun st => bind_congr' _ fun a => bind_congr' _ fun fresh => bind_congr' _ fun fp => ?_
    have hm : (fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
        reshareOut K (localContext i) (elementCodec K) (frandShare D (x j0).length a.2.1 a.2.2 fresh fp i).1
          (frandShare D (x j0).length a.2.1 a.2.2 fresh fp i).2 (productValues K i (x i)) (x i).length c'
        else none) = realMsgs K D (elementCodec K) a.2.1 a.2.2 fresh fp (fun i => productValues K i (x i)) := by
      funext c' i
      unfold realMsgs
      split_ifs with h
      · rw [hxc i h.2]
      · rfl
    rw [hm]
    refine bind_congr' _ fun b => ?_
    congr 3
    refine Prod.ext rfl (funext fun i => ?_)
    unfold realOut
    by_cases hi : i ∈ D.1
    · simp [hi]
    have hin : (fun k => if k ∈ D.1 then b.2 k i else
        reshareOut K (localContext k) (elementCodec K) (frandShare D (x j0).length a.2.1 a.2.2 fresh fp k).1
          (frandShare D (x j0).length a.2.1 a.2.2 fresh fp k).2 (productValues K k (x k)) (x k).length i) =
        fun k => if k ∈ D.1 then b.2 k i else
        reshareOut K (localContext k) (elementCodec K) (frandShare D (x j0).length a.2.1 a.2.2 fresh fp k).1
          (frandShare D (x j0).length a.2.1 a.2.2 fresh fp k).2 (productValues K k (x k)) (x j0).length i := by
      funext k
      by_cases hk : k ∈ D.1
      · simp [hk]
      · simp only [hk, if_false, hxc k hk]
    simp only [hi, if_false]
    rw [hin, hxc i hi]
  case hideal =>
    exact WEq.symm prims (WEq.bind_right prims _ fun st => WEq.bind_right prims _ fun a =>
      WEq.sim_samples prims _ _ _ _ _)

end ExtendMultProof

section PeerClaims
variable [Field E] [Algebra Bit E]

/-- `MulRep` and a peer `Reshare` securely compute `F_mult` (GS20, Lemma 4). -/
theorem multPeerSecurity (prims : Primitives) (K : Constants C E) :
    SecurelyComputes prims (multProtocol K .peer) (1 + ReshareMode.peer.rounds) (Frand Bit) (FmultBit K .peer)
      (fun D x => SameCount D fun i => (x i).2.2) 0 fun _ => 0 :=
  multPeer_of_coupling prims K (multPeerCoupling prims K)

theorem extendMultSecurity (prims : Primitives) (K : Constants C E) [SampleableType E] :
    ExtendMultStatement prims K :=
  extendMult_of_coupling prims K (extendMultCoupling prims K)

end PeerClaims

section Collector
variable [Field E] [Algebra Bit E]

/-- The gates that operator `j` collects. -/
def collectedBy (K : Constants C E) (count : ℕ) (j : C.Party) : List ℕ :=
  (List.range count).filter fun g => (K.collector g).2 = j

/-- The gates of collector `κ` whose term `T*` operator `h` holds. -/
def forwardedTo (K : Constants C E) (count : ℕ) (κ h : C.Party) : List ℕ :=
  (collectedBy K count κ).filter fun g => h ∈ C.holders (K.collector g).1

/-- `u_i` of a collector reshare. -/
def colU (K : Constants C E) (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit) : ℕ → Bit :=
  fun g => v g + ∑ j ∈ Finset.univ.erase i, Zs j g +
    ∑ T ∈ Finset.univ.filter (fun T => T ≠ (K.collector g).1 ∧ K.owner T = i), r T g

def colOut1 (K : Constants C E) (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit)
    (count : ℕ) : Mail C E := fun j =>
  if j ≠ i then some (.bits ((collectedBy K count j).map (colU K i r Zs v))) else none

/-- The sum that collector `i` forms for its gates. -/
def colSum (K : Constants C E) (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit)
    (count : ℕ) (inbox : Mail C E) : ℕ → Bit := fun g =>
  colU K i r Zs v g + ∑ j ∈ Finset.univ.erase i, Msg.bitAt (inbox j) ((collectedBy K count i).idxOf g)

def colOut2 (K : Constants C E) (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit)
    (count : ℕ) (inbox : Mail C E) : Mail C E := fun h =>
  if h ≠ i then some (.bits ((forwardedTo K count i h).map (colSum K i r Zs v count inbox))) else none

def colZ (K : Constants C E) (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit)
    (count : ℕ) (inbox forward : Mail C E) : Shares C Bit := fun T g =>
  if i ∉ C.holders T ∨ count ≤ g then 0
  else if T = (K.collector g).1 then
    if (K.collector g).2 = i then colSum K i r Zs v count inbox g
    else Msg.bitAt (forward (K.collector g).2) ((forwardedTo K count (K.collector g).2 i).idxOf g)
  else r T g

theorem reshareCollector_run' {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C)
    (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit) (count : ℕ) (st : RunState C) :
    (reshareCollector (G := G) K ctx (r, Zs) v count).run' st =
      exchange (colOut1 K ctx.self r Zs v count) >>= fun inbox =>
        exchange (colOut2 K ctx.self r Zs v count inbox) >>= fun forward =>
          pure (colZ K ctx.self r Zs v count inbox forward) := by
  unfold reshareCollector
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_lift]
  simp only [bind_assoc, pure_bind, map_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
  refine congrArg (_ >>= ·) (funext fun forward => ?_)
  simp only [record, StateT.run_modify, StateT.run_pure, pure_bind, map_pure]
  rfl

end Collector

section ThreeSteps
variable {I O R : Type} [AddCommGroup R] [SampleableType R]

/-- One round of the real run when each honest operator waits or has aborted. -/
theorem executeRounds_round {Ih Oh Lh Rh α : Type} (D : C.Coalition) (A : Adversary C E I Lh Rh)
    (F : Functionality C Ih Oh Lh Rh) (n : ℕ) (st : A.State) (ab : C.Party → Bool) (o : C.Party → Mail C E)
    (k : C.Party → Mail C E → OracleComp (PartySpec C E (CallSpec Ih Oh)) (Option α))
    (h : ∃ i, i ∉ D.1 ∧ ¬ ab i) :
    executeRounds worldRoles D A F (n + 1) st
        (fun j => if j ∈ D.1 ∨ ab j then Step.done none else Step.wait (o j) (k j)) =
      (do
        let b ← counted (liftComp (A.round st fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 ∧ ¬ ab i then o i c' else none)
          (SimulatorSpec C))
        let steps ← Concrete.sequenceFin fun j => if j ∈ D.1 ∨ ab j then pure (Step.done none) else
          free (advance (k j fun k' => if k' ∈ D.1 then b.2 k' j else if ab k' then some .abort else o k' j))
        executeRounds worldRoles D A F n b.1 steps) := by
  obtain ⟨i0, hi0, hab0⟩ := h
  rw [executeRounds, if_neg (by push Not; exact ⟨i0, hi0, by simp [hi0, hab0]⟩)]
  rw [stepRound, if_neg (by push Not; intro _; exact ⟨i0, hi0, by simp [hi0, hab0]⟩)]
  simp only [bind_assoc, pure_bind]
  have hm : (fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then (if i ∈ D.1 ∨ ab i then Step.done none else Step.wait (o i) (k i) :
      Step C E (CallSpec Ih Oh) α).outbox c' else none) =
      fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 ∧ ¬ ab i then o i c' else none := by
    funext c' i
    by_cases h1 : c' ∈ D.1 <;> by_cases h2 : i ∈ D.1 <;> by_cases h3 : ab i <;> simp [h1, h2, h3, Step.outbox]
  rw [hm]
  refine bind_congr' _ fun b => ?_
  refine congrArg (· >>= _) (congrArg Concrete.sequenceFin (funext fun j => ?_))
  by_cases hj : j ∈ D.1
  · simp only [hj, true_or, if_true]
  by_cases hab : ab j
  · simp only [hab, or_true, if_true]
  · simp only [hj, hab, or_self, if_false, worldRoles, Bool.false_eq_true, false_or]
    congr 3; funext k'
    by_cases hk : k' ∈ D.1
    · simp [hk]
    · by_cases hk' : ab k' <;> simp [hk, hk', Step.delivered]

/-- The real run of a protocol with one call to `F_rand` and two rounds, where an operator may abort
after the first round. -/
theorem realExecution_frand3 (D : C.Coalition) (A : Adversary C E I Unit (Shares C R × (C.Party → C.Party → ℕ → R)))
    (program : C.Party → I → PartyM C E (CallSpec ℕ (PrssOutput C R)) O)
    (callIn : C.Party → I → ℕ)
    (resume : C.Party → I → Option (PrssOutput C R) → OracleComp (PartySpec C E (CallSpec ℕ (PrssOutput C R))) (Option O))
    (out1 : C.Party → I → PrssOutput C R → Mail C E)
    (k1 : C.Party → I → PrssOutput C R → Mail C E → OracleComp (PartySpec C E (CallSpec ℕ (PrssOutput C R))) (Option O))
    (ab : C.Party → I → PrssOutput C R → Mail C E → Bool)
    (out2 : C.Party → I → PrssOutput C R → Mail C E → Mail C E)
    (k2 : C.Party → I → PrssOutput C R → Mail C E → Mail C E →
      OracleComp (PartySpec C E (CallSpec ℕ (PrssOutput C R))) (Option O))
    (res : C.Party → I → PrssOutput C R → Mail C E → Mail C E → Option O)
    (h1 : ∀ i xi, advance (program i xi).run = pure (.call (callIn i xi) (resume i xi)))
    (h2 : ∀ i xi o, advance (resume i xi (some o)) = pure (.wait (out1 i xi o) (k1 i xi o)))
    (h3 : ∀ i xi o inbox, advance (k1 i xi o inbox) =
      pure (if ab i xi o inbox then .done none else .wait (out2 i xi o inbox) (k2 i xi o inbox)))
    (h4 : ∀ i xi o inbox fwd, advance (k2 i xi o inbox fwd) = pure (.done (res i xi o inbox fwd)))
    (x : C.Party → I) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (callIn i (x i))
    realExecution D A (Frand R) 3 program x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → R)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → R)) (LocalSpec C))
      let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
      let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then out1 i (x i) (rnd i) c' else none)
        (SimulatorSpec C))
      let inbox := fun i k => if k ∈ D.1 then b.2 k i else out1 k (x k) (rnd k) i
      if ∀ i, i ∉ D.1 → ab i (x i) (rnd i) (inbox i) then pure (b.1, fun _ => none) else do
      let b' ← counted (liftComp (A.round b.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 ∧ ¬ ab i (x i) (rnd i) (inbox i) then
        out2 i (x i) (rnd i) (inbox i) c' else none) (SimulatorSpec C))
      pure (b'.1, fun i => if i ∈ D.1 ∨ ab i (x i) (rnd i) (inbox i) then none else
        res i (x i) (rnd i) (inbox i) fun k => if k ∈ D.1 then b'.2 k i else
          if ab k (x k) (rnd k) (inbox k) then some .abort else out2 k (x k) (rnd k) (inbox k) i)) := by
  intro c
  obtain ⟨i0, hi0⟩ := exists_honest D
  simp only [realExecution, executePhase, startSteps]
  rw [sequenceFin_congr_pure _ (fun i => if i ∈ D.1 then Step.done none else Step.call (callIn i (x i)) (resume i (x i)))
    (fun i => by split_ifs <;> simp [worldRoles, h1, free]; rfl)]
  simp only [pure_bind]
  show counted _ >>= _ = counted _ >>= _
  congr 1; funext st
  rw [executeRounds, if_neg (by push Not; exact ⟨i0, hi0, by simp [hi0]⟩)]
  rw [stepRound, if_pos ⟨⟨i0, hi0, by simp [hi0]⟩, fun i hi => Or.inl (by simp [hi])⟩]
  have hin : (fun i => if i ∈ D.1 then none else
      (if i ∈ D.1 then Step.done none else Step.call (callIn i (x i)) (resume i (x i)) :
        Step C E (CallSpec ℕ (PrssOutput C R)) O).callInput) =
      fun i => if i ∈ D.1 then none else some (callIn i (x i)) := by
    funext i; split_ifs <;> simp
  rw [hin, runFunctionality_Frand R D A st _ (fun i hi => by simp [hi])]
  simp only [bind_assoc, pure_bind]
  simp only [c]
  refine bind_congr' _ fun a => ?_
  refine bind_congr' _ fun fresh => ?_
  refine bind_congr' _ fun freshPair => ?_
  rw [sequenceFin_congr_pure _ (fun j => if j ∈ D.1 then Step.done none else
      Step.wait (out1 j (x j) (frandShare D c a.2.1 a.2.2 fresh freshPair j))
        (k1 j (x j) (frandShare D c a.2.1 a.2.2 fresh freshPair j)))
    (fun j => by
      by_cases hj : j ∈ D.1
      · simp only [hj, if_true]
      · simp only [hj, if_false, frandOut_eq, worldRoles]; rw [h2]; rfl)]
  simp only [pure_bind]
  rw [executeRounds_wait]
  refine bind_congr' _ fun b => ?_
  set rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
  set inbox := fun i k => if k ∈ D.1 then b.2 k i else out1 k (x k) (rnd k) i
  rw [sequenceFin_congr_pure _ (fun j => if j ∈ D.1 ∨ ab j (x j) (rnd j) (inbox j) then Step.done none else
      Step.wait (out2 j (x j) (rnd j) (inbox j)) (k2 j (x j) (rnd j) (inbox j)))
    (fun j => by
      by_cases hj : j ∈ D.1
      · simp only [hj, if_true, true_or]
      · simp only [hj, if_false, false_or, worldRoles]
        rw [h3]
        split_ifs <;> rfl)]
  simp only [pure_bind]
  by_cases hall : ∀ i, i ∉ D.1 → ab i (x i) (rnd i) (inbox i)
  · rw [if_pos hall, executeRounds, if_pos (fun i hi => by simp [hall i hi])]
    congr 2; funext i
    by_cases hi : i ∈ D.1
    · simp [hi, Step.output]
    · simp [hi, hall i hi, Step.output]
  rw [if_neg hall]
  push Not at hall
  rw [executeRounds_round D A (Frand R) 0 b.1 (fun j => ab j (x j) (rnd j) (inbox j)) _ _ hall]
  refine bind_congr' _ fun b' => ?_
  rw [sequenceFin_congr_pure _ (fun j => if j ∈ D.1 ∨ ab j (x j) (rnd j) (inbox j) then Step.done none else
      Step.done (res j (x j) (rnd j) (inbox j) fun k' => if k' ∈ D.1 then b'.2 k' j else
        if ab k' (x k') (rnd k') (inbox k') then some .abort else out2 k' (x k') (rnd k') (inbox k') j))
    (fun j => by
      split_ifs
      · rfl
      · rw [h4]; rfl)]
  simp only [pure_bind, executeRounds]
  congr 2; funext i; split_ifs <;> rfl

end ThreeSteps

section CollectorReal
variable [Field E] [Algebra Bit E]

theorem realExecution_multCollector (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Shares C Bit × Shares C Bit × ℕ) Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (x : C.Party → Shares C Bit × Shares C Bit × ℕ) (z : Aux) :
    let c := firstInput fun i => if i ∈ D.1 then none else some (x i).2.2
    realExecution D A (Frand Bit) (1 + ReshareMode.collector.rounds) (multProtocol K .collector) x z = (do
      let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
      let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
      let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → Bit)) (LocalSpec C))
      let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → Bit)) (LocalSpec C))
      let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
      let v := fun i => mulRep K (localContext i) (x i).1 (x i).2.1
      let b ← counted (liftComp (A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
        colOut1 K i (rnd i).1 (rnd i).2 (v i) (x i).2.2 c' else none) (SimulatorSpec C))
      let inbox := fun i k => if k ∈ D.1 then b.2 k i else colOut1 K k (rnd k).1 (rnd k).2 (v k) (x k).2.2 i
      if ∀ i, i ∉ D.1 → anyAbort (inbox i) = true then pure (b.1, fun _ => none) else do
      let b' ← counted (liftComp (A.round b.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 ∧ ¬ anyAbort (inbox i) = true then
        colOut2 K i (rnd i).1 (rnd i).2 (v i) (x i).2.2 (inbox i) c' else none) (SimulatorSpec C))
      pure (b'.1, fun i => if i ∈ D.1 ∨ anyAbort (inbox i) = true then none else
        let forward : Mail C E := fun k => if k ∈ D.1 then b'.2 k i else
          if anyAbort (inbox k) = true then some .abort else colOut2 K k (rnd k).1 (rnd k).2 (v k) (x k).2.2 (inbox k) i
        if anyAbort forward then none else some (colZ K i (rnd i).1 (rnd i).2 (v i) (x i).2.2 (inbox i) forward))) :=
  realExecution_frand3 D A (multProtocol K .collector) (fun _ xi => xi.2.2)
    (fun i xi r => OptionT.run (match r with
      | some randomness => (reshareWith K (localContext i) .collector randomness
          (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2).run' startRun
      | _ => failure))
    (fun i xi o => colOut1 K i o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2)
    (fun i xi o inbox => OptionT.run (if anyAbort inbox then failure else
      exchange (colOut2 K i o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox) >>= fun forward =>
        pure (colZ K i o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox forward)))
    (fun _ _ _ inbox => anyAbort inbox)
    (fun i xi o inbox => colOut2 K i o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox)
    (fun i xi o inbox forward => OptionT.run (if anyAbort forward then failure else
      pure (colZ K i o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox forward)))
    (fun i xi o inbox forward => if anyAbort forward then none else
      some (colZ K i o.1 o.2 (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2 inbox forward))
    (fun i xi => by
      rcases xi with ⟨x, y, c⟩
      unfold multProtocol; rw [advance_call]; congr 2; funext r; cases r <;> rfl)
    (fun i xi o => by
      rcases o with ⟨r, Zs⟩
      show advance (OptionT.run ((reshareCollector K (localContext i) (r, Zs)
        (mulRep K (localContext i) xi.1 xi.2.1) xi.2.2).run' startRun)) = _
      rw [reshareCollector_run']; exact advance_exchange _ _)
    (fun i xi o inbox => by
      by_cases h : anyAbort inbox = true
      · simp only [h, if_true]; rfl
      · simp only [h, if_false, Bool.false_eq_true]
        exact advance_exchange _ _)
    (fun i xi o inbox forward => by split <;> rfl) x z

end CollectorReal

section CollectorSim
variable [Field E] [Algebra Bit E]

/-- The reply of the collector simulator after the second round. -/
def colReply (K : Constants C E) (D : C.Coalition) (n : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (inbox : C.Party → Mail C E) (sent : C.Party → C.Party → Option (Msg E)) :
    (ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party :=
  let forward := fun i k => if k ∈ D.1 then sent k i else
    if anyAbort (inbox k) = true then some .abort else colOut2 K k (rnd k).1 (rnd k).2 (fun _ => 0) n (inbox k) i
  let zf := fun i => colZ K i (rnd i).1 (rnd i).2 (fun _ => 0) n (inbox i) (forward i)
  let known : Shares C Bit := fun T => zf (refHolder D T) T
  (fun g => ∑ T, known T g, known, fun i T g => zf i T g - known T g,
    Finset.univ.filter fun i => i ∉ D.1 ∧ anyAbort (inbox i) = false ∧ anyAbort (forward i) = false)

/-- The reply of the collector simulator to a leak with count `n`. It runs the adversary on a
simulated `F_rand` and on the two rounds of honest operators with zero inputs, where each honest
collector forwards its sums. -/
def colSimAnswer {I : Type} (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E I Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit))) (n : ℕ) (st : A.State) :
    OracleComp (LocalSpec C)
      (A.State × ((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party)) := do
  let a ← A.answer st ()
  let fresh ← liftComp ($ᵗ (C.Term → Fin n → Bit)) (LocalSpec C)
  let freshPair ← liftComp ($ᵗ (C.Pair → Fin n → Bit)) (LocalSpec C)
  let rnd := frandShare D n a.2.1 a.2.2 fresh freshPair
  let b ← A.round a.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then
    colOut1 K i (rnd i).1 (rnd i).2 (fun _ => 0) n c' else none
  let inbox := fun i k => if k ∈ D.1 then b.2 k i else colOut1 K k (rnd k).1 (rnd k).2 (fun _ => 0) n i
  if ∀ i, i ∉ D.1 → anyAbort (inbox i) = true then
    pure (b.1, (fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, ∅)) else do
  let b' ← A.round b.1 fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 ∧ ¬ anyAbort (inbox i) = true then
    colOut2 K i (rnd i).1 (rnd i).2 (fun _ => 0) n (inbox i) c' else none
  pure (b'.1, colReply K D n rnd inbox b'.2)

/-- The simulator of a collector reshare (GS20, Lemma 4). -/
def colSim {I Lk : Type} (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E I Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit))) (count : Lk → ℕ) :
    Simulator (C := C) (LocalSpec C) I Lk ((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party)
      A.State where
  State := A.State
  start := A.start
  answer st l := colSimAnswer K D A (count l) st
  output st := pure st

/-- The coupling of `MultStatement` in collector mode. The real run and the run of `colSim` agree. -/
def MultCollectorCoupling (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (D : C.Coalition)
    (A : Adversary C E (Shares C Bit × Shares C Bit × ℕ) Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (x : C.Party → Shares C Bit × Shares C Bit × ℕ) (z : Aux) (Z : Distinguisher C A.State (Shares C Bit)),
    SameCount D (fun i => (x i).2.2) →
    WEq prims (distinguish (realExecution D A (Frand Bit) (1 + ReshareMode.collector.rounds)
        (multProtocol K .collector) x z) Z)
      (distinguish (idealExecution worldRoles.adversary D (FmultBit K .collector) (colSim K D A (·.1)) x z) Z)

theorem CostLe.ite (prims : Primitives) {α : Type} (p : Prop) [Decidable p] {oa ob : OracleComp (WorldSpec C) α} {n : ℕ}
    (ha : CostLe prims oa n) (hb : CostLe prims ob n) : CostLe prims (if p then oa else ob) n := by
  split_ifs <;> assumption

theorem CostLe.counted_pure' (prims : Primitives) {α : Type} (a : α) :
    CostLe prims (counted (C := C) (liftComp (Pure.pure a : OracleComp (LocalSpec C) α) (SimulatorSpec C))) 0 := by
  rw [liftComp_pure, counted_pure]; exact CostLe.pure prims a

theorem multCollector_of_coupling (prims : Primitives) (K : Constants C E) (h : MultCollectorCoupling prims K) :
    SecurelyComputes prims (multProtocol K .collector) (1 + ReshareMode.collector.rounds) (Frand Bit)
      (FmultBit K .collector) (fun D x => SameCount D fun i => (x i).2.2) 0 fun _ => 0 := by
  intro D A
  refine ⟨colSim K D A (·.1), fun x z Z q hx hq => ⟨?_, ?_⟩⟩
  · obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
    apply hasHashQueryBound_of_costLe
    unfold distinguish FmultBit
    rw [idealExecution_Fmult]
    simp only [colSim, colSimAnswer, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure, pure_bind,
      worldRoles]
    have hite : ∀ (c : Prop) [Decidable c] {β : Type} (st' : A.State) (p : A.State × β)
        (msgs : C.Party → C.Party → Option (Msg E)) (f : A.State × (C.Party → C.Party → Option (Msg E)) → β),
        CostLe prims (counted (liftComp (if c then pure p else
          A.round st' msgs >>= fun b' => pure (b'.1, f b')) (SimulatorSpec C))) step := by
      intro c _ β st' p msgs f
      rw [apply_ite (fun oa => counted (liftComp oa (SimulatorSpec C)))]
      refine CostLe.ite prims _ ?_ ?_
      · simp only [liftComp_pure, counted_pure]
        exact CostLe.mono prims (CostLe.pure prims _) (Nat.zero_le _)
      · simp only [liftComp_bind, counted_bind, liftComp_pure, counted_pure]
        exact CostLe.mono prims (CostLe.bind prims (CostLe.of_counted prims _ _ (hr _ _)) fun _ => CostLe.pure prims _)
          (by omega)
    exact CostLe.mono prims (CostLe.bind prims (CostLe.of_counted prims _ _ (hs _ _)) fun st =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (ha _ _)) fun a =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun f' =>
      CostLe.bind prims (CostLe.counted_sample prims _) fun fp =>
      CostLe.bind prims (CostLe.of_counted prims _ _ (hr _ _)) fun b =>
      CostLe.bind prims (hite _ _ _ _ _) fun ans =>
      CostLe.bind prims (CostLe.free_sample prims _) fun fr =>
      CostLe.of_counted prims _ _ (hz _))
      (by simp only [ReshareMode.rounds] at hsum; omega)
  · rw [accepts_eq_of_WEq prims (h D A x z Z hx), sub_self, abs_zero]

end CollectorSim

section MultClaim
variable [Field E] [Algebra Bit E]

theorem multStatement_of_coupling (prims : Primitives) (K : Constants C E) (h : MultCollectorCoupling prims K) :
    MultStatement prims K := fun mode =>
  match mode with
  | .peer => multPeerSecurity prims K
  | .collector => multCollector_of_coupling prims K h

end MultClaim

section CollectorValues
variable [Field E] [Algebra Bit E]

theorem getD_map_idxOf {l : List ℕ} {g : ℕ} (hg : g ∈ l) (f : ℕ → Bit) : (l.map f).getD (l.idxOf g) 0 = f g := by
  have h : l.idxOf g < l.length := List.idxOf_lt_length_iff.mpr hg
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h, List.getElem_idxOf]

/-- `u_j` of a collector reshare at gate `g`. -/
def colUVal (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (j : C.Party) (g : ℕ) : Bit :=
  v j g + ∑ k ∈ Finset.univ.erase j, pairVal D knownPairs freshPair j k g +
    ∑ T ∈ Finset.univ.filter (fun T => T ≠ (K.collector g).1 ∧ K.owner T = j), randVal D known fresh g T

/-- The sum of an honest collector `κ` at gate `g`, where corrupt `k` sends `sent k κ`. -/
def colSumVal (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent : C.Party → C.Party → Option (Msg E)) (κ : C.Party) (g : ℕ) : Bit :=
  ∑ j ∈ Finset.univ.filter (· ∉ D.1), colUVal K D known knownPairs fresh freshPair v j g +
    ∑ k ∈ D.1, Msg.bitAt (sent k κ) ((collectedBy K c κ).idxOf g)

/-- Term `T` at gate `g` after a collector reshare in the view of operator `i`. -/
def termValC (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent sent' : C.Party → C.Party → Option (Msg E)) (i : C.Party) (T : C.Term) (g : ℕ) :
    Bit :=
  if T = (K.collector g).1 then
    (if (K.collector g).2 ∈ D.1 then Msg.bitAt (sent' (K.collector g).2 i) ((forwardedTo K c (K.collector g).2 i).idxOf g)
    else colSumVal K D known knownPairs fresh freshPair v sent (K.collector g).2 g)
  else randVal D known fresh g T

theorem colU_frandShare (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (j : C.Party) (g : ℕ) :
    colU K j (frandShare D c known knownPairs fresh freshPair j).1 (frandShare D c known knownPairs fresh freshPair j).2
      (v j) g = colUVal K D known knownPairs fresh freshPair v j g := by
  unfold colU colUVal
  simp only [frandShare_snd]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' := (Finset.mem_filter.mp hT).2
  exact frandShare_fst D known knownPairs fresh freshPair j T g (hT'.2 ▸ K.owner_held T)

theorem mem_collectedBy (K : Constants C E) {c g : ℕ} (hg : g < c) : g ∈ collectedBy K c (K.collector g).2 := by
  simp [collectedBy, hg]

theorem colSum_frandShare (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent : C.Party → C.Party → Option (Msg E)) (g : ℕ) (hg : g < c)
    (hκ : (K.collector g).2 ∉ D.1) :
    let rnd := frandShare D c known knownPairs fresh freshPair
    let κ := (K.collector g).2
    colSum K κ (rnd κ).1 (rnd κ).2 (v κ) c
        (fun k => if k ∈ D.1 then sent k κ else colOut1 K k (rnd k).1 (rnd k).2 (v k) c κ) g =
      colSumVal K D known knownPairs fresh freshPair v sent κ g := by
  intro rnd κ
  set F : C.Party → Bit := fun j => if j ∈ D.1 then Msg.bitAt (sent j κ) ((collectedBy K c κ).idxOf g) else
    colUVal K D known knownPairs fresh freshPair v j g
  have hF : ∀ j ∈ Finset.univ.erase κ, Msg.bitAt ((fun k => if k ∈ D.1 then sent k κ else
      colOut1 K k (rnd k).1 (rnd k).2 (v k) c κ) j) ((collectedBy K c κ).idxOf g) = F j := by
    intro j hj
    have hjκ := Finset.ne_of_mem_erase hj
    simp only [F]
    by_cases hjD : j ∈ D.1
    · simp [hjD]
    · simp only [hjD, if_false, colOut1, if_pos (Ne.symm hjκ), Msg.bitAt]
      rw [getD_map_idxOf (mem_collectedBy K hg), colU_frandShare]
  unfold colSum
  rw [Finset.sum_congr rfl hF, colU_frandShare]
  have hκF : colUVal K D known knownPairs fresh freshPair v κ g = F κ := by
    show _ = if κ ∈ D.1 then _ else _
    rw [if_neg hκ]
  rw [hκF, Finset.add_sum_erase _ _ (Finset.mem_univ κ)]
  simp only [F, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, colSumVal]
  ring

theorem colZ_frandShare (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent sent' : C.Party → C.Party → Option (Msg E)) (ab : C.Party → Bool)
    (hab : ∀ k, k ∉ D.1 → ab k = false) (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (g : ℕ)
    (hiT : i ∈ C.holders T) (hg : g < c) :
    let rnd := frandShare D c known knownPairs fresh freshPair
    let inbox := fun j k => if k ∈ D.1 then sent k j else colOut1 K k (rnd k).1 (rnd k).2 (v k) c j
    colZ K i (rnd i).1 (rnd i).2 (v i) c (inbox i) (fun k => if k ∈ D.1 then sent' k i else
        if ab k = true then some .abort else colOut2 K k (rnd k).1 (rnd k).2 (v k) c (inbox k) i) T g =
      termValC K D known knownPairs fresh freshPair v sent sent' i T g := by
  intro rnd inbox
  have hcg : ¬ c ≤ g := Nat.not_le.mpr hg
  unfold colZ termValC
  rw [if_neg (by simp [hiT, hcg])]
  by_cases hT : T = (K.collector g).1
  · rw [if_pos hT, if_pos hT]
    by_cases hκi : (K.collector g).2 = i
    · rw [if_pos hκi]
      have hκ : (K.collector g).2 ∉ D.1 := hκi ▸ hi
      rw [if_neg hκ]
      have := colSum_frandShare K D known knownPairs fresh freshPair v sent g hg hκ
      simp only at this
      rw [← this]
      subst hκi; rfl
    · rw [if_neg hκi]
      by_cases hκ : (K.collector g).2 ∈ D.1
      · simp only [hκ, if_true]
      · simp only [hκ, if_false, hab _ hκ, Bool.false_eq_true, colOut2, if_pos (Ne.symm hκi), Msg.bitAt]
        have hmem : g ∈ forwardedTo K c (K.collector g).2 i := by
          simp only [forwardedTo, List.mem_filter, decide_eq_true_eq]
          exact ⟨mem_collectedBy K hg, hT ▸ hiT⟩
        rw [getD_map_idxOf hmem]
        exact colSum_frandShare K D known knownPairs fresh freshPair v sent g hg hκ
  · rw [if_neg hT, if_neg hT]
    exact frandShare_fst D known knownPairs fresh freshPair i T g hiT

end CollectorValues

section CollectorShift
variable [Field E] [Algebra Bit E]

theorem bit_add_self (a : Bit) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem colUVal_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh Δ : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (p : C.Party) (hp : p ∉ D.1) (δ : C.Party → Fin c → Bit) (hδ : ∀ k ∈ D.1, δ k = 0)
    (v : C.Party → ℕ → Bit) (j : C.Party) (hj : j ∉ D.1) (g : ℕ) (hg : g < c) :
    colUVal K D known knownPairs (fresh + Δ) (freshPair + pairShift p δ) v j g =
      colUVal K D known knownPairs fresh freshPair (fun _ _ => 0) j g + v j g +
        (if j = p then ∑ k ∈ Finset.univ.erase p, δ k ⟨g, hg⟩ else δ j ⟨g, hg⟩) +
        ∑ T ∈ Finset.univ.filter (fun T => T ≠ (K.collector g).1 ∧ K.owner T = j),
          (if KnownTo D.1 T then 0 else Δ T ⟨g, hg⟩) := by
  have hextra : ∑ k ∈ Finset.univ.erase j,
      (if h : j = k then 0 else if k ∈ D.1 then 0 else pairShift p δ (C.pairOf j k h) ⟨g, hg⟩) =
      if j = p then ∑ k ∈ Finset.univ.erase p, δ k ⟨g, hg⟩ else δ j ⟨g, hg⟩ := by
    have hterm : ∀ k ∈ Finset.univ.erase j,
        (if h : j = k then 0 else if k ∈ D.1 then 0 else pairShift p δ (C.pairOf j k h) ⟨g, hg⟩) =
        if j = p then δ k ⟨g, hg⟩ else if k = p then δ j ⟨g, hg⟩ else 0 := by
      intro k hk
      rw [dif_neg (Finset.ne_of_mem_erase hk).symm, pairShift_pairOf]
      by_cases hkD : k ∈ D.1
      · have hkp : k ≠ p := fun h => hp (h ▸ hkD)
        simp [hkD, hδ k hkD, hkp]
      · simp only [hkD, if_false]
        split_ifs <;> rfl
    rw [Finset.sum_congr rfl hterm]
    split_ifs with hjp
    · subst hjp; rfl
    · rw [Finset.sum_ite_eq']
      simp [Ne.symm hjp]
  unfold colUVal
  simp only [pairVal_add D knownPairs freshPair _ j _ g hg, randVal_add D known fresh Δ g hg,
    Finset.sum_add_distrib, hextra]
  ring

/-- The translation of the hidden terms other than `T0` and `T*` of gate `g` by `w`. -/
def Δ0C (K : Constants C E) (D : C.Coalition) (T0 : C.Term) {c : ℕ} (w : C.Term → Fin c → Bit) (T : C.Term)
    (g : Fin c) : Bit :=
  if ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g.val).1 then w T g else 0

/-- What a translation `Δ` of the terms adds to `u_j` at gate `g`. -/
def ownC (K : Constants C E) (D : C.Coalition) {c : ℕ} (Δ : C.Term → Fin c → Bit) (j : C.Party) (g : Fin c) : Bit :=
  ∑ T ∈ Finset.univ.filter (fun T => T ≠ (K.collector g.val).1 ∧ K.owner T = j), if KnownTo D.1 T then 0 else Δ T g

/-- The pair-stream translation at a gate with a corrupt collector, for each honest `j ≠ p`. -/
def δC (K : Constants C E) (D : C.Coalition) (T0 : C.Term) (p : C.Party) {c : ℕ} (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (j : C.Party) (g : Fin c) : Bit :=
  if (K.collector g.val).2 ∈ D.1 ∧ j ∉ D.1 ∧ j ≠ p then v j g.val + ownC K D (Δ0C K D T0 w) j g else 0

/-- The translation of `T0` at gate `g`. -/
def γC (K : Constants C E) (D : C.Coalition) (T0 : C.Term) {c : ℕ} (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (g : Fin c) : Bit :=
  ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g.val +
    ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g.val).1), w T g +
    if (K.collector g.val).2 ∉ D.1 ∧ ¬ KnownTo D.1 (K.collector g.val).1 ∧ (K.collector g.val).1 ≠ T0 then
      w (K.collector g.val).1 g else 0

def ΔC (K : Constants C E) (D : C.Coalition) (T0 : C.Term) {c : ℕ} (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (T : C.Term) (g : Fin c) : Bit :=
  Δ0C K D T0 w T g + if T = T0 ∧ T0 ≠ (K.collector g.val).1 then γC K D T0 v w g else 0

theorem ownC_sum (K : Constants C E) (D : C.Coalition) (T0 : C.Term) {c : ℕ} (w : C.Term → Fin c → Bit) (g : Fin c) :
    ∑ j ∈ Finset.univ.filter (· ∉ D.1), ownC K D (Δ0C K D T0 w) j g =
      ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g.val).1), w T g := by
  unfold ownC
  have hfib : ∀ j ∈ Finset.univ.filter (· ∉ D.1),
      Finset.univ.filter (fun T => T ≠ (K.collector g.val).1 ∧ K.owner T = j) =
      (Finset.univ.filter (fun T => T ≠ (K.collector g.val).1 ∧ K.owner T ∉ D.1)).filter (K.owner · = j) := by
    intro j hj
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    constructor
    · rintro ⟨hT, rfl⟩; exact ⟨⟨hT, hj⟩, rfl⟩
    · rintro ⟨⟨hT, -⟩, rfl⟩; exact ⟨hT, rfl⟩
  rw [Finset.sum_congr rfl fun j hj => by rw [hfib j hj], Finset.sum_fiberwise_of_maps_to
    (fun T hT => by simp at hT ⊢; exact hT.2)]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold Δ0C
  by_cases hk : KnownTo D.1 T
  · simp [hk]
  · have ho : K.owner T ∉ D.1 := fun h => hk ⟨_, h, K.owner_held T⟩
    by_cases hs : T = (K.collector g.val).1 <;> simp [hk, ho, hs]

theorem ownC_ΔC (K : Constants C E) (D : C.Coalition) (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) {c : ℕ}
    (v : C.Party → ℕ → Bit) (w : C.Term → Fin c → Bit) (j : C.Party) (g : Fin c) :
    ownC K D (ΔC K D T0 v w) j g = ownC K D (Δ0C K D T0 w) j g +
      if T0 ≠ (K.collector g.val).1 ∧ K.owner T0 = j then γC K D T0 v w g else 0 := by
  unfold ownC ΔC
  have hsplit : ∀ T, (if KnownTo D.1 T then 0 else Δ0C K D T0 w T g +
      if T = T0 ∧ T0 ≠ (K.collector g.val).1 then γC K D T0 v w g else 0) =
      (if KnownTo D.1 T then 0 else Δ0C K D T0 w T g) +
        if T = T0 then (if T0 ≠ (K.collector g.val).1 then γC K D T0 v w g else 0) else 0 := fun T => by
    by_cases hk : KnownTo D.1 T
    · have hne : T ≠ T0 := fun h => hT0 (h ▸ hk)
      simp [hk, hne]
    · by_cases hT : T = T0
      · subst hT; by_cases hs : T = (K.collector g.val).1 <;> simp [hk, hs]
      · simp [hk, hT]
  rw [Finset.sum_congr rfl fun T _ => hsplit T, Finset.sum_add_distrib, Finset.sum_ite_eq']
  congr 1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : T0 ≠ (K.collector g.val).1 <;> by_cases h2 : K.owner T0 = j <;> simp [h1, h2]

/-- At a gate with a corrupt collector, the translation keeps every honest `u_j`. -/
theorem colUVal_corrupt (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1) (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (j : C.Party) (hj : j ∉ D.1) (g : ℕ) (hg : g < c) (hκ : (K.collector g).2 ∈ D.1) :
    colUVal K D known knownPairs (fresh + ΔC K D T0 v w) (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w))
        v j g = colUVal K D known knownPairs fresh freshPair (fun _ _ => 0) j g := by
  have hδ : ∀ k ∈ D.1, δC K D T0 (K.owner T0) v w k = 0 := fun k hk => by funext g; simp [δC, hk]
  have hstar : T0 ≠ (K.collector g).1 := fun h => hT0 ⟨_, hκ, h ▸ K.collector_held g⟩
  rw [colUVal_shift K D known knownPairs fresh _ freshPair _ hp _ hδ v j hj g hg]
  have hown := ownC_ΔC K D T0 hT0 v w j ⟨g, hg⟩
  unfold ownC at hown
  rw [hown]
  have hsum := ownC_sum K D T0 w ⟨g, hg⟩
  simp only [Fin.val_mk] at hown hsum ⊢
  by_cases hjp : j = K.owner T0
  · subst hjp
    have hA : ∑ k ∈ Finset.univ.filter (· ∉ D.1), v k g +
        ∑ k ∈ Finset.univ.filter (· ∉ D.1), ownC K D (Δ0C K D T0 w) k ⟨g, hg⟩ =
        v (K.owner T0) g + ownC K D (Δ0C K D T0 w) (K.owner T0) ⟨g, hg⟩ +
          ∑ k ∈ Finset.univ.erase (K.owner T0), δC K D T0 (K.owner T0) v w k ⟨g, hg⟩ := by
      rw [← Finset.sum_add_distrib, Finset.sum_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ (K.owner T0)),
        if_pos hj]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkp := Finset.ne_of_mem_erase hk
      by_cases hkD : k ∈ D.1
      · simp [δC, hkD]
      · simp [δC, hkD, hκ, hkp]
    have h2 := bit_add_self (∑ k ∈ Finset.univ.filter (· ∉ D.1), v k g +
      ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g).1), w T ⟨g, hg⟩)
    simp only [if_true, hstar, ne_eq, not_false_eq_true, and_self, γC, Fin.val_mk, hκ, not_true_eq_false,
      false_and, if_false, add_zero]
    unfold ownC at hA hsum
    simp only [Fin.val_mk] at hA hsum
    linear_combination -hA + hsum + h2
  · have hoj : ¬ K.owner T0 = j := fun h => hjp h.symm
    simp only [hjp, if_false, hoj, and_false, add_zero, δC, Fin.val_mk, hκ, hj, not_false_eq_true, ne_eq, true_and]
    unfold ownC
    simp only [Fin.val_mk, ite_true, ne_eq]
    have := bit_add_self (v j g + ∑ T ∈ Finset.univ.filter (fun T => T ≠ (K.collector g).1 ∧ K.owner T = j),
      (if KnownTo D.1 T then 0 else Δ0C K D T0 w T ⟨g, hg⟩))
    simp only [ne_eq] at this
    linear_combination this

end CollectorShift

section CollectorTerms
variable [Field E] [Algebra Bit E]

/-- At a gate with an honest collector, the translation moves its sum. -/
theorem colSumVal_honest (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1) (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (sent : C.Party → C.Party → Option (Msg E)) (g : ℕ) (hg : g < c)
    (hκ : (K.collector g).2 ∉ D.1) :
    colSumVal K D known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v sent (K.collector g).2 g =
      colSumVal K D known knownPairs fresh freshPair (fun _ _ => 0) sent (K.collector g).2 g +
        ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g +
        ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g).1), w T ⟨g, hg⟩ +
        (if T0 ≠ (K.collector g).1 then γC K D T0 v w ⟨g, hg⟩ else 0) := by
  have hδ : ∀ k ∈ D.1, δC K D T0 (K.owner T0) v w k = 0 := fun k hk => by funext g; simp [δC, hk]
  have hδg : ∀ k, δC K D T0 (K.owner T0) v w k ⟨g, hg⟩ = 0 := fun k => by simp [δC, hκ]
  unfold colSumVal
  have hj : ∀ j ∈ Finset.univ.filter (· ∉ D.1),
      colUVal K D known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v j g =
      colUVal K D known knownPairs fresh freshPair (fun _ _ => 0) j g + v j g +
        (ownC K D (Δ0C K D T0 w) j ⟨g, hg⟩ +
          if T0 ≠ (K.collector g).1 ∧ K.owner T0 = j then γC K D T0 v w ⟨g, hg⟩ else 0) := by
    intro j hjm
    rw [colUVal_shift K D known knownPairs fresh _ freshPair _ hp _ hδ v j (Finset.mem_filter.mp hjm).2 g hg]
    have hown := ownC_ΔC K D T0 hT0 v w j ⟨g, hg⟩
    unfold ownC at hown ⊢
    simp only [Fin.val_mk] at hown
    rw [hown]
    simp [hδg]
  rw [Finset.sum_congr rfl hj]
  simp only [Finset.sum_add_distrib, ownC_sum K D T0 w ⟨g, hg⟩, Fin.val_mk]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilt : (Finset.univ.filter (· ∉ D.1)).filter (fun j => T0 ≠ (K.collector g).1 ∧ K.owner T0 = j) =
      if T0 ≠ (K.collector g).1 then {K.owner T0} else ∅ := by
    ext j
    split_ifs with h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, rfl⟩; rfl
      · rintro rfl; exact ⟨hp, h, rfl⟩
    · simp [h]
  rw [hfilt]
  split_ifs <;> simp <;> ring

theorem termValC_viewer (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent sent' sent'' : C.Party → C.Party → Option (Msg E)) (i i' : C.Party) (T : C.Term)
    (g : ℕ) (hT : ¬ (T = (K.collector g).1 ∧ (K.collector g).2 ∈ D.1)) :
    termValC K D known knownPairs fresh freshPair v sent sent' i T g =
      termValC K D known knownPairs fresh freshPair v sent sent'' i' T g := by
  unfold termValC
  split_ifs with h1 h2
  · exact absurd ⟨h1, h2⟩ hT
  · rfl
  · rfl

/-- A hidden term is the simulated value with no corrupt message plus what corrupt operators send to its collector. -/
def cbC (K : Constants C E) (D : C.Coalition) {c : ℕ} (sent : C.Party → C.Party → Option (Msg E)) (T : C.Term)
    (g : Fin c) : Bit :=
  if T = (K.collector g.val).1 ∧ (K.collector g.val).2 ∉ D.1 then
    ∑ k ∈ D.1, Msg.bitAt (sent k (K.collector g.val).2) ((collectedBy K c (K.collector g.val).2).idxOf g.val) else 0

theorem termValC_hidden (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent sent' : C.Party → C.Party → Option (Msg E)) (i i' : C.Party) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (g : ℕ) (hg : g < c) :
    termValC K D known knownPairs fresh freshPair v sent sent' i T g =
      termValC K D known knownPairs fresh freshPair v (fun _ _ => none) (fun _ _ => none) i' T g +
        cbC K D sent T ⟨g, hg⟩ := by
  unfold termValC cbC
  simp only [Fin.val_mk]
  by_cases hs : T = (K.collector g).1
  · have hκ : (K.collector g).2 ∉ D.1 := fun h => hT ⟨_, h, hs ▸ K.collector_held g⟩
    simp only [hs, hκ, if_true, if_false, not_false_eq_true, and_self, colSumVal]
    simp [Msg.bitAt]
  · simp [hs]

theorem termValC_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1) (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (sent sent' : C.Party → C.Party → Option (Msg E)) (i : C.Party) (T : C.Term)
    (hT : T ≠ T0) (g : ℕ) (hg : g < c) :
    termValC K D known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v sent sent' i T g =
      termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' i T g +
        if KnownTo D.1 T then 0 else w T ⟨g, hg⟩ := by
  unfold termValC
  by_cases hs : T = (K.collector g).1
  · rw [if_pos hs, if_pos hs]
    by_cases hκ : (K.collector g).2 ∈ D.1
    · have hk : KnownTo D.1 T := ⟨_, hκ, hs ▸ K.collector_held g⟩
      simp [hκ, hk]
    · rw [if_neg hκ, if_neg hκ, colSumVal_honest K D known knownPairs fresh freshPair T0 hT0 hp v w sent g hg hκ]
      have hne : T0 ≠ (K.collector g).1 := fun h => hT (hs.trans h.symm)
      subst hs
      simp only [if_pos hne, γC, Fin.val_mk, hκ, not_false_eq_true, true_and, Ne.symm hne, and_true]
      have h2 := bit_add_self (∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g +
        ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g).1), w T ⟨g, hg⟩)
      by_cases hk : KnownTo D.1 (K.collector g).1
      · simp only [hk, hT, ne_eq, not_true_eq_false, not_false_eq_true, false_and, true_and, if_false, if_true,
          add_zero]
        linear_combination h2
      · simp only [hk, hT, ne_eq, not_false_eq_true, true_and, if_true, if_false]
        linear_combination h2
  · rw [if_neg hs, if_neg hs, randVal_add D known fresh _ g hg]
    congr 1
    unfold ΔC Δ0C
    by_cases hk : KnownTo D.1 T
    · simp [hk]
    · simp [hk, hT, hs]

theorem termValC_shift_T0 (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1) (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (sent sent' : C.Party → C.Party → Option (Msg E)) (i : C.Party) (g : ℕ) (hg : g < c) :
    termValC K D known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v sent sent' i T0 g =
      termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' i T0 g +
        ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g +
        ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0), w T ⟨g, hg⟩ := by
  have hsplit : ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0), w T ⟨g, hg⟩ =
      ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g).1), w T ⟨g, hg⟩ +
        if ¬ KnownTo D.1 (K.collector g).1 ∧ (K.collector g).1 ≠ T0 then w (K.collector g).1 ⟨g, hg⟩ else 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun T => T ≠ (K.collector g).1)]
    congr 1
    · rw [Finset.filter_filter]; refine Finset.sum_congr (Finset.filter_congr fun T _ => by tauto) fun _ _ => rfl
    · rw [Finset.filter_filter]
      split_ifs with h
      · rw [Finset.sum_eq_single_of_mem (K.collector g).1 (by simp [h.1, h.2])]
        intro T hT hne; simp at hT; exact absurd hT.2 (by simpa using hne)
      · refine Finset.sum_eq_zero fun T hT => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hT
        exact absurd ⟨hT.2 ▸ hT.1.1, hT.2 ▸ hT.1.2⟩ h
  unfold termValC
  by_cases hs : T0 = (K.collector g).1
  · have hκ : (K.collector g).2 ∉ D.1 := fun h => hT0 ⟨_, h, hs ▸ K.collector_held g⟩
    rw [if_pos hs, if_pos hs, if_neg hκ, if_neg hκ,
      colSumVal_honest K D known knownPairs fresh freshPair T0 hT0 hp v w sent g hg hκ, if_neg (not_not.mpr hs)]
    have hf : Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g).1) =
        Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0) :=
      Finset.filter_congr fun T _ => by rw [← hs]; tauto
    rw [hf, add_zero]
  · rw [if_neg hs, if_neg hs, randVal_add D known fresh _ g hg, if_neg hT0, hsplit]
    unfold ΔC Δ0C γC
    simp only [Fin.val_mk, ne_eq, not_true_eq_false, and_false, false_and, if_false, zero_add, true_and, hs,
      not_false_eq_true, if_true]
    by_cases hκ : (K.collector g).2 ∈ D.1
    · have hk : KnownTo D.1 (K.collector g).1 := ⟨_, hκ, K.collector_held g⟩
      simp [hκ, hk]
      ring
    · simp [hκ]
      ring

end CollectorTerms

section CollectorPointwise
variable [Field E] [Algebra Bit E]

/-- The honest round-one inboxes of a collector reshare. -/
def colInbox (K : Constants C E) (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent : C.Party → C.Party → Option (Msg E)) : C.Party → Mail C E :=
  fun i k => if k ∈ D.1 then sent k i else colOut1 K k (rnd k).1 (rnd k).2 (v k) c i

def colMsgs1 (K : Constants C E) (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) :
    C.Party → C.Party → Option (Msg E) :=
  fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 then colOut1 K i (rnd i).1 (rnd i).2 (v i) c c' else none

def colMsgs2 (K : Constants C E) (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent : C.Party → C.Party → Option (Msg E)) : C.Party → C.Party → Option (Msg E) :=
  fun c' i => if c' ∈ D.1 ∧ i ∉ D.1 ∧ ¬ anyAbort (colInbox K D c rnd v sent i) = true then
    colOut2 K i (rnd i).1 (rnd i).2 (v i) c (colInbox K D c rnd v sent i) c' else none

def colOuts (K : Constants C E) (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent sent' : C.Party → C.Party → Option (Msg E)) : C.Party → Option (Shares C Bit) :=
  fun i => if i ∈ D.1 ∨ anyAbort (colInbox K D c rnd v sent i) = true then none else
    let forward : Mail C E := fun k => if k ∈ D.1 then sent' k i else
      if anyAbort (colInbox K D c rnd v sent k) = true then some .abort else
        colOut2 K k (rnd k).1 (rnd k).2 (v k) c (colInbox K D c rnd v sent k) i
    if anyAbort forward then none else some (colZ K i (rnd i).1 (rnd i).2 (v i) c (colInbox K D c rnd v sent i) forward)

theorem anyAbort_colInbox (K : Constants C E) (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (v : C.Party → ℕ → Bit) (sent : C.Party → C.Party → Option (Msg E)) (i : C.Party) :
    anyAbort (colInbox K D c rnd v sent i) = anyAbort (fun k => if k ∈ D.1 then sent k i else none) := by
  unfold anyAbort colInbox
  congr 1; funext k
  by_cases hk : k ∈ D.1
  · simp [hk]
  · simp only [hk, if_false, colOut1]; split_ifs <;> rfl

theorem anyAbort_colForward (K : Constants C E) (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (v : C.Party → ℕ → Bit) (sent sent' : C.Party → C.Party → Option (Msg E)) (i : C.Party) :
    anyAbort (fun k => if k ∈ D.1 then sent' k i else
      if anyAbort (colInbox K D c rnd v sent k) = true then some .abort else
        colOut2 K k (rnd k).1 (rnd k).2 (v k) c (colInbox K D c rnd v sent k) i) =
    anyAbort (fun k => if k ∈ D.1 then sent' k i else
      if anyAbort (fun k' => if k' ∈ D.1 then sent k' k else none) = true then some .abort else none) := by
  unfold anyAbort
  congr 1; funext k
  by_cases hk : k ∈ D.1
  · simp [hk]
  · have h := anyAbort_colInbox K D c rnd v sent k
    unfold anyAbort at h
    simp only [hk, if_false, h]
    unfold colOut2
    split_ifs <;> rfl

end CollectorPointwise

section CollectorPointwise2
variable [Field E] [Algebra Bit E]

theorem colMsgs1_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1) (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) :
    colMsgs1 K D c (frandShare D c known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w))) v =
      colMsgs1 K D c (frandShare D c known knownPairs fresh freshPair) (fun _ _ => 0) := by
  funext c' i
  unfold colMsgs1
  split_ifs with h
  · unfold colOut1
    split_ifs with h2
    · congr 2
      refine List.map_congr_left fun g hg => ?_
      simp only [collectedBy, List.mem_filter, List.mem_range, decide_eq_true_eq] at hg
      rw [colU_frandShare, colU_frandShare (v := fun _ _ => 0),
        colUVal_corrupt K D known knownPairs fresh freshPair T0 hT0 hp v w i h.2 g hg.1 (hg.2 ▸ h.1)]
    · rfl
  · rfl

theorem colMsgs2_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1) (v : C.Party → ℕ → Bit)
    (w : C.Term → Fin c → Bit) (sent : C.Party → C.Party → Option (Msg E)) :
    colMsgs2 K D c (frandShare D c known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w))) v sent =
      colMsgs2 K D c (frandShare D c known knownPairs fresh freshPair) (fun _ _ => 0) sent := by
  funext c' i
  unfold colMsgs2
  simp only [anyAbort_colInbox]
  split_ifs with h
  · unfold colOut2
    split_ifs with h2
    · congr 2
      refine List.map_congr_left fun g hg => ?_
      simp only [forwardedTo, collectedBy, List.mem_filter, List.mem_range, decide_eq_true_eq] at hg
      obtain ⟨⟨hgc, hκ⟩, hc'⟩ := hg
      subst hκ
      have hκD : (K.collector g).2 ∉ D.1 := h.2.1
      have hk : KnownTo D.1 (K.collector g).1 := ⟨c', h.1, hc'⟩
      have hne : T0 ≠ (K.collector g).1 := fun he => hT0 (he ▸ hk)
      have e1 := colSum_frandShare K D known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v sent g hgc hκD
      have e0 := colSum_frandShare K D known knownPairs fresh freshPair (fun _ _ => 0) sent g hgc hκD
      simp only at e1 e0
      unfold colInbox
      rw [e1, e0, colSumVal_honest K D known knownPairs fresh freshPair T0 hT0 hp v w sent g hgc hκD, if_pos hne]
      simp only [γC, Fin.val_mk, hκD, hk, not_true_eq_false, false_and, and_false, if_false, add_zero, not_false_eq_true,
        true_and]
      have h2 := bit_add_self (∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g +
        ∑ T ∈ Finset.univ.filter (fun T => ¬ KnownTo D.1 T ∧ T ≠ T0 ∧ T ≠ (K.collector g).1), w T ⟨g, hgc⟩)
      linear_combination h2
    · rfl
  · rfl

end CollectorPointwise2

section CollectorOutputs
variable [Field E] [Algebra Bit E]

theorem filler_collector_corrupt (K : Constants C E) (D : C.Coalition) (T : C.Term) (g : ℕ) :
    (∃ j ∈ D.1, filler K .collector T g = some j) ↔ T = (K.collector g).1 ∧ (K.collector g).2 ∈ D.1 := by
  simp only [filler]
  constructor
  · rintro ⟨j, hj, h⟩
    split_ifs at h with h1
    · cases h; exact ⟨h1.symm, hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, by rw [if_pos h1.symm]⟩

theorem colZ_colInbox (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (v : C.Party → ℕ → Bit) (sent sent' : C.Party → C.Party → Option (Msg E))
    (hall : ∀ k, k ∉ D.1 → anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E))) = false)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (g : ℕ) (hiT : i ∈ C.holders T) (hg : g < c) :
    colZ K i (frandShare D c known knownPairs fresh freshPair i).1 (frandShare D c known knownPairs fresh freshPair i).2
        (v i) c (colInbox K D c (frandShare D c known knownPairs fresh freshPair) v sent i)
        (fun k => if k ∈ D.1 then sent' k i else
          if anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E))) = true then some .abort else
            colOut2 K k (frandShare D c known knownPairs fresh freshPair k).1
              (frandShare D c known knownPairs fresh freshPair k).2 (v k) c
              (colInbox K D c (frandShare D c known knownPairs fresh freshPair) v sent k) i) T g =
      termValC K D known knownPairs fresh freshPair v sent sent' i T g :=
  colZ_frandShare K D known knownPairs fresh freshPair v sent sent'
    (fun k => anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E)))) hall i hi T g hiT hg

theorem colOuts_shift (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (T0 : C.Term) (hlacked : lackedTerm D.1 = some T0) (hT0 : ¬ KnownTo D.1 T0) (hp : K.owner T0 ∉ D.1)
    (v : C.Party → ℕ → Bit) (w : C.Term → Fin c → Bit)
    (product : ℕ → Bit) (hproduct : ∀ g, product g = ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
    (sent sent' : C.Party → C.Party → Option (Msg E)) :
    colOuts K D c (frandShare D c known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w))) v sent sent' =
      idealOut D (filler K .collector) product
        (colReply K D c (frandShare D c known knownPairs fresh freshPair)
          (colInbox K D c (frandShare D c known knownPairs fresh freshPair) (fun _ _ => 0) sent) sent')
        (w + (fun T g => termValC K D known knownPairs fresh freshPair (fun _ _ => 0) (fun _ _ => none)
          (fun _ _ => none) (refHolder D T) T g.val) + cbC K D sent) := by
  funext i
  unfold colOuts idealOut colReply
  dsimp only
  by_cases hi : i ∈ D.1
  · simp [hi]
  simp only [anyAbort_colForward]
  simp only [anyAbort_colInbox]
  by_cases h1 : anyAbort (fun k => if k ∈ D.1 then sent k i else (none : Option (Msg E))) = true
  · simp [hi, h1]
  by_cases h2 : anyAbort (fun k => if k ∈ D.1 then sent' k i else
      if anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E))) = true then some .abort
      else none) = true
  · simp [hi, h2]
  have hall : ∀ k, k ∉ D.1 → anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E))) = false := by
    intro k hk
    by_contra hc
    apply h2
    unfold anyAbort
    rw [List.any_eq_true]
    refine ⟨k, by simp [Committee.parties], ?_⟩
    have hc' := Bool.eq_true_of_not_eq_false hc
    unfold anyAbort at hc'
    simp only [hk, if_false, hc', if_true]
    rfl
  simp only [hi, h1, h2, Bool.false_eq_true, or_self, if_false, Finset.mem_filter, Finset.mem_univ, true_and,
    not_false_eq_true, Bool.not_eq_true, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, and_self,
    not_true_eq_false, Option.some.injEq]
  funext T g
  have href : ∀ T, refHolder D T ∉ D.1 := fun T => (refHolder_spec D T).2
  have hrefh : ∀ T, refHolder D T ∈ C.holders T := fun T => (refHolder_spec D T).1
  by_cases hTg : i ∈ C.holders T ∧ g < c
  swap
  · rw [if_neg hTg]
    unfold colZ
    rw [if_pos (by rw [not_and_or, not_lt] at hTg; exact hTg)]
  rw [if_pos hTg]
  have hz1 := colZ_colInbox K D known knownPairs (fresh + ΔC K D T0 v w)
    (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v sent sent' hall
  have hz0 := colZ_colInbox K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' hall
  rw [hz1 i hi T g hTg.1 hTg.2]
  simp only [hz0 _ (href _) _ g (hrefh _) hTg.2, hz0 i hi T g hTg.1 hTg.2, dif_pos hTg.2, Pi.add_apply,
    filler_collector_corrupt]
  have hshift := termValC_shift K D known knownPairs fresh freshPair T0 hT0 hp v w sent sent'
  have hbase : ∀ T', T' ≠ T0 → (if KnownTo D.1 T' then
      termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' (refHolder D T') T' g else
      w T' ⟨g, hTg.2⟩ + termValC K D known knownPairs fresh freshPair (fun _ _ => 0) (fun _ _ => none)
        (fun _ _ => none) (refHolder D T') T' g + cbC K D sent T' ⟨g, hTg.2⟩) =
      termValC K D known knownPairs (fresh + ΔC K D T0 v w)
        (freshPair + pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w)) v sent sent' (refHolder D T') T' g := by
    intro T' hT'
    rw [hshift (refHolder D T') T' hT' g hTg.2]
    split_ifs with hk
    · rw [add_zero]
    · rw [termValC_hidden K D known knownPairs fresh freshPair _ sent sent' (refHolder D T') (refHolder D T') T' hk g
        hTg.2]
      ring
  by_cases hT : T = T0
  · subst hT
    have hnf : ¬ (T = (K.collector g).1 ∧ (K.collector g).2 ∈ D.1) :=
      fun ⟨h1, h2⟩ => hT0 ⟨_, h2, h1 ▸ K.collector_held g⟩
    rw [if_pos hlacked, if_neg hnf, add_zero,
      Finset.sum_congr rfl (fun T' hT' => hbase T' (Finset.ne_of_mem_erase hT'))]
    rw [termValC_shift_T0 K D known knownPairs fresh freshPair T hT0 hp v w sent sent' i g hTg.2,
      termValC_viewer K D known knownPairs fresh freshPair _ sent sent' sent' i (refHolder D T) T g hnf, hproduct]
    have hsum : ∑ T', termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' (refHolder D T') T' g =
        termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' (refHolder D T) T g +
          ∑ T' ∈ Finset.univ.erase T,
            termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' (refHolder D T') T' g :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ T)).symm
    have hw : ∑ T' ∈ Finset.univ.erase T, termValC K D known knownPairs (fresh + ΔC K D T v w)
        (freshPair + pairShift (K.owner T) (δC K D T (K.owner T) v w)) v sent sent' (refHolder D T') T' g =
        ∑ T' ∈ Finset.univ.erase T,
          termValC K D known knownPairs fresh freshPair (fun _ _ => 0) sent sent' (refHolder D T') T' g +
        ∑ T' ∈ Finset.univ.filter (fun T' => ¬ KnownTo D.1 T' ∧ T' ≠ T), w T' ⟨g, hTg.2⟩ := by
      rw [Finset.sum_congr rfl fun T' hT' => hshift (refHolder D T') T' (Finset.ne_of_mem_erase hT') g hTg.2,
        Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, zero_add]
      congr 2
      ext T'; simp [and_comm]
    rw [hsum, hw]
    have h2 := bit_add_self (∑ T' ∈ Finset.univ.filter (fun T' => ¬ KnownTo D.1 T' ∧ T' ≠ T), w T' ⟨g, hTg.2⟩)
    linear_combination h2
  · rw [if_neg (fun h => hT (Option.some.inj (h.symm.trans hlacked))), hbase T hT]
    by_cases hcf : T = (K.collector g).1 ∧ (K.collector g).2 ∈ D.1
    · have hk : KnownTo D.1 T := ⟨_, hcf.2, hcf.1 ▸ K.collector_held g⟩
      rw [if_pos hcf, hshift i T hT g hTg.2, hshift (refHolder D T) T hT g hTg.2]
      simp only [if_pos hk, add_zero]
      ring
    · rw [if_neg hcf, add_zero]
      exact termValC_viewer K D known knownPairs _ _ v sent sent' sent' i (refHolder D T) T g hcf

end CollectorOutputs
section CollectorCoupling
variable [Field E] [Algebra Bit E]

theorem evalDist_shift2 {α β γ δ : Type} [AddGroup α] [AddGroup β] [AddGroup γ]
    [SampleableType α] [SampleableType β] [SampleableType γ]
    (F : α → β → ProbComp δ) (G H : α → β → γ → ProbComp δ) (τ : γ → α × β)
    (h : ∀ w x y, F (x + (τ w).1) (y + (τ w).2) = H x y w)
    (h' : ∀ x y, 𝒟[do let w ← $ᵗ γ; H x y w] = 𝒟[do let w ← $ᵗ γ; G x y w]) :
    𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; F x y] = 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y w] := by
  have h1 : ∀ w, 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; F x y] = 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; H x y w] := fun w => by
    simp only [← h w]
    rw [evalDist_bind_add_uniform (τ w).1 (fun x => do let y ← $ᵗ β; F x (y + (τ w).2))]
    exact evalDist_bind_congr_all _ fun x => (evalDist_bind_add_uniform (τ w).2 (F x)).symm
  calc 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; F x y]
      = 𝒟[do let w ← $ᵗ γ; let x ← $ᵗ α; let y ← $ᵗ β; F x y] := (evalDist_uniform_bind_const _).symm
    _ = 𝒟[do let w ← $ᵗ γ; let x ← $ᵗ α; let y ← $ᵗ β; H x y w] := evalDist_bind_congr_all _ h1
    _ = 𝒟[do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; H x y w] := by
        rw [evalDist_bind_bind_swap]
        exact evalDist_bind_congr_all _ fun x => evalDist_bind_bind_swap _ _ _
    _ = _ := evalDist_bind_congr_all _ fun x => evalDist_bind_congr_all _ fun y => h' x y

/-- A translation of a free sample by a value that a later step fixes keeps the distribution. -/
theorem WEq.shift_after (prims : Primitives) {β γ δ : Type} [AddGroup γ] [SampleableType γ]
    (R1 : OracleComp (WorldSpec C) β) (L : β → γ → OracleComp (WorldSpec C) δ) (a : β → γ) :
    WEq prims (free (liftComp ($ᵗ γ) (LocalSpec C)) >>= fun w => R1 >>= fun b => L b (w + a b))
      (free (liftComp ($ᵗ γ) (LocalSpec C)) >>= fun w => R1 >>= fun b => L b w) := by
  refine WEq.trans prims (WEq.free_swap prims _ _ _) (WEq.trans prims ?_ (WEq.symm prims (WEq.free_swap prims _ _ _)))
  refine WEq.bind_right prims _ fun b => fun s => ?_
  rw [world_run_free_bind, world_run_free_bind]
  exact evalDist_bind_add_uniform (a b) fun w => (simulateQ (world prims) (L b w)).run.run s

/-- The honest outputs of `F_mult` when every honest operator aborts. -/
theorem idealOut_none (D : C.Coalition) {c : ℕ} (filled : C.Term → ℕ → Option C.Party) (product : ℕ → Bit)
    (f : C.Term → Fin c → Bit) :
    idealOut D filled product (fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, ∅) f = fun _ => none := by
  funext i; simp [idealOut]

/-- The first round of the collector simulator. -/
def colRound1 (K : Constants C E) (D : C.Coalition) {I Rp : Type} (A : Adversary C E I Unit Rp) (c : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (st : A.State) :
    OracleComp (WorldSpec C) (A.State × (C.Party → C.Party → Option (Msg E))) :=
  counted (liftComp (A.round st (colMsgs1 K D c rnd (fun _ _ => 0))) (SimulatorSpec C))

/-- The rest of the collector simulator after its first round. -/
def colRest (K : Constants C E) (D : C.Coalition) {I Rp : Type} (A : Adversary C E I Unit Rp) (c : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (b : A.State × (C.Party → C.Party → Option (Msg E))) :
    OracleComp (WorldSpec C) (A.State × ((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party)) :=
  if ∀ i, i ∉ D.1 → anyAbort (colInbox K D c rnd (fun _ _ => 0) b.2 i) = true then
    pure (b.1, (fun _ => 0, fun _ _ => 0, fun _ _ _ => 0, ∅)) else do
  let b' ← counted (liftComp (A.round b.1 (colMsgs2 K D c rnd (fun _ _ => 0) b.2)) (SimulatorSpec C))
  pure (b'.1, colReply K D c rnd (colInbox K D c rnd (fun _ _ => 0) b.2) b'.2)

/-- The distinguisher on the outputs of `F_mult` with the collector filler. -/
def colTail (K : Constants C E) (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Shares C Bit)) {c : ℕ}
    (product : ℕ → Bit) (f : C.Term → Fin c → Bit)
    (ans : σ × ((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party)) :
    OracleComp (WorldSpec C) Bool :=
  counted (liftComp (Z (ans.1, idealOut D (filler K .collector) product ans.2 f)) (SimulatorSpec C))

/-- The shift of the fresh terms of `F_mult` that the collector coupling fixes after the first round. -/
def colShiftF (K : Constants C E) (D : C.Coalition) {c : ℕ} (known : Shares C Bit)
    (knownPairs : C.Party → C.Party → ℕ → Bit) (fresh : C.Term → Fin c → Bit) (freshPair : C.Pair → Fin c → Bit)
    (sent : C.Party → C.Party → Option (Msg E)) : C.Term → Fin c → Bit :=
  (fun T (g : Fin c) => termValC K D known knownPairs fresh freshPair (fun _ _ => 0) (fun _ _ => none)
    (fun _ _ => none) (refHolder D T) T g.val) + cbC K D sent

/-- The run of a collector reshare after `F_rand` and the run of `F_mult` with the collector simulator
agree (GS20, Lemma 4), gate by gate. -/
theorem col_coupling (prims : Primitives) (K : Constants C E) (D : C.Coalition) {I : Type}
    (A : Adversary C E I Unit (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
    (Z : Distinguisher C A.State (Shares C Bit)) (start : OracleComp (WorldSpec C) A.State) (c : ℕ)
    (v : C.Party → ℕ → Bit) (product : ℕ → Bit)
    (hproduct : ∀ g, product g = ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g) :
    WEq prims
      (do
        let st ← start
        let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → Bit)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → Bit)) (LocalSpec C))
        let rnd := frandShare D c a.2.1 a.2.2 fresh freshPair
        let b ← counted (liftComp (A.round a.1 (colMsgs1 K D c rnd v)) (SimulatorSpec C))
        let r ← if ∀ i, i ∉ D.1 → anyAbort (colInbox K D c rnd v b.2 i) = true then pure (b.1, fun _ => none) else do
          let b' ← counted (liftComp (A.round b.1 (colMsgs2 K D c rnd v b.2)) (SimulatorSpec C))
          pure (b'.1, colOuts K D c rnd v b.2 b'.2)
        counted (liftComp (Z r) (SimulatorSpec C)))
      (do
        let st ← start
        let a ← counted (liftComp (A.answer st ()) (SimulatorSpec C))
        let fresh ← free (liftComp ($ᵗ (C.Term → Fin c → Bit)) (LocalSpec C))
        let freshPair ← free (liftComp ($ᵗ (C.Pair → Fin c → Bit)) (LocalSpec C))
        let freshF ← free (liftComp ($ᵗ (C.Term → Fin c → Bit)) (LocalSpec C))
        let b ← colRound1 K D A c (frandShare D c a.2.1 a.2.2 fresh freshPair) a.1
        let ans ← colRest K D A c (frandShare D c a.2.1 a.2.2 fresh freshPair) b
        colTail K D Z product freshF ans) := by
  obtain ⟨T0, hT0, hk⟩ := lackedTerm_spec D
  have hp : K.owner T0 ∉ D.1 := fun h => hk ⟨_, h, K.owner_held T0⟩
  refine WEq.bind_right prims _ fun st => WEq.bind_right prims _ fun a => fun s => ?_
  simp only [world_run_free_bind]
  refine evalDist_shift2 _ _ (fun fresh freshPair w => (simulateQ (world prims)
      (colRound1 K D A c (frandShare D c a.2.1 a.2.2 fresh freshPair) a.1 >>= fun b =>
        colRest K D A c (frandShare D c a.2.1 a.2.2 fresh freshPair) b >>= fun ans =>
        colTail K D Z product (w + colShiftF K D a.2.1 a.2.2 fresh freshPair b.2) ans)).run.run s)
    (fun w => (ΔC K D T0 v w, pairShift (K.owner T0) (δC K D T0 (K.owner T0) v w))) (fun w fresh freshPair => ?_)
    (fun fresh freshPair => ?_)
  · dsimp only
    rw [colMsgs1_shift K D a.2.1 a.2.2 fresh freshPair T0 hk hp v w]
    refine congrArg (fun oa => (simulateQ (world prims) oa).run.run s) (bind_congr' _ fun b => ?_)
    simp only [anyAbort_colInbox, colRest, colTail]
    split_ifs with hall
    · simp only [pure_bind, idealOut_none]
    · rw [colMsgs2_shift K D a.2.1 a.2.2 fresh freshPair T0 hk hp v w]
      simp only [bind_assoc, pure_bind]
      refine bind_congr' _ fun b' => ?_
      rw [colOuts_shift K D a.2.1 a.2.2 fresh freshPair T0 hT0 hk hp v w product hproduct, add_assoc]
      rfl
  · have := WEq.shift_after prims (colRound1 K D A c (frandShare D c a.2.1 a.2.2 fresh freshPair) a.1)
      (fun b f => colRest K D A c (frandShare D c a.2.1 a.2.2 fresh freshPair) b >>= colTail K D Z product f)
      (fun b => colShiftF K D a.2.1 a.2.2 fresh freshPair b.2) s
    rw [world_run_free_bind, world_run_free_bind] at this
    exact this

theorem ite_bind' {m : Type → Type} [Monad m] {α β : Type} (p : Prop) [Decidable p] (a b : m α) (f : α → m β) :
    (if p then a else b) >>= f = if p then a >>= f else b >>= f := by
  split_ifs <;> rfl

theorem counted_liftComp_ite {α : Type} (p : Prop) [Decidable p] (a b : OracleComp (LocalSpec C) α) :
    counted (liftComp (if p then a else b) (SimulatorSpec C)) =
      if p then counted (liftComp a (SimulatorSpec C)) else counted (liftComp b (SimulatorSpec C)) := by
  split_ifs <;> rfl

theorem multCollectorCoupling (prims : Primitives) (K : Constants C E) : MultCollectorCoupling prims K := by
  intro D A x z Z hx
  obtain ⟨j0, hj0, hfirst⟩ := firstInput_honest D x
  have hxc : ∀ i, i ∉ D.1 → (x i).2.2 = (x j0).2.2 := fun i hi => hx i j0 hi hj0
  unfold distinguish
  rw [realExecution_multCollector]
  have hc := firstInput_eq_of_same D (fun i => (x i).2.2) hx j0 hj0
  generalize firstInput (fun i => if i ∈ D.1 then none else some (x i).2.2) = c at hc ⊢
  subst hc
  unfold FmultBit
  rw [idealExecution_Fmult]
  simp only [colSim, colSimAnswer, liftComp_bind, counted_bind, bind_assoc, liftComp_pure, counted_pure,
    pure_bind, worldRoles, fmultOut_eq]
  rw [hfirst]
  refine WEq.trans prims (WEq.of_eq prims ?hreal) (WEq.trans prims (col_coupling prims K D A Z
    (counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))) (x j0).2.2
    (fun i => mulRep K (localContext i) (x i).1 (x i).2.1)
    (fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), (((fun i => if i ∈ D.1 then none else some (x i)) i).map
      fun y => mulRep K (localContext i) y.1 y.2.1 g).getD 0) ?hprod) ?hideal)
  case hprod =>
    intro g
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [(Finset.mem_filter.mp hi).2]
  case hreal =>
    generalize (x j0).2.2 = c at hxc ⊢
    unfold colMsgs1 colMsgs2 colOuts colInbox
    simp (maxSteps := 2000000) +contextual only [hxc, not_false_eq_true, ite_or,
      ite_bind', pure_bind, bind_assoc]
  case hideal =>
    refine WEq.symm prims (WEq.bind_right prims _ fun st => WEq.bind_right prims _ fun a => ?_)
    refine WEq.trans prims (WEq.of_eq prims ?e1) (WEq.trans prims (WEq.sim_samples prims ($ᵗ (C.Term → Fin (x j0).2.2 → Bit))
      ($ᵗ (C.Pair → Fin (x j0).2.2 → Bit)) ($ᵗ (C.Term → Fin (x j0).2.2 → Bit))
      (fun fresh fp => colRound1 K D A (x j0).2.2 (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp) a.1 >>=
        colRest K D A (x j0).2.2 (frandShare D (x j0).2.2 a.2.1 a.2.2 fresh fp))
      (fun _ _ ans freshF => colTail K D Z (fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1),
        (((fun i => if i ∈ D.1 then none else some (x i)) i).map
          fun y => mulRep K (localContext i) y.1 y.2.1 g).getD 0) freshF ans)) (WEq.of_eq prims ?e2))
    case e1 =>
      unfold colRound1 colRest colTail colMsgs1 colMsgs2 colInbox
      simp only [bind_assoc, counted_liftComp_ite, liftComp_bind, counted_bind, liftComp_pure, counted_pure, pure_bind]
    case e2 =>
      simp only [bind_assoc]

end CollectorCoupling

section MultProof
variable [Field E] [Algebra Bit E]

/-- `MulRep` and `Reshare` securely compute `F_mult` in each mode (GS20, Lemma 4). -/
theorem multStatement (prims : Primitives) (K : Constants C E) : MultStatement prims K :=
  multStatement_of_coupling prims K (multCollectorCoupling prims K)

end MultProof
end ThresholdLeanXmssSecurity

