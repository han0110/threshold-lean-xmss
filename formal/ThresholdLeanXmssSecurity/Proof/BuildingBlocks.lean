import ThresholdLeanXmssSecurity.Base.DkgClaims
import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-!
# The building blocks

The values and the simulation of the coin (GS20, Lemma 3), the reshare of `F_mult` with the
translation of a peer (GS20, Lemma 4, in both reshare modes) and the collector of `F_extendMult`
(GS20, Lemma 5).
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
variable {C : Committee} {E : Type}
attribute [local instance] Classical.propDecidable

@[simp] theorem Step.isDone_call {ι : Type} {G : OracleSpec ι} {α : Type} (input : ι) (k) :
    (Step.call (C := C) (E := E) (G := G) (α := α) input k).isDone = False := rfl

theorem bind_congr' {m : Type → Type} [Monad m] {α β : Type} (x : m α) {f g : α → m β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by rw [funext h]

theorem exists_honest (D : C.Coalition) : ∃ i, i ∉ D.1 := by
  by_contra hne
  push Not at hne
  have h1 : (Finset.univ : Finset C.Party) ⊆ D.1 := fun i _ => hne i
  have h2 := Finset.card_le_card h1
  have := D.2; have := C.one_le_t
  simp [Committee.n] at h2; omega

/-- The PRSS output of `F_rand` at an honest operator. -/
def frandShare {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (fresh : C.Term → Fin count → R) (freshPair : C.Pair → Fin count → R)
    (i : C.Party) : PrssOutput C R :=
  (fun T => if i ∈ C.holders T then
      (if KnownTo D.1 T then known T else fun g => if h : g < count then fresh T ⟨g, h⟩ else 0) else fun _ => 0,
    fun j => if h : i = j then fun _ => 0 else if j ∈ D.1 then knownPairs j i
      else fun g => if h' : g < count then freshPair (C.pairOf i j h) ⟨g, h'⟩ else 0)

variable {I O R : Type} [AddCommGroup R] [SampleableType R]

section Field
variable [Field E] [Algebra Bit E]
open Polynomial

theorem charTwo : CharP E 2 := charP_of_injective_algebraMap (algebraMap Bit E).injective 2

/-- The first `t` operators. -/
abbrev firstParties (C : Committee) : Finset C.Party := Finset.univ.filter fun l : C.Party => l.val < C.t

theorem card_firstParties : (firstParties C).card = C.t := by
  have ht : C.t ≤ C.n := by simp only [Committee.n]; have := C.one_le_t; omega
  rw [firstParties, Fin.card_filter_val_lt]; omega

/-- `Conv` of a replicated sharing is a Shamir sharing of degree `t - 1` of the same value (CDI05). -/
theorem conv_poly (K : Constants C E) (y : C.Term → E) :
    ∃ V : Polynomial E, V.natDegree ≤ C.t - 1 ∧ V.eval 0 = ∑ T, y T ∧
      ∀ i, (∑ T ∈ Finset.univ.filter (i ∈ C.holders ·), psi K T i * y T) = V.eval (K.point i) := by
  classical
  have := charTwo (E := E)
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
  split <;> rename_i h
  · erw [if_pos h]; rfl
  · erw [if_neg h]; rfl

end Field

variable (prims : Primitives)

/-- Two computations with the same distribution in the world from every cache. -/
def WEq {α : Type} (oa ob : OracleComp (WorldSpec C) α) : Prop :=
  ∀ s, (simulateQ (world prims) oa).run.run s =ᵈ (simulateQ (world prims) ob).run.run s

theorem world_run_bind {α β : Type} (oa : OracleComp (WorldSpec C) α) (k : α → OracleComp (WorldSpec C) β)
    (s : HashCache C) :
    (simulateQ (world prims) (oa >>= k)).run.run s = (simulateQ (world prims) oa).run.run s >>= fun p =>
      (fun q => ((q.1.1, p.1.2 * q.1.2), q.2)) <$> (simulateQ (world prims) (k p.1.1)).run.run p.2 := by
  rw [simulateQ_bind, WriterT.run_bind, StateT.run_bind]
  refine bind_congr' _ fun p => ?_
  rw [StateT.run_map]

theorem WEq.bind_left {α β : Type} {oa ob : OracleComp (WorldSpec C) α} (h : WEq prims oa ob)
    (k : α → OracleComp (WorldSpec C) β) : WEq prims (oa >>= k) (ob >>= k) := fun s => by
  rw [world_run_bind, world_run_bind]
  exact (h s).bind_left _

theorem WEq.bind_right {α β : Type} (oa : OracleComp (WorldSpec C) α) {k k' : α → OracleComp (WorldSpec C) β}
    (h : ∀ a, WEq prims (k a) (k' a)) : WEq prims (oa >>= k) (oa >>= k') := fun s => by
  rw [world_run_bind, world_run_bind]
  exact EvalDistEq.bind_right _ fun p => (h p.1.1 p.2).map _

theorem world_run_free_bind {α β : Type} (p : ProbComp α) (k : α → OracleComp (WorldSpec C) β) (s : HashCache C) :
    (simulateQ (world prims) (free (liftComp p (LocalSpec C)) >>= k)).run.run s =
      p >>= fun a => (simulateQ (world prims) (k a)).run.run s := by
  rw [world_run_bind, world_free_liftComp]
  simp only [bind_map_left, one_mul]
  refine bind_congr' _ fun a => ?_
  simp

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

end Coin

section CoinOpen
variable [Field E] [Algebra Bit E]

/-- The term values of `F_rand` at position `g`, each fresh term from its table. -/
def freshAt {count : ℕ} (fresh : C.Term → Fin count → E) (g : ℕ) (T : C.Term) : E :=
  if h : g < count then fresh T ⟨g, h⟩ else 0

theorem vector_getD {R : Type} [Zero R] (count : ℕ) (v : ℕ → R) (g : ℕ) (hg : g < count) :
    (vector count v).getD g 0 = v g := by
  simp [vector, hg]

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

end CoinHonest

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
  split_ifs at hj; simp_all

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
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j : C.Party => j ∈ D.1)
  have hD : (Finset.univ.filter fun j : C.Party => j ∈ D.1).card = D.1.card := by
    congr 1; ext j; simp
  have := D.2; have := C.one_le_t
  simp only [Finset.card_univ, Fintype.card_fin, Committee.n] at h
  omega

/-- Two polynomials of degree below `t` that agree at the honest points are equal. -/
theorem poly_eq_of_honest (K : Constants C E) (D : C.Coalition) (P V : Polynomial E)
    (hP : P.degree < C.t) (hV : V.degree < C.t) (h : ∀ j, j ∉ D.1 → P.eval (K.point j) = V.eval (K.point j)) :
    P = V := by
  have : DecidableEq E := Classical.decEq E
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
    (do let v ← $ᵗ (Fin n → E); let fresh' ← $ᵗ (C.Term → Fin n → E); f (adjust D known fresh' v)) =ᵈ
      ($ᵗ (C.Term → Fin n → E) >>= f) := by
  obtain ⟨T0, hT0, -⟩ := lackedTerm_spec D
  simp only [adjust_eq_update D known _ _ T0 hT0]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  have hshift : ∀ fresh' : C.Term → Fin n → E,
      (do let v ← $ᵗ (Fin n → E); f (Function.update fresh' T0 (v - fun g : Fin n => ∑ T' ∈ Finset.univ.erase T0,
        (if KnownTo D.1 T' then known T' g else fresh' T' g)))) =ᵈ
      (do let u ← $ᵗ (Fin n → E); f (Function.update fresh' T0 u)) := fun fresh' => by
    simp only [sub_eq_add_neg]
    have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective (AddGroup.addRight_bijective
      (-fun g : Fin n => ∑ T' ∈ Finset.univ.erase T0, (if KnownTo D.1 T' then known T' g else fresh' T' g)))).bind_left
      fun u : Fin n → E => f (Function.update fresh' T0 u)
    rwa [bind_map_left] at h
  refine (EvalDistEq.bind_right _ hshift).trans ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_)
  let : MeasurableSpace (Fin n → E) := ⊤
  let : MeasurableSpace γ := ⊤
  exact EvalDistEq.of_evalDist_eq (evalDist_bind_bind_update ($ᵗ (Fin n → E)) ($ᵗ (C.Term → Fin n → E))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample T0 f)

end CoinSim

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

end Reshare

section ExtendMult
variable [Field E] [Algebra Bit E] [SampleableType E]

/-- The additive shares of the inner products of operator `i`. -/
def productValues (K : Constants C E) (i : C.Party) (products : List (Product C E)) : ℕ → E :=
  fun g => match products[g]? with | some p => productShare K (localContext i) p | none => 0

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

end PeerSim

section ShiftDist

theorem evalDist_bind_add_uniform {α β : Type} [AddGroup α] [SampleableType α] (m : α) (f : α → ProbComp β) :
    (do let y ← $ᵗ α; f (y + m)) =ᵈ (do let y ← $ᵗ α; f y) := by
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective (AddGroup.addRight_bijective m)).bind_left f
  rwa [bind_map_left] at h

theorem evalDist_bind_congr_all {α β : Type} (mx : ProbComp α) {f g : α → ProbComp β} (h : ∀ a, f a =ᵈ g a) :
    (mx >>= f) =ᵈ (mx >>= g) :=
  EvalDistEq.bind_right mx h

/-- A translation `τ w` of two uniform samples, averaged over a uniform `w`, moves a third sample by `W0`. -/
theorem evalDist_shift {α β γ δ : Type} [AddGroup α] [AddGroup β] [AddGroup γ]
    [SampleableType α] [SampleableType β] [SampleableType γ]
    (F : α → β → ProbComp δ) (G : α → β → γ → ProbComp δ) (τ : γ → α × β) (W0 : α → β → γ)
    (h : ∀ w x y, F (x + (τ w).1) (y + (τ w).2) = G x y (w + W0 x y)) :
    (do let x ← $ᵗ α; let y ← $ᵗ β; F x y) =ᵈ (do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y w) := by
  have h1 : ∀ w, (do let x ← $ᵗ α; let y ← $ᵗ β; F x y) =ᵈ
      (do let x ← $ᵗ α; let y ← $ᵗ β; G x y (w + W0 x y)) := fun w => by
    simp only [← h w]
    exact (evalDist_bind_congr_all _ fun x => (evalDist_bind_add_uniform (τ w).2 (F x)).symm).trans
      (evalDist_bind_add_uniform (τ w).1 (fun x => do let y ← $ᵗ β; F x (y + (τ w).2))).symm
  calc (do let x ← $ᵗ α; let y ← $ᵗ β; F x y : ProbComp δ)
      =ᵈ (do let w ← $ᵗ γ; let x ← $ᵗ α; let y ← $ᵗ β; F x y : ProbComp δ) := (evalDist_uniform_bind_const _).symm
    _ =ᵈ (do let w ← $ᵗ γ; let x ← $ᵗ α; let y ← $ᵗ β; G x y (w + W0 x y) : ProbComp δ) :=
        evalDist_bind_congr_all _ h1
    _ =ᵈ (do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y (w + W0 x y) : ProbComp δ) :=
        (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
          (evalDist_bind_congr_all _ fun x => OracleComp.EvalDistEq.bind_bind_swap _ _ _)
    _ =ᵈ (do let x ← $ᵗ α; let y ← $ᵗ β; let w ← $ᵗ γ; G x y w : ProbComp δ) :=
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

theorem bitCodec_roundTrip : CodecRoundTrip (C := C) (E := E) bitCodec := fun _l _g => ⟨rfl, rfl⟩

theorem elementCodec_roundTrip (K : Constants C E) : CodecRoundTrip (elementCodec K) := fun _l _g => ⟨rfl, rfl⟩

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
  by_cases h1 : i ∉ C.holders T ∨ c ≤ g
  · erw [if_pos h1, if_pos h1]
  erw [if_neg h1, if_neg h1]
  by_cases h2 : T ∈ filledTerms K
  · erw [if_pos h2, if_pos h2]
    push Not at h1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjT := (Finset.mem_filter.mp hj).2
    by_cases hji : j = i
    · subst hji; simp only [if_true, hi, if_false]; exact reshareU_frandShare K D known knownPairs fresh freshPair v j g
    · simp only [hji, if_false]
      by_cases hjD : j ∈ D.1
      · simp [hjD]
      · simp only [hjD, if_false, reshareOut]
        rw [if_pos ⟨Ne.symm hji, hjT ▸ h1.1⟩, (hcodec _ g).1, vector_getD _ _ g h1.2]
        exact reshareU_frandShare K D known knownPairs fresh freshPair v j g
  · erw [if_neg h2, if_neg h2]
    push Not at h1
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
  simp only [hi, if_false, hab, false_or, not_false_eq_true, and_self, not_true_eq_false]
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

end MultPeerProof

section ExtendMultProof
variable [Field E] [Algebra Bit E] [SampleableType E]

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

end ExtendMultProof

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

end Collector

section CollectorValues
variable [Field E] [Algebra Bit E]

theorem getD_map_idxOf {l : List ℕ} {g : ℕ} (hg : g ∈ l) (f : ℕ → Bit) : (l.map f).getD (l.idxOf g) 0 = f g := by
  have h : l.idxOf g < l.length := List.idxOf_lt_length_iff.mpr hg
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h, List.getElem_idxOf]

end CollectorValues

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

end CollectorOutputs

end ThresholdLeanXmssSecurity
