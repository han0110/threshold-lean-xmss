import ThresholdLeanXmssSecurity.Proof.Execution
import VCVio.ProgramLogic.Relational.Basic

/-!
# Couplings and query bounds

This module holds small lemmas on couplings and on counted calls.

* `relTriple_of_support_left` gives a coupling from a postcondition that holds on every left output.
  The signing proof uses it.
* `relTriple_support_left` adds a property of the left support to a coupling.
  `relTriple_of_support` gives a coupling from a relation that holds on all
  pairs of the two supports. The round lemmas of the signing compiler use it.
* `fuse` makes one handler on both states from a handler into a state and an outer handler.
  `evalDist_truncateHash_uniform` states that a truncated uniform hash output is a uniform digest.
  `evalDist_simulateQ_state_projection` projects the state of a simulation in distribution. `Tree`
  and the signing proof use them.
* `probEvent_uniform_coord_eq` bounds the probability that one coordinate of uniform secret points
  equals a fixed point. `SeedGenAlias` uses it.
* `WorldCounted`, `isQueryBoundP_adversary`, `isQueryBoundP_free` and `isQueryBoundP_sequenceFin`
  count the calls of a world computation. `PrssRand/KeyHop` uses them.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-! ## Couplings up to bad -/

section UpToBad

variable {α β : Type}

/-- A postcondition that holds for every left output and every right value holds on a coupling. -/
theorem relTriple_of_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    (h : ∀ a ∈ support oa, ∀ b, R a b) : RelTriple oa ob R :=
  relTriple_post_mono (relTriple_prod (P := fun a => ∀ b, R a b) (Q := fun _ => True) h fun _ _ => trivial)
    fun _ b hab => hab.1 b

end UpToBad

section Support

variable {α β : Type}

theorem relTriple_support_left {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    {P : α → Prop} (h : RelTriple oa ob R) (hp : ∀ a ∈ support oa, P a) :
    RelTriple oa ob (fun a b => R a b ∧ P a) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, ?_⟩
  filter_upwards [hc, ae_mem_support_prod c] with z hz hmem
  exact ⟨hz, hp z.1 hmem.1⟩

theorem relTriple_of_support {oa : ProbComp α} {ob : ProbComp β} {R : α → β → Prop}
    (h : ∀ a ∈ support oa, ∀ b ∈ support ob, R a b) : RelTriple oa ob R := by
  have left := relTriple_support_left (relTriple_true oa ob) (P := fun a => a ∈ support oa)
    (fun a ha => ha)
  have right := relTriple_symm (relTriple_support_left (relTriple_symm left)
    (P := fun b => b ∈ support ob) (fun b hb => hb))
  exact relTriple_post_mono right fun a b hab => h a hab.1.2 b hab.2

end Support

/-! ## Handlers and uniform samples -/

section Fuse
variable {ι κ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec κ} {σ τ : Type}

/-- One handler into a state over the oracles of an outer handler, as one handler on both states. -/
def fuse (inner : QueryImpl spec (StateT σ (OracleComp spec₂))) (outer : QueryImpl spec₂ (StateT τ ProbComp)) :
    QueryImpl spec (StateT (σ × τ) ProbComp) := fun q => StateT.mk fun st =>
  (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ outer ((inner q).run st.1)).run st.2

end Fuse

section Uniform

def splitHalves (output : HashOutput) : Digest × Digest :=
  (truncateHash output, output.extractLsb' digestBits digestBits)

theorem splitHalves_bijective : Function.Bijective splitHalves := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun x y heq => ?_, by simp [Fintype.card_prod, digestBits]⟩
  have hlow := congrArg Prod.fst heq
  have hhigh := congrArg Prod.snd heq
  simp only [splitHalves, truncateHash] at hlow hhigh
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < digestBits
  · have := congrArg (fun b : Digest => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - digestBits < digestBits := by simp [digestBits] at hi ⊢; omega
    have := congrArg (fun b : Digest => b.getLsbD (i - digestBits)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show digestBits + (i - digestBits) = i by omega] at this

theorem evalDist_truncateHash_uniform :
    (truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ Digest : ProbComp Digest) := by
  have hmap : truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> (splitHalves <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, splitHalves]
  rw [hmap]
  refine ((SampleableType.map_uniformSample_evalDistEq_of_bijective splitHalves_bijective).map Prod.fst).trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [map_bind, map_pure]
  exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans (by rw [bind_pure])

/-- Distributional state projection, including samplers with different representations. -/
theorem evalDist_simulateQ_state_projection {ι σ τ α : Type} {spec : OracleSpec ι}
    (I : QueryImpl spec (StateT σ ProbComp)) (J : QueryImpl spec (StateT τ ProbComp))
    (π : σ → τ)
    (hstep : ∀ q s, (Prod.map id π <$> (I q).run s) =ᵈ (J q).run (π s))
    (game : OracleComp spec α) (s : σ) :
    (Prod.map id π <$> (simulateQ I game).run s) =ᵈ (simulateQ J game).run (π s) := by
  induction game using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind]
    refine (EvalDistEq.bind_right ((I q).run s) fun p => ih p.1 p.2).trans ?_
    have he : ((I q).run s >>= fun p => (simulateQ J (k p.1)).run (π p.2)) =
        (Prod.map id π <$> (I q).run s) >>= fun p => (simulateQ J (k p.1)).run p.2 := by
      simp only [bind_map_left, Prod.map, id_eq]
    rw [he]
    exact (hstep q s).bind_left _

end Uniform

/-! ## Hitting a hidden secret -/

section Hit

open ENNReal

variable {κ σ S β : Type} {spec : OracleSpec κ}

variable {P : Type} [Fintype P] [DecidableEq P] [SampleableType P]

/-- One coordinate of `k` uniform secret points equals a fixed point with probability `1 / |P|`. -/
theorem probEvent_uniform_coord_eq {k : ℕ} (j : Fin k) (x : P) :
    Pr{let s ← $ᵗ (Fin k → P)}[s j = x] = (Fintype.card P : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
  have hfil : (Finset.univ.filter fun s : Fin k → P => s j = x).card = Fintype.card P ^ (k - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset P) j (Finset.mem_univ x)
    simpa using this
  have hk : k = (k - 1) + 1 := by have := j.2; omega
  have hP : (Fintype.card P : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨x⟩
    exact_mod_cast this.ne'
  rw [hfil, Fintype.card_fun, Fintype.card_fin, hk, pow_succ, Nat.cast_mul, Nat.add_sub_cancel]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP))))
    (Or.inl (by simp))]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP)))
    (ENNReal.natCast_ne_top _), one_mul]

end Hit

/-! ## Acceptance in the world -/

section World

variable (prims : Primitives) {C : Committee}

/-- The calls of a world computation that the budget counts, namely the counted calls of the counted
copy and its programming queries. -/
def WorldCounted : (WorldSpec C).Domain → Prop
  | .inl (.inl u) => Counted u
  | .inl (.inr _) => True
  | .inr _ => False

/-- The adversary role keeps the counted calls of a computation. -/
theorem isQueryBoundP_adversary {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) : IsQueryBoundP (worldRoles.adversary oa) WorldCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- The honest role makes no counted call. -/
theorem isQueryBoundP_free {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ) :
    IsQueryBoundP (free oa) WorldCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e]
    exact ⟨Or.inl not_false, fun u => ih u _⟩

/-- A sequence of computations without counted calls makes no counted call. -/
theorem isQueryBoundP_sequenceFin {κ β : Type} {spec : OracleSpec κ} {p : κ → Prop} [DecidablePred p] :
    ∀ {N : ℕ} (f : Fin N → OracleComp spec β), (∀ i, IsQueryBoundP (f i) p 0) →
      IsQueryBoundP (OverPermutation.sequenceFin f) p 0
  | 0, f, _ => by simp [OverPermutation.sequenceFin]
  | N + 1, f, h => by
    simp only [OverPermutation.sequenceFin]
    exact isQueryBoundP_bind (h 0) fun _ _ => isQueryBoundP_bind
      (m := 0) (isQueryBoundP_sequenceFin (fun i : Fin N => f i.succ) fun i => h i.succ) fun _ _ => isQueryBoundP_pure _ _ 0

variable {E Ia I O L R α : Type} {C : Committee}

end World

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.relTriple_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.relTriple_of_support
