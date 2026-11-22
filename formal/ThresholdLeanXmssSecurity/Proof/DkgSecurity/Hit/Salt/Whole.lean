import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.WholeTree
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Provenance

/-!
# The hidden salts are full at the end of the game in `loggedWorld`

`HiddenWorld impl hid` collects three facts on a world with a hidden table `hid`. Each call grows the
table. A call changes it only at the cell of a free call of `PRG` under a hidden name. Such a call
sets its cell. These facts give `CallKeeps` and `DrawKeeps` of the invariant `Full` on the table
(`callKeeps_of_hiddenWorld`, `drawKeeps_of_hiddenWorld`). `loggedWorld` has them, so
`saltFullLogged` is `SaltFullLogged`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (HonestP)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} (D : C.Coalition)

section General

variable {W : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (hid : W → HiddenCache C)

/-- The three facts on a world with a hidden table. -/
structure HiddenWorld : Prop where
  grows : ∀ t w, ∀ z ∈ support ((impl t).run w), Grows (hid w) (hid z.2)
  only : ∀ t w, ∀ z ∈ support ((impl t).run w), ∀ d, hid z.2 d ≠ hid w d →
    ∃ x, t = .inr (.inr (.inr x)) ∧ Hidden D x.1 ∧ d = ((x.1, x.2.1), x.2.2)
  set : ∀ (x : PrgInput C), Hidden D x.1 → ∀ w, ∀ z ∈ support ((impl (.inr (.inr (.inr x)))).run w),
    hid z.2 ((x.1, x.2.1), x.2.2) ≠ none

variable {impl hid D} (hw : HiddenWorld D impl hid)
include hw

theorem callKeeps_of_hiddenWorld : CallKeeps impl fun w => Full (hid w) := by
  intro t ht st hst z hz T key ρ h0 position hp
  have hg := hw.grows t st z hz
  by_cases hc : hid z.2 ((.term T, key), ρ, 2, 0) = hid st ((.term T, key), ρ, 2, 0)
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hst T key ρ (hc ▸ h0) position hp)
    rw [hg _ v hv]
    simp
  · obtain ⟨x, rfl, -, hd⟩ := hw.only _ st z hz _ hc
    obtain ⟨x₁, x₂, x₃, x₄, x₅⟩ := x
    simp only [Prod.mk.injEq] at hd
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := hd
    exact absurd ⟨⟨T, rfl⟩, rfl, rfl⟩ ht

/-- The reads of a stream at the positions of a list grow the hidden table, change it only at the
cells of the reads under a hidden name, and set each such cell. -/
theorem reads_of_hiddenWorld (name : KeyName C) (key : HashOutput) (ρ idx : ℕ) :
    ∀ (xs : List ℕ) (st : W), ∀ z ∈ support ((simulateQ impl
      (free (liftComp (xs.mapM fun position => readCell (name, key, ρ, idx, position)) (LocalSpec C)))).run st),
      Grows (hid st) (hid z.2) ∧
        (∀ d, hid z.2 d ≠ hid st d → Hidden D name ∧ ∃ p ∈ xs, d = ((name, key), ρ, idx, p)) ∧
        (Hidden D name → ∀ p ∈ xs, hid z.2 ((name, key), ρ, idx, p) ≠ none)
  | [], st, z, hz => by
    simp only [List.mapM_nil, liftComp_pure, ThresholdLeanXmssSecurity.free_pure, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨Grows.refl _, fun d hd => absurd rfl hd, fun _ p hp => absurd hp List.not_mem_nil⟩
  | p :: xs, st, z, hz => by
    rw [List.mapM_cons, free_liftComp_readCell_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨u, hu, hz⟩ := hz
    simp only [liftComp_pure, ThresholdLeanXmssSecurity.free_pure, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    have gy := hw.grows _ st y hy
    obtain ⟨gu, cu, su⟩ := reads_of_hiddenWorld name key ρ idx xs y.2 u hu
    refine ⟨gy.trans gu, fun d hd => ?_, fun hn q hq => ?_⟩
    · by_cases hdy : hid y.2 d = hid st d
      · obtain ⟨hn, q, hq, rfl⟩ := cu d (hdy ▸ hd)
        exact ⟨hn, q, List.mem_cons_of_mem _ hq, rfl⟩
      · obtain ⟨x, hx, hn, rfl⟩ := hw.only _ st y hy d hdy
        cases hx
        exact ⟨hn, p, List.mem_cons_self, rfl⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hw.set (name, key, ρ, idx, q) hn st y hy)
        rw [gu _ v hv]
        simp
      · exact su hn q hq

theorem drawKeeps_of_hiddenWorld : DrawKeeps impl fun w => Full (hid w) := by
  intro T key ρ
  have hp : prgBits (.term T) key ρ 2 256 = ((List.range 256).mapM fun position =>
      readCell (.term T, key, ρ, 2, position)) >>= fun bits => pure fun g => bits.getD g 0 := rfl
  rw [hp, liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
  refine KeepsQ.bind (P := fun _ => True) (fun st hst z hz => ⟨?_, trivial⟩) fun _ _ => ?_
  · obtain ⟨g, ch, se⟩ := reads_of_hiddenWorld hw (.term T) key ρ 2 (List.range 256) st z hz
    intro T' key' ρ' h0 position hpos
    by_cases hc : hid z.2 ((.term T', key'), ρ', 2, 0) = hid st ((.term T', key'), ρ', 2, 0)
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hst T' key' ρ' (hc ▸ h0) position hpos)
      rw [g _ v hv]
      simp
    · obtain ⟨hn, q, -, hd⟩ := ch _ hc
      simp only [Prod.mk.injEq, KeyName.term.injEq] at hd
      obtain ⟨⟨rfl, rfl⟩, rfl, -, -⟩ := hd
      exact se hn position (List.mem_range.2 hpos)
  · rw [liftComp_pure, ThresholdLeanXmssSecurity.free_pure]
    exact keepsQ_pure trivial

end General

variable (prims : Primitives)

/-- A free call of `PRG` under a hidden name sets its cell of the hidden table of `loggedWorld`. -/
theorem loggedWorld_stream_set (x : PrgInput C) (hx : Hidden D x.1) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D (.inr (.inr (.inr x)))).run w), z.2.1.2 ((x.1, x.2.1), x.2.2) ≠ none := by
  intro z hz
  simp only [loggedWorld, streamWorld, ite_eq_left hx, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, ⟨r', hr', rfl⟩, rfl⟩ := hz
  exact (randomOracle_grows _ _ r' hr').2

theorem hiddenWorld_loggedWorld : HiddenWorld D (loggedWorld prims D) fun w : LogState C => w.1.2 :=
  ⟨fun t w z hz => (loggedWorld_grows prims D t w z hz).2, loggedWorld_hiddenOnly prims D,
    loggedWorld_stream_set D prims⟩

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- At the end of the game in `loggedWorld` each place of a term with a cell at the position 0 of the
stream index 2 has all 256 cells. -/
theorem full_loggedWorld (A : DkgTsigAdversary C E) :
    ∀ z ∈ support ((simulateQ (loggedWorld prims D)
      (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])), Full z.2.1.2 :=
  fun z hz => (keeps_dealtRun K circuits settings runLimit D
    (callKeeps_of_hiddenWorld (hiddenWorld_loggedWorld D prims))
    (drawKeeps_of_hiddenWorld (hiddenWorld_loggedWorld D prims)) (treeWhole K circuits settings)
    ⟨true, fun _ => 0⟩ (fun _ => rfl) A _ full_empty z hz).1

omit [Fintype E] [DecidableEq E] in
/-- At the end of the game in `loggedWorld` each salt of a hidden term is the salt of a place with all
256 cells. -/
theorem saltFullLogged : SaltFullLogged prims K circuits settings runLimit :=
  fun D A z hz => hiddenSalts_subset_full D (full_loggedWorld D prims K circuits settings runLimit A z hz)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.saltFullLogged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.saltFullLogged
