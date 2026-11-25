import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Game

/-!
# The hidden salts of the game with the keys of the dealer

`SaltPoint d` says that the cell `d` of the hidden table is the position 0 of a stream at the index 2
under the name of a term. `places w` is the set of such cells with a value in the world `w`. A call of
`loggedWorld` adds a cell to the hidden table only on a free call of `PRG` under a hidden name, and
then only the cell of the call (`loggedWorld_hidden`).

`sharedDealt_erase` states that `sharedDealt` with the flag erased is `dealtRun` in `loggedWorld`,
with the same world and log.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (HonestP)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-- A cell of the hidden table at the position 0 of a stream at the index 2 under the name of a term. -/
def SaltPoint (d : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) : Prop :=
  (∃ T : C.Term, d.1.1 = .term T) ∧ d.2.2.1 = 2 ∧ d.2.2.2 = 0

/-- The cells of `SaltPoint` with a value in the hidden table. -/
def places (hidden : HiddenCache C) : Set ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) :=
  {d | SaltPoint d ∧ hidden d ≠ none}

/-- A call of a lazy random oracle changes its cache only at the cell of the call. -/
theorem randomOracle_other {α β : Type} [DecidableEq α] [SampleableType β] (q : α)
    (s : (α →ₒ β).QueryCache) (p : β × (α →ₒ β).QueryCache)
    (hp : p ∈ support (((α →ₒ β).randomOracle q).run s)) : ∀ d, d ≠ q → p.2 d = s d := by
  intro d hd
  rcases hs : s q with _ | u
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs] at hp
    erw [support_map, Set.mem_image] at hp
    obtain ⟨u, _, rfl⟩ := hp
    exact QueryCache.cacheQuery_of_ne _ _ hd
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs] at hp
    simp at hp
    subst hp
    rfl

variable (prims : Primitives) (D : C.Coalition)

/-- A call of `loggedWorld` changes the hidden table only at the cell of a free call of `PRG` under a
hidden name. -/
theorem loggedWorld_hidden (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w), ∀ d, z.2.1.2 d ≠ w.1.2 d →
      ∃ x, t = .inr (.inr (.inr x)) ∧ d = ((x.1, x.2.1), x.2.2) := by
  intro z hz d hd
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with t | t
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', -, rfl⟩ := hr
    exact absurd rfl hd
  · rcases t with n | q | x
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', -, rfl⟩ := hr
      exact absurd rfl hd
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', -, rfl⟩ := hr
      exact absurd rfl hd
    · refine ⟨x, rfl, ?_⟩
      by_contra hne
      simp only [streamWorld] at hr
      split_ifs at hr
      · simp only [StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        exact hd (randomOracle_other _ _ _ hr' d hne)
      · simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨r', -, rfl⟩ := hr
        exact hd rfl

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- `sharedDealt` with the flag erased is `dealtRun` in `loggedWorld`, with the same world and log. -/
theorem sharedDealt_erase (m : Mode) (A : DkgTsigAdversary C E) :
    (fun r : DealtOut C => (r.1.1, r.2)) <$> sharedDealt prims K circuits settings runLimit m D A =
      simulateQ (loggedWorld prims D) (dealtRun K circuits settings runLimit m D A) := by
  unfold sharedDealt dealtRun sharedRest secRest
  simp only [map_bind, simulateQ_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨state, parameter, seeds, dealt, emu⟩
  simp only [inWorld, StateT.run'_eq, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, pure_bind,
    bind_assoc, simulateQ_bind, simulateQ_map, map_bind]
  refine bind_congr fun v => ?_
  have h := ((flagErases_sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst D m A.net
    parameter seeds dealt (committed v.2 emu) .top runLimit).bind
    fun _ => flagErases_dealerSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D m A
      parameter seeds dealt (committed v.2 emu)).fst
    (votedStart D (startState D state fun i => (emu i).map fun _ => dealt i) v.1 v.2)
  have h' := congrArg (fun z => z >>= fun win =>
    (pure (win, parameter, seeds, dealt, emu) : StateT (LogState C) ProbComp _)) h
  simp only [StateT.run_bind, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind,
    simulateQ_pure] at h' ⊢
  exact h'

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedDealt_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedDealt_erase
