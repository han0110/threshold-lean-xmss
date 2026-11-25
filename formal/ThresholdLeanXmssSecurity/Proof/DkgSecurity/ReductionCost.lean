import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Programs

/-!
# The cost bound of the forger of the setup

`dkgReduction_cost` is the first conjunct of `DkgSecurityPreservation`. The forger `dkgReduction` costs at most
the budget `q` of the adversary plus `dkgOverhead runLimit C`.

* The seed generation costs the start and `setupRounds` rounds of the adversary
  (`seedGenEmulation_cost`).
* A vote costs one round of the adversary, because the emulated operators hash their votes in the
  own table (`voteRound_cost`).
* A run of a tree costs `treeFuel` rounds of the adversary, its vote and the forwarded calls of the
  honest operators (`emulatedRun_cost`). `runsPotential` pays for the runs that each tree may still
  make. A run is allowed only below `runLimit` runs, so each run spends its part of the potential.
* The oracles of `forge` cost at most `forgeCost` and the drop of the potential (`forgeOracles_cost`).
* `dkgReduction_cost_of_programCost` gives the bound from `ProgramCost`, the bound of the programs of
  the emulated operators, and `programCost` proves `ProgramCost`.
-/

set_option autoImplicit false

open OracleComp OracleSpec ThresholdLeanXmss HashSig LeanXmss
open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

section Forger

variable {E : Type} [Field E] [Algebra Bit E]

/-! ## The calls of one emulated operator -/

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (aes : Aes)
  (D : C.Coalition)

/-- The seed generation of an emulated operator forwards no call, and its program in a run of
`tree` forwards at most `operatorCalls C tree` calls. -/
def ProgramCost : Prop :=
  (∀ (i : C.Party) (parts : Parts C), cost (partyCharge (E := E)) (seedGenWith (G := RealSpec) i parts).run ≤ 0) ∧
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (openings : List (List (List Bit)))
      (randomizer : Randomizer) (i : C.Party) (operator : OperatorState C) (tree : Tree),
      cost partyCharge (emulatedProgram K circuits settings
        (shiftedBuildingBlocks K circuits settings D parameter seeds openings) randomizer i operator tree).run ≤
        operatorCalls C tree

/-! ## The potential of the runs -/

/-- The cost of one run of `tree` and its vote with `step` calls of the adversary in each round. -/
def perRun (step : ℕ) (tree : Tree) : ℕ := (treeFuel circuits settings + 1) * step + C.n * operatorCalls C tree

/-- The cost of the runs that each tree may still make after `runs` runs. -/
def runsPotential (step : ℕ) (runs : Tree → ℕ) : ℕ :=
  (runLimit - runs .top) * perRun (C := C) circuits settings step .top +
    ∑ b : Fin (2 ^ layerHeight), (runLimit - runs (.bottom b)) * perRun (C := C) circuits settings step (.bottom b)

theorem perRun_add_runsPotential (step : ℕ) (runs : Tree → ℕ) (tree : Tree) (h : runs tree < runLimit) :
    perRun (C := C) circuits settings step tree +
      runsPotential (C := C) circuits settings runLimit step (Function.update runs tree (runs tree + 1)) =
      runsPotential (C := C) circuits settings runLimit step runs := by
  have key : ∀ r P : ℕ, r < runLimit → P + (runLimit - (r + 1)) * P = (runLimit - r) * P := fun r P hr => by
    rw [show runLimit - r = runLimit - (r + 1) + 1 by omega, add_mul, one_mul, add_comm]
  unfold runsPotential
  cases tree with
  | top =>
    have hb : ∀ b : Fin (2 ^ layerHeight), Function.update runs Tree.top (runs .top + 1) (.bottom b) = runs (.bottom b) :=
      fun b => Function.update_of_ne (by simp) _ _
    simp only [Function.update_self, hb]
    rw [← add_assoc, key _ _ h]
  | bottom b0 =>
    have ht : Function.update runs (Tree.bottom b0) (runs (.bottom b0) + 1) .top = runs .top :=
      Function.update_of_ne (by simp) _ _
    rw [ht, ← Finset.add_sum_erase _ _ (Finset.mem_univ b0), ← Finset.add_sum_erase _ _ (Finset.mem_univ b0),
      Function.update_self]
    have hs : ∀ b ∈ Finset.univ.erase b0,
        (runLimit - Function.update runs (Tree.bottom b0) (runs (.bottom b0) + 1) (.bottom b)) *
          perRun (C := C) circuits settings step (.bottom b) =
        (runLimit - runs (.bottom b)) * perRun (C := C) circuits settings step (.bottom b) := fun b hb => by
      rw [Function.update_of_ne (by simpa using Finset.ne_of_mem_erase hb)]
    rw [Finset.sum_congr rfl hs, ← key _ _ h]
    ring

/-! ## Pointwise steps -/

theorem RedCost.get_bind {σ α : Type} {f : RealState C σ → RedM C σ α} {k : α → RealState C σ → ℕ∞}
    {Φ : RealState C σ → ℕ∞} (h : ∀ s, TableCost ((f s).run s) (fun p => k p.1 p.2) (Φ s)) :
    RedCost (MonadState.get >>= f) k Φ := fun s => by
  rw [StateT.run_bind]
  exact h s

theorem RedCost.modify {σ : Type} (f : RealState C σ → RealState C σ) (k : PUnit → RealState C σ → ℕ∞) :
    RedCost (modify f : RedM C σ PUnit) k (fun s => k () (f s)) :=
  fun s => TableCost.pure (PUnit.unit, f s) _

theorem TableCost.map {α β : Type} {m : TableM C α} (f : α → β) {k : β → ℕ∞} {B : ℕ∞}
    (h : TableCost m (fun a => k (f a)) B) : TableCost (f <$> m) k B := by
  rw [map_eq_bind_pure_comp]
  exact TableCost.bind h fun a => TableCost.pure _ _

theorem TableCost.forIn {β γ : Type} (R : ℕ∞) (f : γ → β → TableM C (ForInStep β))
    (hf : ∀ x b, TableCost (f x b) (fun _ => R) R) : ∀ (xs : List γ) (b : β), TableCost (forIn xs b f) (fun _ => R) R
  | [], b => TableCost.pure _ _
  | x :: xs, b => by
    rw [List.forIn_cons]
    refine TableCost.bind (hf x b) fun step => ?_
    cases step with
    | done b' => exact TableCost.pure _ _
    | yield b' => exact TableCost.forIn R f hf xs b'

/-- A forwarded call costs its `adversaryCost`. -/
theorem RedCost.forward {σ : Type} (t : (LocalSpec C + TsigSpec C).Domain) (Ψ : RealState C σ → ℕ∞) :
    RedCost (StateT.lift (forward t) : RedM C σ _) (fun _ s => Ψ s) (fun s => (adversaryCost t : ℕ∞) + Ψ s) :=
  RedCost.lift fun s => ((tableCost_forward t).frame (Ψ s)).mono (fun _ => le_of_eq (zero_add _).symm) le_rfl

/-! ## The runs of the trees -/

section Runs

variable {K circuits settings runLimit aes D}
variable (hprog : ProgramCost K circuits settings D) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
  (hround : ∀ state sent, cost (fun t => (ownCost t : ℕ∞)) (net.round state sent) ≤ step)

/-- The input of each vote of a tree is in a setup domain. -/
theorem isSetupQuery_treeVote (tree : Tree) (output : TreeOutput) : isSetupQuery (treeVote tree output : Query C) = true := by
  cases tree <;> cases output <;> rfl

omit [Field E] [Algebra Bit E] in
include hround in
/-- A vote costs one round of the adversary. Each emulated operator hashes its vote in the own table. -/
theorem voteRound_cost (state : net.State) (input : C.Party → Option (Query C))
    (hinput : ∀ j q, input j = some q → isSetupQuery q = true) (R : ℕ∞) :
    TableCost (voteRound (reductionRoles aes D) D net state input) (fun _ => R) (step + R) := by
  unfold voteRound
  refine TableCost.bind (K := fun _ => step + R) (((TableCost.sequenceFin (fun _ => 0) _ (fun _ => 0) fun j => ?_).frame
    (step + R)).mono (fun _ => le_of_eq (by rw [Finset.sum_const_zero, zero_add]))
      (le_of_eq (by rw [Finset.sum_const_zero, zero_add]))) fun honest => ?_
  · split
    · rename_i q hq
      split_ifs
      · exact TableCost.pure _ _
      · exact (tableCost_honest aes D _ _).mono (fun _ => le_rfl)
          (cost_map_le _ ((cost_liftComp_ro _).trans (roFree_hashQuery q (hinput j q hq))))
    · exact TableCost.pure _ _
  refine TableCost.bind (K := fun _ => R) ((tableCost_adversary aes D _ _).mono (fun _ => le_rfl)
    ((costWith_le_cost_add _ _).trans (add_le_add (hround _ _) iSup_const_le))) fun r => ?_
  obtain ⟨state', sent⟩ := r
  exact TableCost.pure _ _

include hprog hround in
/-- One emulated run of `tree` and its vote cost `perRun`. -/
theorem emulatedRun_cost (openings : List (List (List Bit))) (randomizer : Randomizer) (tree : Tree) :
    RedCost (emulatedRun K circuits settings aes D net openings randomizer tree)
      (fun _ s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞))
      (fun s => (perRun (C := C) circuits settings step tree +
        runsPotential (C := C) circuits settings runLimit step (Function.update s.runs tree (s.runs tree + 1)) : ℕ)) := by
  unfold emulatedRun
  refine RedCost.get_bind fun s => ?_
  dsimp only
  rw [StateT.run_bind]
  refine TableCost.bind (K := fun _ => step + (runsPotential (C := C) circuits settings runLimit step
      (Function.update s.runs tree (s.runs tree + 1)) : ℕ∞)) ((RedCost.lift (k := fun _ _ => step + (runsPotential (C := C)
        circuits settings runLimit step (Function.update s.runs tree (s.runs tree + 1)) : ℕ∞))
        (Φ := fun _ => ((perRun (C := C) circuits settings step tree + runsPotential (C := C) circuits settings
          runLimit step (Function.update s.runs tree (s.runs tree + 1)) : ℕ) : ℕ∞)) fun _ => ?_) s) fun p => ?_
  rotate_left
  · obtain ⟨state, outputs⟩ := p
    dsimp only
    rw [StateT.run_bind]
    refine TableCost.bind ((RedCost.lift (k := fun _ _ => (runsPotential (C := C) circuits settings runLimit step
      (Function.update s.runs tree (s.runs tree + 1)) : ℕ∞)) fun _ => voteRound_cost net step hround _ _
        (fun j q h => ?_) _) _) fun r => ?_
    · obtain ⟨output, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact isSetupQuery_treeVote _ _
    obtain ⟨state', ok⟩ := r
    exact TableCost.pure _ _
  refine ((executePhase_cost (tableCost_adversary aes D) (tableCost_honest aes D) D net step hround
    (treeFuel circuits settings) s.adversary _ (fun _ => (operatorCalls C tree : ℕ∞))
    fun j _ => hprog.2 _ _ _ _ _ _ _).frame _).mono (fun _ => le_of_eq (zero_add _).symm) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, perRun]
  push_cast
  ring

include hprog hround in
/-- The emulated runs of a tree spend the potential of their runs. -/
theorem emulatedRuns_cost (openings : List (List (List Bit))) (randomizer : Randomizer) (tree : Tree) :
    ∀ count, RedCost (emulatedRuns K circuits settings runLimit aes D net openings randomizer tree count)
      (fun _ s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞))
      (fun s => runsPotential (C := C) circuits settings runLimit step s.runs)
  | 0 => RedCost.pure _ _
  | count + 1 => by
    unfold emulatedRuns
    refine RedCost.get_bind fun s => ?_
    split_ifs with h
    · have hlt : s.runs tree < runLimit := by
        cases tree with
        | top => exact h.1
        | bottom b => exact h.2.1
      refine ((RedCost.bind (emulatedRun_cost hprog net step hround openings randomizer tree)
        fun _ => emulatedRuns_cost openings randomizer tree count) s).mono (fun _ => le_rfl) (le_of_eq ?_)
      exact_mod_cast perRun_add_runsPotential circuits settings runLimit step s.runs tree hlt
    · exact TableCost.pure _ _

include hprog hround in
/-- A call of `forge` costs at most `forgeCost` and the drop of the potential of the runs. -/
theorem forgeOracles_cost (t : (LocalSpec C + (TsigSpec C + StateSpec net.State)).Domain) :
    RedCost (forgeOracles K circuits settings runLimit aes D net t)
      (fun _ s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞))
      (fun s => (forgeCost t : ℕ∞) + runsPotential (C := C) circuits settings runLimit step s.runs) := by
  rcases t with t | (q | q)
  · refine RedCost.lift fun s => ((tableCost_adversaryCall aes t).frame _).mono
      (fun _ => le_of_eq (zero_add _).symm) (add_le_add (le_of_eq ?_) le_rfl)
    rcases t with _ | _ | _ <;> rfl
  · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · exact (RedCost.pure _ _).mono (fun _ _ => le_rfl) fun _ => le_add_self
    · unfold forgeOracles emulatedTreeRequest
      dsimp only
      refine RedCost.bind (K := fun _ s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞))
        (RedCost.forward _ _) fun dealt => ?_
      rcases dealt with _ | ⟨tree, ρ⟩
      · refine RedCost.get_bind fun s => ?_
        split <;> exact TableCost.pure _ _
      · refine RedCost.bind (emulatedRuns_cost hprog net step hround _ _ _ 1) fun _ => RedCost.get_bind fun s => ?_
        split <;> exact TableCost.pure _ _
    · unfold forgeOracles emulatedSignRequest
      dsimp only
      refine RedCost.bind (K := fun _ s => (forgeCost (C := C) (σ := net.State) (.inr (.inl _)) : ℕ∞) +
        runsPotential (C := C) circuits settings runLimit step s.runs) (RedCost.modify _ _) fun _ =>
          RedCost.get_bind fun s => ?_
      split
      · exact ((RedCost.forward (σ := net.State) (.inr (.round1 i J e message)) fun s =>
          (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞)) s).mono (fun _ => le_rfl) (le_of_eq rfl)
      · exact (TableCost.pure _ _).mono (fun _ => le_rfl) le_add_self
    · unfold forgeOracles emulatedSignRequest
      dsimp only
      refine RedCost.bind (K := fun _ s => (forgeCost (C := C) (σ := net.State) (.inr (.inl _)) : ℕ∞) +
        runsPotential (C := C) circuits settings runLimit step s.runs) (RedCost.modify _ _) fun _ =>
          RedCost.get_bind fun s => ?_
      split
      · exact ((RedCost.forward (σ := net.State) (.inr (.round2 i J e message parts)) fun s =>
          (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞)) s).mono (fun _ => le_rfl) (le_of_eq rfl)
      · exact (TableCost.pure _ _).mono (fun _ => le_rfl) le_add_self
  · rcases q with _ | state
    · intro s
      exact (TableCost.pure _ _).mono (fun _ => le_rfl) le_add_self
    · exact (RedCost.modify _ _).mono (fun _ _ => le_rfl) fun _ => le_add_self

end Runs

/-! ## The seed generation -/

theorem tableCost_of_cost {ι β : Type} {spec : OracleSpec.{0, 0} ι} {m : TableM C β} {c : ι → ℕ∞} {oa : OracleComp spec β} {b X : ℕ∞}
    (h : ∀ k, TableCost m k (costWith c oa k)) (hb : cost c oa ≤ b) : TableCost m (fun _ => X) (b + X) :=
  (h _).mono (fun _ => le_rfl) ((costWith_le_cost_add _ _).trans (add_le_add hb iSup_const_le))

variable (net : Adversary C E Unit PEmpty PEmpty) (start step : ℕ)
  (hstart : ∀ x z, cost (fun t => (ownCost t : ℕ∞)) (net.start x z) ≤ start)
  (hround : ∀ state sent, cost (fun t => (ownCost t : ℕ∞)) (net.round state sent) ≤ step)

omit [Field E] [Algebra Bit E] in
include hstart hround in
/-- The seed generation costs the start and `setupRounds` rounds of the adversary. -/
theorem seedGenEmulation_cost (hseed : ∀ (i : C.Party) (parts : Parts C),
      cost (partyCharge (E := E)) (seedGenWith (G := RealSpec) i parts).run ≤ 0)
    (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) (R : ℕ∞) :
    TableCost (seedGenEmulation aes D parameter corrupt net) (fun _ => R) (start + setupRounds * step + R) := by
  unfold seedGenEmulation
  dsimp only
  refine TableCost.bind (K := fun _ => (setupRounds * step : ℕ∞) + R)
    ((tableCost_of_cost (tableCost_adversary aes D _) (hstart _ _)).mono (fun _ => le_rfl) (le_of_eq (add_assoc _ _ _).symm))
    fun state => ?_
  refine TableCost.bind (K := fun _ => (setupRounds * step : ℕ∞) + R)
    ((tableCost_of_cost (tableCost_honest aes D _) (cost_liftComp_local _)).mono (fun _ => le_rfl) (le_of_eq (zero_add _)))
    fun parts => ?_
  refine TableCost.bind (K := fun st => ∑ j, rest (st j) + ((setupRounds * step : ℕ∞) + R))
    (((startSteps_cost (tableCost_honest aes D) D _).frame _).mono (fun _ => le_rfl) ?_) fun steps => ?_
  · refine (add_le_add (Finset.sum_le_sum (g := fun _ => (0 : ℕ∞)) fun j _ => ?_) le_rfl).trans
      (le_of_eq (by rw [Finset.sum_const_zero, zero_add]))
    split_ifs
    · exact le_rfl
    · exact hseed _ _
  refine TableCost.bind (K := fun r => ∑ j, rest (r.2.1 j) + (((setupRounds - 1 : ℕ) * step : ℕ∞) + R))
    (((stepRound_cost (tableCost_adversary aes D) (tableCost_honest aes D) D net step hround _ _).frame _).mono
      (fun _ => le_rfl) (le_of_eq ?_)) fun r => ?_
  · simp only [setupRounds]
    push_cast
    ring
  obtain ⟨state', steps', sent⟩ := r
  dsimp only
  have hw : ∀ (q : Query C) (value : HashOutput) (X : ℕ∞), TableCost (writeTable q value) (fun _ => X) X :=
    fun _ _ _ _ => le_rfl
  refine TableCost.bind (TableCost.get _ _ fun _ => le_rfl) fun log => ?_
  refine TableCost.bind ((tableCost_of_cost (tableCost_honest aes D _) (cost_liftComp_local _)).mono
    (fun _ => le_rfl) (le_of_eq (zero_add _))) fun high => ?_
  refine TableCost.bind (hw _ _ _) fun _ => ?_
  refine TableCost.bind (TableCost.forIn _ _ (fun T _ => ?_) _ _) fun _ => ?_
  · split
    · exact TableCost.bind (hw _ _ _) fun _ => TableCost.pure _ _
    · exact TableCost.pure _ _
  refine TableCost.bind (TableCost.forIn _ _ (fun j _ => ?_) _ _) fun _ => ?_
  · refine TableCost.bind (TableCost.forIn _ _ (fun i _ => ?_) _ _) fun _ => TableCost.pure _ _
    split
    · exact TableCost.bind (hw _ _ _) fun _ => TableCost.pure _ _
    · exact TableCost.pure _ _
  refine ((executeRounds_cost (tableCost_adversary aes D) (tableCost_honest aes D) D net step hround _ _ _).frame R).mono
    (fun _ => le_of_eq (zero_add _).symm) (le_of_eq ?_)
  ring

/-! ## The cost of the forger -/

theorem TableCost.cost_le {α : Type} {m : TableM C α} {B : ℕ∞} (h : TableCost m (fun _ => 0) B) (ts : TableState C) :
    cost (fun t => (adversaryCost t : ℕ∞)) (m.run ts) ≤ B :=
  h ts

/-- The budget of the adversary and the potential at the start pay the forger. -/
theorem runsPotential_zero_le (step start forge q : ℕ)
    (hq : start + dkgTsigRounds circuits settings runLimit * step + forge ≤ q) :
    start + (setupRounds + 1) * step + (runsPotential (C := C) circuits settings runLimit step (fun _ => 0) + forge) ≤
      q + dkgOverhead runLimit C := by
  have hsum : ∑ b : Fin (2 ^ layerHeight), treeReductionCalls C (.bottom b) =
      ∑ b : Fin (2 ^ layerHeight), C.n * operatorCalls C (.bottom b) :=
    Finset.sum_congr rfl fun b _ => treeReductionCalls_eq _
  unfold runsPotential perRun dkgOverhead dkgTsigRounds at *
  rw [hsum, treeReductionCalls_eq] at *
  simp only [Nat.sub_zero, mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at *
  nlinarith

variable (hprog : ProgramCost K circuits settings D)

include hprog in
/-- The cost bound of the forger from the bound of the programs of the emulated operators. -/
theorem dkgReduction_cost_of_programCost (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) (pk : PublicKey) (top : TopTree) :
    QueryCostAtMost (dkgReduction K circuits settings runLimit aes D A pk top) adversaryCost
      (q + dkgOverhead runLimit C) := by
  obtain ⟨start, step, forge, hq, hstart, hround, hforge⟩ := bounded
  have hstart' := fun x z => (queryCostAtMost_iff_cost_le _ _ _).1 (hstart x z)
  have hround' := fun state sent => (queryCostAtMost_iff_cost_le _ _ _).1 (hround state sent)
  have hforge' := (queryCostAtMost_iff_cost_le _ _ _).1 (hforge pk top)
  rw [queryCostAtMost_iff_cost_le]
  unfold dkgReduction StateT.run'
  refine cost_map_le _ ((TableCost.cost_le (B := ((start + (setupRounds + 1) * step : ℕ) : ℕ∞) +
    ((runsPotential (C := C) circuits settings runLimit step (fun _ => 0) : ℕ∞) + forge)) ?_ _).trans ?_)
  rotate_left
  · exact_mod_cast runsPotential_zero_le circuits settings runLimit step start forge q hq
  refine TableCost.bind (K := fun _ => ((start + (setupRounds + 1) * step : ℕ) : ℕ∞) +
      ((runsPotential (C := C) circuits settings runLimit step (fun _ => 0) : ℕ∞) + forge))
    (((TableCost.sequenceFin (fun _ => 0) _ (fun _ => 0) fun i => ?_).frame _).mono
      (fun _ => le_of_eq (by rw [Finset.sum_const_zero, zero_add]))
      (le_of_eq (by rw [Finset.sum_const_zero, zero_add]))) fun corrupt => ?_
  · by_cases h : i ∈ D.1
    · simp only [h, ↓reduceIte]
      exact (tableCost_forward _).mono (fun _ => le_rfl) (le_of_eq (by simp [adversaryCost]))
    · simp only [h, ↓reduceIte]
      exact TableCost.pure _ _
  refine TableCost.bind (K := fun _ => (step : ℕ∞) + ((runsPotential (C := C) circuits settings runLimit step (fun _ => 0) : ℕ∞) + forge))
    ((seedGenEmulation_cost aes D A.net start step hstart' hround' hprog.1 _ _ _).mono (fun _ => le_rfl)
      (le_of_eq (by push_cast; ring))) fun p => ?_
  obtain ⟨state, keys⟩ := p
  refine TableCost.bind (voteRound_cost A.net step hround' _ _ (fun j q h => ?_) _) fun r => ?_
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  obtain ⟨state', ok⟩ := r
  refine TableCost.map _ ?_
  refine (?_ : RedCost _ (fun _ _ => 0) fun s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞) +
    forge) _
  refine RedCost.bind (K := fun _ s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞) + forge)
    ((emulatedRuns_cost hprog A.net step hround' _ _ .top runLimit).frame _) fun _ => RedCost.get_bind fun s => ?_
  split
  · exact (TableCost.pure _ _).mono (fun _ => le_rfl) zero_le
  · refine ((RedCost.simulateQ _ (fun t => (forgeCost t : ℕ∞))
      (fun s => (runsPotential (C := C) circuits settings runLimit step s.runs : ℕ∞))
      (forgeOracles_cost hprog A.net step hround') (A.forge pk top)) s).mono (fun _ => zero_le) ?_
    exact (add_le_add hforge' le_rfl).trans (le_of_eq (add_comm _ _))

end Forger

/-! ## The cost conjunct of `DkgSecurityPreservation` -/

section Claim

variable {E : Type} [Field E] [Algebra Bit E]

/-- The emulated operators forward no call in the seed generation and at most `operatorCalls C tree`
calls in a run of `tree`. -/
theorem programCost (K : Constants C E) (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (hsize : 0 < settings.batchSize) : ProgramCost K circuits settings D :=
  ⟨fun i parts => seedGenWith_cost i parts, fun parameter seeds openings randomizer i operator tree =>
    emulatedProgram_cost K circuits settings D hsize parameter seeds openings randomizer i operator tree⟩

/-- The first conjunct of `DkgSecurityPreservation`. The forger `dkgReduction` costs at most the budget `q` of
the adversary plus `dkgOverhead runLimit C`. -/
theorem dkgReduction_cost (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (runLimit : ℕ) (hsize : 0 < settings.batchSize) (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    ∀ pk top, QueryCostAtMost (dkgReduction K circuits settings runLimit prims.aes D A pk top) adversaryCost
      (q + dkgOverhead runLimit C) := fun pk top =>
  dkgReduction_cost_of_programCost K circuits settings runLimit prims.aes D (programCost K circuits settings D hsize)
    A q bounded pk top

/-- `dkgReduction_cost` is the first component of the field. -/
example [Fintype E] [DecidableEq E] (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
    (h : DkgSecurityPreservation prims K circuits settings runLimit (dkgReduction K circuits settings runLimit))
    (hsize : 0 < settings.batchSize) (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) :
    (h hsize D A q bounded).1 = dkgReduction_cost prims K circuits settings runLimit hsize D A q bounded :=
  rfl

end Claim

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dkgReduction_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dkgReduction_cost

