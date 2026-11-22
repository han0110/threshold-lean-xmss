import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Sound
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.Budgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Glue

/-!
# The ledger of the coin keys at the end of the game

`flows_treeProgram` gives the coin calls of one honest operator in one run of a tree,
`treePhase_soundCache` the ledger of the phase of one run of a tree, and `streamTreeRun_soundCache`
the ledger with its monitor. A run of `tree` adds at most `treeFuel * step + treeCoins tree` charged
inputs and `treeCoins tree` expansion keys. `SoundRun` is this ledger of one run, and `SoundPot` is
the potential of the walk of `firstRunOf` for each run with that ledger, in the form of
`FirstCounts.Pot`. Each attempted run of a tree takes its charge from the runs that remain, the calls
of the forger move the potential, and the signing answers keep it. `soundAtEndOf` bounds the ledger at
the end for each such run, and `soundAtEnd` proves `Ready.SoundAtEnd` as its instance at
`streamTreeRun`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open FirstCounts DigestBudgets
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

attribute [local instance] Classical.propDecidable

attribute [local irreducible] wrongOutput

/-! ## The coin calls of one run of a tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A computation of `H` on `.hash` and `.prf` only makes no call in class `challenge`. -/
theorem sflows_lift_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    SFlows (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) 0 :=
  SFlows.of_stateBound (lift_tweakable_bound (c := .challenge) nofun oa)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree make at most `P` coin calls for each batch of the tree, when each run of a
job list of the protocol makes at most `P` for each of its batches and the local steps make none. -/
theorem sflows_ceremonyOutput_of
    (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), SFlows (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (P : ℕ)
    (hrun : ∀ (b : Fin (2 ^ layerHeight)) (encoding : Encoding) (jobs : List Job),
      (jobs = topJobs ∨ jobs = bottomJobs b ∨ jobs = signJobs b encoding) →
        SFlows (run jobs) ((chunks settings.batchSize jobs).length * P)) (top : TopTree) (tree : Tree) :
    SFlows (ceremonyOutput lift parameter run top tree) (treeBatches settings tree * P) := by
  cases tree with
  | top =>
    rw [treeBatches.eq_1]
    unfold ceremonyOutput
    refine (SFlows.bind (m := 0) (hrun ⟨0, Nat.two_pow_pos _⟩ (fun _ => digit 0) topJobs (Or.inl rfl))
      fun out => ?_).mono (Nat.add_zero _).le
    rcases out with _ | outputs
    · exact SFlows.pure _
    · exact SFlows.zero_bind (hlift _) fun _ => SFlows.pure _
  | bottom b =>
    rw [treeBatches.eq_2, Nat.add_mul]
    unfold ceremonyOutput
    refine SFlows.bind (hrun b (fun _ => digit 0) (bottomJobs b) (Or.inr (Or.inl rfl))) fun out => ?_
    rcases out with _ | outputs
    · exact (SFlows.pure _).mono (Nat.zero_le _)
    refine SFlows.zero_bind (hlift _) fun root => ?_
    refine SFlows.zero_bind (hlift _) fun base => ?_
    refine SFlows.zero_bind (hlift _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact (SFlows.pure _).mono (Nat.zero_le _)
    rw [← chunks_signJobs settings b encoding]
    refine (SFlows.bind (m := 0) (hrun b encoding (signJobs b encoding) (Or.inr (Or.inr rfl))) fun out => ?_).mono
      (Nat.add_zero _).le
    rcases out with _ | values
    · exact SFlows.pure _
    refine SFlows.zero_bind (hlift _) fun path => ?_
    refine SFlows.zero_bind (hlift _) fun topRoot => ?_
    split_ifs
    · exact SFlows.pure _
    · exact SFlows.pure _

omit [Fintype E] [DecidableEq E] in
/-- The ceremonies of a tree at one operator make at most `batchCoins` coin calls for each batch of
the tree. Each job list of the protocol is admissible, the signature ceremony for each encoding. -/
theorem sflows_ceremonyOutput (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    SFlows (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) top tree)
      (treeBatches settings tree * batchCoins circuits settings) :=
  sflows_ceremonyOutput_of settings (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => sflows_lift_tweakable oa) keys.parameter _ _
    (fun b encoding jobs h st => flows_ceremonyRun K circuits settings i keys jobs
      (admissible_of_protocol circuits settings b encoding jobs h) st) top tree

omit [Fintype E] [DecidableEq E] in
/-- The program of one operator in one run of `tree` makes at most `batchCoins` coin calls for each
batch of the tree. -/
theorem flows_treeProgram (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    Flows (treeProgram K circuits settings i operator tree) (treeBatches settings tree * batchCoins circuits settings) := by
  have hnew : ∀ (keys : Keys C) (top : TopTree),
      Flows (newTree K circuits settings i keys top tree) (treeBatches settings tree * batchCoins circuits settings) := by
    intro keys top
    unfold newTree
    refine (Flows.bind (m := 0) ?_ fun out _ => ?_).mono (Nat.add_zero _).le
    · rw [StateT.run'_eq, map_eq_bind_pure_comp]
      exact (Flows.bind (m := 0) (sflows_ceremonyOutput K circuits settings i keys top tree (0, 0)) fun _ _ =>
        Flows.of_classBound (ClassBound.pure _)).mono (Nat.add_zero _).le
    · rcases out with _ | output
      · exact Flows.of_classBound ClassBound.failure
      · exact Flows.of_classBound (ClassBound.pure _)
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact (Flows.of_classBound ClassBound.failure).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact hnew keys _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact (Flows.of_classBound ClassBound.failure).mono (Nat.zero_le _)
    · simp only [treeProgram, hk]
      exact (Flows.of_classBound ClassBound.failure).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact (Flows.of_classBound ClassBound.failure).mono (Nat.zero_le _)
    · simp only [treeProgram, hk, ht]
      exact hnew keys top

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A call of `HonestIn c` adds a cell of class `c`. -/
theorem adds_of_honestIn {c : HashClass} {t : (WorldSpec C).Domain} (h : HonestIn c t) : FirstCounts.Adds c t := by
  rcases t with (_ | _) | _
  · exact h.elim
  · exact h.elim
  · exact h

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A call of `OwnAdds c` adds a cell of class `c`. -/
theorem adds_of_ownAdds {c : HashClass} {t : (WorldSpec C).Domain} (h : OwnAdds c t) : FirstCounts.Adds c t := by
  rcases t with (_ | _) | _
  · exact h
  · trivial
  · exact h.elim

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The monitor makes no call of `Q` when `Q` excludes each call of the monitor. -/
theorem wrongOutput_bound (D : C.Coalition) (Q : (WorldSpec C).Domain → Prop)
    (hQ : ∀ t, GameCount.MonitorCall t → ¬ Q t) (keys : C.Party → Option (Keys C)) (tree : Tree)
    (outputs : C.Party → Option TreeOutput) : IsQueryBoundP (wrongOutput D keys tree outputs) Q 0 :=
  (noCall_iff _ _).1 (GameCount.wrongOutput_noCall D Q hQ keys tree outputs)

omit [Fintype E] [DecidableEq E] in
/-- The ledger of the phase of one run of `tree`. An adversary with `step` calls in class `challenge`
in a round adds at most `treeFuel * step` charged inputs, and the honest operators add at most
`coinKeysOf (treeBatches tree)` charged inputs and expansion keys, on every outcome. -/
theorem treePhase_soundCache (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .challenge) step) (tree : Tree)
    (s : RealState C net.State) (w : StreamState C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hs : SoundCache 0 w.1 seen keys) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
      (treeFuel circuits settings) s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree)).run w),
      ∃ (seen' : Finset (Query C)) (keys' : Finset HashOutput), SoundCache 0 z.2.1 seen' keys' ∧
        seen'.card ≤ seen.card +
          (treeFuel circuits settings * step + coinKeysOf circuits settings C (treeBatches settings tree)) ∧
        keys'.card ≤ keys.card + coinKeysOf circuits settings C (treeBatches settings tree) := by
  have hflow : WorldFlow (executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
      fun i => treeProgram K circuits settings i (s.operators i) tree)
      (coinKeysOf circuits settings C (treeBatches settings tree)) ∅ := by
    refine (worldFlow_executePhase D net _ _ _ (fun _ => treeBatches settings tree * batchCoins circuits settings)
      (fun j _ => flows_treeProgram K circuits settings j _ tree) ∅).mono ?_ subset_rfl
    rw [sum_batchCoins]
  intro z hz
  obtain ⟨seen', keys', h', hc', hk'⟩ := simulateQ_soundCache prims D _ _ _ ∅ w seen keys
    (ownAdds_executePhase .challenge D net step hround _ _ _) hflow (Finset.empty_subset _) hs z hz
  exact ⟨seen', keys', h', by omega, hk'⟩

omit [Fintype E] [DecidableEq E] in
/-- The ledger of one run of `tree` with its monitor. It is the ledger of the phase, and the monitor
adds no charged input and no expansion key. -/
theorem streamTreeRun_soundCache (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .challenge) step) (tree : Tree)
    (s : RealState C net.State) (w : StreamState C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (hs : SoundCache 0 w.1 seen keys) :
    ∀ z ∈ support ((streamTreeRun prims K circuits settings D net tree s).run w),
      ∃ (seen' : Finset (Query C)) (keys' : Finset HashOutput), SoundCache 0 z.2.1 seen' keys' ∧
        seen'.card ≤ seen.card +
          (treeFuel circuits settings * step + coinKeysOf circuits settings C (treeBatches settings tree)) ∧
        keys'.card ≤ keys.card + coinKeysOf circuits settings C (treeBatches settings tree) := by
  have hmonitor : ∀ (Q : (WorldSpec C).Domain → Prop), (∀ t, Q t → FirstCounts.Adds .challenge t) →
      ∀ outputs : C.Party → Option TreeOutput,
        IsQueryBoundP (wrongOutput D (fun i => (s.operators i).keys) tree outputs) Q 0 := fun Q hQ outputs =>
    wrongOutput_bound D Q (fun t ht hq => FirstCounts.monitorCall_not_adds (c := .challenge) nofun ht (hQ t hq))
      _ _ _
  intro z hz
  unfold streamTreeRun at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, y, hy, rfl⟩ := hz
  obtain ⟨seen₁, keys₁, h₁, hc₁, hk₁⟩ :=
    treePhase_soundCache prims K circuits settings D net step hround tree s w seen keys hs r hr
  obtain ⟨seen₂, keys₂, h₂, hc₂, hk₂⟩ := simulateQ_soundCache prims D _ 0 0 ∅ r.2 seen₁ keys₁
    (hmonitor _ (fun _ h => adds_of_ownAdds h) _)
    (worldFlow_of_noHonestChallenge _ (hmonitor _ (fun _ h => adds_of_honestIn h) _) 0 ∅)
    (Finset.empty_subset _) h₁ y hy
  exact ⟨seen₂, keys₂, h₂, by omega, by omega⟩

end Tree

/-! ## The ledger of the coin keys through the game -/

section Walk

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (step keysBound : ℕ)

attribute [local instance] inhabitedField

/-- The honest coin keys of one run of `tree`. -/
abbrev treeCoins (C : Committee) (tree : Tree) : ℕ := coinKeysOf circuits settings C (treeBatches settings tree)

/-- The potential of the walk. The ledger `SoundCache` holds with `seen` and `keys`, `seen` with the
charge of the runs that remain is at most `k`, and `keys` with the honest coin keys of the runs that
remain is at most `keysBound`. -/
def SoundPot {σ : Type} (k : ℕ) (s : FirstState C σ) (w : StreamState C) : Prop :=
  ∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 w.1 seen keys ∧
    seen.card + FirstCounts.remaining runLimit
      (fun tree => treeFuel circuits settings * step + treeCoins circuits settings C tree) s.real.runs ≤ k ∧
    keys.card + FirstCounts.remaining runLimit (treeCoins circuits settings C) s.real.runs ≤ keysBound

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem soundPot_mono {σ : Type} : ∀ k k' (s : FirstState C σ) w, k ≤ k' →
    SoundPot circuits settings runLimit step keysBound k s w → SoundPot circuits settings runLimit step keysBound k' s w := by
  rintro k k' s w hk ⟨seen, keys, hs, h1, h2⟩
  exact ⟨seen, keys, hs, h1.trans hk, h2⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem soundPot_frame {σ : Type} : FrameKeeps (C := C) (σ := σ) (SoundPot circuits settings runLimit step keysBound) := by
  intro k s s' w _ hruns hpot
  obtain ⟨seen, keys, hs, h1, h2⟩ := hpot
  refine ⟨seen, keys, hs, ?_, ?_⟩
  · rw [hruns]
    exact h1
  · rw [hruns]
    exact h2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem ownAdds_of_adds {c : HashClass} {β : Type} {oa : OracleComp (WorldSpec C) β} {n : ℕ}
    (h : IsQueryBoundP oa (FirstCounts.Adds c) n) : IsQueryBoundP oa (OwnAdds c) n :=
  h.of_imp fun _ ht => adds_of_ownAdds ht

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem honestIn_of_adds {c : HashClass} {β : Type} {oa : OracleComp (WorldSpec C) β} {n : ℕ}
    (h : IsQueryBoundP oa (FirstCounts.Adds c) n) : IsQueryBoundP oa (HonestIn c) n :=
  h.of_imp fun _ ht => adds_of_honestIn ht

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the world with at most `a` counted coin or expansion calls and no honest call in
class `challenge` moves the potential by `a`. -/
theorem inStream_soundMoves (D : C.Coalition) {σ β : Type} (oa : OracleComp (WorldSpec C) β) (a : ℕ)
    (hown : IsQueryBoundP oa (OwnAdds .challenge) a) (hhonest : IsQueryBoundP oa (HonestIn .challenge) 0) :
    FirstCounts.Moves (SoundPot circuits settings runLimit step keysBound) a (inStream (σ := σ) prims D oa) := by
  rintro k s w ⟨seen, keys, hs, h1, h2⟩ z hz
  simp only [inStream, StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨seen', keys', h', hc', hk'⟩ := simulateQ_soundCache prims D oa a 0 ∅ w seen keys hown
    (worldFlow_of_noHonestChallenge oa hhonest 0 ∅) (Finset.empty_subset _) hs y hy
  exact ⟨seen', keys', h', by dsimp only; omega, by dsimp only; omega⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem soundPot_quiet (D : C.Coalition) {σ : Type} :
    QuietKeeps prims D .challenge (σ := σ) (SoundPot circuits settings runLimit step keysBound) := fun oa h =>
  inStream_soundMoves prims circuits settings runLimit step keysBound D oa 0 (ownAdds_of_adds h) (honestIn_of_adds h)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The ledger of each run of the run `run`. A run of `tree` adds at most `treeFuel * step` charged
inputs of the network and `treeCoins tree` charged inputs and expansion keys of the honest operators.
`streamTreeRun_soundCache` states it for `streamTreeRun`. -/
def SoundRun {σ : Type} (run : RunOf C σ) : Prop :=
  ∀ (tree : Tree) (s : RealState C σ) (w : StreamState C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    SoundCache 0 w.1 seen keys → ∀ z ∈ support ((run tree s).run w),
      ∃ (seen' : Finset (Query C)) (keys' : Finset HashOutput), SoundCache 0 z.2.1 seen' keys' ∧
        seen'.card ≤ seen.card + (treeFuel circuits settings * step + treeCoins circuits settings C tree) ∧
        keys'.card ≤ keys.card + treeCoins circuits settings C tree

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A run of `tree` that the game allows keeps the potential. Its charge comes from the runs that
remain. -/
theorem firstTreeRun_soundPot {σ : Type} (run : RunOf C σ) (hsound : SoundRun circuits settings step run)
    (ready : RealState C σ → StreamState C → Prop) (tree : Tree)
    (k : ℕ) (s : FirstState C σ) (w : StreamState C)
    (hs : SoundPot circuits settings runLimit step keysBound k s w) (hrun : s.real.runs tree < runLimit) :
    ∀ z ∈ support (((firstTreeRunOf run ready tree).run s).run w),
      SoundPot circuits settings runLimit step keysBound k z.1.2 z.2 := by
  intro z hz
  unfold firstTreeRunOf at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  obtain ⟨seen, keys, hcache, h1, h2⟩ := hs
  obtain ⟨seen', keys', h', hc', hk'⟩ := hsound tree s.real w seen keys hcache x hx
  have e1 := FirstCounts.remaining_update runLimit
    (fun tree => treeFuel circuits settings * step + treeCoins circuits settings C tree) s.real.runs tree hrun
  have e2 := FirstCounts.remaining_update runLimit (treeCoins circuits settings C) s.real.runs tree hrun
  have hcoins : treeCoins circuits settings C tree = coinKeysOf circuits settings C (treeBatches settings tree) := rfl
  refine ⟨seen', keys', h', ?_, ?_⟩
  · change seen'.card + FirstCounts.remaining runLimit _ (Function.update s.real.runs tree (s.real.runs tree + 1)) ≤ k
    omega
  · change keys'.card + FirstCounts.remaining runLimit _ (Function.update s.real.runs tree (s.real.runs tree + 1)) ≤
      keysBound
    omega

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The ledger at the end of `firstRunOf`, for each readiness test and each run with the ledger
`SoundRun`. The seed generation, each run of each tree up to `runLimit` and the forger charge their
calls, and the honest operators add at most the coin keys of `runLimit` runs of each tree. -/
theorem firstRunOf_soundCache (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (hsound : SoundRun circuits settings step run)
    (ready : RealState C A.net.State → StreamState C → Prop) (start forge : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.net.start x z) (InClass .challenge) start)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .challenge) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .challenge) forge) :
    ∀ r ∈ support (firstRunOf prims runLimit D A run ready),
      ∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 r.2.1 seen keys ∧
        seen.card ≤ start + setupRounds * step + FirstCounts.remaining runLimit
          (fun tree => treeFuel circuits settings * step + treeCoins circuits settings C tree) (fun _ => 0) + forge ∧
        keys.card ≤ FirstCounts.remaining runLimit (treeCoins circuits settings C) (fun _ => 0) := by
  intro r hr
  unfold firstRunOf at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hseedOwn := ownAdds_realExecution .challenge D A.net start step hstart hround setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  have hseedHonest := (GameCount.bound_iff _ _ _).1 (seedHonest (C := C) (E := E) (c := .challenge) nofun D A.net)
  obtain ⟨seen₀, keys₀, h₀, hc₀, hk₀⟩ := simulateQ_soundCache prims D _ _ 0 ∅ (∅, ∅) ∅ ∅ hseedOwn
    (worldFlow_of_noHonestChallenge _ hseedHonest 0 ∅) (Finset.empty_subset _)
    (SoundCache.of_covered 0 ∅ ∅ fun _ h => absurd rfl h) _ hy
  have hcall : ∀ t, FirstCounts.Moves (σ := A.net.State)
      (SoundPot circuits settings runLimit step (FirstCounts.remaining runLimit (treeCoins circuits settings C)
        (fun _ => 0))) (if ForgeInClass (σ := A.net.State) .challenge (.inl t) then 1 else 0)
      (inStream prims D (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) := by
    intro t
    refine inStream_soundMoves prims circuits settings runLimit step _ D _ _ ?_ ?_
    · rw [ThresholdLeanXmssSecurity.adversary_query]
      change IsQueryBoundP (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
        (OwnAdds .challenge) (if InClass .challenge t then 1 else 0)
      rw [isQueryBoundP_query_iff]
      split_ifs with ht
      · exact fun _ => Nat.one_pos
      · exact fun h => absurd h ht
    · rw [ThresholdLeanXmssSecurity.adversary_query]
      change IsQueryBoundP (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
        (HonestIn .challenge) 0
      rw [isQueryBoundP_query_iff]
      exact fun h => h.elim
  have hpot : SoundPot circuits settings runLimit step
      (FirstCounts.remaining runLimit (treeCoins circuits settings C) (fun _ => 0))
      (start + setupRounds * step + FirstCounts.remaining runLimit
        (fun tree => treeFuel circuits settings * step + treeCoins circuits settings C tree) (fun _ => 0))
      (⟨startState D state keys, if (startState D state keys).flag then some (.seeds, world) else none⟩ :
        FirstState C A.net.State) world := by
    refine ⟨seen₀, keys₀, h₀, ?_, ?_⟩
    · change seen₀.card + FirstCounts.remaining runLimit _ (fun _ => 0) ≤ _
      simp only [Finset.card_empty] at hc₀
      omega
    · change keys₀.card + FirstCounts.remaining runLimit _ (fun _ => 0) ≤ _
      simp only [Finset.card_empty] at hk₀
      omega
  obtain ⟨seen, keys', hcache, h1, h2⟩ := FirstCounts.moves_bind
    (firstTreeRuns_walk runLimit D
      (SoundPot circuits settings runLimit step (FirstCounts.remaining runLimit (treeCoins circuits settings C)
        (fun _ => 0))) run ready .top
      (firstTreeRun_soundPot circuits settings runLimit step _ run hsound ready .top) runLimit)
    (fun _ => firstSigning_walk prims runLimit D .challenge nofun
      (signQuiet nofun) A run
      (SoundPot circuits settings runLimit step (FirstCounts.remaining runLimit (treeCoins circuits settings C)
        (fun _ => 0)))
      (soundPot_mono circuits settings runLimit step _) ready
      (fun tree => firstTreeRun_soundPot circuits settings runLimit step _ run hsound ready tree)
      (soundPot_quiet prims circuits settings runLimit step _ D) (soundPot_frame circuits settings runLimit step _)
      (ForgeInClass .challenge) (fun _ => id) hcall forge hforge)
    _ _ world hpot x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)
  exact ⟨seen, keys', hcache, by omega, by omega⟩

end Walk

/-! ## The ledger at the end of the game -/

section End

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

attribute [local instance] inhabitedField

/-- The honest coin keys of `runLimit` runs of each tree are `gameCoinKeys`. -/
theorem remaining_treeCoins :
    FirstCounts.remaining runLimit (treeCoins circuits settings C) (fun _ => 0) =
      gameCoinKeys circuits settings runLimit C := by
  simp only [FirstCounts.remaining, Nat.sub_zero, treeCoins, coinKeysOf, gameCoinKeys, gameBatches]
  set M := maxBatch circuits settings fun jobs => halvings (tupleCount jobs)
  rw [show runLimit * (treeBatches settings .top + ∑ b : Fin (2 ^ layerHeight), treeBatches settings (.bottom b)) *
      C.n * (M + 2) = runLimit * (treeBatches settings .top * C.n * (M + 2)) +
        ∑ b : Fin (2 ^ layerHeight), runLimit * (treeBatches settings (.bottom b) * C.n * (M + 2)) by
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
    ring]

theorem remaining_seenCost (step : ℕ) :
    FirstCounts.remaining runLimit (fun tree => treeFuel circuits settings * step + treeCoins circuits settings C tree)
        (fun _ => 0) =
      runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step +
        FirstCounts.remaining runLimit (treeCoins circuits settings C) (fun _ => 0) := by
  simp only [FirstCounts.remaining, Nat.sub_zero, Nat.mul_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- At the end of the game with the run `run` the coin keys and the expansions are within the ledger,
for each readiness test, when each run has the ledger `SoundRun` for each bound `step` of a round of
the network. -/
theorem soundAtEndOf (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q) (run : RunOf C A.net.State)
    (hsound : ∀ step, (∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .challenge) step) →
      SoundRun circuits settings step run)
    (ready : RealState C A.net.State → StreamState C → Prop) :
    ∀ r ∈ support (firstRunOf prims runLimit D A run ready),
      ∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 r.2.1 seen keys ∧
        seen.card ≤ (startBudget circuits settings runLimit C q).coins ∧
        keys.card ≤ (startBudget circuits settings runLimit C q).keys := by
  intro r hr
  obtain ⟨start, step, forge, hsum, hs, hround, hf⟩ :=
    dkgTsigBounded_classBounded circuits settings runLimit bounded .challenge
  dsimp only at hsum
  obtain ⟨seen, keys, h, h1, h2⟩ := firstRunOf_soundCache prims circuits settings runLimit step D A run
    (hsound step hround) ready start forge hs hround hf r hr
  rw [remaining_seenCost, remaining_treeCoins] at h1
  rw [remaining_treeCoins] at h2
  have e : dkgTsigRounds circuits settings runLimit * step =
      setupRounds * step + runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step := by
    unfold dkgTsigRounds
    ring
  refine ⟨seen, keys, h, ?_, h2⟩
  change seen.card ≤ q + gameCoinKeys circuits settings runLimit C
  omega

omit [Fintype E] [DecidableEq E] in
/-- At the end of the game the coin keys and the expansions are within the ledger. -/
theorem soundAtEnd : Ready.SoundAtEnd prims K circuits settings runLimit := fun D A q bounded r hr =>
  soundAtEndOf prims circuits settings runLimit D A q bounded _
    (fun step hround => streamTreeRun_soundCache prims K circuits settings D A.net step hround) _ r hr

end End

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.soundAtEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.soundAtEnd
