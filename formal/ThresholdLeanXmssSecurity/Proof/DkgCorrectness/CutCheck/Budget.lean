import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Joint
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Cells

/-!
# The budget at the cut of one ceremony

`ceremonyBudget` proves `CeremonyBudget`. The honest programs of the prefix up to the check of batch
`k` take exactly `prefixRounds` rounds, so the prefix with more fuel has the law of the prefix with
exactly these rounds (`prefix_support_exact`). The adversary is charged for these rounds only. The
lead operator stops at the head of batch `k` (`honest_stop_counts`), so the count of the check is the tuple
count of that batch. For a positive count, the rounds of the prefix and the charge `checkRounds` of
the check are at most the rounds of the ceremony plus two (`prefix_add_checkRounds_le`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CutBudget

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The rounds of a prefix and of the check -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- For a batch `js` after the batches `pre` with a positive tuple count, the rounds of the prefix up
to its check and the charge `checkRounds` of its check are at most the rounds of the ceremony plus
two. The batch has `headRounds` rounds before its check, and its check and opening take the rest of
`exactBatchRounds`. -/
theorem prefix_add_checkRounds_le (parameter : PublicParameter) (jobs : List Job) (pre : List (List Job))
    (js : List Job) (suf : List (List Job)) (hsplit : chunks settings.batchSize jobs = pre ++ js :: suf)
    (hc : tupleCount (js.map (circuits parameter ·.kind)) ≠ 0) :
    prefixRounds circuits settings parameter jobs pre.length + checkRounds (tupleCount (js.map (circuits parameter ·.kind))) ≤
      CheckTiming.ceremonyRounds circuits settings parameter jobs + 2 := by
  unfold prefixRounds stopRounds CheckTiming.ceremonyRounds
  rw [hsplit, List.take_left' rfl, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero]
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  dsimp only
  rw [show ∀ (m : ReshareMode) (cs : List Circuit), headRounds m cs = depth cs * m.rounds + 1 from fun _ _ => rfl]
  unfold CheckTiming.exactBatchRounds checkRounds
  simp only [hc, ↓reduceIte]
  omega

/-! ## The prefix with more fuel -/

/-- The prefix of one ceremony from consistent keys, with at least `prefixRounds` rounds of fuel, has
the support of the prefix with exactly `prefixRounds` rounds. -/
theorem prefix_support_exact (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds k : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (hle : prefixRounds circuits settings (gameParameter D c.keys) c.jobs k ≤ rounds) :
    support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world) =
      support ((ceremonyPrefix prims K circuits settings D net
        (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) k c).run world) := by
  obtain ⟨m, rfl⟩ : ∃ m, rounds = prefixRounds circuits settings (gameParameter D c.keys) c.jobs k + m :=
    ⟨rounds - prefixRounds circuits settings (gameParameter D c.keys) c.jobs k, by omega⟩
  exact support_eq_of_evalDistEq (WorldSplit.executePhase_extra (impl := streamWorld prims D) D net noFunctionality
    (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) m c.adversary
    (fun i => cutCeremony K circuits settings k i c)
    (fun i hi => timed_cutCeremony K circuits settings k i c _ fun keys hkeys =>
      parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys) world)

/-! ## The stop of the lead operator -/

/-- An honest operator that stops in the prefix of one ceremony up to the check of batch `k` stops at
the head of batch `k`. The counts of its tuples are `headCounts` of the circuits of that batch under
the parameter of the game. -/
theorem honest_stop_counts (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds k : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (z : (net.State × (C.Party → Option (CutOf C E RunResult))) × StreamState C)
    (hz : z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world))
    (i : C.Party) (hi : i ∉ D.1) (point : CheckPoint C) (rest : RunState C → PartyM C E RealSpec RunResult)
    (hpoint : z.1.2 i = some (.inr (point, rest))) :
    ∃ pre js suf, chunks settings.batchSize c.jobs = pre ++ js :: suf ∧ pre.length = k ∧
      point.tuples.map (·.count) = headCounts (js.map (circuits (gameParameter D c.keys) ·.kind)) := by
  have hreach := SetupCut.executePhase_reach D net _ _ _ z.1 (mem_support_phase prims D _ world z hz) i hi _ hpoint
  unfold cutCeremony at hreach
  cases hkeys : c.keys i with
  | none =>
    simp only [hkeys] at hreach
    simp at hreach
  | some keys =>
    simp only [hkeys] at hreach
    obtain ⟨prss, pre, js, suf, hsplit, hlen, hpa⟩ :=
      (cutWalk_cutRun K circuits settings (c.counters.2 + k) i keys c.jobs c.counters _ hreach).2 point rest rfl
    rw [parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys] at hpa
    exact ⟨pre, js, suf, hsplit, by omega, hpa.2.1⟩

/-! ## The budget at the cut -/

/-- `CeremonyBudget`. The coin inputs of the prefix are charged at its exact rounds, and the padding
of `LedgerRoom` pays the two rounds of the check charge beyond the batch. The salts and the history
cells are charged at the fuel of the phase. -/
theorem ceremonyBudget : CeremonyBudget prims K circuits settings runLimit := by
  intro D net q step rounds hround ℓ c world hadm hready hroom hq hfuel k hk z hz start hjoint hglobal hcount
  have hseeds : seedsDiffer D c.keys = false := hready.1
  obtain ⟨hsplitStart, hsoundStart, hsaltsStart, -⟩ := hready.2.1
  obtain ⟨hall, j, hj, -, -, hcounts, -, -, -, -, hworld⟩ := Joint.jointStop_some D _ _ start hjoint
  obtain ⟨point, rest, hpt⟩ := hall j hj
  have hstop : stopPoint j (z.1.2 j) = point := by rw [hpt]; rfl
  obtain ⟨pre, js, suf, hsplit, hlen, hpc⟩ :=
    honest_stop_counts prims K circuits settings D net rounds k c world hseeds z hz j hj point rest hpt
  have hsum : start.counts.sum = tupleCount (js.map (circuits (gameParameter D c.keys) ·.kind)) := by
    rw [hcounts, hstop, hpc, sum_headCounts]
  have hjs : js ∈ chunks settings.batchSize c.jobs := by rw [hsplit]; simp
  have hmem := (hadm (gameParameter D c.keys) js hjs).1
  have hle := prefix_add_checkRounds_le circuits settings (gameParameter D c.keys) c.jobs pre js suf hsplit
    (hsum ▸ hcount)
  rw [hlen, ← hsum] at hle
  have hpre := prefixRounds_le circuits settings (gameParameter D c.keys) c.jobs k
  have hz' := prefix_support_exact prims K circuits settings D net rounds k c world hseeds (by omega) ▸ hz
  obtain ⟨seen, ekeys, hsc, hseen, hekeys⟩ := prefixSound prims K circuits settings D net step
    (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) k hround ℓ.coins ℓ.keys c world hadm
    hsoundStart z hz'
  obtain ⟨salts, hcover, hsalts⟩ := prefixSalts prims K circuits settings D net step rounds k hround ℓ.salts c
    world hsaltsStart z hz
  have hsplitZ := prefixSplit prims K circuits settings D net step rounds k hround ℓ.split c world hsplitStart z hz
  have hcoll : ¬ CacheHasCollision (splitRegionCache SplitHashDomain z.2.1) :=
    fun h => hglobal (Or.inr (Or.inr (Or.inr h)))
  have hmul : (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k + checkRounds start.counts.sum) * step ≤
      (rounds + 2) * step := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.add_mul] at hmul
  rw [Nat.add_mul] at hq
  obtain ⟨hroomCoins, hroomKeys, hroomSalts⟩ := hroom
  simp only [ledgerStep] at hroomCoins hroomKeys hroomSalts
  unfold CheckBudget
  rw [hworld]
  refine ⟨seen, ekeys, salts, _, ⟨hsc.mono_label (Nat.zero_le _), hcover, hsplitZ, hcoll⟩, by omega, by omega,
    by omega, by omega, ?_⟩
  rw [hsum]
  exact hmem

end CutBudget

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.ceremonyBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.ceremonyBudget
