import ThresholdLeanXmss.Statement

/-!
# The position of a batch in a ceremony

A ceremony starts at public counters. The tag of a batch is the batch counter, and it does not
start at zero in a signature ceremony. `ceremonySimulator` reads the outputs of `F_ceremony` at the
position `k - counters.2` of batch `k`.

* `ceremonyWith_position` states that the batch at position `j` of a ceremony runs with the gadgets
  of position `j`, for every start of the counters. Its tag is `counters.2 + j`.
* `getD_chunks_map` states that the outputs of `F_ceremony` at position `j` of `chunks` are the
  outputs of the jobs of batch `j`.
* `ceremonySimulator_answer` states that `ceremonySimulator` runs `ceremonyWith` with such gadgets.

This file imports only the statement layer.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-! ## The batches of a list -/

theorem chunks_map {α β : Type} (size : ℕ) (f : α → β) (l : List α) :
    chunks size (l.map f) = (chunks size l).map (List.map f) := by
  simp only [chunks, List.length_map, List.map_map, Function.comp_def, List.map_take, List.map_drop]

/-- The outputs at position `j` of `chunks` are the outputs of the jobs of batch `j`. -/
theorem getD_chunks_map {α β : Type} (size : ℕ) (f : α → β) (l : List α) (j : ℕ) :
    (chunks size (l.map f)).getD j [] = ((chunks size l).getD j []).map f := by
  rw [chunks_map]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (chunks size l)[j]? <;> rfl

/-! ## The batches of a ceremony -/

section Programs

variable [Field E] [Algebra Bit E] (K : Constants C E)

/-- The batches of a ceremony from the label `label` and the tag `k`. The batch at position `j` has
the tag `k + j - j₀` for the start `j₀` of the positions, and it runs with the gadgets
`gadgets ctx j jobs` of its position. -/
def batchesAt (circuits : Circuits) (gadgets : Context C → ℕ → List Job → RunGadgets C E G)
    (ctx : Context C) : List (List Job) → ℕ → ℕ → ℕ →
      PartyM C E G (List (Option (List (List Bit))) × (ℕ × ℕ))
  | [], _, label, k => pure ([], (label, k))
  | jobs :: rest, j, label, k => do
      let inputs ← jobs.mapM (inputShares ctx)
      let r ← (runJobs K (gadgets ctx j jobs) (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run
        ⟨fun _ => [], label, k⟩
      let rs ← batchesAt circuits gadgets ctx rest (j + 1) r.2.label (k + 1)
      pure (some r.1 :: rs.1, rs.2)

/-- A ceremony from the counters `(label, k₀ + j)`, with gadgets that read the position `k - k₀` of
batch `k`. It is the PRSS setup and then the batches from position `j`. -/
theorem ceremonyRun_position (circuits : Circuits) (settings : Settings)
    (gadgets : Context C → ℕ → List Job → RunGadgets C E G) (i : C.Party) (keys : Keys C)
    (jobs : List Job) (label k₀ j : ℕ) :
    (ceremonyRun K circuits settings (fun ctx k js => gadgets ctx (k - k₀) js) i keys jobs).run (label, k₀ + j) =
      prssSetup i >>= fun prss =>
        batchesAt K circuits gadgets ⟨i, keys, prss⟩ (chunks settings.batchSize jobs) j label (k₀ + j) >>= fun p =>
          pure (p.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], p.2) := by
  have hbatches : ∀ (ctx : Context C) (batches : List (List Job)) (label j : ℕ),
      (batches.mapM (fun js => (do
        let (label, k) ← get
        let inputs ← StateT.lift (js.mapM (inputShares ctx))
        let (outputs, state) ← StateT.lift ((runJobs K (gadgets ctx (k - k₀) js)
          (js.map (circuits ctx.keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩)
        set (state.label, k + 1)
        pure (some outputs) : StateT (ℕ × ℕ) (PartyM C E G) (Option (List (List Bit)))))).run (label, k₀ + j) =
      batchesAt K circuits gadgets ctx batches j label (k₀ + j) := by
    intro ctx batches
    induction batches with
    | nil => intro label j; simp [batchesAt]
    | cons js rest ih =>
      intro label j
      simp only [List.mapM_cons, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
        StateT.run_pure, bind_assoc, pure_bind, batchesAt, Nat.add_sub_cancel_left]
      refine bind_congr fun inputs => bind_congr fun r => ?_
      exact congrArg (· >>= fun rs => pure (some r.1 :: rs.1, rs.2)) (ih r.2.label (j + 1))
  simp only [ceremonyRun, batched, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure]
  refine bind_congr fun prss => ?_
  exact congrArg (· >>= fun p => pure (p.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], p.2))
    (hbatches ⟨i, keys, prss⟩ (chunks settings.batchSize jobs) label j)

/-- The ceremony that `ceremonySimulator` runs. From every start `counters`, the batch at position
`j` runs with the gadgets of position `j`, and the tag of its coin keys is `counters.2 + j`. -/
theorem ceremonyWith_position (circuits : Circuits) (settings : Settings)
    (gadgets : Context C → ℕ → List Job → RunGadgets C E G) (i : C.Party) (keys : Keys C)
    (counters : ℕ × ℕ) (jobs : List Job) :
    ceremonyWith K circuits settings (fun ctx k js => gadgets ctx (k - counters.2) js) i keys counters jobs =
      prssSetup i >>= fun prss =>
        batchesAt K circuits gadgets ⟨i, keys, prss⟩ (chunks settings.batchSize jobs) 0 counters.1 counters.2 >>=
          fun p => match p.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
            | some outputs => pure outputs
            | none => failure := by
  have h := ceremonyRun_position K circuits settings gadgets i keys jobs counters.1 counters.2 0
  rw [Nat.add_zero] at h
  unfold ceremonyWith
  rw [StateT.run'_eq, show counters = (counters.1, counters.2) from rfl, h]
  simp only [map_bind, map_pure, bind_assoc, pure_bind]
  refine bind_congr fun prss => bind_congr fun p => ?_
  generalize p.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = o
  cases o <;> rfl

end Programs

/-! ## The simulator of a ceremony -/

section Simulator

variable [Field E] [Algebra Bit E] (K : Constants C E)

attribute [local instance] Classical.propDecidable

/-- The gadgets of `ceremonySimulator` for the batch at position `j`. The opening shifts the first
lacked term by the outputs of `F_ceremony` at position `j` of `chunks`. -/
def simulatorGadgets (circuits : Circuits) (settings : Settings) (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (opened : List (List Bit)) (ctx : Context C) (j : ℕ) (batch : List Job) :
    RunGadgets C E RealSpec :=
  { realRunGadgets K ctx settings.mode with
    output := fun v count => do
      let clear ← StateT.lift (oracleStep (batch.mapM (evalJob circuits parameter seeds)))
      let shift := fun g => (((chunks settings.batchSize opened).getD j []).flatten.getD g 0) + (clear.flatten.getD g 0)
      StateT.lift (openRep K ctx (fun T g => if lackedTerm D.1 = some T then v T g + shift g else v T g) count) }

/-- `ceremonySimulator` runs `ceremonyWith` with gadgets that read the position `k - counters.2` of
batch `k`. So `ceremonyWith_position` applies to the program that it runs. -/
theorem ceremonySimulator_answer (circuits : Circuits) (settings : Settings) (counters : ℕ × ℕ) (jobs : List Job)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (st : (ceremonySimulator K circuits settings counters jobs D A).State) (parameter : PublicParameter)
    (opened : List (List Bit)) :
    (ceremonySimulator K circuits settings counters jobs D A).answer st (parameter, opened) =
      (let seeds : C.Term → HashOutput := fun T => (C.parties.findSome? fun j =>
        if j ∈ C.holders T then (st.corrupt j).map (·.seed T) else none).getD 0
      let keys : Keys C := ⟨parameter, seeds, fun _ => 0⟩
      do
        let (((state, outputs), _), calls) ← ((executePhase (emulatedRoles D) D A noFunctionality
          (ceremonyFuel circuits settings) st.adversary fun i =>
            (ceremonyWith K circuits settings (fun ctx k js =>
              simulatorGadgets K circuits settings D parameter seeds opened ctx (k - counters.2) js)
              i keys counters jobs : PartyM C E RealSpec (List (List Bit)))).run ∅).run
        pure (⟨state, st.log ++ calls, st.corrupt⟩, Finset.univ.filter fun i => (outputs i).isSome)) := rfl

end Simulator

end ThresholdLeanXmssSecurity
