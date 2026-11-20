import Sketch.Completeness
import ThresholdLeanXmssSecurity.Proof.Signing

/-!
# The abort of the dealer

`dealerAbort` proves `DealerAbort`. The top tree of `referenceTree` never fails, so the dealer
gives no bottom tree only when the randomizer search of bottom tree `b` fails.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

variable {C : Committee}

/-- `dealerDkg` on the random oracles, for the parameter, the seeds and the keys of `prawnsKeyGen`. -/
def dealerRo (parameter : PublicParameter) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C)
    (b : Fin (2 ^ layerHeight)) : OracleComp (RoSpec C) (SetupOutputs C) := do
  let some (.top top) ← referenceTree tweakable (prfValue seeds) parameter emptyTop .top
    | pure fun _ => (none, none, none)
  let output ← referenceTree tweakable (prfValue seeds) parameter top (.bottom b)
  pure fun i => (some (keys i), some top, (fun | some (.bottom tree) => some tree | _ => none) output)

/-- `dealerDkg` samples by `prawnsKeyGen` and then runs `dealerRo` on the free copy. -/
theorem dealerDkg_eq (b : Fin (2 ^ layerHeight)) :
    dealerDkg (C := C) b = free (liftComp prawnsKeyGen _) >>= fun x => φ (dealerRo x.1 x.2.1 x.2.2 b) := by
  unfold dealerDkg dealerKeyGen dealerKeyGenWith
  rw [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨parameter, seeds, keys⟩
  simp only [dealerRo, referenceTree_φ, bind_assoc, φ_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp [φ_pure]
  swap
  · simp [φ_pure]
  simp only [pure_bind, dealtWith, referenceTree_φ, φ_bind, bind_map_left, φ_pure]
  refine bind_congr fun output => ?_
  rcases output with _ | (_ | _) <;> rfl

/-- The outputs of `dealerDkg` in the world are the outputs of `dealerRo` from the empty cache. -/
theorem fst_runWorld_dealerDkg (prims : Primitives) (b : Fin (2 ^ layerHeight)) :
    Prod.fst <$> runWorld prims (dealerDkg (C := C) b) =
      prawnsKeyGen >>= fun x => Prod.fst <$> roRun prims (dealerRo x.1 x.2.1 x.2.2 b) ∅ := by
  rw [dealerDkg_eq, runWorld, simulateQ_bind]
  simp only [WriterT.run_bind, StateT.run'_eq, StateT.run_bind, world_sample_run]
  have hw : ∀ x : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C),
      (WriterT.run (simulateQ (world prims) (φ (dealerRo x.1 x.2.1 x.2.2 b)))).run ∅ =
        (fun p => ((p.1, (1 : Multiplicative ℕ)), p.2)) <$> roRun prims (dealerRo x.1 x.2.1 x.2.2 b) ∅ :=
    fun x => world_lift_run prims _ ∅
  simp only [StateT.run_map, bind_map_left, hw, map_bind, Functor.map_map]
  erw [map_bind]
  refine bind_congr (m := ProbComp) fun x => ?_
  exact Functor.map_map _ _ _

/-- `dealerRo` gives `none` to an operator only when the randomizer search of bottom tree `b` fails. -/
theorem dealerRo_fail (prims : Primitives) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (keys : C.Party → Keys C) (b : Fin (2 ^ layerHeight)) :
    Pr{let z ← roRun prims (dealerRo parameter seeds keys b) ∅}[∃ i,
        (z.1 i).1 = none ∨ (z.1 i).2.1 = none ∨ (z.1 i).2.2 = none] ≤
      (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold dealerRo
  refine step prims _ _ _ ∅ _ noMpc_empty fun r1 s1 hle1 hn1 hd1 hp1 => ?_
  have hm1 := hp1 IsMsg (Pres_refTop prims IsMsg (fun _ h => h) seeds parameter emptyTop) (noB_empty _)
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s1 hn1
  obtain ⟨top, htop, -, -⟩ := D_refTop (prims := prims) (h := h0) parameter seeds emptyTop
  have hr1 : r1 = some (.top top) := (hd1 h0 hg0 ha0).trans htop
  have htopf : ∀ h, Good prims h → Agrees h s1 → TopFacts prims h seeds parameter top := by
    intro h hg ha
    obtain ⟨top', htop', hc', hr'⟩ := D_refTop (prims := prims) (h := h) parameter seeds emptyTop
    have : some (TreeOutput.top top') = some (.top top) := htop'.symm.trans ((hd1 h hg ha).symm.trans hr1)
    cases this
    exact ⟨hc', hr'⟩
  subst hr1
  dsimp only
  refine (step_add prims _ _ _ (fun r => r = none) s1 0 hn1
    fun r2 s2 hr2 hle2 hn2 hd2 hp2 => ?_).trans
    (by rw [add_zero]; exact refBottom_fail prims seeds parameter top b s1 hn1 hm1 htopf)
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s2 hn2
  obtain ⟨hc0, hrt0⟩ := htopf h0 hg0 (ha0.mono hle2)
  rcases D_refBottom (prims := prims) (h := h0) parameter seeds top hc0 hrt0 b with hb | ⟨tree, hb, -⟩
  · exact absurd ((hd2 h0 hg0 ha0).trans hb) hr2
  have hr2' : r2 = some (.bottom tree) := (hd2 h0 hg0 ha0).trans hb
  subst hr2'
  rw [roRun_pure]
  simp

/-- `DealerAbort` holds. The top tree never fails, and bottom tree `b` fails with probability at most
`searchFailure`. -/
theorem dealerAbort : DealerAbort (C := C) := by
  intro prims b
  have hfin : (1 - codewordP) ^ randomizerAttemptLimit ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  rw [← toReal_failure]
  refine ENNReal.toReal_mono hfin ?_
  have h1 : Pr{let r ← runWorld prims (dealerDkg (C := C) b)}[∃ i,
        (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none] =
      Pr{let r ← Prod.fst <$> runWorld prims (dealerDkg (C := C) b)}[∃ i,
        (r i).1 = none ∨ (r i).2.1 = none ∨ (r i).2.2 = none] := by
    rw [prEvent_map]
  rw [h1, fst_runWorld_dealerDkg]
  refine pr_bind_le fun x _ => ?_
  rw [prEvent_map]
  exact dealerRo_fail prims _ _ _ b

/-- info: 'ThresholdLeanXmss.Sketch.dealerAbort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerAbort

end ThresholdLeanXmss.Sketch
