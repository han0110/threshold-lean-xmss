import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoDrop

/-!
# The law of the block of `midRun` and of the list block

`blockLaw` proves `BlockLaw`. In `compLocal` each two programs commute. So in pass 2 of each operator the
shared key calls of the pairs with `SharesHidden` move behind the other calls (`mapM_split`), and then
behind the whole block (`runEq_sequenceFin_split`). `echoCompare` proves `EchoCompare`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

section Law

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

theorem runEq_sequenceFin {α : Type} (I : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp)) :
    ∀ {n : ℕ} (f g : Fin n → OracleComp (LocalSpec C) α), (∀ j, RunEq I (f j) (g j)) →
      RunEq I (OverPermutation.sequenceFin f) (OverPermutation.sequenceFin g)
  | 0, f, g, _ => RunEq.refl _
  | n + 1, f, g, h => by
    simp only [OverPermutation.sequenceFin]
    exact (h 0).bind fun a => (runEq_sequenceFin I (fun j : Fin n => f j.succ) (fun j => g j.succ)
      fun j => h j.succ).bind fun _ => RunEq.refl _

/-- The shared key calls of one operator with the calls of the pairs with `SharesHidden` moved behind
the others. The answers of these pairs are set to `0`. -/
theorem mapM_split (S : C.Party → Prop) (addr : C.Party → Query C) {γ : Type} :
    ∀ (xs : List C.Party) (K : List HashOutput → OracleComp (LocalSpec C) γ), RunEq (compLocal prims D parts seed)
      ((xs.mapM fun l => liftComp (hashQuery (addr l)) (LocalSpec C)) >>= fun sh =>
        K (List.zipWith (fun l v => if S l then 0 else v) xs sh))
      ((xs.mapM fun l => liftComp (if S l then pure 0 else hashQuery (addr l)) (LocalSpec C)) >>= fun sh' =>
        (xs.mapM fun l => liftComp (if S l then hashQuery (addr l) else pure 0) (LocalSpec C)) >>= fun _ => K sh')
  | [], K => by
    refine RunEq.of_eq ?_
    simp
  | l :: xs, K => by
    have ih := mapM_split S addr (γ := γ) xs
    simp only [List.mapM_cons, bind_assoc, pure_bind, List.zipWith_cons_cons]
    by_cases hl : S l
    · simp only [hl, ite_true, liftComp_pure, pure_bind]
      refine (RunEq.bind_right _ fun v => ih (fun sh => K (0 :: sh))).trans ?_
      refine (runEq_swap (commutes_compLocal prims D parts seed) _ _ _).trans ?_
      exact RunEq.bind_right _ fun sh' => RunEq.refl _
    · simp only [hl, ite_false, liftComp_pure, pure_bind]
      refine RunEq.bind_right _ fun v => ?_
      have := ih (fun sh => K (v :: sh))
      simpa only [bind_assoc, pure_bind] using this


/-- The shared key calls of operator `j` for the pairs with `SharesHidden`, with the answers forgotten. -/
def discOne (j : C.Party) : Option (SeedGenEchoData C) → OracleComp (LocalSpec C) Unit
  | none => pure ()
  | some x => liftComp (C.parties.mapM fun l => if SharesHidden D j l then hashQuery (sharedAddress j l x.1.2.1)
      else pure 0) (LocalSpec C) >>= fun _ => pure ()

theorem passTwo_split (j : C.Party) (k : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))) :
    RunEq (compLocal prims D parts seed) (passTwo j k >>= fun r => pure (r.map (zeroShared D j)))
      (passTwoList D j k >>= fun r => discOne D j r >>= fun _ => pure r) := by
  rcases k with _ | keys
  · refine RunEq.of_eq ?_
    simp [passTwo, passTwoList, discOne]
  · have h := mapM_split prims D parts seed (SharesHidden D j) (fun l => sharedAddress j l keys.2.1) C.parties
      (fun sh => pure (some (keys, sh)))
    simp only [passTwo, passTwoList, discOne, seedGen_liftComp_mapM, bind_assoc, pure_bind, Option.map_some, zeroShared]
    exact h

/-- `BlockLaw` holds. -/
theorem blockLaw {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] :
    BlockLaw (C := C) (E := E) prims := by
  intro D parts seed committed d sent c
  have e1 : (fun r => (zeroD D r.1, r.2)) <$> (simulateQ (compLocal prims D parts seed)
      (localBlock D parts committed d sent)).run c =
      (simulateQ (compLocal prims D parts seed) (OverPermutation.sequenceFin fun j =>
        (passOne D parts committed d sent j >>= passTwo j) >>= fun r => pure (r.map (zeroShared D j)))).run c := by
    rw [sequenceFin_bind_pure, simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [e1]
  have h1 : RunEq (compLocal prims D parts seed)
      (OverPermutation.sequenceFin fun j =>
        (passOne D parts committed d sent j >>= passTwo j) >>= fun r => pure (r.map (zeroShared D j)))
      (OverPermutation.sequenceFin fun j => passOne D parts committed d sent j >>= fun k =>
        passTwoList D j k >>= fun r => discOne D j r >>= fun _ => pure r) := by
    refine runEq_sequenceFin _ _ _ fun j => ?_
    rw [bind_assoc]
    exact RunEq.bind_right _ fun k => passTwo_split prims D parts seed j k
  have hs := runEq_sequenceFin_split (commutes_compLocal prims D parts seed)
    (fun j => passOne D parts committed d sent j >>= passTwoList D j) (fun j r => discOne D j r >>= fun _ => pure r)
  simp only [bind_assoc] at hs
  refine (h1.trans (hs.trans (RunEq.of_eq ?_))) c
  unfold localBlockList discards
  refine bind_congr fun ks => ?_
  rw [sequenceFin_bind_pure]
  simp only [bind_assoc, pure_bind]
  rfl

end Law

/-! ## `EchoCompare` -/

section Final

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The echo comparison `EchoCompare`. -/
theorem echoCompare : EchoCompare prims K circuits settings runLimit :=
  echoCompare_of_parts prims K circuits settings runLimit (echoPair_of_block prims (preInv prims) (blockBound prims))
    (midList_of_parts prims K circuits settings runLimit (blockLaw prims) (tailDrop prims))

end Final

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.blockLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.blockLaw

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.echoCompare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.echoCompare
