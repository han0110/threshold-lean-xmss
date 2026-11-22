import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Steps

/-!
# The forger on its table and in the world

`couple_body` couples the body of `dkgReduction` with `bodyW` part by part. The parts are the
network through `mapRoles` (`couple_executePhase`), the seed generation (`couple_seedGen`), the runs
of a tree (`coupleS_emulatedRuns`) and the oracles of `forge` (`coupleS_forgeOracles`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The network -/

/-- The two roles as two copies of the local oracles. -/
def splitRoles : Roles C (OracleComp (LocalSpec C + LocalSpec C)) :=
  ⟨fun oa => simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C + LocalSpec C) (.inl t))) oa,
    fun oa => simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C + LocalSpec C) (.inr t))) oa⟩

theorem reductionRoles_eq (aes : Aes) (D : C.Coalition) :
    reductionRoles aes D = mapRoles (adversaryCall (C := C) aes + honestCall aes D) splitRoles := by
  unfold reductionRoles mapRoles splitRoles
  congr 1 <;> funext β oa <;>
    exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp) oa).symm

theorem forgerWorldRoles_eq :
    forgerWorldRoles (C := C) = mapRoles (worldAdversaryCall (C := C) + worldHonestCall (C := C)) splitRoles := by
  unfold forgerWorldRoles mapRoles splitRoles
  congr 1 <;> funext β oa <;>
    exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp) oa).symm

variable {prims : Primitives} {D : C.Coalition} {dealt : Dealt C (OracleComp (WorldSpec C))}

theorem couple_split (t : (LocalSpec C + LocalSpec C).Domain) :
    Couple prims D dealt ((adversaryCall (C := C) prims.aes + honestCall prims.aes D) t)
      ((worldAdversaryCall (C := C) + worldHonestCall (C := C)) t) := by
  rcases t with t | t
  · exact couple_adversaryCall t
  · exact couple_honestCall t

section Network

variable {I O L R Ia α : Type} (A : Adversary C E Ia L R) (F : Functionality C I O L R)

theorem couple_startSteps (program : C.Party → PartyM C E (CallSpec I O) α) :
    Couple prims D dealt (startSteps (reductionRoles prims.aes D) D program) (startSteps forgerWorldRoles D program) := by
  rw [reductionRoles_eq, forgerWorldRoles_eq, ← simulateQ_startSteps, ← simulateQ_startSteps]
  exact Couple.simulateQ couple_split _

theorem couple_stepRound (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    Couple prims D dealt (stepRound (reductionRoles prims.aes D) D A F state steps)
      (stepRound forgerWorldRoles D A F state steps) := by
  rw [reductionRoles_eq, forgerWorldRoles_eq, ← simulateQ_stepRound_mapRoles, ← simulateQ_stepRound_mapRoles]
  exact Couple.simulateQ couple_split _

theorem couple_executeRounds (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    Couple prims D dealt (executeRounds (reductionRoles prims.aes D) D A F fuel state steps)
      (executeRounds forgerWorldRoles D A F fuel state steps) := by
  rw [reductionRoles_eq, forgerWorldRoles_eq, ← simulateQ_executeRounds_mapRoles,
    ← simulateQ_executeRounds_mapRoles]
  exact Couple.simulateQ couple_split _

theorem couple_executePhase (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α) :
    Couple prims D dealt (executePhase (reductionRoles prims.aes D) D A F fuel state program)
      (executePhase forgerWorldRoles D A F fuel state program) := by
  rw [reductionRoles_eq, forgerWorldRoles_eq, ← simulateQ_executePhase_mapRoles,
    ← simulateQ_executePhase_mapRoles]
  exact Couple.simulateQ couple_split _

end Network

/-- A read of the log of the setup calls. -/
theorem Couple.get_bind {β : Type} {f : TableState C → TableM C β} {g : CallLog C → WorldM C β}
    (h : ∀ ts, Couple prims D dealt (f ts) (g ts.log)) :
    Couple prims D dealt (get >>= f) (get >>= g) := by
  intro ts st s
  have e₁ : semR prims dealt (get >>= f) ts st s = semR prims dealt (f ts) ts st s := by
    simp [semR, StateT.run_bind]
  have e₂ : semW prims D (get >>= g) ts.log st (tableImage ts s) =
      semW prims D (g ts.log) ts.log st (tableImage ts s) := by
    simp [semW, StateT.run_bind]
  rw [e₁, e₂]
  exact h ts ts st s

/-! ## The seed generation -/

theorem couple_seedGen (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C))
    (net : Adversary C E Unit PEmpty PEmpty) :
    Couple prims D dealt (seedGenEmulation prims.aes D parameter corrupt net) (seedGenWorld D parameter corrupt net) := by
  unfold seedGenEmulation seedGenWorld
  refine (Couple.simulateQ couple_adversaryCall _).bind fun state => ?_
  refine (Couple.simulateQ couple_honestCall _).bind fun parts => ?_
  refine (couple_startSteps _).bind fun steps => ?_
  refine (couple_stepRound _ _ _ _).bind fun r => ?_
  obtain ⟨state, steps, sent⟩ := r
  refine Couple.get_bind fun ts => ?_
  refine (Couple.simulateQ couple_honestCall _).bind fun high => ?_
  refine (couple_writeTable ?_ _).bind fun _ => ?_
  · rfl
  refine (Couple.forIn _ _ fun T r => ?_).bind fun _ => ?_
  · split
    next j heq =>
      simp only [heq]
      refine (couple_writeTable ?_ _).bind fun _ => Couple.pure _
      rfl
    next heq =>
      simp only [heq]
      exact Couple.pure _
  refine (Couple.forIn _ _ fun j r => ?_).bind fun _ => ?_
  · refine (Couple.forIn _ _ fun i r' => ?_).bind fun _ => Couple.pure _
    split
    · refine (couple_writeTable ?_ _).bind fun _ => Couple.pure _
      rfl
    · exact Couple.pure _
  exact couple_executeRounds _ _ _ _ _

/-! ## The runs and the oracles of `forge` -/

variable [Field E] [Algebra Bit E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

theorem coupleS_emulatedRun (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) :
    CoupleS prims D dealt (emulatedRun K circuits settings prims.aes D net openings randomizer tree)
      (emulatedRunW K circuits settings D net openings randomizer tree) := by
  unfold emulatedRun emulatedRunW
  refine CoupleS.get.bind fun s => ?_
  refine (CoupleS.lift (couple_executePhase _ _ _ _ _)).bind fun r => ?_
  exact CoupleS.set _

theorem coupleS_emulatedRuns (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) : ∀ count : ℕ,
    CoupleS prims D dealt (emulatedRuns K circuits settings runLimit prims.aes D net openings randomizer tree count)
      (emulatedRunsW K circuits settings runLimit D net openings randomizer tree count)
  | 0 => CoupleS.pure _
  | count + 1 => by
    simp only [emulatedRuns, emulatedRunsW]
    refine CoupleS.get.bind fun s => ?_
    split
    · exact (coupleS_emulatedRun K circuits settings net openings randomizer tree).bind fun _ =>
        coupleS_emulatedRuns net openings randomizer tree count
    · exact CoupleS.pure _

variable {K circuits settings runLimit}

theorem coupleS_emulatedTreeRequest (hdealt : SafeDealt dealt) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) :
    CoupleS prims D dealt (emulatedTreeRequest K circuits settings runLimit prims.aes D net b)
      (emulatedTreeRequestW K circuits settings runLimit D dealt net b) := by
  unfold emulatedTreeRequest emulatedTreeRequestW
  refine (CoupleS.lift (couple_tsigCall hdealt _)).bind fun answer => ?_
  rcases answer with _ | ⟨tree, ρ⟩ <;> dsimp only
  · refine CoupleS.get.bind fun s => ?_
    generalize heldBottom D s.operators b = held
    cases held <;> exact CoupleS.pure _
  · refine (coupleS_emulatedRuns K circuits settings runLimit _ _ _ _ 1).bind fun _ => CoupleS.get.bind fun s => ?_
    generalize heldBottom D s.operators b = held
    cases held <;> exact CoupleS.pure _

theorem coupleS_emulatedSignRequest (hdealt : SafeDealt dealt) {σ : Type} (i : C.Party) (e : KeyIndex)
    (q : TsigQuery C) :
    CoupleS prims D dealt (emulatedSignRequest (σ := σ) i e q) (emulatedSignRequestW dealt i e q) := by
  unfold emulatedSignRequest emulatedSignRequestW
  refine (CoupleS.modify _).bind fun _ => CoupleS.get.bind fun s => ?_
  generalize (s.operators i).keys = k
  generalize (s.operators i).top = tp
  generalize (s.operators i).bottom (treeOf e) = bt
  rcases k with _ | _ <;> rcases tp with _ | _ <;> rcases bt with _ | _ <;>
    first | exact CoupleS.pure _ | exact CoupleS.lift (couple_tsigCall hdealt q)

theorem coupleS_forgeOracles (hdealt : SafeDealt dealt) (net : Adversary C E Unit PEmpty PEmpty)
    (t : (LocalSpec C + (TsigSpec C + StateSpec net.State)).Domain) :
    CoupleS prims D dealt (forgeOracles K circuits settings runLimit prims.aes D net t)
      (forgeOraclesW K circuits settings runLimit D dealt net t) := by
  rcases t with t | q | q
  · exact CoupleS.lift (couple_adversaryCall t)
  · cases q with
    | corrupt i => exact CoupleS.pure _
    | tree b => exact coupleS_emulatedTreeRequest hdealt net b
    | round1 i J e message => exact coupleS_emulatedSignRequest hdealt i e _
    | round2 i J e message parts => exact coupleS_emulatedSignRequest hdealt i e _
  · cases q with
    | read => exact CoupleS.get.map _
    | write state => exact CoupleS.modify _

/-- The body of `dkgReduction` on its table and `bodyW` give the same run. -/
theorem couple_body (hdealt : SafeDealt dealt) (A : DkgTsigAdversary C E) (pk : PublicKey) (top : TopTree) :
    Couple prims D dealt (bodyR K circuits settings runLimit prims.aes D A pk top)
      (bodyW K circuits settings runLimit D dealt A pk top) := by
  unfold bodyR bodyW
  refine (Couple.sequenceFin fun i => ?_).bind fun corrupt => ?_
  · by_cases h : i ∈ D.1
    · simp only [h, ↓reduceIte]
      exact couple_tsigCall hdealt _
    · simp only [h, ↓reduceIte]
      exact Couple.pure _
  refine (couple_seedGen _ _ _).bind fun r => ?_
  obtain ⟨state, keys⟩ := r
  refine CoupleS.run' ?_ _
  refine (coupleS_emulatedRuns K circuits settings runLimit _ _ _ _ _).bind fun _ => CoupleS.get.bind fun s => ?_
  generalize topHolder D s.operators = holder
  cases holder
  · exact CoupleS.pure _
  · exact CoupleS.simulateQ (coupleS_forgeOracles hdealt _) _

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.couple_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.couple_body
