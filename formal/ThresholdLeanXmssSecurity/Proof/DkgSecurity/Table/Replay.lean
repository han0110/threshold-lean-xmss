import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Pieces
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk

/-!
# The replay stage

`replayStage` proves `ReplayStage`. After the first run of the top tree of the dealer each later
`worldDealer` gives the same dealer and changes no state (`worldDealer_replay`), because the cache
only grows. `RunEqW c0` relates two computations that give the same law from each state whose cache
holds `c0`, and `RunEqR`, `RunEq2` are the same on the real state and on the state of the signing game.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-! ## The relation -/

/-- Two computations of the world with the same law from each state whose cache holds `c0`. -/
def RunEqW (c0 : HashCache C) {α : Type} (x y : OracleComp (WorldSpec C) α) : Prop :=
  ∀ w : HashCache C × HiddenCache C, c0 ≤ w.1 →
    (simulateQ (streamWorld prims D) x).run w =ᵈ (simulateQ (streamWorld prims D) y).run w

/-- `RunEqW` from each real state. -/
def RunEqR (c0 : HashCache C) {σ α : Type} (x y : RealM C σ α) : Prop :=
  ∀ rs, RunEqW prims D c0 (x.run rs) (y.run rs)

/-- `RunEqR` from each state of the signing game. -/
def RunEq2 (c0 : HashCache C) {σ α : Type} (x y : StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ st, RunEqR prims D c0 (x.run st) (y.run st)

variable {prims D} {c0 : HashCache C}

theorem RunEqW.refl {α : Type} (x : OracleComp (WorldSpec C) α) : RunEqW prims D c0 x x := fun _ _ => .rfl

theorem RunEqW.bind {α β : Type} {x y : OracleComp (WorldSpec C) α} {f g : α → OracleComp (WorldSpec C) β}
    (h : RunEqW prims D c0 x y) (hfg : ∀ a, RunEqW prims D c0 (f a) (g a)) :
    RunEqW prims D c0 (x >>= f) (y >>= g) := fun w hw => by
  simp only [simulateQ_bind, StateT.run_bind]
  refine ((h w hw).bind_left _).trans ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  exact hfg z.1 z.2 (hw.trans (streamWorld_run_mono prims D y w z hz))

theorem RunEqR.refl {σ α : Type} (x : RealM C σ α) : RunEqR prims D c0 x x := fun _ => RunEqW.refl _

theorem RunEqR.bind {σ α β : Type} {x y : RealM C σ α} {f g : α → RealM C σ β}
    (h : RunEqR prims D c0 x y) (hfg : ∀ a, RunEqR prims D c0 (f a) (g a)) :
    RunEqR prims D c0 (x >>= f) (y >>= g) := fun rs => by
  simp only [StateT.run_bind]
  exact (h rs).bind fun p => hfg p.1 p.2

theorem RunEqR.trans {σ α : Type} {x y z : RealM C σ α} (h : RunEqR prims D c0 x y) (h' : RunEqR prims D c0 y z) :
    RunEqR prims D c0 x z := fun rs w hw => (h rs w hw).trans (h' rs w hw)

theorem RunEq2.refl {σ α : Type} (x : StateT (TsigState C) (RealM C σ) α) : RunEq2 prims D c0 x x :=
  fun _ => RunEqR.refl _

theorem RunEq2.bind {σ α β : Type} {x y : StateT (TsigState C) (RealM C σ) α}
    {f g : α → StateT (TsigState C) (RealM C σ) β}
    (h : RunEq2 prims D c0 x y) (hfg : ∀ a, RunEq2 prims D c0 (f a) (g a)) :
    RunEq2 prims D c0 (x >>= f) (y >>= g) := fun st => by
  simp only [StateT.run_bind]
  exact (h st).bind fun p => hfg p.1 p.2

theorem RunEq2.lift {σ α : Type} {x y : RealM C σ α} (h : RunEqR prims D c0 x y) :
    RunEq2 prims D c0 (StateT.lift x) (StateT.lift y) := fun st => by
  simp only [StateT.run_lift]
  exact h.bind fun a => RunEqR.refl _

theorem RunEq2.simulateQ {σ ι : Type} {spec : OracleSpec ι}
    {implL implR : QueryImpl spec (StateT (TsigState C) (RealM C σ))}
    (h : ∀ t, RunEq2 prims D c0 (implL t) (implR t)) {α : Type} (oa : OracleComp spec α) :
    RunEq2 prims D c0 (simulateQ implL oa) (simulateQ implR oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using RunEq2.refl (pure a)
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (h t).bind ih

/-! ## The code with the dealer given -/

section Code

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (runLimit : ℕ) (m : Mode) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
  (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))

/-- `worldDealer` gives `dealer` and changes no state from each state whose cache holds `c0`. -/
def DealerReplays (σ : Type) (dealer : Dealt C (RealM C σ)) : Prop :=
  ∀ (rs : RealState C σ) (w : HashCache C × HiddenCache C), c0 ≤ w.1 →
    (simulateQ (streamWorld prims D) ((worldDealer (σ := σ) parameter seeds dealt).run rs)).run w =
      pure ((dealer, rs), w)

variable {parameter seeds dealt}

theorem runEqR_worldDealer {σ α : Type} {dealer : Dealt C (RealM C σ)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt σ dealer) (k : Dealt C (RealM C σ) → RealM C σ α) :
    RunEqR prims D c0 (worldDealer parameter seeds dealt >>= k) (k dealer) := fun rs w hw => by
  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hrep rs w hw, pure_bind]

theorem secRun_replay (net : Adversary C E Unit PEmpty PEmpty) {dealer : Dealt C (RealM C net.State)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt net.State dealer) (tree : Tree) :
    RunEqR prims D c0 (secRun K circuits settings m D net parameter seeds dealt emu tree)
      (secRunD K circuits settings D m net dealer emu tree) := by
  unfold secRun secRunD
  refine RunEqR.bind (RunEqR.refl get) fun st => ?_
  split
  · exact runEqR_worldDealer hrep _
  · exact RunEqR.refl _

theorem secRuns_replay (net : Adversary C E Unit PEmpty PEmpty) {dealer : Dealt C (RealM C net.State)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt net.State dealer) (tree : Tree) :
    ∀ count, RunEqR prims D c0 (secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count)
      (secRunsD K circuits settings runLimit D m net dealer emu tree count)
  | 0 => RunEqR.refl _
  | count + 1 => by
    simp only [secRuns, secRunsD]
    refine RunEqR.bind (RunEqR.refl get) fun st => ?_
    split
    · exact (secRun_replay K circuits settings m emu net hrep tree).bind fun _ =>
        secRuns_replay net hrep tree count
    · exact RunEqR.refl _

theorem secTreeRequest_replay (net : Adversary C E Unit PEmpty PEmpty) {dealer : Dealt C (RealM C net.State)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt net.State dealer)
    (b : Fin (2 ^ layerHeight)) :
    RunEq2 prims D c0 (secTreeRequest K circuits settings runLimit m D net parameter seeds dealt emu dealer b)
      (secTreeRequestD K circuits settings runLimit D m net dealer emu b) := by
  unfold secTreeRequest secTreeRequestD
  refine RunEq2.bind (RunEq2.refl _) fun answer => ?_
  split
  · exact (RunEq2.lift (secRuns_replay K circuits settings runLimit m emu net hrep _ 1)).bind fun _ =>
      RunEq2.refl _
  · exact RunEq2.refl _

theorem secOracles_replay (net : Adversary C E Unit PEmpty PEmpty) {dealer : Dealt C (RealM C net.State)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt net.State dealer)
    (q : TsigQuery C) :
    RunEq2 prims D c0 (secOracles K circuits settings runLimit m D net parameter seeds dealt emu dealer q)
      (secOraclesD K circuits settings runLimit D m net dealer emu q) := by
  cases q with
  | tree b => exact secTreeRequest_replay K circuits settings runLimit m emu net hrep b
  | _ => exact RunEq2.refl _

theorem secSigning_replay (A : DkgTsigAdversary C E) {dealer : Dealt C (RealM C A.net.State)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt A.net.State dealer) :
    RunEqR prims D c0 (secSigning K circuits settings runLimit m D A parameter seeds dealt emu)
      (secSigningD K circuits settings runLimit D m A dealer emu) := by
  unfold secSigning secSigningD
  refine RunEqR.bind (RunEqR.refl get) fun st => ?_
  rcases topHolder D st.operators with _ | holder
  · exact RunEqR.refl _
  · refine (runEqR_worldDealer hrep _).trans ?_
    dsimp only
    refine RunEqR.bind (RunEq2.simulateQ (fun t => ?_) _ _) fun _ => RunEqR.refl _
    rcases t with t | q | q
    · simp only [QueryImpl.add_apply_inl]
      exact RunEq2.refl _
    · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact secOracles_replay K circuits settings runLimit m emu A.net hrep q
    · simp only [QueryImpl.add_apply_inr]
      exact RunEq2.refl _

theorem secRest_replay (A : DkgTsigAdversary C E) {dealer : Dealt C (RealM C A.net.State)}
    (hrep : DealerReplays (prims := prims) (D := D) (c0 := c0) parameter seeds dealt A.net.State dealer) :
    RunEqR prims D c0 (secRest K circuits settings runLimit m D A parameter seeds dealt emu)
      (secRestD K circuits settings runLimit D m A dealer emu) := by
  unfold secRest secRestD
  refine RunEqR.bind (RunEqR.refl get) fun st => RunEqR.bind (RunEqR.refl _) fun v => ?_
  obtain ⟨state, ok⟩ := v
  exact RunEqR.bind (RunEqR.refl _) fun _ =>
    (secRuns_replay K circuits settings runLimit m (committed ok emu) A.net hrep .top runLimit).bind fun _ =>
      secSigning_replay K circuits settings runLimit m (committed ok emu) A hrep

end Code

/-! ## The stage -/

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (runLimit : ℕ)

theorem dealerReplays_of_support {σ : Type} (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
    (w : HashCache C × HiddenCache C) (z : Option TreeOutput × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (dealerTop r.1 r.2.1)).run w)) :
    DealerReplays (prims := prims) (D := D) (c0 := z.2.1) r.1 r.2.1 r.2.2 σ (dealerOf r z.1) :=
  fun rs w' hw' => worldDealer_replay prims D r.1 r.2.1 r.2.2 w z hz w' hw' rs

theorem worldRun_bind_run {α β : Type} {x : OracleComp (WorldSpec C) α} {f g : α → OracleComp (WorldSpec C) β}
    (h : ∀ w z, z ∈ support ((simulateQ (streamWorld prims D) x).run w) →
      (simulateQ (streamWorld prims D) (f z.1)).run z.2 =ᵈ (simulateQ (streamWorld prims D) (g z.1)).run z.2) :
    WorldRun (streamWorld prims D) (x >>= f) (x >>= g) := fun w => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => h w z hz

theorem replayStage : ReplayStage K circuits settings runLimit prims := fun _ D A => by
  unfold streamAccepts
  suffices h : WorldRun (streamWorld prims D) (dealerFirstGame K circuits settings runLimit D A)
      (givenDealerGame K circuits settings runLimit D A) by
    rw [(h (∅, ∅)).prEvent_eq]
  refine WorldRun.bind_right _ _ fun r => ?_
  refine worldRun_bind_run fun w z hz => ?_
  have hrep := dealerReplays_of_support (prims := prims) (D := D) (σ := A.net.State) r w z hz
  refine RunEqW.bind (RunEqW.refl _) (fun o => ?_) z.2 le_rfl
  unfold dealtTail
  refine RunEqW.bind (RunEqW.refl _) fun te => ?_
  rw [StateT.run'_eq, StateT.run'_eq, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact (secRest_replay K circuits settings runLimit _ te.2 A hrep _).bind fun _ => RunEqW.refl _

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.replayStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.replayStage

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)
  (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- `TableHop` from `StructureStage`. -/
theorem tableHop_of_structureStage (h : StructureStage K circuits settings runLimit prims) :
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
      streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) ≤
        accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) :=
  tableHop_of_dealerFirstForger prims K circuits settings runLimit
    (dealerFirstForger_of_stages K circuits settings runLimit prims
      (replayStage (prims := prims) K circuits settings runLimit) h)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop_of_structureStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop_of_structureStage
