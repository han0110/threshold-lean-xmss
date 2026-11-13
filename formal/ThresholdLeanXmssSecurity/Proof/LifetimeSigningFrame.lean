import ThresholdLeanXmssSecurity.Proof.LifetimePrecomputeSwap

/-! # Keygen-domain frames for the actual external signing operations

The zero-query signing construction is ported from LifetimeTailDriver's
setupQuiet lemmas with RoKeygen in place of the PRSS-setup predicate.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeSigningFrame
open LifetimeIdealBad LifetimePrecomputeSwap
attribute [local instance] Classical.propDecidable
variable {C : Committee}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem hash_noKeygen (q : Query C) (hq : ¬ RoKeygen (.inl q)) :
    IsQueryBoundP (hashQuery q) RoKeygen 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h hq

theorem prfValue_noKeygen (seeds : C.Term → HashOutput) (x : Point) :
    IsQueryBoundP (prfValue seeds x) RoKeygen 0 := by
  unfold prfValue
  apply zero_bind RoKeygen (zero_mapM _ _ _ fun _ => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  exact (isQueryBoundP_map_iff _ _ _).2 (hash_noKeygen _ id)

theorem eval_noKeygen (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    IsQueryBoundP (eval keys i J x message) RoKeygen 0 := by
  unfold eval
  refine zero_bind RoKeygen (zero_mapM _ _ _ fun _ => ?_) fun _ _ => ?_
  · exact (isQueryBoundP_map_iff _ _ _).2 (hash_noKeygen _ id)
  exact zero_bind RoKeygen (zero_mapM _ _ _ fun _ =>
    (isQueryBoundP_map_iff _ _ _).2 (hash_noKeygen _ id)) fun _ _ => isQueryBoundP_pure _ _ _

section Signing

variable {ι : Type} {spec : OracleSpec ι} (P : ι → Prop)
variable (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp spec α)
variable (hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
  IsQueryBoundP p RoKeygen 0 → IsQueryBoundP (lift p) P 0)

include hlift

theorem signRound2With_noKeygen (part : Point → OracleComp spec Digest)
    (hp : ∀ x, IsQueryBoundP (part x) P 0) (parameter : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    IsQueryBoundP (signRound2With lift part parameter J commitment e message parts) P 0 := by
  unfold signRound2With
  apply zero_bind P (hlift _ (tweakable_noKeygen _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (zero_sequenceFin _ _ fun l => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  split
  · exact (isQueryBoundP_map_iff _ _ _).2 (hp _)
  · exact isQueryBoundP_pure _ _ _

theorem referenceJob_noKeygen (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (job : Job) :
    IsQueryBoundP (referenceJob (fun p => lift (tweakable p)) value parameter job) P 0 := by
  unfold referenceJob
  apply zero_bind P (zero_mapM _ _ _ hv)
  intro values _
  cases job.kind with
  | chainEnd key l => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_noKeygen _))
  | chainRow key l =>
    exact zero_bind P (hlift _ (tweakable_noKeygen _)) fun _ _ =>
      zero_bind P (hlift _ (tweakable_noKeygen _)) fun _ _ =>
        zero_bind P (hlift _ (tweakable_noKeygen _)) fun _ _ => isQueryBoundP_pure _ _ _
  | chainValue key l p => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_noKeygen _))
  | commitment key => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_noKeygen _))
  | randomizer => exact isQueryBoundP_pure _ _ _

theorem referenceTree_noKeygen (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    IsQueryBoundP (referenceTree (fun p => lift (tweakable p)) value parameter top tree) P 0 :=
  ceremonyOutput_quiet P _ (fun p => hlift _ (tweakable_noKeygen p)) _
    (fun _js => (isQueryBoundP_map_iff _ _ _).2
      (zero_mapM _ _ _ fun job => referenceJob_noKeygen P lift hlift value hv parameter job))
    parameter top tree

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
theorem dealtWith_noKeygen (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → OracleComp spec Digest) (hv : ∀ x, IsQueryBoundP (value x) P 0) :
    DealtQuiet P (dealtWith lift parameter keys top value) := by
  refine ⟨hv, fun i J x message => hlift _ (eval_noKeygen _ _ _ _ _), fun b => ?_⟩
  change IsQueryBoundP (_ <$> referenceTree (fun p => lift (tweakable p)) value parameter top (.bottom b)) P 0
  with_reducible exact ((isQueryBoundP_map_iff _ _ _).2
    (referenceTree_noKeygen P lift hlift value hv parameter top (.bottom b)))

theorem honestSignature_noKeygen (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (e : KeyIndex) (message : Message) : IsQueryBoundP (honestSignature lift dealt e message) P 0 := by
  unfold honestSignature
  apply zero_bind P (hd.bottom _)
  rintro (_ | tree) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (hd.value _)
  intro rho _
  apply zero_bind P (hlift _ (tweakable_noKeygen _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  refine zero_bind P (zero_sequenceFin _ _ fun l => ?_) (fun values _ => ?_)
  · split
    · exact hd.value _
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  · exact zero_bind P (hlift _ (tweakable_noKeygen _)) fun _ _ => isQueryBoundP_pure _ _ _

theorem forgeryWins_noKeygen (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (st : TsigState C) (forgery : Forgery) : IsQueryBoundP (forgeryWins lift dealt st forgery) P 0 := by
  unfold forgeryWins
  apply zero_bind P (hlift _ (tweakable_noKeygen _))
  intro verified _
  split
  · exact isQueryBoundP_pure _ _ _
  · exact zero_bind P (honestSignature_noKeygen P lift hlift dealt hd _ _) fun _ _ =>
      isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- One signing oracle step asks no `P` query, when the dealt values and `lift` ask none. -/
theorem tsig_noKeygen (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (q : (TsigSpec C).Domain) (st : TsigState C) :
    IsQueryBoundP ((tsigOracles lift dealt q).run st) P 0 := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
      exact isQueryBoundP_pure _ _ _
  | tree b =>
    simp only [tsigOracles, StateT.run_bind]
    apply zero_bind P (bottomOnce_quiet P dealt hd _ st)
    rintro ⟨_ | tree, st'⟩ _
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, run_liftM, bind_map_left, StateT.run_pure]
      exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map, run_liftM, Functor.map_map]
      exact (isQueryBoundP_map_iff _ _ _).2 (hd.part _ _ _ _)
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · apply zero_bind P (bottomOnce_quiet P dealt hd _ st)
      rintro ⟨_ | tree, st'⟩ _
      · exact isQueryBoundP_pure _ _ _
      · change IsQueryBoundP (StateT.run _ st') P 0
        simp only [StateT.run_bind, run_liftM, bind_map_left]
        apply zero_bind P (hd.part _ _ _ _)
        intro own _
        apply zero_bind P (signRound2With_noKeygen P lift hlift _ (hd.part i J · message) _ _ _ _ _ _)
        rintro (_ | values) _
        · exact isQueryBoundP_pure _ _ _
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact isQueryBoundP_pure _ _ _

end Signing
/-- The world simulation of a separated free program frames the private domain. -/
theorem frames_dealerProgram (prims : Primitives) {α : Type}
    (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p (fun t => ¬ DealerQuery t) 0) :
    Frames (fun q => ¬ KeygenPoint q) (simulateQ (worldAnswer prims) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using frames_pure (fun q => ¬ KeygenPoint q) a
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : DealerQuery t := Classical.not_not.mp (safe.1.resolve_right (by omega))
    simp only [simulateQ_bind, simulateQ_spec_query]
    apply frames_bind
    · rcases t with (t | x) | t
      · simp [DealerQuery] at ht
      · simp [DealerQuery] at ht
      · rcases t with u | (q | x)
        · exact frames_lift _ _
        · exact frames_hashAnswer prims ht
        · exact frames_prgAnswer prims x
    · intro a
      apply ih a
      simpa only [ht, not_true_eq_false, if_false] using safe.2 a

def worldRo {α : Type} (p : OracleComp (RoSpec C) α) : OracleComp (WorldSpec C) α :=
  free (liftComp p (LocalSpec C))

def fixedDealt (d : LifetimeBridge.Dealing C) (top : TopTree) :
    Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith worldRo d.1 d.2.2 top (fun x => worldRo (prfValue d.2.1 x))

/-- Actual fixed-dealing operations read no programmed keygen input. -/
theorem fixedDealt_quiet (d : LifetimeBridge.Dealing C) (top : TopTree) :
    DealtQuiet (fun t => ¬ DealerQuery t) (fixedDealt d top) :=
  dealtWith_noKeygen (fun t => ¬ DealerQuery t) worldRo (fun p hp => by
      convert free_ro_dealerQuery p hp using 1; rfl) _ _ _ _
    (fun x => by
      convert free_ro_dealerQuery _ (prfValue_noKeygen d.2.1 x) using 1; rfl)

/-- The full external signing result, including its state, frames keygen points. -/
theorem signing_frame (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (q : (TsigSpec C).Domain) (st : TsigState C) :
    Frames (fun q => ¬ KeygenPoint q)
      (simulateQ (worldAnswer prims) ((tsigOracles worldRo (fixedDealt d top) q).run st)) :=
  frames_dealerProgram prims _ (by
    convert (tsig_noKeygen (fun t => ¬ DealerQuery t) worldRo (fun p hp => by
      convert free_ro_dealerQuery p hp using 1; rfl)
      _ (fixedDealt_quiet d top) q st) using 1)

/-- The actual strong-forgery test also frames keygen points. -/
theorem finish_frame (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (st : TsigState C) (f : Forgery) :
    Frames (fun q => ¬ KeygenPoint q)
      (simulateQ (worldAnswer prims) (forgeryWins worldRo (fixedDealt d top) st f)) :=
  frames_dealerProgram prims _ (by
    convert (forgeryWins_noKeygen (fun t => ¬ DealerQuery t) worldRo (fun p hp => by
      convert free_ro_dealerQuery p hp using 1; rfl)
      _ (fixedDealt_quiet d top) st f) using 1)

end ThresholdLeanXmssSecurity.LifetimeSigningFrame

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.hash_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.hash_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.prfValue_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.prfValue_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.eval_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.eval_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.signRound2With_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.signRound2With_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.referenceJob_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.referenceJob_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.referenceTree_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.referenceTree_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.dealtWith_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.dealtWith_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.honestSignature_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.honestSignature_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.forgeryWins_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.forgeryWins_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.tsig_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.tsig_noKeygen

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.frames_dealerProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.frames_dealerProgram

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.fixedDealt_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.fixedDealt_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.signing_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.signing_frame

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSigningFrame.finish_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeSigningFrame.finish_frame
