import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Forger

/-!
# The table of the forger moves into the world

`accepts_dkgReduction` shows that the forger `dkgReduction` wins `tsigGame` as often as
`forgerWorldGame` wins in `streamWorld`. `forgerWorldGame` runs the dealer first and then the code of
the forger with its table in the world.

`DealerFirst` states that `dealtGame` with each run emulated wins at most as often as
`forgerWorldGame`, two programs of the world. `tableHop_of_dealerFirst` gives `TableHop` from it.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem curryStreams_empty : curryStreams (C := C) ∅ = ∅ := QueryCache.ext fun _ => rfl

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- One dealt key. The forger in `tsigGame` and the forger in the world give the same result, from
a cache of the world and the same cache with no setup cell. -/
theorem forger_run {dealt : Dealt C (OracleComp (WorldSpec C))} (hdealt : SafeDealt dealt) (D : C.Coalition)
    (A : DkgTsigAdversary C E) (s : HashCache C) :
    Prod.fst <$> (simulateQ (streamWorld prims D) (do
        let ((forgery, _), st) ← ((bodyW K circuits settings runLimit D dealt A ⟨dealt.top.root, dealt.parameter⟩
          dealt.top).run []).run SigningCoreProof.tsigInit
        forgeryWins (fun oa => SigningCoreProof.honestLift oa) dealt st forgery)).run (SeedPartition.merge isSetupQuery s ∅, ∅) =
      (simulateQ (baseAnswer prims)
        ((·.1) <$> tsigGameWith worldRoles dealt (dkgReduction K circuits settings runLimit prims.aes D A))).run' s := by
  rw [game_eq, dkgReduction_eq]
  have hR : ∀ (f : (Forgery × TsigState C) → OracleComp (WorldSpec C) Bool),
      (simulateQ (baseAnswer prims) ((simulateQ (SigningCoreProof.gameOracles dealt)
        ((bodyR K circuits settings runLimit prims.aes D A ⟨dealt.top.root, dealt.parameter⟩ dealt.top).run'
          ⟨∅, ∅, []⟩)).run SigningCoreProof.tsigInit >>= f)).run' s =
        semR prims dealt (bodyR K circuits settings runLimit prims.aes D A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)
          ⟨∅, ∅, []⟩ SigningCoreProof.tsigInit s >>= fun w =>
            (simulateQ (baseAnswer prims) (f (w.1.1.1, w.1.2))).run' w.2 := by
    intro f
    simp [semR, StateT.run'_eq, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]
  have hW : ∀ (g : ((Forgery × CallLog C) × TsigState C) → OracleComp (WorldSpec C) Bool) c,
      Prod.fst <$> (simulateQ (streamWorld prims D) (((bodyW K circuits settings runLimit D dealt A
        ⟨dealt.top.root, dealt.parameter⟩ dealt.top).run []).run SigningCoreProof.tsigInit >>= g)).run c =
        semW prims D (bodyW K circuits settings runLimit D dealt A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)
          [] SigningCoreProof.tsigInit c >>= fun w =>
            Prod.fst <$> (simulateQ (streamWorld prims D) (g w.1)).run w.2 := by
    intro g c
    simp [semW, simulateQ_bind, StateT.run_bind]
  rw [hR, hW]
  have hc : (SeedPartition.merge isSetupQuery s ∅, (∅ : HiddenCache C)) = tableImage ⟨∅, ∅, []⟩ s := by
    simp [tableImage, curryStreams_empty]
  rw [hc, couple_body hdealt A _ _ ⟨∅, ∅, []⟩ SigningCoreProof.tsigInit s, bind_map_left]
  refine bind_congr fun z => ?_
  have hsafe : AllQueriesSatisfy (forgeryWins (fun oa => worldRoles.honest (liftComp oa (LocalSpec C))) dealt
      z.1.2 z.1.1.1) WorldSafe := forgeryWins_safe freeLift_safe hdealt _ _
  simp only [image, tableImage, SigningCoreProof.honestLift]
  rw [streamWorld_safe hsafe, Functor.map_map, simulate_frame prims hsafe, Functor.map_map, StateT.run'_eq]

/-- The forger `dkgReduction` wins `tsigGame` as often as `forgerWorldGame` wins in `streamWorld`. -/
theorem accepts_dkgReduction (D : C.Coalition) (A : DkgTsigAdversary C E) :
    accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) =
      streamAccepts prims D (forgerWorldGame K circuits settings runLimit D A) := by
  rw [accepts_eq]
  unfold streamAccepts
  have hdealer : (simulateQ (baseAnswer prims) (dealerKeyGen (C := C))).run ∅ =
      (fun z => (z.1, SeedPartition.merge isSetupQuery z.2 ∅)) <$> (simulateQ (baseAnswer prims) (dealerKeyGen (C := C))).run ∅ := by
    conv_lhs => rw [← SeedPartition.merge_empty isSetupQuery]
    exact simulate_frame prims dealerKeyGen_safe ∅ ∅
  have key : Prod.fst <$> (simulateQ (streamWorld prims D) (forgerWorldGame K circuits settings runLimit D A)).run
      (∅, ∅) =ᵈ (simulateQ (baseAnswer prims) (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A))).run' ∅ := by
    unfold forgerWorldGame tsigGame
    rw [simulateQ_bind, StateT.run_bind, streamWorld_safe dealerKeyGen_safe, hdealer, run'_bind, Functor.map_map,
      bind_map_left, map_bind]
    refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
    obtain ⟨output, c⟩ := z
    have hmem : output ∈ support (dealerKeyGen (C := C)) := by
      refine support_simulateQ_run'_subset (baseAnswer prims) _ ∅ ?_
      rw [StateT.run'_eq, support_map]
      exact ⟨_, hz, rfl⟩
    cases output with
    | none => simp
    | some dealt =>
      have hdealt := dealerKeyGen_support _ hmem dealt rfl
      dsimp only
      rw [forger_run prims K circuits settings runLimit hdealt D A c]
  refine congrArg ENNReal.toReal ?_
  rw [← key.prEvent_eq]
  simp

/-- `dealtGame` with each run emulated wins at most as often as `forgerWorldGame`. Both are programs
of the world. They differ in the place of the dealer, in the
recomputation of the dealer in each emulated run, in the log of the calls of `A`, in the keys of the
start state, and in the branch with no top holder. -/
def DealerFirst : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) ≤
      streamAccepts prims D (forgerWorldGame K circuits settings runLimit D A)

/-- `TableHop` from `DealerFirst`. -/
theorem tableHop_of_dealerFirst (h : DealerFirst prims K circuits settings runLimit) :
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
      streamAccepts prims D (dealtGame K circuits settings runLimit ⟨true, fun _ => runLimit⟩ D A) ≤
        accepts prims (tsigGame (dkgReduction K circuits settings runLimit prims.aes D A)) := fun D A => by
  rw [accepts_dkgReduction]
  exact h D A

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.accepts_dkgReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.accepts_dkgReduction

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop_of_dealerFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.tableHop_of_dealerFirst
