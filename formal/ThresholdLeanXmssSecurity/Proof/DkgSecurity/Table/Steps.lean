import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Coupling
import ThresholdLeanXmssSecurity.Proof.PrssRealRand

/-!
# One operation of the forger against the world

The operations of the forger on its table and their counterparts in the world give the same run.

* `couple_adversaryCall` is a call of `A`.
* `couple_honestCall` is a call of an emulated operator.
* `couple_writeTable` is a write of a cell in a setup domain.
* `couple_tsigCall` is a query to the signing oracles, for a dealer with only `WorldSafe` queries.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {prims : Primitives} {D : C.Coalition} {dealt : Dealt C (OracleComp (WorldSpec C))}

/-! ## The runs of the parts -/

theorem semR_forwardLocal (t : (LocalSpec C).Domain) (ts : TableState C) (st : TsigState C) (s : HashCache C) :
    semR prims dealt (forward (.inl t)) ts st s =
      (fun z => (((z.1, ts), st), z.2)) <$> (localAnswer prims t).run s := by
  simp only [semR, forward, StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [gameOracles_local]
  simp

theorem semR_forwardTsig (q : TsigQuery C) (ts : TableState C) (st : TsigState C) (s : HashCache C) :
    semR prims dealt (forward (.inr q)) ts st s =
      (fun z => (((z.1.1, ts), z.1.2), z.2)) <$>
        (simulateQ (baseAnswer prims) ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) dealt q).run st)).run s := by
  simp only [semR, forward, StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  simp [SigningCoreProof.gameOracles]

theorem semR_tableCall (x : (RoSpec C).Domain) (ts : TableState C) (st : TsigState C) (s : HashCache C) :
    semR prims dealt (tableCall prims.aes x) ts st s =
      (fun z => (((z.1, { ts with table := z.2 }), st), s)) <$> (privateStep prims.aes x).run ts.table := by
  simp only [semR, tableCall, StateT.run_mk, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [gameOracles_liftComp]
  simp

theorem semR_streams (x : PrgInput C) (ts : TableState C) (st : TsigState C) (s : HashCache C) :
    semR prims dealt (StateT.mk fun s => do
        let (y, streams) ← liftComp (((PrgInput C →ₒ Bit).randomOracle x).run s.streams) (LocalSpec C + TsigSpec C)
        pure (y, { s with streams := streams }) : TableM C Bit) ts st s =
      (fun z => (((z.1, { ts with streams := z.2 }), st), s)) <$> ((PrgInput C →ₒ Bit).randomOracle x).run ts.streams := by
  simp only [semR, StateT.run_mk, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [gameOracles_liftComp]
  simp

theorem semW_toWorld {α : Type} (oa : OracleComp (WorldSpec C) α) (log : CallLog C) (st : TsigState C)
    (c : HashCache C × HiddenCache C) :
    semW prims D (toWorld oa) log st c = (fun z => (((z.1, log), st), z.2)) <$> (simulateQ (streamWorld prims D) oa).run c := by
  simp [semW, toWorld, StateT.run_lift]

theorem semW_worldTsig (q : TsigQuery C) (log : CallLog C) (st : TsigState C) (c : HashCache C × HiddenCache C) :
    semW prims D (worldTsig dealt q) log st c =
      (fun z => (((z.1.1, log), z.1.2), z.2)) <$>
        (simulateQ (streamWorld prims D) ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) dealt q).run st)).run c := by
  simp [semW, worldTsig, StateT.run_lift]

theorem streamWorld_adversary (t : (LocalSpec C).Domain) :
    simulateQ (streamWorld prims D) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) =
      onHash (localAnswer prims t) := by
  rw [SeedHitProof.simulateQ_adversary_query]
  rfl

theorem streamWorld_honest (t : (LocalSpec C).Domain) :
    simulateQ (streamWorld prims D) (worldRoles.honest (OracleComp.lift (OracleSpec.query t))) =
      streamWorld prims D (.inr t) := by
  simp [worldRoles, free]

/-- A world query with no setup call and no programming query is a step of the world on the hash
cache. -/
theorem streamWorld_safeQuery (t : (WorldSpec C).Domain) (ht : WorldSafe t) :
    streamWorld prims D t = onHash (baseAnswer prims t) := by
  rcases t with (t | x) | t
  · rfl
  · exact ht.elim
  · rcases t with n | q | x
    · rfl
    · rfl
    · exact (ht (by simp [SetupOnly, isSetupRo])).elim

/-- A world computation with no setup call and no programming query runs in `streamWorld` as in the
world on the hash cache, with no change of the hidden streams. -/
theorem streamWorld_safe {α : Type} {oa : OracleComp (WorldSpec C) α} (h : AllQueriesSatisfy oa WorldSafe)
    (c : HashCache C) (hidden : HiddenCache C) :
    (simulateQ (streamWorld prims D) oa).run (c, hidden) =
      (fun z => (z.1, (z.2, hidden))) <$> (simulateQ (baseAnswer prims) oa).run c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self]
    rw [streamWorld_safeQuery t h.1, onHash_run, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ (h.2 _) z.2

/-! ## The operations -/

theorem couple_tsigCall (hdealt : SafeDealt dealt) (q : TsigQuery C) :
    Couple prims D dealt (tsigCall q) (worldTsig dealt q) := by
  intro ts st s
  have hsafe : AllQueriesSatisfy ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) dealt q).run st)
      WorldSafe := tsigOracles_safe freeLift_safe hdealt q st
  rw [semW_worldTsig, tableImage, streamWorld_safe hsafe, simulate_frame prims hsafe s ts.table]
  rw [show tsigCall (C := C) q = forward (.inr q) from rfl, semR_forwardTsig]
  simp [image, tableImage, Functor.map_map]

theorem couple_writeTable {q : Query C} (hq : isSetupQuery q = true) (value : HashOutput) :
    Couple prims D dealt (writeTable q value) (worldWrite q value) := by
  intro ts st s
  have hp : simulateQ (streamWorld prims D) (program q value) = onHash (programAnswer (q, value)) := by
    simp [program, counted]
    rfl
  rw [worldWrite, semW_bind, semW_toWorld, hp, tableImage, onHash_run]
  have hnot : ¬ ∃ input, q = .hash input ∧ MpcInput input := by
    rintro ⟨input, rfl, -⟩
    exact absurd hq (by simp [isSetupQuery])
  by_cases h : (ts.table q).isSome
  · simp [programAnswer, SeedPartition.merge_read_right _ hq, h, hnot, semW, semR, writeTable, image, tableImage]
  · simp [programAnswer, SeedPartition.merge_read_right _ hq, h, hnot, semW, semR, writeTable, image, tableImage,
      SeedPartition.merge_write_right _ hq]

theorem streamWorld_adversaryHash (q : Query C) :
    simulateQ (streamWorld prims D) (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C))) =
      onHash (localAnswer prims (.inr (.inl q))) :=
  streamWorld_adversary (.inr (.inl q))

theorem couple_adversaryCall (t : (LocalSpec C).Domain) :
    Couple prims D dealt (adversaryCall prims.aes t) (worldAdversaryCall t) := by
  intro ts st s
  rcases t with n | q | x
  · rw [show adversaryCall prims.aes (.inl n) = forward (.inl (.inl n)) from rfl, semR_forwardLocal,
      show worldAdversaryCall (C := C) (.inl n) =
        toWorld (worldRoles.adversary (OracleComp.lift (OracleSpec.query (.inl n)))) from rfl,
      semW_toWorld, streamWorld_adversary, tableImage, onHash_run,
      localAnswer_frame prims _ (by simp [SetupOnly]) s ts.table]
    simp [image, tableImage, Functor.map_map]
  · by_cases hq : isSetupQuery q = true
    · have eR : adversaryCall prims.aes (.inr (.inl q)) = (do
          let y : HashOutput ← tableCall prims.aes (.inl q)
          modify fun s : TableState C => { s with log := s.log ++ [(q, y)] }
          pure y) := by simp [adversaryCall, hq]
      have eW : worldAdversaryCall (C := C) (.inr (.inl q)) = (do
          let y : HashOutput ← toWorld (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C)))
          modify fun log : CallLog C => log ++ [(q, y)]
          pure y) := by simp [worldAdversaryCall, hq]
      rw [eR, eW, semR_bind, semW_bind, semR_tableCall, semW_toWorld, streamWorld_adversaryHash, tableImage,
        onHash_run, localAnswer_setup prims (.inl q) hq s ts.table]
      simp [semR, semW, image, tableImage, Functor.map_map]
    · have hq' : isSetupQuery q = false := by simpa using hq
      have eR : adversaryCall prims.aes (.inr (.inl q)) = forward (.inl (.inr (.inl q))) := by
        simp [adversaryCall, hq']
      have eW : worldAdversaryCall (C := C) (.inr (.inl q)) =
          toWorld (worldRoles.adversary (liftComp (hashQuery q) (LocalSpec C))) := by
        simp [worldAdversaryCall, hq']
      rw [eR, eW, semR_forwardLocal, semW_toWorld, streamWorld_adversaryHash, tableImage, onHash_run,
        localAnswer_frame prims _ (by simpa [SetupOnly, isSetupRo] using hq') s ts.table]
      simp [image, tableImage, Functor.map_map]
  · rw [show adversaryCall prims.aes (.inr (.inr x)) = tableCall prims.aes (.inr x) from rfl, semR_tableCall,
      show worldAdversaryCall (C := C) (.inr (.inr x)) =
        toWorld (worldRoles.adversary (OracleComp.lift (OracleSpec.query (.inr (.inr x))))) from rfl,
      semW_toWorld, streamWorld_adversary, tableImage, onHash_run,
      localAnswer_setup prims (.inr x) rfl s ts.table]
    simp [image, tableImage, Functor.map_map]

theorem curryStreams_cacheQuery (c : StreamCache C) (x : PrgInput C) (v : Bit) :
    curryStreams (c.cacheQuery x v) = (curryStreams c).cacheQuery ((x.1, x.2.1), x.2.2) v := by
  refine QueryCache.ext fun y => ?_
  by_cases h : y = ((x.1, x.2.1), x.2.2)
  · subst h; simp [curryStreams]
  · have h' : (y.1.1, y.1.2, y.2) ≠ x := fun e => h (by subst e; rfl)
    simp [curryStreams, QueryCache.cacheQuery_of_ne _ _ h, QueryCache.cacheQuery_of_ne _ _ h']

/-- The stream of a hidden key in the forger is the stream of `streamWorld`. -/
theorem randomOracle_curry (x : PrgInput C) (c : StreamCache C) :
    ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle ((x.1, x.2.1), x.2.2)).run (curryStreams c) =
      (fun z => (z.1, curryStreams z.2)) <$> ((PrgInput C →ₒ Bit).randomOracle x).run c := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  have e : curryStreams c ((x.1, x.2.1), x.2.2) = c x := rfl
  rw [e]
  cases c x with
  | some u => simp
  | none => simp [curryStreams_cacheQuery]

theorem couple_honestCall (t : (LocalSpec C).Domain) :
    Couple prims D dealt (honestCall prims.aes D t) (worldHonestCall t) := by
  intro ts st s
  have eW : ∀ t, worldHonestCall (C := C) t = toWorld (worldRoles.honest (OracleComp.lift (OracleSpec.query t))) :=
    fun _ => rfl
  rw [eW, semW_toWorld, streamWorld_honest]
  rcases t with n | q | x
  · rw [show honestCall prims.aes D (.inl n) = forward (.inl (.inl n)) from rfl, semR_forwardLocal,
      show streamWorld prims D (.inr (.inl n)) = onHash (localAnswer prims (.inl n)) from rfl, tableImage, onHash_run,
      localAnswer_frame prims _ (by simp [SetupOnly]) s ts.table]
    simp [image, tableImage, Functor.map_map]
  · rw [show streamWorld prims D (.inr (.inr (.inl q))) = onHash (localAnswer prims (.inr (.inl q))) from rfl,
      tableImage, onHash_run]
    by_cases hq : isSetupQuery q = true
    · rw [show honestCall prims.aes D (.inr (.inl q)) = tableCall prims.aes (.inl q) by simp [honestCall, hq],
        semR_tableCall, localAnswer_setup prims (.inl q) hq s ts.table]
      simp [image, tableImage, Functor.map_map]
    · have hq' : isSetupQuery q = false := by simpa using hq
      rw [show honestCall prims.aes D (.inr (.inl q)) = forward (.inl (.inr (.inl q))) by simp [honestCall, hq'],
        semR_forwardLocal, localAnswer_frame prims _ (by simpa [SetupOnly, isSetupRo] using hq') s ts.table]
      simp [image, tableImage, Functor.map_map]
  · by_cases hx : Hidden D x.1
    · have eS : streamWorld prims D (.inr (.inr (.inr x))) = StateT.mk fun st =>
          (fun r => (r.1, (st.1, r.2))) <$>
            ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle ((x.1, x.2.1), x.2.2)).run st.2 := by
        simp [streamWorld, hx]
      have eR : honestCall prims.aes D (.inr (.inr x)) = (StateT.mk fun s => do
          let (y, streams) ← liftComp (((PrgInput C →ₒ Bit).randomOracle x).run s.streams) (LocalSpec C + TsigSpec C)
          pure (y, { s with streams := streams }) : TableM C Bit) := by simp [honestCall, hx]
      rw [eS, eR, semR_streams, tableImage, StateT.run_mk, randomOracle_curry]
      simp [image, tableImage, Functor.map_map]
    · have eS : streamWorld prims D (.inr (.inr (.inr x))) = onHash (localAnswer prims (.inr (.inr x))) := by
        simp [streamWorld, hx]
      rw [eS, show honestCall prims.aes D (.inr (.inr x)) = tableCall prims.aes (.inr x) by simp [honestCall, hx],
        semR_tableCall, tableImage, onHash_run, localAnswer_setup prims (.inr x) rfl s ts.table]
      simp [image, tableImage, Functor.map_map]

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.couple_honestCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.couple_honestCall
