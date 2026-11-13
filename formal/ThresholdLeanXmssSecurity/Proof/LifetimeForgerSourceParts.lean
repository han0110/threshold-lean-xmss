import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.LifetimeForgerPrecompute
import ThresholdLeanXmssSecurity.Proof.LifetimeForgerMerge

/-! # Source and prefix identities for the lifetime forger

The concrete source uses the exact static corruption requests and delivered
keys, including the default keys of corrupt operators in the slot execution.
The source prefix preserves the external signing state. The table prefix keeps
the joint search-failure flag and win, with the original cache continuation.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeForgerSourceParts
open LifetimeForgerMerge LifetimeSigningFrame
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}
def delivered (D : C.Coalition) (d : LifetimeBridge.Dealing C) : C.Party → Option (Keys C) :=
  fun i => if i ∉ D.1 then some (d.2.2 i) else none
def receivedKeys (D : C.Coalition) (d : LifetimeBridge.Dealing C) : C.Party → Keys C :=
  fun i => (delivered D d i).getD default


/-- Honest delivered keys are exactly the sampled keys. -/
theorem receivedKeys_honest (D : C.Coalition) (d : LifetimeBridge.Dealing C)
    (i : C.Party) (hi : i ∉ D.1) : receivedKeys D d i = d.2.2 i := by
  simp only [receivedKeys, delivered, if_pos hi, Option.getD_some]

def corruptRequests (D : C.Coalition) : OracleComp (ReplaySpec C) (C.Party → Option (Keys C)) :=
  Concrete.sequenceFin fun i =>
    if i ∈ D.1 then OracleComp.lift (OracleSpec.query (spec := ReplaySpec C) (.inr (.corrupt i)))
    else pure none


/-- Both seed selectors are fixed by the actual supported dealing. -/
theorem dealing_seeds (D : C.Coalition) (d : LifetimeBridge.Dealing C)
    (hd : d ∈ support (prawnsKeyGen (C := C))) :
    honestSeeds D d.2.2 = d.2.1 ∧
    honestSeeds D (receivedKeys D d) = d.2.1 ∧
    LifetimeSlots.simSeeds D (receivedKeys D d) = (fun T =>
      (C.parties.findSome? fun j => if j ∈ C.holders T then
        ((if j ∈ D.1 then some (d.2.2 j) else none) : Option (Keys C)).map (·.seed T)
        else none).getD 0) := by
  obtain ⟨pairs, dealt⟩ := prawnsKeyGen_support d hd
  have honest : honestSeeds D d.2.2 = d.2.1 := by
    funext T
    unfold honestSeeds
    have found : (C.parties.findSome? fun i => if i ∉ D.1 ∧ i ∈ C.holders T
        then some ((d.2.2 i).seed T) else none) = some (d.2.1 T) := by
      apply findSome_eq_of_unique
      · obtain ⟨i, held, hi⟩ := keygen_honest_holder D T
        exact ⟨i, by simp [Committee.parties], by simp [hi, held, dealt, dealtKeys]⟩
      · intro i _ b hb
        split_ifs at hb with hi
        · simpa [dealt, dealtKeys, hi.2] using hb.symm
    simp only [found, Option.getD_some]
  have received : honestSeeds D (receivedKeys D d) = d.2.1 :=
    (LifetimeTableReplay.honestSeeds_congr D _ _ (receivedKeys_honest D d)).trans honest
  refine ⟨honest, received, ?_⟩
  funext T
  simp only [LifetimeSlots.simSeeds, received]
  by_cases known : KnownTo D.1 T
  · rw [if_pos known]
    have found : (C.parties.findSome? fun j => if j ∈ C.holders T then
        ((if j ∈ D.1 then some (d.2.2 j) else none) : Option (Keys C)).map (·.seed T)
        else none) = some (d.2.1 T) := by
      apply findSome_eq_of_unique
      · obtain ⟨j, hj, held⟩ := known
        exact ⟨j, by simp [Committee.parties], by simp [hj, held, dealt, dealtKeys]⟩
      · intro j _ b hb
        split_ifs at hb with held hj
        · simpa [dealt, dealtKeys, held] using hb.symm
        · simp at hb
    simp only [found, Option.getD_some]
  · rw [if_neg known]
    have found : (C.parties.findSome? fun j => if j ∈ C.holders T then
        ((if j ∈ D.1 then some (d.2.2 j) else none) : Option (Keys C)).map (·.seed T)
        else none) = none := by
      apply List.findSome?_eq_none_iff.mpr
      intro j _
      by_cases held : j ∈ C.holders T
      · have hj : j ∉ D.1 := fun hj => known ⟨j, hj, held⟩
        simp [held, hj]
      · simp [held]
    simp only [found, Option.getD_none]

private theorem corrupt_one (D : C.Coalition) (d : LifetimeBridge.Dealing C)
    (top : TopTree) (S : Finset C.Party) (inside : S ⊆ D.1) (i : C.Party) :
    (simulateQ (directHandler d top)
      (if i ∈ D.1 then OracleComp.lift (OracleSpec.query (spec := ReplaySpec C) (.inr (.corrupt i)))
       else pure none)).run (initialSign S) =
      pure ((if i ∈ D.1 then some (d.2.2 i) else none),
        initialSign (if i ∈ D.1 then insert i S else S)) := by
  by_cases hi : i ∈ D.1
  · have bound : ¬ C.t - 1 < (insert i S).card :=
      not_lt.mpr ((Finset.card_le_card (Finset.insert_subset hi inside)).trans D.2)
    simp only [if_pos hi, simulateQ_spec_query]
    change (tsigOracles worldRo (fixedDealt d top) (.corrupt i)).run (initialSign S) = _
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind, initialSign,
      if_neg bound, StateT.run_set, StateT.run_pure, fixedDealt, dealtWith]
  · simp only [if_neg hi, simulateQ_pure, StateT.run_pure]

private theorem corrupt_sequence (D : C.Coalition) (d : LifetimeBridge.Dealing C)
    (top : TopTree) : ∀ {n : ℕ} (f : Fin n → C.Party) (S : Finset C.Party), S ⊆ D.1 →
    ∃ S', S' ⊆ D.1 ∧ (∀ i, i ∈ S' ↔ i ∈ S ∨ ∃ j, f j = i ∧ i ∈ D.1) ∧
      (simulateQ (directHandler d top) (Concrete.sequenceFin fun j =>
        if f j ∈ D.1 then OracleComp.lift (OracleSpec.query (spec := ReplaySpec C) (.inr (.corrupt (f j))))
        else pure none)).run (initialSign S) =
      pure ((fun j => if f j ∈ D.1 then some (d.2.2 (f j)) else none), initialSign S') := by
  intro n
  induction n with
  | zero =>
    intro f S inside
    refine ⟨S, inside, ?_, ?_⟩
    · intro i; simp
    · simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure]
      congr 2
      funext j
      exact j.elim0
  | succ n ih =>
    intro f S inside
    let S₁ := if f 0 ∈ D.1 then insert (f 0) S else S
    have inside₁ : S₁ ⊆ D.1 := by
      dsimp only [S₁]
      split_ifs with h
      · exact Finset.insert_subset h inside
      · exact inside
    obtain ⟨S', inside', members, run⟩ := ih (fun j => f j.succ) S₁ inside₁
    refine ⟨S', inside', ?_, ?_⟩
    · intro i
      rw [members]
      simp only [S₁, Fin.exists_fin_succ]
      by_cases h : f 0 ∈ D.1
      · simp only [if_pos h, Finset.mem_insert]
        constructor
        · rintro ((eq | old) | later)
          · exact Or.inr (Or.inl ⟨eq.symm, eq ▸ h⟩)
          · exact Or.inl old
          · exact Or.inr (Or.inr later)
        · rintro (old | ⟨eq, _⟩ | later)
          · exact Or.inl (Or.inr old)
          · exact Or.inl (Or.inl eq.symm)
          · exact Or.inr later
      · simp only [if_neg h]
        constructor
        · rintro (old | later)
          · exact Or.inl old
          · exact Or.inr (Or.inr later)
        · rintro (old | ⟨eq, hi⟩ | later)
          · exact Or.inl old
          · exact (h (eq ▸ hi)).elim
          · exact Or.inr later
    · simp only [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind]
      rw [corrupt_one D d top S inside (f 0)]
      simp only [pure_bind]
      rw [run]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      congr 2
      funext j
      cases j using Fin.cases <;> rfl

/-- The actual static corruption prefix returns the coalition's dealt keys. -/
theorem corrupt_direct (D : C.Coalition) (d : LifetimeBridge.Dealing C) (top : TopTree) :
    (simulateQ (directHandler d top) (corruptRequests D)).run (initialSign ∅) =
      pure ((fun i => if i ∈ D.1 then some (d.2.2 i) else none), initialSign D.1) := by
  obtain ⟨S, _, members, run⟩ := corrupt_sequence D d top (fun i : C.Party => i) ∅
    (Finset.empty_subset _)
  have eq : S = D.1 := by
    ext i
    simpa using members i
  simpa only [corruptRequests, eq] using run

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

abbrev Tables := Tree → Option TreeOutput × List (List (List Bit))
abbrev ForgerState (C : Committee) (E : Type) :=
  LifetimeState C E × Option (StreamCache C × Option TreeOutput)
def initialForger (D : C.Coalition) : ForgerState C E :=
  ((LifetimeSlotTransport.initialSlot (E := E) D).1, none)

def sourceReplay (publicKey : PublicKey) (top : TopTree) : OracleComp (ReplaySpec C) Forgery := do
  let corrupt ← corruptRequests D
  let sim := keygenSimulator D A.keygen
  let st ← inWorld (sim.start (corruptInputs D fun _ => ()) [])
  let (st, _) ← inWorld (sim.answer st (publicKey.parameter, corrupt))
  let state ← inWorld (sim.output st)
  let h := (C.parties.find? (· ∉ D.1)).getD (firstParty C)
  let adversary : QueryImpl (LocalSpec C)
      (StateT (ForgerState C E) (OracleComp (ReplaySpec C))) :=
    fun t => StateT.lift (inWorld (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  (simulateQ (adversary + forgerOracles K circuits settings attempts D publicKey.parameter corrupt top h)
    (A.run state publicKey.parameter)).run' (initialForger D)

theorem forger_source (publicKey : PublicKey) (top : TopTree) :
    lifetimeForger K circuits settings attempts D A publicKey top =
      (simulateQ forgerWorld (sourceReplay K circuits settings attempts D A publicKey top)).run' ∅ := by rfl


-- Port of LifetimeForgerSearch.output_lift_bind, whose helper is private.
private def output {α : Type} (p : EmulationM C α) : OracleComp (WorldSpec C) α :=
  (fun r => r.1.1) <$> (p.run ∅).run

private theorem output_lift_bind {α β : Type} (p : OracleComp (WorldSpec C) α)
    (f : α → EmulationM C β) :
    output (StateT.lift (liftM p) >>= f) = p >>= fun a => output (f a) := by
  simp only [output, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    WriterT.run_bind, WriterT.run_liftM, bind_map_left, map_bind, Functor.map_map]

/-- The exact joint precompute observation retains its table flag and win. -/
theorem precompute_pair (prims : Primitives) :
    LifetimeForgerReplay.precomputeRun prims K circuits settings attempts D A = (do
      let d ← prawnsKeyGen (C := C)
      let r ← roRun prims (LifetimeForgerReplay.dealerTables circuits settings d.1
        (honestSeeds D d.2.2)) ∅
      let win ← (simulateQ (worldAnswer prims)
        (LifetimeForgerPrecompute.tableWorld K circuits settings attempts D A d r.1)).run' r.2
      pure (LifetimeForgerReplay.searchFails r.1, win)) := by
  rw [LifetimeForgerPrecompute.precomputeRun_output]
  unfold LifetimeForgerReplay.precomputeGame
  change (simulateQ (worldAnswer prims) (output _)).run' ∅ = _
  rw [output_lift_bind]
  simp only [simulateQ_bind, simulateQ_world_sample, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
  apply bind_congr
  intro d
  change (Prod.fst <$> (simulateQ (worldAnswer prims)
    (output (StateT.lift (liftM (free (liftComp
      (LifetimeForgerReplay.dealerTables circuits settings d.1 (honestSeeds D d.2.2))
        (LocalSpec C)))) >>= _))).run ∅) = _
  rw [output_lift_bind]
  simp only [simulateQ_bind, StateT.run_bind, map_bind, simulateQ_free, localRun_liftComp]
  apply bind_congr
  intro r
  rw [output_lift_bind]
  simp only [LifetimeForgerPrecompute.tableWorld, simulateQ_bind, StateT.run_bind,
    map_bind]
  apply bind_congr
  intro keygen
  simp only [output, LifetimeHybridOrder.emulationGame, StateT.run_map, WriterT.run_map,
    simulateQ_map, Functor.map_map]

def forgerRequests (d : LifetimeBridge.Dealing C) (top : TopTree) (h : C.Party) : QueryImpl (LocalSpec C + LifetimeSpec C E)
    (StateT (ForgerState C E) (OracleComp (ReplaySpec C))) :=
  (fun t => (StateT.lift (inWorld (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) :
    StateT (ForgerState C E) (OracleComp (ReplaySpec C)) ((LocalSpec C).Range t))) +
    forgerOracles K circuits settings attempts D d.1
      (fun i => if i ∈ D.1 then some (d.2.2 i) else none) top h

def slotKernel (d : LifetimeBridge.Dealing C) (h : C.Party) (tables : Tables) (prims : Primitives) :
    QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT (LifetimeSlotTransport.Physical C E) ProbComp) :=
  fun t => LifetimeTableReplay.tableKernel K circuits settings attempts D (receivedKeys D d) h tables prims (.inl t)

theorem slot_delivered (prims : Primitives) (d : LifetimeBridge.Dealing C)
    (hd : d ∈ support (prawnsKeyGen (C := C))) (tables : Tables) (state : A.keygen.State)
    (h : C.Party) (hh : C.parties.find? (· ∉ D.1) = some h) (c : HashCache C) :
    (LifetimeSlotTransport.evalEmulation prims
      (LifetimeSlots.slotRun K circuits settings attempts
        (LifetimeForgerReplay.tableEnv circuits settings D tables)
        (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D A state (delivered D d))).run'
        (∅, c, []) =
    ((simulateQ (slotKernel K circuits settings attempts D d h tables prims)
      (A.run state d.1)).run (LifetimeSlotTransport.initialSlot D, (∅, c, [])) >>= fun a =>
        (LifetimeSlotTransport.evalEmulation prims
          (LifetimeSlotTransport.finish D (receivedKeys D d) h a.1 a.2.1.1)).run' a.2.2)  := by
  rw [LifetimeTableReplay.slotRun_table_tail]
  have honest : h ∉ D.1 := of_decide_eq_true (List.find?_some (p := fun i : C.Party => decide (i ∉ D.1)) hh)
  have ready : ∀ i, i ∉ D.1 → (delivered D d i).isSome := by
    intro i hi
    simp only [delivered, if_pos hi, Option.isSome_some]
  simp only [hh, if_neg (not_not_intro ready)]
  have parameter : (receivedKeys D d h).parameter = d.1 := by
    rw [receivedKeys_honest D d h honest]
    exact LifetimeTableReplay.prawnsKeyGen_parameter d hd h
  change (LifetimeSlotTransport.evalEmulation prims (Prod.fst <$>
    (simulateQ (LifetimeTableReplay.tableHandler K circuits settings attempts D
      (receivedKeys D d) h tables)
      (LifetimeSlotTransport.tailProgram A state (receivedKeys D d h).parameter)).run
        (LifetimeSlotTransport.initialSlot D))).run' (∅, c, []) = _
  rw [parameter, ← LifetimeSlotTransport.evalSlot_output,
    ← LifetimeTableReplay.tableKernel_run]
  simp only [LifetimeSlotTransport.tailProgram, simulateQ_bind,
    LifetimeEmulatedBudget.simulateQ_comp, simulateQ_spec_query, StateT.run_bind, map_bind]
  change (do
    let a ← (simulateQ (slotKernel K circuits settings attempts D d h tables prims)
      (A.run state d.1)).run (LifetimeSlotTransport.initialSlot D, (∅, c, []))
    Prod.fst <$> (LifetimeTableReplay.tableKernel K circuits settings attempts D
      (receivedKeys D d) h tables prims (.inr a.1)).run a.2) = _
  apply bind_congr
  intro a
  change Prod.fst <$> (LifetimeSlotTransport.evalSlot prims
    (StateT.mk fun s : LifetimeSlots.SlotState C E =>
      (fun b => (b, s)) <$> LifetimeSlotTransport.finish D (receivedKeys D d) h a.1 s.1)).run a.2 = _
  simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk,
    LifetimeSlotTransport.evalEmulation_map, StateT.run_map, Functor.map_map, StateT.run'_eq]

/-- Direct interpretation of a world computation preserves the external signer state. -/
theorem direct_inWorld (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (p : OracleComp (WorldSpec C) α) (st : TsigState C) :
    (simulateQ (directHandler d top) (inWorld p)).run st =
      (fun a => (a, st)) <$> p := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp only [inWorld, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [inWorld, simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query, StateT.run_bind]
    have handler : directHandler d top (.inl t) = StateT.lift (OracleComp.lift (OracleSpec.query t)) := rfl
    rw [handler]
    simp only [StateT.run_lift, bind_assoc, pure_bind, map_bind]
    apply bind_congr
    intro a
    exact ih a st

theorem source_keygen_split (d : LifetimeBridge.Dealing C) (top : TopTree) :
    (simulateQ (directHandler d top)
      (sourceReplay K circuits settings attempts D A ⟨top.root, d.1⟩ top)).run (initialSign ∅) = (do
      let sim := keygenSimulator D A.keygen
      let st ← sim.start (corruptInputs D fun _ => ()) []
      let (st, _) ← sim.answer st (d.1, fun i => if i ∈ D.1 then some (d.2.2 i) else none)
      let state ← sim.output st
      let h := (C.parties.find? (· ∉ D.1)).getD (firstParty C)
      (simulateQ (directHandler d top)
        ((simulateQ (forgerRequests K circuits settings attempts D d top h)
          (A.run state d.1)).run' (initialForger D))).run (initialSign D.1))  := by
  simp only [sourceReplay, simulateQ_bind, StateT.run_bind]
  rw [corrupt_direct]
  simp only [pure_bind, direct_inWorld, bind_map_left]
  rfl


end ThresholdLeanXmssSecurity.LifetimeForgerSourceParts

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.receivedKeys_honest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.receivedKeys_honest

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.dealing_seeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.dealing_seeds

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.corrupt_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.corrupt_direct

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.forger_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.forger_source

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.precompute_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.precompute_pair

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.slot_delivered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.slot_delivered

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.direct_inWorld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.direct_inWorld

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.source_keygen_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerSourceParts.source_keygen_split
