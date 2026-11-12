import ThresholdLeanXmssSecurity.Proof.LifetimeTailFlagBound
import ThresholdLeanXmssSecurity.Proof.LifetimeTailDriver
import ThresholdLeanXmssSecurity.Proof.LifetimeTailFlag

/-!
# The selected lifetime tail and its generic driver

The four-copy lifetime continuation maps to the driver's world roles. The
selected setup boundary retains the lifetime state and pending continuation.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeTailBridge

open LifetimePrfTransportProof LifetimeRunBoundary LifetimeSetupBridge
open LifetimeTailKernel LifetimeTailDriver LifetimeEmulatedBudget

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Map the two counted copies to the adversary and both free copies to the
honest interface. -/
def tailMap : QueryImpl (Spec4 C) (OracleComp (WorldSpec C)) :=
  (((fun t => (worldRoles (C := C)).adversary (OracleComp.lift (OracleSpec.query t))) +
    (fun t => (worldRoles (C := C)).adversary (OracleComp.lift (OracleSpec.query t)))) +
    (fun t => (worldRoles (C := C)).honest (OracleComp.lift (OracleSpec.query t)))) +
    (fun t => (worldRoles (C := C)).honest (OracleComp.lift (OracleSpec.query t)))

private theorem world_adversary_simulate {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (fun t => worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) p =
      worldRoles.adversary p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    simp only [worldRoles, liftComp_bind, counted_bind]

private theorem world_honest_simulate {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (fun t => worldRoles.honest (OracleComp.lift (OracleSpec.query t))) p =
      worldRoles.honest p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    simp only [worldRoles_honest, free_bind]

-- These are the four-copy ports of `impl4_advCopy` through
-- `impl4_targetCopy_free`, with the target monad changed to the world.
@[simp] theorem tailMap_advCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ tailMap (advCopy4 p) = worldRoles.adversary p := by
  rw [advCopy4, simulateQ_comp]
  refine Eq.trans ?_ (world_adversary_simulate p)
  apply congrArg (fun impl : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ impl p)
  funext t
  exact simulateQ_spec_query tailMap (.inl (.inl (.inl t)))

@[simp] theorem tailMap_emulCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ tailMap (emulCopy4 p) = worldRoles.adversary p := by
  rw [emulCopy4, simulateQ_comp]
  refine Eq.trans ?_ (world_adversary_simulate p)
  apply congrArg (fun impl : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ impl p)
  funext t
  exact simulateQ_spec_query tailMap (.inl (.inl (.inr t)))

@[simp] theorem tailMap_freeCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ tailMap (freeCopy4 p) = worldRoles.honest p := by
  rw [freeCopy4, simulateQ_comp]
  refine Eq.trans ?_ (world_honest_simulate p)
  apply congrArg (fun impl : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ impl p)
  funext t
  exact simulateQ_spec_query tailMap (.inl (.inr t))

@[simp] theorem tailMap_targetCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ tailMap (targetCopy4 p) = worldRoles.honest p := by
  rw [targetCopy4, simulateQ_comp]
  refine Eq.trans ?_ (world_honest_simulate p)
  apply congrArg (fun impl : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ impl p)
  funext t
  exact simulateQ_spec_query tailMap (.inr t)

/-- All chronological roles have the exact driver image, including earlier
runs. The later erasure theorem uses the absence of emulated calls. -/
theorem tailMap_roles (n r : ℕ) :
    RolesHom (simulateQ' tailMap) (roles4 (C := C) n r) (tailRoles n r) := by
  unfold roles4 tailRoles
  split_ifs with hlt heq
  · subst r
    omega
  · exact ⟨fun p => tailMap_advCopy p, fun p => tailMap_emulCopy p⟩
  · exact ⟨fun p => tailMap_advCopy p, fun p => tailMap_targetCopy p⟩
  · exact ⟨fun p => tailMap_advCopy p, fun p => tailMap_advCopy p⟩

theorem tailMap_base : RolesHom (simulateQ' tailMap) (base4 (C := C)) worldRoles :=
  ⟨fun p => tailMap_advCopy p, fun p => tailMap_freeCopy p⟩

/-- The setup adversary's held continuation supplies the driver's seed. -/
def seedOf (s : Option (Held C E) × StreamCache C) : Option (TailSeed C E) :=
  s.1.bind fun held => held.state.running.map fun r =>
    ⟨held.keys, held.h, r.1, held.state.restore, held.continuation⟩

/-- The sole copy whose interpretation may change the stream table. -/
def Emul4 : (Spec4 C).Domain → Prop
  | .inl (.inl (.inr _)) => True
  | _ => False

/-- Without emulated calls, erasing the log leaves the stream table fixed and
maps every remaining call to its world role. -/
theorem erase_quiet (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (hp : IsQueryBoundP p Emul4 0) :
    treeSimErase (simulateQ (hybridImpl D) p) = StateT.lift (simulateQ tailMap p) := by
  have hstep : ∀ t : (Spec4 C).Domain, ¬ Emul4 t →
      treeSimErase (hybridImpl D t) = StateT.lift (tailMap t) := by
    intro t ht
    rcases t with ((t | t) | t) | t
    · exact treeSimErase_adversary D _
    · exact False.elim (ht trivial)
    · exact LifetimeKeygenHopProof.erase_base_honest D _
    · exact LifetimeKeygenHopProof.erase_base_honest D _
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp only [simulateQ_pure, treeSimErase_pure]
    funext table
    change (pure a : StateT (StreamCache C) (OracleComp (WorldSpec C)) α).run table =
      (StateT.lift (pure a)).run table
    simp only [StateT.run_pure, StateT.run_lift, pure_bind]
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBoundP_query_bind_iff Emul4 t k 0).mp hp
    have ht : ¬ Emul4 t := ht.resolve_right (by omega)
    have hk : ∀ u, IsQueryBoundP (k u) Emul4 0 := by simpa [ht] using hk
    rw [simulateQ_bind, simulateQ_spec_query, treeSimErase_bind, hstep t ht]
    simp only [ih _ (hk _), simulateQ_bind, simulateQ_spec_query]
    funext table
    change ((StateT.lift (tailMap t) >>= fun a => StateT.lift (simulateQ tailMap (k a))) :
      StateT (StreamCache C) (OracleComp (WorldSpec C)) α).run table =
      (StateT.lift (tailMap t >>= fun a => simulateQ tailMap (k a))).run table
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]

/-- Signing changes only the signing record, retaining every stored top. -/
theorem signAs_top {ι : Type} {spec : OracleSpec ι} (base : Roles C (OracleComp spec))
    (keys : C.Party → Keys C) (value : Point → OracleComp spec Digest)
    (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E) (r : _ × LifetimeState C E)
    (hr : r ∈ support (LifetimeProof.signAs base keys value i q st)) : r.2.top = st.top := by
  unfold LifetimeProof.signAs at hr
  obtain ⟨⟨answer, sign⟩, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  change r = (answer, { st with sign := { sign with trees := fun _ => none } }) at hr
  rw [hr]

@[simp] theorem restore_override (st : LifetimeState C E)
    (running : Option (ThresholdLeanXmss.Tree × ℕ × (C.Party → Step C E RealSpec TreeOutput))) :
    { ((visibleState st).restore : LifetimeState C E) with running := running } = { st with running := running } := by
  cases st
  rfl

section Continuation

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ)

@[simp] theorem tailMap_value (keys : C.Party → Keys C) (point : Point) :
    simulateQ tailMap (value4 D keys point) = valueW D keys point :=
  tailMap_freeCopy _

/-- The lifetime oracle homomorphism keeps the complete state and answer. -/
theorem tailMap_oracles (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E) :
    simulateQ tailMap ((oracles4 K circuits settings attempts D n keys h t).run st) =
      (oraclesW K circuits settings attempts D n keys h t).run st := by
  rcases t with t | q
  · change simulateQ tailMap ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) =
      (StateT.lift (worldRoles.adversary _) : StateT _ (OracleComp (WorldSpec C)) _).run st
    simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure, tailMap_advCopy]
  · exact hom_lifetimeOracles (simulateQ' tailMap) K circuits settings attempts
      (roles4 n) base4 (tailRoles n) worldRoles (tailMap_roles n) tailMap_base D keys
      (value4 D keys) (valueW D keys) (tailMap_value D keys) h q st

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The final win test has the driver's base-role image, without changing the
stored tops, signing state, or forgery. -/
theorem tailMap_finish (keys : C.Party → Keys C) (h : C.Party)
    (r : Forgery × LifetimeState C E) :
    simulateQ tailMap (finish4 D keys h r) = finishW D keys h r := by
  classical
  let φ := simulateQ' (tailMap (C := C))
  have hlift : ∀ {β : Type} (p : OracleComp (RoSpec C) β),
      φ ((base4 (C := C)).honest (liftComp p _)) = roW p :=
    fun p => tailMap_freeCopy _
  unfold finish4 finishW
  split
  · exact simulateQ_pure _ _
  · cases hpub : r.2.publicKey (keys h).parameter h with
    | none => simp only [simulateQ_pure]
    | some pub =>
      rcases pub with ⟨pk, top⟩
      change φ (forgeryWins _ _ _ _) = _
      rw [hom_forgeryWins, hom_dealtWith φ _ _ hlift _ _ _ _ _ (tailMap_value D keys)]
      simp only [hlift]

/-- The entire four-copy continuation maps call for call to the driver world. -/
theorem tailMap_tail (b : Boundary C E) :
    simulateQ tailMap (tail4 K circuits settings attempts D n (some b)) =
      (simulateQ (oraclesW K circuits settings attempts D n b.keys b.h) b.rest).run b.state >>=
        finishW D b.keys b.h := by
  rw [tail4, simulateQ_bind]
  have hm := hom_run_simulate (simulateQ' tailMap)
    (oracles4 K circuits settings attempts D n b.keys b.h)
    (oraclesW K circuits settings attempts D n b.keys b.h)
    (tailMap_oracles K circuits settings attempts D n b.keys b.h) b.rest b.state
  change simulateQ tailMap _ = _ at hm
  rw [hm]
  exact bind_congr fun r => tailMap_finish D b.keys b.h r

set_option backward.isDefEq.respectTransparency false in
/-- Non-round requests cannot replace a top while a ceremony is running. -/
theorem nonround_top (keys : C.Party → Keys C) (h : C.Party)
    (st : LifetimeState C E) (hrun : st.running ≠ none)
    (t : (LocalSpec C + LifetimeSpec C E).Domain)
    (ht : ∀ sent, t ≠ .inr (.round sent)) (r : _ × LifetimeState C E)
    (hr : r ∈ support ((oracles4 K circuits settings attempts D n keys h t).run st)) :
    r.2.top = st.top := by
  rcases t with t | q
  · change r ∈ support ((StateT.lift (advCopy4 _) : StateT _ (OracleComp (Spec4 C)) _).run st) at hr
    rw [StateT.run_lift] at hr
    obtain ⟨a, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    change r = (a, st) at hr
    rw [hr]
  · rw [oracles4_inr] at hr
    cases q with
    | sign q =>
      cases q with
      | corrupt i => have he : r = (none, st) := hr; rw [he]
      | tree b =>
        rw [LifetimeProof.run_sign_tree] at hr
        exact signAs_top base4 keys (value4 D keys) h (.tree b) st r hr
      | round1 i J e message =>
        rw [LifetimeProof.run_round1] at hr
        split at hr
        · have he : r = (none, st) := hr; rw [he]
        · exact signAs_top base4 keys (value4 D keys) i (.round1 i J e message)
            { st with signed := insert (treeOf e) st.signed } r hr
      | round2 i J e message parts =>
        rw [LifetimeProof.run_round2] at hr
        split at hr
        · have he : r = (none, st) := hr; rw [he]
        · exact signAs_top base4 keys (value4 D keys) i (.round2 i J e message parts)
            { st with signed := insert (treeOf e) st.signed } r hr
    | publicKey => have he : r = (st.publicKey (keys h).parameter h, st) := hr; rw [he]
    | start tree =>
      rw [LifetimeProof.run_start, if_pos (fun hc => hrun hc.1)] at hr
      have he : r = (none, st) := hr
      rw [he]
    | round sent => exact False.elim (ht sent rfl)

/-- The whole segment before the next round retains the honest ceremony's tops. -/
theorem runTo_top (keys : C.Party → Keys C) (h : C.Party)
    (prog : Program C E) (st : LifetimeState C E) (hrun : st.running ≠ none)
    (r : Pause C E × LifetimeState C E)
    (hr : r ∈ support ((runTo (oracles4 K circuits settings attempts D n keys h) RoundStop prog).run st)) :
    r.2.top = st.top := by
  have inv := runTo_quietP (P := fun _ => False)
    (oracles4 K circuits settings attempts D n keys h) RoundStop
    (fun s => s.top = st.top ∧ s.running = st.running) ?_ prog st ⟨rfl, rfl⟩
  · exact (inv.2 r hr).1.1
  · intro t s hs ht
    refine ⟨?_, fun out hout => ?_⟩
    · convert isQueryBoundP_false ((oracles4 K circuits settings attempts D n keys h t).run s) 0 using 1
    have hn : s.running ≠ none := by rw [hs.2]; exact hrun
    exact ⟨(nonround_top K circuits settings attempts D n keys h s hn t
        (fun sent he => ht (.round sent) he trivial) out hout).trans hs.1,
      (nonround_running K circuits settings attempts D n keys h s hn t
        (fun sent he => ht (.round sent) he trivial) out hout).trans hs.2⟩

/-- Every selected setup continuation avoids the emulated copy. -/
theorem tail4_noEmul (A : LifetimeAdversary C E) (ob : Option (Boundary C E))
    (hb : ob ∈ support (setup4 K circuits settings attempts D n A)) :
    IsQueryBoundP (tail4 K circuits settings attempts D n ob) Emul4 0 := by
  cases ob with
  | none => exact isQueryBoundP_pure _ _ _
  | some b =>
    apply IsQueryBoundP.of_imp (p' := TailRun (rowsOf b.rows))
    · intro t ht
      rcases t with ((t | t) | t) | t
      · exact ht
      · trivial
      · exact ht
      · exact False.elim ht
    · exact tail4_run_quiet D n K circuits settings attempts b
        (setup4_tail D n K circuits settings attempts A _ hb b rfl)

/-- The selected tail ignores both the earlier stream table and the erased log.
This equality retains every ordinary oracle answer. -/
theorem worldTail_eq (A : LifetimeAdversary C E) (ob : Option (Boundary C E))
    (hb : ob ∈ support (setup4 K circuits settings attempts D n A))
    (table : StreamCache C) (log : CallLog C) :
    worldTail K circuits settings attempts D n ((ob, table), log) =
      simulateQ tailMap (tail4 K circuits settings attempts D n ob) := by
  have he := congrArg (fun p => Prod.fst <$> p.run table)
    (erase_quiet D _ (tail4_noEmul K circuits settings attempts D n A ob hb))
  simpa only [treeSimErase, StateT.run_mk, keygenEraseLog, Functor.map_map,
    StateT.run_lift, bind_pure_comp, Function.comp_def, id_map', worldTail] using he

set_option backward.isDefEq.respectTransparency false in
/-- On a held reveal, the seed retains the same keys, top trees, continuation,
and complete settled lifetime state. -/
theorem driver_tail_some (held : Held C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hr : held.state.running = some (tree, fuel))
    (hc : CountIs (n + 1) (held.state.restore : LifetimeState C E))
    (rows : RevealRows C) (table : StreamCache C) :
    (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings
      ((some held, table), some rows) =
      let steps := fun i => suspendStep
        (cont K circuits settings held.keys held.state.restore tree i) (prssFinishStep i (rows i))
      simulateQ tailMap (tail4 K circuits settings attempts D n
        (some ⟨held.keys, held.h, some rows, held.continuation (some (toCoalition D steps)),
          LifetimeState.settle D { (held.state.restore : LifetimeState C E) with
            running := some (tree, ceremonyFuel circuits settings - 2, steps) }⟩)) := by
  dsimp only
  rw [tailMap_tail]
  unfold TailDriver.tail TailDriver.steps lifeDriver seedOf
  simp only [Option.bind_some, hr, Option.map_some, Option.getD_some, if_pos hc]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The driver's retained stream table does not enter its continuation. -/
theorem driver_tail_table (held : Option (Held C E)) (rows : Option (RevealRows C))
    (first second : StreamCache C) :
    (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings ((held, first), rows) =
      (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings ((held, second), rows) := by
  cases rows <;> rfl

/-- The reveal keeps the external driver's complete held state. -/
def revealFull4 (held : Held C E) (inbox : Sent C E) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (Spec4 C) (Option (Held C E) × Option (RevealRows C)) := do
  let (next, sent) ← resume4 K circuits settings attempts D n held inbox
  let rows ← targetCopy4 (prssRevealRows D active parts committed sent)
  pure (next, some rows)

/-- Both selected rounds retain the state used by the tail driver. -/
def finishFull4 (state : Option (Held C E)) (data : C.Party → Parts C × List HashOutput) :
    OracleComp (Spec4 C) (Option (Held C E) × Option (RevealRows C)) := do
  let (next, sent, revealed) ← earlyRounds4 K circuits settings attempts D n state data
  match revealed with
  | none => pure (next, none)
  | some sent' => do
      let rows ← targetCopy4 (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
        (prssCommitInbox D data sent) sent')
      pure (next, some rows)

/-- The full setup result includes the seed, without projecting it to rows. -/
def driverFull4 (A : LifetimeAdversary C E) :
    OracleComp (Spec4 C) (Option (Held C E) × Option (RevealRows C)) := do
  let (data, next, sent, revealed) ← early4 K circuits settings attempts D n A
  match revealed with
  | none => pure (next, none)
  | some sent' => do
      let rows ← targetCopy4 (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
        (prssCommitInbox D data sent) sent')
      pure (next, some rows)

omit [Fintype E] [DecidableEq E] in
set_option backward.isDefEq.respectTransparency false in
theorem driverFull4_factor (A : LifetimeAdversary C E) :
    driverFull4 K circuits settings attempts D n A =
      prefix4 K circuits settings attempts D n A >>= fun state =>
        targetCopy4 (prssInitialData D) >>= finishFull4 K circuits settings attempts D n state := by
  unfold driverFull4 early4 finishFull4
  simp only [bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- The external setup has the joint seed, rows and stream table represented by
`driverFull4`, with all local oracle effects unchanged. -/
theorem boundary_full_local (A : LifetimeAdversary C E) (x : C.Party → Keys C) (z : Aux) :
    (setupEarly D (boundaryAdv K circuits settings attempts D n A)
      ((boundaryAdv K circuits settings attempts D n A).start (corruptInputs D x) z) >>= setupReveal D) =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        localHybrid D (driverFull4 K circuits settings attempts D n A) ∅ := by
  rw [boundary_setupEarly, driverFull4, localHybrid_bind]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro r
  rcases r with ⟨⟨data, state, sent, revealed⟩, table⟩
  cases revealed with
  | none => simp only [setupReveal, localHybrid_pure, map_pure]
  | some sent' =>
    rw [localHybrid_bind, localHybrid_target]
    simp only [setupReveal, localHybrid_pure, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- The post-reveal seed reconstructs the complete settled source boundary. -/
theorem driver_tail_reveal (keys : C.Party → Keys C) (h : C.Party)
    (next : Option (Sent C E) → Program C E) (st : LifetimeState C E)
    (tree : ThresholdLeanXmss.Tree) (hc : CountIs (n + 1) st) (rows : RevealRows C)
    (table : StreamCache C) :
    let held : Held C E := ⟨keys, h, next,
      { visibleState st with running := some (tree, ceremonyFuel circuits settings - 2) }⟩
    let steps := fun i => suspendStep (cont K circuits settings keys st tree i) (prssFinishStep i (rows i))
    (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings ((some held, table), some rows) =
      simulateQ tailMap (tail4 K circuits settings attempts D n
        (some ⟨keys, h, some rows, next (some (toCoalition D steps)),
          LifetimeState.settle D { st with running := some (tree, ceremonyFuel circuits settings - 2, steps) }⟩)) := by
  let held : Held C E := ⟨keys, h, next,
    { visibleState st with running := some (tree, ceremonyFuel circuits settings - 2) }⟩
  exact driver_tail_some K circuits settings attempts D n held tree
    (ceremonyFuel circuits settings - 2) rfl hc rows table

/-- Evaluate a four-copy prefix, then inspect its result and actual hash cache. -/
def test4 (prims : Primitives) {α : Type} (p : OracleComp (Spec4 C) α)
    (f : α → HashCache C → ProbComp Bool) (table : StreamCache C) (cache : HashCache C) : ProbComp Bool :=
  eval4 D prims p table cache >>= fun r => f r.1.1 r.2

@[simp] theorem test4_pure (prims : Primitives) {α : Type} (a : α)
    (f : α → HashCache C → ProbComp Bool) (table : StreamCache C) (cache : HashCache C) :
    test4 D prims (pure a) f table cache = f a cache := by
  rw [test4, eval4_pure, pure_bind]

theorem test4_bind (prims : Primitives) {α β : Type} (p : OracleComp (Spec4 C) α)
    (k : α → OracleComp (Spec4 C) β) (f : β → HashCache C → ProbComp Bool)
    (table : StreamCache C) (cache : HashCache C) :
    test4 D prims (p >>= k) f table cache =
      eval4 D prims p table cache >>= fun r => test4 D prims (k r.1.1) f r.1.2 r.2 := by
  simp only [test4, eval4_bind, bind_assoc]

theorem test4_map (prims : Primitives) {α β : Type} (g : α → β) (p : OracleComp (Spec4 C) α)
    (f : β → HashCache C → ProbComp Bool) (table : StreamCache C) (cache : HashCache C) :
    test4 D prims (g <$> p) f table cache = test4 D prims p (fun a => f (g a)) table cache := by
  simp only [test4, eval4_map, bind_map_left]

/-- An observation with zero probability at every supported prefix result stays zero. -/
theorem test4_zero (prims : Primitives) {α : Type} (p : OracleComp (Spec4 C) α)
    (f : α → HashCache C → ProbComp Bool)
    (hf : ∀ a ∈ support p, ∀ cache, Pr[fun b => b = true | f a cache] = 0)
    (table : StreamCache C) (cache : HashCache C) :
    Pr[fun b => b = true | test4 D prims p f table cache] = 0 := by
  rw [test4, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  by_cases hr : r ∈ support (eval4 D prims p table cache)
  · rw [hf r.1.1 (eval4_support D prims p table cache r hr) r.2, mul_zero]
  · rw [(probOutput_eq_zero_iff _ _).mpr hr, zero_mul]

/-- The observation keeps the rows, the complete world continuation and the cache. -/
def sourceKernel
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool)
    (ob : Option (Boundary C E)) : HashCache C → ProbComp Bool :=
  F (ob.bind Boundary.rows) (simulateQ tailMap (tail4 K circuits settings attempts D n ob))

def driverKernel
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool)
    (r : Option (Held C E) × Option (RevealRows C)) : HashCache C → ProbComp Bool :=
  F r.2 ((lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings ((r.1, ∅), r.2))

set_option backward.isDefEq.respectTransparency false in
/-- At a live reveal the source and driver have the same rows and complete
continuation. A source that ends before its next round has no rows to observe. -/
theorem reveal_kernel_le (prims : Primitives)
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool)
    (hF : ∀ p cache, Pr[fun b => b = true | F none p cache] = 0)
    (held : Held C E) (inbox : Sent C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hk : k = cont K circuits settings held.keys st tree)
    (hs : st.running = some (tree, ceremonyFuel circuits settings - 1,
      fun i => suspendStep (k i) (prssRevealStep D active parts committed i)))
    (table : StreamCache C) (cache : HashCache C) :
    Pr[fun b => b = true | test4 D prims
      (revealSegment K circuits settings attempts D n held.keys held.h k active parts committed
        (held.continuation (some inbox)) st)
      (fun r => sourceKernel K circuits settings attempts D n F
        (some ⟨held.keys, held.h, r.1.1, r.1.2, r.2⟩)) table cache] ≤
    Pr[fun b => b = true | test4 D prims
      (revealFull4 K circuits settings attempts D n held inbox active parts committed)
      (driverKernel K circuits settings attempts D n F) table cache] := by
  rw [revealSegment_running K circuits settings attempts D n held.keys held.h k active parts committed
    (held.continuation (some inbox)) st tree _ hc hs,
    runTo_reconstruct K circuits settings attempts D n held.keys held.h
      (held.continuation (some inbox)) st tree _ _ hs, hv]
  unfold revealFull4
  rw [resume4_map]
  simp only [bind_map_left]
  rw [test4_bind, test4_bind]
  apply probEvent_bind_mono
  intro r hr
  have hr' := eval4_support D prims _ table cache r hr
  have hrun : (held.state.restore : LifetimeState C E).running =
      some (tree, ceremonyFuel circuits settings - 1, fun _ => .done none) := by
    rw [← hv]
    simp [VisibleState.restore, visibleState, hs]
  have hf := runTo_frame K circuits settings attempts D n held.keys held.h
    (held.continuation (some inbox)) held.state.restore (by rw [hrun]; simp) r.1.1 hr'
  have hcount : CountIs (n + 1) r.1.1.2 := by
    change r.1.1.2.runCount = n + 1
    rw [hf.1, ← hv]
    exact hc
  have hrunning := hf.2.trans hrun
  have htop := runTo_top K circuits settings attempts D n held.keys held.h
    (held.continuation (some inbox)) held.state.restore (by rw [hrun]; simp) r.1.1 hr'
  have hkt : k = cont K circuits settings held.keys r.1.1.2 tree := by
    rw [hk]
    funext i prss
    simp only [cont, htop, ← hv, VisibleState.restore, visibleState]
  cases hp : r.1.1.1 with
  | done f =>
    simp only [Pause.atRound, test4_pure, sourceKernel, Option.bind_some, hF, zero_le]
  | wait q next =>
    cases q <;> simp only [hp, Pause.atRound, resumed]
    all_goals try { simp only [test4_pure, sourceKernel, Option.bind_some, hF, zero_le] }
    rename_i sent
    rw [test4_bind, test4_bind]
    apply probEvent_bind_mono
    intro rows _
    rw [test4_pure, test4_pure]
    dsimp only [sourceKernel, driverKernel, Option.bind_some]
    have he := driver_tail_reveal K circuits settings attempts D n held.keys held.h next
      r.1.1.2 tree hcount rows.1.1 (∅ : StreamCache C)
    simpa only [hrunning, Option.map_some, Nat.sub_sub, hkt, replaceSteps, cont] using
      (congrArg (fun p => Pr[fun b => b = true | F (some rows.1.1) p rows.2]) he).symm.le

/-- The two-round setup from a live held start, retaining the final seed. -/
def commitFull4 (held : Held C E) (data : C.Party → Parts C × List HashOutput) :
    OracleComp (Spec4 C) (Option (Held C E) × Option (RevealRows C)) := do
  let (state, sent) ← resume4 K circuits settings attempts D n held (prssCommitVisible D data)
  if ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i then pure (state, none) else do
  let (next, sent') ← round4 K circuits settings attempts D n state
    (prssRevealVisible D (prssCommitActive D sent) (fun i => (data i).1))
  let rows ← targetCopy4 (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
    (prssCommitInbox D data sent) sent')
  pure (next, some rows)

omit [Fintype E] [DecidableEq E] in
set_option backward.isDefEq.respectTransparency false in
theorem finishFull4_some (held : Held C E) (data : C.Party → Parts C × List HashOutput) :
    finishFull4 K circuits settings attempts D n (some held) data =
      commitFull4 K circuits settings attempts D n held data := by
  unfold finishFull4 earlyRounds4 commitFull4
  simp only [round4, bind_assoc]
  apply bind_congr
  intro r
  split
  · rw [pure_bind]
  · simp only [bind_assoc, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- The commit comparison feeds both honest views to the same held continuation
and retains its complete reveal seed. -/
theorem commit_kernel_le (prims : Primitives)
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool)
    (hF : ∀ p cache, Pr[fun b => b = true | F none p cache] = 0)
    (held : Held C E) (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hk : k = cont K circuits settings held.keys st tree)
    (hs : st.running = some (tree, ceremonyFuel circuits settings,
      fun i => suspendStep (k i) (prssInitialSteps D data i)))
    (table : StreamCache C) (cache : HashCache C) :
    Pr[fun b => b = true | test4 D prims
      (commitSegment K circuits settings attempts D n held.keys held.h k data
        (held.continuation (some (prssCommitVisible D data))) st)
      (fun r => sourceKernel K circuits settings attempts D n F
        (some ⟨held.keys, held.h, r.1.1, r.1.2, r.2⟩)) table cache] ≤
    Pr[fun b => b = true | test4 D prims
      (commitFull4 K circuits settings attempts D n held data)
      (driverKernel K circuits settings attempts D n F) table cache] := by
  rw [commitSegment_running K circuits settings attempts D n held.keys held.h k data
    (held.continuation (some (prssCommitVisible D data))) st tree _ hc hs,
    runTo_reconstruct K circuits settings attempts D n held.keys held.h
      (held.continuation (some (prssCommitVisible D data))) st tree _ _ hs, hv]
  simp only [bind_map_left]
  unfold commitFull4 resume4
  rw [bind_assoc, test4_bind, test4_bind]
  apply probEvent_bind_mono
  intro r hr
  have hr' := eval4_support D prims _ table cache r hr
  have hrun : (held.state.restore : LifetimeState C E).running =
      some (tree, ceremonyFuel circuits settings, fun _ => .done none) := by
    rw [← hv]
    simp [VisibleState.restore, visibleState, hs]
  have hf := runTo_frame K circuits settings attempts D n held.keys held.h
    (held.continuation (some (prssCommitVisible D data))) held.state.restore
    (by rw [hrun]; simp) r.1.1 hr'
  have hcount : CountIs (n + 1) r.1.1.2 := by
    change r.1.1.2.runCount = n + 1
    rw [hf.1, ← hv]
    exact hc
  have hrunning := hf.2.trans hrun
  have htop := runTo_top K circuits settings attempts D n held.keys held.h
    (held.continuation (some (prssCommitVisible D data))) held.state.restore
    (by rw [hrun]; simp) r.1.1 hr'
  have hkt : k = cont K circuits settings held.keys r.1.1.2 tree := by
    rw [hk]
    funext i prss
    simp only [cont, htop, ← hv, VisibleState.restore, visibleState]
  cases hp : r.1.1.1 with
  | done f =>
    simp only [hp, Pause.atRound, test4_pure, sourceKernel, Option.bind_some, hF, zero_le]
  | wait q next =>
    cases q <;> simp only [hp, Pause.atRound, pure_bind]
    all_goals try { simp only [test4_pure, sourceKernel, Option.bind_some, hF, zero_le] }
    rename_i sent
    have ha : (fun i => (C.parties.any fun j =>
        Msg.isAbort (prssCommitInbox D data sent i j)) = false) = prssCommitActive D sent :=
      funext (prssCommitInbox_active D data sent)
    rw [ha]
    by_cases hall : ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i
    · rw [if_pos hall]
      have hsource := inactive_pastSelected D n
        (replaceSteps (fun i => suspendStep (k i) (prssInitialSteps D data i)) r.1.1.2)
        tree (ceremonyFuel circuits settings - 1) (prssCommitActive D sent) (fun i => (data i).1)
        (prssCommitInbox D data sent) k hcount hall
      rw [test4_zero D prims _ _ (fun out hout cache => ?_) r.1.2 r.2]
      · exact bot_le
      · have he := revealSegment_pastSelected K circuits settings attempts D n held.keys held.h
          k _ _ _ _ _ hsource out hout
        simp only [sourceKernel, Option.bind_some, he, hF]
    · rw [if_neg hall, round4]
      rw [settle_commit_active circuits settings D _ tree data sent k hall, reveal_visible D]
      exact reveal_kernel_le K circuits settings attempts D n prims F hF
        ⟨held.keys, held.h, next,
          { visibleState r.1.1.2 with running := r.1.1.2.running.map fun r => (r.1, r.2.1 - 1) }⟩
        _ k (prssCommitActive D sent) (fun i => (data i).1) (prssCommitInbox D data sent)
        ({ replaceSteps (fun i => suspendStep (k i) (prssInitialSteps D data i)) r.1.1.2 with
          running := some (tree, ceremonyFuel circuits settings - 1,
            fun i => suspendStep (k i) (prssRevealStep D (prssCommitActive D sent)
              (fun j => (data j).1) (prssCommitInbox D data sent) i)) } : LifetimeState C E)
        tree hcount (visible_advance r.1.1.2 tree _ _ _ hrunning) hkt rfl r.1.2 r.2

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Joint setup domination for every observation of rows, the complete
continuation and the actual hash cache that vanishes on empty rows. -/
theorem setup_kernel_le (prims : Primitives) (A : LifetimeAdversary C E)
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool)
    (hF : ∀ p cache, Pr[fun b => b = true | F none p cache] = 0) :
    Pr[fun b => b = true | test4 D prims (setup4 K circuits settings attempts D n A)
      (sourceKernel K circuits settings attempts D n F) ∅ ∅] ≤
    Pr[fun b => b = true | test4 D prims (driverFull4 K circuits settings attempts D n A)
      (driverKernel K circuits settings attempts D n F) ∅ ∅] := by
  rw [setup4_beforeStart, driverFull4_factor, prefix4_eq]
  simp only [bind_map_left]
  rw [test4_bind, test4_bind]
  apply probEvent_bind_mono
  intro r _
  rcases r with ⟨⟨before, table⟩, cache⟩
  cases before with
  | none =>
    simp only [setupAfterStart4, test4_pure, sourceKernel, Option.bind_none, hF, zero_le]
  | some before =>
    unfold setupAfterStart4 holdStart
    cases hp : before.pause with
    | done f =>
      simp only [hp, Pause.atStart, pure_bind, test4_pure, sourceKernel, Option.bind_some, hF, zero_le]
    | wait q next =>
      cases q <;> simp only [hp, Pause.atStart]
      all_goals try { simp only [pure_bind, test4_pure, sourceKernel, Option.bind_some, hF, zero_le] }
      rename_i tree
      by_cases hstart : LifetimeProof.canStart attempts D before.state tree ∧ CountIs n before.state
      · simp only [if_pos hstart, bind_assoc]
        rw [test4_bind, test4_bind]
        apply probEvent_bind_mono
        intro data _
        rw [settle_initial circuits settings D, initial_visible D, finishFull4_some]
        have hc : CountIs (n + 1)
            ({ LifetimeProof.increment before.state tree with
              running := some (tree, ceremonyFuel circuits settings,
                fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                  (prssInitialSteps D data.1.1 i)) } : LifetimeState C E) := by
          change (LifetimeProof.increment before.state tree).runCount = n + 1
          rw [LifetimeProof.increment_runCount]
          exact congrArg (fun x => x + 1) hstart.2
        have htop : (LifetimeProof.increment before.state tree).top = before.state.top := by
          cases tree <;> rfl
        have hk : cont K circuits settings before.keys before.state tree =
            cont K circuits settings before.keys
              ({ LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings,
                  fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                    (prssInitialSteps D data.1.1 i)) } : LifetimeState C E) tree := by
          funext i prss
          simp only [cont, htop]
        simpa only [test4, eval4_bind, eval4_pure, bind_assoc, pure_bind] using
          commit_kernel_le K circuits settings attempts D n prims F hF
            ⟨before.keys, before.h, next, visibleState (E := E)
              { LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }⟩
            data.1.1 (cont K circuits settings before.keys before.state tree)
            ({ LifetimeProof.increment before.state tree with
              running := some (tree, ceremonyFuel circuits settings,
                fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                  (prssInitialSteps D data.1.1 i)) } : LifetimeState C E)
            tree hc rfl hk rfl data.1.2 data.2
      · simp only [if_neg hstart, pure_bind, test4_pure, sourceKernel, Option.bind_some, hF, zero_le]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Port of `aimedFlagQueries_empty` through the actual lazy key interpreter. -/
theorem lazyAimed_empty (prims : Primitives) {α : Type} (p : OracleComp (WorldSpec C) α)
    (s : HashCache C × KeyCache C) (b : Bool) :
    (simulateQ (lazyAimedImpl prims D (fun _ => none)) p).run (s, b) =
      (fun r => (r.1, (r.2, b))) <$> (simulateQ (lazyKeyWorld prims D) p).run s := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    have ht : ¬ AimedCall D (fun _ => none) t := by
      rcases t with ((n | q | x) | p) | (n | q | x)
      all_goals simp [AimedCall, RowKey]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lazyAimedImpl, flagImpl,
      StateT.run_mk, bind_map_left, map_bind, ht, decide_false, Bool.or_false, ih]

/-- The exact apart-keys and lazy-flag observation of a continuation. -/
def flagKernel (prims : Primitives) (rows : Option (RevealRows C))
    (p : OracleComp (WorldSpec C) Bool) (cache : HashCache C) : ProbComp Bool :=
  (fun y => decide (KeysApart D (rowsOf rows)) && y.2.2) <$>
    (simulateQ (lazyAimedImpl prims D (rowsOf rows)) p).run ((cache, ∅), false)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagKernel_probability (prims : Primitives) (rows : Option (RevealRows C))
    (p : OracleComp (WorldSpec C) Bool) (cache : HashCache C) :
    Pr[fun b => b = true | flagKernel D prims rows p cache] =
      Pr[fun y => KeysApart D (rowsOf rows) ∧ y.2.2 = true |
        (simulateQ (lazyAimedImpl prims D (rowsOf rows)) p).run ((cache, ∅), false)] := by
  simp only [flagKernel, probEvent_map, Function.comp_def, Bool.and_eq_true, decide_eq_true_eq]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem flagKernel_none (prims : Primitives) (p : OracleComp (WorldSpec C) Bool) (cache : HashCache C) :
    Pr[fun b => b = true | flagKernel D prims none p cache] = 0 := by
  rw [flagKernel_probability]
  simp only [rowsOf, Option.getD_none, lazyAimed_empty, probEvent_map, Function.comp_def,
    Bool.false_eq_true, and_false, probEvent_False]

omit [Fintype E] [DecidableEq E] in
set_option backward.isDefEq.respectTransparency false in
/-- Erasing only the setup log gives its complete boundary/table/cache output. -/
theorem eval4_setup (prims : Primitives) (A : LifetimeAdversary C E) :
    eval4 D prims (setup4 K circuits settings attempts D n A) ∅ ∅ =
      (fun r => ((r.1.1.1, r.1.1.2), r.2)) <$>
        worldRun prims (worldSetup K circuits settings attempts D n A) := by
  rw [eval4, localHybrid_evaluate]
  simp only [treeSimErase, StateT.run_mk, keygenEraseLog, simulateQ_map, StateT.run_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete source boundary evaluates exactly its joint continuation kernel. -/
theorem source_test_eq (prims : Primitives) (A : LifetimeAdversary C E)
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool) :
    (worldRun prims (worldSetup K circuits settings attempts D n A) >>= fun r =>
      F (r.1.1.1.bind Boundary.rows) (worldTail K circuits settings attempts D n r.1) r.2) =
      test4 D prims (setup4 K circuits settings attempts D n A)
        (sourceKernel K circuits settings attempts D n F) ∅ ∅ := by
  rw [test4, eval4_setup, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro r hr
  have hw : r.1 ∈ support (worldSetup K circuits settings attempts D n A) := by
    apply support_simulateQ_run'_subset (worldAnswer prims) _ ∅
    simp only [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨r, hr, rfl⟩
  have hb : r.1.1.1 ∈ support (setup4 K circuits settings attempts D n A) :=
    support_emulation (hybridImpl D) _ ∅ r.1 hw
  rw [worldTail_eq K circuits settings attempts D n A r.1.1.1 hb]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The external setup retains exactly the seed consumed by the tail kernel. -/
theorem driver_test_eq (prims : Primitives) (A : LifetimeAdversary C E)
    (x : C.Party → Keys C) (z : Aux)
    (F : Option (RevealRows C) → OracleComp (WorldSpec C) Bool → HashCache C → ProbComp Bool) :
    (worldRun prims (setupPrefix D (boundaryAdv K circuits settings attempts D n A) x z) >>= fun r =>
      F r.1.2 ((lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings r.1) r.2) =
      test4 D prims (driverFull4 K circuits settings attempts D n A)
        (driverKernel K circuits settings attempts D n F) ∅ ∅ := by
  rw [worldRun_setupPrefix, boundary_full_local]
  simp only [simulateQ_map, StateT.run_map, bind_map_left, test4, eval4, driverKernel]
  apply bind_congr
  intro r
  rw [driver_tail_table K circuits settings attempts D n _ _ r.1.2 ∅]

set_option backward.isDefEq.respectTransparency false in
/-- The original lifetime tail flag is dominated by the generic driver at the
same selected setup, for every external key input and auxiliary input. -/
theorem lazyRunBoundary_le (prims : Primitives) (A : LifetimeAdversary C E)
    (x : C.Party → Keys C) (z : Aux) :
    Pr[fun y => KeysApart D (rowsAt y.1.1) ∧ y.2.2.2 = true |
      LifetimeTailFlag.lazyRunBoundary K circuits settings attempts D n A prims] ≤
    Pr[fun y => KeysApart D (rowsOf y.1.1.2) ∧ y.2.2.2 = true |
      LifetimeTailFlagBound.lazyBoundaryG prims K circuits settings D
        (boundaryAdv K circuits settings attempts D n A)
        (lifeDriver K circuits settings attempts D n seedOf) x z] := by
  have h := setup_kernel_le K circuits settings attempts D n prims A
    (flagKernel D prims) (flagKernel_none D prims)
  rw [← source_test_eq K circuits settings attempts D n prims A,
    ← driver_test_eq K circuits settings attempts D n prims A x z] at h
  simpa only [LifetimeTailFlag.lazyRunBoundary, LifetimeTailFlagBound.lazyBoundaryG,
    probEvent_bind_eq_tsum, flagKernel_probability, probEvent_map, Function.comp_def, rowsAt] using h

end Continuation

end ThresholdLeanXmssSecurity.LifetimeTailBridge

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.erase_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.erase_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.tailMap_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.tailMap_tail

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.worldTail_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.worldTail_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.driver_tail_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.driver_tail_reveal

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.boundary_full_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.boundary_full_local

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.setup_kernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.setup_kernel_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBridge.lazyRunBoundary_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBridge.lazyRunBoundary_le
