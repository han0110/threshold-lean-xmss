import ThresholdLeanXmssSecurity.Proof.LifetimeSlotTransport
import ThresholdLeanXmssSecurity.Proof.LifetimeForgerReplay

/-!
# Replaying the lifetime dealer table

A hash/PRG computation replays its supported result from any extension of its final
cache, leaving that extension unchanged. `TableRuns` records these supported runs
for the top tree and each bottom tree, including their opening logs.

`TableInv` relates stored tops and active ideal outputs to this concrete table.
The final-world kernel agrees with the table kernel on this invariant, and the
VCVio invariant projection theorem extends that equality to every adaptive tail.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeTableReplay

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

variable {C : Committee}

/-- A supported hash answer is replayed from an extension of its final cache. -/
theorem hashAnswer_rerun_pure (prims : Primitives) (q : Query C)
    {c c' : HashCache C} {z : HashOutput × HashCache C}
    (hz : z ∈ support ((hashAnswer prims q).run c)) (hle : z.2 ≤ c') :
    (hashAnswer prims q).run c' = pure (z.1, c') := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure,
      mem_support_pure_iff] at hz
    subst z
    rw [hashAnswer_of_isFixed prims hm]
    rfl
  · exact hashAnswer_run_cached prims hq (hle (hashAnswer_cached prims hq c z hz))

/-- A supported hash or PRG step replays without changing a larger cache. -/
theorem roImpl_rerun_pure (prims : Primitives) (t : (RoSpec C).Domain)
    {c c' : HashCache C} {z : (RoSpec C).Range t × HashCache C}
    (hz : z ∈ support ((roImpl prims t).run c)) (hle : z.2 ≤ c') :
    (roImpl prims t).run c' = pure (z.1, c') := by
  rcases t with q | x
  · exact hashAnswer_rerun_pure prims q hz hle
  · change z ∈ support ((prgAnswer prims x).run c) at hz
    unfold prgAnswer at hz
    rw [StateT.run_bind] at hz
    simp only [support_bind] at hz
    obtain ⟨w, hw, hz⟩ := Set.mem_iUnion₂.mp hz
    simp only [StateT.run_pure, support_pure] at hz
    subst hz
    change (prgAnswer prims x).run c' = _
    simp only [prgAnswer, StateT.run_bind]
    rw [hashAnswer_rerun_pure prims _ hw hle, pure_bind]
    rfl

/-- Port of pinned leanVM `XmssSecurity/Proof/CacheReplayEval.lean:451`,
`randomOracle_rerun_largerCache_eq_pure_of_mem_support`, to the fixed-`Th`
hash/PRG handler. The fixed branches are pure and PRG maps a stream-key read. -/
theorem roRun_rerun_pure (prims : Primitives) {α : Type}
    (oa : OracleComp (RoSpec C) α) {c c' : HashCache C} {z : α × HashCache C}
    (hz : z ∈ support (roRun prims oa c)) (hle : z.2 ≤ c') :
    roRun prims oa c' = pure (z.1, c') := by
  induction oa using OracleComp.inductionOn generalizing c c' z with
  | pure a =>
      simp only [roRun_pure, mem_support_pure_iff] at hz
      subst z
      rfl
  | query_bind t k ih =>
      change z ∈ support ((simulateQ (roImpl prims) _).run c) at hz
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      have hwle : w.2 ≤ z.2 := (roRun_support prims (k w.1) w.2 z hz).1
      change (simulateQ (roImpl prims) _).run c' = _
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        roImpl_rerun_pure prims t hw (hwle.trans hle), pure_bind]
      exact ih w.1 hz hle

/-- The top argument used when each entry of the dealer table is computed. -/
def tableTop (tables : Tree → Option TreeOutput × List (List (List Bit))) : Tree → TopTree
  | .top => emptyTop
  | .bottom _ => (TreeOutput.topTree (tables .top).1).getD emptyTop

/-- Every table entry records a supported dealer run whose cache lies below `c`. -/
def TableRuns (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (tables : Tree → Option TreeOutput × List (List (List Bit))) (c : HashCache C) : Prop :=
  ∀ tree, ∃ before result,
    result ∈ support (roRun prims
      (dealerCeremony circuits settings parameter seeds (tableTop tables tree) tree) before) ∧
    result.1 = tables tree ∧ result.2 ≤ c

/-- The recorded output and all openings replay without changing the current cache. -/
theorem TableRuns.replay {prims : Primitives} {circuits : Circuits} {settings : Settings}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput}
    {tables : Tree → Option TreeOutput × List (List (List Bit))} {c c' : HashCache C}
    (h : TableRuns prims circuits settings parameter seeds tables c) (hle : c ≤ c') (tree : Tree) :
    roRun prims (dealerCeremony circuits settings parameter seeds (tableTop tables tree) tree) c' =
      pure (tables tree, c') := by
  obtain ⟨before, result, hr, he, hc⟩ := h tree
  simpa only [he] using roRun_rerun_pure prims _ hr (hc.trans hle)

/-- Each result of a sequential map has a supported component run below the final cache. -/
theorem roRun_mapM_forall₂ (prims : Primitives) {α β : Type}
    (f : α → OracleComp (RoSpec C) β) (xs : List α)
    {c : HashCache C} {z : List β × HashCache C}
    (hz : z ∈ support (roRun prims (xs.mapM f) c)) :
    List.Forall₂ (fun a b => ∃ before after,
      (b, after) ∈ support (roRun prims (f a) before) ∧ after ≤ z.2) xs z.1 := by
  induction xs generalizing c z with
  | nil =>
      simp only [List.mapM_nil, roRun_pure, mem_support_pure_iff] at hz
      subst z
      exact .nil
  | cons a xs ih =>
      simp only [List.mapM_cons, roRun_bind, support_bind, Set.mem_iUnion,
        roRun_pure, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w, hw, v, hv, rfl⟩ := hz
      refine .cons ⟨c, w.2, hw, (roRun_support prims _ _ _ hv).1⟩ ?_
      exact ih hv

/-- The concrete dealer-table construction supplies every supported component run. -/
theorem tableRuns_of_support (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    {c : HashCache C}
    {r : (Tree → Option TreeOutput × List (List (List Bit))) × HashCache C}
    (hr : r ∈ support (roRun prims
      (LifetimeForgerReplay.dealerTables circuits settings parameter seeds) c)) :
    TableRuns prims circuits settings parameter seeds r.1 r.2 := by
  simp only [LifetimeForgerReplay.dealerTables, roRun_bind, support_bind, Set.mem_iUnion,
    roRun_pure, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨top, ht, bottoms, hb, rfl⟩ := hr
  let f := fun b => dealerCeremony circuits settings parameter seeds
    ((TreeOutput.topTree top.1.1).getD emptyTop) (.bottom b)
  have hcache := (roRun_support prims ((List.finRange (2 ^ layerHeight)).mapM f)
    top.2 bottoms hb).1
  intro tree
  cases tree with
  | top =>
      exact ⟨c, top, ht, rfl, hcache⟩
  | bottom b =>
      have hall := roRun_mapM_forall₂ prims f (List.finRange (2 ^ layerHeight)) hb
      have hn : b.val < bottoms.1.length := by
        rw [← hall.length_eq]
        simpa only [List.length_finRange] using b.isLt
      have hi : b.val < (List.finRange (2 ^ layerHeight)).length := by
        simpa only [List.length_finRange] using b.isLt
      have h := hall.get hi hn
      have hget : (List.finRange (2 ^ layerHeight)).get ⟨b.val, hi⟩ = b := by
        simp only [List.get_finRange]
        apply Fin.ext
        rfl
      rw [hget] at h
      obtain ⟨before, after, hs, ha⟩ := h
      refine ⟨before, (bottoms.1.getD b.val default, after), ?_, rfl, ha⟩
      simpa only [f, tableTop, List.getD_eq_getElem _ _ hn, List.get_eq_getElem] using hs

/-- Flattening the emulation retains monotonicity of the external hash cache. -/
theorem evalSlot_grows (prims : Primitives) {E α : Type}
    (p : StateT (LifetimeSlots.SlotState C E) (EmulationM C) α)
    (s : LifetimeSlotTransport.Physical C E) (r : α × LifetimeSlotTransport.Physical C E)
    (hr : r ∈ support ((LifetimeSlotTransport.evalSlot prims p).run s)) :
    s.2.2.1 ≤ r.2.2.2.1 := by
  simp only [LifetimeSlotTransport.evalSlot, LifetimeSlotTransport.evalEmulation,
    StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  exact (grows_worldAnswer prims).simulateQ _ _ _ hb

/-- Every stored top is the one from the dealer table. -/
def TopMatches {E : Type} (tables : Tree → Option TreeOutput × List (List (List Bit)))
    (st : LifetimeState C E) : Prop :=
  ∀ i top, st.top i = some top → TreeOutput.topTree (tables .top).1 = some top

/-- The table cache, stored tops and active ideal output agree with the physical state. -/
structure TableInv {E : Type} (tables : Tree → Option TreeOutput × List (List (List Bit)))
    (c : HashCache C) (s : LifetimeSlotTransport.Physical C E) : Prop where
  cache : c ≤ s.2.2.1
  tops : TopMatches tables s.1.1
  active : ∀ tree fuel steps, s.1.1.running = some (tree, fuel, steps) →
    ∃ own, s.1.2 = some (own, some (tables tree).1)

/-- The post-keygen slot state has no stored top or active ceremony. -/
theorem tableInv_initial {E : Type}
    (tables : Tree → Option TreeOutput × List (List (List Bit))) (D : C.Coalition)
    (c : HashCache C) (w : LifetimeSlotTransport.WorldState C) (hc : c ≤ w.2.1) :
    TableInv (E := E) tables c (LifetimeSlotTransport.initialSlot D, w) := by
  refine ⟨hc, ?_, ?_⟩
  · intro i top ht
    cases ht
  · intro tree fuel steps hr
    cases hr

/-- An admitted bottom start supplies exactly the table's top argument. -/
theorem tableTop_of_canStart {E : Type} (attempts : ℕ) (D : C.Coalition)
    (tables : Tree → Option TreeOutput × List (List (List Bit)))
    (st : LifetimeState C E) (h : C.Party) (hh : h ∉ D.1)
    (ht : TopMatches tables st) (b : Fin (2 ^ layerHeight))
    (hs : LifetimeProof.canStart attempts D st (.bottom b)) :
    (st.top h).getD emptyTop = tableTop tables (.bottom b) := by
  have hv := hs.2.2.2.1 h hh
  cases he : st.top h with
  | none => simp [he] at hv
  | some top =>
      have heq := ht h top he
      simp only [tableTop, heq, Option.getD_some]

/-- A top dealer does not read the supplied top tree. -/
theorem dealerCeremony_top_arg (circuits : Circuits) (settings : Settings)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) :
    dealerCeremony circuits settings parameter seeds top .top =
      dealerCeremony circuits settings parameter seeds emptyTop .top := rfl

/-- Settlement of an ideal table output preserves agreement of every stored top. -/
theorem settleIdeal_topMatches {E : Type} (D : C.Coalition)
    (tables : Tree → Option TreeOutput × List (List (List Bit)))
    (st : LifetimeState C E) (tree : Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput)
    (hr : st.running = some (tree, fuel, steps)) (ht : TopMatches tables st) :
    TopMatches tables (LifetimeSlots.settleIdeal D (tables tree).1 st) := by
  simp only [LifetimeSlots.settleIdeal, hr]
  split
  · cases tree with
    | bottom b => exact ht
    | top =>
        intro i top hi
        cases he : st.top i with
        | some old =>
            have hold : old = top := by simpa [he] using hi
            subst top
            exact ht i old he
        | none =>
            by_cases ho : ((steps i).output).isSome
            · simpa [he, ho] using hi
            · simp [he, ho, TreeOutput.topTree] at hi
  · exact ht

/-- An ideal settlement retains its table output if the ceremony remains active. -/
theorem tableInv_settle {E : Type} (D : C.Coalition)
    (tables : Tree → Option TreeOutput × List (List (List Bit)))
    (c : HashCache C) (st : LifetimeState C E) (ht : TopMatches tables st)
    (tree : Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (own : StreamCache C) (w : LifetimeSlotTransport.WorldState C) (hc : c ≤ w.2.1) :
    TableInv tables c
      ((LifetimeSlots.settleIdeal D (tables tree).1
        { st with running := some (tree, fuel, steps) }, some (own, some (tables tree).1)), w) := by
  refine ⟨hc, settleIdeal_topMatches D tables _ tree fuel steps rfl ht, ?_⟩
  intro other fuel' steps' hr
  simp only [LifetimeSlots.settleIdeal] at hr
  split at hr
  · cases tree <;> cases hr
  · cases hr
    exact ⟨own, rfl⟩

/-- Changes to signing bookkeeping leave the table invariant intact. -/
theorem tableInv_frame {E : Type}
    (tables : Tree → Option TreeOutput × List (List (List Bit))) (c : HashCache C)
    (s t : LifetimeSlotTransport.Physical C E) (hs : TableInv tables c s)
    (hc : s.2.2.1 ≤ t.2.2.1) (ht : t.1.1.top = s.1.1.top)
    (hr : t.1.1.running = s.1.1.running) (ha : t.1.2 = s.1.2) : TableInv tables c t := by
  refine ⟨hs.cache.trans hc, ?_, ?_⟩
  · intro i top hi
    exact hs.tops i top (by simpa only [ht] using hi)
  · intro tree fuel steps hi
    rw [ha]
    exact hs.active tree fuel steps (by simpa only [hr] using hi)

/-- A cached dealer call leaves the stream table and observation log unchanged as well. -/
theorem evalEmulation_dealer_replay (prims : Primitives) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
    (result : Option TreeOutput × List (List (List Bit)))
    (w : LifetimeSlotTransport.WorldState C)
    (hr : roRun prims (dealerCeremony circuits settings parameter seeds top tree) w.2.1 =
      pure (result, w.2.1)) :
    (LifetimeSlotTransport.evalEmulation prims
      ((LifetimeSlots.worldEnv (E := Unit) D circuits settings).dealer parameter seeds top tree)).run w =
      pure (result, w) := by
  change (LifetimeSlotTransport.evalEmulation prims (StateT.lift (liftM
    (free (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C)))))).run w = _
  rw [LifetimeSlotTransport.evalEmulation_lift]
  simp only [worldAnswer, simulateQ_free]
  rw [simulateQ_localAnswer_liftComp]
  change (fun r => (r.1, (w.1, r.2, w.2.2))) <$>
    roRun prims (dealerCeremony circuits settings parameter seeds top tree) w.2.1 = _
  rw [hr, map_pure]

section Kernel

variable {E : Type} [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party)
variable (tables : Tree → Option TreeOutput × List (List (List Bit)))

/-- The frozen tail handler with its dealer replaced by the concrete table. -/
def tableHandler : QueryImpl (LifetimeSlotTransport.TailSpec C E)
    (StateT (LifetimeSlots.SlotState C E) (EmulationM C)) :=
  ((fun t => StateT.lift ((lifetimeHybridRoles D 0 0).adversary
      (OracleComp.lift (OracleSpec.query t)))) +
    LifetimeSlots.slotOracles K circuits settings attempts
      (LifetimeForgerReplay.tableEnv circuits settings D tables)
      (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
      (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _)) h) +
    (fun forgery => StateT.mk fun (s : LifetimeSlots.SlotState C E) =>
      (fun b => (b, s)) <$> LifetimeSlotTransport.finish D keys h forgery s.1)

/-- The table handler evaluated with the complete physical state. -/
def tableKernel (prims : Primitives) : QueryImpl (LifetimeSlotTransport.TailSpec C E)
    (StateT (LifetimeSlotTransport.Physical C E) ProbComp) :=
  fun t => LifetimeSlotTransport.evalSlot prims (tableHandler K circuits settings attempts D keys h tables t)

omit [Field E] [Algebra Bit E] in
/-- Every admitted start belongs to an ideal slot in the final world. -/
theorem startSlot_final (st : LifetimeState C E) (tree : Tree)
    (hc : LifetimeProof.canStart attempts D st tree) :
    (LifetimeSlots.startSlot attempts st tree).map
      (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) = some .ideal := by
  cases tree <;> simp only [LifetimeSlots.startSlot, dif_pos hc.2.1, Option.map_some,
    LifetimeForgerReplay.worldMode_final]

/-- The actual final-world kernel and the table kernel agree on table-consistent states. -/
theorem kernel_eq_table (prims : Primitives) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (c : HashCache C)
    (hparam : (keys h).parameter = parameter) (hseeds : honestSeeds D keys = seeds)
    (hh : h ∉ D.1) (hruns : TableRuns prims circuits settings parameter seeds tables c)
    (t : (LifetimeSlotTransport.TailSpec C E).Domain)
    (s : LifetimeSlotTransport.Physical C E) (hs : TableInv tables c s) :
    (LifetimeSlotTransport.rawKernel K circuits settings attempts (lifetimeRuns attempts)
      D keys h prims false t).run s =
      (tableKernel K circuits settings attempts D keys h tables prims t).run s := by
  rcases t with (request | q) | forgery
  · rfl
  · cases q with
    | round sent => rfl
    | sign q => rfl
    | publicKey => rfl
    | start tree =>
        simp only [LifetimeSlotTransport.rawKernel, tableKernel, LifetimeSlotTransport.tailHandler,
          tableHandler,
          LifetimeSlotTransport.evalSlot, StateT.run_mk]
        congr 1
        change (LifetimeSlotTransport.evalEmulation prims
          ((LifetimeSlots.slotOracles K circuits settings attempts
            (LifetimeSlots.worldEnv D circuits settings)
            (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
            (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
            h (.start tree)).run s.1)).run s.2 =
          (LifetimeSlotTransport.evalEmulation prims
          ((LifetimeSlots.slotOracles K circuits settings attempts
            (LifetimeForgerReplay.tableEnv circuits settings D tables)
            (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
            (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
            h (.start tree)).run s.1)).run s.2
        simp only [LifetimeSlots.slotOracles, StateT.run_mk]
        split_ifs with hc
        · have hm := startSlot_final attempts D s.1.1 tree hc
          simp only [hm]
          have hd : roRun prims (dealerCeremony circuits settings (keys h).parameter
              (honestSeeds D keys) ((s.1.1.top h).getD emptyTop) tree) s.2.2.1 =
              pure (tables tree, s.2.2.1) := by
            rw [hparam, hseeds]
            cases tree with
            | top =>
                rw [dealerCeremony_top_arg]
                exact hruns.replay hs.cache .top
            | bottom b =>
                rw [tableTop_of_canStart attempts D tables s.1.1 h hh hs.tops b hc]
                exact hruns.replay hs.cache (.bottom b)
          have he := evalEmulation_dealer_replay prims circuits settings D
            (keys h).parameter (honestSeeds D keys) ((s.1.1.top h).getD emptyTop)
            tree (tables tree) s.2 hd
          simp only [LifetimeSlotTransport.evalEmulation_bind, StateT.run_bind]
          erw [he, pure_bind]
          simp only [LifetimeForgerReplay.tableEnv, LifetimeSlotTransport.evalEmulation_pure,
            StateT.run_pure, pure_bind]
        · rfl
  · rfl

/-- Every table-kernel request preserves the cache and table consistency invariant. -/
theorem tableInv_step (prims : Primitives) (c : HashCache C)
    (t : (LifetimeSlotTransport.TailSpec C E).Domain)
    (s : LifetimeSlotTransport.Physical C E) (hs : TableInv tables c s)
    (r : (LifetimeSlotTransport.TailSpec C E).Range t × LifetimeSlotTransport.Physical C E)
    (hr : r ∈ support ((tableKernel K circuits settings attempts D keys h tables prims t).run s)) :
    TableInv tables c r.2 := by
  have hc := evalSlot_grows prims (tableHandler K circuits settings attempts D keys h tables t) s r hr
  rcases t with (request | q) | forgery
  · change r ∈ support ((LifetimeSlotTransport.evalSlot prims
      (StateT.lift ((lifetimeHybridRoles D 0 0).adversary
        (OracleComp.lift (OracleSpec.query request))))).run s) at hr
    simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk, StateT.run_lift,
      bind_pure_comp, LifetimeSlotTransport.evalEmulation_map, StateT.run_map,
      support_map, Set.mem_image] at hr
    obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
    exact tableInv_frame tables c s _ hs hc rfl rfl rfl
  · cases q with
    | publicKey =>
        change r ∈ support ((LifetimeSlotTransport.evalSlot prims
          (StateT.mk fun st : LifetimeSlots.SlotState C E =>
            pure (st.1.publicKey (keys h).parameter h, st))).run s) at hr
        simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk,
          LifetimeSlotTransport.evalEmulation_pure, StateT.run_pure,
          map_pure, mem_support_pure_iff] at hr
        subst r
        exact hs
    | start tree =>
        change r ∈ support ((LifetimeSlotTransport.evalSlot prims
          (LifetimeSlots.slotOracles K circuits settings attempts
            (LifetimeForgerReplay.tableEnv circuits settings D tables)
            (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
            (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
            h (.start tree))).run s) at hr
        simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk,
          LifetimeSlots.slotOracles] at hr
        split_ifs at hr with can
        · rw [startSlot_final attempts D s.1.1 tree can] at hr
          simp only [LifetimeForgerReplay.tableEnv, pure_bind,
            bind_pure_comp, LifetimeSlotTransport.evalEmulation_map, StateT.run_map,
            support_map, Set.mem_image] at hr
          obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
          apply tableInv_settle D tables c _ _ tree _ _ _ _ (hs.cache.trans hc)
          cases tree <;> exact hs.tops
        · simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind,
            LifetimeProof.canStart] at can hr
          erw [if_pos can] at hr
          simp only [StateT.run_pure, map_pure,
            LifetimeSlotTransport.evalEmulation_pure, StateT.run_pure, map_pure,
            mem_support_pure_iff] at hr
          subst r
          exact hs
    | round sent =>
        change r ∈ support ((LifetimeSlotTransport.evalSlot prims
          (LifetimeSlots.slotOracles K circuits settings attempts
            (LifetimeForgerReplay.tableEnv circuits settings D tables)
            (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
            (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
            h (.round sent))).run s) at hr
        cases running : s.1.1.running with
        | none =>
            simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk,
              LifetimeSlots.slotOracles, running, lifetimeOraclesWith,
              StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
              map_pure, LifetimeSlotTransport.evalEmulation_pure,
              mem_support_pure_iff] at hr
            subst r
            exact hs
        | some active =>
            rcases active with ⟨tree, fuel, steps⟩
            obtain ⟨own, aux⟩ := hs.active tree fuel steps running
            simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk,
              LifetimeSlots.slotOracles, running, aux,
              bind_pure_comp, LifetimeSlotTransport.evalEmulation_map, StateT.run_map,
            support_map, Set.mem_image] at hr
            obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
            exact tableInv_settle D tables c s.1.1 hs.tops tree _ _ _ _ (hs.cache.trans hc)
    | sign query =>
        change r ∈ support ((LifetimeSlotTransport.evalSlot prims
          (LifetimeSlots.slotOracles K circuits settings attempts
            (LifetimeForgerReplay.tableEnv circuits settings D tables)
            (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
            (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _))
            h (.sign query))).run s) at hr
        cases query with
        | corrupt i =>
            simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk, LifetimeSlots.slotOracles,
              lifetimeOraclesWith, StateT.run_pure, map_pure,
              LifetimeSlotTransport.evalEmulation_pure] at hr
            subst r
            exact hs
        | tree b =>
            simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk, LifetimeSlots.slotOracles,
              lifetimeOraclesWith, StateT.run_mk, bind_pure_comp,
              LifetimeSlotTransport.evalEmulation_map, StateT.run_map,
              Functor.map_map, support_map, Set.mem_image] at hr
            obtain ⟨a, ha, rfl⟩ := hr
            exact tableInv_frame tables c s _ hs hc rfl rfl rfl
        | round1 i J e message =>
            simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk, LifetimeSlots.slotOracles,
              lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind] at hr
            split_ifs at hr with blocked <;>
              simp only [StateT.run_pure, StateT.run_set, StateT.run_mk,
                pure_bind, Bool.false_eq_true, if_false, if_true, map_pure, bind_pure_comp,
                LifetimeSlotTransport.evalEmulation_pure, LifetimeSlotTransport.evalEmulation_map,
                StateT.run_map, Functor.map_map, support_map, Set.mem_image] at hr
            · subst r
              exact hs
            · obtain ⟨a, ha, rfl⟩ := hr
              exact tableInv_frame tables c s _ hs hc rfl rfl rfl
        | round2 i J e message parts =>
            simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk, LifetimeSlots.slotOracles,
              lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind] at hr
            split_ifs at hr with blocked <;>
              simp only [StateT.run_pure, StateT.run_set, StateT.run_mk,
                pure_bind, Bool.false_eq_true, if_false, if_true, map_pure, bind_pure_comp,
                LifetimeSlotTransport.evalEmulation_pure, LifetimeSlotTransport.evalEmulation_map,
                StateT.run_map, Functor.map_map, support_map, Set.mem_image] at hr
            · subst r
              exact hs
            · obtain ⟨a, ha, rfl⟩ := hr
              exact tableInv_frame tables c s _ hs hc rfl rfl rfl
  · change r ∈ support ((LifetimeSlotTransport.evalSlot prims
      (StateT.mk fun st : LifetimeSlots.SlotState C E =>
        (fun b => (b, st)) <$> LifetimeSlotTransport.finish D keys h forgery st.1)).run s) at hr
    simp only [LifetimeSlotTransport.evalSlot, StateT.run_mk,
      LifetimeSlotTransport.evalEmulation_map, StateT.run_map,
      support_map, Set.mem_image] at hr
    obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
    exact tableInv_frame tables c s _ hs hc rfl rfl rfl

/-- Adaptive tails replay with their entire physical state unchanged by precomputation. -/
theorem tail_replay (prims : Primitives) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (c : HashCache C)
    (hparam : (keys h).parameter = parameter) (hseeds : honestSeeds D keys = seeds)
    (hh : h ∉ D.1) (hruns : TableRuns prims circuits settings parameter seeds tables c)
    {α : Type} (p : OracleComp (LifetimeSlotTransport.TailSpec C E) α)
    (s : LifetimeSlotTransport.Physical C E) (hs : TableInv tables c s) :
    (simulateQ (LifetimeSlotTransport.rawKernel K circuits settings attempts (lifetimeRuns attempts)
      D keys h prims false) p).run s =
      (simulateQ (tableKernel K circuits settings attempts D keys h tables prims) p).run s := by
  have hk : ∀ t s, TableInv tables c s →
      Prod.map id id <$> (tableKernel K circuits settings attempts D keys h tables prims t).run s =
        (LifetimeSlotTransport.rawKernel K circuits settings attempts (lifetimeRuns attempts)
          D keys h prims false t).run s := by
    intro t s hs
    simpa only [Prod.map_id, id_map] using
      (kernel_eq_table K circuits settings attempts D keys h tables prims parameter seeds c
        hparam hseeds hh hruns t s hs).symm
  have ht := map_run_simulateQ_eq_of_query_map_eq_inv'
    (tableKernel K circuits settings attempts D keys h tables prims)
    (LifetimeSlotTransport.rawKernel K circuits settings attempts (lifetimeRuns attempts)
      D keys h prims false)
    (TableInv tables c) id
    (tableInv_step K circuits settings attempts D keys h tables prims c) hk p s hs
  simpa only [Prod.map_id, id_map, id_eq] using ht.symm

/-- The table kernel is the complete-state evaluation of its slot handler. -/
theorem tableKernel_run (prims : Primitives) {α : Type}
    (p : OracleComp (LifetimeSlotTransport.TailSpec C E) α) :
    simulateQ (tableKernel K circuits settings attempts D keys h tables prims) p =
      LifetimeSlotTransport.evalSlot prims
        (simulateQ (tableHandler K circuits settings attempts D keys h tables) p) := by
  symm
  exact LifetimeEmulatedBudget.hom_simulateQ (LifetimeSlotTransport.evalSlotHom prims) _ _

/-- The original adversary tail is interpreted by the table handler, including its final test. -/
theorem tailProgram_table_run (A : LifetimeAdversary C E) (state : A.keygen.State)
    (s : LifetimeSlots.SlotState C E) :
    (simulateQ (tableHandler K circuits settings attempts D keys h tables)
      (LifetimeSlotTransport.tailProgram A state (keys h).parameter)).run s = (do
    let (forgery, s') ← (simulateQ
      ((fun t => StateT.lift ((lifetimeHybridRoles D 0 0).adversary
        (OracleComp.lift (OracleSpec.query t)))) +
      LifetimeSlots.slotOracles K circuits settings attempts
        (LifetimeForgerReplay.tableEnv circuits settings D tables)
        (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
        (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _)) h)
      (A.run state (keys h).parameter)).run s
    (fun b => (b, s')) <$> LifetimeSlotTransport.finish D keys h forgery s'.1) := by
  unfold LifetimeSlotTransport.tailProgram
  rw [simulateQ_bind, LifetimeEmulatedBudget.simulateQ_comp]
  have hi : (fun t => simulateQ (tableHandler K circuits settings attempts D keys h tables)
      (OracleComp.lift (OracleSpec.query (.inl t)))) =
      ((fun t => StateT.lift ((lifetimeHybridRoles D 0 0).adversary
        (OracleComp.lift (OracleSpec.query t)))) +
      LifetimeSlots.slotOracles K circuits settings attempts
        (LifetimeForgerReplay.tableEnv circuits settings D tables)
        (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D keys
        (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _)) h) := by
    funext t
    rw [simulateQ_spec_query]
    rfl
  erw [hi]
  simp only [StateT.run_bind]
  apply bind_congr
  intro r
  erw [simulateQ_spec_query]
  rfl

/-- The table interpreter's post-keygen execution is its flattened adaptive tail. -/
theorem slotRun_table_tail (A : LifetimeAdversary C E) (state : A.keygen.State)
    (outputs : C.Party → Option (Keys C)) :
    LifetimeSlots.slotRun K circuits settings attempts
      (LifetimeForgerReplay.tableEnv circuits settings D tables)
      (LifetimeSlots.worldMode attempts (lifetimeRuns attempts) false) D A state outputs = (do
    let some h := C.parties.find? (· ∉ D.1) | pure false
    if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure false else do
    let keys := fun i => (outputs i).getD default
    Prod.fst <$> (simulateQ (tableHandler K circuits settings attempts D keys h tables)
      (LifetimeSlotTransport.tailProgram A state (keys h).parameter)).run
        (LifetimeSlotTransport.initialSlot D)) := by
  unfold LifetimeSlots.slotRun
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => rfl
  | some h =>
    dsimp only
    by_cases ho : ∀ i, i ∉ D.1 → (outputs i).isSome
    · rw [if_neg (not_not_intro ho), if_neg (not_not_intro ho), tailProgram_table_run]
      simp only [map_bind, Functor.map_map]
      apply bind_congr
      intro r
      change _ = id <$> _
      rw [id_map]
      rfl
    · rw [if_pos ho, if_pos ho]

end Kernel

/-- Surviving ideal keygen delivery supplies the dealt key to every honest operator. -/
theorem dealtKeygen_keys (D : C.Coalition) (dealing : LifetimeBridge.Dealing C)
    (receivers : Finset C.Party)
    (ready : ∀ i, i ∉ D.1 →
      ((if i ∉ D.1 ∧ i ∈ receivers then some (dealing.2.2 i) else none) : Option (Keys C)).isSome) :
    ∀ i, i ∉ D.1 →
      ((if i ∉ D.1 ∧ i ∈ receivers then some (dealing.2.2 i) else none) : Option (Keys C)).getD
        default = dealing.2.2 i := by
  intro i hi
  have hrec : i ∈ receivers := by
    by_contra hn
    simpa only [hi, hn, and_false, if_false, Option.isSome_none, Bool.false_eq_true] using ready i hi
  simp only [if_pos (show i ∉ D.1 ∧ i ∈ receivers from ⟨hi, hrec⟩), Option.getD_some]

/-- Every sampled dealing uses its sampled public parameter at every operator. -/
theorem prawnsKeyGen_parameter (dealing : LifetimeBridge.Dealing C)
    (hd : dealing ∈ support (prawnsKeyGen (C := C))) (i : C.Party) :
    (dealing.2.2 i).parameter = dealing.1 := by
  obtain ⟨pairs, he⟩ := prawnsKeyGen_support dealing hd
  rw [he]
  rfl

/-- Honest seed selection depends only on the keys delivered to honest operators. -/
theorem honestSeeds_congr (D : C.Coalition) (keys keys' : C.Party → Keys C)
    (he : ∀ i, i ∉ D.1 → keys i = keys' i) : honestSeeds D keys = honestSeeds D keys' := by
  funext T
  unfold honestSeeds
  congr 2
  funext i
  by_cases hi : i ∉ D.1
  · rw [he i hi]
  · simp only [hi, false_and, if_false]

end ThresholdLeanXmssSecurity.LifetimeTableReplay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.roRun_rerun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.roRun_rerun_pure

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.TableRuns.replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.TableRuns.replay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.tableRuns_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.tableRuns_of_support

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.kernel_eq_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.kernel_eq_table

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.tableInv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.tableInv_step

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.tail_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.tail_replay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.slotRun_table_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.slotRun_table_tail

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.prawnsKeyGen_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.prawnsKeyGen_parameter

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTableReplay.honestSeeds_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTableReplay.honestSeeds_congr
