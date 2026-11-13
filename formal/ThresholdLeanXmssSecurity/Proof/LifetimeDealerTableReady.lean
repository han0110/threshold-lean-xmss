import ThresholdLeanXmssSecurity.Proof.LifetimeTopLog
import ThresholdLeanXmssSecurity.Proof.LifetimeBottomLog
import ThresholdLeanXmssSecurity.Proof.LifetimeSigningFrame

/-! # Concrete readiness of the supported dealer table

The original dealer-table prefix determines its top and bottom outputs, complete
opening logs, and reference/randomizer replays from every larger cache. Starting
from the empty cache, this prefix leaves every keygen derivation entry empty.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeDealerTableReady
open LifetimeDealerLog LifetimeTableReplay
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {C : Committee}

abbrev Tables := Tree → Option TreeOutput × List (List (List Bit))
abbrev BottomIndex := Fin (2 ^ layerHeight)

/-- Exact outputs and full logs, with reference replays at every cache extension. -/
structure Ready (prims : Primitives) (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (tables : Tables) (c : HashCache C)
    (top : TopTree) (bottom : BottomIndex → BottomTree) (rho : BottomIndex → Digest) : Prop where
  top_out : (tables .top).1 = some (.top top)
  bottom_out : ∀ b, (tables (.bottom b)).1 = some (.bottom (bottom b))
  top_log : (tables .top).2 = treeOpenings settings 0 .top (.top top)
  bottom_log : ∀ b, (tables (.bottom b)).2 =
    treeOpenings settings (rho b) (.bottom b) (.bottom (bottom b))
  reference_replay : ∀ tree c', c ≤ c' →
    roRun prims (referenceTree tweakable (prfValue seeds) parameter
      (tableTop tables tree) tree) c' = pure ((tables tree).1, c')
  rho_replay : ∀ b c', c ≤ c' →
    roRun prims (prfValue seeds (.randomizer topLayer (topKey b))) c' = pure (rho b, c')

/-- Readiness is forced by a supported successful run of the original table prefix. -/
theorem ready_of_support (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (before : HashCache C) (tables : Tables) (c : HashCache C)
    (ht : (tables, c) ∈ support
      (roRun prims (LifetimeForgerReplay.dealerTables circuits settings parameter seeds) before))
    (good : LifetimeForgerReplay.searchFails tables = false) :
    ∃ top bottom rho, Ready prims settings parameter seeds tables c top bottom rho := by
  have runs := tableRuns_of_support prims circuits settings parameter seeds ht
  obtain ⟨start, result, hr, he, _⟩ := runs .top
  rw [dealer_reference_log prims circuits settings hc] at hr
  obtain ⟨top, htop, hlog⟩ :=
    LifetimeTopLog.reference_top_log prims settings hsize parameter seeds _ start result hr
  rw [he] at htop hlog
  have bottoms : ∀ b : BottomIndex, ∃ (out : BottomTree) (rho : Digest),
      (tables (.bottom b)).1 = some (.bottom out) ∧
      (tables (.bottom b)).2 = treeOpenings settings rho (.bottom b) (.bottom out) ∧
      ∀ c', c ≤ c' →
        roRun prims (prfValue seeds (.randomizer topLayer (topKey b))) c' = pure (rho, c') := by
    intro b
    obtain ⟨start, result, hr, he, hle⟩ := runs (.bottom b)
    have hout : result.1.1 ≠ none := by
      intro hn
      have bad : LifetimeForgerReplay.searchFails tables = true := by
        apply List.any_eq_true.mpr
        refine ⟨b, List.mem_finRange b, ?_⟩
        change ((tables, c).1 (.bottom b)).1.isNone = true
        rw [← he, hn]
        rfl
      rw [good] at bad
      contradiction
    rw [dealer_reference_log prims circuits settings hc] at hr
    obtain ⟨out, rho, ho, hl, replay⟩ :=
      LifetimeBottomLog.reference_bottom_log prims settings hsize parameter seeds _ b
        start result hr hout
    refine ⟨out, rho, ?_, ?_, fun c' hc' => replay c' (hle.trans hc')⟩
    · simpa only [he] using ho
    · simpa only [he] using hl
  choose bottom rho hout hlogs hreplay using bottoms
  refine ⟨top, bottom, rho, htop, hout, hlog, hlogs, ?_, hreplay⟩
  intro tree c' hle
  rw [← roRun_dealer prims circuits settings hc hsize, roRun_map,
    runs.replay hle tree, map_pure]

/-- The actual table prefix from the empty cache leaves keygen derivation entries empty. -/
theorem table_noKeygen (circuits : Circuits) (settings : Settings) (prims : Primitives)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (tables : Tables) (c : HashCache C)
    (ht : (tables, c) ∈ support (roRun prims
      (LifetimeForgerReplay.dealerTables circuits settings parameter seeds) ∅)) :
    ∀ q, KeygenPoint q → c q = none := by
  have frame := LifetimeSigningFrame.frames_dealerProgram prims _
    (LifetimePrecomputeSwap.free_dealerTables_dealerQuery circuits settings parameter seeds)
    (∅ : HashCache C) (∅ : HashCache C)
  have hempty : mergeOn (fun q : Query C => ¬ KeygenPoint q) ∅ ∅ = ∅ := by
    funext q
    simp only [mergeOn, ite_self]
  simp only [simulateQ_free, localRun_liftComp, hempty] at frame
  rw [← frame, support_map] at ht
  obtain ⟨result, _, he⟩ := ht
  have hc := congrArg Prod.snd he
  intro q hq
  have h := congrFun hc q
  simpa only [mergeOn, hq, not_true_eq_false, if_false, QueryCache.empty_apply] using h.symm

end ThresholdLeanXmssSecurity.LifetimeDealerTableReady

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerTableReady.ready_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerTableReady.ready_of_support

/-- info: 'ThresholdLeanXmssSecurity.LifetimeDealerTableReady.table_noKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeDealerTableReady.table_noKeygen
