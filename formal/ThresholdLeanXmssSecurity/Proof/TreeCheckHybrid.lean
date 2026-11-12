import ThresholdLeanXmssSecurity.Proof.TreeCheckWalk

/-!
# Cache accounting at a hybrid check cut

The check cache certificate tracks coin inputs and expansion queries. Other
counted queries can be removed from its finite `seen` set without changing the
hybrid experiment. A recorded commitment outside that projection reserves one
query for the counted setup opening.

The pinned and current leanVM proof trees were searched for this cache
projection. The `SoundCache` and prior-coin conditions are specific to the
threshold check.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E α : Type}

/-- Only these public queries enter the hybrid check's `seen` certificate. -/
def TreeCheckSeenQuery : Query C → Prop
  | .coinKey _ _ _ | .expand _ _ => True
  | _ => False

def treeCheckSeen (seen : Finset (Query C)) : Finset (Query C) :=
  seen.filter TreeCheckSeenQuery

/-- Removing other domains preserves the original sound-cache condition. -/
theorem treeCheck_soundCache_filter {L : ℕ} {cache : HashCache C}
    {seen : Finset (Query C)} {keys : Finset HashOutput}
    (sound : SoundCache L cache seen keys) : SoundCache L cache (treeCheckSeen seen) keys := by
  constructor
  · intro tag label bits bound cached
    exact Finset.mem_filter.mpr ⟨sound.1 tag label bits bound cached, trivial⟩
  · intro key index cached
    rcases sound.2 key index cached with known | seen
    · exact Or.inl known
    · exact Or.inr (Finset.mem_filter.mpr ⟨seen, trivial⟩)

/-- A counted point in a different domain leaves one query outside the
check's projection, even when other queries repeat. -/
theorem treeCheck_seen_reserve (seen : Finset (Query C)) (q : Query C)
    (mem : q ∈ seen) (outside : ¬ TreeCheckSeenQuery q) :
    (treeCheckSeen seen).card + 1 ≤ seen.card := by
  have subset : treeCheckSeen seen ⊆ seen.erase q := by
    intro x hx
    obtain ⟨member, relevant⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨fun eq => outside (eq ▸ relevant), member⟩
  have bound := Nat.add_le_add_right (Finset.card_le_card subset) 1
  rwa [Finset.card_erase_add_one mem] at bound

/-- The initial and final sound-cache certificates differ only in the
actual query projection. The prior keys keep their original cached witnesses. -/
theorem treeCheck_local_cache (prims : Primitives) (program : OracleComp (LocalSpec C) α)
    (cost : ℕ) (bounded : IsQueryBoundP program Counted cost)
    (L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (sound : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (out : α × HashCache C) (run : out ∈ support ((simulateQ (localAnswer prims) program).run cache)) :
    ∃ seen', SoundCache L out.2 seen' keys ∧ TreeSimCheckPriorKeys L out.2 keys ∧
      (∀ q ∈ seen', TreeCheckSeenQuery q) ∧ seen'.card ≤ (treeCheckSeen seen).card + cost := by
  obtain ⟨raw, sound', card⟩ := (treeCheck_soundCache_filter sound).local prims program cost bounded out run
  refine ⟨treeCheckSeen raw, treeCheck_soundCache_filter sound',
    prior.mono le_rfl ((grows_localAnswer prims).simulateQ program cache out run), ?_, ?_⟩
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans card

/-- A newly cached, irrelevant query consumes one unit of a local prefix's
budget. Its cache entry supplies the witness in the actual projected trace. -/
theorem treeCheck_local_reserve (prims : Primitives) (program : OracleComp (LocalSpec C) α)
    (cost : ℕ) (bounded : IsQueryBoundP program Counted cost)
    (L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (sound : SoundCache L cache seen keys) (prior : TreeSimCheckPriorKeys L cache keys)
    (out : α × HashCache C) (run : out ∈ support ((simulateQ (localAnswer prims) program).run cache))
    (q : Query C) (outside : ¬ TreeCheckSeenQuery q) (fresh : cache q = none) (cached : out.2 q ≠ none) :
    ∃ seen', SoundCache L out.2 seen' keys ∧ TreeSimCheckPriorKeys L out.2 keys ∧
      seen'.card + 1 ≤ (treeCheckSeen seen).card + cost := by
  rw [← projectQueries_forget (localAnswer prims) soundQueryProjection program cache [], support_map] at run
  obtain ⟨trace, traced, equal⟩ := run
  cases equal
  have entries := projectQueries_sound_entries prims program (fun k => cache k ≠ none) cache []
    (fun _ h => Or.inl h) trace traced
  have length := projectQueries_length (localAnswer prims) Counted soundQueryProjection
    soundQueryProjection_counted bounded cache [] traced
  let raw := treeCheckSeen seen ∪ trace.2.2.toFinset
  have sound' : SoundCache L trace.2.1 raw keys := by
    constructor
    · intro tag label bits bound present
      rcases entries _ present with old | new
      · exact Finset.mem_union_left _ ((treeCheck_soundCache_filter sound).1 tag label bits bound old)
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr new)
    · intro key index present
      rcases entries _ present with old | new
      · exact (sound.2 key index old).imp_right fun h =>
          Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, trivial⟩)
      · exact Or.inr (Finset.mem_union_right _ (List.mem_toFinset.mpr new))
  have qmem : q ∈ raw := by
    rcases entries q cached with old | new
    · exact (old fresh).elim
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr new)
  have rawBound : raw.card ≤ (treeCheckSeen seen).card + cost :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left
      ((List.toFinset_card_le _).trans (by simpa using length)) _)
  have original : (trace.1, trace.2.1) ∈ support ((simulateQ (localAnswer prims) program).run cache) := by
    rw [← projectQueries_forget (localAnswer prims) soundQueryProjection program cache [], support_map]
    exact ⟨trace, traced, rfl⟩
  exact ⟨treeCheckSeen raw, treeCheck_soundCache_filter sound',
    prior.mono le_rfl ((grows_localAnswer prims).simulateQ program cache _ original),
    (treeCheck_seen_reserve raw q qmem outside).trans rawBound⟩

section Hybrid

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Only the ghost `seen` set changes; the experiment and its starting
cache retain every original entry. -/
def TreeCheckHybrid.restrictSeen (h : TreeCheckHybrid C E) : TreeCheckHybrid C E :=
  { h with seen := treeCheckSeen h.seen }

theorem TreeCheckHybrid.event_restrictSeen (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (h : TreeCheckHybrid C E) :
    h.restrictSeen.event prims K D = h.event prims K D := rfl

theorem TreeCheckHybrid.restrictSeen_budget (h : TreeCheckHybrid C E) (q : ℕ)
    (accounted : h.seen.card + (2 * halvings h.counts.sum + 5) * h.step ≤ q)
    (reserved : ∃ point ∈ h.seen, ¬ TreeCheckSeenQuery point) :
    h.restrictSeen.seen.card + (2 * halvings h.restrictSeen.counts.sum + 5) *
      h.restrictSeen.step + 1 ≤ q := by
  obtain ⟨point, mem, outside⟩ := reserved
  have card := treeCheck_seen_reserve h.seen point mem outside
  change (treeCheckSeen h.seen).card + (2 * halvings h.counts.sum + 5) * h.step + 1 ≤ q
  omega

/-- Restrict the ghost certificate at every cut state, keeping the exact
source split and continuation. -/
def TreeCheckCountedCutData.restrictSeen {A : Adversary C E (Keys C) PEmpty PEmpty}
    (cut : TreeCheckCountedCutData A) : TreeCheckCountedCutData A :=
  { cut with hybrid := fun s => (cut.hybrid s).restrictSeen }

namespace TreeCheckCountedCutData

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
  (j : Fin (treeBatches settings tree)) (cut : TreeCheckCountedCutData A)

theorem restrictSeen_cache (cache : cut.Cache prims K circuits settings top tree D A x z j) :
    cut.restrictSeen.Cache prims K circuits settings top tree D A x z j := by
  intro s hs live
  exact treeCheck_soundCache_filter (cache s hs live)

/-- The transport inequality is literally unchanged by removing irrelevant
points from the certificate. This transformation incurs no probability loss. -/
theorem restrictSeen_transport :
    cut.restrictSeen.Transport prims K circuits settings top tree D A x z j ↔
      cut.Transport prims K circuits settings top tree D A x z j := Iff.rfl

/-- At the original live states, the counted point outside the projection
pays the exact extra query required by `Budget`. -/
theorem restrictSeen_budget (q : ℕ)
    (accounted : ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
      (cut.hybrid s).seen.card + (2 * halvings (cut.count s) + 5) * (cut.hybrid s).step ≤ q)
    (reserved : ∀ s ∈ support cut.pre, cut.Live prims K circuits settings top tree D A x z j s →
      ∃ point ∈ (cut.hybrid s).seen, ¬ TreeCheckSeenQuery point) :
    cut.restrictSeen.Budget prims K circuits settings top tree D A x z q j := by
  intro s hs live
  obtain ⟨point, mem, outside⟩ := reserved s hs live
  have card := treeCheck_seen_reserve (cut.hybrid s).seen point mem outside
  have bound := accounted s hs live
  change (treeCheckSeen (cut.hybrid s).seen).card +
    (2 * halvings (cut.count s) + 5) * (cut.hybrid s).step + 1 ≤ q
  omega

/-- The five hybrid clauses of the original counted cut, at the same cut,
live states, query budget and branch index. -/
def HybridParts (q : ℕ) : Prop :=
  cut.Queries prims K circuits settings top tree D A x z j ∧
  cut.Cache prims K circuits settings top tree D A x z j ∧
  cut.Prior prims K circuits settings top tree D A x z j ∧
  cut.Budget prims K circuits settings top tree D A x z q j ∧
  cut.Transport prims K circuits settings top tree D A x z j

end TreeCheckCountedCutData
end Hybrid

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_local_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_local_cache

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_local_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_local_reserve

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCountedCutData.restrictSeen_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckCountedCutData.restrictSeen_cache

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCountedCutData.restrictSeen_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckCountedCutData.restrictSeen_transport

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCountedCutData.restrictSeen_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckCountedCutData.restrictSeen_budget

end ThresholdLeanXmssSecurity
