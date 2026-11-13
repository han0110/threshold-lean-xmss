import ThresholdLeanXmssSecurity.Proof.TreeTwinHolderKeys
import ThresholdLeanXmssSecurity.Proof.TreeSimStages

/-!
# Cached entry inputs at honest holders

Holder keys persist when the set of live parties shrinks. The concrete cached
inputs of a batch agree termwise at live honest holders of that term.
-/

open LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeTwinEntryReplay

open TreeTwinHolderKeys

variable {C : Committee} {D : C.Coalition} {live live' : C.Party → Prop}
    {parameter : PublicParameter} {ctx : C.Party → Context C}

theorem holderKeys_antitone (keys : HolderKeys D live parameter ctx)
    (sub : ∀ i, live' i → live i) : HolderKeys D live' parameter ctx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi li
    exact keys.self i hi (sub i li)
  · intro i hi li
    exact keys.parameter_eq i hi (sub i li)
  · intro T i k hiT hkT hi hk li lk
    exact keys.seeds T i k hiT hkT hi hk (sub i li) (sub k lk)
  · intro T i k hiT hkT hi hk li lk
    exact keys.terms T i k hiT hkT hi hk (sub i li) (sub k lk)

/-- The actual cached batch inputs, at the same cache and job list. -/
theorem wiresAt_cachedInputs (keys : HolderKeys D live parameter ctx)
    (base : HashCache C) (jobs : List Job) :
    ∀ T i k, i ∈ C.holders T → k ∈ C.holders T →
      i ∉ D.1 → k ∉ D.1 → live i → live k →
      TreeCheckWalkConsistent.wiresAt T (jobs.map (treeStagesCachedInputs base (ctx i))) =
        TreeCheckWalkConsistent.wiresAt T (jobs.map (treeStagesCachedInputs base (ctx k))) := by
  intro T i k hiT hkT hi hk li lk
  -- Same termwise map calculation as TreeTwinHolderKeys.inputsAgree_of_replay.
  unfold TreeCheckWalkConsistent.wiresAt
  simp only [List.map_map]
  apply List.map_congr_left
  intro job _
  simp only [Function.comp_apply, treeStagesCachedInputs, keys.self i hi li,
    keys.self k hk lk, if_pos hiT, if_pos hkT, inputBits]
  rw [keys.seeds T i k hiT hkT hi hk li lk]

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntryReplay.holderKeys_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holderKeys_antitone

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntryReplay.wiresAt_cachedInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wiresAt_cachedInputs

end TreeTwinEntryReplay
end ThresholdLeanXmssSecurity
