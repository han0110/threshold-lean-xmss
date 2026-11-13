import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Slack

/-! # Pure facts of the O1 slack at the release points

The slack `ReleaseSlackO1` gives each release point of the opening and of the tree an exact
target or a missing concrete term. The completion of one bottom randomizer or of one tree
release point keeps each other clause. A virtual term keeps the slack unless it makes its own
bottom randomizer ready, and a smaller virtual set keeps the slack. A new binding keeps the slack
when the key is not ready, and always when the comparison state drops the virtual terms of the key.

No bottom chain cell and no pad changes in these steps, so `BottomDone.frame` carries the clauses
`bottom_chain` and `crossed_done`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

variable {seeds : C.Term → HashOutput} {s : HiddenKey → Digest} {sig : TsigState C}
  {starts : KeyIndex → ChainIndex → Finset Digit}

/-- Each bottom randomizer has its exact target or a missing concrete term. -/
theorem ReleaseSlackO1.bottom_opening_admissible {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (e : KeyIndex) :
    PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
      firstUnmaterialized seeds data (.randomizer bottomLayer e) ≠ none := by
  rcases h.bottom_opening e with hd | ⟨_, hu⟩ | ⟨_, T, _, hT⟩
  · exact Or.inl hd
  · exact Or.inr (hu.missing h.corrupt_bound)
  · exact Or.inr (firstUnmaterialized_ne_none_of_missing seeds data _ T hT)

/-- Each tree release point has its exact target or a missing concrete term. -/
theorem ReleaseSlackO1.top_admissible {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (b : XmssSecurity.TopIndex)
    (kind : Option ChainIndex) :
    PointDone seeds data (topReleasePoint b kind) (s (topReleaseKey b kind)) ∨
      firstUnmaterialized seeds data (topReleasePoint b kind) ≠ none := by
  cases kind with
  | none => exact (h.top_opening b).imp id (fun hu => hu.missing h.corrupt_bound)
  | some l => exact (h.top_start b l).imp id (fun hu => hu.missing h.corrupt_bound)

/-- The completion of one bottom randomizer keeps each other clause. -/
theorem ReleaseSlackO1.complete_bottom {source source' : SourceState C}
    {data data' : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (e : KeyIndex)
    (hc : ∀ seed point, point ≠ .randomizer bottomLayer e →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : ∀ f, f ≠ e → ∀ T : C.Term,
      ((T, Point.randomizer bottomLayer f) ∈ data'.virtual ↔
        (T, Point.randomizer bottomLayer f) ∈ data.virtual))
    (hp : data'.pads = data.pads)
    (hr : ∀ f, f ≠ e → source'.revealed (.opening bottomLayer f) ≠ none →
      source.revealed (.opening bottomLayer f) ≠ none)
    (hd : PointDone seeds data' (.randomizer bottomLayer e) (s (.opening bottomLayer e))) :
    ReleaseSlackO1 seeds s sig ⟨source', starts⟩ data' := by
  have done : ∀ point target, point ≠ .randomizer bottomLayer e →
      PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hn hh => hh.of_cache_eq (fun T => hc _ _ hn)
  have uncache : ∀ D point, point ≠ .randomizer bottomLayer e →
      LackedUncached seeds D data point → LackedUncached seeds D data' point := by
    intro D point hn hh T hT
    rw [hc _ _ hn]
    exact hh T hT
  have bd : ∀ f l pos, BottomDone seeds s data f l pos → BottomDone seeds s data' f l pos :=
    fun _ _ _ hh => BottomDone.frame hh (fun T => hc _ _ (by simp)) hp
  refine ⟨h.corrupt_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    by_cases he : f = e
    · subst f
      exact Or.inl hd
    · have hn : Point.randomizer bottomLayer f ≠ .randomizer bottomLayer e := by simpa
      rcases h.bottom_opening f with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
      · exact Or.inl (done _ _ hn hh)
      · exact Or.inr (Or.inl ⟨hb, uncache _ _ hn hh⟩)
      · exact Or.inr (Or.inr ⟨hb, T, (hv f he T).not.mpr ht, (hc _ _ hn).trans hh⟩)
  · intro f l pos
    rcases h.bottom_chain f l pos with hh | hh | ⟨hm, m, hb, hn, hh⟩
    · exact Or.inl (bd f l pos hh)
    · exact Or.inr (Or.inl (uncache _ _ (by simp) hh))
    · exact Or.inr (Or.inr ⟨hm, m, hb, hn, uncache _ _ (by simp) hh⟩)
  · intro b
    have hn : Point.randomizer topLayer (topKey b) ≠ .randomizer bottomLayer e := by
      simp [topLayer, bottomLayer]
    exact (h.top_opening b).imp (done _ _ hn) (uncache _ _ hn)
  · intro b l
    exact (h.top_start b l).imp (done _ _ (by simp)) (uncache _ _ (by simp))
  · intro f hf
    by_cases he : f = e
    · subst f
      exact hd
    · exact done _ _ (by simpa) (h.bottom_released f (hr f he hf))
  · intro f m hb hn l pos hcov
    exact bd f l pos (h.crossed_done f m hb hn l pos hcov)

/-- The completion of one point of the tree release keeps each other clause. -/
theorem ReleaseSlackO1.complete_top {source source' : SourceState C}
    {data data' : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (b : XmssSecurity.TopIndex)
    (kind : Option ChainIndex)
    (hc : ∀ seed point, point ≠ topReleasePoint b kind →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads)
    (hr : ∀ e, source'.revealed (.opening bottomLayer e) ≠ none →
      source.revealed (.opening bottomLayer e) ≠ none)
    (hd : PointDone seeds data' (topReleasePoint b kind) (s (topReleaseKey b kind))) :
    ReleaseSlackO1 seeds s sig ⟨source', starts⟩ data' := by
  have done : ∀ point target, point ≠ topReleasePoint b kind →
      PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hn hh => hh.of_cache_eq (fun T => hc _ _ hn)
  have uncache : ∀ D point, point ≠ topReleasePoint b kind →
      LackedUncached seeds D data point → LackedUncached seeds D data' point := by
    intro D point hn hh T hT
    rw [hc _ _ hn]
    exact hh T hT
  have randomizer_ne : ∀ e, Point.randomizer bottomLayer e ≠ topReleasePoint b kind := by
    intro e
    cases kind <;> simp [topReleasePoint, topLayer, bottomLayer]
  have chain_ne : ∀ e l pos, Point.chain bottomLayer e l pos ≠ topReleasePoint b kind := by
    intro e l pos
    cases kind <;> simp [topReleasePoint, topLayer, bottomLayer]
  have bd : ∀ e l pos, BottomDone seeds s data e l pos → BottomDone seeds s data' e l pos :=
    fun e l _ hh => BottomDone.frame hh (fun T => hc _ _ (chain_ne e l _)) hp
  refine ⟨h.corrupt_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases h.bottom_opening e with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
    · exact Or.inl (done _ _ (randomizer_ne e) hh)
    · exact Or.inr (Or.inl ⟨hb, uncache _ _ (randomizer_ne e) hh⟩)
    · exact Or.inr (Or.inr ⟨hb, T, hv ▸ ht, (hc _ _ (randomizer_ne e)).trans hh⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with hh | hh | ⟨hm, m, hb, hn, hh⟩
    · exact Or.inl (bd e l pos hh)
    · exact Or.inr (Or.inl (uncache _ _ (chain_ne e l _) hh))
    · exact Or.inr (Or.inr ⟨hm, m, hb, hn, uncache _ _ (chain_ne e l _) hh⟩)
  · intro f
    by_cases he : Point.randomizer topLayer (topKey f) = topReleasePoint b kind
    · apply Or.inl
      cases kind with
      | none =>
          have hk := (Point.randomizer.inj he).2
          simpa only [topReleasePoint, topReleaseKey, hk] using hd
      | some l => cases he
    · exact (h.top_opening f).imp (done _ _ he) (uncache _ _ he)
  · intro f j
    by_cases he : Point.chain topLayer (topKey f) j (digit 0) = topReleasePoint b kind
    · apply Or.inl
      cases kind with
      | none => cases he
      | some l =>
          obtain ⟨_, hk, hj, _⟩ := Point.chain.inj he
          have hf : f = b := by
            have hh := congrArg (fun e : KeyIndex => e.val) hk
            exact Fin.ext hh
          subst f
          subst j
          exact hd
    · exact (h.top_start f j).imp (done _ _ he) (uncache _ _ he)
  · intro e he
    exact done _ _ (randomizer_ne e) (h.bottom_released e (hr e he))
  · intro e m hb hn l pos hcov
    exact bd e l pos (h.crossed_done e m hb hn l pos hcov)

/-- A virtual term keeps the slack unless it makes its own bottom randomizer ready. -/
theorem ReleaseSlackO1.virtual_unready {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (T : C.Term) (point : Point)
    (hn : ∀ e, point = .randomizer bottomLayer e →
      ¬OpeningReady seeds { data with virtual := insert (T, point) data.virtual } sig e) :
    ReleaseSlackO1 seeds s sig ⟨source, starts⟩
      { data with virtual := insert (T, point) data.virtual } := by
  refine ⟨h.corrupt_bound, ?_, h.bottom_chain, h.top_opening, h.top_start, h.bottom_released,
    h.crossed_done⟩
  intro e
  rcases h.bottom_opening e with hd | ⟨hb, hu⟩ | ⟨hb, U, hv, hc⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨hb, hu⟩)
  · apply Or.inr ∘ Or.inr
    refine ⟨hb, ?_⟩
    by_cases he : point = .randomizer bottomLayer e
    · have hnot : ¬∀ V : C.Term,
          (V, Point.randomizer bottomLayer e) ∈ insert (T, point) data.virtual ∨
            (data.cache (.prf (seeds V) (.randomizer bottomLayer e))).isSome := by
        intro hall
        exact hn e he ⟨hb, hall⟩
      obtain ⟨V, hV⟩ := not_forall.mp hnot
      refine ⟨V, fun hmem => hV (Or.inl hmem), ?_⟩
      cases hh : data.cache (.prf (seeds V) (.randomizer bottomLayer e)) with
      | none => rfl
      | some value => exact (hV (Or.inr (by simp [hh]))).elim
    · refine ⟨U, ?_, hc⟩
      change (U, Point.randomizer bottomLayer e) ∉ insert (T, point) data.virtual
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun heq => he (congrArg Prod.snd heq).symm, hv⟩

/-- The last virtual term at a ready bottom randomizer that is not complete has no cache entry. -/
theorem ReleaseSlackO1.ready_virtual_missing {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (T : C.Term) (e : KeyIndex)
    (hd : ¬PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (hr : OpeningReady seeds
      { data with virtual := insert (T, Point.randomizer bottomLayer e) data.virtual } sig e) :
    data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none := by
  rcases h.bottom_opening e with hh | ⟨hb, _⟩ | ⟨_, U, hv, hc⟩
  · exact (hd hh).elim
  · exact (hr.1 hb).elim
  · rcases hr.2 U with hmem | hcached
    · have heq : U = T := by
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · exact congrArg Prod.fst heq
        · exact (hv hmem).elim
      subst U
      exact hc
    · simp only [hc, Option.isSome_none, Bool.false_eq_true] at hcached

/-- A smaller virtual set keeps the slack. -/
theorem ReleaseSlackO1.virtual_subset {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (virtual : Finset (C.Term × Point))
    (hv : virtual ⊆ data.virtual) :
    ReleaseSlackO1 seeds s sig ⟨source, starts⟩ { data with virtual := virtual } := by
  refine ⟨h.corrupt_bound, ?_, h.bottom_chain, h.top_opening, h.top_start, h.bottom_released,
    h.crossed_done⟩
  intro e
  rcases h.bottom_opening e with hd | ⟨hb, hu⟩ | ⟨hb, T, ht, hc⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl ⟨hb, hu⟩)
  · exact Or.inr (Or.inr ⟨hb, T, fun hm => ht (hv hm), hc⟩)

/-- A new binding keeps the slack when it does not make the key ready. -/
theorem ReleaseSlackO1.bind_unready {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (e : KeyIndex) (message : Message)
    (hfree : sig.bound e = none ∨ sig.bound e = some message)
    (hrel : SigningGuessProof.ReleasedBound sig)
    (hn : ¬OpeningReady seeds data
      { sig with bound := Function.update sig.bound e (some message) } e) :
    ReleaseSlackO1 seeds s { sig with bound := Function.update sig.bound e (some message) }
      ⟨source, starts⟩ data := by
  apply SigningCompilerO1Slack.ReleaseSlackO1.bind h e message hfree hrel
  apply Or.inr
  have hall : ¬∀ T : C.Term, (T, Point.randomizer bottomLayer e) ∈ data.virtual ∨
      (data.cache (.prf (seeds T) (.randomizer bottomLayer e))).isSome :=
    fun ht => hn ⟨by simp, ht⟩
  obtain ⟨T, hT⟩ := not_forall.mp hall
  refine ⟨T, fun hm => hT (Or.inl hm), ?_⟩
  cases hc : data.cache (.prf (seeds T) (.randomizer bottomLayer e)) with
  | none => rfl
  | some value => exact (hT (Or.inr (by simp [hc]))).elim

/-- A new binding keeps the slack of the comparison state without the virtual terms of the key. -/
theorem ReleaseSlackO1.bind_filtered {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (e : KeyIndex) (message : Message)
    (hfree : sig.bound e = none ∨ sig.bound e = some message)
    (hrel : SigningGuessProof.ReleasedBound sig) :
    ReleaseSlackO1 seeds s { sig with bound := Function.update sig.bound e (some message) }
      ⟨source, starts⟩
      { data with virtual := data.virtual.filter (fun tp => tp.2 ≠ .randomizer bottomLayer e) } := by
  apply SigningCompilerO1Slack.ReleaseSlackO1.bind
    (ReleaseSlackO1.virtual_subset h _ (Finset.filter_subset _ _)) e message hfree hrel
  rcases h.bottom_opening e with hd | ⟨_, hu⟩ | ⟨_, T, _, hc⟩
  · exact Or.inl hd
  · obtain ⟨T, hT⟩ := exists_lacked_term sig.corrupt h.corrupt_bound
    exact Or.inr ⟨T, fun hm => (Finset.mem_filter.mp hm).2 rfl, hu T hT⟩
  · exact Or.inr ⟨T, fun hm => (Finset.mem_filter.mp hm).2 rfl, hc⟩

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.bottom_opening_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.bottom_opening_admissible

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.top_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.top_admissible

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.complete_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.complete_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.complete_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.complete_top

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.virtual_unready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.virtual_unready

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.ready_virtual_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.ready_virtual_missing

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.virtual_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.virtual_subset

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.bind_unready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.bind_unready

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.bind_filtered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackPure.ReleaseSlackO1.bind_filtered
