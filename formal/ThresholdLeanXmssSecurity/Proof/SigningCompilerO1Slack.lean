import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Release
import ThresholdLeanXmssSecurity.Proof.SigningSelection

/-! # The slack of the O1 source with the record of the signer

The invariant of the handlers is `GuardedReleaseInvariantS`. It is `GuardedReleaseInvariantO1`
with one more clause, that each release record is at the bound message of its key.

The slack `ReleaseSlackO1` takes the signing state of the coalition as a parameter. This file
gives the working invariants at a fixed coalition state and the pure facts of the slack. A read
of a held term at a recorded chain point keeps the slack. A new binding keeps the slack, because
each release record is at its bound message. A new digit below the threshold keeps the slack. The
record of a signer keeps the slack below the threshold, and at the threshold when each covered
position of the key is complete.

`round2Callback` is the callback of round 2 of the O1 source, and `sourceRound2O1_eq` states
round 2 with this callback by name.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Slack
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

/-! ## Definitions -/

/-- The guarded release invariant of the O1 source, with each release record at the bound message
of its key. -/
def GuardedReleaseInvariantS (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (src : SourceStateO1 C) (backend : CappedCompilerState C) : Prop :=
  GuardedReleaseInvariantO1 seeds s src backend ∧
    SigningGuessProof.ReleasedBound src.base.signing

/-- The release invariant at the coalition state `sig`, for a base source state that has the bound
map of `sig`. -/
def LinkedInvariant (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (source : SourceState C)
    (backend : CappedCompilerState C) : Prop :=
  source.signing.bound = sig.bound ∧ BaseInvariant seeds s sig starts source backend

/-- A PRF read that keeps the slack at the coalition state `sig`. The term is held by a corrupt
operator, or its cell is cached, or the point is a bound bottom randomizer, or the point is a
recorded bottom chain point and a signer of its key holds the term. -/
def ReadAllowedO1 (seeds : C.Term → HashOutput) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (data : DeferredState C) (query : Query C) :
    Prop :=
  ∀ T point, query = .prf (seeds T) point →
    TprfSecurityProof.Revealed sig.corrupt (.inl T) ∨
      data.cache (.prf (seeds T) point) ≠ none ∨
      (∃ e, point = .randomizer bottomLayer e ∧ sig.bound e ≠ none) ∨
      ∃ (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) (m : Message),
        point = .chain bottomLayer e l (chainStepDigit pos) ∧
          chainStepDigit pos ∈ starts e l ∧ sig.bound e = some m ∧
          TprfSecurityProof.Revealed (signersAt sig e m) (.inl T)

/-- The point is a recorded bottom chain point at a key where operator `i` is a signer. -/
def HeldReadable (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)
    (i : C.Party) (point : Point) : Prop :=
  ∃ (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) (m : Message),
    point = .chain bottomLayer e l (chainStepDigit pos) ∧
      chainStepDigit pos ∈ starts e l ∧ sig.bound e = some m ∧ i ∈ signersAt sig e m

/-- The joint invariant of an honest computation that reads PRF cells at one point only. -/
def ReadInvariantO1 (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (point : Point) (source : SourceState C)
    (backend : CappedCompilerState C) : Prop :=
  LinkedInvariant seeds s sig starts source backend ∧
    PointReadable seeds source backend.1.1.data point

/-- Preservation of a joint invariant by the O1 source over the capped backend. -/
def SourcePreservesO1 {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ)
    (s : HiddenKey → Digest) (I : SourceStateO1 C → CappedCompilerState C → Prop)
    (oa : SourceMO1 C α) : Prop :=
  ∀ src backend, I src backend →
    ∀ r : (α × SourceStateO1 C) × CappedCompilerState C,
      r ∈ support (runSourceO1 P seeds q s oa src backend) → I r.1.2 r.2

/-- The fields of the O1 source that hold on every run. The pending answers are valid, each stored
tree has the shape of the tree release, the hidden flag has a fixed value, and each release record
is at the bound message of its key. -/
def ControlInvariantO1 (flag : Bool) (src : SourceStateO1 C)
    (backend : CappedCompilerState C) : Prop :=
  PendingValid backend.1.1.data ∧ StoredTopShape src.base ∧ src.base.hiddenFlag = flag ∧
    SigningGuessProof.ReleasedBound src.base.signing

/-! ## Pure facts of the signing state -/

section SigningState

/-- The signing state after signer `i` releases at key `e`. -/
abbrev withRecord (st : TsigState C) (e : KeyIndex) (message : Message) (i : C.Party) :
    TsigState C :=
  { st with released := st.released ++ [(e, message, i)] }

theorem signersAt_withRecord_subset (st : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) (f : KeyIndex) (m : Message) :
    signersAt st f m ⊆ signersAt (withRecord st e message i) f m := by
  intro j hj
  simp only [signersAt, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_append] at hj ⊢
  rcases hj with hj | ⟨r, ⟨hr, hc⟩, rfl⟩
  · exact Or.inl hj
  · exact Or.inr ⟨r, ⟨Or.inl hr, hc⟩, rfl⟩

theorem signersAt_withRecord_of_ne (st : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) (f : KeyIndex) (m : Message) (h : ¬(f = e ∧ m = message)) :
    signersAt (withRecord st e message i) f m = signersAt st f m := by
  ext j
  simp only [signersAt, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_append, List.mem_singleton, decide_eq_true_eq]
  constructor
  · rintro (hj | ⟨r, ⟨hr | hr, hc⟩, rfl⟩)
    · exact Or.inl hj
    · exact Or.inr ⟨r, ⟨hr, hc⟩, rfl⟩
    · subst r
      exact (h ⟨hc.1.symm, hc.2.symm⟩).elim
  · rintro (hj | ⟨r, ⟨hr, hc⟩, rfl⟩)
    · exact Or.inl hj
    · exact Or.inr ⟨r, ⟨Or.inl hr, hc⟩, rfl⟩

theorem mem_signersAt_withRecord (st : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) : i ∈ signersAt (withRecord st e message i) e message := by
  simp only [signersAt, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_append, List.mem_singleton, decide_eq_true_eq]
  exact Or.inr ⟨(e, message, i), ⟨Or.inr rfl, rfl, rfl⟩, rfl⟩

theorem releasedBound_withRecord (st : TsigState C) (e : KeyIndex) (message : Message)
    (i : C.Party) (h : SigningGuessProof.ReleasedBound st) (hb : st.bound e = some message) :
    SigningGuessProof.ReleasedBound (withRecord st e message i) := by
  intro f m j hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact h f m j hold
  · have ht : (f, m, j) = (e, message, i) := List.mem_singleton.mp hnew
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj ht
    obtain ⟨rfl, _⟩ := Prod.mk.inj hrest
    exact hb

theorem releasedBound_bind (st : TsigState C) (e : KeyIndex) (message : Message)
    (h : SigningGuessProof.ReleasedBound st)
    (hfree : st.bound e = none ∨ st.bound e = some message) :
    SigningGuessProof.ReleasedBound
      { st with bound := Function.update st.bound e (some message) } := by
  intro f m j hm
  have hold := h f m j hm
  by_cases hf : f = e
  · subst f
    rcases hfree with hn | hs
    · rw [hn] at hold
      cases hold
    · rw [hs] at hold
      simpa using hold
  · simpa [Function.update_of_ne hf] using hold

theorem releasedBound_corrupt (st : TsigState C) (D : Finset C.Party)
    (h : SigningGuessProof.ReleasedBound st) :
    SigningGuessProof.ReleasedBound { st with corrupt := D } := h

end SigningState

/-! ## Pure facts of the slack -/

section Pure
variable {seeds : C.Term → HashOutput} {s : HiddenKey → Digest} {sig : TsigState C}
  {starts : KeyIndex → ChainIndex → Finset Digit}

theorem revealed_mono {D E : Finset C.Party} {T : C.Term} (hDE : D ⊆ E)
    (h : TprfSecurityProof.Revealed D (.inl T)) : TprfSecurityProof.Revealed E (.inl T) := by
  obtain ⟨i, hi, hh⟩ := h
  exact ⟨i, hDE hi, hh⟩

/-- A permitted read keeps the slack. A read that closes the readiness of a bottom randomizer needs
a complete opening point. -/
theorem ReleaseSlackO1.read {source : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (query : Query C)
    (ha : ReadAllowedO1 seeds sig starts data query)
    (hready : ∀ e, (∃ seed, query = .prf seed (.randomizer bottomLayer e)) →
      PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
        ¬ReadyAfter seeds data sig e query)
    (hc : data.cache ≤ data'.cache)
    (hf : ∀ seed point, query ≠ .prf seed point →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads) :
    ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data' := by
  have hu (point : Point) (unbound : ∀ e, point = .randomizer bottomLayer e → sig.bound e = none)
      (nochain : ∀ e l (pos : XmssSecurity.ChainStep),
        point ≠ .chain bottomLayer e l (chainStepDigit pos))
      (old : LackedUncached seeds sig.corrupt data point) :
      LackedUncached seeds sig.corrupt data' point := by
    intro T hT
    have hneq : query ≠ .prf (seeds T) point := by
      intro he
      rcases ha T point he with ht | ht | ⟨e, he', hb⟩ | ⟨e, l, pos, m, hp', _⟩
      · exact hT ht
      · exact ht (old T hT)
      · exact hb (unbound e he')
      · exact nochain e l pos hp'
    exact (hf _ _ hneq).trans (old T hT)
  have hdone : ∀ e l pos, BottomDone seeds s data e l pos → BottomDone seeds s data' e l pos := by
    intro e l pos hd
    refine ⟨by simpa only [hp] using hd.1, ?_⟩
    simpa only [bottomReleaseTarget, hp] using hd.2.mono hc
  have coalition : ∀ e l (pos : XmssSecurity.ChainStep) m, sig.bound e = some m →
      LackedUncached seeds (signersAt sig e m) data (.chain bottomLayer e l (chainStepDigit pos)) →
      LackedUncached seeds (signersAt sig e m) data'
        (.chain bottomLayer e l (chainStepDigit pos)) := by
    intro e l pos m hb old T hT
    have hneq : query ≠ .prf (seeds T) (.chain bottomLayer e l (chainStepDigit pos)) := by
      intro he
      rcases ha T _ he with ht | ht | ⟨f, hf', _⟩ | ⟨e', l', pos', m', hp', _, hb', hrev⟩
      · exact hT (revealed_mono Finset.subset_union_left ht)
      · exact ht (old T hT)
      · cases hf'
      · obtain ⟨_, he', _, _⟩ := Point.chain.inj hp'
        subst e'
        rw [hb] at hb'
        cases hb'
        exact hT hrev
    exact (hf _ _ hneq).trans (old T hT)
  refine ⟨h.corrupt_bound, ?_, ?_, ?_, ?_, fun e he => (h.bottom_released e he).mono hc, ?_⟩
  · intro e
    rcases h.bottom_opening e with hd | ⟨hb, hl⟩ | ⟨hb, T, ht, hm⟩
    · exact Or.inl (hd.mono hc)
    · refine Or.inr (Or.inl ⟨hb, hu _ ?_ ?_ hl⟩)
      · intro f he
        have hef := (Point.randomizer.inj he).2
        simpa only [← hef] using hb
      · intro f l pos he
        cases he
    · by_cases hq : ∃ seed, query = .prf seed (.randomizer bottomLayer e)
      · rcases hready e hq with hd | hn
        · exact Or.inl (hd.mono hc)
        · obtain ⟨U, hvU, hcU, hqU⟩ := not_readyAfter_missing seeds data
            { source with signing := sig } e query hb hn
          exact Or.inr (Or.inr ⟨hb, U, hv ▸ hvU, (hf _ _ hqU).trans hcU⟩)
      · exact Or.inr (Or.inr ⟨hb, T, hv ▸ ht, (hf _ _ (fun he => hq ⟨seeds T, he⟩)).trans hm⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with hd | hl | ⟨hm, m, hb, hlt, hl⟩
    · exact Or.inl (hdone e l pos hd)
    · by_cases hq : ∃ T, query = .prf (seeds T) (.chain bottomLayer e l (chainStepDigit pos)) ∧
          ¬TprfSecurityProof.Revealed sig.corrupt (.inl T)
      · obtain ⟨T, hqT, hT⟩ := hq
        rcases ha T _ hqT with ht | ht | ⟨f, hf', _⟩ | ⟨e', l', pos', m, hp', hstart, hb, hrev⟩
        · exact (hT ht).elim
        · exact (ht (hl T hT)).elim
        · cases hf'
        · obtain ⟨_, he', hl', hpos⟩ := Point.chain.inj hp'
          subst e'
          subst l'
          rw [← hpos] at hstart
          by_cases hlt : (signersAt sig e m).card < C.t
          · refine Or.inr (Or.inr ⟨hstart, m, hb, hlt, ?_⟩)
            apply coalition e l pos m hb
            intro T' hT'
            exact hl T' (fun hr => hT' (revealed_mono Finset.subset_union_left hr))
          · exact Or.inl (hdone e l pos (h.crossed_done e m hb (by omega) l pos
              ⟨chainStepDigit pos, hstart, by simp [chainStepDigit]⟩))
      · refine Or.inr (Or.inl ?_)
        intro T hT
        exact (hf _ _ (fun he => hq ⟨T, he, hT⟩)).trans (hl T hT)
    · exact Or.inr (Or.inr ⟨hm, m, hb, hlt, coalition e l pos m hb hl⟩)
  · intro b
    rcases h.top_opening b with hd | hl
    · exact Or.inl (hd.mono hc)
    · exact Or.inr (hu _ (fun e he => by cases he) (fun e l pos he => by cases he) hl)
  · intro b l
    rcases h.top_start b l with hd | hl
    · exact Or.inl (hd.mono hc)
    · refine Or.inr (hu _ (fun e he => by cases he) ?_ hl)
      intro e l' pos
      simp [topLayer, bottomLayer]
  · intro e m hb hn l pos hcov
    exact hdone e l pos (h.crossed_done e m hb hn l pos hcov)

/-- The read permission of the older source gives the read permission of the O1 source. -/
theorem ReadAllowedO1.of_source {source : SourceState C} {data : DeferredState C}
    {query : Query C} (h : SourceReadAllowed seeds source data query)
    (hb : source.signing.bound = sig.bound) (hc : source.signing.corrupt ⊆ sig.corrupt) :
    ReadAllowedO1 seeds sig starts data query := by
  intro T point hq
  rcases h T point hq with ht | ht | ⟨e, he, hbe⟩
  · exact Or.inl (revealed_mono hc ht)
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl ⟨e, he, hb ▸ hbe⟩))

/-- A permitted read stays permitted when the cache grows. -/
theorem ReadAllowedO1.mono {data data' : DeferredState C} {query : Query C}
    (h : ReadAllowedO1 seeds sig starts data query) (hc : data.cache ≤ data'.cache) :
    ReadAllowedO1 seeds sig starts data' query := by
  intro T point hq
  rcases h T point hq with ht | ht | ht
  · exact Or.inl ht
  · obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp ht
    exact Or.inr (Or.inl (Option.ne_none_iff_exists'.mpr ⟨value, hc hv⟩))
  · exact Or.inr (Or.inr ht)

/-- A query at a readable point is a permitted read. -/
theorem PointReadable.allowedO1 {source : SourceState C} {data : DeferredState C} {point : Point}
    (h : PointReadable seeds source data point) (hb : source.signing.bound = sig.bound)
    (query : Query C) (hq : ∀ seed p, query = .prf seed p → p = point) :
    ReadAllowedO1 seeds sig starts data query := by
  intro T p he
  have hp := hq (seeds T) p he
  subst p
  rcases h with hc | ⟨e, hpe, hbe⟩
  · exact Or.inr (Or.inl (hc T))
  · exact Or.inr (Or.inr (Or.inl ⟨e, hpe, hb ▸ hbe⟩))

/-- A read of a held term at a recorded chain point is a permitted read. -/
theorem HeldReadable.allowed {i : C.Party} {point : Point} {data : DeferredState C}
    (hinj : Function.Injective seeds) (h : HeldReadable sig starts i point) (T : C.Term)
    (hT : i ∈ C.holders T) :
    ReadAllowedO1 seeds sig starts data (.prf (seeds T) point) := by
  intro T' p he
  obtain ⟨hseed, hpoint⟩ := Query.prf.inj he
  have hTT := hinj hseed
  subst T'
  subst p
  obtain ⟨e, l, pos, m, hp, hstart, hb, hi⟩ := h
  exact Or.inr (Or.inr (Or.inr ⟨e, l, pos, m, hp, hstart, hb, ⟨i, hi, hT⟩⟩))


/-- A new binding keeps the slack. The release records at their bound messages give no signer at an
unbound key. -/
theorem ReleaseSlackO1.bind {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (e : KeyIndex) (message : Message)
    (hfree : sig.bound e = none ∨ sig.bound e = some message)
    (hrel : SigningGuessProof.ReleasedBound sig)
    (he : PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
      ∃ T : C.Term, (T, Point.randomizer bottomLayer e) ∉ data.virtual ∧
        data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none) :
    ReleaseSlackO1 seeds s { sig with bound := Function.update sig.bound e (some message) }
      ⟨source, starts⟩ data := by
  have hold : ∀ f m, Function.update sig.bound e (some message) f = some m →
      C.t ≤ (signersAt sig f m).card → sig.bound f = some m := by
    intro f m hb hn
    exact SigningSelectionProof.message_of_signers sig hrel h.corrupt_bound f m (by omega)
  refine ⟨h.corrupt_bound, ?_, ?_, h.top_opening, h.top_start, h.bottom_released, ?_⟩
  · intro f
    by_cases hfe : f = e
    · subst f
      rcases he with hd | hm
      · exact Or.inl hd
      · exact Or.inr (Or.inr ⟨by simp, hm⟩)
    · rcases h.bottom_opening f with hd | ⟨hb, hu⟩ | ⟨hb, hm⟩
      · exact Or.inl hd
      · exact Or.inr (Or.inl ⟨by simpa only [Function.update_of_ne hfe] using hb, hu⟩)
      · exact Or.inr (Or.inr ⟨by simpa only [Function.update_of_ne hfe] using hb, hm⟩)
  · intro f l pos
    rcases h.bottom_chain f l pos with hd | hu | ⟨hm, m, hb, hlt, hu⟩
    · exact Or.inl hd
    · exact Or.inr (Or.inl hu)
    · refine Or.inr (Or.inr ⟨hm, m, ?_, hlt, hu⟩)
      by_cases hfe : f = e
      · subst f
        rcases hfree with hn | hs
        · rw [hn] at hb
          cases hb
        · rw [hs] at hb
          cases hb
          simp
      · simpa only [Function.update_of_ne hfe] using hb
  · intro f m hb hn l pos hcov
    exact h.crossed_done f m (hold f m hb hn) hn l pos hcov


/-- A new digit at a key below the threshold keeps the slack. -/
theorem ReleaseSlackO1.record_below {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (e : KeyIndex) (l : ChainIndex)
    (d : Digit) (m : Message) (hb : sig.bound e = some m)
    (hlt : (signersAt sig e m).card < C.t) :
    ReleaseSlackO1 seeds s sig
      ⟨source, Function.update starts e (Function.update (starts e) l (insert d (starts e l)))⟩
      data := by
  have hsub : ∀ f j, starts f j ⊆
      (Function.update starts e (Function.update (starts e) l (insert d (starts e l)))) f j := by
    intro f j
    by_cases hf : f = e
    · subst f
      by_cases hj : j = l
      · subst j
        simp only [Function.update_self]
        exact Finset.subset_insert _ _
      · simp only [Function.update_self, Function.update_of_ne hj]
        exact Finset.Subset.refl _
    · simp only [Function.update_of_ne hf]
      exact Finset.Subset.refl _
  refine ⟨h.corrupt_bound, h.bottom_opening, ?_, h.top_opening, h.top_start, h.bottom_released, ?_⟩
  · intro f j pos
    rcases h.bottom_chain f j pos with hh | hh | ⟨hm, m', hb', hn, hh⟩
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr ⟨hsub f j hm, m', hb', hn, hh⟩)
  · intro f m' hb' hn j pos hcov
    by_cases hf : f = e
    · subst f
      rw [hb] at hb'
      cases hb'
      omega
    · apply h.crossed_done f m' hb' hn j pos
      simpa only [Covered, Function.update_of_ne hf] using hcov

/-- The slack reads the source state only at the recorded digits and at the reveal map. -/
theorem ReleaseInvariantO1.source_frame {src src' : SourceStateO1 C}
    {backend : CappedCompilerState C} (h : ReleaseInvariantO1 seeds s sig src backend)
    (hstarts : src'.starts = src.starts) (hr : src'.base.revealed = src.base.revealed) :
    ReleaseInvariantO1 seeds s sig src' backend := by
  obtain ⟨base', starts'⟩ := src'
  obtain ⟨base, starts⟩ := src
  change starts' = starts at hstarts
  subst hstarts
  exact ⟨ReleaseSlackO1.frame h.1 (fun _ _ => rfl) rfl rfl (fun _ he => hr ▸ he),
    h.2.1.frame hr rfl, h.2.2⟩

/-- The record of a signer below the threshold keeps the slack. -/
theorem ReleaseSlackO1.promote_below {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (e : KeyIndex) (message : Message) (i : C.Party)
    (hlt : (signersAt (withRecord sig e message i) e message).card < C.t) :
    ReleaseSlackO1 seeds s (withRecord sig e message i) src data := by
  apply ReleaseSlackO1.promote seeds s sig (withRecord sig e message i) src data h rfl
    (fun f m => signersAt_withRecord_subset sig e message i f m) (Finset.Subset.refl _)
    h.corrupt_bound
  intro f m hb hold hnew
  by_cases hfm : f = e ∧ m = message
  · obtain ⟨rfl, rfl⟩ := hfm
    omega
  · rw [signersAt_withRecord_of_ne sig e message i f m hfm] at hnew
    omega

/-- The record of a signer keeps the slack when each covered position of the key is complete. -/
theorem ReleaseSlackO1.promote_covered {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (e : KeyIndex) (message : Message) (i : C.Party)
    (hdone : ∀ l pos, Covered src.starts e l pos → BottomDone seeds s data e l pos) :
    ReleaseSlackO1 seeds s (withRecord sig e message i) src data := by
  apply ReleaseSlackO1.promote seeds s sig (withRecord sig e message i) src data h rfl
    (fun f m => signersAt_withRecord_subset sig e message i f m) (Finset.Subset.refl _)
    h.corrupt_bound
  intro f m hb hold hnew
  by_cases hfm : f = e ∧ m = message
  · obtain ⟨rfl, rfl⟩ := hfm
    exact hdone
  · rw [signersAt_withRecord_of_ne sig e message i f m hfm] at hnew
    omega

end Pure

/-! ## Round 2 and the initial state -/

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

/-- The callback of round 2 in the O1 source. -/
def round2Callback (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (message : Message) (atThreshold : Bool) (p : Point) : SourceMO1 C Digest := do
  match p with
  | .chain _ key l pos =>
      recordStart key l pos
      if atThreshold then sourceReleaseCovered x.1 x.2.1 key l
  | _ => pure ()
  liftBase (sourcePart prims x i J p message)

/-- Round 2 of the O1 source, with its callback by name. -/
theorem sourceRound2O1_eq (top : TopTree) (i : C.Party) (J : C.Quorum)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    sourceTsigO1 prims x top (.round2 i J e message parts) = (do
      let st := (← get).base.signing
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else
        let atThreshold := roundTwoReleased st e message i
        let some tree ← liftBase (sourceBottomOnce x.1 x.2.1 top (treeOf e)) | pure none
        let own ← liftBase (sourcePart prims x i J (.randomizer bottomLayer e) message)
        let parts := Function.update parts i own
        let some values ← signRound2With (fun oa => liftBase (sourceRoProgram prims x.1 x.2.1 oa))
            (round2Callback prims x i J message atThreshold)
            x.1 J (tree.commitment e) e message parts | pure none
        if atThreshold then sourceReleaseKey x.1 x.2.1 e
        modify fun (s : SourceStateO1 C) => { s with base := { s.base with signing :=
          { s.base.signing with released := s.base.signing.released ++ [(e, message, i)] } } }
        pure (some values)) := rfl

theorem round2Callback_below (i : C.Party) (J : C.Quorum) (message : Message) (e : KeyIndex)
    (l : ChainIndex) (d : Digit) :
    round2Callback prims x i J message false (.chain bottomLayer e l d) = (do
      recordStart e l d
      liftBase (sourcePart prims x i J (.chain bottomLayer e l d) message)) := by
  simp [round2Callback]

theorem round2Callback_at (i : C.Party) (J : C.Quorum) (message : Message) (e : KeyIndex)
    (l : ChainIndex) (d : Digit) :
    round2Callback prims x i J message true (.chain bottomLayer e l d) = (do
      recordStart e l d
      sourceReleaseCovered x.1 x.2.1 e l
      liftBase (sourcePart prims x i J (.chain bottomLayer e l d) message)) := by
  simp [round2Callback]

/-- The initial states of the O1 source and of the backend satisfy the guarded invariant. -/
theorem guardedReleaseInvariantS_initial (seeds : C.Term → HashOutput) :
    GuardedReleaseInvariantS (C := C) seeds s sourceInitO1
      ((compilerInit, 0), fun _ => none, false) := by
  refine ⟨guardedReleaseInvariantO1_initial seeds s, ?_⟩
  intro e m i hm
  simp [sourceInitO1, sourceInit, SigningCoreProof.tsigInit] at hm

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1Slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.signersAt_withRecord_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.signersAt_withRecord_subset

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.signersAt_withRecord_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.signersAt_withRecord_of_ne

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.mem_signersAt_withRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.mem_signersAt_withRecord

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.releasedBound_withRecord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.releasedBound_withRecord

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.releasedBound_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.releasedBound_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.releasedBound_corrupt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.releasedBound_corrupt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.revealed_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.revealed_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.read

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReadAllowedO1.of_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReadAllowedO1.of_source

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReadAllowedO1.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReadAllowedO1.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.PointReadable.allowedO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.PointReadable.allowedO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.HeldReadable.allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.HeldReadable.allowed

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.record_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.record_below

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseInvariantO1.source_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseInvariantO1.source_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.promote_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.promote_below

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.promote_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.ReleaseSlackO1.promote_covered

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.sourceRound2O1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.sourceRound2O1_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.round2Callback_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.round2Callback_below

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.round2Callback_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.round2Callback_at

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Slack.guardedReleaseInvariantS_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Slack.guardedReleaseInvariantS_initial
