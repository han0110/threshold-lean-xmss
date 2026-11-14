import ThresholdLeanXmssSecurity.Proof.SigningOwnWalk
import ThresholdLeanXmssSecurity.Proof.SigningOwnFree

/-!
# The walk of the base source over the ledger

`charges_setup` states that the setup of the O1 source keeps `WalkInv` and makes no charged call.

The units of the base source are stated with `Walk`, a triple over runs of the base source with the
ledger. A triple has a precondition on the source and the hybrid state, a bound on the charged
calls and a postcondition. Each run also extends the backend (`Grows`). `BaseInv` is `WalkInv` on
the base state, with an optional key at which `ready` or `revealedCached` need not hold. A virtual
call at a bottom randomizer uses the first exception until the release. The release uses the
second exception between the reveal and `completePrf`. `charges_of_walk` gives `SourceCharges` of
the lift of a unit.

* A raw backend call keeps `BaseInv` when it adds no PRF cell or virtual row at an unrevealed bottom
  randomizer, and no commitment answer without its virtual terms (`baseInv_step`).
* A pending point with a known input makes a hash call at a revealed key, so `pending_not_charged`
  applies. A hash program queries free inputs, so `free_not_charged` applies.
* `sourceVirtual` releases a ready opening, and the release caches each term of the opening.
* `sourceCommitment` makes each term virtual before its pending call, which gives `commitTerms`.
* The store of a tree gives `treeCommit`, because the commitment of each key of the tree is the low
  half of its pending answer.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnWalkBuild

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Clean SigningOwnLedger SigningOwnFree SigningOwnWalk

variable {C : Committee}

attribute [local instance] Classical.propDecidable

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

/-- The state of the hybrid with the ledger. -/
abbrev LState (C : Committee) := CappedCompilerState C × OwnGhost

/-- `WalkInv` on the base state. `ready` may fail at the key `readyEx`, and `revealedCached` may
fail at the key `cachedEx`. -/
structure BaseInv (P : PublicParameter) (seeds : C.Term → HashOutput)
    (readyEx cachedEx : Option KeyIndex) (src : SourceState C) (st : LState C) : Prop where
  reveal : src.revealed = st.1.2.1
  bound : st.1.1.1.bound = src.signing.bound
  ready : ∀ e, readyEx ≠ some e → OpeningReady seeds st.1.1.1.data src.signing e →
    src.revealed (.opening bottomLayer e) ≠ none
  commitTerms : ∀ e, st.1.1.1.data.pending (.commitment e) ≠ none →
    ∀ T, (T, Point.randomizer bottomLayer e) ∈ st.1.1.1.data.virtual
  treeCommit : ∀ b, src.trees b ≠ none → ∀ k,
    ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
      ∀ tree, src.trees b = some (some tree) →
        c.low = .known (tree.commitment (bottomKey b k))
  revealedCached : ∀ e, cachedEx ≠ some e → src.revealed (.opening bottomLayer e) ≠ none →
    SigningGuessProof.RandomizerCached seeds st.1.1.1.data.cache e
  releasedBound : SigningGuessProof.ReleasedBound src.signing
  corruptBound : src.signing.corrupt.card ≤ C.t - 1
  reachable : CompilerReachable P seeds st.1.1
  dirtySecond : st.2.dirty = true → SecondOpening P seeds st.1.1.1.data
  storedTopShape : ∀ b tree, src.trees b = some (some tree) → TopShape tree

theorem walkInv_iff (P : PublicParameter) (seeds : C.Term → HashOutput) (src : SourceStateO1 C)
    (st : LState C) : WalkInv P seeds src st ↔ BaseInv P seeds none none src.base st := by
  constructor
  · intro h
    exact ⟨h.reveal, h.bound, fun e _ => h.ready e, h.commitTerms, h.treeCommit,
      fun e _ => h.revealedCached e, h.releasedBound, h.corruptBound, h.reachable, h.dirtySecond,
      h.storedTopShape⟩
  · intro h
    exact ⟨h.reveal, h.bound, fun e => h.ready e (by simp), h.commitTerms, h.treeCommit,
      fun e => h.revealedCached e (by simp), h.releasedBound, h.corruptBound, h.reachable,
      h.dirtySecond, h.storedTopShape⟩

/-- The backend of `st'` extends the backend of `st`. -/
structure Grows (st st' : LState C) : Prop where
  cache : st.1.1.1.data.cache ≤ st'.1.1.1.data.cache
  pending : ∀ p v, st.1.1.1.data.pending p = some v → st'.1.1.1.data.pending p = some v
  virtual : st.1.1.1.data.virtual ⊆ st'.1.1.1.data.virtual

theorem Grows.refl (st : LState C) : Grows st st :=
  ⟨le_rfl, fun _ _ h => h, Finset.Subset.refl _⟩

theorem Grows.trans {st st' st'' : LState C} (h : Grows st st') (h' : Grows st' st'') :
    Grows st st'' :=
  ⟨h.cache.trans h'.cache, fun p v hp => h'.pending p v (h.pending p v hp),
    h.virtual.trans h'.virtual⟩

/-- A run of a base source program over the hybrid with the ledger. -/
def runL {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ)
    (s : HiddenKey → Digest) (oa : SourceM C α) (src : SourceState C) (st : LState C) :
    ProbComp ((α × SourceState C) × LState C) :=
  (simulateQ (ownHybrid P seeds Q s) (oa.run src)).run st

/-- A triple over the runs of a base source program. From each state of `Pre`, each run makes at
most `c` charged calls, extends the backend and ends in a state of `Post`. -/
def Walk {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ)
    (s : HiddenKey → Digest) (Pre : SourceState C → LState C → Prop) (c : ℕ)
    (Post : α → SourceState C → LState C → Prop) (oa : SourceM C α) : Prop :=
  ∀ src st, Pre src st → ∀ r ∈ support (runL P seeds Q s oa src st),
    r.2.2.ledger ≤ st.2.ledger + c ∧ Grows st r.2 ∧ Post r.1.1 r.1.2 r.2

namespace Walk

variable {P : PublicParameter} {seeds : C.Term → HashOutput} {Q : ℕ} {s : HiddenKey → Digest}

theorem conseq {α : Type} {oa : SourceM C α} {Pre Pre' : SourceState C → LState C → Prop}
    {Post Post' : α → SourceState C → LState C → Prop} {c d : ℕ}
    (h : Walk P seeds Q s Pre c Post oa) (hPre : ∀ src st, Pre' src st → Pre src st)
    (hPost : ∀ a src st, Post a src st → Post' a src st) (hcd : c ≤ d) :
    Walk P seeds Q s Pre' d Post' oa := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq⟩ := h src st (hPre src st hp) r hr
  exact ⟨by omega, hg, hPost _ _ _ hq⟩

theorem pure {α : Type} {Pre : SourceState C → LState C → Prop}
    {Post : α → SourceState C → LState C → Prop} (value : α)
    (h : ∀ src st, Pre src st → Post value src st) :
    Walk P seeds Q s Pre 0 Post (Pure.pure value) := by
  intro src st hp r hr
  simp only [runL, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
  subst r
  exact ⟨le_rfl, Grows.refl st, h src st hp⟩

theorem get {Pre : SourceState C → LState C → Prop} :
    Walk P seeds Q s Pre 0 (fun a src st => a = src ∧ Pre src st)
      (MonadState.get : SourceM C (SourceState C)) := by
  intro src st hp r hr
  simp only [runL, StateT.run_get, simulateQ_pure] at hr
  subst r
  exact ⟨le_rfl, Grows.refl st, rfl, hp⟩

theorem modify {Pre : SourceState C → LState C → Prop} {Post : Unit → SourceState C → LState C → Prop}
    (f : SourceState C → SourceState C) (h : ∀ src st, Pre src st → Post () (f src) st) :
    Walk P seeds Q s Pre 0 Post (modify f : SourceM C Unit) := by
  intro src st hp r hr
  simp only [runL, StateT.run_modify, simulateQ_pure] at hr
  subst r
  exact ⟨le_rfl, Grows.refl st, h src st hp⟩

theorem bind {α β : Type} {oa : SourceM C α} {next : α → SourceM C β}
    {Pre : SourceState C → LState C → Prop} {Mid : α → SourceState C → LState C → Prop}
    {Post : β → SourceState C → LState C → Prop} {c d : ℕ}
    (h : Walk P seeds Q s Pre c Mid oa) (hn : ∀ a, Walk P seeds Q s (Mid a) d Post (next a)) :
    Walk P seeds Q s Pre (c + d) Post (oa >>= next) := by
  intro src st hp r hr
  simp only [runL, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨hla, hga, hqa⟩ := h src st hp a ha
  obtain ⟨hlr, hgr, hqr⟩ := hn a.1.1 a.1.2 a.2 hqa r hr
  exact ⟨by omega, hga.trans hgr, hqr⟩

/-- A list of steps that each move a predicate from a prefix of the list to the next prefix. -/
theorem mapM_prefix {α β : Type} {c : ℕ} (oa : α → SourceM C β)
    (I : List α → SourceState C → LState C → Prop) :
    ∀ (items done : List α),
      (∀ pre a post, done ++ items = pre ++ a :: post →
        Walk P seeds Q s (I pre) c (fun _ => I (pre ++ [a])) (oa a)) →
      Walk P seeds Q s (I done) (items.length * c) (fun _ => I (done ++ items)) (items.mapM oa)
  | [], done, _ => by
      simpa only [List.append_nil, List.length_nil, Nat.zero_mul, List.mapM_nil] using
        Walk.pure (P := P) (seeds := seeds) (Q := Q) (s := s) (Pre := I done)
          (Post := fun (_ : List β) => I done) [] fun _ _ h => h
  | a :: items, done, h => by
      rw [List.mapM_cons]
      have hhead := h done a items rfl
      have htail := mapM_prefix oa I items (done ++ [a]) (fun pre b post hb =>
        h pre b post (by simpa only [List.append_assoc, List.singleton_append] using hb))
      refine Walk.conseq (Walk.bind hhead fun head => Walk.bind htail fun tail =>
        Walk.pure (Post := fun _ => I (done ++ [a] ++ items)) (head :: tail)
          fun _ _ h => h) (fun _ _ h => h) ?_ ?_
      · intro _ _ _ h
        simpa only [List.append_assoc, List.singleton_append] using h
      · simp only [List.length_cons]
        nlinarith

/-- A list of steps that each keep an invariant. -/
theorem mapM {α β : Type} {c : ℕ} (items : List α) (oa : α → SourceM C β)
    (I : SourceState C → LState C → Prop)
    (h : ∀ a ∈ items, Walk P seeds Q s I c (fun _ => I) (oa a)) :
    Walk P seeds Q s I (items.length * c) (fun _ => I) (items.mapM oa) := by
  simpa using mapM_prefix oa (fun _ => I) items [] (fun pre a post hp =>
    h a (by rw [List.nil_append] at hp; rw [hp]; simp))

theorem sequenceFin {α : Type} {c : ℕ} (n : ℕ) (oa : Fin n → SourceM C α)
    (I : SourceState C → LState C → Prop)
    (h : ∀ i, Walk P seeds Q s I c (fun _ => I) (oa i)) :
    Walk P seeds Q s I (n * c) (fun _ => I) (OverPermutation.sequenceFin oa) := by
  induction n with
  | zero =>
      simpa only [OverPermutation.sequenceFin, Nat.zero_mul] using
        Walk.pure (P := P) (seeds := seeds) (Q := Q) (s := s) (Pre := I)
          (Post := fun (_ : Fin 0 → α) => I) _ fun _ _ h => h
  | succ n ih =>
      simp only [OverPermutation.sequenceFin]
      refine Walk.conseq (Walk.bind (h 0) fun head =>
        Walk.bind (ih (fun i => oa i.succ) fun i => h i.succ) fun tail =>
          Walk.pure (Post := fun _ => I) _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) ?_
      nlinarith

/-- A predicate on the hybrid state that each extension of the backend keeps. -/
theorem frame {α : Type} {oa : SourceM C α} {Pre : SourceState C → LState C → Prop}
    {Post : α → SourceState C → LState C → Prop} {c : ℕ} (F : LState C → Prop)
    (hF : ∀ st st', Grows st st' → F st → F st') (h : Walk P seeds Q s Pre c Post oa) :
    Walk P seeds Q s (fun src st => Pre src st ∧ F st) c (fun a src st => Post a src st ∧ F st)
      oa := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq⟩ := h src st hp.1 r hr
  exact ⟨hl, hg, hq, hF _ _ hg hp.2⟩

/-- A list of lifted oracle steps. Each step keeps an invariant and gives a fact that each
extension of the backend keeps. -/
theorem liftM_mapM {α β : Type} {c : ℕ}
    (oa : α → OracleComp (DeferredSpec C + RevealSpec HiddenKey Digest) β)
    (I : SourceState C → LState C → Prop) (G : α → LState C → Prop)
    (hG : ∀ a st st', Grows st st' → G a st → G a st') :
    ∀ items : List α, (∀ a ∈ items, Walk P seeds Q s I c (fun _ src st => I src st ∧ G a st)
        (liftM (oa a) : SourceM C β)) →
      Walk P seeds Q s I (items.length * c) (fun _ src st => I src st ∧ ∀ a ∈ items, G a st)
        (liftM (items.mapM oa) : SourceM C (List β))
  | [], _ => by
      simpa only [List.mapM_nil, liftM_pure, List.length_nil, Nat.zero_mul] using
        Walk.pure (P := P) (seeds := seeds) (Q := Q) (s := s) (Pre := I)
          (Post := fun (_ : List β) src st => I src st ∧ ∀ a ∈ ([] : List α), G a st) []
          fun _ _ h => ⟨h, fun _ ha => by cases ha⟩
  | a :: items, h => by
      rw [List.mapM_cons, liftM_bind]
      refine Walk.conseq (c := c + (items.length * c + 0))
        (Walk.bind (h a (List.mem_cons_self ..)) fun head => ?_)
        (fun _ _ h => h) (fun _ _ _ h => h) (by simp only [List.length_cons]; nlinarith)
      rw [liftM_bind]
      refine Walk.bind (Walk.frame (G a) (hG a) (liftM_mapM oa I G hG items
        fun b hb => h b (List.mem_cons_of_mem _ hb))) fun tail => ?_
      rw [liftM_pure]
      exact Walk.pure _ fun _ _ h => ⟨h.1.1, fun b hb => (List.mem_cons.mp hb).elim
        (fun he => he ▸ h.2) (h.1.2 b)⟩

/-- A list of steps that each keep an invariant and relate their result to their item by a
relation that each extension of the backend keeps. -/
theorem mapM_rel {α β : Type} {c : ℕ} (oa : α → SourceM C β)
    (I : SourceState C → LState C → Prop) (R : α → β → LState C → Prop)
    (hR : ∀ a b st st', Grows st st' → R a b st → R a b st') :
    ∀ items : List α, (∀ a ∈ items, Walk P seeds Q s I c (fun b src st => I src st ∧ R a b st)
        (oa a)) →
      Walk P seeds Q s I (items.length * c)
        (fun bs src st => I src st ∧ List.Forall₂ (fun a b => R a b st) items bs)
        (items.mapM oa)
  | [], _ => by
      simpa only [List.mapM_nil, List.length_nil, Nat.zero_mul] using
        Walk.pure (P := P) (seeds := seeds) (Q := Q) (s := s) (Pre := I)
          (Post := fun (bs : List β) src st => I src st ∧
            List.Forall₂ (fun a b => R a b st) ([] : List α) bs) []
          fun _ _ h => ⟨h, List.Forall₂.nil⟩
  | a :: items, h => by
      rw [List.mapM_cons]
      refine Walk.conseq (c := c + (items.length * c + 0))
        (Walk.bind (h a (List.mem_cons_self ..)) fun head => ?_)
        (fun _ _ h => h) (fun _ _ _ h => h) (by simp only [List.length_cons]; nlinarith)
      refine Walk.bind (Walk.frame (R a head) (hR a head) (mapM_rel oa I R hR items
        fun b hb => h b (List.mem_cons_of_mem _ hb))) fun tail => ?_
      exact Walk.pure _ fun _ _ h => ⟨h.1.1, List.Forall₂.cons h.2 h.1.2⟩

end Walk

/-- The relation of `Walk.mapM_rel` over `List.finRange` at one index. -/
theorem forall₂_finRange {β : Type} {n : ℕ} {R : Fin n → β → Prop} {bs : List β} (d : β)
    (h : List.Forall₂ R (List.finRange n) bs) (k : Fin n) : R k (bs.getD k.val d) := by
  have hlen := h.length_eq
  simp only [List.length_finRange] at hlen
  have hk : k.val < bs.length := by rw [← hlen]; exact k.isLt
  have := (List.forall₂_iff_get.mp h).2 k.val (by simp) hk
  simp only [List.get_eq_getElem, List.getElem_finRange] at this
  rw [List.getD_eq_getElem _ _ hk]
  exact this

/-- A triple of a base program with `BaseInv` and no exception gives `SourceCharges` of its lift. -/
theorem charges_of_walk {P : PublicParameter} {seeds : C.Term → HashOutput} {Q : ℕ}
    {s : HiddenKey → Digest} {α : Type} {oa : SourceM C α} {c : ℕ}
    (h : Walk P seeds Q s (BaseInv P seeds none none) c (fun _ => BaseInv P seeds none none) oa) :
    SourceCharges P seeds Q s (fun _ => True) c (liftBase oa) := by
  refine SourceCharges.liftBase fun src st hw _ r hr => ?_
  obtain ⟨hl, -, hq⟩ := h src.base st ((walkInv_iff P seeds src st).1 hw) r hr
  exact ⟨(walkInv_iff P seeds _ r.2).2 hq, hl⟩

/-! ## One backend call -/

section Calls

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

set_option backward.isDefEq.respectTransparency false in
/-- A backend call other than a `.record` over an answer keeps each pending answer. -/
theorem deferredImpl_pending_keep (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C) (hr : r ∈ support ((deferredImpl t).run st))
    (hrec : ∀ p' value, t = .record p' value → st.pending p' = none)
    (p : PendingInput) (v : DeferredOutput) (hp : st.pending p = some v) :
    r.2.pending p = some v := by
  cases t with
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          have hne : p ≠ key := by
            rintro rfl
            rw [hp] at hk
            cases hk
          simpa only [Function.update_of_ne hne] using hp
  | record key value =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      have hne : p ≠ key := by
        rintro rfl
        rw [hrec _ _ rfl] at hp
        cases hp
      simpa only [Function.update_of_ne hne] using hp
  | pad point =>
      cases hk : st.pads point with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact hp
  | plant q value =>
      cases hk : st.cache q.query with
      | some prior =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
      | none =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact hp
  | _ =>
      first
        | (simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr; subst r; exact hp)
        | (simp only [deferredImpl, StateT.run, support_map] at hr
           obtain ⟨a, _, rfl⟩ := hr
           exact hp)

/-- The compiler keeps each pending answer at a call other than a `.record` over an answer. -/
theorem compilerImpl_pending_keep (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C) (hr : r ∈ support ((compilerImpl P seeds t).run st))
    (hrec : ∀ p' value, t = .record p' value → st.data.pending p' = none)
    (p : PendingInput) (v : DeferredOutput) (hp : st.data.pending p = some v) :
    r.2.data.pending p = some v := by
  cases t with
  | hash query =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, _, rfl⟩ := hr
      exact deferredImpl_pending_keep (.hash query) st.data a ha (fun _ _ h => by cases h) p v hp
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact hp
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_pending_keep _ st.data a ha hrec p v hp

/-- The compiler changes the bound map only at `.bindKey`. -/
theorem compilerImpl_bound_eq (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C) (hr : r ∈ support ((compilerImpl P seeds t).run st))
    (ht : ∀ e message, t ≠ .bindKey e message) : r.2.bound = st.bound := by
  cases t with
  | hash query =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, _, rfl⟩ := hr
      rfl
  | bindKey e message => exact absurd rfl (ht e message)
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      rfl

/-- A raw backend call over the hybrid with the ledger. -/
theorem mem_runL_query (t : DeferredQuery C) (src : SourceState C) (st : LState C)
    (r : (DeferredSpec C t × SourceState C) × LState C)
    (hr : r ∈ support (runL P seeds Q s (liftM (deferredQuery t)) src st)) :
    ∃ x ∈ support ((compilerImpl P seeds t).run st.1.1.1), ∃ flag : Bool,
      r = ((x.1, src), (((x.2, st.1.1.2 + if deferredCounted t then 1 else 0), st.1.2.1, flag),
        ownAux P seeds t (st.1.1, st.1.2.1) st.2)) := by
  obtain ⟨⟨σ₀, stored, b⟩, g⟩ := st
  change r ∈ support ((simulateQ (ownHybrid P seeds Q s)
    (deferredQuery t >>= fun value => Pure.pure (value, src))).run ((σ₀, stored, b), g)) at hr
  simp only [deferredQuery, HasQuery.instOfMonadLift_query] at hr
  erw [SigningLedgerExpect.ledgerHybrid_inl_run] at hr
  simp only [simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  simp only [countImpl, StateT.run_mk, support_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, _, rfl⟩

/-- A reveal over the hybrid with the ledger. -/
theorem mem_runL_reveal (k : HiddenKey) (src : SourceState C) (st : LState C)
    (r : (Digest × SourceState C) × LState C)
    (hr : r ∈ support (runL P seeds Q s (liftM (revealQuery (C := C) k)) src st)) :
    r = ((((st.1.2.1 k).getD (s k)), src), ((st.1.1, Function.update st.1.2.1 k
      (some ((st.1.2.1 k).getD (s k))), st.1.2.2), st.2)) := by
  obtain ⟨⟨σ₀, stored, b⟩, g⟩ := st
  change r ∈ support ((simulateQ (ownHybrid P seeds Q s)
    (revealQuery k >>= fun value => Pure.pure (value, src))).run ((σ₀, stored, b), g)) at hr
  simp only [revealQuery, HasQuery.instOfMonadLift_query] at hr
  erw [SigningLedgerExpect.ledgerHybrid_inr_run] at hr
  simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using hr

/-- A raw backend call, with the strongest postcondition. A call that charges needs `1 ≤ c`. -/
theorem walk_query (t : DeferredQuery C) (Pre : SourceState C → LState C → Prop) (c : ℕ)
    (hrec : ∀ p value, t = .record p value → ∀ src st, Pre src st →
      st.1.1.1.data.pending p = none)
    (hc : ∀ src st, Pre src st → ownCharged P seeds t (st.1.1, st.1.2.1) st.2 → 1 ≤ c) :
    Walk P seeds Q s Pre c (fun y src' st' => ∃ st, Pre src' st ∧
        ∃ x ∈ support ((compilerImpl P seeds t).run st.1.1.1), y = x.1 ∧ ∃ flag : Bool,
          st' = (((x.2, st.1.1.2 + if deferredCounted t then 1 else 0), st.1.2.1, flag),
            ownAux P seeds t (st.1.1, st.1.2.1) st.2))
      (liftM (deferredQuery t)) := by
  intro src st hp r hr
  obtain ⟨x, hx, flag, rfl⟩ := mem_runL_query P seeds Q s t src st r hr
  refine ⟨?_, ⟨compilerImpl_cache_le P seeds t _ x hx,
    fun p v hv => compilerImpl_pending_keep P seeds t _ x hx
      (fun p' value he => hrec p' value he src st hp) p v hv,
    SigningCompilerSyncRows.compilerImpl_virtual_mono P seeds t _ x hx⟩, st, hp, x, hx, rfl, flag, rfl⟩
  change st.2.ledger + (if ownCharged P seeds t (st.1.1, st.1.2.1) st.2 then 1 else 0) ≤ _
  split
  · have := hc src st hp (by assumption)
    omega
  · omega

/-- A reveal, with the strongest postcondition. -/
theorem walk_reveal (k : HiddenKey) (Pre : SourceState C → LState C → Prop) :
    Walk P seeds Q s Pre 0 (fun v src' st' => ∃ st, Pre src' st ∧
        v = (st.1.2.1 k).getD (s k) ∧
        st' = ((st.1.1, Function.update st.1.2.1 k (some v), st.1.2.2), st.2))
      (liftM (revealQuery (C := C) k)) := by
  intro src st hp r hr
  rw [mem_runL_reveal P seeds Q s k src st r hr]
  exact ⟨le_refl _, ⟨le_rfl, fun _ _ h => h, Finset.Subset.refl _⟩, st, hp, rfl, rfl⟩

/-- A second opening stays when the cache and the pending answers grow. -/
theorem secondOpening_mono {data data' : DeferredState C} (hcache : data.cache ≤ data'.cache)
    (hpending : ∀ p v, data.pending p = some v → data'.pending p = some v)
    (h : SecondOpening P seeds data) : SecondOpening P seeds data' := by
  obtain ⟨e, ρ, v, c, hv, hc, hlow, hprf, hne⟩ := h
  refine ⟨e, ρ, v, c, hcache hv, hpending _ _ hc, hlow,
    SigningGuessProof.randomizerCached_mono seeds _ _ hcache e hprf, ?_⟩
  rwa [← SigningGuessProof.cachedRandomizer_stable seeds _ _ e hcache hprf]

/-- One backend call keeps `BaseInv`, when it makes no key ready that has no revealed opening, and
it adds no commitment answer without its virtual terms. -/
theorem baseInv_step {readyEx cachedEx : Option KeyIndex} {src : SourceState C} {st : LState C}
    {t : DeferredQuery C} (h : BaseInv P seeds readyEx cachedEx src st)
    {x : DeferredSpec C t × CompilerBackend C}
    (hx : x ∈ support ((compilerImpl P seeds t).run st.1.1.1))
    (ht : ∀ e message, t ≠ .bindKey e message)
    (hrec : ∀ p value, t = .record p value → st.1.1.1.data.pending p = none)
    (hready : ∀ e, OpeningReady seeds x.2.data src.signing e →
      OpeningReady seeds st.1.1.1.data src.signing e ∨
        src.revealed (.opening bottomLayer e) ≠ none ∨ readyEx = some e)
    (hcommit : ∀ e, x.2.data.pending (.commitment e) ≠ none →
      st.1.1.1.data.pending (.commitment e) ≠ none ∨
        ∀ T, (T, Point.randomizer bottomLayer e) ∈ x.2.data.virtual)
    (flag : Bool) :
    BaseInv P seeds readyEx cachedEx src
      (((x.2, st.1.1.2 + if deferredCounted t then 1 else 0), st.1.2.1, flag),
        ownAux P seeds t (st.1.1, st.1.2.1) st.2) := by
  have hcache := compilerImpl_cache_le P seeds t _ x hx
  have hkeep := fun p v hv => compilerImpl_pending_keep P seeds t _ x hx hrec p v hv
  have hvirt := SigningCompilerSyncRows.compilerImpl_virtual_mono P seeds t _ x hx
  refine ⟨h.reveal, ?_, ?_, ?_, ?_, ?_, h.releasedBound, h.corruptBound, ?_, ?_, h.storedTopShape⟩
  · exact (compilerImpl_bound_eq P seeds t _ x hx ht).trans h.bound
  · intro e hne hr
    rcases hready e hr with h1 | h1 | h1
    · exact h.ready e hne h1
    · exact h1
    · exact absurd h1 hne
  · intro e hp T
    rcases hcommit e hp with h1 | h1
    · exact hvirt (h.commitTerms e h1 T)
    · exact h1 T
  · intro b hb k
    obtain ⟨c, hc, hct⟩ := h.treeCommit b hb k
    exact ⟨c, hkeep _ _ hc, hct⟩
  · intro e hne hr
    exact SigningGuessProof.randomizerCached_mono seeds _ _ hcache e (h.revealedCached e hne hr)
  · refine CompilerReachable.step t st.1.1 (x.1, (x.2, _)) h.reachable ?_
    simp only [countImpl, StateT.run_mk, support_map]
    exact ⟨x, hx, rfl⟩
  · intro hd
    change (st.2.dirty || decide (SecondOpening P seeds st.1.1.1.data)) = true at hd
    rcases Bool.or_eq_true_iff.mp hd with hd | hd
    · exact secondOpening_mono P seeds hcache hkeep (h.dirtySecond hd)
    · exact secondOpening_mono P seeds hcache hkeep (of_decide_eq_true hd)

set_option backward.isDefEq.respectTransparency false in
/-- A backend call adds a virtual row only at `.virtual`, and a pending answer only at `.pending`
or `.record`. -/
theorem deferredImpl_frame (t : DeferredQuery C) (st : DeferredState C)
    (r : DeferredSpec C t × DeferredState C) (hr : r ∈ support ((deferredImpl t).run st)) :
    (∀ T point, (T, point) ∈ r.2.virtual → (T, point) ∈ st.virtual ∨ t = .virtual T point) ∧
      (∀ q, r.2.pending q ≠ none →
        st.pending q ≠ none ∨ t = .pending q ∨ ∃ value, t = .record q value) := by
  have keep : (∀ T point, (T, point) ∈ st.virtual → (T, point) ∈ st.virtual ∨
      t = .virtual T point) ∧ (∀ q, st.pending q ≠ none →
        st.pending q ≠ none ∨ t = .pending q ∨ ∃ value, t = .record q value) :=
    ⟨fun _ _ h => Or.inl h, fun _ h => Or.inl h⟩
  cases t with
  | pending key =>
      cases hk : st.pending key with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact keep
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          refine ⟨fun _ _ h => Or.inl h, fun q h => ?_⟩
          by_cases hq : q = key
          · exact Or.inr (Or.inl (hq ▸ rfl))
          · exact Or.inl (by simpa only [Function.update_of_ne hq] using h)
  | record key value =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      refine ⟨fun _ _ h => Or.inl h, fun q h => ?_⟩
      by_cases hq : q = key
      · exact Or.inr (Or.inr ⟨value, hq ▸ rfl⟩)
      · exact Or.inl (by simpa only [Function.update_of_ne hq] using h)
  | virtual T point =>
      simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      refine ⟨fun T' point' h => ?_, fun _ h => Or.inl h⟩
      rcases Finset.mem_insert.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr rfl
      · exact Or.inl h
  | pad point =>
      cases hk : st.pads point with
      | some value =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact keep
      | none =>
          simp only [deferredImpl, StateT.run, hk, support_map] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact keep
  | plant q value =>
      cases hk : st.cache q.query with
      | some prior =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact keep
      | none =>
          simp only [deferredImpl, StateT.run, hk, mem_support_pure_iff] at hr
          subst r
          exact keep
  | _ =>
      first
        | (simp only [deferredImpl, StateT.run, mem_support_pure_iff] at hr; subst r; exact keep)
        | (simp only [deferredImpl, StateT.run, support_map] at hr
           obtain ⟨a, _, rfl⟩ := hr
           exact keep)

/-- `deferredImpl_frame` for the compiler. -/
theorem compilerImpl_frame (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C) (hr : r ∈ support ((compilerImpl P seeds t).run st)) :
    (∀ T point, (T, point) ∈ r.2.data.virtual → (T, point) ∈ st.data.virtual ∨
      t = .virtual T point) ∧
      (∀ q, r.2.data.pending q ≠ none →
        st.data.pending q ≠ none ∨ t = .pending q ∨ ∃ value, t = .record q value) := by
  cases t with
  | hash query =>
      simp only [compilerImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, b, _, rfl⟩ := hr
      exact deferredImpl_frame (.hash query) st.data a ha
  | bindKey e message =>
      simp only [compilerImpl, StateT.run, mem_support_pure_iff] at hr
      subst r
      exact ⟨fun _ _ h => Or.inl h, fun _ h => Or.inl h⟩
  | _ =>
      simp only [compilerImpl, StateT.run, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      exact deferredImpl_frame _ st.data a ha

/-- A call that adds no virtual row and writes no PRF cell at the bottom randomizer of `e` makes
`e` ready only when it was ready before. -/
theorem openingReady_back (t : DeferredQuery C) (st : CompilerBackend C)
    (r : DeferredSpec C t × CompilerBackend C) (hr : r ∈ support ((compilerImpl P seeds t).run st))
    (sig : TsigState C) (e : KeyIndex)
    (hv : ∀ T, t ≠ .virtual T (.randomizer bottomLayer e))
    (hw : ∀ T, ¬WritesPrf (seeds T) (.randomizer bottomLayer e) t)
    (h : OpeningReady seeds r.2.data sig e) : OpeningReady seeds st.data sig e := by
  refine ⟨h.1, fun T => (h.2 T).imp (fun hm => ?_) (fun hc => ?_)⟩
  · exact ((compilerImpl_frame P seeds t st r hr).1 T _ hm).resolve_right (hv T)
  · rwa [compilerImpl_prf_frame P seeds t st r hr _ _ (hw T)] at hc

/-- `BaseInv` reads only the revealed secrets, the signing state and the trees of the source. -/
theorem BaseInv.of_source {readyEx cachedEx : Option KeyIndex} {src src' : SourceState C}
    {st : LState C} (h : BaseInv P seeds readyEx cachedEx src st)
    (hrev : src'.revealed = src.revealed) (hsig : src'.signing = src.signing)
    (htrees : src'.trees = src.trees) : BaseInv P seeds readyEx cachedEx src' st := by
  cases h
  constructor <;> (try simp only [hrev, hsig, htrees]) <;> assumption

/-- A raw backend call that keeps `BaseInv`. The postcondition holds the call on the state before. -/
theorem walk_call {readyEx cachedEx : Option KeyIndex} (t : DeferredQuery C)
    (A : SourceState C → LState C → Prop) (ht : ∀ e message, t ≠ .bindKey e message)
    (hrec : ∀ p value, t = .record p value → ∀ src st, BaseInv P seeds readyEx cachedEx src st →
      A src st → st.1.1.1.data.pending p = none)
    (hcharge : ∀ src st, BaseInv P seeds readyEx cachedEx src st → A src st →
      ¬ownCharged P seeds t (st.1.1, st.1.2.1) st.2)
    (hready : ∀ src st, BaseInv P seeds readyEx cachedEx src st → A src st →
      ∀ x ∈ support ((compilerImpl P seeds t).run st.1.1.1), ∀ e,
        OpeningReady seeds x.2.data src.signing e →
          OpeningReady seeds st.1.1.1.data src.signing e ∨
            src.revealed (.opening bottomLayer e) ≠ none ∨ readyEx = some e)
    (hcommit : ∀ src st, BaseInv P seeds readyEx cachedEx src st → A src st →
      ∀ x ∈ support ((compilerImpl P seeds t).run st.1.1.1), ∀ e,
        x.2.data.pending (.commitment e) ≠ none →
          st.1.1.1.data.pending (.commitment e) ≠ none ∨
            ∀ T, (T, Point.randomizer bottomLayer e) ∈ x.2.data.virtual) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ A src st) 0
      (fun y src' st' => BaseInv P seeds readyEx cachedEx src' st' ∧ ∃ st, A src' st ∧
        ∃ x ∈ support ((compilerImpl P seeds t).run st.1.1.1), y = x.1 ∧ st'.1.1.1 = x.2)
      (liftM (deferredQuery t)) := by
  refine Walk.conseq (walk_query P seeds Q s t _ 0
    (fun p value he src st hp => hrec p value he src st hp.1 hp.2)
    (fun src st hp hc => absurd hc (hcharge src st hp.1 hp.2))) (fun _ _ h => h) ?_ le_rfl
  rintro y src' st' ⟨st, hp, x, hx, rfl, flag, rfl⟩
  exact ⟨baseInv_step P seeds hp.1 hx ht (fun p value he => hrec p value he _ _ hp.1 hp.2)
    (hready _ _ hp.1 hp.2 x hx) (hcommit _ _ hp.1 hp.2 x hx) flag, st, hp.2, x, hx, rfl, rfl⟩

theorem compilerImpl_inspect_eq (p : PendingInput) (st : CompilerBackend C)
    (x : Option DeferredOutput × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.inspect p)).run st)) :
    x = (st.data.pending p, st) := by
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure] at hx
  exact hx

theorem compilerImpl_snapshot_eq (st : CompilerBackend C) (x : DeferredState C × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds .snapshot).run st)) : x = (st.data, st) := by
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
theorem compilerImpl_pending_some (p : PendingInput) (st : CompilerBackend C)
    (x : DeferredOutput × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.pending p)).run st)) :
    x.2.data.pending p = some x.1 := by
  simp only [compilerImpl, StateT.run, support_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  cases hk : st.data.pending p with
  | some value =>
      simp only [deferredImpl, hk, mem_support_pure_iff] at ha
      subst a
      exact hk
  | none =>
      simp only [deferredImpl, hk, support_map] at ha
      obtain ⟨value, _, rfl⟩ := ha
      simp only [Function.update_self]

theorem compilerImpl_record_some (p : PendingInput) (value : HashOutput) (st : CompilerBackend C)
    (x : Unit × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.record p value)).run st)) :
    x.2.data.pending p = some ⟨(XmssSecurity.Rom.hashOutputEquivDigestPair value).1,
      match p.next with
      | some k => .secret k
      | none => .known (XmssSecurity.Rom.hashOutputEquivDigestPair value).2⟩ := by
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure] at hx
  subst x
  simp only [Function.update_self]
  rfl

/-- A call with no virtual row at a bottom randomizer and no PRF write there keeps readiness. -/
theorem ready_plain {readyEx : Option KeyIndex} (t : DeferredQuery C)
    (hv : ∀ T e, t ≠ .virtual T (.randomizer bottomLayer e))
    (hw : ∀ T e, ¬WritesPrf (seeds T) (.randomizer bottomLayer e) t) (src : SourceState C)
    (st : LState C) (x : DeferredSpec C t × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds t).run st.1.1.1)) (e : KeyIndex)
    (h : OpeningReady seeds x.2.data src.signing e) :
    OpeningReady seeds st.1.1.1.data src.signing e ∨
      src.revealed (.opening bottomLayer e) ≠ none ∨ readyEx = some e :=
  Or.inl (openingReady_back P seeds t _ x hx _ e (fun T => hv T e) (fun T => hw T e) h)

/-- A call that adds no commitment answer keeps `commitTerms`. -/
theorem commit_plain (t : DeferredQuery C) (hp : ∀ e, t ≠ .pending (.commitment e))
    (hr : ∀ e value, t ≠ .record (.commitment e) value) (st : LState C)
    (x : DeferredSpec C t × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds t).run st.1.1.1)) (e : KeyIndex)
    (h : x.2.data.pending (.commitment e) ≠ none) :
    st.1.1.1.data.pending (.commitment e) ≠ none ∨
      ∀ T, (T, Point.randomizer bottomLayer e) ∈ x.2.data.virtual := by
  rcases (compilerImpl_frame P seeds t _ x hx).2 _ h with h | h | ⟨value, h⟩
  · exact Or.inl h
  · exact absurd h (hp e)
  · exact absurd h (hr e value)

/-- A call that is no `.hash (.hash _)` call is never charged. -/
theorem not_charged_of_ne (t : DeferredQuery C) (ht : ∀ input, t ≠ .hash (.hash input))
    (st : (CompilerBackend C × ℕ) × (HiddenKey → Option Digest)) (g : OwnGhost) :
    ¬ownCharged P seeds t st g := by
  rintro ⟨input, rfl, -⟩
  exact ht input rfl

/-- A bookkeeping call that adds no virtual row, writes no PRF cell at a bottom randomizer, adds no
commitment answer and is no hash call. -/
theorem walk_plain {readyEx cachedEx : Option KeyIndex} (t : DeferredQuery C)
    (A : SourceState C → LState C → Prop) (ht : ∀ e message, t ≠ .bindKey e message)
    (hv : ∀ T e, t ≠ .virtual T (.randomizer bottomLayer e))
    (hw : ∀ T e, ¬WritesPrf (seeds T) (.randomizer bottomLayer e) t)
    (hp : ∀ e, t ≠ .pending (.commitment e)) (hr : ∀ p value, t ≠ .record p value)
    (hh : ∀ input, t ≠ .hash (.hash input)) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ A src st) 0
      (fun y src' st' => BaseInv P seeds readyEx cachedEx src' st' ∧ ∃ st, A src' st ∧
        ∃ x ∈ support ((compilerImpl P seeds t).run st.1.1.1), y = x.1 ∧ st'.1.1.1 = x.2)
      (liftM (deferredQuery t)) :=
  walk_call P seeds Q s t A ht (fun p value he => absurd he (hr p value))
    (fun _ _ _ _ => not_charged_of_ne P seeds t hh _ _)
    (fun src st _ _ x hx => ready_plain P seeds t hv hw src st x hx)
    (fun _ st _ _ x hx => commit_plain P seeds t hp (fun _ value => hr _ value) st x hx)

end Calls

/-! ## Free inputs of the top routines -/

section Free

variable (P : PublicParameter)

theorem free_sequenceFin {α : Type} (n : ℕ) (oa : Fin n → OracleComp HashSpec α)
    (h : ∀ i, XmssSecurity.Bridge.OnlyQueries (FreeInput P) (oa i)) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P) (OverPermutation.sequenceFin oa) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
      simp only [OverPermutation.sequenceFin]
      exact (h 0).bind fun _ => (ih (fun i => oa i.succ) fun i => h i.succ).bind fun _ => .pure _

theorem free_merklePath (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest)
    (key : KeyIndex) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P) (merklePath P lay chainEnd key) :=
  free_sequenceFin P _ _ fun _ => free_merkleNode P lay chainEnd _ _

theorem free_leafHash (lay : Layer) (key : KeyIndex) (endpoints : ChainIndex → Digest) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P)
      (Verification.leafHashWithHash P lay key endpoints : OracleComp HashSpec Digest) :=
  (XmssSecurity.Bridge.onlyQueries_query (free_leaf P lay _ _)).bind fun _ => .pure _

theorem free_treeFold (lay : Layer) (key : KeyIndex) (path : Fin layerHeight → Digest)
    (levels : ℕ) (value : Digest) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P)
      (Verification.treeFoldWithHash P lay key path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => exact .pure _
  | succ levels ih =>
      simp only [Verification.treeFoldWithHash]
      refine ih.bind fun _ => ?_
      split
      · exact (XmssSecurity.Bridge.onlyQueries_query (free_node P lay _ _ _)).bind fun _ => .pure _
      · exact (XmssSecurity.Bridge.onlyQueries_query (free_node P lay _ _ _)).bind fun _ => .pure _

theorem free_topMessageDigest (b : Fin (2 ^ layerHeight)) (root : Digest)
    (randomness : Randomizer) :
    XmssSecurity.Bridge.OnlyQueries (FreeInput P)
      (Verification.messageDigestWithHash P topLayer (topKey b) (littleEndianBytes 16 root) randomness :
        OracleComp HashSpec Digest) := by
  have hfree := free_topDigest P b (root, randomness)
  unfold XmssSecurity.Concrete.CacheView.topEncodingInput at hfree
  rw [← XmssSecurity.Bridge.topMessage_input P b root randomness] at hfree
  exact (XmssSecurity.Bridge.onlyQueries_query hfree).bind fun _ => .pure _

end Free

/-! ## The units of the base source -/

section Units

variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

/-- The virtual terms of a commitment point, which a new commitment answer needs. -/
def CommitReady (p : PendingInput) (st : LState C) : Prop :=
  ∀ e, p = .commitment e → ∀ T, (T, Point.randomizer bottomLayer e) ∈ st.1.1.1.data.virtual

/-- A run of a bookkeeping call keeps the source, extends the backend and keeps `BaseInv`. -/
theorem plain_run {readyEx cachedEx : Option KeyIndex} (t : DeferredQuery C)
    (ht : ∀ e message, t ≠ .bindKey e message)
    (hv : ∀ T e, t ≠ .virtual T (.randomizer bottomLayer e))
    (hw : ∀ T e, ¬WritesPrf (seeds T) (.randomizer bottomLayer e) t)
    (hp : ∀ e, t ≠ .pending (.commitment e)) (hr : ∀ p value, t ≠ .record p value)
    (hh : ∀ input, t ≠ .hash (.hash input)) (src : SourceState C) (st : LState C)
    (h : BaseInv P seeds readyEx cachedEx src st) (r : (DeferredSpec C t × SourceState C) × LState C)
    (hrun : r ∈ support (runL P seeds Q s (liftM (deferredQuery t)) src st)) :
    r.2.2.ledger ≤ st.2.ledger + 0 ∧ Grows st r.2 ∧ BaseInv P seeds readyEx cachedEx src r.2 ∧
      r.1.2 = src ∧ ∃ x ∈ support ((compilerImpl P seeds t).run st.1.1.1),
        r.1.1 = x.1 ∧ r.2.1.1.1 = x.2 := by
  obtain ⟨hl, hg, hq, st0, ⟨rfl, hsrc⟩, x, hx, hy, hst⟩ := walk_plain P seeds Q s
    (readyEx := readyEx) (cachedEx := cachedEx) t (fun src' st' => st' = st ∧ src' = src)
    ht hv hw hp hr hh src st ⟨h, rfl, rfl⟩ r hrun
  subst hsrc
  exact ⟨hl, hg, hq, rfl, x, hx, hy, hst⟩

theorem walk_inspect {readyEx cachedEx : Option KeyIndex} (p : PendingInput)
    (B : SourceState C → LState C → Prop) (hB : ∀ src st st', Grows st st' → B src st → B src st') :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st) 0
      (fun y src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st ∧
        st.1.1.1.data.pending p = y)
      (liftM (deferredQuery (C := C) (.inspect p))) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq, hsrc, x, hx, hy, hst⟩ := plain_run P seeds Q s (.inspect p)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) src st hp.1 r hr
  rw [hsrc]
  refine ⟨hl, hg, hq, hB _ _ _ hg hp.2, ?_⟩
  obtain rfl := compilerImpl_inspect_eq P seeds p _ x hx
  rw [hst, hy]

theorem walk_snapshot {readyEx cachedEx : Option KeyIndex}
    (B : SourceState C → LState C → Prop) (hB : ∀ src st st', Grows st st' → B src st → B src st') :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st) 0
      (fun y src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st ∧ st.1.1.1.data = y)
      (liftM (deferredQuery (C := C) .snapshot)) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq, hsrc, x, hx, hy, hst⟩ := plain_run P seeds Q s .snapshot
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) src st hp.1 r hr
  rw [hsrc]
  refine ⟨hl, hg, hq, hB _ _ _ hg hp.2, ?_⟩
  obtain rfl := compilerImpl_snapshot_eq P seeds _ x hx
  rw [hst, hy]

theorem walk_sample {readyEx cachedEx : Option KeyIndex}
    (B : SourceState C → LState C → Prop) (hB : ∀ src st st', Grows st st' → B src st → B src st') :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st) 0
      (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st)
      (liftM (deferredQuery (C := C) .sample)) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq, hsrc, -⟩ := plain_run P seeds Q s .sample
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) src st hp.1 r hr
  rw [hsrc]
  exact ⟨hl, hg, hq, hB _ _ _ hg hp.2⟩

theorem walk_pad {readyEx cachedEx : Option KeyIndex} (point : Point) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ => BaseInv P seeds readyEx cachedEx)
      (liftM (deferredQuery (C := C) (.pad point))) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq, hsrc, -⟩ := plain_run P seeds Q s (.pad point)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) src st hp r hr
  rw [hsrc]
  exact ⟨hl, hg, hq⟩

theorem walk_uniform {readyEx cachedEx : Option KeyIndex} (n : ℕ) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ => BaseInv P seeds readyEx cachedEx)
      (liftM (deferredQuery (C := C) (.uniform n))) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq, hsrc, -⟩ := plain_run P seeds Q s (.uniform n)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ h => by cases h) src st hp r hr
  rw [hsrc]
  exact ⟨hl, hg, hq⟩

theorem compilerImpl_plant_cached (q : PlantInput) (value : HashOutput) (st : CompilerBackend C)
    (x : Bool × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.plant q value)).run st)) :
    x.2.data.cache (q.query (C := C)) ≠ none := by
  simp only [compilerImpl, StateT.run, support_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  cases hk : st.data.cache q.query with
  | some prior =>
      simp only [deferredImpl, hk, mem_support_pure_iff] at ha
      subst a
      simp [hk]
  | none =>
      simp only [deferredImpl, hk, mem_support_pure_iff] at ha
      subst a
      simp [QueryCache.cacheQuery_self]

/-- A plant. A plant at a PRF cell of a bottom randomizer needs the revealed opening. The planted
cell is cached afterwards. -/
theorem walk_plant {readyEx cachedEx : Option KeyIndex} (q : PlantInput) (value : HashOutput)
    (B : SourceState C → LState C → Prop) (hB : ∀ src st st', Grows st st' → B src st → B src st')
    (hq : ∀ src st, B src st → ∀ T e, q.query (C := C) = .prf (seeds T) (.randomizer bottomLayer e) →
      src.revealed (.opening bottomLayer e) ≠ none) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st) 0
      (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st ∧
        st.1.1.1.data.cache (q.query (C := C)) ≠ none)
      (liftM (deferredQuery (C := C) (.plant q value))) := by
  intro src st hp r hr
  have hready : ∀ src' st', BaseInv P seeds readyEx cachedEx src' st' →
      (st' = st ∧ src' = src) →
      ∀ x ∈ support ((compilerImpl P seeds (.plant q value)).run st'.1.1.1), ∀ e,
        OpeningReady seeds x.2.data src'.signing e →
          OpeningReady seeds st'.1.1.1.data src'.signing e ∨
            src'.revealed (.opening bottomLayer e) ≠ none ∨ readyEx = some e := by
    rintro src' st' - ⟨rfl, rfl⟩ x hx e hready
    by_cases hw : ∀ T, ¬WritesPrf (seeds T) (.randomizer bottomLayer e)
      (DeferredQuery.plant (C := C) q value)
    · exact Or.inl (openingReady_back P seeds _ _ x hx _ e (fun _ h => by cases h) hw hready)
    · obtain ⟨T, hT⟩ := not_forall.mp hw
      exact Or.inr (Or.inl (hq _ _ hp.2 T e (not_not.mp hT)))
  obtain ⟨hl, hg, hq', st0, ⟨rfl, hsrc⟩, x, hx, -, hst⟩ := walk_call P seeds Q s
    (readyEx := readyEx) (cachedEx := cachedEx) (.plant q value)
    (fun src' st' => st' = st ∧ src' = src) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ _ _ _ => not_charged_of_ne P seeds _ (fun _ h => by cases h) _ _) hready
    (fun _ st' _ _ x hx => commit_plain P seeds _ (fun _ h => by cases h)
      (fun _ _ h => by cases h) st' x hx) src st ⟨hp.1, rfl, rfl⟩ r hr
  subst hsrc
  refine ⟨hl, hg, hq', hB _ _ _ hg hp.2, ?_⟩
  rw [hst]
  exact compilerImpl_plant_cached P seeds q value _ x hx

/-- The pending call of a point. A new commitment answer needs the virtual terms of its key. -/
theorem walk_pendingCall {readyEx cachedEx : Option KeyIndex} (p : PendingInput) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ CommitReady p st) 0
      (fun value src st => BaseInv P seeds readyEx cachedEx src st ∧
        st.1.1.1.data.pending p = some value)
      (liftM (deferredQuery (C := C) (.pending p))) := by
  refine Walk.conseq (walk_call P seeds Q s (.pending p) (fun _ st => CommitReady p st)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ st _ _ => not_charged_of_ne P seeds _ (fun _ h => by cases h) _ _)
    (fun src st _ _ x hx => ready_plain P seeds (.pending p) (fun _ _ h => by cases h)
      (fun _ _ h => h) src st x hx) ?_) (fun _ _ h => h) ?_ le_rfl
  · intro src st _ hcr x hx e he
    rcases (compilerImpl_frame P seeds _ _ x hx).2 _ he with h | h | ⟨value, h⟩
    · exact Or.inl h
    · injection h with h
      exact Or.inr fun T =>
        SigningCompilerSyncRows.compilerImpl_virtual_mono P seeds _ _ x hx (hcr e h T)
    · cases h
  · rintro y src' st' ⟨hinv, st0, -, x, hx, rfl, hst⟩
    exact ⟨hinv, by rw [hst]; exact compilerImpl_pending_some P seeds p _ x hx⟩

theorem commitReady_grows (p : PendingInput) (st st' : LState C) (hg : Grows st st')
    (h : CommitReady p st) : CommitReady p st' :=
  fun e he T => hg.virtual (h e he T)

/-- `sourcePending` keeps `BaseInv` and makes no charged call. With a known input, its hash call is
at a revealed key. The answer is the pending answer of the point. -/
theorem walk_sourcePending {readyEx cachedEx : Option KeyIndex} (p : PendingInput) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ CommitReady p st) 0
      (fun value src st => BaseInv P seeds readyEx cachedEx src st ∧
        st.1.1.1.data.pending p = some value)
      (sourcePending P p) := by
  unfold sourcePending
  refine Walk.conseq (c := 0 + (0 + 0)) (Walk.bind (walk_inspect P seeds Q s p (fun _ => CommitReady p)
    (fun _ => commitReady_grows p)) fun prior => Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  dsimp only
  split
  · rename_i input hknown hnext
    refine Walk.conseq (c := 0 + (0 + (0 + 0))) (Walk.bind (walk_call P seeds Q s
        (readyEx := readyEx) (cachedEx := cachedEx) (.hash (.hash (p.input P input)))
        (fun src st => src0 = src ∧ CommitReady p st ∧ st.1.1.1.data.pending p = none)
        (fun _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun src st hinv hA => pending_not_charged P seeds p input _ _
          (by rw [← hinv.reveal, ← hA.1]; simp [hknown]))
        (fun src st _ _ x hx => ready_plain P seeds (.hash (.hash _)) (fun _ _ h => by cases h)
          (fun _ _ h => by cases h) src st x hx)
        (fun _ st _ _ x hx => commit_plain P seeds _ (fun _ h => by cases h)
          (fun _ _ h => by cases h) st x hx))
      fun value => Walk.bind (Walk.conseq (walk_call P seeds Q s (readyEx := readyEx)
        (cachedEx := cachedEx) (.record p value)
        (fun _ st => st.1.1.1.data.pending p = none ∧ CommitReady p st)
        (fun _ _ h => by cases h) (fun _ _ he _ _ _ hA => by cases he; exact hA.1)
        (fun _ st _ _ => not_charged_of_ne P seeds _ (fun _ h => by cases h) _ _)
        (fun src st _ _ x hx => ready_plain P seeds (.record p value) (fun _ _ h => by cases h)
          (fun _ _ h => h) src st x hx) ?_) ?_ (fun _ _ _ h => h) le_rfl)
      fun _ => Walk.bind (Walk.modify (Post := fun _ src st =>
          BaseInv P seeds readyEx cachedEx src st ∧ st.1.1.1.data.pending p = some
            ⟨(XmssSecurity.Rom.hashOutputEquivDigestPair value).1,
              .known (XmssSecurity.Rom.hashOutputEquivDigestPair value).2⟩) _ ?_)
      fun _ => Walk.pure _ fun _ _ h => h) ?_ (fun _ _ _ h => h) le_rfl
    · intro src st _ hA x hx e he
      rcases (compilerImpl_frame P seeds _ _ x hx).2 _ he with h | h | ⟨v, h⟩
      · exact Or.inl h
      · cases h
      · injection h with h1 h2
        exact Or.inr fun T =>
          SigningCompilerSyncRows.compilerImpl_virtual_mono P seeds _ _ x hx (hA.2 e h1 T)
    · rintro src st ⟨hinv, st0, ⟨-, hcr, hnone⟩, x, hx, -, hst⟩
      refine ⟨hinv, ?_, fun e he T => ?_⟩
      · rw [hst]
        by_contra hne
        rcases (compilerImpl_frame P seeds _ _ x hx).2 _ hne with h | h | ⟨v, h⟩
        · exact h hnone
        · cases h
        · cases h
      · rw [hst]
        exact SigningCompilerSyncRows.compilerImpl_virtual_mono P seeds _ _ x hx (hcr e he T)
    · rintro src st ⟨hinv, st1, -, x, hx, -, hst⟩
      refine ⟨BaseInv.of_source P seeds hinv rfl rfl rfl, ?_⟩
      rw [hst, compilerImpl_record_some P seeds p value _ x hx, hnext]
    · exact fun _ _ h => ⟨h.2.1, h.1, h.2.2⟩
  · have tail : ∀ c : Bool, Walk P seeds Q s
        (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ CommitReady p st) 0
        (fun x src st => BaseInv P seeds readyEx cachedEx src st ∧
          st.1.1.1.data.pending p = some x)
        (do
          let value ← liftM (deferredQuery (C := C) (.pending p))
          if c = true then do
              modify fun (st : SourceState C) => { st with allocated := st.allocated ++ [p] }
              pure value
            else do
              pure PUnit.unit
              pure value) := by
      intro c
      refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_pendingCall P seeds Q s p) fun value => ?_)
        (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
      split
      · exact Walk.conseq (c := 0 + 0) (Walk.bind (Walk.modify (Post := fun _ src st =>
          BaseInv P seeds readyEx cachedEx src st ∧ st.1.1.1.data.pending p = some value) _
          fun src st h => ⟨BaseInv.of_source P seeds (src := src) h.1 rfl rfl rfl, h.2⟩) fun _ =>
            Walk.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
      · exact Walk.conseq (c := 0 + 0) (Walk.bind (Walk.pure (Post := fun _ src st =>
          BaseInv P seeds readyEx cachedEx src st ∧ st.1.1.1.data.pending p = some value)
          PUnit.unit fun _ _ h => h) fun _ => Walk.pure _ fun _ _ h => h)
          (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    split
    · exact Walk.conseq (c := 0 + 0) (Walk.bind (Walk.modify (Post := fun _ src st =>
        BaseInv P seeds readyEx cachedEx src st ∧ CommitReady p st) _
        fun src st h => ⟨BaseInv.of_source P seeds (src := src) h.2.1 rfl rfl rfl, h.2.2.1⟩) fun _ => tail _)
        (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    · refine Walk.conseq (tail _) (fun _ _ h => ?_) (fun _ _ _ h => h) le_rfl
      exact ⟨h.2.1, h.2.2.1⟩

/-- A hash call at a free input keeps `BaseInv` and is not charged. -/
theorem walk_freeHash {readyEx cachedEx : Option KeyIndex} (input : HashInput)
    (hfree : FreeInput P input) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ => BaseInv P seeds readyEx cachedEx) (sourceHash P seeds (.hash input)) := by
  simp only [sourceHash, pure_bind]
  exact Walk.conseq (walk_call P seeds Q s (.hash (.hash input)) (fun _ _ => True)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ st _ _ => free_not_charged P seeds input hfree _ _)
    (fun src st _ _ x hx => ready_plain P seeds (.hash (.hash input)) (fun _ _ h => by cases h)
      (fun _ _ h => by cases h) src st x hx)
    (fun _ st _ _ x hx => commit_plain P seeds _ (fun _ h => by cases h)
      (fun _ _ h => by cases h) st x hx))
    (fun _ _ h => ⟨h, trivial⟩) (fun _ _ _ h => h.1) le_rfl

/-- A hash program that queries free inputs only keeps `BaseInv` and makes no charged call. -/
theorem walk_hashProgram {readyEx cachedEx : Option KeyIndex} {α : Type}
    (oa : OracleComp HashSpec α) (h : XmssSecurity.Bridge.OnlyQueries (FreeInput P) oa) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ => BaseInv P seeds readyEx cachedEx) (sourceHashProgram P seeds oa) := by
  induction h with
  | pure a =>
      simp only [sourceHashProgram, deferredHash, simulateQ_pure]
      exact Walk.pure a fun _ _ h => h
  | query x hx next _ ih =>
      simp only [sourceHashProgram, deferredHash, simulateQ_bind, backendQuery, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map]
      exact Walk.conseq (c := 0 + 0) (Walk.bind (walk_freeHash P seeds Q s x hx) ih)
        (fun _ _ h => h) (fun _ _ _ h => h) le_rfl

theorem compilerImpl_virtual_mem (T : C.Term) (point : Point) (st : CompilerBackend C)
    (x : Unit × CompilerBackend C)
    (hx : x ∈ support ((compilerImpl P seeds (.virtual T point)).run st)) :
    (T, point) ∈ x.2.data.virtual := by
  simp only [compilerImpl, deferredImpl, StateT.run, map_pure] at hx
  subst x
  exact Finset.mem_insert_self _ _

/-- The virtual call at a point that is no bottom randomizer. -/
theorem walk_virtualCall {readyEx cachedEx : Option KeyIndex} (T : C.Term) (point : Point)
    (hpoint : ∀ e, point ≠ .randomizer bottomLayer e) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧
        (T, point) ∈ st.1.1.1.data.virtual)
      (liftM (deferredQuery (C := C) (.virtual T point))) := by
  refine Walk.conseq (walk_call P seeds Q s (.virtual T point) (fun _ _ => True)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ st _ _ => not_charged_of_ne P seeds _ (fun _ h => by cases h) _ _)
    (fun src st _ _ x hx => ready_plain P seeds (.virtual T point)
      (fun T' e h => by injection h with h1 h2; exact hpoint e h2) (fun _ _ h => h) src st x hx)
    (fun _ st _ _ x hx => commit_plain P seeds _ (fun _ h => by cases h)
      (fun _ _ h => by cases h) st x hx))
    (fun _ _ h => ⟨h, trivial⟩) ?_ le_rfl
  rintro y src' st' ⟨hinv, st0, -, x, hx, -, hst⟩
  exact ⟨hinv, by rw [hst]; exact compilerImpl_virtual_mem P seeds T point _ x hx⟩

/-- `sourceVirtual` at a point that is no bottom randomizer. -/
theorem walk_sourceVirtual_other {readyEx cachedEx : Option KeyIndex} (T : C.Term) (point : Point)
    (hpoint : ∀ e, point ≠ .randomizer bottomLayer e) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧
        (T, point) ∈ st.1.1.1.data.virtual)
      (sourceVirtual P seeds T point) := by
  unfold sourceVirtual
  refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_virtualCall P seeds Q s T point hpoint)
    fun _ => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  cases point with
  | chain lay e l d => exact Walk.pure _ fun _ _ h => h
  | randomizer lay e =>
      have hlay : lay ≠ bottomLayer := by
        rintro rfl
        exact hpoint e rfl
      simp only [hlay, if_false]
      exact Walk.pure _ fun _ _ h => h

theorem walk_sourceTopEnd (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (simulateQ (sourceBackend P seeds) (deferredTopEnd b l)) := by
  have hpend : ∀ i, Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun _ => BaseInv P seeds none none) (sourcePending P (.top b l i)) := fun i =>
    Walk.conseq (walk_sourcePending P seeds Q s (.top b l i)) (fun _ _ h => ⟨h, fun _ he => by
      cases he⟩) (fun _ _ _ h => h.1) le_rfl
  simp only [deferredTopEnd, simulateQ_bind, simulateQ_pure, backendQuery,
    simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  erw [simulateQ_list_mapM]
  refine Walk.conseq (c := C.terms.length * 0 + (0 + (0 + (0 + 0)))) (Walk.bind
    (Walk.mapM _ _ _ fun T _ => Walk.conseq (walk_sourceVirtual_other P seeds Q s T _
      (fun _ h => by cases h)) (fun _ _ h => h) (fun _ _ _ h => h.1) le_rfl)
    fun _ => Walk.bind (hpend _) fun _ => Walk.bind (hpend _) fun _ => Walk.bind (hpend _)
      fun _ => Walk.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (by simp)

theorem walk_sourceTopTree :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceTopTree P seeds) := by
  simp only [sourceTopTree, deferredTopTree, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure]
  refine Walk.conseq (c := _ * 0 + (0 + 0)) (Walk.bind
    (Walk.mapM _ _ _ fun bl _ => walk_sourceTopEnd P seeds Q s bl.1 bl.2) fun ends =>
      Walk.bind (walk_hashProgram P seeds Q s _ (free_merkleNode P topLayer _ layerHeight 0))
        fun _ => Walk.pure _ fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (by simp)

/-- `fillTerm` caches its term. A plant at a bottom randomizer needs the revealed opening. -/
theorem walk_fillTerm {readyEx cachedEx : Option KeyIndex} (point : Point) (T : C.Term)
    (B : SourceState C → LState C → Prop) (hB : ∀ src st st', Grows st st' → B src st → B src st')
    (hrev : ∀ src st, B src st → ∀ e, point = .randomizer bottomLayer e →
      src.revealed (.opening bottomLayer e) ≠ none) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st) 0
      (fun _ src st => (BaseInv P seeds readyEx cachedEx src st ∧ B src st) ∧
        st.1.1.1.data.cache (.prf (seeds T) point) ≠ none)
      (liftM (fillTerm seeds point T)) := by
  unfold fillTerm
  rw [liftM_bind]
  refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_snapshot P seeds Q s B hB) fun y => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · rename_i hnone
    rw [liftM_bind]
    refine Walk.conseq (c := 0 + (0 + 0)) (Walk.bind (Walk.conseq (walk_sample P seeds Q s B hB)
      (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ h => h) le_rfl) fun v => ?_)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    rw [liftM_bind]
    refine Walk.bind (walk_plant P seeds Q s (.prf (seeds T) point) v B hB ?_) fun _ => ?_
    · intro src st hb T' e he
      exact hrev src st hb e (Query.prf.inj he).2
    · rw [liftM_pure]
      exact Walk.pure _ fun _ _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · rename_i hsome
    rw [liftM_pure]
    refine Walk.pure _ fun src st h => ⟨⟨h.1, h.2.1⟩, ?_⟩
    rw [h.2.2]
    intro hn
    exact hsome (by rw [hn]; rfl)

/-- `completePrf` caches each term of its point. A plant at a bottom randomizer needs the revealed
opening. -/
theorem walk_completePrf {readyEx cachedEx : Option KeyIndex} (point : Point) (target : Digest)
    (B : SourceState C → LState C → Prop) (hB : ∀ src st st', Grows st st' → B src st → B src st')
    (hrev : ∀ src st, B src st → ∀ e, point = .randomizer bottomLayer e →
      src.revealed (.opening bottomLayer e) ≠ none) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st) 0
      (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧ B src st ∧
        ∀ T, st.1.1.1.data.cache (.prf (seeds T) point) ≠ none)
      (liftM (completePrf seeds point target)) := by
  unfold completePrf
  rw [liftM_bind]
  refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_snapshot P seeds Q s B hB) fun y => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · rename_i hnone
    rw [liftM_pure]
    refine Walk.pure _ fun src st h => ⟨h.1, h.2.1, fun T => ?_⟩
    obtain ⟨value, hv⟩ := (firstUnmaterialized_none_iff seeds y point).mp hnone T
    rw [h.2.2, hv]
    simp
  · rename_i slack hslack
    have hcached : ∀ st st' : LState C, Grows st st' → ∀ T,
        st.1.1.1.data.cache (.prf (seeds T) point) ≠ none →
          st'.1.1.1.data.cache (.prf (seeds T) point) ≠ none := by
      intro st st' hg T hT hn
      obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp hT
      rw [hg.cache hv] at hn
      cases hn
    rw [liftM_bind]
    refine Walk.conseq (c := (C.terms.filter (· ≠ slack)).length * 0 + 0)
      (Walk.bind (Walk.liftM_mapM _ (fun src st => BaseInv P seeds readyEx cachedEx src st ∧
        B src st) (fun T st => st.1.1.1.data.cache (.prf (seeds T) point) ≠ none)
        (fun T st st' hg => hcached st st' hg T) _
        fun T _ => walk_fillTerm P seeds Q s point T B hB hrev) fun _ => ?_)
      (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ h => h) (by simp)
    rw [liftM_bind]
    refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_snapshot P seeds Q s (fun src st => B src st ∧
      ∀ T ∈ C.terms.filter (· ≠ slack), st.1.1.1.data.cache (.prf (seeds T) point) ≠ none)
      (fun src st st' hg h => ⟨hB src st st' hg h.1, fun T hT => hcached st st' hg T (h.2 T hT)⟩))
      fun st' => ?_) (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ _ h => h) le_rfl
    erw [liftM_bind]
    refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_sample P seeds Q s (fun src st => B src st ∧
      ∀ T ∈ C.terms.filter (· ≠ slack), st.1.1.1.data.cache (.prf (seeds T) point) ≠ none)
      (fun src st st' hg h => ⟨hB src st st' hg h.1, fun T hT => hcached st st' hg T (h.2 T hT)⟩))
      fun high => ?_) (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ h => h) le_rfl
    refine Walk.conseq (walk_plant P seeds Q s (.prf (seeds slack) point) _ (fun src st => B src st ∧
      ∀ T ∈ C.terms.filter (· ≠ slack), st.1.1.1.data.cache (.prf (seeds T) point) ≠ none)
      (fun src st st' hg h => ⟨hB src st st' hg h.1, fun T hT => hcached st st' hg T (h.2 T hT)⟩)
      (fun src st h T e he => hrev src st h.1 e (Query.prf.inj he).2))
      (fun _ _ h => h) ?_ le_rfl
    intro _ src st h
    refine ⟨h.1, h.2.1.1, fun T => ?_⟩
    by_cases hT : T = slack
    · subst hT
      exact h.2.2
    · exact h.2.1.2 T (List.mem_filter.mpr ⟨mem_terms T, by simpa using hT⟩)

/-- A reveal keeps `BaseInv`. The exceptions may move to the revealed key. -/
theorem baseInv_reveal {readyEx cachedEx readyEx' cachedEx' : Option KeyIndex}
    {src : SourceState C} {st : LState C} (h : BaseInv P seeds readyEx cachedEx src st)
    (k : HiddenKey) (v : Digest)
    (hready : ∀ e, readyEx' ≠ some e → readyEx = some e → k = .opening bottomLayer e)
    (hcached : ∀ e, cachedEx' ≠ some e → k ≠ .opening bottomLayer e)
    (hcx : ∀ e, cachedEx' ≠ some e → cachedEx ≠ some e) :
    BaseInv P seeds readyEx' cachedEx' { src with revealed := Function.update src.revealed k (some v) }
      ((st.1.1, Function.update st.1.2.1 k (some v), st.1.2.2), st.2) := by
  refine ⟨by simp only [h.reveal], h.bound, ?_, h.commitTerms, h.treeCommit, ?_, h.releasedBound,
    h.corruptBound, h.reachable, h.dirtySecond, h.storedTopShape⟩
  · intro e hne hr
    by_cases hre : readyEx = some e
    · rw [hready e hne hre]
      simp
    · have hold := h.ready e hre hr
      by_cases hke : k = .opening bottomLayer e
      · rw [hke]
        simp
      · simpa only [Function.update_of_ne (Ne.symm hke)] using hold
  · intro e hne hr
    have hke := hcached e hne
    refine h.revealedCached e (hcx e hne) ?_
    simpa only [Function.update_of_ne (Ne.symm hke)] using hr

/-- A revealed key keeps `BaseInv` with the exceptions of `baseInv_reveal`. -/
theorem baseInv_revealed {readyEx cachedEx readyEx' cachedEx' : Option KeyIndex}
    {src : SourceState C} {st : LState C} (h : BaseInv P seeds readyEx cachedEx src st)
    (k : HiddenKey) (hk : src.revealed k ≠ none)
    (hready : ∀ e, readyEx' ≠ some e → readyEx = some e → k = .opening bottomLayer e)
    (hcx : ∀ e, cachedEx' ≠ some e → cachedEx ≠ some e) :
    BaseInv P seeds readyEx' cachedEx' src st := by
  refine ⟨h.reveal, h.bound, ?_, h.commitTerms, h.treeCommit, ?_, h.releasedBound,
    h.corruptBound, h.reachable, h.dirtySecond, h.storedTopShape⟩
  · intro e hne hr
    by_cases hre : readyEx = some e
    · rw [← hready e hne hre]
      exact hk
    · exact h.ready e hre hr
  · intro e hne hr
    exact h.revealedCached e (hcx e hne) hr

/-- `sourceReveal`, with a frame `F` that a reveal keeps. -/
theorem walk_sourceReveal {readyEx cachedEx readyEx' cachedEx' : Option KeyIndex} (k : HiddenKey)
    (hready : ∀ e, readyEx' ≠ some e → readyEx = some e → k = .opening bottomLayer e)
    (hcached : ∀ e, cachedEx' ≠ some e → k ≠ .opening bottomLayer e)
    (hcx : ∀ e, cachedEx' ≠ some e → cachedEx ≠ some e)
    (F : SourceState C → LState C → Prop)
    (hF : ∀ src st v, F src st → F { src with revealed := Function.update src.revealed k (some v) }
      ((st.1.1, Function.update st.1.2.1 k (some v), st.1.2.2), st.2)) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ F src st) 0
      (fun _ src st => BaseInv P seeds readyEx' cachedEx' src st ∧ F src st ∧
        src.revealed k ≠ none)
      (sourceReveal k) := by
  unfold sourceReveal
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · rename_i value hv
    refine Walk.pure _ fun src st h => ?_
    obtain ⟨rfl, hinv, hf⟩ := h
    exact ⟨baseInv_revealed P seeds hinv k (by rw [hv]; simp) hready hcx, hf, by rw [hv]; simp⟩
  · rename_i hnone
    refine Walk.conseq (c := 0 + (0 + 0)) (Walk.bind (walk_reveal P seeds Q s k _) fun v =>
      Walk.bind (Walk.modify (Post := fun _ src st => BaseInv P seeds readyEx' cachedEx' src st ∧
        F src st ∧ src.revealed k ≠ none) _ ?_) fun _ => Walk.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    rintro src st ⟨st0, ⟨rfl, hinv, hf⟩, rfl, rfl⟩
    have hstored : st0.1.2.1 k = none := by rw [← hinv.reveal, hnone]
    rw [hstored]
    exact ⟨baseInv_reveal P seeds hinv k _ hready hcached hcx, hF _ _ _ hf, by simp⟩

theorem BaseInv.weaken_ready {cachedEx : Option KeyIndex} {src : SourceState C} {st : LState C}
    (h : BaseInv P seeds none cachedEx src st) (e : KeyIndex) :
    BaseInv P seeds (some e) cachedEx src st :=
  ⟨h.reveal, h.bound, fun e' _ hr => h.ready e' (by simp) hr, h.commitTerms, h.treeCommit,
    h.revealedCached, h.releasedBound, h.corruptBound, h.reachable, h.dirtySecond,
    h.storedTopShape⟩

theorem BaseInv.close_ready {cachedEx : Option KeyIndex} {src : SourceState C} {st : LState C}
    {e : KeyIndex} (h : BaseInv P seeds (some e) cachedEx src st)
    (hr : OpeningReady seeds st.1.1.1.data src.signing e →
      src.revealed (.opening bottomLayer e) ≠ none) :
    BaseInv P seeds none cachedEx src st := by
  refine ⟨h.reveal, h.bound, fun e' _ hr' => ?_, h.commitTerms, h.treeCommit,
    h.revealedCached, h.releasedBound, h.corruptBound, h.reachable, h.dirtySecond,
    h.storedTopShape⟩
  by_cases he : e' = e
  · subst he
    exact hr hr'
  · exact h.ready e' (by simpa using Ne.symm he) hr'

theorem BaseInv.close_cached {readyEx : Option KeyIndex} {src : SourceState C} {st : LState C}
    {e : KeyIndex} (h : BaseInv P seeds readyEx (some e) src st)
    (hc : ∀ T, st.1.1.1.data.cache (.prf (seeds T) (.randomizer bottomLayer e)) ≠ none) :
    BaseInv P seeds readyEx none src st := by
  refine ⟨h.reveal, h.bound, h.ready, h.commitTerms, h.treeCommit, fun e' _ hr => ?_,
    h.releasedBound, h.corruptBound, h.reachable, h.dirtySecond, h.storedTopShape⟩
  by_cases he : e' = e
  · subst he
    exact fun T => Option.ne_none_iff_exists'.mp (hc T)
  · exact h.revealedCached e' (by simpa using Ne.symm he) hr

/-- The next key of a pending point is a chain key. -/
theorem next_ne_opening (p : PendingInput) (k : HiddenKey) (hk : p.next = some k) (e : KeyIndex) :
    k ≠ .opening bottomLayer e := by
  cases p with
  | bottom e' l step =>
      simp only [PendingInput.next] at hk
      split at hk
      · cases hk
        exact fun h => by cases h
      · cases hk
  | top b l step =>
      simp only [PendingInput.next] at hk
      split at hk
      · cases hk
        exact fun h => by cases h
      · cases hk
  | commitment e' => cases hk
  | base lay e' message => cases hk

/-- `sourceReveal` at a revealed key. -/
theorem walk_sourceReveal_known (k : HiddenKey) (Pre : SourceState C → LState C → Prop) :
    Walk P seeds Q s (fun src st => Pre src st ∧ src.revealed k ≠ none) 0
      (fun _ src st => Pre src st ∧ src.revealed k ≠ none) (sourceReveal k) := by
  unfold sourceReveal
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · exact Walk.pure _ fun src st h => by obtain ⟨rfl, h⟩ := h; exact h
  · rename_i hnone
    intro src st h
    obtain ⟨rfl, -, h⟩ := h
    exact absurd hnone h

/-- A fact that each state of the precondition gives. -/
theorem Walk.assume {α : Type} {oa : SourceM C α} {Pre : SourceState C → LState C → Prop}
    {Post : α → SourceState C → LState C → Prop} {c : ℕ} (φ : Prop)
    (hφ : ∀ src st, Pre src st → φ) (h : φ → Walk P seeds Q s Pre c Post oa) :
    Walk P seeds Q s Pre c Post oa :=
  fun src st hp => h (hφ src st hp) src st hp

/-- `sourcePlant` at a point whose key is revealed when it is a bottom opening. It keeps the
revealed key `K` revealed. -/
theorem walk_sourcePlant {readyEx cachedEx : Option KeyIndex} (p : PendingInput)
    (K : HiddenKey) :
    Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧
        ((∀ e, p.key = .opening bottomLayer e → src.revealed p.key ≠ none) ∧
          src.revealed K ≠ none))
      0 (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧
        ((∀ e, p.key = .opening bottomLayer e → src.revealed p.key ≠ none) ∧
          src.revealed K ≠ none))
      (sourcePlant P p) := by
  let F : SourceState C → LState C → Prop := fun src _ =>
    (∀ e, p.key = .opening bottomLayer e → src.revealed p.key ≠ none) ∧ src.revealed K ≠ none
  have hF : ∀ (k : HiddenKey) (src : SourceState C) (st : LState C) (v : Digest), F src st →
      F { src with revealed := Function.update src.revealed k (some v) }
        ((st.1.1, Function.update st.1.2.1 k (some v), st.1.2.2), st.2) := by
    intro k src st v h
    have mono : ∀ k', src.revealed k' ≠ none →
        Function.update src.revealed k (some v) k' ≠ none := by
      intro k' hk'
      by_cases he : k' = k
      · subst he
        simp
      · simpa only [Function.update_of_ne he] using hk'
    exact ⟨fun e he => mono _ (h.1 e he), mono _ h.2⟩
  have reveal : ∀ k : HiddenKey, (∀ e, k ≠ .opening bottomLayer e) →
      Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ F src st) 0
        (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧ F src st)
        (sourceReveal k) := fun k hk =>
    Walk.conseq (walk_sourceReveal P seeds Q s k (fun e hne hre => absurd hre hne)
      (fun e _ => hk e) (fun _ h => h) F (hF k)) (fun _ _ h => h)
      (fun _ _ _ h => ⟨h.1, h.2.1⟩) le_rfl
  unfold sourcePlant
  refine Walk.conseq (c := 0 + 0) (Walk.bind (walk_inspect P seeds Q s p F
    (fun _ _ _ _ h => h)) fun prior => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · rename_i answer
    refine Walk.assume P seeds Q s ((∃ k, p.next = some k ∧ answer.low = .secret k) ∨
      (p.next = none ∧ ∃ d, answer.low = .known d)) ?_ fun hlow => ?_
    · intro src st h
      exact CompilerReachable.pendingValid P seeds _ h.1.reachable p answer h.2.2
    · have hkey : Walk P seeds Q s (fun src st => BaseInv P seeds readyEx cachedEx src st ∧
          F src st) 0 (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧ F src st)
          (sourceReveal p.key) := by
        by_cases hk : ∃ e, p.key = .opening bottomLayer e
        · obtain ⟨e, he⟩ := hk
          exact Walk.conseq (walk_sourceReveal_known P seeds Q s p.key
            (fun src st => BaseInv P seeds readyEx cachedEx src st ∧ F src st))
            (fun _ _ h => ⟨h, h.2.1 e he⟩) (fun _ _ _ h => h.1) le_rfl
        · exact reveal p.key (fun e he => hk ⟨e, he⟩)
      have hdigest : ∀ low : DeferredDigest, (∀ k, low = .secret k → ∀ e,
          k ≠ .opening bottomLayer e) → Walk P seeds Q s (fun src st =>
            BaseInv P seeds readyEx cachedEx src st ∧ F src st) 0
          (fun _ src st => BaseInv P seeds readyEx cachedEx src st ∧ F src st)
          (sourceRevealDigest low) := by
        intro low hl
        cases low with
        | known d => exact Walk.pure _ fun _ _ h => h
        | secret k => exact reveal k (hl k rfl)
      refine Walk.conseq (c := 0 + (0 + (0 + 0))) (Walk.bind (Walk.conseq hkey
        (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ h => h) le_rfl) fun input =>
        Walk.bind (hdigest answer.low ?_) fun low =>
        Walk.bind (walk_plant P seeds Q s (.pending P p input) _ F (fun _ _ _ _ h => h)
          (fun _ _ _ T e he => by cases he)) fun ok =>
        Walk.modify _ fun src st h => ⟨BaseInv.of_source P seeds (src := src) h.1 rfl rfl rfl,
          h.2.1⟩) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
      intro k hk e
      rcases hlow with ⟨k', hn, hl⟩ | ⟨_, d, hl⟩
      · rw [hl] at hk
        injection hk with hk
        rw [← hk]
        exact next_ne_opening p k' hn e
      · rw [hl] at hk
        cases hk
  · exact Walk.pure _ fun _ _ h => ⟨h.1, h.2.1⟩

/-- The release of a bottom opening. It reveals the opening, caches each term of its randomizer
and plants the pending points of the key. It ends with no exception. -/
theorem walk_sourceReleaseOpening (e : KeyIndex) :
    Walk P seeds Q s (BaseInv P seeds (some e) none) 0 (fun _ => BaseInv P seeds none none)
      (sourceReleaseOpening P seeds e) := by
  unfold sourceReleaseOpening
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · let K : HiddenKey := .opening bottomLayer e
    let R : SourceState C → LState C → Prop := fun src _ => src.revealed K ≠ none
    have hplants : ∀ src1 : SourceState C, Walk P seeds Q s
        (fun src st => BaseInv P seeds none none src st ∧ R src st) 0
        (fun _ src st => BaseInv P seeds none none src st ∧ R src st)
        ((src1.allocated.filter fun p => decide (p.key = K)).mapM (sourcePlant P)) := by
      intro src1
      refine Walk.conseq (Walk.mapM (c := 0) _ (sourcePlant P) _ fun p hp => ?_) (fun _ _ h => h)
        (fun _ _ _ h => h) (by simp)
      have hk : p.key = K := of_decide_eq_true (List.mem_filter.mp hp).2
      exact Walk.conseq (walk_sourcePlant P seeds Q s p K)
        (fun _ _ h => ⟨h.1, fun _ _ => by rw [hk]; exact h.2, h.2⟩)
        (fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    refine Walk.conseq (c := 0 + (0 + (0 + (0 + (0 + 0))))) (Walk.bind (Walk.conseq
      (walk_sourceReveal P seeds Q s (readyEx := some e) (cachedEx := none) (readyEx' := none)
        (cachedEx' := some e) K ?_ ?_ ?_ (fun _ _ => True) (fun _ _ _ _ => trivial))
      (fun _ _ h => ⟨h.2, trivial⟩) (fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl) fun value =>
      Walk.bind (Walk.conseq (Post' := fun _ src st => BaseInv P seeds none none src st ∧ R src st)
        (walk_completePrf P seeds Q s (readyEx := none) (cachedEx := some e)
        (.randomizer bottomLayer e) value R (fun _ _ _ _ h => h) ?_) (fun _ _ h => h)
        (fun _ src st h => ⟨BaseInv.close_cached P seeds h.1 h.2.2, h.2.1⟩) le_rfl) fun ok =>
      Walk.bind (Walk.modify (Post := fun _ src st => BaseInv P seeds none none src st ∧ R src st) _
        fun src st h => ⟨BaseInv.of_source P seeds (src := src) h.1 rfl rfl rfl, h.2⟩) fun _ =>
      Walk.bind Walk.get fun src1 => Walk.bind (Walk.conseq (hplants src1) (fun _ _ h => h.2)
        (fun _ _ _ h => h) le_rfl) fun _ => Walk.pure _ fun _ _ h => h.1)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    · intro e' hne hre
      cases hre
      rfl
    · intro e' hne hke
      have he : e = e' := by
        simp only [K, HiddenKey.opening.injEq] at hke
        exact hke.2
      exact hne (by rw [he])
    · intro _ _
      simp
    · intro src st h e' he
      cases he
      exact h
  · rename_i hrev
    refine Walk.pure _ fun src st h => ?_
    obtain ⟨rfl, h⟩ := h
    refine baseInv_revealed P seeds h (.opening bottomLayer e) ?_ ?_ (fun _ _ => by simp)
    · simpa using hrev
    · intro e' _ hre
      cases hre
      rfl

/-- The virtual call at a bottom randomizer. Its key may become ready. -/
theorem walk_virtualCall_bottom {cachedEx : Option KeyIndex} (T : C.Term) (e : KeyIndex) :
    Walk P seeds Q s (BaseInv P seeds none cachedEx) 0
      (fun _ src st => BaseInv P seeds (some e) cachedEx src st ∧
        (T, Point.randomizer bottomLayer e) ∈ st.1.1.1.data.virtual)
      (liftM (deferredQuery (C := C) (.virtual T (.randomizer bottomLayer e)))) := by
  refine Walk.conseq (walk_call P seeds Q s (readyEx := some e) (cachedEx := cachedEx)
    (.virtual T (.randomizer bottomLayer e)) (fun _ _ => True)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ st _ _ => not_charged_of_ne P seeds _ (fun _ h => by cases h) _ _) ?_
    (fun _ st _ _ x hx => commit_plain P seeds _ (fun _ h => by cases h)
      (fun _ _ h => by cases h) st x hx))
    (fun _ _ h => ⟨BaseInv.weaken_ready P seeds h e, trivial⟩) ?_ le_rfl
  · intro src st _ _ x hx e' hr
    by_cases he : e' = e
    · exact Or.inr (Or.inr (by rw [he]))
    · refine Or.inl (openingReady_back P seeds _ _ x hx _ e' (fun T' h => ?_) (fun _ h => h) hr)
      injection h with h1 h2
      injection h2 with h3 h4
      exact he h4.symm
  · rintro y src' st' ⟨hinv, st0, -, x, hx, -, hst⟩
    exact ⟨hinv, by rw [hst]; exact compilerImpl_virtual_mem P seeds T _ _ x hx⟩

/-- `sourceVirtual` keeps `BaseInv` and makes no charged call. At a bottom randomizer it releases
the opening of a key that becomes ready. -/
theorem walk_sourceVirtual (T : C.Term) (point : Point) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun _ src st => BaseInv P seeds none none src st ∧ (T, point) ∈ st.1.1.1.data.virtual)
      (sourceVirtual P seeds T point) := by
  by_cases hpoint : ∃ e, point = .randomizer bottomLayer e
  · obtain ⟨e, rfl⟩ := hpoint
    let M : LState C → Prop := fun st => (T, Point.randomizer bottomLayer e) ∈ st.1.1.1.data.virtual
    have hM : ∀ st st', Grows st st' → M st → M st' := fun _ _ hg h => hg.virtual h
    unfold sourceVirtual
    refine Walk.conseq (c := 0 + (0 + (0 + 0))) (Walk.bind (walk_virtualCall_bottom P seeds Q s T e)
      fun _ => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
    simp only [if_true]
    refine Walk.bind (walk_snapshot P seeds Q s (fun _ st => M st) (fun _ => hM)) fun y =>
      Walk.bind Walk.get fun src0 => ?_
    split
    · exact Walk.conseq (Walk.frame M hM (walk_sourceReleaseOpening P seeds Q s e))
        (fun _ _ h => ⟨h.2.1, h.2.2.1⟩) (fun _ _ _ h => h) le_rfl
    · rename_i hready
      refine Walk.pure _ fun src st h => ?_
      obtain ⟨rfl, hinv, hm, hy⟩ := h
      refine ⟨BaseInv.close_ready P seeds hinv fun hr => absurd (hy ▸ hr) hready, hm⟩
  · exact walk_sourceVirtual_other P seeds Q s T point fun e he => hpoint ⟨e, he⟩

/-- The virtual calls of the terms at one point make each term virtual. -/
theorem walk_virtualTerms (point : Point) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun _ src st => BaseInv P seeds none none src st ∧
        ∀ T, (T, point) ∈ st.1.1.1.data.virtual)
      (C.terms.mapM fun T => sourceVirtual P seeds T point) := by
  have h := Walk.mapM_prefix (P := P) (seeds := seeds) (Q := Q) (s := s) (c := 0)
    (fun T => sourceVirtual P seeds T point)
    (fun done src st => BaseInv P seeds none none src st ∧
      ∀ T ∈ done, (T, point) ∈ st.1.1.1.data.virtual) C.terms [] fun pre a _ _ =>
    Walk.conseq (Walk.frame (fun st => ∀ T ∈ pre, (T, point) ∈ st.1.1.1.data.virtual)
      (fun _ _ hg h T hT => hg.virtual (h T hT)) (walk_sourceVirtual P seeds Q s a point))
      (fun _ _ h => h) (fun _ _ _ h => ⟨h.1.1, fun T hT => (List.mem_append.mp hT).elim (h.2 T)
        fun he => by rw [List.mem_singleton.mp he]; exact h.1.2⟩) le_rfl
  exact Walk.conseq h (fun _ _ h => ⟨h, fun _ hT => by cases hT⟩)
    (fun _ _ _ h => ⟨h.1, fun T => h.2 T (by simpa using mem_terms T)⟩) (by simp)

/-- `sourceCommitment` keeps `BaseInv` and makes no charged call. Its result is the known low half
of the commitment answer of its key. -/
theorem walk_sourceCommitment (e : KeyIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun d src st => BaseInv P seeds none none src st ∧
        ∃ c, st.1.1.1.data.pending (.commitment e) = some c ∧ c.low = .known d)
      (sourceCommitment P seeds e) := by
  unfold sourceCommitment
  refine Walk.conseq (c := 0 + (0 + 0)) (Walk.bind (walk_virtualTerms P seeds Q s _) fun _ =>
    Walk.bind (Walk.conseq (walk_sourcePending P seeds Q s (.commitment e))
      (fun _ _ h => ⟨h.1, fun e' he T => by cases he; exact h.2 T⟩) (fun _ _ _ h => h) le_rfl)
      fun value => Walk.pure _ fun src st h => ⟨h.1, value, h.2, ?_⟩)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  rcases CompilerReachable.pendingValid P seeds _ h.1.reachable _ value h.2 with
    ⟨k, hk, -⟩ | ⟨-, d, hd⟩
  · cases hk
  · rw [hd]

/-- `sourcePending` at a point that is no commitment. -/
theorem walk_sourcePending_other {readyEx cachedEx : Option KeyIndex} (p : PendingInput)
    (hp : ∀ e, p ≠ .commitment e) :
    Walk P seeds Q s (BaseInv P seeds readyEx cachedEx) 0
      (fun _ => BaseInv P seeds readyEx cachedEx) (sourcePending P p) :=
  Walk.conseq (walk_sourcePending P seeds Q s p) (fun _ _ h => ⟨h, fun e he => absurd he (hp e)⟩)
    (fun _ _ _ h => h.1) le_rfl

theorem walk_sourceBottomRow (e : KeyIndex) (l : ChainIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceBottomRow P seeds e l) := by
  have hpend : ∀ p ∈ bottomRowCalls e l, Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun _ => BaseInv P seeds none none)
      (simulateQ (sourceBackend P seeds) (liftM (OracleSpec.query (spec := DeferredSpec C)
        (DeferredQuery.pending p)))) := by
    intro p hp
    rw [simulateQ_spec_query]
    refine walk_sourcePending_other P seeds Q s p fun e' he => ?_
    simp only [bottomRowCalls, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> cases he
  simp only [sourceBottomRow, deferredBottomRow, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_pure, backendQuery, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  erw [simulateQ_list_mapM]
  refine Walk.conseq (c := _ * 0 + (0 + (0 + (_ * 0 + 0)))) (Walk.bind
    (Walk.mapM _ _ _ fun t ht => ?_) fun _ => Walk.bind (walk_pad P seeds Q s _) fun _ =>
      Walk.bind (walk_pad P seeds Q s _) fun _ => Walk.bind (Walk.mapM _ _ _ fun p hp =>
        hpend p hp) fun _ => Walk.pure _ fun _ _ h => h)
    (fun _ _ h => h) (fun _ _ _ h => h) (by simp)
  · obtain ⟨pos, _, hm⟩ := List.mem_flatMap.mp ht
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hm
    exact Walk.conseq (c := 0 + 0) (Walk.bind (walk_sourceVirtual P seeds Q s T _) fun _ =>
      Walk.pure _ fun _ _ h => h.1) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl

theorem walk_sourceTopValue (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : WinternitzDigit) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceTopValue P seeds b l pos) := by
  unfold sourceTopValue
  exact Walk.conseq (c := 0 + (_ * 0 + 0)) (Walk.bind (Walk.conseq (walk_virtualTerms P seeds Q s _)
    (fun _ _ h => h) (fun _ _ _ h => h.1) le_rfl) fun _ =>
      Walk.bind (Walk.mapM _ _ _ fun i _ => walk_sourcePending_other P seeds Q s _
        fun _ h => by cases h) fun _ => Walk.pure _ fun _ _ h => h)
    (fun _ _ h => h) (fun _ _ _ h => h) (by simp)

theorem walk_sourceTopRecover (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : WinternitzDigit)
    (initial : DeferredDigest) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceTopRecover P b l pos initial) := by
  unfold sourceTopRecover
  refine Walk.conseq (c := _ * 0 + 0) (Walk.bind (Walk.mapM _ _ _ fun i _ =>
    walk_sourcePending_other P seeds Q s _ fun _ h => by cases h) fun values => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) (by simp)
  dsimp only
  split
  · exact Walk.pure _ fun _ _ h => h
  · exact Walk.conseq (c := 0 + 0) (Walk.bind (Walk.modify (Post := fun _ =>
      BaseInv P seeds none none) _ fun src st h =>
      BaseInv.of_source P seeds (src := src) h rfl rfl rfl) fun _ => Walk.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl

theorem bottomKey_mod (b k : Fin (2 ^ layerHeight)) :
    (bottomKey b k).val % 2 ^ layerHeight = k.val := by
  show (2 ^ layerHeight * b.val + k.val) % 2 ^ layerHeight = k.val
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]

/-- The commitments of the keys of a bottom tree. Each result is the known low half of the
commitment answer of its key. -/
theorem walk_commitments (b : XmssSecurity.TopIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun ds src st => BaseInv P seeds none none src st ∧ ∀ k : Fin (2 ^ layerHeight),
        ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
          c.low = .known (ds.getD k.val 0))
      ((List.finRange (2 ^ layerHeight)).mapM fun k => sourceCommitment P seeds (bottomKey b k)) :=
  Walk.conseq (Walk.mapM_rel (c := 0) _ _ (fun k d st => ∃ c,
      st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧ c.low = .known d)
    (fun _ _ _ _ hg ⟨c, hc, hl⟩ => ⟨c, hg.pending _ _ hc, hl⟩) _
    fun k _ => walk_sourceCommitment P seeds Q s (bottomKey b k))
    (fun _ _ h => h) (fun _ _ _ h => ⟨h.1, fun k => forall₂_finRange 0 h.2 k⟩) (by simp)

/-- `sourceBottomTree` keeps `BaseInv` and makes no charged call. Each key of the tree has a
commitment answer, and a successful tree holds its low half. -/
theorem walk_sourceBottomTree (top : TopTree) (b : XmssSecurity.TopIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun r src st => BaseInv P seeds none none src st ∧ ∀ k : Fin (2 ^ layerHeight),
        ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
          ∀ tree, r = some tree → c.low = .known (tree.commitment (bottomKey b k)))
      (sourceBottomTree P seeds top b) := by
  unfold sourceBottomTree
  refine Walk.conseq (c := _ * 0 + (0 + 0)) (Walk.bind (Walk.mapM _ _ _ fun el _ =>
    walk_sourceBottomRow P seeds Q s el.1 el.2) fun rows =>
      Walk.bind (walk_commitments P seeds Q s b) fun ds => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) (by simp)
  let CF : LState C → Prop := fun st => ∀ k : Fin (2 ^ layerHeight),
    ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
      c.low = .known (ds.getD k.val 0)
  have hCF : ∀ st st', Grows st st' → CF st → CF st' := fun _ _ hg h k => by
    obtain ⟨c, hc, hl⟩ := h k
    exact ⟨c, hg.pending _ _ hc, hl⟩
  have fr : ∀ {α : Type} {oa : SourceM C α},
      Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none) oa →
      Walk P seeds Q s (fun src st => BaseInv P seeds none none src st ∧ CF st) 0
        (fun _ src st => BaseInv P seeds none none src st ∧ CF st) oa :=
    fun h => Walk.frame CF hCF h
  have hnone : ∀ src st, BaseInv P seeds none none src st ∧ CF st →
      BaseInv P seeds none none src st ∧ ∀ k : Fin (2 ^ layerHeight),
        ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
          ∀ tree, (none : Option DeferredBottomTree) = some tree →
            c.low = .known (tree.commitment (bottomKey b k)) := fun _ _ h =>
    ⟨h.1, fun k => by obtain ⟨c, hc, -⟩ := h.2 k; exact ⟨c, hc, fun _ he => by cases he⟩⟩
  have seq0 : ∀ {α : Type} (oa : Fin chainCount → SourceM C α), (∀ l, Walk P seeds Q s
      (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none) (oa l)) →
      Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
        (OverPermutation.sequenceFin oa) := fun oa h =>
    Walk.conseq (Walk.sequenceFin _ oa _ h) (fun _ _ h => h) (fun _ _ _ h => h) (by simp)
  dsimp only
  refine Walk.conseq (c := 0 + (0 + (0 + (0 + 0)))) (Walk.bind (fr (Walk.conseq
    (walk_virtualTerms P seeds Q s _) (fun _ _ h => h) (fun _ _ _ h => h.1) le_rfl)) fun _ =>
    Walk.bind (fr (walk_hashProgram P seeds Q s _ (free_merkleNode P bottomLayer _ layerHeight
      b.val))) fun root =>
    Walk.bind (fr (walk_sourcePending_other P seeds Q s _ fun _ h => by cases h)) fun baseAnswer =>
    Walk.bind (fr (walk_hashProgram P seeds Q s _ (free_topGrind P b root _ _ _))) fun found => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  rcases found with _ | ⟨randomness, encoding⟩
  · exact Walk.pure _ hnone
  dsimp only
  refine Walk.conseq (c := 0 + (0 + (0 + 0))) (Walk.bind (fr (seq0 _ fun l =>
    walk_sourceTopValue P seeds Q s b l (encoding l))) fun values =>
    Walk.bind (fr (walk_hashProgram P seeds Q s _ (free_merklePath P topLayer top.chainEnd
      (topKey b)))) fun path =>
    Walk.bind (fr (walk_hashProgram P seeds Q s _ (free_topMessageDigest P b root randomness)))
      fun digest => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  cases Codeword.decode digest with
  | none => exact Walk.pure _ hnone
  | some checked =>
      dsimp only
      split
      · exact Walk.conseq (c := 0 + 0) (Walk.bind (Walk.modify (Post := fun _ src st =>
          BaseInv P seeds none none src st ∧ CF st) _ fun src st h =>
            ⟨BaseInv.of_source P seeds (src := src) h.1 rfl rfl rfl, h.2⟩) fun _ =>
          Walk.pure _ hnone) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
      · refine Walk.conseq (c := 0 + (0 + (0 + 0))) (Walk.bind (fr (seq0 _ fun l =>
          walk_sourceTopRecover P seeds Q s b l (encoding l) (values l))) fun ends =>
          Walk.bind (fr (walk_hashProgram P seeds Q s _ (free_leafHash P topLayer (topKey b) ends)))
            fun leaf =>
          Walk.bind (fr (walk_hashProgram P seeds Q s _ (free_treeFold P topLayer (topKey b) path
            layerHeight leaf))) fun topRoot => ?_) (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
        split
        · exact Walk.pure _ hnone
        · refine Walk.pure _ fun src st h => ⟨h.1, fun k => ?_⟩
          obtain ⟨c, hc, hl⟩ := h.2 k
          refine ⟨c, hc, fun tree he => ?_⟩
          cases he
          rw [hl]
          exact congrArg (fun n => DeferredDigest.known (ds.getD n 0)) (bottomKey_mod b k).symm

/-- A run over the ledger is a run over the capped hybrid without the ledger. -/
theorem runL_proj {α : Type} (oa : SourceM C α) (src : SourceState C) (st : LState C)
    (r : (α × SourceState C) × LState C) (hr : r ∈ support (runL P seeds Q s oa src st)) :
    (r.1, r.2.1) ∈ support (runSource P seeds Q s oa src st.1) := by
  obtain ⟨st1, g⟩ := st
  have h : Prod.map id Prod.fst <$> runL P seeds Q s oa src (st1, g) =
      runSource P seeds Q s oa src st1 := OracleComp.extendState_run_proj_eq _ _ _ _ _
  rw [← h, support_map]
  exact ⟨r, hr, rfl⟩

/-- `walk_sourceBottomTree`, which also states that a successful tree has `TopShape`. -/
theorem walk_sourceBottomTree_shape (top : TopTree) (b : XmssSecurity.TopIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0
      (fun r src st => (BaseInv P seeds none none src st ∧ ∀ k : Fin (2 ^ layerHeight),
        ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
          ∀ tree, r = some tree → c.low = .known (tree.commitment (bottomKey b k))) ∧
        ∀ tree, r = some tree → TopShape tree)
      (sourceBottomTree P seeds top b) := by
  intro src st hp r hr
  obtain ⟨hl, hg, hq⟩ := walk_sourceBottomTree P seeds Q s top b src st hp r hr
  refine ⟨hl, hg, hq, fun tree ht l k hk e he => ?_⟩
  have hno := sourceBottomTree_noBottomOpening P seeds Q s top b src st.1
    (CompilerReachable.pendingValid P seeds _ hp.reachable) (r.1, r.2.1)
    (runL_proj P seeds Q s _ src st r hr) tree ht l e
  exact hno (by rw [hk, he])

/-- The store of a tree keeps `BaseInv` when each key of the tree has a commitment answer, and a
successful tree holds its low half and has `TopShape`. -/
theorem baseInv_store {src : SourceState C} {st : LState C} (h : BaseInv P seeds none none src st)
    (b : XmssSecurity.TopIndex) (r : Option DeferredBottomTree)
    (hr : ∀ k : Fin (2 ^ layerHeight), ∃ c,
      st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
        ∀ tree, r = some tree → c.low = .known (tree.commitment (bottomKey b k)))
    (hshape : ∀ tree, r = some tree → TopShape tree) :
    BaseInv P seeds none none { src with trees := Function.update src.trees b (some r) } st := by
  refine ⟨h.reveal, h.bound, h.ready, h.commitTerms, fun b' hb k => ?_, h.revealedCached,
    h.releasedBound, h.corruptBound, h.reachable, h.dirtySecond, fun b' tree ht => ?_⟩
  swap
  · by_cases he : b' = b
    · subst he
      simp only [Function.update_self, Option.some.injEq] at ht
      exact hshape tree ht
    · simp only [Function.update_of_ne he] at ht
      exact h.storedTopShape b' tree ht
  by_cases he : b' = b
  · subst he
    obtain ⟨c, hc, hl⟩ := hr k
    refine ⟨c, hc, fun tree ht => hl tree ?_⟩
    simp only [Function.update_self, Option.some.injEq] at ht
    exact ht
  · simp only [Function.update_of_ne he] at hb ⊢
    exact h.treeCommit b' hb k

/-- `sourceBottomOnce` keeps `BaseInv` and makes no charged call. -/
theorem walk_sourceBottomOnce (top : TopTree) (b : XmssSecurity.TopIndex) :
    Walk P seeds Q s (BaseInv P seeds none none) 0 (fun _ => BaseInv P seeds none none)
      (sourceBottomOnce P seeds top b) := by
  unfold sourceBottomOnce
  refine Walk.conseq (c := 0 + 0) (Walk.bind Walk.get fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) le_rfl
  split
  · exact Walk.pure _ fun _ _ h => h.2
  · refine Walk.conseq (c := 0 + (0 + 0)) (Walk.bind (Walk.conseq (walk_sourceBottomTree_shape P
      seeds Q s top b) (fun _ _ h => h.2) (fun _ _ _ h => h) le_rfl) fun tree =>
      Walk.bind (Walk.modify (Post := fun _ => BaseInv P seeds none none) _ fun src st h =>
        baseInv_store P seeds h.1.1 b tree h.1.2 h.2) fun _ => Walk.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) le_rfl

end Units

/-- The setup makes no charged call. -/
theorem charges_setup (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True) 0 (liftBase (sourceTopTree x.1 x.2.1)) :=
  charges_of_walk (walk_sourceTopTree x.1 x.2.1 Q s)

end ThresholdLeanXmssSecurity.SigningOwnWalkBuild

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walkInv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walkInv_iff

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Grows.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Grows.refl

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Grows.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Grows.trans

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.conseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.conseq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.get

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.modify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.mapM_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.mapM_prefix

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.frame

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.liftM_mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.liftM_mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.mapM_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.mapM_rel

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.forall₂_finRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.forall₂_finRange

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.charges_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.charges_of_walk

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.deferredImpl_pending_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.deferredImpl_pending_keep

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_pending_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_pending_keep

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_bound_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.mem_runL_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.mem_runL_query

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.mem_runL_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.mem_runL_reveal

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_query

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_reveal

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.secondOpening_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.secondOpening_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_step

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.deferredImpl_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.deferredImpl_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.openingReady_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.openingReady_back

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.of_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.of_source

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_call

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_inspect_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_inspect_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_snapshot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_snapshot_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_pending_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_pending_some

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_record_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_record_some

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.ready_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.ready_plain

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.commit_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.commit_plain

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.not_charged_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.not_charged_of_ne

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_plain

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_merklePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_merklePath

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_leafHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_leafHash

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_treeFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_treeFold

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_topMessageDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.free_topMessageDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.plain_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.plain_run

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_inspect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_inspect

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_snapshot

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sample

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_pad

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_uniform

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_plant_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_plant_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_plant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_plant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_pendingCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_pendingCall

/--
info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.commitReady_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.commitReady_grows

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourcePending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourcePending

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_freeHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_freeHash

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_hashProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_hashProgram

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_virtual_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.compilerImpl_virtual_mem

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_virtualCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_virtualCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceVirtual_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceVirtual_other

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopEnd

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopTree

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_fillTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_fillTerm

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_completePrf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_completePrf

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_reveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_reveal

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_revealed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceReveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceReveal

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.weaken_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.weaken_ready

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.close_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.close_ready

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.close_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.BaseInv.close_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.next_ne_opening' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.next_ne_opening

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceReveal_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceReveal_known

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.assume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.Walk.assume

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourcePlant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourcePlant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceReleaseOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceReleaseOpening

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_virtualCall_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_virtualCall_bottom

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceVirtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceVirtual

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_virtualTerms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_virtualTerms

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceCommitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceCommitment

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourcePending_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourcePending_other

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomRow

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopValue

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceTopRecover

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.bottomKey_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.bottomKey_mod

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_commitments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_commitments

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomTree

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.baseInv_store

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomOnce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomOnce

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.charges_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.charges_setup

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.runL_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.runL_proj

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomTree_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnWalkBuild.walk_sourceBottomTree_shape
