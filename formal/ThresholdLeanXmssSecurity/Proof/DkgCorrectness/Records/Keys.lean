import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Records.Streams
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningDigests
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Setup
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.BatchRecords
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cover.Cells
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Abort

/-!
# The echo round of a PRSS setup on the recorded run

`reachH_prssSetup` follows a PRSS setup and its continuation to the exchange of the echo, two rounds
after its start, with the answers of the shared-key hashes in the history. Each later result of the
continuation needs the test of the echo. `echo_termsAgree` gives, on a ghost phase, one key of each
term to two honest holders that passed the echo, or an echo collision.

* `ghost_termKeys` is this for the records of one ceremony.
* `cut_termKeys` is this for the stops of a prefix of one ceremony, through the ghost form `cutGhost`
  of its programs.
* `cut_pairKeys` gives one key of each honest pair at the stops, from the hidden pair names of
  `Draws.setupRounds_oneKey`.
* `ceremonyKeysAgree` is the leaf `CeremonyKeysAgree`.

`ghostOnPath` is `GhostOnPath` from `executePhaseR_onPathRH`. So `ceremonyMonitor` and `ceremonyBatch`
hold. `recordedTermKeys` is `RecordedTermKeys` from the echo of the PRSS setup (`ghost_termKeys`), and
with `ceremonyStarted` it gives `ceremonyOutputsAgree`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace EchoRound

open LiveRounds CachedOpening RecordedOpening OpeningDigests

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Walk

variable {C : Committee} {E : Type} {γ : Type} {P : γ → Prop}
  {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}

/-- A timed step of a program and then a continuation that reaches its wait of depth `n` from each
result of the support reach that wait at depth `m + n`. -/
theorem reachH_partyBind {α β : Type} {m n : ℕ} {p : PartyM C E RealSpec α} {q : α → PartyM C E RealSpec β}
    {g : Option β → OracleComp (PartySpec C E RealSpec) γ} (hp : Timed m p.run) (hnone : ∃ y, g none = pure y ∧ P y)
    (hq : ∀ hist a, some a ∈ support p.run → ReachH P Q n hist ((q a).run >>= g)) (hist : List (Query C × HashOutput)) :
    ReachH P Q (m + n) hist ((p >>= q).run >>= g) := by
  rw [OptionT.run_bind, Option.elimM, bind_assoc]
  refine timedLog_reachH_bind (DigestRound.timedLog_of_timed hp (fun o => o ∈ support p.run ∧ o.isSome)
    fun o ho hs => ⟨ho, hs⟩) (fun x hx => ?_) (fun hist x hx => ?_) hist
  · subst hx
    obtain ⟨y, hy, hPy⟩ := hnone
    exact ⟨y, by simp [hy], hPy⟩
  · rcases x with _ | a
    · cases hx.2
    · simpa only [Option.elim] using hq hist a hx.1

theorem timed_localStep {α : Type} (oa : OracleComp (LocalSpec C) α) : Timed 0 (localStep (E := E) (G := RealSpec) oa).run := by
  rw [← bind_pure (localStep oa)]
  exact Timed.localStep_bind 0 _ _ fun a => timed_pure a

/-- The hashes at `q a` for each `a` of a list put their answers into the history. -/
theorem reachH_hashList_bind {α : Type} (n : ℕ) (q : α → Query C) :
    ∀ (l : List α) (hist : List (Query C × HashOutput)) (k : List HashOutput → OracleComp (PartySpec C E RealSpec) γ),
      (∀ ds hist', hist ⊆ hist' → ds.length = l.length → (∀ m (hm : m < l.length), (q l[m], ds.getD m 0) ∈ hist') →
        ReachH P Q n hist' (k ds)) →
      ReachH P Q n hist (liftComp (liftComp (l.mapM fun a => hashQuery (q a)) (LocalSpec C)) (PartySpec C E RealSpec) >>= k)
  | [], hist, k, hk => by
    simpa using hk [] hist (List.Subset.refl _) rfl fun m hm => absurd hm (Nat.not_lt_zero m)
  | a :: l, hist, k, hk => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
    rw [liftComp_hashQuery]
    refine ReachH.queryLocal n hist _ _ fun r => ?_
    refine reachH_hashList_bind n q l _ (fun ds => k (r :: ds)) fun ds hist' hsub hlen hcells =>
      hk _ hist' (fun x hx => hsub (List.mem_append_right _ hx)) (by simp [hlen]) fun m hm => ?_
    rcases m with _ | m
    · exact hsub (by simp [hashLog])
    · exact hcells m (by simpa using hm)

end Walk


/-! ## The echo of a PRSS setup -/

section Echo

variable {C : Committee} {E : Type} {γ : Type}

/-- The echo mail of operator `i` passes its test. Each other operator sent the shared-key hash of
`i` for it. -/
def EchoPass (i : C.Party) (shared : List HashOutput) (inbox : Mail C E) : Prop :=
  ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [shared.getD j.val 0]

/-- The exchange of the echo of a PRSS setup at operator `i`, before the continuation `g` of the
setup. The outbox holds the shared-key hashes of the derived keys, whose answers are in `hist`. Each
later outcome is an outcome of `g` at an abort, or of `g` at the derived keys after the test of the
echo. -/
def EchoWait (i : C.Party) (g : Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) γ)
    (hist : List (Query C × HashOutput)) (out : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) γ) : Prop :=
  ∃ (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput),
    out = (fun j => if j = i then none else some (.hashes [shared.getD j.val 0])) ∧
    (∀ j : C.Party, ((.sharedKeys .prss ((sharedTerms i j).map keys.2.1) : Query C), shared.getD j.val 0) ∈ hist) ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), x ∈ support (g none) ∨
      (EchoPass i shared inbox ∧ x ∈ support (g (some ⟨keys.2.1, keys.2.2⟩)))

/-- A PRSS setup of operator `i` and its continuation `g` reach the exchange of the echo two rounds
after the start, or end with the abort leaf of `g`. -/
theorem reachH_prssSetup {P : γ → Prop} (i : C.Party) (g : Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) γ)
    (hnone : ∃ y, g none = pure y ∧ P y) (hist : List (Query C × HashOutput)) :
    ReachH P (EchoWait i g) 2 hist ((prssSetup (E := E) (G := RealSpec) i).run >>= g) := by
  unfold prssSetup prssSetupWith commitRevealEcho
  simp only [bind_assoc]
  rw [show (2 : ℕ) = 0 + (0 + (1 + (1 + (0 + (0 + (0 + 0)))))) from rfl]
  refine reachH_partyBind (timed_localStep _) hnone (fun hist own _ => ?_) hist
  refine reachH_partyBind (timed_oracleStep _) hnone (fun hist commitments _ => ?_) hist
  refine reachH_partyBind (timed_exchange _) hnone (fun hist committed _ => ?_) hist
  refine reachH_partyBind (timed_exchange _) hnone (fun hist revealed _ => ?_) hist
  refine reachH_partyBind (timed_oracleStep _) hnone (fun hist opens _ => ?_) hist
  refine reachH_partyBind (timed_require _) hnone (fun hist u _ => ?_) hist
  refine reachH_partyBind (timed_oracleStep _) hnone (fun hist keys _ => ?_) hist
  simp only [oracleStep, localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_assoc, pure_bind,
    Option.elim]
  refine reachH_hashList_bind 0 (fun j => Query.sharedKeys .prss ((sharedTerms i j).map keys.2.1)) C.parties hist _
    fun shared hist' hsub hlen hcells => ?_
  simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
  refine ReachH.here hist' _ _ ⟨keys, shared, by funext j; simp, fun j => ?_, fun inbox x hx => ?_⟩
  · have h := hcells j.val (by simp [SetupAgree.parties_length])
    simp only [SetupAgree.parties_getElem] at h
    exact h
  · change x ∈ support (OptionT.run (if (C.parties.any fun j => Msg.isAbort (inbox j)) = true then failure
      else pure inbox) >>= _) at hx
    by_cases hab : (C.parties.any fun j => Msg.isAbort (inbox j)) = true
    · left
      simp only [hab, ↓reduceIte, OptionT.run_failure, pure_bind] at hx
      exact hx
    simp only [hab, Bool.false_eq_true, ↓reduceIte, OptionT.run_pure, pure_bind] at hx
    by_cases hreq : ∀ (j : C.Party), j ≠ i →
        Msg.hashesOf (inbox j) = (if Phase.prss = Phase.seedGen then [keys.1] else []) ++ [shared.getD (↑j) 0]
    · unfold require at hx
      rw [ite_eq_left hreq] at hx
      simp only [OptionT.run_pure, pure_bind] at hx
      exact Or.inr ⟨fun j hj => by simpa using hreq j hj, hx⟩
    · left
      unfold require at hx
      rw [ite_eq_right hreq] at hx
      simp only [OptionT.run_failure, pure_bind] at hx
      exact hx

end Echo


/-! ## The agreement of the shared term keys -/

section Agree

variable {C : Committee} {E : Type} {α ρ : Type} (prims : Primitives) (Dw D' : C.Coalition)

/-- Two equal shared-key cells of two lists are equal lists, or `EchoDomain` has a collision. -/
theorem sharedKeys_eq {cache : HashCache C} {l l' : List HashOutput} {d : HashOutput}
    (h : cache (.sharedKeys .prss l) = some d) (h' : cache (.sharedKeys .prss l') = some d) :
    l = l' ∨ DomainCollision EchoDomain cache := by
  by_cases hl : l = l'
  · exact Or.inl hl
  · refine Or.inr ⟨.sharedKeys .prss l, .sharedKeys .prss l', d, d, fun e => hl (Query.sharedKeys.inj e).2, ?_, ?_,
      HEq.rfl⟩
    · simp [splitRegionCache, EchoDomain, h]
    · simp [splitRegionCache, EchoDomain, h']

theorem sharedTerms_comm (i j : C.Party) : sharedTerms i j = sharedTerms j i := by
  unfold sharedTerms
  exact List.filter_congr fun T _ => by simp [and_comm]

/-- The shared term keys after the echo of a PRSS setup in a ghost phase. Take honest programs that
reach the echo of a setup with the continuations `g`. Two honest operators whose records have the
property `Good`, which no abort leaf has, end in their continuations at some derived keys. On each
term that both hold, these keys agree, or `EchoDomain` has a collision in the end hash cache. -/
theorem echo_termsAgree {Ia : Type} (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ) (fuel : ℕ) (st : A.State)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (g : C.Party → Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (hreach : ∀ l, l ∉ D'.1 → ReachH (fun x => x ∈ support (g l none)) (EchoWait l (g l)) 2 [] (program l))
    (Good : C.Party → ρ → Prop) (hblank : ∀ l, ¬ Good l blank)
    (hgood : ∀ l (x : Option α × ρ), Good l x.2 → x ∉ support (g l none))
    (s : HashCache C × HiddenCache C)
    (z : (A.State × (C.Party → RStep C E RealSpec α ρ)) × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims Dw)
      (executePhaseR worldRoles D' A noFunctionality blank fuel st program)).run s))
    (i j : C.Party) (hi : i ∉ D'.1) (hj : j ∉ D'.1) (hij : i ≠ j) (hgi : Good i ((z.1.2 i).record blank))
    (hgj : Good j ((z.1.2 j).record blank)) :
    ∃ pi pj : PrssKeys C, (∃ out, (out, (z.1.2 i).record blank) ∈ support (g i (some pi))) ∧
      (∃ out, (out, (z.1.2 j).record blank) ∈ support (g j (some pj))) ∧
      ((∀ T, i ∈ C.holders T → j ∈ C.holders T → pi.term T = pj.term T) ∨ DomainCollision EchoDomain z.2.1) := by
  rcases CachedOpening.executePhaseR_reachH prims Dw D' A blank (fun l x => x ∈ support (g l none))
    (fun l => EchoWait l (g l)) 2 fuel st program hreach s z hz with hstop | ⟨steps₀, sent, cache, hle, hsteps, hrest⟩
  · exfalso
    rcases hstop i hi with h | ⟨out, hout⟩
    · exact hblank i (h ▸ hgi)
    · exact hgood i _ hgi hout
  have hwait : ∀ l, l ∉ D'.1 → Good l ((z.1.2 l).record blank) → ∃ outbox resume, steps₀ l = .wait outbox resume ∧
      ∃ hist, Cached hist cache ∧ EchoWait l (g l) hist outbox resume ∧
        ∃ out, (out, (z.1.2 l).record blank) ∈ support (resume (LiveRounds.roundInbox D' steps₀ sent l)) := by
    intro l hl hgl
    obtain ⟨out, hout⟩ : ∃ out, (out, (z.1.2 l).record blank) ∈
        support (nextR blank (steps₀ l) (LiveRounds.roundInbox D' steps₀ sent l)) := by
      rcases hrest l hl with h | h
      · exact absurd (h ▸ hgl) (hblank l)
      · exact h
    have hsl := hsteps l hl
    rcases hs : steps₀ l with ⟨out', r'⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hsl hout
    · exfalso
      simp only [nextR, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
      rw [hout.2] at hgl
      exact hgood l _ hgl hsl
    · obtain ⟨hist, hc, hq⟩ := hsl
      exact ⟨outbox, resume, rfl, hist, hc, hq, out, hout⟩
    · exact input.elim
  obtain ⟨oi, ri, hsi, histi, hci, ⟨keysi, sharedi, houti, hcellsi, hresi⟩, outi, hxi⟩ := hwait i hi hgi
  obtain ⟨oj, rj, hsj, histj, hcj, ⟨keysj, sharedj, houtj, hcellsj, hresj⟩, outj, hxj⟩ := hwait j hj hgj
  rcases hresi _ _ hxi with hn | ⟨hpassi, hgi'⟩
  · exact absurd hn (hgood i _ hgi)
  rcases hresj _ _ hxj with hn | ⟨-, hgj'⟩
  · exact absurd hn (hgood j _ hgj)
  refine ⟨⟨keysi.2.1, keysi.2.2⟩, ⟨keysj.2.1, keysj.2.2⟩, ⟨_, hgi'⟩, ⟨_, hgj'⟩, ?_⟩
  have hdeliv : Msg.hashesOf (LiveRounds.roundInbox D' steps₀ sent i j) = [sharedj.getD i.val 0] := by
    simp [LiveRounds.roundInbox, hj, hsj, RStep.delivered, houtj, hij]
    rfl
  have hsame : sharedj.getD i.val 0 = sharedi.getD j.val 0 := by
    have := hpassi j (Ne.symm hij)
    rw [hdeliv] at this
    exact List.head_eq_of_cons_eq this
  have c1 : z.2.1 (.sharedKeys .prss ((sharedTerms i j).map keysi.2.1)) = some (sharedi.getD j.val 0) :=
    hle (hci _ (hcellsi j) (by rintro ⟨_, he, -⟩; cases he))
  have c2 : z.2.1 (.sharedKeys .prss ((sharedTerms j i).map keysj.2.1)) = some (sharedi.getD j.val 0) := by
    rw [← hsame]
    exact hle (hcj _ (hcellsj i) (by rintro ⟨_, he, -⟩; cases he))
  rcases sharedKeys_eq c1 c2 with heq | hcoll
  · left
    intro T hiT hjT
    have hT : T ∈ sharedTerms i j := by simp [sharedTerms, Committee.terms, hiT, hjT]
    rw [sharedTerms_comm j i] at heq
    exact List.map_inj_left.1 heq T hT
  · exact Or.inr hcoll

end Agree


/-! ## The PRSS keys in the records of one ceremony -/

section Ceremony

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The rest of `recCeremony` at operator `l` after its PRSS setup. A dead operator aborts. -/
def recRest (l : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  match c.keys l with
  | some keys => fun o => o.elim (pure (none, [])) fun prss =>
      ((batched settings.batchSize (recBatch K circuits settings ⟨l, keys, prss⟩ keys.parameter) c.jobs).run
        c.counters).run.run >>= recCont fun p => p.1.elim failure fun outputs => pure (outputs, p.2)
  | none => fun _ => pure (none, [])

omit [Fintype E] [DecidableEq E] in
theorem recCeremony_split (l : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hk : c.keys l = some keys) :
    (recCeremony K circuits settings l c).run.run =
      (prssSetup (E := E) (G := RealSpec) l).run >>= recRest K circuits settings l c := by
  unfold recCeremony recRest
  simp only [hk]
  rw [run_recBind]
  simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
  rw [run_recLift_bind, OptionT.run_bind, Option.elimM, bind_assoc, bind_assoc]
  refine bind_congr fun o => ?_
  rcases o with _ | prss
  · simp [recCont]
  · simp only [Option.elim, OptionT.run_pure, pure_bind]

omit [Fintype E] [DecidableEq E] in
/-- The starts that the batches of a ceremony record have the context of the batches. -/
theorem batched_ctx (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    ∀ st z, z ∈ support ((batched settings.batchSize (recBatch K circuits settings ctx parameter) jobs).run st).run.run →
      ∀ b ∈ startsOf z.2, b.ctx = ctx := by
  refine closed_batched (m := StateT (ℕ × ℕ) (RecM C E))
    (fun x => ∀ st z, z ∈ support ((x.run st).run.run) → ∀ b ∈ startsOf z.2, b.ctx = ctx)
    (fun a st z hz => ?_) (fun x f hx hf st z hz => ?_) _ _ (fun js => ?_) jobs
  · simp at hz
    subst hz
    simp [startsOf]
  · rw [StateT.run_bind] at hz
    obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨a, -, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
    · exact hx st z₁ h₁
    · intro b hb
      rw [RecordedOpening.startsOf_append, List.mem_append] at hb
      rcases hb with hb | hb
      · exact hx st z₁ h₁ b hb
      · exact hf a.1 a.2 z₂ h₂ b hb
  · rintro ⟨L, k⟩ z hz b hb
    rcases BatchCounters.recBatch_counters K circuits settings ctx parameter js L k z hz with ⟨hs, -⟩ | ⟨b', hs, hb', -⟩
    · rw [hs] at hb
      cases hb
    · rw [hs, List.mem_singleton] at hb
      subst hb
      exact hb'.2.2.2.2.1

omit [Fintype E] [DecidableEq E] in
/-- Each start that the rest of a ceremony after its setup records has the PRSS keys of the setup. -/
theorem recRest_prss (l : C.Party) {σ : Type} (c : CeremonyStart C σ) (p : PrssKeys C)
    (x : Option CeremonyResult × Record C E) (hx : x ∈ support (recRest K circuits settings l c (some p))) :
    ∀ b ∈ startsOf x.2, b.ctx.prss = p := by
  unfold recRest at hx
  rcases hk : c.keys l with _ | keys <;> simp only [hk] at hx
  · simp at hx
    subst hx
    simp [startsOf]
  · simp only [Option.elim] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨y, hy, hx⟩ := hx
    have hctx := batched_ctx K circuits settings _ _ _ _ y hy
    rcases y with ⟨_ | a, w⟩
    · simp only [recCont, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      intro b hb
      rw [hctx b hb]
    · simp only [recCont, support_map, Set.mem_image] at hx
      obtain ⟨y', hy', rfl⟩ := hx
      have hnil : y'.2 = [] := by
        rcases a with ⟨_ | outputs, st⟩
        · simp at hy'
          rw [hy']
        · simp at hy'
          rw [hy']
      intro b hb
      rw [hnil, List.append_nil] at hb
      rw [hctx b hb]

omit [Fintype E] [DecidableEq E] in
/-- The term keys at the starts of the honest records of one ceremony. Two honest operators recorded
starts with the same PRSS key of each term that both hold, or `EchoDomain` has a collision in the end
hash cache. -/
theorem ghost_termKeys (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (T : C.Term)
    (j j' : C.Party) (b b' : BatchStart C) (hj : j ∉ D.1) (hj' : j' ∉ D.1) (hjT : j ∈ C.holders T)
    (hj'T : j' ∈ C.holders T) (hb : b ∈ startsOf (ceremonyRecord ω.1.2 j))
    (hb' : b' ∈ startsOf (ceremonyRecord ω.1.2 j')) (hjj : j ≠ j') :
    b.ctx.prss.term T = b'.ctx.prss.term T ∨ DomainCollision EchoDomain ω.2.1 := by
  unfold ghostCeremony at hω
  have hrest_none : ∀ l, recRest K circuits settings l c none = pure (none, []) := fun l => by
    unfold recRest
    rcases c.keys l <;> rfl
  have hreach : ∀ l, l ∉ D.1 → ReachH (fun x => x ∈ support (recRest K circuits settings l c none))
      (EchoWait l (recRest K circuits settings l c)) 2 [] (recCeremony K circuits settings l c).run.run := by
    intro l _
    rcases hk : c.keys l with _ | keys
    · have : (recCeremony K circuits settings l c).run.run = pure (none, []) := by
        unfold recCeremony
        simp only [hk]
        rfl
      rw [this]
      exact ReachH.early 2 [] _ (by rw [hrest_none]; simp)
    · rw [recCeremony_split K circuits settings l c keys hk]
      exact reachH_prssSetup l _ ⟨(none, []), hrest_none l, by rw [hrest_none]; simp⟩ []
  obtain ⟨p, p', ⟨o, ho⟩, ⟨o', ho'⟩, h⟩ := echo_termsAgree prims D D net ([] : Record C E) rounds c.adversary
    (fun i => (recCeremony K circuits settings i c).run.run) (recRest K circuits settings · c) hreach
    (fun _ r => startsOf r ≠ []) (fun _ => by simp [startsOf])
    (fun l x hx hmem => by rw [hrest_none] at hmem; simp at hmem; rw [hmem] at hx; simp [startsOf] at hx)
    world ω hω j j' hj hj' hjj (List.ne_nil_of_mem hb) (List.ne_nil_of_mem hb')
  rw [recRest_prss K circuits settings j c p _ ho b hb, recRest_prss K circuits settings j' c p' _ ho' b' hb']
  exact h.imp (fun h => h T hjT hj'T) id

end Ceremony


/-! ## The PRSS keys at the cut of one ceremony -/

section Cut

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- The program that stops at check `k` is the PRSS setup and then the batches. -/
theorem cutCeremony_split (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hk : c.keys i = some keys) :
    cutCeremony K circuits settings k i c = prssSetup i >>= fun prss =>
      ((SetupCut.cutBatches K circuits settings (c.counters.2 + k) i keys prss c.jobs).run c.counters).run := by
  unfold cutCeremony
  simp only [hk]
  rw [SetupCut.cutRun_eq]
  simp only [StateT.run_bind, CutM.lift_run, StateT.run_lift, Paused.run_bind, Paused.lift, map_bind, map_pure,
    pure_bind, bind_assoc]

/-- The ghost form of the program that stops at check `k`, with its outcome as its record. -/
def cutGhost (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    OracleComp (PartySpec C E RealSpec) (Option (CutOf C E RunResult) × Option (CutOf C E RunResult)) :=
  (fun o => (o, o)) <$> (cutCeremony K circuits settings k i c).run

/-- The rest of `cutGhost` after its PRSS setup. A dead operator aborts. -/
def cutGhostRest (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Option (PrssKeys C) →
      OracleComp (PartySpec C E RealSpec) (Option (CutOf C E RunResult) × Option (CutOf C E RunResult)) :=
  match c.keys i with
  | some keys => fun o => (fun o' => (o', o')) <$> o.elim (pure none) fun prss =>
      ((SetupCut.cutBatches K circuits settings (c.counters.2 + k) i keys prss c.jobs).run c.counters).run.run
  | none => fun _ => pure (none, none)

omit [Fintype E] [DecidableEq E] in
theorem cutGhostRest_none (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    cutGhostRest K circuits settings k i c none = pure (none, none) := by
  unfold cutGhostRest
  rcases c.keys i <;> simp

/-- A stop of the rest of `cutGhost` after a setup with the keys `prss` has these PRSS keys. -/
theorem cutGhostRest_stop (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (prss : PrssKeys C)
    (x : Option (CutOf C E RunResult) × Option (CutOf C E RunResult))
    (hx : x ∈ support (cutGhostRest K circuits settings k i c (some prss))) (point : CheckPoint C)
    (rest : RunState C → PartyM C E RealSpec RunResult) (hr : x.2 = some (.inr (point, rest))) :
    point.ctx.prss = prss := by
  unfold cutGhostRest at hx
  rcases hk : c.keys i with _ | keys <;> simp only [hk] at hx
  · simp at hx
    rw [hx] at hr
    cases hr
  · simp only [Option.elim, support_map, Set.mem_image] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact ((SetupCut.cutWalk_cutBatches K circuits settings _ i keys prss c.jobs) c.counters o ho).2 point rest hr

omit [Fintype E] [DecidableEq E] in
theorem reachH_cutGhost (k : ℕ) (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    ReachH (fun x => x ∈ support (cutGhostRest K circuits settings k i c none))
      (EchoWait i (cutGhostRest K circuits settings k i c)) 2 [] (cutGhost K circuits settings k i c) := by
  rcases hk : c.keys i with _ | keys
  · have : cutGhost K circuits settings k i c = pure (none, none) := by
      unfold cutGhost cutCeremony
      simp only [hk]
      rfl
    rw [this]
    exact ReachH.early 2 [] _ (by rw [cutGhostRest_none]; simp)
  · have : cutGhost K circuits settings k i c = (prssSetup i).run >>= cutGhostRest K circuits settings k i c := by
      unfold cutGhost cutGhostRest
      rw [cutCeremony_split K circuits settings k i c keys hk]
      simp only [hk, OptionT.run_bind, Option.elimM, map_bind]
    rw [this]
    exact reachH_prssSetup i _ ⟨(none, none), cutGhostRest_none K circuits settings k i c,
      by rw [cutGhostRest_none]; simp⟩ []

/-- The term keys at the stops of a prefix of one ceremony. Two honest operators that stop at the
check hold the same PRSS key of each term that both hold, or `EchoDomain` has a collision in the end
hash cache. -/
theorem cut_termKeys (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds k : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (z : (net.State × (C.Party → Option (CutOf C E RunResult))) × StreamState C)
    (hz : z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world)) (i j : C.Party)
    (hi : i ∉ D.1) (hj : j ∉ D.1) (hij : i ≠ j) (pi pj : CheckPoint C)
    (ri rj : RunState C → PartyM C E RealSpec RunResult)
    (hzi : z.1.2 i = some (.inr (pi, ri))) (hzj : z.1.2 j = some (.inr (pj, rj))) :
    (∀ T, i ∈ C.holders T → j ∈ C.holders T → pi.ctx.prss.term T = pj.ctx.prss.term T) ∨
      DomainCollision EchoDomain z.2.1 := by
  have hdrop : (fun l => dropRecord (cutGhost K circuits settings k l c)) =
      fun l => cutCeremony K circuits settings k l c := by
    funext l
    refine OptionT.ext ?_
    simp [dropRecord, cutGhost, Functor.map_map]
  unfold ceremonyPrefix at hz
  rw [← hdrop, executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
    (none : Option (CutOf C E RunResult)), simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  have hrec : ∀ l, l ∉ D.1 → ∀ point rest, (z'.1.2 l).output = some (.inr (point, rest)) →
      (z'.1.2 l).record none = some (.inr (point, rest)) := by
    intro l hl point rest ho
    have hpath := BatchCounters.executePhaseR_onPathR prims D D net (none : Option (CutOf C E RunResult)) rounds
      c.adversary (fun l => cutGhost K circuits settings k l c) world z' hz' l hl
    rcases hs : z'.1.2 l with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at ho hpath
    · have hmem := hpath.done
      simp only [cutGhost, support_map, Set.mem_image, Prod.mk.injEq] at hmem
      obtain ⟨o, -, h1, h2⟩ := hmem
      simp only [RStep.output] at ho
      simp only [RStep.record, ← h2, h1, ho]
    · cases ho
    · cases ho
  have hgi := hrec i hi pi ri hzi
  have hgj := hrec j hj pj rj hzj
  obtain ⟨p, p', ⟨o, ho⟩, ⟨o', ho'⟩, h⟩ := echo_termsAgree prims D D net (none : Option (CutOf C E RunResult)) rounds
    c.adversary (fun l => cutGhost K circuits settings k l c) (cutGhostRest K circuits settings k · c)
    (fun l _ => reachH_cutGhost K circuits settings k l c)
    (fun _ r => ∃ point rest, r = some (.inr (point, rest))) (fun _ ⟨_, _, h⟩ => by cases h)
    (fun l x ⟨point, rest, hx⟩ hmem => by
      rw [cutGhostRest_none] at hmem
      simp at hmem
      rw [hmem] at hx
      cases hx)
    world z' hz' i j hi hj hij ⟨pi, ri, hgi⟩ ⟨pj, rj, hgj⟩
  rw [cutGhostRest_stop K circuits settings k i c p _ ho pi ri hgi,
    cutGhostRest_stop K circuits settings k j c p' _ ho' pj rj hgj]
  exact h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem pairOf_comm (i j : C.Party) (h : i ≠ j) : C.pairOf i j h = C.pairOf j i (Ne.symm h) := by
  unfold Committee.pairOf
  split_ifs with h1 h2 h2
  · exact absurd (h1.trans h2) (lt_irrefl i)
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) h

/-- The rest of the program that stops at check `k` after its PRSS setup. -/
def cutRest (k : ℕ) (i : C.Party) (keys : Keys C) {σ : Type} (c : CeremonyStart C σ) (prss : PrssKeys C) :
    PartyM C E RealSpec (CutOf C E RunResult) :=
  ((SetupCut.cutBatches K circuits settings (c.counters.2 + k) i keys prss c.jobs).run c.counters).run

/-- The pair keys at the stops of a prefix of one ceremony. Two honest operators that stop at the
check hold one key of their pair. The pair is a hidden name, and after the reveal round of the setup
both hold the cached answer of one derive input. -/
theorem cut_pairKeys (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds k : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (z : (net.State × (C.Party → Option (CutOf C E RunResult))) × StreamState C)
    (hz : z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world)) (i j : C.Party)
    (hi : i ∉ D.1) (hj : j ∉ D.1) (hij : i ≠ j) (pi pj : CheckPoint C)
    (ri rj : RunState C → PartyM C E RealSpec RunResult)
    (hzi : z.1.2 i = some (.inr (pi, ri))) (hzj : z.1.2 j = some (.inr (pj, rj))) :
    pi.ctx.prss.pair j = pj.ctx.prss.pair i := by
  let G : C.Party → (PrssKeys C → PartyM C E RealSpec (CutOf C E RunResult)) → Prop := fun l R =>
    ∀ prss, ∀ o ∈ support (R prss).run, ∀ point rest, o = some (.inr (point, rest)) → point.ctx.prss = prss
  unfold ceremonyPrefix executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  have h0 : ∀ l, l ∉ D.1 → a.1 l = .done none ∨ ∃ own commitments R,
      a.1 l = Draws.commitStepK l own commitments R ∧ G l R := by
    intro l hl
    have hmem := mem_support_sequenceFin_oc _ _ (CachedOpening.fst_mem_support prims D _ world a ha) l
    simp only [hl, ↓reduceIte, worldRoles] at hmem
    have hadv := support_free_subset _ hmem
    rcases hk : c.keys l with _ | keys
    · have : cutCeremony K circuits settings k l c = failure := by
        unfold cutCeremony
        simp only [hk]
      rw [this, advance_run_failure] at hadv
      simp at hadv
      exact Or.inl hadv
    · rw [cutCeremony_split K circuits settings k l c keys hk, Draws.advance_prssSetup_bind] at hadv
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hadv
      obtain ⟨own, -, commitments, -, he⟩ := hadv
      refine Or.inr ⟨own, commitments, _, he, fun prss o ho point rest hr => ?_⟩
      exact ((SetupCut.cutWalk_cutBatches K circuits settings _ l keys prss c.jobs) c.counters o ho).2 point rest hr
  have hout0 : ∀ l, l ∉ D.1 → ∀ step : Step C E RealSpec (CutOf C E RunResult),
      (step = .done none ∨ ∃ outbox resume, step = .wait outbox resume) → step.output = none := by
    rintro l - step (rfl | ⟨outbox, resume, rfl⟩) <;> rfl
  have hshape0 : a.1 i = .done none ∨ ∃ outbox resume, a.1 i = .wait outbox resume := by
    rcases h0 i hi with h | ⟨own, commitments, R, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, _, h⟩
  have h1 := fun q1 hq1 => Draws.commitRound_shape D prims G net c.adversary a.1 h0 a.2 q1 hq1
  rcases rounds with _ | _ | rounds
  · simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [hout0 i hi _ hshape0] at hzi
  · rw [executeRounds] at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [hout0 i hi _ hshape0] at hzi
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨q1, hq1, hz⟩ := hz
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    have hs1 : q1.1.2.1 i = .done none ∨ ∃ outbox resume, q1.1.2.1 i = .wait outbox resume := by
      rcases h1 q1 hq1 i hi with h | ⟨own, committed, R, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, _, h⟩
    simp [hout0 i hi _ hs1] at hzi
  rw [executeRounds] at hz
  split_ifs at hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [hout0 i hi _ hshape0] at hzi
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨q1, hq1, hz⟩ := hz
  have hs1 : q1.1.2.1 i = .done none ∨ ∃ outbox resume, q1.1.2.1 i = .wait outbox resume := by
    rcases h1 q1 hq1 i hi with h | ⟨own, committed, R, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, _, h⟩
  rw [executeRounds] at hz
  split_ifs at hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [hout0 i hi _ hs1] at hzi
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨q2, hq2, hz⟩ := hz
  obtain ⟨input, hkey⟩ := Draws.setupRounds_oneKey D prims G net c.adversary a.1 h0 a.2 q1 hq1 q2 hq2
  have hz1 := CachedOpening.fst_mem_support prims D _ q2.2 z hz
  have hreach := SetupCut.executeRounds_reach D net (fun l => stepProgram (q2.1.2.1 l)) rounds q2.1.1 q2.1.2.1
    (fun l _ a ha => ha) z.1 hz1
  have hpoint : ∀ l, l ∉ D.1 → ∀ point rest, z.1.2 l = some (.inr (point, rest)) →
      ∃ keys, point.ctx.prss = SetupAgree.prssOf keys ∧
        ∀ N key, Hidden D N → NameKey l (SetupAgree.prssOf keys) N key → q2.2.1 (input N) = some key := by
    intro l hl point rest hzl
    have hmem := hreach l hl _ hzl
    rcases hkey l hl with hd | ⟨keys, shared, R, he, hG, hk⟩
    · rw [hd] at hmem
      simp [stepProgram] at hmem
    refine ⟨keys, ?_, hk⟩
    rw [he] at hmem
    simp only [stepProgram, Draws.echoStepK, mem_support_bind_iff] at hmem
    obtain ⟨inbox, -, hmem⟩ := hmem
    unfold exchangeResume at hmem
    split_ifs at hmem
    · simp at hmem
    rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at hmem
    obtain ⟨o, -, hmem⟩ := hmem
    rcases o with _ | u
    · simp at hmem
    · exact hG _ _ hmem point rest rfl
  obtain ⟨ki, hpi, hki⟩ := hpoint i hi pi ri hzi
  obtain ⟨kj, hpj, hkj⟩ := hpoint j hj pj rj hzj
  have hN : Hidden D (.pair (C.pairOf i j hij)) := by
    rcases Draws.pairOf_ends i j hij with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · show (C.pairOf i j hij).1.1 ∉ D.1 ∧ (C.pairOf i j hij).1.2 ∉ D.1
      rw [e1, e2]
      exact ⟨hi, hj⟩
    · show (C.pairOf i j hij).1.1 ∉ D.1 ∧ (C.pairOf i j hij).1.2 ∉ D.1
      rw [e1, e2]
      exact ⟨hj, hi⟩
  have c1 := hki _ (ki.2.2 j) hN (Or.inr ⟨j, Ne.symm hij, rfl, rfl⟩)
  have c2 := hkj _ (kj.2.2 i) hN (Or.inr ⟨i, hij, by rw [pairOf_comm i j hij], rfl⟩)
  rw [hpi, hpj]
  exact Option.some.inj (c1.symm.trans c2)

/-- `CeremonyKeysAgree` holds. At a joint start of a check the honest operators agree on the PRSS
keys of the terms by the echo of the setup, or two echo hashes collide, and on the pair keys by the
hidden pair names. -/
theorem ceremonyKeysAgree : CeremonyKeysAgree prims K circuits settings := by
  intro D net rounds c world k _ z hz start hstart
  unfold jointStop at hstart
  split_ifs at hstart with hall
  split at hstart
  · cases hstart
    have hstop : ∀ l, l ∉ D.1 → ∃ point rest, z.1.2 l = some (.inr (point, rest)) ∧
        stopPoint l (z.1.2 l) = point := by
      intro l hl
      obtain ⟨point, rest, h⟩ := hall l hl
      exact ⟨point, rest, h, by simp [stopPoint, h]⟩
    by_cases hcoll : DomainCollision EchoDomain z.2.1
    · exact Or.inr hcoll
    left
    refine ⟨fun T i j hi hj hiT hjT => ?_, fun i j hi hj hij => ?_⟩
    · obtain ⟨pi, ri, hzi, hsi⟩ := hstop i hi
      obtain ⟨pj, rj, hzj, hsj⟩ := hstop j hj
      show (stopPoint i (z.1.2 i)).ctx.prss.term T = (stopPoint j (z.1.2 j)).ctx.prss.term T
      rw [hsi, hsj]
      by_cases hij : i = j
      · subst hij
        rw [hzi] at hzj
        cases hzj
        rfl
      rcases cut_termKeys prims K circuits settings D net rounds k c world z hz i j hi hj hij pi pj ri rj hzi hzj with
        h | h
      · exact h T hiT hjT
      · exact absurd h hcoll
    · obtain ⟨pi, ri, hzi, hsi⟩ := hstop i hi
      obtain ⟨pj, rj, hzj, hsj⟩ := hstop j hj
      show (stopPoint i (z.1.2 i)).ctx.prss.pair j = (stopPoint j (z.1.2 j)).ctx.prss.pair i
      rw [hsi, hsj]
      exact cut_pairKeys prims K circuits settings D net rounds k c world z hz i j hi hj hij pi pj ri rj hzi hzj
  · cases hstart

end Cut

end EchoRound

namespace CeremonyRecords

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `GhostOnPath` holds. -/
theorem ghostOnPath : GhostOnPath (C := C) (E := E) prims := by
  intro Dw D' Ia A α ρ blank fuel st program s z hz h hg hagree i hi
  exact executePhaseR_onPathRH prims Dw D' A blank fuel st program s z hz h hg hagree i hi

omit [Fintype E] [DecidableEq E] in
/-- `CeremonyMonitor` holds. -/
theorem ceremonyMonitor : CeremonyMonitor prims K circuits settings :=
  ceremonyMonitor_of prims K circuits settings (ghostOnPath prims)

/-- `CeremonyBatch` holds. -/
theorem ceremonyBatch : CeremonyBatch prims K circuits settings :=
  ceremonyBatch_of prims K circuits settings (ghostOnPath prims)

omit [Fintype E] [DecidableEq E] in
/-- `RecordedTermKeys` holds. With no global event the echo of the PRSS setup gives one key of each
term to its honest holders. -/
theorem recordedTermKeys : RecordedTermKeys prims K circuits settings := by
  intro D net rounds ℓ c world _ ω hω hglobal k _ _ T j j' b b' hj hj' hjT hj'T hb hb'
  by_cases hjj : j = j'
  · subst hjj
    rw [hb] at hb'
    cases hb'
    rfl
  · rcases EchoRound.ghost_termKeys prims K circuits settings D net rounds c world ω hω T j j' b b' hj hj' hjT hj'T
      (List.mem_of_getElem? hb) (List.mem_of_getElem? hb') hjj with h | h
    · exact h
    · exact absurd (Or.inl h) hglobal

/-- `CeremonyOutputsAgree` holds. -/
theorem ceremonyOutputsAgree : CeremonyOutputsAgree prims K circuits settings :=
  ceremonyOutputsAgree_of_rest prims K circuits settings (ghostOnPath prims) (ceremonyStarted prims K circuits settings)
    (recordedTermKeys prims K circuits settings)

end CeremonyRecords

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.EchoRound.ceremonyKeysAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.EchoRound.ceremonyKeysAgree

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.EchoRound.ghost_termKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.EchoRound.ghost_termKeys

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyMonitor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyMonitor

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyBatch

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree
