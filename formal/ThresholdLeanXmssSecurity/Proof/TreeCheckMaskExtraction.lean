import ThresholdLeanXmssSecurity.Proof.TreeCheckAllHonest

/-!
# Common PRSS masks in an all-honest batch

With an empty coalition, every term and pair stream uses the shared hidden
cache. The actual setup supplies common term and unordered-pair keys. A
joint replay of each batch preserves the real deliveries and saved views,
so the common-mask trace applies even when its incoming cache is populated.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeCheckMaskExtraction

open TreeCheckAllHonestProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- Every PRSS coordinate is hidden from the empty coalition. -/
theorem hidden_noCoalition (name : KeyName C) (h : name ≠ .parameter) :
    Hidden noCoalition name := by
  cases name with
  | parameter => exact (h rfl).elim
  | term T => simp [Hidden, KnownTo, noCoalition]
  | pair p => simp [Hidden, noCoalition]

/-- The finite part of a bit row; the protocol returns zero beyond its count. -/
def row (count : ℕ) (values : ℕ → Bit) : ℕ → Bit :=
  fun g => ((List.range count).map values).getD g 0

/-- A replay of a list of locally determined computations has their mapped values. -/
theorem allowed_mapM_eq {ι α β : Type} {S : OracleSpec.{0, 0} ι}
    (allowed : (t : S.Domain) → S.Range t → Prop)
    (f : α → OracleComp S β) (g : α → β) (xs : List α) (ys : List β)
    (determined : ∀ a ∈ xs, ∀ b, TreeSimCheckAllowed allowed (f a) b → b = g a)
    (run : TreeSimCheckAllowed allowed (xs.mapM f) ys) : ys = xs.map g := by
  induction xs generalizing ys with
  | nil => exact run.pure_inv
  | cons a xs ih =>
    simp only [List.mapM_cons] at run
    obtain ⟨b, hb, rest⟩ := run.bind_inv
    obtain ⟨tail, ht, result⟩ := rest.bind_inv
    rw [result.pure_inv, determined a (by simp) b hb,
      ih tail (fun a ha => determined a (by simp [ha])) ht]
    rfl

/-- The replay's finite stream values are read from its final hidden cache. -/
theorem prgDraw_allowed_eq (prims : Primitives) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (name : KeyName C) (hidden : name ≠ .parameter) (key : HashOutput)
    (label idx count : ℕ) (values : ℕ → Bit)
    (run : TreeSimCheckAllowed allowed (prgBits name key label idx count) values) :
    values = row count (fun g => (cache.2 ((name, key), label, idx, g)).getD 0) := by
  obtain ⟨answers, zero⟩ := treeLockstep_prg_stream_answers prims noCoalition cache
    allowed streams name key label idx count values run
  funext g
  by_cases hg : g < count
  · have cached := answers g hg
    simp only [TreeLockstepStreamAnswer, hidden_noCoalition name hidden, if_true] at cached
    simp only [row, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hg, Option.map_some, Option.getD_some]
    rw [cached]
    rfl
  · rw [zero g (Nat.le_of_not_gt hg)]
    simp [row, List.getD_eq_getElem?_getD, hg]

omit [Field E] [Algebra Bit E] in
/-- A complete PRSS replay yields common term rows and symmetric pair rows.
The cache is the final cache of the same run, rather than an independent sample. -/
theorem prssDraw_allowed_eq (prims : Primitives) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (ctx : Context C) (keys : KeyName C → HashOutput) (label idx count : ℕ)
    (terms : ∀ T, ctx.self ∈ C.holders T → ctx.prss.term T = keys (.term T))
    (pairs : ∀ j (hj : j ≠ ctx.self),
      ctx.prss.pair j = keys (.pair (C.pairOf ctx.self j (Ne.symm hj))))
    (rnd : PrssOutput C Bit)
    (run : TreeSimCheckAllowed allowed (prssDraw ctx (bitCodec (E := E)) label idx count) rnd) :
    let values := fun name => row count
      (fun g => (cache.2 ((name, keys name), label, idx, g)).getD 0)
    rnd = (honestR (fun T => values (.term T)) ctx.self,
      honestZ (fun p => values (.pair p)) ctx.self) := by
  let values := fun name => row count
    (fun g => (cache.2 ((name, keys name), label, idx, g)).getD 0)
  unfold prssDraw at run
  obtain ⟨rr, hrr, rest⟩ := run.bind_inv
  obtain ⟨zz, hzz, result⟩ := rest.bind_inv
  have tr : rr = C.terms.map (fun T => if ctx.self ∈ C.holders T
      then values (.term T) else fun _ => 0) := by
    apply allowed_mapM_eq allowed _ _ C.terms rr _ hrr
    intro T _ v hv
    by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held] at hv ⊢
      rw [terms T held] at hv
      exact prgDraw_allowed_eq prims cache allowed streams (.term T)
        (by intro he; cases he) _ label idx count v hv
    · simp only [if_neg held] at hv ⊢
      exact hv.pure_inv
  have pr : zz = C.parties.map (fun j => if hj : j = ctx.self then fun _ => 0
      else values (.pair (C.pairOf ctx.self j (Ne.symm hj)))) := by
    apply allowed_mapM_eq allowed _ _ C.parties zz _ hzz
    intro j _ v hv
    by_cases hj : j = ctx.self
    · simp only [dif_pos hj] at hv ⊢
      exact hv.pure_inv
    · simp only [dif_neg hj] at hv ⊢
      rw [pairs j hj] at hv
      exact prgDraw_allowed_eq prims cache allowed streams
        (.pair (C.pairOf ctx.self j (Ne.symm hj))) (by intro he; cases he)
        _ label idx count v hv
  rw [result.pure_inv, tr, pr]
  apply Prod.ext
  · funext T
    exact getD_terms_idxOf _ (fun _ => 0) T
  · funext j
    exact getD_parties _ (fun _ => 0) j

/-- Extract a local replay from the honest copy of the world oracles. -/
theorem allowed_free {α : Type}
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (p : OracleComp (LocalSpec C) α) (a : α)
    (run : TreeSimCheckAllowed allowed (free p) a) :
    TreeSimCheckAllowed (fun t u => allowed (.inr t) u) p a :=
  TreeSimCheckAllowed.simulate_inv
    (fun t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (Sum.inr t))) allowed _
    (fun t u hu => TreeSimCheckAllowed.query_inv (allowed := allowed) (Sum.inr t) u hu) p a run

omit [Field E] [Algebra Bit E] in
/-- With an empty coalition the adversary cannot alter a real network delivery.
Its calls are erased from the replay while every honest local answer is retained. -/
theorem stepRound_erase {Ia α : Type}
    (A : Adversary C E Ia PEmpty PEmpty)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (r : A.State × (C.Party → Step C E RealSpec α) ×
      (C.Party → C.Party → Option (Msg E)))
    (run : TreeSimCheckAllowed allowed
      (stepRound worldRoles noCoalition A noFunctionality state steps) r) :
    TreeSimCheckAllowed (fun t u => allowed (.inr t) u)
      (honestStep noFunctionality PEmpty.elim steps) r.2.1 := by
  have noCall i : (steps i).callInput.isSome = false := by
    cases steps i with
    | done _ => rfl
    | wait _ _ => rfl
    | call input _ => exact input.elim
  unfold stepRound at run
  simp only [noCoalition_val, Finset.notMem_empty,
    not_false_eq_true, if_false, noCall, Bool.false_eq_true, and_false,
    exists_false, false_and] at run
  obtain ⟨p, _, rest⟩ := run.bind_inv
  obtain ⟨next, hn, result⟩ := rest.bind_inv
  rw [result.pure_inv]
  unfold honestStep
  simp only [noCall, Bool.false_eq_true, exists_false, false_and, if_false]
  apply allowed_free allowed _ next
  rw [free_sequenceFin]
  convert hn using 1
  congr 1
  funext i
  cases steps i with
  | done _ => rfl
  | wait _ _ => rfl
  | call input _ => exact input.elim

omit [Field E] [Algebra Bit E] in
/-- Arbitrary adversary calls disappear from an all-honest real execution's replay. -/
theorem rounds_erase {Ia α : Type}
    (A : Adversary C E Ia PEmpty PEmpty)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed
      (executeRounds worldRoles noCoalition A noFunctionality fuel state steps) r) :
    TreeSimCheckAllowed (fun t u => allowed (.inr t) u)
      (honestRounds noFunctionality PEmpty.elim fuel steps) r.2 := by
  induction fuel generalizing state steps r with
  | zero =>
    rw [run.pure_inv]
    exact .pure _ _
  | succ fuel ih =>
    unfold executeRounds at run
    unfold honestRounds
    by_cases done : ∀ i, (steps i).isDone
    · rw [if_pos (by simpa using done)] at run
      rw [if_pos done, run.pure_inv]
      exact .pure _ _
    · rw [if_neg (by simpa using done)] at run
      rw [if_neg done]
      obtain ⟨next, hn, rest⟩ := run.bind_inv
      exact (stepRound_erase A allowed state steps next hn).bind
        (ih next.1 next.2.1 r rest)

omit [Field E] [Algebra Bit E] in
/-- The whole all-honest phase retains one honest-network replay in the same final cache. -/
theorem phase_erase {Ia α : Type}
    (A : Adversary C E Ia PEmpty PEmpty)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (r : A.State × (C.Party → Option α))
    (run : TreeSimCheckAllowed allowed
      (executePhase worldRoles noCoalition A noFunctionality fuel state program) r) :
    TreeSimCheckAllowed (fun t u => allowed (.inr t) u)
      (honestStart program >>= honestRounds noFunctionality PEmpty.elim fuel) r.2 := by
  obtain ⟨steps, hs, hr⟩ := run.bind_inv
  rw [startSteps_honest] at hs
  exact (allowed_free allowed _ steps hs).bind (rounds_erase A allowed fuel state steps r hr)

/-- The actual batch's honest-network replay uses the final cache of that same batch. -/
theorem batch_honest_replay [Fintype E] [DecidableEq E]
    (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : o ∈ support (treeCheckBatchPre prims K circuits settings noCoalition A b)) :
    TreeSimCheckAllowed (fun t u => TreeLockstepWorldStreams prims noCoalition o.2.1 (.inr t) u)
      (honestStart (fun i => treeSimCheckBatchPrefix K circuits settings (b.ctx i) b.jobs b.initial) >>=
        honestRounds noFunctionality PEmpty.elim (b.rounds circuits settings)) o.1.2 :=
  phase_erase A _ _ b.state _ o.1
    (treeLockstep_logged_run_allowed prims noCoalition _ b.world o run)

/-- A sequence of local draws retains one value for each operator, with the
continuations replayed in their original order. -/
theorem allowed_sequence_bind {ι α β : Type} {S : OracleSpec.{0, 0} ι}
    (allowed : (t : S.Domain) → S.Range t → Prop) :
    ∀ {n : ℕ} (draw : Fin n → OracleComp S α)
      (next : Fin n → α → OracleComp S β) (out : Fin n → β),
      TreeSimCheckAllowed allowed (Concrete.sequenceFin (fun i => draw i >>= next i)) out →
      ∃ values : Fin n → α, (∀ i, TreeSimCheckAllowed allowed (draw i) (values i)) ∧
        TreeSimCheckAllowed allowed (Concrete.sequenceFin (fun i => next i (values i))) out
  | 0, _, _, out, _ => ⟨Fin.elim0, fun i => i.elim0, by
      have he : out = Fin.elim0 := funext fun i => i.elim0
      subst out
      exact .pure _ _⟩
  | n + 1, draw, next, out, run => by
      simp only [Concrete.sequenceFin] at run
      obtain ⟨head, hh, rest⟩ := run.bind_inv
      obtain ⟨value, hv, hn⟩ := hh.bind_inv
      obtain ⟨tail, ht, result⟩ := rest.bind_inv
      obtain ⟨values, each, tailRun⟩ := allowed_sequence_bind allowed
        (fun i => draw i.succ) (fun i => next i.succ) tail ht
      refine ⟨Fin.cons value values, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => exact hv
        | succ i => exact each i
      · rw [result.pure_inv]
        exact hn.bind (tailRun.bind (.pure _ _))

omit [Field E] [Algebra Bit E] in
/-- The local draws at a phase head can be extracted without changing any continuation. -/
theorem honest_local_draw_replay {α β : Type}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (draw : C.Party → OracleComp (LocalSpec C) α)
    (next : C.Party → α → PartyM C E RealSpec β) (fuel : ℕ)
    (out : C.Party → Option β)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => localStep (draw i) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim fuel) out) :
    ∃ values : C.Party → α,
      (∀ i, TreeSimCheckAllowed allowed (draw i) (values i)) ∧
      TreeSimCheckAllowed allowed
        (honestStart (fun i => next i (values i)) >>=
          honestRounds noFunctionality PEmpty.elim fuel) out := by
  obtain ⟨steps, hs, hr⟩ := run.bind_inv
  simp only [honestStart, advance_localStep_bind] at hs
  obtain ⟨values, each, rest⟩ := allowed_sequence_bind allowed _ _ steps hs
  exact ⟨values, each, rest.bind hr⟩

omit [Field E] [Algebra Bit E] in
/-- Extracting draws from the hash-and-stream interface. -/
theorem honest_draw_replay {α β : Type}
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (draw : C.Party → OracleComp (RoSpec C) α)
    (next : C.Party → α → PartyM C E RealSpec β) (fuel : ℕ)
    (out : C.Party → Option β)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => oracleStep (draw i) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim fuel) out) :
    ∃ values : C.Party → α,
      (∀ i, TreeSimCheckAllowed allowed (liftComp (draw i) (LocalSpec C)) (values i)) ∧
      TreeSimCheckAllowed allowed
        (honestStart (fun i => next i (values i)) >>=
          honestRounds noFunctionality PEmpty.elim fuel) out :=
  honest_local_draw_replay allowed _ next fuel out run

omit [Field E] [Algebra Bit E] in
/-- The same final cache supplies one common mask family for the next real PRSS round. -/
theorem shared_prss_draw_replay {α : Type}
    (prims : Primitives) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr (.inr x)) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (ctx : C.Party → Context C) (shared : TreeCheckAllHonestProof.SharedPrss ctx)
    (label idx count : ℕ) (next : C.Party → PrssOutput C Bit → PartyM C E RealSpec α)
    (fuel : ℕ) (out : C.Party → Option α)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => oracleStep (prssDraw (ctx i) (bitCodec (E := E)) label idx count) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim fuel) out) :
    ∃ (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit),
      TreeSimCheckAllowed allowed
        (honestStart (fun i => next i (honestR rr i, honestZ zz i)) >>=
          honestRounds noFunctionality PEmpty.elim fuel) out := by
  obtain ⟨values, each, rest⟩ := honest_draw_replay allowed _ next fuel out run
  obtain ⟨terms, pairs, self, ht, hp⟩ := shared
  let keys : KeyName C → HashOutput
    | .parameter => 0
    | .term T => terms T
    | .pair p => pairs p
  let rows := fun name => row count
    (fun g => (cache.2 ((name, keys name), label, idx, g)).getD 0)
  have masks i : values i = (honestR (fun T => rows (.term T)) i,
      honestZ (fun p => rows (.pair p)) i) := by
    have ro : TreeSimCheckAllowed (fun t u => allowed (.inr t) u)
        (prssDraw (ctx i) (bitCodec (E := E)) label idx count) (values i) :=
      TreeSimCheckAllowed.simulate_inv
        (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (Sum.inr t))) allowed _
        (fun t u hu => TreeSimCheckAllowed.query_inv (allowed := allowed) (Sum.inr t) u hu)
        _ _ (each i)
    have hm := prssDraw_allowed_eq prims cache (fun t u => allowed (.inr t) u)
      streams (ctx i) keys label idx count
      (fun T held => ht i T (by simpa only [self i] using held))
      (fun j hj => by
        have hij : i ≠ j := by simpa only [self i] using Ne.symm hj
        simpa only [self i, keys] using hp i j hij) (values i) ro
    simpa only [self i] using hm
  refine ⟨fun T => rows (.term T), fun p => rows (.pair p), ?_⟩
  simpa only [masks] using rest

/-- Common PRSS masks pass through the actual peer or collector messages. -/
theorem reshare_rounds {α : Type} [Nonempty C.Party]
    (K : Constants C E) (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (mode : ReshareMode) (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit)
    (v : C.Party → ℕ → Bit) (count : ℕ) (st : C.Party → RunState C)
    (next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) (fuel : ℕ) :
    (honestStart (fun i => (reshareWith K (ctx i) mode (honestR rr i, honestZ zz i)
      (v i) count).run (st i) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim (fuel + mode.rounds)) =
      (honestStart (fun i =>
        let z := TreeCheckAllHonestProof.maskOutputs K mode rr zz v count i
        next i (z, ⟨recordMode K mode i (st i).history z count, (st i).label, (st i).tag⟩)) >>=
        honestRounds noFunctionality PEmpty.elim fuel) := by
  cases mode with
  | peer =>
    simp only [reshareWith, reshare_run, bind_assoc, pure_bind, ReshareMode.rounds]
    rw [honestRounds_exchange noFunctionality PEmpty.elim fuel _ _
      (fun k j => isAbort_reshareOut K _ bitCodec_roundTrip _ _ _ _ _ _)]
    unfold TreeCheckAllHonestProof.maskOutputs reshareZ reshareOut reshareU
      localContext recordPeer recordMode
    simp only [self]
  | collector =>
    simp only [reshareWith, reshareCollector_run, bind_assoc, pure_bind, ReshareMode.rounds, self]
    rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
    rw [honestRounds_exchange noFunctionality PEmpty.elim (fuel + 1) _ _
      (fun k j => isAbort_colOut1 K _ _ _ _ _ _)]
    rw [honestRounds_exchange noFunctionality PEmpty.elim fuel _ _
      (fun k j => isAbort_colOut2 K _ _ _ _ _ _ _)]
    rfl

/-- A complete real mask draw and reshare removes exactly its network rounds. -/
theorem gadget_replay {α : Type} [Nonempty C.Party]
    (prims : Primitives) (K : Constants C E) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr (.inr x)) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (ctx : C.Party → Context C) (shared : TreeCheckAllHonestProof.SharedPrss ctx)
    (mode : ReshareMode) (v : C.Party → ℕ → Bit) (count label : ℕ)
    (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (fuel : ℕ) (out : C.Party → Option α)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => oracleStep
        (prssDraw (ctx i) (bitCodec (E := E)) (st i).label 0 count) >>= fun rnd =>
        (reshareWith K (ctx i) mode rnd (v i) count).run (nextLabel (st i)) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim (fuel + mode.rounds)) out) :
    ∃ (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit),
      TreeSimCheckAllowed allowed
        (honestStart (fun i =>
          let z := TreeCheckAllHonestProof.maskOutputs K mode rr zz v count i
          next i (z, ⟨recordMode K mode i (st i).history z count, label + 1, (st i).tag⟩)) >>=
          honestRounds noFunctionality PEmpty.elim fuel) out := by
  simp only [labels] at run
  obtain ⟨rr, zz, rest⟩ := shared_prss_draw_replay prims cache allowed streams ctx shared
    label 0 count _ (fuel + mode.rounds) out run
  refine ⟨rr, zz, ?_⟩
  rw [reshare_rounds K ctx shared.choose_spec.choose_spec.1 mode rr zz v count
    (fun i => nextLabel (st i)) next fuel] at rest
  simpa only [nextLabel, labels] using rest

/-- A real multiplication layer extends the common-mask trace of its saved tuples. -/
theorem layer_replay {α : Type} [Nonempty C.Party]
    (prims : Primitives) (K : Constants C E) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr (.inr x)) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (ctx : C.Party → Context C) (shared : SharedPrss ctx)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C)
    (l label : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (trace : MaskLayerTrace K mode jobs x l p)
    (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (next : C.Party → (MainInput C × List (Tuple C)) × RunState C → PartyM C E RealSpec α)
    (fuel : ℕ) (out : C.Party → Option α)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => (layerBody K (realRunGadgets K (ctx i) mode) jobs (p i) l).run (st i) >>=
        next i) >>= honestRounds noFunctionality PEmpty.elim (fuel + mode.rounds)) out) :
    ∃ (p' : C.Party → MainInput C × List (Tuple C)) (st' : C.Party → RunState C),
      MaskLayerTrace K mode jobs x (l + 1) p' ∧ (∀ i, (st' i).label = label + 1) ∧
      TreeSimCheckAllowed allowed
        (honestStart (fun i => next i (p' i, st' i)) >>=
          honestRounds noFunctionality PEmpty.elim fuel) out := by
  have self := shared.choose_spec.choose_spec.1
  have mult i : mulRep K (ctx i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1) =
      mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1) := by
    unfold mulRep
    rw [self i]
    rfl
  simp only [layerBody, StateT.run_bind, StateT.run_pure, realMult_run,
    bind_assoc, pure_bind, mult] at run
  obtain ⟨rr, zz, rest⟩ := gadget_replay prims K cache allowed streams ctx shared mode
    (fun i => mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1))
    (gatesAt jobs l).length label st labels _ fuel out run
  let z := maskOutputs K mode rr zz
    (fun i => mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1))
    (gatesAt jobs l).length
  refine ⟨layerUpdate K mode jobs l p z,
    fun i => ⟨recordMode K mode i (st i).history (z i) (gatesAt jobs l).length,
      label + 1, (st i).tag⟩, .step trace rr zz, fun _ => rfl, ?_⟩
  exact rest

/-- The actual ordered fold of multiplication layers yields its common-mask trace. -/
theorem layers_replay {α : Type} [Nonempty C.Party]
    (prims : Primitives) (K : Constants C E) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr (.inr x)) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (ctx : C.Party → Context C) (shared : SharedPrss ctx)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C)
    (count l label : ℕ) (p : C.Party → MainInput C × List (Tuple C))
    (trace : MaskLayerTrace K mode jobs x l p)
    (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (next : C.Party → (MainInput C × List (Tuple C)) × RunState C → PartyM C E RealSpec α)
    (fuel : ℕ) (out : C.Party → Option α)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => ((List.range' l count).foldlM
        (layerBody K (realRunGadgets K (ctx i) mode) jobs) (p i)).run (st i) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim (fuel + count * mode.rounds)) out) :
    ∃ (p' : C.Party → MainInput C × List (Tuple C)) (st' : C.Party → RunState C),
      MaskLayerTrace K mode jobs x (l + count) p' ∧ (∀ i, (st' i).label = label + count) ∧
      TreeSimCheckAllowed allowed
        (honestStart (fun i => next i (p' i, st' i)) >>=
          honestRounds noFunctionality PEmpty.elim fuel) out := by
  induction count generalizing l label p st with
  | zero =>
    refine ⟨p, st, trace, labels, ?_⟩
    simpa only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind,
      Nat.zero_mul, Nat.add_zero] using run
  | succ count ih =>
    simp only [List.range'_succ, List.foldlM_cons, StateT.run_bind, bind_assoc] at run
    have cost : fuel + (count + 1) * mode.rounds =
        (fuel + count * mode.rounds) + mode.rounds := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [cost] at run
    obtain ⟨p', st', trace', labels', rest⟩ := layer_replay prims K cache allowed streams
      ctx shared mode jobs x l label p trace st labels _ (fuel + count * mode.rounds) out run
    obtain ⟨p'', st'', trace'', labels'', last⟩ := ih (l + 1) (label + 1) p' trace'
      st' labels' rest
    exact ⟨p'', st'', by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using trace'',
      fun i => by simpa only [Nat.add_assoc, Nat.add_comm 1 count] using labels'' i, last⟩

/-- The honest batch prefix saves exactly a trace of common-mask multiplications
and its final peer rerandomization. -/
theorem beforeVerify_replay [Fintype E] [DecidableEq E] [Nonempty C.Party]
    (prims : Primitives) (K : Constants C E) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr (.inr x)) u →
      TreeLockstepStreamAnswer prims noCoalition cache x u)
    (ctx : C.Party → Context C) (shared : SharedPrss ctx)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C)
    (label : ℕ) (st : C.Party → RunState C) (labels : ∀ i, (st i).label = label)
    (out : C.Party → Option (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => (treeSimCheckBeforeVerify K (ctx i) mode jobs (x i)).run (st i) >>=
        fun result => pure (x i, result)) >>=
        honestRounds noFunctionality PEmpty.elim (depth jobs * mode.rounds + 1)) out) :
    (∀ i, (out i).isSome) ∧ (∀ i, (treeCheckPrefixData (out i)).1 = x i) ∧
      SavedByMasks K mode jobs x (fun i => (treeCheckPrefixData (out i)).2.1.2) := by
  have self := shared.choose_spec.choose_spec.1
  simp only [treeSimCheckBeforeVerify, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind, List.range_eq_range'] at run
  rw [Nat.add_comm (depth jobs * mode.rounds) 1] at run
  obtain ⟨p, st', trace, labels', rest⟩ := layers_replay prims K cache allowed streams ctx shared
    mode jobs x (depth jobs) 0 label (fun i => (x i, [])) (.zero) st labels _ 1 out run
  have owner i : ownerSum K (ctx i) (outputShares K jobs (p i).1) =
      ownerSum K (localContext i) (outputShares K jobs (p i).1) := by
    unfold ownerSum
    rw [self i]
    rfl
  simp only [realRerand_run, owner] at rest
  obtain ⟨rr, zz, last⟩ := gadget_replay prims K cache allowed streams ctx shared .peer
    (fun i => ownerSum K (localContext i) (outputShares K jobs (p i).1))
    (outputsOf jobs).length (label + depth jobs) st' labels' _ 0 out rest
  rw [honestRounds_pure] at last
  rw [last.pure_inv]
  refine ⟨fun _ => rfl, fun _ => rfl, p, rr, zz, ?_, rfl⟩
  simpa only [Nat.zero_add] using trace

set_option backward.isDefEq.respectTransparency false in
/-- The original all-honest extraction target, on the actual scheduler and caches. -/
theorem batchMaskExtraction [Fintype E] [DecidableEq E]
    (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    BatchMaskExtraction prims K circuits settings := by
  have positive : 0 < C.n := by
    have := C.one_le_t
    unfold Committee.n
    omega
  letI : Nonempty C.Party := ⟨⟨0, positive⟩⟩
  intro A b parameters shared o run _
  have replay := batch_honest_replay prims K circuits settings A b o run
  simp only [treeSimCheckBatchPrefix, inputShares_fun, mapM_oracleStep, parameters] at replay
  let allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop :=
    fun t u => TreeLockstepWorldStreams prims noCoalition o.2.1 (.inr t) u
  let next : C.Party → MainInput C → PartyM C E RealSpec
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C) := fun i inputs => do
    let result ← (treeSimCheckBeforeVerify K (b.ctx i) settings.mode
      (b.jobs.map (circuits b.parameter ·.kind)) inputs).run
      ⟨fun _ => [], b.initial.1, b.initial.2⟩
    pure (inputs, result)
  obtain ⟨x, _, rest⟩ := honest_draw_replay allowed
    (fun i => b.jobs.mapM (inputQuery (b.ctx i))) next (b.rounds circuits settings) o.1.2 replay
  dsimp only [next, allowed, TreeCheckBatchBoundary.rounds] at rest
  have certificate := beforeVerify_replay prims K o.2.1
    (fun t u => TreeLockstepWorldStreams prims noCoalition o.2.1 (.inr t) u)
    (fun _ _ h => h) b.ctx shared settings.mode (b.jobs.map (circuits b.parameter ·.kind)) x
    b.initial.1 (fun _ => ⟨fun _ => [], b.initial.1, b.initial.2⟩) (fun _ => rfl) o.1.2
  have extracted := certificate (by
    dsimp only [RealSpec, WorldSpec] at rest ⊢
    with_reducible_and_instances exact rest)
  obtain ⟨_, inputs, saved⟩ := extracted
  have input_eq : (fun i => (treeCheckPrefixData (o.1.2 i)).1) = x := funext inputs
  rw [input_eq]
  exact saved

/-- Interpreting an allowed replay preserves its value when every interpreted
query has an allowed replay with the same answer. -/
theorem allowed_simulate {ι κ α : Type} {S : OracleSpec.{0, 0} ι} {T : OracleSpec.{0, 0} κ}
    (source : (t : S.Domain) → S.Range t → Prop)
    (target : (t : T.Domain) → T.Range t → Prop) (impl : QueryImpl S (OracleComp T))
    (queries : ∀ t u, source t u → TreeSimCheckAllowed target (impl t) u)
    (p : OracleComp S α) (a : α) (run : TreeSimCheckAllowed source p a) :
    TreeSimCheckAllowed target (simulateQ impl p) a := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b =>
    rw [run.pure_inv, simulateQ_pure]
    exact .pure _ _
  | query_bind t k ih =>
    obtain ⟨u, hu, rest⟩ := run.bind_inv
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (queries t u (hu.query_inv t u)).bind (ih u a rest)

/-- A local hash-only replay can use the existing deterministic oracle-step replay theorem. -/
theorem local_hash_replay [Fintype E] [DecidableEq E] {α : Type}
    (prims : Primitives) (hash : Query C → HashOutput)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (hashes : ∀ q u, allowed (.inr (.inl q)) u → hash q = u)
    (p : OracleComp (RoSpec C) α) (noPrg : IsQueryBoundP p TreeCheckPrgQuery 0)
    (a : α) (run : TreeSimCheckAllowed allowed (liftComp p (LocalSpec C)) a) :
    a = D prims hash p := by
  let party : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop
    | .inl (.inl t), u => allowed t u
    | _, _ => True
  have lifted : TreeSimCheckAllowed party (liftComp (liftComp p (LocalSpec C)) (PartySpec C E RealSpec)) a := by
    rw [liftComp_def]
    apply allowed_simulate allowed party _ _ _ a run
    intro t u hu
    rcases t with n | (q | x)
    · exact TreeSimCheckAllowed.query (allowed := party) (.inl (.inl (.inl n))) pure u u hu (.pure _ _)
    · exact TreeSimCheckAllowed.query (allowed := party) (.inl (.inl (.inr (.inl q)))) pure u u hu (.pure _ _)
    · exact TreeSimCheckAllowed.query (allowed := party) (.inl (.inl (.inr (.inr x)))) pure u u hu (.pure _ _)
  apply treeCheck_hash_replay prims hash party hashes p noPrg a
  exact lifted.bind (.pure _ _)

/-- Hash-only draws can be replaced by their values under the run's one coherent hash function. -/
theorem honest_hash_draw_replay [Fintype E] [DecidableEq E] {α β : Type}
    (prims : Primitives) (hash : Query C → HashOutput)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (hashes : ∀ q u, allowed (.inr (.inl q)) u → hash q = u)
    (draw : C.Party → OracleComp (RoSpec C) α)
    (noPrg : ∀ i, IsQueryBoundP (draw i) TreeCheckPrgQuery 0)
    (next : C.Party → α → PartyM C E RealSpec β) (fuel : ℕ) (out : C.Party → Option β)
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => oracleStep (draw i) >>= next i) >>=
        honestRounds noFunctionality PEmpty.elim fuel) out) :
    TreeSimCheckAllowed allowed
      (honestStart (fun i => next i (D prims hash (draw i))) >>=
        honestRounds noFunctionality PEmpty.elim fuel) out := by
  obtain ⟨values, each, rest⟩ := honest_draw_replay allowed draw next fuel out run
  have fixed i := local_hash_replay (E := E) prims hash allowed hashes (draw i) (noPrg i) (values i) (each i)
  simpa only [fixed] using rest

/-- A hash query does not use the PRG interface. -/
theorem hash_noPrg (q : Query C) : IsQueryBoundP (hashQuery q) TreeCheckPrgQuery 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [TreeCheckPrgQuery]

/-- A list of hash queries contains no PRG query. -/
theorem hash_mapM_noPrg {α : Type} (queries : α → Query C) (xs : List α) :
    IsQueryBoundP (xs.mapM (fun a => hashQuery (queries a))) TreeCheckPrgQuery 0 := by
  simpa using queryBound_mapM TreeCheckPrgQuery _ 0 xs
    (fun a _ => hash_noPrg _)

/-- Setup key derivation uses only its domain-separated hash queries. -/
theorem deriveKeys_noPrg (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) TreeCheckPrgQuery 0 := by
  have hh q : IsQueryBoundP (hashQuery (C := C) q) TreeCheckPrgQuery 0 := hash_noPrg q
  have rest (parameter : HashOutput) : IsQueryBoundP (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        hashQuery (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        hashQuery (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      pure (parameter, fun T => term.getD (C.terms.idxOf T) 0,
        fun (j : C.Party) => pair.getD j.val 0) : OracleComp (RoSpec C) _) TreeCheckPrgQuery 0 := by
    apply isQueryBoundP_bind (m := 0)
    · simpa using queryBound_mapM TreeCheckPrgQuery _ 0 C.terms (fun T _ => by
        split_ifs
        · exact hh _
        · exact isQueryBoundP_pure _ _ _)
    · intro terms _
      apply isQueryBoundP_bind (m := 0)
      · simpa using queryBound_mapM TreeCheckPrgQuery _ 0 C.parties (fun j _ => by
          split_ifs
          · exact isQueryBoundP_pure _ _ _
          · exact hh _)
      · intro pairs _
        exact isQueryBoundP_pure _ _ _
  unfold deriveKeys
  split_ifs
  · exact isQueryBoundP_bind (m := 0) (hh _) fun parameter _ => rest parameter
  · exact isQueryBoundP_bind (m := 0) (isQueryBoundP_pure _ _ _) fun parameter _ => rest parameter

set_option backward.isDefEq.respectTransparency false in
/-- In an all-honest setup every term and unordered pair has one actual derived key. -/
theorem honest_setup_replay [Fintype E] [DecidableEq E] [Nonempty C.Party]
    (prims : Primitives) (hash : Query C → HashOutput)
    (allowed : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → Prop)
    (hashes : ∀ q u, allowed (.inr (.inl q)) u → hash q = u)
    (out : C.Party → Option (PrssKeys C))
    (run : TreeSimCheckAllowed allowed
      (honestStart (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) >>=
        honestRounds noFunctionality PEmpty.elim setupRounds) out) :
    ∃ (terms : C.Term → HashOutput) (pairs : C.Pair → HashOutput),
      out = fun i => some (prssKeysOf terms pairs i) := by
  simp only [prssSetup_eq, bind_assoc, commitRevealEcho_eq] at run
  obtain ⟨parts, _, run⟩ := honest_local_draw_replay allowed _ _ _ out run
  have run := honest_hash_draw_replay prims hash allowed hashes
    (fun i => commitQueries .prss i (parts i))
    (fun _ => hash_mapM_noPrg _ _) _ 3 out run
  rw [show 3 = (1 + 1) + 1 from rfl,
    honestRounds_exchange noFunctionality PEmpty.elim 2 _ _
      (fun k j => isAbort_commitOutbox k _ j),
    honestRounds_exchange noFunctionality PEmpty.elim 1 _ _
      (fun k j => isAbort_revealOutbox _ k _ j)] at run
  have run := honest_hash_draw_replay prims hash allowed hashes
    (fun i => openQueries .prss i (honestReveals (E := E) .prss parts i))
    (fun _ => hash_mapM_noPrg _ _) _ 1 out run
  have opened i : openCheck .prss i (parts i)
      (fun k => commitOutbox (E := E) k (D prims hash (commitQueries .prss k (parts k))) i)
      (fun k => revealOutbox .prss k (parts k) i)
      (D prims hash (openQueries .prss i (honestReveals (E := E) .prss parts i))) :=
    openCheck_honest prims hash .prss parts i
  simp only [require_bind_of (opened _), pure_bind] at run
  have run := honest_hash_draw_replay prims hash allowed hashes
    (fun i => deriveKeys .prss i (honestView (E := E) .prss parts i))
    (fun i => deriveKeys_noPrg _ _ _) _ 1 out run
  have run := honest_hash_draw_replay prims hash allowed hashes
    (fun i => sharedQueries .prss i (D prims hash (deriveKeys .prss i (honestView (E := E) .prss parts i))))
    (fun _ => hash_mapM_noPrg _ _) _ 1 out run
  rw [show 1 = 0 + 1 from rfl,
    honestRounds_exchange noFunctionality PEmpty.elim 0 _ _
      (fun k j => isAbort_echoOutbox _ k _ _ j)] at run
  simp only [require_bind_of (echoCheck_honest prims hash .prss parts _)] at run
  rw [honestRounds_pure] at run
  refine ⟨fun T => hash (termInput .prss parts T), fun p => hash (pairInput .prss parts p), ?_⟩
  rw [run.pure_inv]
  funext i
  simp only [D_deriveKeys_honest]
  rfl


/-- A real logged execution has a coherent hash replay in its own final public cache. -/
theorem logged_hash_replay {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    TreeSimCheckAllowed (TreeSimCheckWorldHashes (hashOf prims r.2.1.1)) p r.1 := by
  rw [treeSimLoggedWorld_run, support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact ⟨u.1.2, treeSimCheckReplay_supported prims D p s.1 u.1.1 u.1.2 u.2 hu,
    (treeSimCheck_logged_hashes prims D p s.1 u.1.1 u.1.2 u.2 hu).2⟩

/-- The actual all-honest setup succeeds with common term and unordered-pair keys,
from every incoming world and against every adversary. -/
theorem setup_keys [Fintype E] [DecidableEq E]
    (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (s : TreeSimState C)
    (o : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : o ∈ support ((executePhase (treeSimRealRoles prims noCoalition)
      noCoalition A noFunctionality setupRounds state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s)) :
    ∃ (terms : C.Term → HashOutput) (pairs : C.Pair → HashOutput),
      o.1.2 = fun i => some (prssKeysOf terms pairs i) := by
  have positive : 0 < C.n := by
    have := C.one_le_t
    unfold Committee.n
    omega
  letI : Nonempty C.Party := ⟨⟨0, positive⟩⟩
  rw [treeSimRealRoles, ← simulateQ_executePhase] at run
  have replay := phase_erase A _ setupRounds state _ o.1
    (logged_hash_replay prims noCoalition _ s o run)
  exact honest_setup_replay prims (hashOf prims o.2.1.1) _
    (fun _ _ h => h) o.1.2 replay

/-- The adversary's actual setup prefix supplies one common dealing to all operators. -/
theorem saltSetup_keys [Fintype E] [DecidableEq E]
    (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux)
    (o : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : o ∈ support (treeSaltSetup prims noCoalition A x z)) :
    ∃ (terms : C.Term → HashOutput) (pairs : C.Pair → HashOutput),
      o.1.2 = fun i => some (prssKeysOf terms pairs i) := by
  obtain ⟨start, _, rest⟩ := (mem_support_bind_iff _ _ _).mp run
  exact setup_keys prims A start.1 start.2 o rest

/-- Contexts retaining one common dealing read the same term and unordered-pair masks. -/
theorem sharedPrss_of_keys (ctx : C.Party → Context C)
    (terms : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (self : ∀ i, (ctx i).self = i)
    (keys : ∀ i, (ctx i).prss = prssKeysOf terms pairs i) : SharedPrss ctx := by
  refine ⟨terms, pairs, self, ?_, ?_⟩
  · intro i T hi
    simp only [keys i, prssKeysOf, if_pos hi]
  · intro i j h
    simp only [keys i, prssKeysOf, dif_neg (Ne.symm h)]

/-- Every batch context retaining the output of the actual setup has shared PRSS keys. -/
theorem saltSetup_shared [Fintype E] [DecidableEq E]
    (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux)
    (o : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : o ∈ support (treeSaltSetup prims noCoalition A x z))
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (keys : ∀ i, o.1.2 i = some (ctx i).prss) : SharedPrss ctx := by
  obtain ⟨terms, pairs, shared⟩ := saltSetup_keys prims A x z o run
  apply sharedPrss_of_keys ctx terms pairs self
  intro i
  have h := keys i
  rw [shared] at h
  exact (Option.some.inj h).symm

/-- Default lookup at a reached setup row always returns the actual common dealing. -/
theorem saltSetup_shared_default [Fintype E] [DecidableEq E]
    (prims : Primitives) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux)
    (o : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : o ∈ support (treeSaltSetup prims noCoalition A x z))
    (fallback : C.Party → PrssKeys C) :
    SharedPrss (fun i => ⟨i, x i, (o.1.2 i).getD (fallback i)⟩) := by
  obtain ⟨terms, pairs, shared⟩ := saltSetup_keys prims A x z o run
  apply sharedPrss_of_keys _ terms pairs (fun _ => rfl)
  intro i
  simp only [shared, Option.getD_some]

end ThresholdLeanXmssSecurity.TreeCheckMaskExtraction

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.prssDraw_allowed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.prssDraw_allowed_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.phase_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.phase_erase

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.batch_honest_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.batch_honest_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.shared_prss_draw_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.shared_prss_draw_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.reshare_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.reshare_rounds

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.gadget_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.gadget_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.layer_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.layer_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.layers_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.layers_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.beforeVerify_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.beforeVerify_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.batchMaskExtraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.batchMaskExtraction

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.honest_setup_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.honest_setup_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.setup_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.setup_keys

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.saltSetup_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.saltSetup_keys

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.saltSetup_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.saltSetup_shared

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.saltSetup_shared_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckMaskExtraction.saltSetup_shared_default
