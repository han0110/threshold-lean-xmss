import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Readiness
import XmssSecurity.Proof.CappedEncodingRejection
import XmssSecurity.Proof.Bridge.Translate

/-!
# The law of the head of a bottom tree

The head of a run of a bottom tree is its first ceremony and then the local search, a phase with no
round.

* `timed_of_bind` moves the round count of a program to its first part when each continuation can
  end with a result in no round. The search can end, because some answer of `H` truncates to a
  codeword (`exists_decode_truncate`).
* `freeRun_tweakable` states that a computation of `Th` in `streamWorld` moves the world only at the
  inputs of `Th` (`HashStep`) and gives its answer again from a larger cache. The ledger, the
  provenance of the hidden keys, the global events and wrong outputs read no such cell.
* `bottomHead_eq` cuts the program of the head after the first ceremony, `bottomCut_split` is the law
  of the head, and `headPhase_support` gives the support of the search as a phase with no round.
* `gameSeeds_congr` and `gameParameter_congr` state that the seeds and the parameter of the game read
  the keys of the honest operators only.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

/-! ## The round count of the first part of a program -/

section Timed

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

theorem timed_local_inv {α : Type} {n : ℕ} {q : (LocalSpec C).Domain}
    {k : (LocalSpec C).Range q → OracleComp (PartySpec C E G) (Option α)}
    (h : Timed n (.liftBind (.inl (.inl q)) k)) : ∀ r, Timed n (k r) := by
  cases h with
  | queryLocal _ _ _ h => exact h

theorem timed_round_inv {α : Type} {n : ℕ} {out : Mail C E}
    {k : Mail C E → OracleComp (PartySpec C E G) (Option α)}
    (h : Timed n (.liftBind (.inl (.inr out)) k)) : ∃ m, n = m + 1 ∧ ∀ r, Timed m (k r) := by
  cases h with
  | round m _ _ h => exact ⟨m, rfl, h⟩

theorem timed_call_inv {α : Type} {n : ℕ} {input : ι}
    {k : G input → OracleComp (PartySpec C E G) (Option α)}
    (h : Timed n (.liftBind (.inr input) k)) : ∃ m, n = m + 1 ∧ ∀ r, Timed m (k r) := by
  cases h with
  | call m _ _ h => exact ⟨m, rfl, h⟩

/-- A program that can end with a result at once takes no round on each timed count. -/
theorem timed_zero_of_done {α : Type} {n : ℕ} {p : PartyM C E G α} (x : α)
    (hx : Step.done (some x) ∈ support (advance p.run)) (h : Timed n p.run) : n = 0 :=
  timed_advance h _ hx

/-- The round count of a sequence is the round count of its first part when each continuation can
end with a result in no round. -/
theorem timed_of_bind {α β : Type} {m n : ℕ} {p : PartyM C E G α} {k : α → PartyM C E G β}
    (hp : Timed m p.run) (hk : ∀ a, ∃ x, Step.done (some x) ∈ support (advance (k a).run))
    (h : Timed n (p >>= k).run) : Timed n p.run := by
  simp only [OptionT.run_bind, Option.elimM] at h
  change Timed n (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run)) at h
  generalize p.run = oa at hp h ⊢
  induction hp generalizing n with
  | abort m => exact Timed.abort n
  | done a =>
    obtain ⟨x, hx⟩ := hk a
    simp only [pure_bind, Option.elim_some] at h
    rw [timed_zero_of_done x hx h]
    exact Timed.done a
  | queryLocal m q f _ ih =>
    exact Timed.queryLocal n q f fun r => ih r (timed_local_inv h r)
  | round m out f _ ih =>
    obtain ⟨n', rfl, h'⟩ := timed_round_inv h
    exact Timed.round n' out f fun r => ih r (h' r)
  | call m input f _ ih =>
    obtain ⟨n', rfl, h'⟩ := timed_call_inv h
    exact Timed.call n' input f fun r => ih r (h' r)

end Timed

/-! ## A search that ends -/

/-- Some answer of `H` truncates to a digest that is a codeword. -/
theorem exists_decode_truncate : ∃ (v : HashOutput) (e : Encoding), Codeword.decode (truncateHash v) = some e := by
  obtain ⟨d, hd⟩ := XmssSecurity.TargetSum.validDigests_nonempty
  obtain ⟨e, he⟩ := (Finset.mem_filter.1 hd).2
  refine ⟨d.setWidth 256, e, ?_⟩
  have htr : truncateHash (d.setWidth 256) = d := by
    unfold truncateHash
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hk' : k < 128 := by simpa only [digestBits] using hk
    simp [show k < 256 by omega, show k < digestBits from hk]
    rfl
  rw [htr, XmssSecurity.Bridge.decode_eq]
  exact he

variable {C : Committee}

/-- The randomizer search with at least one attempt can end with a randomizer, for some answers of
`H`. -/
theorem exists_some_grind (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomizer) (n trial : ℕ) (hn : n ≠ 0) :
    ∃ y, some y ∈ support (tweakable (C := C) (grind parameter lay key message base n trial)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨v, e, he⟩ := exists_decode_truncate
  refine ⟨(base + BitVec.ofNat digestBits trial, e), ?_⟩
  rw [grind, tweakable_bind, mem_support_bind_iff]
  refine ⟨truncateHash v, ?_, ?_⟩
  · simp [Verification.messageDigestWithHash, Verification.thWithHash, Verification.oracleHashWithHash, tweakable,
      hashQuery]
  · rw [he, tweakable_pure, support_pure]
    rfl

/-! ## A computation of `Th` in the stream world -/

/-- Two hash caches agree at each cell that is not an input of `Th`. -/
def SameOffHash (c c' : HashCache C) : Prop := ∀ q, (∀ x, q ≠ .hash x) → c' q = c q

theorem SameOffHash.refl (c : HashCache C) : SameOffHash c c := fun _ _ => rfl

theorem SameOffHash.trans {c c' c'' : HashCache C} (h : SameOffHash c c') (h' : SameOffHash c' c'') :
    SameOffHash c c'' := fun q hq => (h' q hq).trans (h q hq)

/-- The world moves only at inputs of `Th`. The hidden cache stays, the hash cache grows and
agrees with the old cache at each other cell. -/
def HashStep (w w' : StreamState C) : Prop := w'.2 = w.2 ∧ SameOffHash w.1 w'.1 ∧ w.1 ≤ w'.1

theorem HashStep.refl (w : StreamState C) : HashStep w w := ⟨rfl, SameOffHash.refl _, le_rfl⟩

theorem HashStep.trans {w w' w'' : StreamState C} (h : HashStep w w') (h' : HashStep w' w'') : HashStep w w'' :=
  ⟨h'.1.trans h.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- A call of `H` on an input of `Th` writes no other cell. -/
theorem hashAnswer_sameOffHash (prims : Primitives) (x : HashInput) (c : HashCache C) (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims (.hash x)).run c)) : SameOffHash c p.2 := by
  by_cases hq : IsFixed (Query.hash (C := C) x)
  · obtain ⟨input, hin, hm⟩ := hq
    cases hin
    rw [hashAnswer_of_isFixed prims hm] at hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact SameOffHash.refl c
  · rw [hashAnswer_of_not_isFixed prims hq] at hp
    intro q hne
    rcases hs : c (.hash x) with _ | u
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs] at hp
      erw [support_map, Set.mem_image] at hp
      obtain ⟨u, _, rfl⟩ := hp
      exact QueryCache.cacheQuery_of_ne _ _ (hne x)
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs] at hp
      simp at hp
      subst hp
      rfl

/-- A computation of `Th` on the free copy keeps the hidden cache, writes only inputs of `Th`, grows
the hash cache, and gives its answer again from each world with a larger hash cache. -/
theorem freeRun_tweakable (prims : Primitives) (D : C.Coalition) {α : Type} (oa : OracleComp HashSpec α) :
    ∀ w, ∀ z ∈ support (Ready.freeRun prims D (tweakable oa) w),
      z.2.2 = w.2 ∧ SameOffHash w.1 z.2.1 ∧ w.1 ≤ z.2.1 ∧
        ∀ w' : StreamState C, z.2.1 ≤ w'.1 → ∀ z' ∈ support (Ready.freeRun prims D (tweakable oa) w'),
          z' = (z.1, w') := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro w z hz
    have hpure : ∀ w', Ready.freeRun prims D (tweakable (C := C) (pure a)) w' = pure (a, w') := fun w' => by
      simp [tweakable_pure, Ready.freeRun]
    rw [hpure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨rfl, SameOffHash.refl _, le_rfl, fun w' _ z' hz' => ?_⟩
    rwa [hpure, support_pure, Set.mem_singleton_iff] at hz'
  | query_bind t k ih =>
    intro w z hz
    have hstep : ∀ w', Ready.freeRun prims D (tweakable (C := C) (liftM (OracleSpec.query t) >>= k)) w' =
        (onHash (hashAnswer prims (.hash t))).run w' >>= fun y => Ready.freeRun prims D (tweakable (k y.1)) y.2 :=
      fun w' => by
      have hq : tweakable (C := C) (liftM (OracleSpec.query t) : OracleComp HashSpec _) = hashQuery (.hash t) := by
        simp [tweakable, hashQuery]
      rw [tweakable_bind, Ready.freeRun_bind, hq, hashQuery, Ready.freeRun_query]
      rfl
    rw [hstep, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ _ _ hy
    obtain ⟨h1, h2, h3, h4⟩ := ih r.1 (r.2, w.2) z hz
    refine ⟨h1, (hashAnswer_sameOffHash prims t w.1 r hr).trans h2,
      (hashAnswer_support _ w.1 r hr).1.trans h3, fun w' hle z' hz' => ?_⟩
    rw [hstep, mem_support_bind_iff] at hz'
    obtain ⟨y', hy', hz'⟩ := hz'
    obtain ⟨r', hr', rfl⟩ := mem_support_onHash _ _ _ hy'
    rw [Ready.hashAnswer_replay prims _ w.1 r hr w'.1 (h3.trans hle), support_pure,
      Set.mem_singleton_iff] at hr'
    subst hr'
    exact h4 w' hle z' hz'

/-! ## The facts of a world that the search does not change -/

section Facts

variable (prims : Primitives)

theorem splitRegionCache_sameOffHash {P : Query C → Prop} (hP : ∀ x, ¬ P (.hash x)) {c c' : HashCache C}
    (h : SameOffHash c c') : splitRegionCache P c' = splitRegionCache P c := by
  refine QueryCache.ext fun q => ?_
  by_cases hq : P q
  · simp only [splitRegionCache, QueryCache.ofFn, hq, ↓reduceIte]
    exact h q fun x hx => hP x (hx ▸ hq)
  · simp [splitRegionCache, QueryCache.ofFn, hq]

/-- The global events read no input of `Th`. -/
theorem globalEvent_hashStep {w w' : StreamState C} (h : HashStep w w') : GlobalEvent w' ↔ GlobalEvent w := by
  simp only [GlobalEvent, DomainCollision]
  rw [splitRegionCache_sameOffHash (fun _ h => h) h.2.1, splitRegionCache_sameOffHash (fun _ h => h) h.2.1,
    splitRegionCache_sameOffHash (fun _ h => h) h.2.1, splitRegionCache_sameOffHash (fun _ h => h) h.2.1]

/-- The ledger reads no input of `Th`. -/
theorem ledgerFits_hashStep {ℓ : StartBudget} {w w' : StreamState C} (h : HashStep w w') (hw : LedgerFits ℓ w) :
    LedgerFits ℓ w' := by
  obtain ⟨hsplit, ⟨seen, keys, hsound, hseen, hkeys⟩, ⟨salts, hsalts, hcard⟩, hhidden⟩ := hw
  have hc := h.2.1
  refine ⟨?_, ⟨seen, keys, ⟨fun tag label bits hL hq => ?_, fun key idx hq => ?_⟩, hseen, hkeys⟩,
    ⟨salts, fun salt hd hq => ?_, hcard⟩, ?_⟩
  · rw [splitRegionCache_sameOffHash (fun _ h => h) hc]
    exact hsplit
  · exact hsound.1 tag label bits hL (by rwa [← hc _ fun x => by simp])
  · exact hsound.2 key idx (by rwa [← hc _ fun x => by simp])
  · exact hsalts salt hd (by rwa [← hc _ fun x => by simp])
  · rw [h.1]
    exact hhidden

/-- The provenance of the hidden keys reads no input of `Th`. -/
theorem hiddenProvenance_hashStep {D : C.Coalition} {w w' : StreamState C} (h : HashStep w w')
    (hw : HiddenProvenance D w) : HiddenProvenance D w' := by
  intro name key ρ idx position hname hcell
  rw [h.1] at hcell
  obtain ⟨kind, parts, hd⟩ := hw name key ρ idx position hname hcell
  exact ⟨kind, parts, by rw [h.2.1 _ fun x => by simp]; exact hd⟩

/-- A job in the clear reads only cells of the PRF. -/
theorem evalJob_sameOffHash (circuits : Circuits) {c c' : HashCache C} (h : SameOffHash c c')
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (job : Job) :
    D prims (hashOf prims c') (evalJob circuits parameter seeds job) =
      D prims (hashOf prims c) (evalJob circuits parameter seeds job) := by
  simp only [evalJob, prfValue, prf, D_bind, D_mapM, D_pure, D_map, D_hashQuery]
  congr 3
  funext x
  congr 2
  funext T
  simp only [hashOf]
  rw [h _ fun y => by simp]

/-- Wrong outputs read no input of `Th`. -/
theorem wrongOutputs_sameOffHash (circuits : Circuits) (D' : C.Coalition) (keys : C.Party → Option (Keys C))
    (jobs : List Job) {c c' : HashCache C} (h : SameOffHash c c') (outputs : List (List Bit)) :
    WrongOutputs prims circuits D' keys jobs c' outputs ↔ WrongOutputs prims circuits D' keys jobs c outputs := by
  unfold WrongOutputs
  rw [evalRun_eq, evalRun_eq]
  simp only [evalJob_sameOffHash prims circuits h]

end Facts

/-! ## The head as the first ceremony and the search -/

section Head

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The local search of the head of bottom tree `b` after a first ceremony with the outputs
`outputs`. It gives the root of the bottom tree, the randomizer and the encoding. -/
def headSearchHash (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) :
    OracleComp HashSpec (Option (Digest × Randomizer × Encoding)) := do
  let root ← merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val
  let base ← truncateHash <$> Verification.oracleHashWithHash
    (randomizerInput parameter topLayer (topKey b) (bRho b outputs) (littleEndianBytes 16 root))
  let g ← grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base randomizerAttemptLimit 0
  pure (g.map fun g => (root, g.1, g.2))

/-- The search of the head at one operator after the result `o` of the first ceremony. -/
def headSearch (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (o : CeremonyResult) :
    PartyM C E RealSpec HeadResult :=
  oracleStep (tweakable (headSearchHash parameter b o.1)) >>= fun g => g.elim failure fun y => pure ((o.1, y), o.2)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The search of the head can end with a result in no round. -/
theorem headSearch_done (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (o : CeremonyResult) :
    ∃ x, Step.done (some x) ∈ support (advance (headSearch (C := C) (E := E) parameter b o).run) := by
  obtain ⟨y, hy⟩ : ∃ y, some y ∈ support (tweakable (C := C) (headSearchHash parameter b o.1)) := by
    simp -implicitDefEqProofs only [headSearchHash, tweakable_bind, tweakable_pure]
    obtain ⟨root, hroot⟩ := OracleComp.support_nonempty (tweakable (C := C)
      (merkleNode parameter bottomLayer (fun e l => (bCpk b o.1 e l).2.2) layerHeight b.val))
    obtain ⟨base, hbase⟩ := OracleComp.support_nonempty (tweakable (C := C) (truncateHash <$>
      Verification.oracleHashWithHash
        (randomizerInput parameter topLayer (topKey b) (bRho b o.1) (littleEndianBytes 16 root))))
    obtain ⟨g, hg⟩ := exists_some_grind (C := C) parameter topLayer (topKey b) (littleEndianBytes 16 root) base
      randomizerAttemptLimit 0 (by unfold randomizerAttemptLimit; positivity)
    refine ⟨(root, g.1, g.2), ?_⟩
    simp only [mem_support_bind_iff]
    refine ⟨root, hroot, base, hbase, some g, hg, ?_⟩
    rw [support_pure]
    rfl
  refine ⟨((o.1, y), o.2), ?_⟩
  rw [headSearch, advance_oracleStep_bind, mem_support_bind_iff]
  refine ⟨some y, by rwa [support_liftComp], ?_⟩
  show _ ∈ support (advance (pure _))
  rw [advance_pure, support_pure]
  rfl

/-- The parameter of the keys of operator `i`. -/
def headParameter {σ : Type} (s : RealState C σ) (i : C.Party) : PublicParameter :=
  ((s.operators i).keys.map (·.parameter)).getD 0

omit [Fintype E] [DecidableEq E] in
/-- The program of the head is the program of the first ceremony and then the search. -/
theorem bottomHead_eq (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ) (i : C.Party) :
    CheckTiming.bottomHead K circuits settings i (s.operators i) b =
      ceremonyProgram K circuits settings i (firstStart b s) >>= headSearch (headParameter s i) b := by
  unfold CheckTiming.bottomHead ceremonyProgram firstStart aliveKeys headParameter
  rcases hk : (s.operators i).keys with _ | keys <;> rcases ht : (s.operators i).top with _ | top <;>
    simp only [hk, ht, failure_bind]
  simp only [CheckTiming.firstPart, StateT.run_bind, bind_assoc, Option.map_some, Option.getD_some]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | outputs, counters⟩
  · simp only [Option.elim, StateT.run_pure, pure_bind, failure_bind]
  simp -implicitDefEqProofs only [headSearch, headSearchHash, tweakable_bind, tweakable_pure, oracleStep_bind,
    oracleStep_pure, bind_assoc, StateT.run_bind, StateT.run_lift, pure_bind, Option.elim_some]
  refine bind_congr fun root => bind_congr fun base => bind_congr fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · simp -implicitDefEqProofs only [StateT.run_pure, pure_bind, Option.map_none, Option.elim]
  · simp -implicitDefEqProofs only [StateT.run_pure, pure_bind, Option.map_some, Option.elim]

omit [DecidableEq E] in
/-- The program of one ceremony has a round count. -/
theorem exists_timed_ceremonyProgram (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    ∃ m, Timed m (ceremonyProgram K circuits settings i c).run := by
  unfold ceremonyProgram
  split
  · rename_i keys _
    refine ⟨setupRounds + Fuel.batchesRounds circuits settings keys.parameter c.jobs + 0, ?_⟩
    refine (Fuel.runTimed_ceremonyRun K circuits settings i keys c.jobs c.counters).bind fun p => ?_
    rcases p with ⟨_ | outputs, st⟩
    · exact timed_failure 0
    · exact timed_pure _
  · exact ⟨0, timed_failure 0⟩

omit [DecidableEq E] in
/-- The round count of the head at an operator is the round count of its first ceremony. -/
theorem timed_ceremonyProgram_of_head (b : Fin (2 ^ layerHeight)) {σ : Type} (s : RealState C σ) (i : C.Party)
    (n : ℕ) (h : Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run) :
    Timed n (ceremonyProgram K circuits settings i (firstStart b s)).run := by
  obtain ⟨m, hm⟩ := exists_timed_ceremonyProgram K circuits settings i (firstStart b s)
  rw [bottomHead_eq] at h
  exact timed_of_bind hm (headSearch_done (headParameter s i) b) h

/-- The search of the head as a phase with no round, after the results `heads` of the first
ceremony. An operator with no result is not alive. -/
def headPhase (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (st : net.State) (heads : C.Party → Option CeremonyResult) :
    StateT (StreamState C) ProbComp (net.State × (C.Party → Option HeadResult)) :=
  simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality 0 st fun i =>
    (heads i).elim failure (headSearch (headParameter s i) b))

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The local work of the search of one operator in the stream world. -/
theorem headStep_support (D : C.Coalition) (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (head : Option CeremonyResult) (w : StreamState C) (y : Step C E RealSpec HeadResult × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D)
      (free (advance (head.elim failure (headSearch parameter b)).run))).run w)) :
    HashStep w y.2 ∧ (head = none → y.1 = .done none) ∧
      ∀ o, head = some o → ∃ g, y.1 = .done (g.map fun v => ((o.1, v), o.2)) ∧
        ∀ w' : StreamState C, y.2.1 ≤ w'.1 →
          ∀ z' ∈ support (Ready.freeRun prims D (tweakable (headSearchHash parameter b o.1)) w'), z'.1 = g := by
  rcases head with _ | o
  · simp only [Option.elim, advance_run_failure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨HashStep.refl w, fun _ => rfl, fun o h => absurd h (by simp)⟩
  · have hk : (fun g : Option (Digest × Randomizer × Encoding) =>
        advance ((g.elim failure fun v => pure ((o.1, v), o.2)) : PartyM C E RealSpec HeadResult).run) =
        fun g => pure (.done (g.map fun v => ((o.1, v), o.2))) := by
      funext g
      rcases g with _ | v <;> rfl
    simp only [Option.elim] at hy
    rw [headSearch, advance_oracleStep_bind, hk, free_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    simp only [free_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨h1, h2, h3, h4⟩ := freeRun_tweakable prims D (headSearchHash parameter b o.1) w p hp
    refine ⟨⟨h1, h2, h3⟩, fun h => absurd h (by simp), fun o' ho => ?_⟩
    cases ho
    exact ⟨p.1, rfl, fun w' hle z' hz' => by rw [h4 w' hle z' hz']⟩

/-- Each computation of a sequence in `streamWorld` moves the world by a reflexive and transitive
relation. Then the sequence moves the world by it. -/
theorem sequenceFin_streamWorld_rel (D : C.Coalition) {β : Type} (R : StreamState C → StreamState C → Prop)
    (hrefl : ∀ w, R w w) (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) β),
      (∀ i s y, y ∈ support ((simulateQ (streamWorld prims D) (f i)).run s) → R s y.2) →
      ∀ s z, z ∈ support ((simulateQ (streamWorld prims D) (OverPermutation.sequenceFin f)).run s) → R s z.2
  | 0, _, _, s, z, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact hrefl s
  | n + 1, f, hf, s, z, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, v, hv, rfl⟩ := hz
    exact htrans _ _ _ (hf 0 s y hy)
      (sequenceFin_streamWorld_rel D R hrefl htrans (fun i => f i.succ) (fun i => hf i.succ) y.2 v hv)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The support of the search as a phase with no round. The state of the adversary stays, the world
moves only at inputs of `Th`, an honest result keeps the outputs and the counters of the first
ceremony, and two honest operators with one result of the first ceremony and one parameter end with
one head result. -/
theorem headPhase_support (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (st : net.State) (heads : C.Party → Option CeremonyResult) (w : StreamState C) :
    ∀ z ∈ support ((headPhase prims D net b s st heads).run w),
      z.1.1 = st ∧ HashStep w z.2 ∧
        (∀ i, i ∉ D.1 → ∀ x, z.1.2 i = some x → ∃ o, heads i = some o ∧ x.1.1 = o.1 ∧ x.2 = o.2) ∧
        (∀ i j, i ∉ D.1 → j ∉ D.1 → heads i = heads j → headParameter s i = headParameter s j →
          z.1.2 i = z.1.2 j) := by
  intro z hz
  unfold headPhase executePhase at hz
  simp only [executeRounds, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  unfold startSteps at ha
  have hrel := sequenceFin_streamWorld_rel prims D HashStep HashStep.refl (fun _ _ _ => HashStep.trans) _
    (fun i s' y hy => by
      split_ifs at hy
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact HashStep.refl s'
      · exact (headStep_support prims D (headParameter s i) b (heads i) s' y hy).1) w a ha
  have hQ := sequenceFin_streamWorld prims D (fun i (v : Step C E RealSpec HeadResult) c =>
      i ∉ D.1 → (heads i = none → v = .done none) ∧
      ∀ o, heads i = some o → ∃ g : Option (Digest × Randomizer × Encoding),
        v = .done (g.map fun v => ((o.1, v), o.2)) ∧ ∀ w' : StreamState C, c ≤ w'.1 →
          ∀ z' ∈ support (Ready.freeRun prims D (tweakable (headSearchHash (headParameter s i) b o.1)) w'),
            z'.1 = g) _
    (fun i v c c' h hle hi => ⟨(h hi).1, fun o ho => by
      obtain ⟨g, hg, hrep⟩ := (h hi).2 o ho
      exact ⟨g, hg, fun w' hw' => hrep w' (hle.trans hw')⟩⟩)
    (fun i s' y hy hi => by
      simp only [hi, ↓reduceIte] at hy
      have h := headStep_support prims D (headParameter s i) b (heads i) s' y hy
      exact ⟨h.2.1, h.2.2⟩) w a ha
  refine ⟨rfl, hrel, fun i hi x hx => ?_, fun i j hi hj hij hpar => ?_⟩
  · change (a.1 i).output = some x at hx
    obtain ⟨hnone, hsome⟩ := hQ i hi
    rcases hh : heads i with _ | o
    · rw [hnone hh] at hx
      exact absurd hx (by simp [Step.output])
    · obtain ⟨g, hg, -⟩ := hsome o hh
      rw [hg] at hx
      simp only [Step.output, Option.map_eq_some_iff] at hx
      obtain ⟨v, -, rfl⟩ := hx
      exact ⟨o, rfl, rfl, rfl⟩
  · change (a.1 i).output = (a.1 j).output
    obtain ⟨hni, hsi⟩ := hQ i hi
    obtain ⟨hnj, hsj⟩ := hQ j hj
    rcases hh : heads i with _ | o
    · rw [hni hh, hnj (hij ▸ hh)]
    · obtain ⟨gi, hgi, hri⟩ := hsi o hh
      obtain ⟨gj, hgj, hrj⟩ := hsj o (hij ▸ hh)
      obtain ⟨z', hz'⟩ := OracleComp.support_nonempty
        (Ready.freeRun prims D (tweakable (headSearchHash (headParameter s i) b o.1)) a.2)
      have e1 := hri a.2 le_rfl z' hz'
      have e2 := hrj a.2 le_rfl z' (hpar ▸ hz')
      rw [hgi, hgj, ← e1, ← e2]

omit [DecidableEq E] in
/-- The law of the head. The head of a bottom tree has the law of its first ceremony and then the
search as a phase with no round. -/
theorem bottomCut_split (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (world : StreamState C) (n : ℕ)
    (htimed : ∀ i ∉ D.1, Timed n (CheckTiming.bottomHead K circuits settings i (s.operators i) b).run) :
    (bottomCut prims K circuits settings D net b s n).run world =ᵈ
      ((ceremonyPhase prims K circuits settings D net n (firstStart b s)).run world >>= fun r =>
        (headPhase prims D net b s r.1.1 r.1.2).run r.2) := by
  unfold bottomCut ceremonyPhase headPhase
  rw [show (fun i => CheckTiming.bottomHead K circuits settings i (s.operators i) b) =
      fun i => ceremonyProgram K circuits settings i (firstStart b s) >>= headSearch (headParameter s i) b from
    funext fun i => bottomHead_eq K circuits settings b s i, ← Nat.add_zero n]
  have h := WorldSplit.executePhase_split prims D net n 0 s.adversary
    (fun i => ceremonyProgram K circuits settings i (firstStart b s)) (fun i => headSearch (headParameter s i) b)
    (fun i hi => timed_ceremonyProgram_of_head K circuits settings b s i n (htimed i hi)) world
  simp only [simulateQ_bind, StateT.run_bind] at h ⊢
  exact h

end Head

/-! ## The game reads the honest keys only -/

section Congr

variable {C : Committee}

/-- The seeds of the game read the keys of the honest operators only. -/
theorem gameSeeds_congr (D : C.Coalition) {keys keys' : C.Party → Option (Keys C)}
    (h : ∀ i, i ∉ D.1 → keys i = keys' i) : gameSeeds D keys = gameSeeds D keys' := by
  funext T
  unfold gameSeeds
  have hp : (fun i => decide (i ∈ C.holders T ∧ i ∉ D.1 ∧ (keys i).isSome = true)) =
      fun i => decide (i ∈ C.holders T ∧ i ∉ D.1 ∧ (keys' i).isSome = true) := funext fun i => by
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp [hi, h i hi]
  rw [hp]
  split
  · rename_i i hf
    have hi := List.find?_some hf
    simp only [decide_eq_true_eq] at hi
    rw [h i hi.2.1]
  · rfl

/-- The parameter of the game reads the keys of the honest operators only. -/
theorem gameParameter_congr (D : C.Coalition) {keys keys' : C.Party → Option (Keys C)}
    (h : ∀ i, i ∉ D.1 → keys i = keys' i) : gameParameter D keys = gameParameter D keys' := by
  unfold gameParameter
  have hp : (fun i => decide (i ∉ D.1 ∧ (keys i).isSome = true)) =
      fun i => decide (i ∉ D.1 ∧ (keys' i).isSome = true) := funext fun i => by
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp [hi, h i hi]
  rw [hp]
  split
  · rename_i i hf
    have hi := List.find?_some hf
    simp only [decide_eq_true_eq] at hi
    rw [h i hi.1]
  · rfl

end Congr

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.bottomCut_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.bottomCut_split

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.headPhase_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.headPhase_support
