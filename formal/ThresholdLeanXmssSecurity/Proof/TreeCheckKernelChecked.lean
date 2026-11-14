import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetCoin
import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetMaskPrefix
import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupled

/-! # The check kernel with its original batch continuation

`coupled_check` couples the supported live checkpoint's actual batch programs
with the fixed hybrid check. It composes the retained-table gadget couplings,
the common hash and exchange segments, and the two GS20 folds. The real side
retains the batch output opening and caller continuation at `2 * halvings + 5`
rounds; the hybrid uses its original `2 * halvings + 8` fuel. Context, tuple,
count and state agreement come from the same checkpoint and live witness.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section

namespace ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-! ## Start state, pair keys and round transitions

The declarations of this part are in the namespace `TreeCheckKernelCoupling`, and the module doc of
`TreeCheckKernelCoupling` describes them. -/

open TreeCheckWalkCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

section Coherent

variable (prims : Primitives) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One world call grows the hash cache and caches a random-oracle answer that it logs. -/
theorem stream_query_coherent (P : Query C → Prop) (hP : ∀ q, P q → ¬ IsFixed q)
    (t : (WorldSpec C).Domain) (s : HashCache C × HiddenCache C)
    (u : (WorldSpec C).Range t) (next : HashCache C × HiddenCache C)
    (hr : (u, next) ∈ support ((streamWorld prims D t).run s)) :
    s.1 ≤ next.1 ∧ TreeSimHashRegionCoherent P next.1 [⟨t, u⟩] := by
  refine ⟨?_, ?_⟩
  · apply treeSim_stream_grows prims D (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) t)) s (u, next)
    simpa only [simulateQ_spec_query] using hr
  · intro q h hq ha
    simp only [TreeSimHashAnswer, List.mem_singleton] at ha
    rcases ha with he | he <;> cases he
    all_goals
      simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨v, hv, he⟩ := hr
      cases he
      exact hashAnswer_cached prims (hP _ hq) s.1 v hv

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A logged run keeps every logged random-oracle answer of a region in its hash cache. -/
theorem logged_coherent (P : Query C → Prop) (hP : ∀ q, P q → ¬ IsFixed q)
    {α : Type} (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (hc : TreeSimHashRegionCoherent P s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    TreeSimHashRegionCoherent P r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    apply ih mid.1 mid.2 r _ hr
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hmid
    obtain ⟨⟨u, next⟩, hu, rfl⟩ := hmid
    have hs := stream_query_coherent prims D P hP t s.1 u next hu
    exact (hc.mono hs.1).append hs.2

end Coherent

section SetupPairs

variable (prims : Primitives) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each answer of a pair-key traversal is logged for its own derivation input. -/
theorem pairs_logged (i : C.Party) (q : ∀ j : C.Party, i ≠ j → Query C) (xs : List C.Party)
    (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (xs.mapM fun j => if h : j = i then pure 0 else hashQuery (q j (Ne.symm h)))
        (LocalSpec C)))).run s)) :
    List.Forall₂ (fun j h => ∀ ne : i ≠ j, TreeSimHashAnswer r.2.2 (q j ne) h) xs r.1 := by
  induction xs generalizing s r with
  | nil =>
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact .nil
  | cons j xs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hr
    refine .cons ?_ (ih a.2 b hb)
    intro ne
    have hji : ¬ j = i := fun he => ne he.symm
    simp only [dif_neg hji] at ha
    exact (treeSetup_hash_logged prims D (q j ne) s a ha).imp
      (fun h => (treeSimLoggedWorld_prefix prims D _ a.2 b hb).subset h)
      (fun h => (treeSimLoggedWorld_prefix prims D _ a.2 b hb).subset h)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A successful reveal row has no abort frame, and its pair key with each `j`
is a logged answer for the input derived from its view of the parts. -/
theorem revealData_pairs (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (s : TreeSimState C) (r : Option (PrssKeys C × List HashOutput) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealData i own committed revealed))).run s)) :
    ∀ row, r.1 = some row → (C.parties.any fun k => Msg.isAbort (revealed k)) = false ∧
      ∀ j (ne : i ≠ j), TreeSimHashAnswer r.2.2
        (pairQuery (fun k => if k = i then own else readReveal .prss (Msg.hashesOf (revealed k)) i k)
          (C.pairOf i j ne)) (row.1.pair j) := by
  unfold prssRevealData at hr
  split_ifs at hr with ha
  · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    intro row he
    cases he
  · unfold prssPostRevealData at hr
    simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨opens, _, hr⟩ := hr
    split_ifs at hr with hc
    · simp only [free_bind, free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨keys, hkeys, shared, hshared, rfl⟩ := hr
      intro row he
      cases he
      refine ⟨by simpa using ha, ?_⟩
      intro j ne
      unfold deriveKeys at hkeys
      simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff,
        reduceCtorEq, if_false] at hkeys
      obtain ⟨param, hparam, term, hterm, pair, hpair, rfl⟩ := hkeys
      have hall := pairs_logged prims D i
        (fun j ne => pairQuery (fun k => if k = i then own else
          readReveal .prss (Msg.hashesOf (revealed k)) i k) (C.pairOf i j ne))
        C.parties term.2 pair hpair
      have hj := forall₂_getD_idxOf _ _ _ hall j (by simp [Committee.parties]) 0 ne
      have later := treeSimLoggedWorld_prefix prims D _ pair.2 shared hshared
      have hj' : TreeSimHashAnswer shared.2.2
          (pairQuery (fun k => if k = i then own else
            readReveal .prss (Msg.hashesOf (revealed k)) i k) (C.pairOf i j ne))
          (pair.1.getD (C.parties.idxOf j) 0) :=
        hj.imp (fun h => later.subset h) (fun h => later.subset h)
      simpa [Committee.parties] using hj'
    · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      intro row he
      cases he

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- In the joint reveal traversal, each successful row is honest, and its pair
key with every honest `j` answers the input derived from the actual parts. -/
theorem revealRows_pairs (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : TreeSimState C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent))).run s)) :
    ∀ i row, r.1 i = some row → i ∉ D.1 ∧ ∀ j, j ∉ D.1 → ∀ ne : i ≠ j,
      TreeSimHashAnswer r.2.2 (pairQuery parts (C.pairOf i j ne)) (row.1.pair j) := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [prssRevealRows, free_sequenceFin, simulateQ_sequenceFin] at hr
  apply (sequenceFin_state_post _
    (fun i out cache => ∀ row, out = some row → i ∉ D.1 ∧ ∀ j, j ∉ D.1 → ∀ ne : i ≠ j,
      TreeSimHashAnswer cache.2 (pairQuery parts (C.pairOf i j ne)) (row.1.pair j)) ?_ ?_ s r hr).2
  · intro i cache result hresult
    refine ⟨(treeSimLoggedWorld_prefix prims D _ cache result hresult).subset, ?_⟩
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hresult
      subst result
      intro row he
      cases he
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        intro row he
        obtain ⟨clean, answers⟩ := revealData_pairs prims D i (parts i) (committed i) _ cache result
          hresult row he
        refine ⟨hi, fun j hj ne => ?_⟩
        have activeJ : active j := by
          by_contra inactive
          have abort : Msg.isAbort (prssRevealInbox D active parts sent i j) = true := by
            simp [prssRevealInbox, hj, inactive, Msg.isAbort]
          have any : (C.parties.any fun k => Msg.isAbort (prssRevealInbox D active parts sent i k)) = true :=
            List.any_eq_true.mpr ⟨j, by simp [Committee.parties], abort⟩
          rw [any] at clean
          cases clean
        have inbox : prssRevealInbox D active parts sent i j =
            some (Msg.hashes (revealTo .prss (parts j) j i)) := by
          simp [prssRevealInbox, hj, activeJ, prssRevealOutbox, ne]
        rw [← pairQuery_congr (fun k => if k = i then parts i else
            readReveal .prss (Msg.hashesOf (prssRevealInbox D active parts sent i k)) i k) parts i j ne
          (by simp)
          (by simp only [if_neg (Ne.symm ne), inbox, readReveal_pair])]
        exact answers j ne
      · simp only [if_neg hi, if_neg ha, free_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hresult
        subst result
        intro row he
        cases he
  · intro i out cache next hle h row he
    exact ⟨(h row he).1, fun j hj ne => ((h row he).2 j hj ne).imp (fun x => hle x) (fun x => hle x)⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Two honest operators that finish the PRSS setup hold the same key for
their pair. Their reveals reach each other unchanged, so both derive it from
the same input of `H`. No collision premise is needed. -/
theorem setup_pair_agree (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (i j : C.Party) (ne : i ≠ j) (ki kj : PrssKeys C)
    (hi : p.1.2 i = some ki) (hj : p.1.2 j = some kj) :
    ki.pair j = kj.pair i := by
  have coherent : TreeSimHashRegionCoherent (fun q => ¬ IsFixed q) p.2.1.1 p.2.2 := by
    have whole := hp
    simp only [treeSaltSetup, mem_support_bind_iff] at whole
    obtain ⟨start, hstart, phase⟩ := whole
    have first := logged_coherent prims D (fun q => ¬ IsFixed q) (fun _ h => h) _ ((∅, ∅), []) start
      (fun _ _ _ ha => by simp [TreeSimHashAnswer] at ha) hstart
    rw [treeSimRealRoles, ← simulateQ_executePhase] at phase
    exact logged_coherent prims D (fun q => ¬ IsFixed q) (fun _ h => h) _ start.2 p first phase
  simp only [treeSaltSetup, mem_support_bind_iff] at hp
  obtain ⟨start, _, hp⟩ := hp
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  change p ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) start.1
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run start.2) at hp
  rw [executePhase_prssSetup_prefix] at hp
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨data, _, adv, _, hp⟩ := hp
  split_ifs at hp with habort
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hp
    subst p
    cases hi
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
    obtain ⟨adv', _, rows, hrows, hp⟩ := hp
    obtain ⟨⟨si, rowI⟩, before⟩ := finish_row prims D A _ rows.1 rows.2 p hp i ki hi
    obtain ⟨⟨sj, rowJ⟩, _⟩ := finish_row prims D A _ rows.1 rows.2 p hp j kj hj
    have pairs := revealRows_pairs prims D _ _ _ _ adv'.2 rows hrows
    obtain ⟨honestI, answerI⟩ := pairs i (ki, si) rowI
    obtain ⟨honestJ, answerJ⟩ := pairs j (kj, sj) rowJ
    have left := answerI j honestJ ne
    have right := answerJ i honestI (Ne.symm ne)
    rw [← pairOf_comm i j ne] at right
    have notFixed : ∀ parts : C.Party → Parts C, ¬ IsFixed (pairQuery parts (C.pairOf i j ne)) := by
      rintro _ ⟨_, h, _⟩
      cases h
    have cachedI := coherent _ _ (notFixed _) (left.imp (fun h => before.subset h) (fun h => before.subset h))
    have cachedJ := coherent _ _ (notFixed _) (right.imp (fun h => before.subset h) (fun h => before.subset h))
    exact Option.some.inj (cachedI.symm.trans cachedJ)

end SetupPairs

/-- Each honest checkpoint row starts the check at the hybrid's tuples,
filled history, label and tag. -/
def RowsAligned (K : Constants C E) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (o : TreeCheckTailCheckpoint A) (h : TreeCheckHybrid C E) : Prop :=
  ∀ i, i ∉ D.1 → ∃ data, o.1.2 i = some data ∧ data.2.1.2 = h.tuples i ∧
    data.2.2.history = filledHistory K i (h.tuples i) ∧ data.2.2.label = h.label ∧
    data.2.2.tag = h.tag

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- At every live checkpoint of the fixed family the real check starts at the
hybrid adapter's state. -/
theorem checkpoint_aligned (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) :
    TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
        RowsAligned K D A o (W.hybrid c o) := by
  intro hb top tree D A x z Z q dealt bounded small j p setup c o pre live
  let W := TreeCheckWalkRecipe.family prims K circuits settings top tree D A x Z q bounded j p
  let b := W.boundary c
  obtain ⟨r, run, bad, _⟩ := live
  have preRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := W) (c := c) (o := o) pre)
  have self i : (b.batch.ctx i).self = i := rfl
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  change r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o) at run
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, accepted, _⟩ := bad.2
  have rows := TreeCheckTailBoundary.counts prims K circuits settings D Z b self parameters
    o preRun r run ⟨i, (value, records), accepted⟩
  intro k honest
  obtain ⟨data, present, history, label, tag, _, _⟩ := rows k honest
  have tuples : data.2.1.2 = (W.hybrid c o).tuples k := by
    change data.2.1.2 = ((o.1.2 k).map (·.2.1.2)).getD []
    rw [present]
    rfl
  refine ⟨data, present, tuples, ?_, ?_, ?_⟩
  · rw [← tuples]
    exact history
  · rw [label]
    rfl
  · rw [tag]
    rfl

/-- Two honest operators hold the same key for their pair. -/
def PairsAgree (D : C.Coalition) (setup : C.Party → Option (PrssKeys C)) : Prop :=
  ∀ i j, i ∉ D.1 → j ∉ D.1 → i ≠ j →
    (TreeCheckWalkRecipe.setupKeys setup i).pair j = (TreeCheckWalkRecipe.setupKeys setup j).pair i

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Present honest setup rows agree on their pair keys. -/
theorem pairsAgree (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setup : p ∈ support (treeSaltSetup prims D A x z))
    (present : ∀ i, i ∉ D.1 → (p.1.2 i).isSome) : PairsAgree D p.1.2 := by
  intro i j hi hj ne
  obtain ⟨ki, rowI⟩ := Option.isSome_iff_exists.mp (present i hi)
  obtain ⟨kj, rowJ⟩ := Option.isSome_iff_exists.mp (present j hj)
  rw [TreeCheckWalkRecipe.setupKeys_some p.1.2 i ki rowI,
    TreeCheckWalkRecipe.setupKeys_some p.1.2 j kj rowJ]
  exact setup_pair_agree prims D A x z p setup i j ne ki kj rowI rowJ

section Phases

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

variable (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)

omit [DecidableEq E] in
/-- An exchange round couples the same outgoing messages; the continuations
receive the same incoming mail. -/
theorem coupled_exchange {β : Type} (n n' ℓ : ℕ) (outbox : C.Party → Option (Mail C E))
    (fR : C.Party → Mail C E → PartyM C E RealSpec β)
    (fH : C.Party → Mail C E → PartyM C E (CheckSpec C E) Unit)
    (ha : ∃ i, i ∉ D.1 ∧ (outbox i).isSome)
    (next : ∀ sent : C.Party → Mail C E, Coupled prims K D A x prss cache0 label0 n n' ℓ
      (fun i => afterExchange D outbox sent i (fR i)) (fun i => afterExchange D outbox sent i (fH i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 1) ℓ
      (fun i => optionalExchange (outbox i) (fR i)) (fun i => optionalExchange (outbox i) (fH i)) := by
  intro stA h c hle fresh
  rw [realRun_exchange prims D A n stA outbox fR (h, c) ha]
  unfold hybRun
  rw [executePhase_optionalExchange D _ _ n' _ outbox fH ha]
  simp only [simulateQ_bind, StateT.run_bind]
  let view : C.Party → C.Party → Option (Msg E) := fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 then ((outbox i).getD (fun _ => none)) c else none
  have hreal := adversary_run prims D (A.round stA view) h c
  have hhyb : (simulateQ (localAnswer prims)
      ((adapter prims K D A x prss cache0 label0).round ((stA, ℓ) : A.State × ℕ) view)).run h =
      (fun r => (((r.1.1, ℓ), r.1.2), r.2)) <$> (simulateQ (localAnswer prims) (A.round stA view)).run h := by
    simp [adapter, TreeCheckWalkRecipe.checkAdversary, simulateQ_map, StateT.run_map]
  rw [hreal]
  erw [hhyb]
  simp only [bind_map_left]
  have base := relTriple_support_left (relTriple_refl ((simulateQ (localAnswer prims)
    (A.round stA view)).run h)) (fun r hr => (grows_localAnswer prims).simulateQ (A.round stA view) h r hr)
  have mapped : RelTriple ((simulateQ (localAnswer prims) (A.round stA view)).run h)
      ((fun r => (((r.1.1, ℓ), r.1.2), r.2)) <$> (simulateQ (localAnswer prims) (A.round stA view)).run h)
      (fun a b => b = (((a.1.1, ℓ), a.1.2), a.2) ∧ h ≤ a.2) := by
    have := relTriple_map (f := id) (g := fun r : (A.State × (C.Party → C.Party → Option (Msg E))) ×
      HashCache C => (((r.1.1, ℓ), r.1.2), r.2))
      (R := fun a b => b = (((a.1.1, ℓ), a.1.2), a.2) ∧ h ≤ a.2)
      (relTriple_post_mono base (fun a b hab => by rcases hab with ⟨rfl, g⟩; exact ⟨rfl, g⟩))
    simpa using this
  apply relTriple_bind mapped
  rintro r _ ⟨rfl, grow⟩
  exact next r.1.2 r.1.1 r.2 c (hle.trans grow) fresh

omit [DecidableEq E] in
/-- A local pass that starts with the same hash queries and is pure afterwards
couples once the continuations couple on every vector of answers. -/
theorem coupled_prefix {X β : Type} [Inhabited X] (n n' ℓ : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (gR : C.Party → X → PartyM C E RealSpec β) (gH : C.Party → X → PartyM C E (CheckSpec C E) Unit)
    (sR : C.Party → X → Step C E RealSpec β) (sH : C.Party → X → Step C E (CheckSpec C E) Unit)
    (pureR : ∀ i x, advance (gR i x).run = pure (sR i x))
    (pureH : ∀ i x, advance (gH i x).run = pure (sH i x))
    (next : ∀ xs : C.Party → X, Coupled prims K D A x prss cache0 label0 n n' ℓ
      (fun i => gR i (xs i)) (fun i => gH i (xs i))) :
    Coupled prims K D A x prss cache0 label0 n n' ℓ
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gR i)
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= gH i) := by
  intro stA h c hle fresh
  unfold realRun hybRun executePhase
  rw [startSteps_world_prefix D W gR sR pureR, startSteps_local_prefix D W gH sH pureH]
  simp only [simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]
  rw [hashPrefix_run prims D W h c, bind_map_left]
  apply relTriple_bind (relTriple_support_left (relTriple_refl _)
    (P := fun r : (C.Party → Option X) × HashCache C => h ≤ r.2 ∧
      ∀ i, (i ∈ D.1 → r.1 i = none) ∧ (i ∉ D.1 → (r.1 i).isSome)) (fun r hr =>
    ⟨(grows_localAnswer prims).simulateQ _ h r hr, hashPrefix_support D W r.1 (by
      apply OracleComp.support_simulateQ_run'_subset (localAnswer prims)
      rw [StateT.run'_eq, support_map]
      exact ⟨r, hr, rfl⟩)⟩))
  rintro r _ ⟨rfl, grow, shape⟩
  let xs : C.Party → X := fun i => (r.1 i).getD default
  have startR : startSteps worldRoles D (fun i => gR i (xs i)) = pure (prefixSteps sR r.1) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi, prefixSteps, (shape i).1 hi]
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((shape i).2 hi)
      simp [hi, prefixSteps, hy, xs, worldRoles, pureR, free_pure]
  have startH : startSteps localRoles D (fun i => gH i (xs i)) = pure (prefixSteps sH r.1) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi, prefixSteps, (shape i).1 hi]
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((shape i).2 hi)
      simp [hi, prefixSteps, hy, xs, localRoles, pureH]
  have hnext := next xs stA r.2 c (hle.trans grow) fresh
  unfold realRun hybRun executePhase at hnext
  rw [startR, startH] at hnext
  simpa only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind] using hnext

omit [DecidableEq E] in
/-- The last local pass: the hybrid decides each operator locally, and every
real operator that it rejects has stopped. -/
theorem coupled_end {β : Type} (n' ℓ : ℕ) (P : C.Party → PartyM C E RealSpec β)
    (Q : C.Party → PartyM C E (CheckSpec C E) Unit) (o : C.Party → Option Unit)
    (decided : ∀ i, advance (Q i).run = pure (.done (o i)))
    (stopped : ∀ i, i ∉ D.1 → o i = none → ∀ step ∈ support (advance (P i).run), step = .done none) :
    Coupled prims K D A x prss cache0 label0 0 n' ℓ P Q := by
  intro stA h c _ _
  have startH : startSteps localRoles D Q = pure (fun i => if i ∈ D.1 then .done none else .done (o i)) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp [hi, localRoles, decided i]
  have hyb : hybRun prims K D (adapter prims K D A x prss cache0 label0) n' ((stA, ℓ) : A.State × ℕ) Q h =
      pure ((((stA, ℓ) : A.State × ℕ), fun i => if i ∈ D.1 then none else o i), h) := by
    unfold hybRun executePhase
    rw [startH, pure_bind]
    cases n' with
    | zero =>
      simp only [executeRounds, simulateQ_pure, StateT.run_pure]
      congr 3
      funext i
      by_cases hi : i ∈ D.1 <;> simp [hi, Step.output]
    | succ n' =>
      rw [executeRounds, if_pos (fun i hi => by simp [hi, Step.isDone])]
      simp only [simulateQ_pure, StateT.run_pure]
      congr 3
      funext i
      by_cases hi : i ∈ D.1 <;> simp [hi, Step.output]
  rw [hyb]
  apply relTriple_of_support
  intro a ha b hb
  have hb' := (mem_support_pure_iff _ _).mp hb
  subst hb'
  unfold realRun at ha
  rw [support_map] at ha
  obtain ⟨r, hr, rfl⟩ := ha
  have grow : h ≤ r.2.1 := treeSim_stream_grows prims D _ (h, c) r hr
  have raw : r.1 ∈ support (startSteps worldRoles D P >>= fun steps =>
      executeSteps worldRoles D A noFunctionality 0 stA steps) := by
    apply OracleComp.support_simulateQ_run'_subset (streamWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨r, hr, rfl⟩
  rw [mem_support_bind_iff] at raw
  obtain ⟨steps, started, rounds⟩ := raw
  simp only [executeSteps, support_pure, Set.mem_singleton_iff] at rounds
  intro i hi alive
  refine ⟨grow, ?_⟩
  simp only [if_neg hi]
  cases hoi : o i with
  | some u => rfl
  | none =>
    exfalso
    apply alive
    rw [rounds]
    have h := mem_support_sequenceFin_oc _ steps started i
    simp only [if_neg hi] at h
    exact stopped i hi hoi _ (treeSimCheck_support_free _ h)

end Phases

end ThresholdLeanXmssSecurity.TreeCheckKernelCoupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.logged_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.logged_coherent

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.setup_pair_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.setup_pair_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.pairsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.pairsAgree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.checkpoint_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.checkpoint_aligned

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_exchange

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckKernelCoupling.coupled_end

namespace ThresholdLeanXmssSecurity.TreeCheckKernelChecked
open TreeCheckKernelCoupling TreeCheckWalkRecipe TreeCheckWalkCoupling
open TreeCheckGadgetPass
attribute [local instance] Classical.propDecidable
attribute [local instance] inhabitedField
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)
local instance : SampleableType E := SampleableType.ofFintype E

/-- Port of `TreeTwinSavedSchedule.conv_self`, avoiding the unrelated tree-track imports. -/
theorem conv_self (ctx : Context C) (i : C.Party) (self : ctx.self = i) (v : Shares C E) :
    conv K ctx v = conv K (localContext i) v := by
  funext g
  simp only [ThresholdLeanXmss.conv, self, localContext]

/-- The check uses its context only for the local party; randomness remains in its gadget argument. -/
theorem check_self {ι : Type} {G : OracleSpec ι} (ctx : Context C) (i : C.Party)
    (self : ctx.self = i) (gadgets : CheckGadgets C E G) (tuples : List (Tuple C)) :
    check K ctx gadgets tuples = check K (localContext i) gadgets tuples := by
  unfold check compareDigests openSh
  simp only [conv_self K ctx i self, self]
  rfl

/-- An optional exchange also covers the all-dead entry. -/
theorem coupled_optionalExchange {β : Type} (n n' label : ℕ)
    (outbox : C.Party → Option (Mail C E))
    (kR : C.Party → Mail C E → PartyM C E RealSpec β)
    (kH : C.Party → Mail C E → PartyM C E (CheckSpec C E) Unit)
    (next : ∀ sent : C.Party → Mail C E,
      Coupled prims K D A x prss cache0 label0 n n' label
        (fun i => afterExchange D outbox sent i (kR i))
        (fun i => afterExchange D outbox sent i (kH i))) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) label
      (fun i => optionalExchange (outbox i) (kR i))
      (fun i => optionalExchange (outbox i) (kH i)) := by
  by_cases ha : ∃ i, i ∉ D.1 ∧ (outbox i).isSome
  · exact coupled_exchange prims K D A x prss cache0 label0 n n' label outbox kR kH ha next
  · have empty : ∀ i, i ∉ D.1 → outbox i = none := by
      intro i hi
      cases h : outbox i with
      | none => rfl
      | some v => exact False.elim (ha ⟨i,hi,by simp [h]⟩)
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
      (n+1) (n'+1) label _ (fun _ => failure) _ (fun _ => failure)
    · intro i hi
      simp only [empty i hi, optionalExchange]
    · intro i hi
      simp only [empty i hi, optionalExchange]
    · exact coupled_failure prims D K A x prss cache0 label0 (n+1) (n'+1) label _ _ (fun _ _ => rfl)

/-- Shared local acceptance permits the real caller continuation to run to its next suspension. -/
theorem coupled_decide {β : Type} (n' label : ℕ) (ok : C.Party → Prop)
    (k : C.Party → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 0 n' label
      (fun i => if ok i then k i else failure)
      (fun i => if ok i then pure () else failure) := by
  apply coupled_end prims K D A x prss cache0 label0 n' label _ _
    (fun i => if ok i then some () else none)
  · intro i
    by_cases hi : ok i <;> simp only [hi,if_true,if_false,advance_run_failure,advance_run_pure]
  · intro i hi ho step hs
    by_cases hok : ok i
    · simp [hok] at ho
    · simp only [if_neg hok, advance_run_failure, mem_support_pure_iff] at hs
      exact hs

/-- A hash-only prefix followed by the same optional network exchange. -/
theorem coupled_hashExchange {X β : Type} [Inhabited X] (n n' label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (outbox : C.Party → X → Option (Mail C E))
    (kR : C.Party → X → Mail C E → PartyM C E RealSpec β)
    (kH : C.Party → X → Mail C E → PartyM C E (CheckSpec C E) Unit)
    (next : ∀ (xs : C.Party → X) (sent : C.Party → Mail C E),
      Coupled prims K D A x prss cache0 label0 n n' label
        (fun i => afterExchange D (fun i => outbox i (xs i)) sent i (kR i (xs i)))
        (fun i => afterExchange D (fun i => outbox i (xs i)) sent i (kH i (xs i)))) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) label
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        optionalExchange (outbox i a) (kR i a))
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        optionalExchange (outbox i a) (kH i a)) := by
  have pureR : ∀ i a, ∃ step, advance (optionalExchange (outbox i a) (kR i a)).run = pure step := by
    intro i a
    cases outbox i a <;> simp only [optionalExchange, advance_run_failure, advance_exchange_bind] <;>
      exact ⟨_,rfl⟩
  have pureH : ∀ i a, ∃ step, advance (optionalExchange (outbox i a) (kH i a)).run = pure step := by
    intro i a
    cases outbox i a <;> simp only [optionalExchange, advance_run_failure, advance_exchange_bind] <;>
      exact ⟨_,rfl⟩
  apply coupled_prefix prims K D A x prss cache0 label0 (n+1) (n'+1) label W _ _
    (fun i a => (pureR i a).choose) (fun i a => (pureH i a).choose)
    (fun i a => (pureR i a).choose_spec) (fun i a => (pureH i a).choose_spec)
  intro xs
  exact coupled_optionalExchange prims K D A x prss cache0 label0 n n' label _ _ _ (next xs)

/-- Hash-only challenge search in the common query signature. -/
def findHash (key : HashOutput) : ℕ → ℕ → OracleComp (Query C →ₒ HashOutput) (Option E)
  | 0, _ => pure none
  | tries+1, index => do
    let r := elementOfHash K (← query (spec := Query C →ₒ HashOutput) (.expand key index))
    if r ≠ 0 ∧ r ≠ 1 then pure (some r) else findHash key tries (index+1)

/-- The common challenge prefix is the protocol's original search. -/
theorem findHash_lift (key : HashOutput) (tries index : ℕ) :
    liftComp (findHash K key tries index) (RoSpec C) = findChallenge K key tries index := by
  induction tries generalizing index with
  | zero => simp only [findHash, findChallenge, liftComp_pure]
  | succ tries ih =>
    simp only [findHash, findChallenge, liftComp_bind]
    change (hashQuery (.expand key index) >>= _) = _
    apply bind_congr
    intro h
    cases dec : Classical.propDecidable (elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1) with
    | isTrue hp => simp only [if_pos hp, liftComp_pure]
    | isFalse hp => simp only [if_neg hp, ih]

/-- The coin-key hash retains the tag and label from before the coin draw. -/
def challengeHash (tag label : ℕ) (values : List E) : OracleComp (Query C →ₒ HashOutput) (Option E) := do
  let key ← query (spec := Query C →ₒ HashOutput) (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v)))
  findHash K key challengeTries 0

/-- The prefixed transition uses exactly `challengeQuery`. -/
theorem challengeHash_lift (tag label : ℕ) (values : List E) :
    liftComp (challengeHash K tag label values) (RoSpec C) = challengeQuery K tag label values := by
  simp only [challengeHash, challengeQuery, liftComp_bind, findHash_lift]
  rfl

/-- The identical abort frame test and local predicate after a shared exchange. -/
theorem coupled_checkedExchange {X β : Type} [Inhabited X] (n' label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (outbox : C.Party → X → Option (Mail C E))
    (ok : C.Party → X → Mail C E → Prop)
    (kR : C.Party → X → Mail C E → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 1 (n'+1) label
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        optionalExchange (outbox i a) (fun inbox => if ok i a inbox then kR i a inbox else failure))
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        optionalExchange (outbox i a) (fun inbox => if ok i a inbox then pure () else failure)) := by
  apply coupled_hashExchange prims K D A x prss cache0 label0 0 n' label W outbox _ _
  intro xs sent
  let boxes := fun i => outbox i (xs i)
  let inbox := fun i k => if k ∈ D.1 then sent k i else
    ((boxes k).getD (fun _ => some .abort)) i
  let good := fun i => (boxes i).isSome ∧
    ¬ C.parties.any (fun j => Msg.isAbort (inbox i j)) ∧ ok i (xs i) (inbox i)
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
    0 n' label _ (fun i => @ite _ (good i) (Classical.propDecidable _) (kR i (xs i) (inbox i)) failure)
    _ (fun i => @ite _ (good i) (Classical.propDecidable _) (pure ()) failure)
  · intro i hi
    rcases Option.eq_none_or_eq_some (boxes i) with hb | ⟨v,hb⟩
    all_goals change afterExchange D boxes sent i _ = _
    all_goals simp only [afterExchange, hb]
    · simp [good, hb]
    · change (if C.parties.any (fun j => Msg.isAbort (inbox i j)) then failure else
        if ok i (xs i) (inbox i) then kR i (xs i) (inbox i) else failure) = _
      simp only [good,hb,Option.isSome_some,true_and]
      split_ifs <;> simp_all
  · intro i hi
    rcases Option.eq_none_or_eq_some (boxes i) with hb | ⟨v,hb⟩
    all_goals change afterExchange D boxes sent i _ = _
    all_goals simp only [afterExchange, hb]
    · simp [good, hb]
    · change (if C.parties.any (fun j => Msg.isAbort (inbox i j)) then failure else
        if ok i (xs i) (inbox i) then pure () else failure) = _
      simp only [good,hb,Option.isSome_some,true_and]
      split_ifs <;> simp_all
  · exact coupled_decide prims K D A x prss cache0 label0 n' label good
      (fun i => kR i (xs i) (inbox i))

/-- The last opening and test of the protocol. -/
def openTest {ι : Type} {G : OracleSpec ι} (i : C.Party) (v : ℕ → E) : RunM C E G Unit := do
  let opened ← StateT.lift (openSh K (localContext i) v 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

/-- The final network message and both local tests, before an arbitrary caller continuation. -/
theorem openTest_run {ι β : Type} {G : OracleSpec ι} (i : C.Party) (v : ℕ → E)
    (st : RunState C) (k : Unit × RunState C → PartyM C E G β) :
    (openTest K i v).run st >>= k = exchange (openOutbox i v) >>= fun inbox =>
      if OpenAgrees K i v inbox ∧
          openValue K i v inbox 0 * openValue K i v inbox 1 = openValue K i v inbox 2
      then k ((),st) else failure := by
  simp only [openTest, StateT.run_bind, StateT.run_lift, bind_assoc, openSh, pure_bind]
  apply bind_congr
  intro inbox
  change (require (OpenAgrees K i v inbox) >>= fun _ =>
    require (openValue K i v inbox 0 * openValue K i v inbox 1 = openValue K i v inbox 2) >>=
      fun _ => k ((),st)) = _
  simp only [require]
  split_ifs <;> simp_all

/-- The last opening follows any shared challenge prefix, with the original caller continuation. -/
theorem coupled_open_prefix {X β : Type} [Inhabited X] (label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (live : C.Party → X → Prop) (v : C.Party → X → ℕ → E)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 1 2 label
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        if live i a then (openTest K i (v i a)).run (st i) >>= k i else failure)
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        if live i a then (openTest K i (v i a)).run' (st i) else failure) := by
  have hc := coupled_checkedExchange prims K D A x prss cache0 label0 1 label W
    (fun i a => if live i a then some (openOutbox i (v i a)) else none)
    (fun i a inbox => OpenAgrees K i (v i a) inbox ∧
      openValue K i (v i a) inbox 0 * openValue K i (v i a) inbox 1 = openValue K i (v i a) inbox 2)
    (fun i _ _ => k i ((),st i))
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0 1 2 label _ _ _ _ _ _ hc
  · intro i hi
    apply bind_congr
    intro a
    by_cases hl : live i a
    · simp only [if_pos hl,optionalExchange,openTest_run]
      apply bind_congr
      intro inbox
      split_ifs <;> rfl
    · simp only [if_neg hl,optionalExchange]
  · intro i hi
    apply bind_congr
    intro a
    by_cases hl : live i a
    · simp only [if_pos hl,optionalExchange,StateT.run'_eq,← bind_pure_comp]
      rw [openTest_run]
      apply bind_congr
      intro inbox
      split_ifs <;> rfl
    · simp only [if_neg hl,optionalExchange]

/-- A shared optional hash result feeds a real stateful segment and its caller. -/
def prefixReal {S β : Type} [Inhabited S]
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option S))
    (st : C.Party → RunState C) (f : C.Party → S → RunM C E RealSpec Unit)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    C.Party → PartyM C E RealSpec β := fun i =>
  oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
    @ite _ (a.isSome = true) (Classical.propDecidable _) ((f i (a.getD default)).run (st i) >>= k i) failure

/-- The hybrid side of the same optional hash prefix. -/
def prefixHybrid {S : Type} [Inhabited S]
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option S))
    (st : C.Party → RunState C) (f : C.Party → S → RunM C E (CheckSpec C E) Unit) :
    C.Party → PartyM C E (CheckSpec C E) Unit := fun i =>
  oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
    @ite _ (a.isSome = true) (Classical.propDecidable _) ((f i (a.getD default)).run' (st i)) failure

/-- The digest queries in the common hash-only signature. -/
def digestHash (i : C.Party) (salts : Shares C Bit) (h : C.Term → List Bit) :
    OracleComp (Query C →ₒ HashOutput) (List HashOutput) :=
  C.terms.mapM fun T => if i ∈ C.holders T then do
    let history ← query (spec := Query C →ₒ HashOutput) (.history (h T))
    query (spec := Query C →ₒ HashOutput) (.digest (vector 256 (salts T)) history)
    else pure 0

/-- A list of common hash computations remains the same list after inclusion. -/
theorem liftComp_hash_mapM {S T : Type} (L : List S)
    (f : S → OracleComp (Query C →ₒ HashOutput) T) :
    liftComp (L.mapM f) (RoSpec C) = L.mapM (fun s => liftComp (f s) (RoSpec C)) := by
  induction L with
  | nil => simp only [List.mapM_nil,liftComp_pure]
  | cons a as ih => simp only [List.mapM_cons,liftComp_bind,liftComp_pure,ih]

/-- The prefix's digests are the actual salted history digests. -/
theorem digestHash_lift (i : C.Party) (salts : Shares C Bit) (h : C.Term → List Bit) :
    liftComp (digestHash i salts h) (RoSpec C) = digestQuery i salts h := by
  unfold digestHash digestQuery
  rw [liftComp_hash_mapM]
  congr 1
  funext T
  split_ifs <;> simp only [liftComp_bind,liftComp_pure]
  rfl

/-- Expansion after the first coin, in the common hash-only signature. -/
def expansionHash (tag label count : ℕ) (values : List E) :
    OracleComp (Query C →ₒ HashOutput) (List E) := do
  let key ← query (spec := Query C →ₒ HashOutput)
    (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v)))
  (List.range count).mapM fun j => elementOfHash K <$> query (spec := Query C →ₒ HashOutput) (.expand key j)

/-- The hash search and the optional challenge after the coin has advanced the state. -/
def afterChallenge {ι S : Type} {G : OracleSpec ι} (tag label : ℕ) (values : List E)
    (f : E → RunM C E G S) : RunM C E G S := do
  let answer ← StateT.lift (oracleStep (liftComp (challengeHash K tag label values) (RoSpec C)))
  match answer with
  | none => StateT.lift failure
  | some r => f r

/-- The challenge's coin uses the old tag and label, and resumes in the returned state. -/
theorem challenge_bind_run {ι S : Type} {G : OracleSpec ι} (gadgets : CheckGadgets C E G)
    (f : E → RunM C E G S) (st : RunState C) :
    (challenge K gadgets >>= f).run st = (gadgets.coin 1).run st >>= fun o =>
      (afterChallenge K st.tag st.label o.1 f).run o.2 := by
  simp only [challenge,coinKey,afterChallenge,challengeHash_lift,challengeQuery,
    oracleStep_bind,StateT.run_bind,StateT.run_get,StateT.run_lift,bind_assoc,pure_bind]
  apply bind_congr
  intro o
  apply bind_congr
  intro key
  apply bind_congr
  intro answer
  cases answer <;> simp only [StateT.run_lift,StateT.run_pure,pure_bind,failure_bind]

/-- The optional hash prefix is exact on every output, including failure. -/
theorem afterChallenge_run {ι S β : Type} {G : OracleSpec ι} (tag label : ℕ) (values : List E)
    (f : E → RunM C E G S) (st : RunState C) (k : S × RunState C → PartyM C E G β) :
    (afterChallenge K tag label values f).run st >>= k =
      oracleStep (liftComp (challengeHash K tag label values) (RoSpec C)) >>= fun a =>
        @ite _ (a.isSome = true) (Classical.propDecidable _) ((f (a.getD default)).run st >>= k) failure := by
  simp only [afterChallenge,StateT.run_bind,StateT.run_lift,bind_assoc]
  apply bind_congr
  intro a
  cases a <;> simp only [Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true,
    StateT.run_lift,Option.getD_some,failure_bind,pure_bind]

/-- The mail delivered by the fixed scheduler, including honest abort frames. -/
def received (outbox : C.Party → Option (Mail C E)) (sent : C.Party → Mail C E)
    (i : C.Party) : Mail C E := fun j => if j ∈ D.1 then sent j i else
  ((outbox j).getD (fun _ => some .abort)) i

/-- An optional exchange resumes exactly when its local inbox has no abort frame. -/
def exchangeActive (outbox : C.Party → Option (Mail C E)) (sent : C.Party → Mail C E)
    (i : C.Party) : Prop := (outbox i).isSome ∧
  ¬ C.parties.any (fun j => Msg.isAbort (received D outbox sent i j))

/-- The shared scheduler's abort predicate does not depend on the continuation. -/
theorem afterExchange_eq {I O β : Type} (outbox : C.Party → Option (Mail C E))
    (sent : C.Party → Mail C E) (i : C.Party)
    (f : Mail C E → PartyM C E (CallSpec I O) β) :
    afterExchange D outbox sent i f =
      if exchangeActive D outbox sent i then f (received D outbox sent i) else failure := by
  rcases Option.eq_none_or_eq_some (outbox i) with h | ⟨v,h⟩
  · simp only [afterExchange,h,exchangeActive,Option.isSome_none,Bool.false_eq_true,false_and,if_false]
  · simp only [afterExchange,h,exchangeActive,Option.isSome_some,true_and]
    change (if C.parties.any (fun j => Msg.isAbort (received D outbox sent i j)) then failure else
      f (received D outbox sent i)) = _
    split_ifs <;> simp_all

section Gadgets
variable (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
variable (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
  (ctx i).prss.term T = streamKey D prss (.term T))
variable (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
  (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
variable (cached : UsedKeysCached D prss cache0)
include self terms pairs cached

/-- A coin followed by its exact shared challenge search composes with any prefixed continuation. -/
theorem coupled_challenge {β : Type} (n n' label : ℕ) (live : C.Party → Prop)
    (bodyR : C.Party → E → RunM C E RealSpec Unit)
    (bodyH : C.Party → E → RunM C E (CheckSpec C E) Unit) (st : C.Party → RunState C)
    (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β)
    (tail : ∀ W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option E),
      Coupled prims K D A x prss cache0 label0 n n' (label+1)
        (prefixReal W (fun i => nextLabel (st i)) bodyR k)
        (prefixHybrid W (fun i => nextLabel (st i)) bodyH)) :
    Coupled prims K D A x prss cache0 label0 (n+1) (n'+1) label
      (fun i => if live i then
        (challenge K (realCheckGadgets K (ctx i)) >>= bodyR i).run (st i) >>= k i
        else failure)
      (fun i => if live i then
        (challenge K (hybridCheckGadgets K i) >>= bodyH i).run' (st i)
        else failure) := by
  let fR := fun i values => afterChallenge K (st i).tag (st i).label values
    (bodyR i)
  let fH := fun i values => afterChallenge K (st i).tag (st i).label values
    (bodyH i)
  have next : ∀ out : C.Party → Option (List E),
      Coupled prims K D A x prss cache0 label0 n n' (label+1)
        (TreeCheckGadgetCoin.resumeCoinR st (fun i o => (fR i o.1).run o.2 >>= k i) out)
        (TreeCheckGadgetCoin.resumeCoinH st fH out) := by
    intro out
    let W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option E) := fun i => match out i with
      | none => pure none
      | some values => challengeHash K (st i).tag (st i).label values
    have hc := tail W
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
      n n' (label+1) _ _ _ _ _ _ hc
    · intro i hi
      cases ho : out i <;> simp only [prefixReal,TreeCheckGadgetCoin.resumeCoinR,ho,Option.elim_none,
        Option.elim_some,W,liftComp_pure,oracleStep_pure,pure_bind,Option.isSome_none,
        Bool.false_eq_true,if_false,fR,afterChallenge_run]
      apply bind_congr
      intro a
      split_ifs <;> rfl
    · intro i hi
      cases ho : out i <;> simp only [prefixHybrid,TreeCheckGadgetCoin.resumeCoinH,ho,Option.elim_none,
        Option.elim_some,W,liftComp_pure,oracleStep_pure,pure_bind,Option.isSome_none,
        Bool.false_eq_true,if_false,fH,StateT.run'_eq,← bind_pure_comp,afterChallenge_run]
      apply bind_congr
      intro a
      split_ifs <;> rfl
  have hc := TreeCheckGadgetCoin.coupled_coin prims K D A x prss cache0 label0
    ctx self terms pairs cached n n' label live st st labels
    (fun i o => (fR i o.1).run o.2 >>= k i) fH next
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
    (n+1) (n'+1) label _ _ _ _ _ _ hc
  · intro i hi
    by_cases hl : live i <;> simp only [hl,if_true,if_false]
    rw [challenge_bind_run,bind_assoc]
  · intro i hi
    by_cases hl : live i <;> simp only [hl,if_true,if_false]
    rw [StateT.run'_eq,challenge_bind_run]
    simp only [StateT.run'_eq,StateT.run_bind,map_bind,fH]

/-- A final challenge and opening use two real rounds, with one spare hybrid round. -/
theorem coupled_challenge_open {β : Type} (label : ℕ) (live : C.Party → Prop)
    (v : C.Party → E → ℕ → E) (st : C.Party → RunState C)
    (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 2 3 label
      (fun i => if live i then
        (challenge K (realCheckGadgets K (ctx i)) >>= fun r => openTest K i (v i r)).run (st i) >>= k i
        else failure)
      (fun i => if live i then
        (challenge K (hybridCheckGadgets K i) >>= fun r => openTest K i (v i r)).run' (st i)
        else failure) := by
  apply coupled_challenge prims K D A x prss cache0 label0 ctx self terms pairs cached
    1 2 label live _ _ st labels k
  intro W
  exact coupled_open_prefix prims K D A x prss cache0 label0 (label+1) W
    (fun _ a => a.isSome) (fun i a => v i (a.getD default)) (fun i => nextLabel (st i)) k

/-- Digests followed by the final challenge and opening, with any surviving set. -/
theorem coupled_digest_final {β : Type} (label : ℕ) (live : C.Party → Prop)
    (salts : C.Party → Shares C Bit) (v : C.Party → E → ℕ → E)
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 3 4 label
      (fun i => if live i then
        (compareDigests (localContext i) (salts i) >>= fun _ =>
          challenge K (realCheckGadgets K (ctx i)) >>= fun r => openTest K i (v i r)).run (st i) >>= k i
        else failure)
      (fun i => if live i then
        (compareDigests (localContext i) (salts i) >>= fun _ =>
          challenge K (hybridCheckGadgets K i) >>= fun r => openTest K i (v i r)).run' (st i)
        else failure) := by
  let W : C.Party → OracleComp (Query C →ₒ HashOutput) (List HashOutput) := fun i =>
    if live i then digestHash i (salts i) (st i).history else pure []
  let boxes := fun i ds => if live i then some (digestOutbox (E := E) i ds) else none
  let bodyR := fun i => (challenge K (realCheckGadgets K (ctx i)) >>= fun r => openTest K i (v i r)).run (st i) >>= k i
  let bodyH := fun i => (challenge K (hybridCheckGadgets K i) >>= fun r => openTest K i (v i r)).run' (st i)
  have next : ∀ (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E),
      Coupled prims K D A x prss cache0 label0 2 3 label
        (fun i => afterExchange D (fun i => boxes i (ds i)) sent i
          (fun inbox => if DigestsAgree i (ds i) inbox then bodyR i else failure))
        (fun i => afterExchange D (fun i => boxes i (ds i)) sent i
          (fun inbox => if DigestsAgree i (ds i) inbox then bodyH i else failure)) := by
    intro ds sent
    let good := fun i => exchangeActive D (fun i => boxes i (ds i)) sent i ∧
      DigestsAgree i (ds i) (received D (fun i => boxes i (ds i)) sent i)
    have hc := coupled_challenge_open prims K D A x prss cache0 label0 ctx self terms pairs cached
      label good v st labels k
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0 2 3 label _ _ _ _ _ _ hc
    · intro i hi
      rw [afterExchange_eq]
      dsimp only [good,bodyR]
      split_ifs <;> simp_all
    · intro i hi
      rw [afterExchange_eq]
      dsimp only [good,bodyH]
      split_ifs <;> simp_all
  have hc := coupled_hashExchange prims K D A x prss cache0 label0 2 3 label W boxes
    (fun i ds inbox => if DigestsAgree i ds inbox then bodyR i else failure)
    (fun i ds inbox => if DigestsAgree i ds inbox then bodyH i else failure) next
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0 3 4 label _ _ _ _ _ _ hc
  · intro i hi
    by_cases hl : live i
    · simp only [if_pos hl,W,boxes,optionalExchange,digestHash_lift,compareDigests,StateT.run_bind,
        StateT.run_get,StateT.run_lift,bind_assoc,pure_bind]
      apply bind_congr
      intro ds
      apply bind_congr
      intro inbox
      change (require (DigestsAgree i ds inbox) >>= _) = _
      simp only [require]
      split_ifs <;> simp only [pure_bind,failure_bind,bodyR,StateT.run_bind,bind_assoc]
    · simp only [if_neg hl,W,boxes,liftComp_pure,oracleStep_pure,pure_bind,optionalExchange]
  · intro i hi
    by_cases hl : live i
    · simp only [if_pos hl,W,boxes,optionalExchange,digestHash_lift,compareDigests_run']
      apply bind_congr
      intro ds
      apply bind_congr
      intro inbox
      change (require (DigestsAgree i ds inbox) >>= fun _ => bodyH i) = _
      simp only [require]
      split_ifs <;> simp
    · simp only [if_neg hl,W,boxes,liftComp_pure,oracleStep_pure,pure_bind,optionalExchange]

omit self terms pairs cached in
/-- The real digest pass reaches its scheduled exchange before any continuation. -/
theorem digest_exchange {β : Type} (i : C.Party) (salts : Shares C Bit) (st : RunState C)
    (f : Unit → RunM C E RealSpec Unit)
    (k : Unit × RunState C → PartyM C E RealSpec β) :
    TreeSimCheckExchange ((compareDigests (localContext i) salts >>= f).run st >>= k) := by
  simp only [compareDigests,StateT.run_bind,StateT.run_get,StateT.run_lift,bind_assoc,pure_bind]
  apply TreeSimCheckExchange.oracle_bind
  intro ds
  exact TreeSimCheckExchange.exchange_bind _ _

/-- The salt draw, digest comparison and final challenge/opening preserve arbitrary real callers. -/
theorem coupled_salts_final {β : Type} (label : ℕ) (live : C.Party → Prop)
    (v : C.Party → E → ℕ → E) (st : C.Party → RunState C)
    (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 3 5 label
      (fun i => if live i then
        ((realCheckGadgets K (ctx i)).randBits 256 >>= fun salts =>
          compareDigests (localContext i) salts.1 >>= fun _ =>
          challenge K (realCheckGadgets K (ctx i)) >>= fun r => openTest K i (v i r)).run (st i) >>= k i
        else failure)
      (fun i => if live i then
        ((hybridCheckGadgets K i).randBits 256 >>= fun salts =>
          compareDigests (localContext i) salts.1 >>= fun _ =>
          challenge K (hybridCheckGadgets K i) >>= fun r => openTest K i (v i r)).run' (st i)
        else failure) := by
  let bodyR := fun i (salts : PrssOutput C Bit) =>
    compareDigests (localContext i) salts.1 >>= fun _ =>
      challenge K (realCheckGadgets K (ctx i)) >>= fun r => (openTest K i (v i r) : RunM C E RealSpec Unit)
  let bodyH := fun i (salts : PrssOutput C Bit) =>
    compareDigests (localContext i) salts.1 >>= fun _ =>
      challenge K (hybridCheckGadgets K i) >>= fun r => (openTest K i (v i r) : RunM C E (CheckSpec C E) Unit)
  have next : ∀ out : C.Party → Option (PrssOutput C Bit),
      Coupled prims K D A x prss cache0 label0 3 4 (label+1)
        (TreeCheckGadgetCoin.resumeBitsR st (fun i o => (bodyR i o.1).run o.2 >>= k i) out)
        (TreeCheckGadgetCoin.resumeBitsH st bodyH out) := by
    intro out
    have hc := coupled_digest_final prims K D A x prss cache0 label0 ctx self terms pairs cached
      (label+1) (fun i => (out i).isSome) (fun i => ((out i).getD default).1) v
      (fun i => nextLabel (st i)) (fun i hi => by simp only [nextLabel,labels i hi]) k
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
      3 4 (label+1) _ _ _ _ _ _ hc
    · intro i hi
      cases ho : out i <;> simp only [TreeCheckGadgetCoin.resumeBitsR,ho,Option.elim_none,
        Option.elim_some,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true,Option.getD_some]
      rfl
    · intro i hi
      cases ho : out i <;> simp only [TreeCheckGadgetCoin.resumeBitsH,ho,Option.elim_none,
        Option.elim_some,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true,Option.getD_some]
      rfl
  have hc := TreeCheckGadgetCoin.coupled_randBits prims K D A x prss cache0 label0
    ctx self terms pairs cached 2 4 label live st st labels
    (fun i o => (bodyR i o.1).run o.2 >>= k i) bodyH (by
      intro i hi hl out
      exact digest_exchange i out.1 _ _ _) next
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0 3 5 label _ _ _ _ _ _ hc
  · intro i hi
    by_cases hl : live i <;> simp only [hl,if_true,if_false,bodyR,StateT.run_bind,bind_assoc]
  · intro i hi
    rfl

/-- The final mask and check decision after any shared hash prefix. -/
theorem coupled_final_prefix {X β : Type} [Inhabited X] (label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (live : C.Party → X → Prop) (p : C.Party → X → (ℕ → E) × (ℕ → E) × E)
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 4 7 label
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a => if live i a then
        (finalStep K (localContext i) (realCheckGadgets K (ctx i)) (p i a)).run (st i) >>= k i else failure)
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a => if live i a then
        (finalStep K (localContext i) (hybridCheckGadgets K i) (p i a)).run' (st i) else failure) := by
  let products : C.Party → X → E → E → List (Product C E) := fun i a wa wb => [Product.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + (p i a).1 0) (fun _ => wb + (p i a).2.1 0) 1]
  let value := fun i a wa wb (q : Shares C E) r j => match j with
    | 0 => wa + r * (wa + (p i a).1 0)
    | 1 => wb + r * (wb + (p i a).2.1 0)
    | _ => conv K (localContext i) q 0 + ((p i a).2.2 + conv K (localContext i) q 0 +
        conv K (localContext i) q 1) * r + conv K (localContext i) q 1 * r ^ 2
  let bodyR : C.Party → X → E → E → Shares C E → RunM C E RealSpec Unit := fun i a wa wb q => do
    let salts ← (realCheckGadgets K (ctx i)).randBits 256
    compareDigests (localContext i) salts.1
    let r ← challenge K (realCheckGadgets K (ctx i))
    openTest K i (value i a wa wb q r)
  let bodyH : C.Party → X → E → E → Shares C E → RunM C E (CheckSpec C E) Unit := fun i a wa wb q => do
    let salts ← (hybridCheckGadgets K i).randBits 256
    compareDigests (localContext i) salts.1
    let r ← challenge K (hybridCheckGadgets K i)
    openTest K i (value i a wa wb q r)
  have next : ∀ (xs : C.Party → X) (wa wb : C.Party → E) (out : C.Party → Option (Shares C E)),
      Coupled prims K D A x prss cache0 label0 3 5 (label+2)
        (TreeCheckGadgetExtend.resumeReal K (fun i => nextLabel (st i))
          (fun i q => (bodyR i (xs i) (wa i) (wb i) q.1).run q.2 >>= k i) out)
        (fun i => afterExtend K i (products i (xs i) (wa i) (wb i)).length (nextLabel (st i))
          (bodyH i (xs i) (wa i) (wb i)) (out i)) := by
    intro xs wa wb out
    let st' := fun i => (⟨recordHistory K i (st i).history ((out i).getD default) 2,
      (st i).label+2, (st i).tag⟩ : RunState C)
    have hc := coupled_salts_final prims K D A x prss cache0 label0 ctx self terms pairs cached
      (label+2) (fun i => (out i).isSome) (fun i => value i (xs i) (wa i) (wb i) ((out i).getD default))
      st' (fun i hi => by simp only [st',labels i hi]) k
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0 3 5 (label+2)
      _ _ _ _ _ _ hc
    · intro i hi
      cases ho : out i <;> simp only [TreeCheckGadgetExtend.resumeReal,ho,Option.isSome_none,
        Option.isSome_some,Bool.false_eq_true,if_false,if_true,Option.getD_some,st',bodyR,nextLabel,Nat.add_assoc]
    · intro i hi
      cases ho : out i <;> simp only [afterExtend,ho,Option.isSome_none,Option.isSome_some,
        Bool.false_eq_true,if_false,if_true,Option.getD_some,st',bodyH,nextLabel,products,List.length_cons,
        List.length_nil,Nat.add_assoc]
  have hc := TreeCheckGadgetMaskPrefix.coupled_finalMask_prefix prims K D A x prss cache0 label0
    ctx self terms pairs cached 3 5 label W live products (fun _ _ _ _ _ => rfl)
    (fun i _ => st i) (fun i _ => st i) (fun i hi _ => labels i hi)
    (fun i a wa wb q => (bodyR i a wa wb q.1).run q.2 >>= k i) bodyH next
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0 4 7 label _ _ _ _ _ _ hc
  · intro i hi
    apply bind_congr
    intro a
    by_cases hl : live i a <;> simp only [hl,if_true,if_false]
    simp only [finalStep,TreeCheckGadgetExtend.maskProgram,conv_self K (ctx i) i (self i hi),
      products,bodyR,value,openTest,StateT.run_bind,bind_assoc]
    rfl
  · intro i hi
    apply bind_congr
    intro a
    by_cases hl : live i a <;> simp only [hl,if_true,if_false]
    rfl

omit self terms pairs cached in
/-- Mapping the shared optional prefix maps precisely the successful state argument. -/
theorem prefixReal_map {S T β : Type} [Inhabited S] [Inhabited T]
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option S))
    (g : C.Party → S → T) (st : C.Party → RunState C)
    (f : C.Party → T → RunM C E RealSpec Unit)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    prefixReal (fun i => W i >>= fun a => pure (a.map (g i))) st f k =
      prefixReal W st (fun i a => f i (g i a)) k := by
  funext i
  simp only [prefixReal,liftComp_bind,liftComp_pure,oracleStep_bind,oracleStep_pure,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  cases a <;> simp only [Option.map_none,Option.map_some,Option.isSome_none,Option.isSome_some,
    Bool.false_eq_true,if_false,if_true,Option.getD_some]

omit self terms pairs cached in
/-- The same mapping law for the hybrid prefix. -/
theorem prefixHybrid_map {S T : Type} [Inhabited S] [Inhabited T]
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option S))
    (g : C.Party → S → T) (st : C.Party → RunState C)
    (f : C.Party → T → RunM C E (CheckSpec C E) Unit) :
    prefixHybrid (fun i => W i >>= fun a => pure (a.map (g i))) st f =
      prefixHybrid W st (fun i a => f i (g i a)) := by
  funext i
  simp only [prefixHybrid,liftComp_bind,liftComp_pure,oracleStep_bind,oracleStep_pure,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  cases a <;> simp only [Option.map_none,Option.map_some,Option.isSome_none,Option.isSome_some,
    Bool.false_eq_true,if_false,if_true,Option.getD_some]

/-- A check iteration is one two-product extension and one challenge. -/
def iteration {ι S : Type} {G : OracleSpec ι} (gadgets : CheckGadgets C E G)
    (products : S → ℕ → List (Product C E)) (update : S → ℕ → Shares C E → E → S)
    (p : S) (j : ℕ) : RunM C E G S := do
  let z ← gadgets.extendMult (products p j)
  let r ← challenge K gadgets
  pure (update p j z r)

/-- List induction composes the common extension/challenge schedule, retaining the real caller. -/
theorem coupled_fold {S β : Type} [Inhabited S]
    (products : C.Party → S → ℕ → List (Product C E))
    (width : ∀ i, i ∉ D.1 → ∀ p j, (products i p j).length = 2)
    (update : C.Party → S → ℕ → Shares C E → E → S)
    (fR : C.Party → S → RunM C E RealSpec Unit)
    (fH : C.Party → S → RunM C E (CheckSpec C E) Unit)
    (n n' : ℕ) (k : C.Party → Unit × RunState C → PartyM C E RealSpec β)
    (tail : ∀ (label : ℕ) (st : C.Party → RunState C),
      (∀ i, i ∉ D.1 → (st i).label = label) →
      ∀ W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option S),
      Coupled prims K D A x prss cache0 label0 n n' label
        (prefixReal W st fR k) (prefixHybrid W st fH))
    (js : List ℕ) (label : ℕ) (st : C.Party → RunState C)
    (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option S)) :
    Coupled prims K D A x prss cache0 label0 (2*js.length+n) (2*js.length+n') label
      (prefixReal W st (fun i p => js.foldlM (iteration K (realCheckGadgets K (ctx i)) (products i) (update i)) p >>= fR i) k)
      (prefixHybrid W st (fun i p => js.foldlM (iteration K (hybridCheckGadgets K i) (products i) (update i)) p >>= fH i)) := by
  induction js generalizing label st W with
  | nil => simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,List.foldlM_nil,pure_bind] using tail label st labels W
  | cons j js ih =>
    let restR := fun i p => js.foldlM (iteration K (realCheckGadgets K (ctx i)) (products i) (update i)) p >>= fR i
    let restH := fun i p => js.foldlM (iteration K (hybridCheckGadgets K i) (products i) (update i)) p >>= fH i
    let contR := fun i (a : Option S) (z : Shares C E) => challenge K (realCheckGadgets K (ctx i)) >>= fun r =>
      restR i (update i (a.getD default) j z r)
    let contH := fun i (a : Option S) (z : Shares C E) => challenge K (hybridCheckGadgets K i) >>= fun r =>
      restH i (update i (a.getD default) j z r)
    have next : ∀ (xs : C.Party → Option S) (out : C.Party → Option (Shares C E)),
        Coupled prims K D A x prss cache0 label0 (2*js.length+n+1) (2*js.length+n'+1) (label+1)
          (TreeCheckGadgetExtend.resumeReal K st (fun i z => (contR i (xs i) z.1).run z.2 >>= k i) out)
          (fun i => afterExtend K i (products i ((xs i).getD default) j).length (st i)
            (contH i (xs i)) (out i)) := by
      intro xs out
      let st' := fun i => (⟨recordHistory K i (st i).history ((out i).getD default) 2,
        (st i).label+1, (st i).tag⟩ : RunState C)
      have hc := coupled_challenge prims K D A x prss cache0 label0 ctx self terms pairs cached
        (2*js.length+n) (2*js.length+n') (label+1) (fun i => (out i).isSome)
        (fun i r => restR i (update i ((xs i).getD default) j ((out i).getD default) r))
        (fun i r => restH i (update i ((xs i).getD default) j ((out i).getD default) r))
        st' (fun i hi => by simp only [st',labels i hi]) k (by
          intro V
          have h := ih (label+1+1) (fun i => nextLabel (st' i))
            (fun i hi => by simp only [nextLabel,st',labels i hi])
            (fun i => V i >>= fun a => pure (a.map (update i ((xs i).getD default) j ((out i).getD default))))
          simpa only [prefixReal_map,prefixHybrid_map,restR,restH] using h)
      apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
        (2*js.length+n+1) (2*js.length+n'+1) (label+1) _ _ _ _ _ _ hc
      · intro i hi
        cases ho : out i <;> simp only [TreeCheckGadgetExtend.resumeReal,ho,Option.isSome_none,
          Option.isSome_some,Bool.false_eq_true,if_false,if_true,Option.getD_some,st',contR]
      · intro i hi
        cases ho : out i <;> simp only [afterExtend,ho,Option.isSome_none,Option.isSome_some,
          Bool.false_eq_true,if_false,if_true,Option.getD_some,st',contH,width i hi]
    have hc := TreeCheckGadgetExtend.coupled_extend prims K D A x prss cache0 label0
      ctx self terms pairs cached (2*js.length+n+1) (2*js.length+n'+1) label W (fun _ a => a.isSome)
      (fun i a => products i (a.getD default) j) (fun i hi a => width i hi _ j)
      (fun i _ => st i) (fun i _ => st i) (fun i hi _ => labels i hi)
      (fun i a z => (contR i a z.1).run z.2 >>= k i) contH next
    have nr : 2*(j::js).length+n = 2*js.length+n+1+1 := by simp only [List.length_cons]; omega
    have nh : 2*(j::js).length+n' = 2*js.length+n'+1+1 := by simp only [List.length_cons]; omega
    rw [nr,nh]
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
      _ _ label _ _ _ _ _ _ hc
    · intro i hi
      unfold prefixReal
      apply bind_congr
      intro a
      by_cases ha : a.isSome = true <;> simp only [ha,Bool.false_eq_true,if_true,if_false]
      simp only [List.foldlM_cons,iteration,StateT.run_bind,pure_bind,
        bind_assoc,contR,restR]
    · intro i hi
      unfold prefixHybrid
      apply bind_congr
      intro a
      by_cases ha : a.isSome = true <;> simp only [ha,Bool.false_eq_true,if_true,if_false]
      simp only [List.foldlM_cons,iteration,bind_assoc,pure_bind,contH,restH]

/-- The halving fold and final test after an optional shared prefix. -/
theorem coupled_halvings {β : Type} (count label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option ((ℕ → E) × (ℕ → E) × E)))
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 (2*(halvings count-sliceBits)+4) (2*(halvings count-sliceBits)+7) label
      (prefixReal W st (fun i p =>
        (List.range (halvings count-sliceBits)).foldlM
          (halvingStep K (localContext i) (realCheckGadgets K (ctx i)) (sliceWidth count)) p >>=
            finalStep K (localContext i) (realCheckGadgets K (ctx i))) k)
      (prefixHybrid W st (fun i p =>
        (List.range (halvings count-sliceBits)).foldlM
          (halvingStep K (localContext i) (hybridCheckGadgets K i) (sliceWidth count)) p >>=
            finalStep K (localContext i) (hybridCheckGadgets K i))) := by
  let products : C.Party → ((ℕ → E) × (ℕ → E) × E) → ℕ → List (Product C E) := fun _ p j =>
    let length := halvedLength^[j] (sliceWidth count)
    let half := halvedLength length
    let hi := fun (v : ℕ → E) k => if k+half < length then v (k+half) else 0
    [.shamir p.1 p.2.1 half, .shamir (fun k => p.1 k + hi p.1 k) (fun k => p.2.1 k + hi p.2.1 k) half]
  let update := fun i (p : (ℕ → E) × (ℕ → E) × E) j (z : Shares C E) r =>
    let length := halvedLength^[j] (sliceWidth count)
    let half := halvedLength length
    let hi := fun (v : ℕ → E) k => if k+half < length then v (k+half) else 0
    let fold := fun (v : ℕ → E) k => v k + r*(v k+hi v k)
    (fold p.1,fold p.2.1,conv K (localContext i) z 0 +
      (p.2.2+conv K (localContext i) z 1)*r+conv K (localContext i) z 1*r^2)
  have step {ι : Type} {G : OracleSpec ι} (i : C.Party) (g : CheckGadgets C E G) :
      iteration K g (products i) (update i) = halvingStep K (localContext i) g (sliceWidth count) := by
    funext p j
    rfl
  have hc := coupled_fold prims K D A x prss cache0 label0 ctx self terms pairs cached products
    (fun _ _ _ _ => rfl) update
    (fun i => finalStep K (localContext i) (realCheckGadgets K (ctx i)))
    (fun i => finalStep K (localContext i) (hybridCheckGadgets K i)) 4 7 k (by
      intro label st labels V
      exact coupled_final_prefix prims K D A x prss cache0 label0 ctx self terms pairs cached label V
        (fun _ a => a.isSome) (fun _ a => a.getD default) st labels k)
    (List.range (halvings count-sliceBits)) label st labels W
  simpa only [step,List.length_range] using hc

omit self terms pairs cached in
/-- An immutable slice challenge is carried through a fold without changing its computation. -/
theorem foldlM_pair {M : Type → Type} [Monad M] [LawfulMonad M] {T S U : Type}
    (f : T → S → ℕ → M S) (g : T × S → M U) (js : List ℕ) (p : T × S) :
    (js.foldlM (fun p j => f p.1 p.2 j >>= fun q => pure (p.1,q)) p >>= g) =
      js.foldlM (f p.1) p.2 >>= fun q => g (p.1,q) := by
  rcases p with ⟨t,s⟩
  induction js generalizing s with
  | nil => simp only [List.foldlM_nil,pure_bind]
  | cons j js ih => simp only [List.foldlM_cons,bind_assoc,pure_bind,ih]

/-- Both check folds after the shared expansion prefix. -/
theorem coupled_slices {β : Type} (count label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput)
      (Option (List E × Shares C E × Shares C E × E)))
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 (2*halvings count+4) (2*halvings count+7) label
      (prefixReal W st (fun i p => do
        let q ← (List.range sliceBits).foldlM (sliceStep K (localContext i) (realCheckGadgets K (ctx i)) p.1 count) p.2
        let q' ← (List.range (halvings count-sliceBits)).foldlM
          (halvingStep K (localContext i) (realCheckGadgets K (ctx i)) (sliceWidth count))
          (conv K (localContext i) q.1,conv K (localContext i) q.2.1,q.2.2)
        finalStep K (localContext i) (realCheckGadgets K (ctx i)) q') k)
      (prefixHybrid W st (fun i p => do
        let q ← (List.range sliceBits).foldlM (sliceStep K (localContext i) (hybridCheckGadgets K i) p.1 count) p.2
        let q' ← (List.range (halvings count-sliceBits)).foldlM
          (halvingStep K (localContext i) (hybridCheckGadgets K i) (sliceWidth count))
          (conv K (localContext i) q.1,conv K (localContext i) q.2.1,q.2.2)
        finalStep K (localContext i) (hybridCheckGadgets K i) q')) := by
  let products : C.Party → (List E × Shares C E × Shares C E × E) → ℕ → List (Product C E) := fun _ p j =>
    let half := sliceWidth count * 2^(sliceBits-1-j)
    let rest := fun k => coinProduct p.1 0 (sliceBits-1-j) (k / sliceWidth count)
    [.replicated (fun T k => rest k*p.2.1 T k) p.2.2.1 half,
      .replicated (fun T k => rest k*(p.2.1 T k+p.2.1 T (k+half)))
        (fun T k => p.2.2.1 T k+p.2.2.1 T (k+half)) half]
  let update := fun i (p : List E × Shares C E × Shares C E × E) j (z : Shares C E) r =>
    let half := sliceWidth count * 2^(sliceBits-1-j)
    let t₀ := conv K (localContext i) z 0
    let tInf := conv K (localContext i) z 1
    let t₁ := (p.2.2.2+t₀)/p.1.getD (sliceBits-1-j) 0
    let fold := fun (v : Shares C E) T k => v T k+r*(v T k+v T (k+half))
    (p.1,fold p.2.1,fold p.2.2.1,(1+r)*t₀+r*t₁+r*(1+r)*tInf)
  let scalar := fun i (p : List E × Shares C E × Shares C E × E) =>
    (conv K (localContext i) p.2.1,conv K (localContext i) p.2.2.1,p.2.2.2)
  let afterR : C.Party → ((ℕ → E) × (ℕ → E) × E) → RunM C E RealSpec Unit := fun i p =>
    (List.range (halvings count-sliceBits)).foldlM
      (halvingStep K (localContext i) (realCheckGadgets K (ctx i)) (sliceWidth count)) p >>=
        finalStep K (localContext i) (realCheckGadgets K (ctx i))
  let afterH : C.Party → ((ℕ → E) × (ℕ → E) × E) → RunM C E (CheckSpec C E) Unit := fun i p =>
    (List.range (halvings count-sliceBits)).foldlM
      (halvingStep K (localContext i) (hybridCheckGadgets K i) (sliceWidth count)) p >>=
        finalStep K (localContext i) (hybridCheckGadgets K i)
  have step {ι : Type} {G : OracleSpec ι} (i : C.Party) (g : CheckGadgets C E G) :
      iteration K g (products i) (update i) =
        fun p j => sliceStep K (localContext i) g p.1 count p.2 j >>= fun q => pure (p.1,q) := by
    funext p j
    simp only [iteration,sliceStep,products,update,bind_assoc,pure_bind]
  have hc := coupled_fold prims K D A x prss cache0 label0 ctx self terms pairs cached products
    (fun _ _ _ _ => rfl) update (fun i p => afterR i (scalar i p)) (fun i p => afterH i (scalar i p))
    (2*(halvings count-sliceBits)+4) (2*(halvings count-sliceBits)+7) k (by
      intro label st labels V
      have h := coupled_halvings prims K D A x prss cache0 label0 ctx self terms pairs cached count label
        (fun i => V i >>= fun a => pure (a.map (scalar i))) st labels k
      simpa only [prefixReal_map,prefixHybrid_map] using h)
    (List.range sliceBits) label st labels W
  have fuel (n : ℕ) : 2*(List.range sliceBits).length+(2*(halvings count-sliceBits)+n) = 2*halvings count+n := by
    simp only [List.length_range,halvings]
    omega
  rw [fuel 4,fuel 7] at hc
  have fold_eq {ι : Type} {G : OracleSpec ι} (i : C.Party) (g : CheckGadgets C E G)
      (p : List E × Shares C E × Shares C E × E)
      (f : Shares C E × Shares C E × E → RunM C E G Unit) :
      ((List.range sliceBits).foldlM (iteration K g (products i) (update i)) p >>= fun q => f q.2) =
        (List.range sliceBits).foldlM (sliceStep K (localContext i) g p.1 count) p.2 >>= f := by
    rw [step]
    exact foldlM_pair (fun τ => sliceStep K (localContext i) g τ count) (fun q => f q.2) _ p
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
    (2*halvings count+4) (2*halvings count+7) label _ _ _ _ _ _ hc
  · intro i hi
    unfold prefixReal
    apply bind_congr
    intro a
    by_cases ha : a.isSome = true
    · simp only [if_pos ha]
      rw [fold_eq i (realCheckGadgets K (ctx i)) (a.getD default)
        (fun q => afterR i (conv K (localContext i) q.1,conv K (localContext i) q.2.1,q.2.2))]
    · simp only [if_neg ha]
  · intro i hi
    unfold prefixHybrid
    apply bind_congr
    intro a
    by_cases ha : a.isSome = true
    · simp only [if_pos ha]
      rw [fold_eq i (hybridCheckGadgets K i) (a.getD default)
        (fun q => afterH i (conv K (localContext i) q.1,conv K (localContext i) q.2.1,q.2.2))]
    · simp only [if_neg ha]

/-- The slice state computed from the first expansion. -/
def initialSlice (i : C.Party) (count : ℕ) (tuples : List (Tuple C)) (τ : List E) :
    List E × Shares C E × Shares C E × E :=
  (τ,(fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k),liftedPart tuples (·.y),
    conv K (localContext i) (claimOf K τ count (liftedPart tuples (·.z))) 0)

/-- The original folds after the expansion test. -/
def checkTail {ι : Type} {G : OracleSpec ι} (i : C.Party) (gadgets : CheckGadgets C E G)
    (count : ℕ) (p : List E × Shares C E × Shares C E × E) : RunM C E G Unit := do
  let q ← (List.range sliceBits).foldlM (sliceStep K (localContext i) gadgets p.1 count) p.2
  let q' ← (List.range (halvings count-sliceBits)).foldlM
    (halvingStep K (localContext i) gadgets (sliceWidth count))
    (conv K (localContext i) q.1,conv K (localContext i) q.2.1,q.2.2)
  finalStep K (localContext i) gadgets q'

/-- The real and hybrid first-coin continuations use the same expansion and rejection test. -/
def afterExpansion {ι : Type} {G : OracleSpec ι} (i : C.Party) (gadgets : CheckGadgets C E G)
    (count : ℕ) (tuples : List (Tuple C)) (tag label : ℕ) (values : List E) : RunM C E G Unit := do
  let τ ← StateT.lift (oracleStep (liftComp (expansionHash K tag label (coins count) values) (RoSpec C)))
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  checkTail K i gadgets count (initialSlice K i count tuples τ)

omit self terms pairs cached in
/-- Inclusion preserves the actual coin-key hash and expansion queries. -/
theorem expansionHash_lift (tag label count : ℕ) (values : List E) :
    liftComp (expansionHash K tag label count values) (RoSpec C) =
      hashQuery (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))) >>= fun key =>
        (List.range count).mapM (fun j => elementOfHash K <$> hashQuery (.expand key j)) := by
  simp only [expansionHash,liftComp_bind,liftComp_hash_mapM,liftComp_map]
  rfl

omit self terms pairs cached in
/-- The first coin retains its old tag and label on both gadget implementations. -/
theorem check_first_run {ι : Type} {G : OracleSpec ι} (i : C.Party) (gadgets : CheckGadgets C E G)
    (count : ℕ) (tuples : List (Tuple C)) (counts : (tuples.map (·.count)).sum = count)
    (nonzero : count ≠ 0) (st : RunState C) :
    (check K (localContext i) gadgets tuples).run st =
      (gadgets.coin 1).run st >>= fun o =>
        (afterExpansion K i gadgets count tuples st.tag st.label o.1).run o.2 := by
  rw [check_eq K (localContext i) gadgets tuples (counts.trans_ne nonzero)]
  simp only [counts,coinKey,expand,afterExpansion,checkTail,initialSlice,expansionHash_lift,
    oracleStep_bind,StateT.run_bind,StateT.run_get,StateT.run_lift,bind_assoc,pure_bind]

omit self terms pairs cached in
/-- The expansion's local failure is the optional input to the slice fold. -/
theorem afterExpansion_run {ι β : Type} {G : OracleSpec ι} (i : C.Party) (gadgets : CheckGadgets C E G)
    (count : ℕ) (tuples : List (Tuple C)) (tag label : ℕ) (values : List E)
    (st : RunState C) (k : Unit × RunState C → PartyM C E G β) :
    (afterExpansion K i gadgets count tuples tag label values).run st >>= k =
      oracleStep (liftComp (expansionHash K tag label (coins count) values) (RoSpec C)) >>= fun τ =>
        if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then
          (checkTail K i gadgets count (initialSlice K i count tuples τ)).run st >>= k
        else failure := by
  simp only [afterExpansion,StateT.run_bind,StateT.run_lift,bind_assoc,pure_bind]
  apply bind_congr
  intro τ
  simp only [require]
  by_cases h : ∀ b < sliceBits, τ.getD b 0 ≠ 0
  · rw [if_pos h,if_pos h,pure_bind]
  · rw [if_neg h,if_neg h,failure_bind]

/-- The full check couples at its exact real round count, with the original real caller. -/
theorem coupled_check_program {β : Type} (count label : ℕ) (nonzero : count ≠ 0)
    (tuples : C.Party → List (Tuple C))
    (counts : ∀ i, i ∉ D.1 → ((tuples i).map (·.count)).sum = count)
    (st : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec β) :
    Coupled prims K D A x prss cache0 label0 (2*halvings count+5) (2*halvings count+8) label
      (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= k i)
      (fun i => (check K (localContext i) (hybridCheckGadgets K i) (tuples i)).run' (st i)) := by
  let fR := fun i => afterExpansion K i (realCheckGadgets (G := RealSpec) K (ctx i)) count (tuples i) (st i).tag (st i).label
  let fH := fun i => afterExpansion K i (hybridCheckGadgets K i) count (tuples i) (st i).tag (st i).label
  have next : ∀ out : C.Party → Option (List E),
      Coupled prims K D A x prss cache0 label0 (2*halvings count+4) (2*halvings count+7) (label+1)
        (TreeCheckGadgetCoin.resumeCoinR st (fun i o => (fR i o.1).run o.2 >>= k i) out)
        (TreeCheckGadgetCoin.resumeCoinH st fH out) := by
    intro out
    let W : C.Party → OracleComp (Query C →ₒ HashOutput) (Option (List E × Shares C E × Shares C E × E)) := fun i =>
      match out i with
      | none => pure none
      | some values => do
        let τ ← expansionHash K (st i).tag (st i).label (coins count) values
        pure (if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then some (initialSlice K i count (tuples i) τ) else none)
    have hc := coupled_slices prims K D A x prss cache0 label0 ctx self terms pairs cached count (label+1) W
      (fun i => nextLabel (st i)) (fun i hi => by simp only [nextLabel,labels i hi]) k
    apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
      (2*halvings count+4) (2*halvings count+7) (label+1) _ _ _ _ _ _ hc
    · intro i hi
      cases ho : out i <;> simp only [TreeCheckGadgetCoin.resumeCoinR,ho,Option.elim_none,Option.elim_some,
        prefixReal,W,liftComp_pure,oracleStep_pure,pure_bind,Option.isSome_none,Bool.false_eq_true,if_false,
        fR,afterExpansion_run,liftComp_bind,oracleStep_bind,bind_assoc]
      apply bind_congr
      intro τ
      by_cases ht : ∀ b < sliceBits, τ.getD b 0 ≠ 0
      · rw [if_pos ht,if_pos ht]
        rfl
      · rw [if_neg ht,if_neg ht]
        rfl
    · intro i hi
      cases ho : out i <;> simp only [TreeCheckGadgetCoin.resumeCoinH,ho,Option.elim_none,Option.elim_some,
        prefixHybrid,W,liftComp_pure,oracleStep_pure,pure_bind,Option.isSome_none,Bool.false_eq_true,if_false,
        fH,StateT.run'_eq,← bind_pure_comp,afterExpansion_run,liftComp_bind,oracleStep_bind,bind_assoc]
      apply bind_congr
      intro τ
      by_cases ht : ∀ b < sliceBits, τ.getD b 0 ≠ 0
      · rw [if_pos ht,if_pos ht]
        rfl
      · rw [if_neg ht,if_neg ht]
        rfl
  have hc := TreeCheckGadgetCoin.coupled_coin prims K D A x prss cache0 label0 ctx self terms pairs cached
    (2*halvings count+4) (2*halvings count+7) label (fun _ => True) st st labels
    (fun i o => (fR i o.1).run o.2 >>= k i) fH next
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x prss cache0 label0
    (2*halvings count+5) (2*halvings count+8) label _ _ _ _ _ _ hc
  · intro i hi
    rw [check_self K (ctx i) i (self i hi),check_first_run K i _ count _ (counts i hi) nonzero]
    simp only [if_true,bind_assoc,fR]
  · intro i hi
    rw [StateT.run'_eq,check_first_run K i _ count _ (counts i hi) nonzero]
    simp only [if_true,StateT.run'_eq,StateT.run_bind,map_bind,fH]

end Gadgets

/-- The batch's original output opening and audit record after its check. -/
def batchAfterCheck (circuits : Circuits) (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (row : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (final : Unit × RunState C) :
    PartyM C E RealSpec ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) := do
  let cs := jobs.map (circuits ctx.keys.parameter ·.kind)
  let opened ← openRep K ctx row.2.1.1 (outputsOf cs).length
  let output := assemble cs opened
  pure ((some output,[⟨ctx,jobs,initial,row.1,row.2.1.2,row.2.2,output,final.2⟩]),
    (final.2.label,initial.2+1))

/-- Factoring the check retains the exact batch finish computation. -/
theorem batchFinish_eq (circuits : Circuits) (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (row : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C) :
    treeSimCheckBatchFinish K circuits ctx jobs initial row =
      (check K ctx (realCheckGadgets K ctx) row.2.1.2).run row.2.2 >>=
        batchAfterCheck K circuits ctx jobs initial row := by
  simp only [treeSimCheckBatchFinish,treeSimCheckAfterVerify,bind_assoc,pure_bind]
  rfl

/-- Setup agreement supplies the canonical pair key at either honest endpoint. -/
theorem pair_key (setup : C.Party → Option (PrssKeys C)) (agree : PairsAgree D setup)
    (i j : C.Party) (hi : i ∉ D.1) (ne : i ≠ j) :
    (setupKeys setup i).pair j = streamKey D (setupKeys setup) (.pair (C.pairOf i j ne)) := by
  unfold streamKey Committee.pairOf
  by_cases order : i < j
  · simp only [dif_pos order,if_pos hi]
  · simp only [dif_neg order]
    by_cases hj : j ∉ D.1
    · simpa only [if_pos hj] using agree i j hi hj ne
    · simp only [if_neg hj]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 4000 in
/-- At the supported live checkpoint, the actual batch programs couple with the fixed hybrid check. -/
theorem coupled_check (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun top tree D A x z Z _ _ j p W =>
      ∀ c o, (.inl (c,o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c,o)) →
        CheckpointFacts D p.1.2 o.2.1.1 →
        let b := (W.boundary c).batch
        let h := W.hybrid c o
        let m := halvings (tupleCount (b.jobs.map (circuits b.parameter ·.kind)))
        Coupled prims K D A x (setupKeys p.1.2) o.2.1.1 h.label (2*m+5) (2*m+8) h.label
          (fun i => (o.1.2 i).elim failure
            (fun row => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial row >>= b.k i))
          (fun i => (check K (localContext i) (hybridCheckGadgets K i) (h.tuples i)).run'
            ⟨filledHistory K i (h.tuples i),h.label,h.tag⟩) := by
  intro hb top tree D A x z Z q dealt bounded small j p setup c o pre live facts
  let W := family prims K circuits settings top tree D A x Z q bounded j p
  let b := (W.boundary c).batch
  let h := W.hybrid c o
  let count := tupleCount (b.jobs.map (circuits b.parameter ·.kind))
  let row := fun i => (o.1.2 i).getD ([],(fun _ _ => 0,[]),⟨fun _ => [],0,0⟩)
  let st := fun i => (⟨filledHistory K i (h.tuples i),h.label,h.tag⟩ : RunState C)
  have aligned : RowsAligned K D A o h := by
    have all := checkpoint_aligned prims K circuits settings
    unfold AtWalk at all
    with_reducible exact (all hb top tree D A x z Z q dealt bounded small j p setup c o pre live)
  have present i (hi : i ∉ D.1) : o.1.2 i = some (row i) := by
    obtain ⟨data,hp,_,_,_,_⟩ := aligned i hi
    simp only [row,hp,Option.getD_some]
  have tupleEq i (hi : i ∉ D.1) : (row i).2.1.2 = h.tuples i := by
    obtain ⟨data,hp,ht,_,_,_⟩ := aligned i hi
    simpa only [row,hp,Option.getD_some] using ht
  have stateEq i (hi : i ∉ D.1) : (row i).2.2 = st i := by
    obtain ⟨data,hp,_,hh,hl,ht⟩ := aligned i hi
    simp only [row,hp,Option.getD_some,st]
    rw [←hh,←hl,←ht]
  have self i : (b.ctx i).self = i := rfl
  have parameters i : (b.ctx i).keys.parameter = b.parameter := by
    obtain ⟨parameter,seeds,ps,hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i,hx (refHolder D K.publicTerm)]
    rfl
  have pairAgree := pairsAgree prims D A x z p setup facts.present
  have keyTerm i (hi : i ∉ D.1) (T : C.Term) (held : (b.ctx i).self ∈ C.holders T) :
      (b.ctx i).prss.term T = streamKey D (setupKeys p.1.2) (.term T) := by
    exact (TreeCheckWalkTransport.streamKey_term D (setupKeys p.1.2) T i hi held
      (fun a b ha hb heldA heldB => facts.agree a b ha hb T heldA heldB)).symm
  have keyPair i (hi : i ∉ D.1) (l : C.Party) (ne : l ≠ (b.ctx i).self) :
      (b.ctx i).prss.pair l = streamKey D (setupKeys p.1.2)
        (.pair (C.pairOf (b.ctx i).self l (Ne.symm ne))) :=
    pair_key D p.1.2 pairAgree i l hi (Ne.symm ne)
  obtain ⟨r,run,bad,_⟩ := live
  have nonzero : count ≠ 0 := by
    with_reducible exact (TreeCheckWalkPositions.source_count_ne_zero prims K D A circuits settings
      top tree x z j Z (TreeCheckQueryBudget.ofBound bounded).step p c o r run bad)
  have preRun : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := W) (c := c) (o := o) pre)
  change r ∈ support (treeCheckBatchCont prims K circuits D A Z b o) at run
  obtain ⟨_,_,_,_,i,value,records,_,_,_,_,_,_,accepted,_⟩ := bad.2
  have rows := TreeCheckTailBoundary.counts prims K circuits settings D Z (W.boundary c) self parameters
    o preRun r run ⟨i,(value,records),accepted⟩
  have counts i (hi : i ∉ D.1) : ((h.tuples i).map (·.count)).sum = count := by
    obtain ⟨data,hp,_,_,_,hc,_⟩ := rows i hi
    rw [←tupleEq i hi]
    simp only [row,hp,Option.getD_some]
    rw [hc,TreeCheckBatchWalk.counts_sum]
  have hc := coupled_check_program prims K D A x (setupKeys p.1.2) o.2.1.1 h.label
    b.ctx (fun i _ => self i) keyTerm keyPair facts.cached count h.label nonzero h.tuples counts st
    (fun _ _ => rfl) (fun i result => batchAfterCheck K circuits (b.ctx i) b.jobs b.initial (row i) result >>= b.k i)
  apply TreeCheckGadgetCoin.coupled_congr_honest prims K D A x (setupKeys p.1.2) o.2.1.1 h.label
    (2*halvings count+5) (2*halvings count+8) h.label _ _ _ _ _ _ hc
  · intro i hi
    rw [present i hi]
    simp only [Option.elim_some,batchFinish_eq,bind_assoc,tupleEq i hi,stateEq i hi]
    rfl
  · intro i hi
    rfl

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_optionalExchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_optionalExchange

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_hashExchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_hashExchange

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_challenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_challenge

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_final_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_final_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_fold

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_halvings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_halvings

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_slices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_slices

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_check_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_check_program

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckKernelChecked.coupled_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_check

end ThresholdLeanXmssSecurity.TreeCheckKernelChecked
