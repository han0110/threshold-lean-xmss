import ThresholdLeanXmssSecurity.Proof.BatchCheck.Wrapper
import ThresholdLeanXmssSecurity.Proof.PrssRealRand

/-!
# The hidden streams as one table, and the join of the check

`streamWorld` answers each free stream call under a hidden name from a lazy uniform table. The first
part moves that table out of the state of the world (`tablePush`). The rows of one block
in a drawn box are fresh rows, and a stream read writes only the cell of its key. The join of the real
check with the check on drawn values (`knownRowsE`, `knownRowsB`, `rowTables`) and the check join
after the prefix of a batch close the file.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkGN

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The coordinate of the hidden table of a stream call. -/
def hiddenCell (x : PrgInput C) : (KeyName C × HashOutput) × ℕ × ℕ × ℕ := ((x.1, x.2.1), x.2.2)

theorem streamWorld_hidden_cached (x : PrgInput C) (hx : Hidden D x.1) (h : HashCache C) (hc : HiddenCache C)
    (b : Bit) (hsome : hc (hiddenCell x) = some b) :
    (streamWorld prims D (.inr (.inr (.inr x)))).run (h, hc) = pure (b, (h, hc)) := by
  simp only [streamWorld, hx, ↓reduceIte, StateT.run_mk]
  rw [randomOracle.run_eq]
  simp only [hiddenCell] at hsome
  simp only [hsome, map_pure]

end ThresholdLeanXmssSecurity.RealNetworkGN

namespace ThresholdLeanXmssSecurity.RealNetworkN3

open ThresholdLeanXmssSecurity.RealNetworkGN

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-! ## The table form -/

/-- A free stream call under a hidden name at a coordinate with no cell in the table `c`. -/
def HiddenMiss (c : HiddenCache C) : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr x)) => Hidden D x.1 ∧ c (hiddenCell x) = none
  | _ => False

/-- The local oracles with the table `c` in the place of each stream under a hidden name. -/
def tableLocal (c : HiddenCache C) : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inr x) => if Hidden D x.1 then pure ((c (hiddenCell x)).getD 0)
      else (query (spec := LocalSpec C) (.inr (.inr x)) : OracleComp (LocalSpec C) Bit)
  | t => (query (spec := LocalSpec C) t : OracleComp (LocalSpec C) _)

/-- The world with the table `c` on the free copy. The counted copy does not change. -/
def tableImpl (c : HiddenCache C) : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) := fun t =>
  match t with
  | .inl t => (query (spec := WorldSpec C) (.inl t) : OracleComp (WorldSpec C) _)
  | .inr t => free (tableLocal D c t)

theorem tableImpl_apply_of_not (c : HiddenCache C) (t : (WorldSpec C).Domain) (ht : ¬ FreeHiddenStream D t) :
    tableImpl D c t = (query (spec := WorldSpec C) t : OracleComp (WorldSpec C) _) := by
  rcases t with ((u | q | x) | p) | (u | q | x) <;> first
    | rfl
    | (simp only [FreeHiddenStream] at ht; simp only [tableImpl, tableLocal, ht, ↓reduceIte]; rfl)

theorem tableImpl_apply_hidden (c : HiddenCache C) (x : PrgInput C) (hx : Hidden D x.1) :
    tableImpl D c (.inr (.inr (.inr x))) = pure ((c (hiddenCell x)).getD 0) := by
  simp only [tableImpl, tableLocal, hx, ↓reduceIte, free_pure]

/-- A computation that calls no coordinate without a cell runs in the stream world as its table form
runs in the ordinary world, and the hidden table does not change. -/
theorem streamWorld_replay {α : Type} (oa : OracleComp (WorldSpec C) α) (c : HiddenCache C)
    (hoa : IsQueryBoundP oa (HiddenMiss D c) 0) (h : HashCache C) :
    (simulateQ (streamWorld prims D) oa).run (h, c) =
      (fun r => (r.1, (r.2, c))) <$> (simulateQ (worldAnswer prims) (simulateQ (tableImpl D c) oa)).run h := by
  induction oa using OracleComp.inductionOn generalizing h with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ HiddenMiss D c t := by
      rcases hoa.1 with h' | h'
      · exact h'
      · exact absurd h' (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) (HiddenMiss D c) 0 := fun u => by
      simpa only [ht, ↓reduceIte] using hoa.2 u
    by_cases hf : FreeHiddenStream D t
    · rcases t with ((u | q | x) | p) | (u | q | x) <;> try exact hf.elim
      obtain ⟨b, hb⟩ : ∃ b, c (hiddenCell x) = some b := by
        cases hc : c (hiddenCell x) with
        | none => exact absurd ⟨hf, hc⟩ ht
        | some b => exact ⟨b, rfl⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind, tableImpl_apply_hidden D c x hf, hb, Option.getD_some, pure_bind]
      rw [RealNetworkGN.streamWorld_hidden_cached prims D x hf h c b hb, pure_bind]
      exact ih b (hk b) h
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind, streamWorld_apply_of_not prims D t hf, onHash_run, bind_map_left, map_bind,
        tableImpl_apply_of_not D c t hf]
      rw [show simulateQ (worldAnswer prims) (query (spec := WorldSpec C) t : OracleComp (WorldSpec C) _) =
        worldAnswer prims t from simulateQ_spec_query _ t]
      exact bind_congr fun r : (WorldSpec C).Range t × HashCache C => ih r.1 (hk r.1) r.2

/-- The coordinates `addr` are drawn first as a uniform table, and the computation reads them from
that table in the ordinary world. The computation calls no coordinate outside the table. -/
theorem streamWorld_table {α : Type} (oa : OracleComp (WorldSpec C) α) {n : ℕ}
    (addr : Fin n → (KeyName C × HashOutput) × ℕ × ℕ × ℕ) (ha : Function.Injective addr) (h : HashCache C)
    (c : HiddenCache C) (hc : ∀ i, c (addr i) = none)
    (hoa : ∀ vals, IsQueryBoundP oa (HiddenMiss D (cacheFin addr vals c)) 0) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) oa).run (h, c) =ᵈ
      (($ᵗ (Fin n → Bit)) >>= fun vals =>
        (simulateQ (worldAnswer prims) (simulateQ (tableImpl D (cacheFin addr vals c)) oa)).run h) := by
  refine (streamWorld_presample prims D oa addr ha h c hc).trans (EvalDistEq.bind_right _ fun vals => ?_)
  rw [streamWorld_replay prims D oa _ (hoa vals) h, Functor.map_map]
  simp only [Prod.mk.eta, id_map']
  exact .rfl

/-! ## The calls that a computation reaches -/

/-- A computation reaches a finite set of calls. -/
theorem exists_finite_queries {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∃ S : Set (WorldSpec C).Domain, S.Finite ∧ IsQueryBoundP oa (· ∉ S) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨∅, Set.finite_empty, trivial⟩
  | query_bind t k ih =>
    choose S hfin hS using ih
    have : Finite ((WorldSpec C).Range t) := by
      rcases t with ((u | q | x) | p) | (u | q | x) <;> exact inferInstance
    obtain ⟨T, hT⟩ : ∃ T : Set (WorldSpec C).Domain, T = insert t (⋃ u, S u) := ⟨_, rfl⟩
    have hfinT : T.Finite := hT ▸ (Set.finite_iUnion hfin).insert t
    have htT : t ∈ T := hT ▸ Set.mem_insert _ _
    have hsub : ∀ u, S u ⊆ T := fun u x hx => hT ▸ Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨u, hx⟩)
    have hnot : ¬ t ∉ T := fun h => h htT
    refine ⟨T, hfinT, (isQueryBoundP_query_bind_iff _ t k 0).2 ⟨Or.inl hnot, fun u => ?_⟩⟩
    simp only [hnot, ↓reduceIte]
    have himp : ∀ t', t' ∉ T → t' ∉ S u := fun t' ht' hmem => ht' (hsub u hmem)
    exact (hS u).of_imp himp

/-! ## The exit from the stream world -/

/-- The exit from the stream world, with no condition on the computation. The public coordinates
`addr` and a finite set `extra` of other coordinates are drawn first. Then the computation runs in
the ordinary world and reads each stream under a hidden name from that table. The other coordinates
are the reachable ones that `addr` and `c` do not hold. -/
theorem streamWorld_exit {α : Type} (oa : OracleComp (WorldSpec C) α) {n : ℕ}
    (addr : Fin n → (KeyName C × HashOutput) × ℕ × ℕ × ℕ) (ha : Function.Injective addr) (h : HashCache C)
    (c : HiddenCache C) (hc : ∀ i, c (addr i) = none) :
    ∃ (m : ℕ) (extra : Fin m → (KeyName C × HashOutput) × ℕ × ℕ × ℕ), Function.Injective extra ∧
      (∀ j, c (extra j) = none) ∧ (∀ j i, extra j ≠ addr i) ∧
      (fun r => (r.1, r.2.1)) <$> (simulateQ (streamWorld prims D) oa).run (h, c) =ᵈ
        (($ᵗ (Fin m → Bit)) >>= fun junk => ($ᵗ (Fin n → Bit)) >>= fun vals =>
          (simulateQ (worldAnswer prims)
            (simulateQ (tableImpl D (cacheFin addr vals (cacheFin extra junk c))) oa)).run h) := by
  obtain ⟨S, hfin, hS⟩ := exists_finite_queries oa
  let cellOf : (WorldSpec C).Domain → (KeyName C × HashOutput) × ℕ × ℕ × ℕ := fun t =>
    match t with
    | .inr (.inr (.inr y)) => hiddenCell y
    | _ => ((.parameter, 0), 0, 0, 0)
  let X : Set ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) :=
    {x | x ∈ cellOf '' S ∧ c x = none ∧ ∀ i, x ≠ addr i}
  have hX : X.Finite := (hfin.image cellOf).subset fun x hx => hx.1
  let e := hX.toFinset.equivFin
  let extra : Fin hX.toFinset.card → (KeyName C × HashOutput) × ℕ × ℕ × ℕ := fun j => (e.symm j).1
  have hmem : ∀ j, extra j ∈ X := fun j => hX.mem_toFinset.1 (e.symm j).2
  have hinj : Function.Injective extra := Subtype.val_injective.comp e.symm.injective
  have hsurj : ∀ x ∈ X, ∃ j, extra j = x := fun x hx =>
    ⟨e ⟨x, hX.mem_toFinset.2 hx⟩, by simp only [extra, Equiv.symm_apply_apply]⟩
  refine ⟨_, extra, hinj, fun j => (hmem j).2.1, fun j i => (hmem j).2.2 i, ?_⟩
  refine (streamWorld_presample prims D oa extra hinj h c fun j => (hmem j).2.1).trans
    (EvalDistEq.bind_right _ fun junk => ?_)
  refine streamWorld_table prims D oa addr ha h _ (fun i => ?_) fun vals => ?_
  · rw [cacheFin_of_not_mem _ _ _ _ fun j hj => (hmem j).2.2 i hj.symm]
    exact hc i
  · refine hS.of_imp fun t ht hmemS => ?_
    rcases t with ((u | q | x) | p) | (u | q | y) <;> try exact ht.elim
    obtain ⟨-, hnone⟩ := ht
    by_cases hi : ∃ i, hiddenCell y = addr i
    · obtain ⟨i, hi⟩ := hi
      rw [hi, cacheFin_at addr ha] at hnone
      exact absurd hnone (by simp)
    · push Not at hi
      rw [cacheFin_of_not_mem _ _ _ _ hi] at hnone
      by_cases hcy : c (hiddenCell y) = none
      · obtain ⟨j, hj⟩ := hsurj (hiddenCell y) ⟨⟨_, hmemS, rfl⟩, hcy, hi⟩
        rw [← hj, cacheFin_at extra hinj] at hnone
        exact absurd hnone (by simp)
      · rw [cacheFin_of_not_mem _ _ _ _ fun j hj => hcy (by rw [hj]; exact (hmem j).2.1)] at hnone
        exact hcy hnone

end ThresholdLeanXmssSecurity.RealNetworkN3

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkN3

open ThresholdLeanXmssSecurity.RealNetworkGN

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support
attribute [local instance] inhabitedField

/-! ## The public box of coordinates -/

section Box

variable {C : Committee} (D : C.Coalition)

/-- A step of the adversary is on the counted copy, and the table does not change it. -/
theorem tableImpl_adversary (c : HiddenCache C) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (tableImpl D c) (worldRoles.adversary oa) = worldRoles.adversary oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [worldRoles_adversary_pure, simulateQ_pure]
  | query_bind t k ih =>
    have hq : (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) = OracleComp.lift (OracleSpec.query t) := rfl
    have hb : worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a) := by
      simp only [worldRoles, liftComp_bind, counted_bind]
    rw [hq, hb, adversary_query, simulateQ_bind]
    simp only [ih]
    congr 1

/-- A step of an honest operator reads the table. -/
theorem tableImpl_free (c : HiddenCache C) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (tableImpl D c) (free oa) = free (simulateQ (tableLocal D c) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [free_pure, simulateQ_pure]
  | query_bind t k ih =>
    simp only [free_bind, simulateQ_bind, ih]
    congr 1
    simp only [free, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact simulateQ_spec_query (tableImpl D c) (Sum.inr t)

end Box

/-! ## The games -/

section Games

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The roles with the table `c`. The adversary uses the local oracles. Each honest operator reads each
stream under a hidden name from the table `c`. -/
def tableRoles (D : C.Coalition) (c : HiddenCache C) : Roles C (OracleComp (LocalSpec C)) :=
  ⟨fun oa => oa, fun oa => simulateQ (tableLocal D c) oa⟩

end Games

/-! ## The table in the programs -/

section Program

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} (D : C.Coalition)

/-- The local calls of an operator program with the table `c`. A round and a call of a functionality
do not change. -/
def partyTable (c : HiddenCache C) : QueryImpl (PartySpec C E G) (OracleComp (PartySpec C E G)) := fun t =>
  match t with
  | .inl (.inl t) => liftComp (tableLocal D c t) (PartySpec C E G)
  | t => (query (spec := PartySpec C E G) t : OracleComp (PartySpec C E G) _)

/-- The program `p` with the table `c` in the place of each stream under a hidden name. -/
def tableProgram (c : HiddenCache C) {α : Type} (p : PartyM C E G α) : PartyM C E G α :=
  OptionT.mk (simulateQ (partyTable D c) p.run)

/-- The table form of a sequence is the sequence of the table forms. -/
theorem tableProgram_bind (c : HiddenCache C) {α β : Type} (p : PartyM C E G α) (f : α → PartyM C E G β) :
    tableProgram D c (p >>= f) = tableProgram D c p >>= fun a => tableProgram D c (f a) := by
  unfold tableProgram
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, simulateQ_bind]
  refine bind_congr fun o => ?_
  cases o <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure]

end Program

/-! ## The statements -/

section Statements

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

variable (C E) in
/-- The table moves from the roles into the programs, on the real network. -/
def TablePushStatement : Prop :=
  ∀ (O L R Ia α : Type) (D : C.Coalition) (c : HiddenCache C) (A : Adversary C E Ia L R)
    (F : Functionality C PEmpty O L R) (fuel : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec PEmpty O) α),
    executePhase (tableRoles D c) D A F fuel st p =
      executePhase localRoles D A F fuel st fun i => tableProgram D c (p i)

end Statements

end ThresholdLeanXmssSecurity.RealNetworkN3

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkN3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} (D : C.Coalition) (c : HiddenCache C)

/-- A stopped program with the table `c` in its rest. -/
def Step.table {α : Type} : Step C E G α → Step C E G α
  | .done out => .done out
  | .wait outbox resume => .wait outbox fun inbox => simulateQ (partyTable D c) (resume inbox)
  | .call input resume => .call input fun r => simulateQ (partyTable D c) (resume r)

theorem advance_table {α : Type} (p : OracleComp (PartySpec C E G) (Option α)) :
    advance (simulateQ (partyTable D c) p) = Step.table D c <$> simulateQ (tableLocal D c) (advance p) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases t with (q | outbox) | input
    · change advance (liftComp (tableLocal D c q) (PartySpec C E G) >>= _) =
        Step.table D c <$> simulateQ (tableLocal D c)
          (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r))
      rw [advance_liftComp_bind, simulateQ_bind, simulateQ_spec_query, map_bind]
      exact bind_congr ih
    · rfl
    · rfl

section Step

variable {α : Type}

theorem Step.outbox_table (s : Step C E G α) : (Step.table D c s).outbox = s.outbox := by
  cases s <;> rfl

theorem Step.delivered_table (s : Step C E G α) : (Step.table D c s).delivered = s.delivered := by
  rcases s with (_ | _) | _ | _ <;> rfl

theorem Step.callInput_table (s : Step C E G α) : (Step.table D c s).callInput = s.callInput := by
  cases s <;> rfl

theorem Step.isDone_table (s : Step C E G α) : (Step.table D c s).isDone = s.isDone := by
  cases s <;> rfl

theorem Step.output_table (s : Step C E G α) : (Step.table D c s).output = s.output := by
  cases s <;> rfl

end Step

section Rounds

variable {O L R Ia α : Type}

theorem startSteps_table (p : C.Party → PartyM C E (CallSpec PEmpty O) α) :
    startSteps localRoles D (fun i => tableProgram D c (p i)) =
      (fun steps i => Step.table D c (steps i)) <$> startSteps (tableRoles D c) D p := by
  unfold startSteps
  have h : ∀ i : C.Party, (if i ∈ D.1 then pure (Step.done none) else
        localRoles.honest (advance (tableProgram D c (p i)).run)) =
      ((if i ∈ D.1 then pure (Step.done none) else (tableRoles D c).honest (advance (p i).run)) >>=
        fun s => pure (Step.table D c s)) := by
    intro i
    split_ifs
    · simp [Step.table]
    · simp only [localRoles, tableRoles, tableProgram, OptionT.run_mk, advance_table, map_eq_bind_pure_comp]
      rfl
  simp only [h]
  rw [sequenceFin_bind_pure, map_eq_bind_pure_comp]
  rfl

theorem stepRound_table (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R) (state : A.State)
    (steps : C.Party → Step C E (CallSpec PEmpty O) α) :
    stepRound localRoles D A F state (fun i => Step.table D c (steps i)) =
      (fun r => (r.1, (fun i => Step.table D c (r.2.1 i)), r.2.2)) <$> stepRound (tableRoles D c) D A F state steps := by
  have hno : ¬ ∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome := by
    rintro ⟨i, -, h⟩
    obtain ⟨x, -⟩ := Option.isSome_iff_exists.1 h
    exact x.elim
  unfold stepRound
  simp only [Step.callInput_table, Step.isDone_table, Step.outbox_table, Step.delivered_table]
  rw [ite_eq_right fun h => hno h.1, ite_eq_right fun h => hno h.1]
  simp only [map_bind, map_pure]
  refine bind_congr fun r => ?_
  rw [sequenceFin_map_bind (g := Step.table D c) (k := fun steps' => pure (r.1, steps', r.2))]
  congr 2
  funext j
  cases hs : steps j with
  | done out => simp [Step.table]
  | wait outbox resume =>
    simp only [Step.table]
    split_ifs
    · simp [Step.table]
    · simp only [localRoles, tableRoles, advance_table]
  | call input resume => simp [Step.table]

theorem executeRounds_table (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α),
    executeRounds localRoles D A F fuel state (fun i => Step.table D c (steps i)) =
      executeRounds (tableRoles D c) D A F fuel state steps
  | 0, state, steps => by simp [executeRounds, Step.output_table]
  | fuel + 1, state, steps => by
    simp only [executeRounds, Step.isDone_table]
    split_ifs
    · simp [Step.output_table]
    · rw [stepRound_table, bind_map_left]
      refine bind_congr fun r => ?_
      exact executeRounds_table A F fuel r.1 r.2.1

end Rounds

theorem tablePush : TablePushStatement C E := by
  intro O L R Ia α D c A F fuel st p
  unfold executePhase
  rw [startSteps_table, bind_map_left]
  exact bind_congr fun steps => (executeRounds_table D c A F fuel st steps).symm

end ThresholdLeanXmssSecurity.RealNetworkN3

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkN3

open ThresholdLeanXmssSecurity.RealNetworkGN

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} (D : C.Coalition) (c : HiddenCache C)

/-- `tableLocal` on the oracles `RoSpec`. -/
def tableRo : QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun t =>
  match t with
  | .inr x => if Hidden D x.1 then pure ((c (hiddenCell x)).getD 0)
      else (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit)
  | t => (query (spec := RoSpec C) t : OracleComp (RoSpec C) _)

theorem tableLocal_liftComp {β : Type} (oa : OracleComp (RoSpec C) β) :
    simulateQ (tableLocal D c) (liftComp oa (LocalSpec C)) = liftComp (simulateQ (tableRo D c) oa) (LocalSpec C) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure]
  | query_bind t k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    congr 1
    rcases t with q | x
    · rfl
    · change simulateQ (tableLocal D c) (liftM ((LocalSpec C).query (.inr (.inr x)))) = _
      simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      by_cases hx : Hidden D x.1
      · simp [tableLocal, tableRo, hx]
      · simp [tableLocal, tableRo, hx]
        rfl

theorem partyTable_liftComp {β : Type} (oa : OracleComp (LocalSpec C) β) :
    simulateQ (partyTable (E := E) (G := G) D c) (liftComp oa (PartySpec C E G)) =
      liftComp (simulateQ (tableLocal D c) oa) (PartySpec C E G) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure, simulateQ_pure]
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k : OracleComp (LocalSpec C) _) (PartySpec C E G) =
        (liftM ((PartySpec C E G).query (.inl (.inl t))) : OracleComp (PartySpec C E G) _) >>=
          fun u => liftComp (k u) _ := by
      rw [liftComp_bind]
      rcases t with n | x | x <;> rfl
    rw [e, simulateQ_bind, simulateQ_bind, liftComp_bind]
    simp only [ih, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rfl

theorem tableProgram_oracleStep {β : Type} (oa : OracleComp (RoSpec C) β) :
    tableProgram D c (oracleStep oa : PartyM C E G β) = oracleStep (simulateQ (tableRo D c) oa) := by
  unfold tableProgram oracleStep localStep
  apply OptionT.ext
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure, partyTable_liftComp,
    tableLocal_liftComp]

theorem tableRo_prgQueries_hidden (name : KeyName C) (key : HashOutput) (ρ idx : ℕ) (hn : Hidden D name)
    (l : List ℕ) :
    simulateQ (tableRo D c) (l.mapM fun position =>
      (liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, position))) : OracleComp (RoSpec C) Bit)) =
      pure (l.map fun position => ((c ((name, key), ρ, idx, position)).getD 0 : Bit)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, simulateQ_bind, ih, simulateQ_pure]
    have hq : simulateQ (tableRo D c)
        (liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, a))) : OracleComp (RoSpec C) Bit) =
          pure ((c ((name, key), ρ, idx, a)).getD 0) := by
      simp [tableRo, hn, hiddenCell]
    rw [hq]
    rfl

theorem tableRo_prgQueries_of_not (name : KeyName C) (key : HashOutput) (ρ idx : ℕ) (hn : ¬ Hidden D name)
    (l : List ℕ) :
    simulateQ (tableRo D c) (l.mapM fun position =>
      (liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, position))) : OracleComp (RoSpec C) Bit)) =
      l.mapM fun position =>
        (liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, position))) : OracleComp (RoSpec C) Bit) := by
  erw [simulateQ_list_mapM]
  refine congrArg (List.mapM · l) (funext fun a => ?_)
  simp [tableRo, hn]

theorem getD_map_range (f : ℕ → Bit) (m g : ℕ) :
    ((List.range m).map f).getD g 0 = if g < m then f g else 0 := by
  by_cases h : g < m <;> simp [h, List.getD_eq_getElem?_getD]

theorem tableRo_prgBits (name : KeyName C) (key : HashOutput) (ρ idx m : ℕ) :
    simulateQ (tableRo D c) (prgBits name key ρ idx m) = cachedBits D c name key ρ idx m := by
  have hp : prgBits name key ρ idx m = (List.range m).mapM (fun position =>
      (liftM (OracleSpec.query (spec := RoSpec C) (.inr (name, key, ρ, idx, position))) : OracleComp (RoSpec C) Bit)) >>=
        fun bits => pure fun g => bits.getD g 0 := rfl
  unfold cachedBits
  by_cases hn : Hidden D name
  · rw [hp, simulateQ_bind, tableRo_prgQueries_hidden D c name key ρ idx hn]
    simp only [hn, ↓reduceIte, simulateQ_pure]
    refine (pure_bind _ _).trans (congrArg (pure (f := OracleComp (RoSpec C))) (funext fun g => ?_))
    exact getD_map_range _ m g
  · rw [hp, simulateQ_bind, tableRo_prgQueries_of_not D c name key ρ idx hn]
    simp only [hn, ↓reduceIte, simulateQ_pure]

variable [Field E] [Algebra Bit E] (K : Constants C E)

theorem tableRo_callStreams (prss : PrssKeys C) (i : C.Party) (ρ : ℕ) (call : RandCall) :
    simulateQ (tableRo D c) (callStreams K prgBits prss i ρ call) = callStreams K (cachedBits D c) prss i ρ call := by
  cases call <;> simp only [callStreams, prssStreams, simulateQ_map, simulateQ_bind, simulateQ_pure,
    simulateQ_list_mapM, apply_ite (simulateQ (tableRo D c)), apply_dite (simulateQ (tableRo D c)), tableRo_prgBits]

theorem tableProgram_randCall_bind {β : Type} (ctx : Context C) (call : RandCall)
    (body : RandOutput C E → RunM C E G β) (st : RunState C) :
    tableProgram D c ((randCall K ctx call >>= body).run st) =
      oracleStep (callStreams K (cachedBits D c) ctx.prss ctx.self st.label call) >>= fun o =>
        tableProgram D c ((body o).run ⟨st.history, st.label + 1, st.tag⟩) := by
  rw [StateT.run_bind, randCall_run, bind_map_left, tableProgram_bind, tableProgram_oracleStep,
    tableRo_callStreams]

variable (prims : Primitives)

end ThresholdLeanXmssSecurity.RealNetworkN3

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkN3

open ThresholdLeanXmssSecurity.RealNetworkGN

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E)

omit [Fintype E] [DecidableEq E] in
theorem reshare_clipOutput {ι : Type} {G : OracleSpec ι} {R : Type} [Field R] (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    reshare (G := G) K ctx codec (clipOutput count randomness) v count = reshare K ctx codec randomness v count := by
  obtain ⟨r, Zs⟩ := randomness
  set r' : Shares C R := fun T g => if g < count then r T g else 0
  set Zs' : C.Party → ℕ → R := fun j g => if g < count then Zs j g else 0
  have hU : ∀ g < count, reshareU K ctx r' Zs' v g = reshareU K ctx r Zs v g := fun g hg => by
    simp only [reshareU, r', Zs', hg, ↓reduceIte]
  have hO : reshareOut K ctx codec r' Zs' v count = reshareOut K ctx codec r Zs v count := by
    have hV : vector count (reshareU K ctx r' Zs' v) = vector count (reshareU K ctx r Zs v) :=
      List.map_congr_left fun g hg => hU g (List.mem_range.1 hg)
    unfold reshareOut
    rw [hV]
  have hZ : ∀ inbox, reshareZ K ctx codec r' Zs' v count inbox = reshareZ K ctx codec r Zs v count inbox :=
    fun inbox => funext fun T => funext fun g => by
      unfold reshareZ
      by_cases hg : count ≤ g
      · simp only [hg, or_true, ↓reduceIte]
      · have hg' : g < count := by omega
        simp only [hg, or_false, hU g hg', r', hg', ↓reduceIte]
  apply StateT.ext
  intro st
  change (reshare K ctx codec (r', Zs') v count).run st = _
  rw [reshare_run, reshare_run, hO]
  simp only [hZ]

omit [Fintype E] [DecidableEq E] in
/-- The `extendMult` of the real check is the `Rand` call `.elements 0 n` and then the reshare. -/
theorem extendMult_randCall {ι : Type} {G : OracleSpec ι} (ctx : Context C) (products : List (Product C E)) :
    (realCheckBuildingBlocks (G := G) K ctx).extendMult products =
      randCall K ctx (.elements 0 products.length) >>= fun o => match o with
        | .inl randomness => reshare K ctx (elementCodec K) randomness
            (fun g => match products[g]? with | some p => productShare K ctx p | none => 0) products.length
        | .inr _ => StateT.lift failure := by
  simp only [realCheckBuildingBlocks, randCall, bind_assoc, pure_bind, reshare_clipOutput]
  rfl

end ThresholdLeanXmssSecurity.RealNetworkN3

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkN3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C)

/-- `Coin` reads its PRSS output only at the `count` positions. -/
theorem coinWith_clipOutput (randomness : PrssOutput C E) (count : ℕ) :
    coinWith (G := G) K ctx (clipOutput count randomness) count = coinWith K ctx randomness count := by
  have hv : ∀ g < count, conv K ctx (clipOutput count randomness).1 g = conv K ctx randomness.1 g := fun g hg => by
    simp only [conv, clipOutput, hg, ↓reduceIte]
  apply StateT.ext
  intro s
  simp only [coinWith, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  unfold openSh
  have hvec : vector count (conv K ctx (clipOutput count randomness).1) = vector count (conv K ctx randomness.1) :=
    List.map_congr_left fun g hg => hv g (List.mem_range.1 hg)
  simp only [bind_assoc, hvec]
  refine bind_congr fun inbox => ?_
  simp only [pure_bind]
  congr 1
  · simp (contextual := true) only [hv]
  · funext u
    exact congrArg (fun l => pure (l, s)) (List.map_congr_left fun g hg => by
      simp only [hv g (List.mem_range.1 hg)])

variable (D : C.Coalition)

end ThresholdLeanXmssSecurity.RealNetworkN3

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1s

open ThresholdLeanXmssSecurity.RealNetworkGN ThresholdLeanXmssSecurity.RealNetworkN3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The statements of the table form -/

section Copies

variable {C : Committee} (D : C.Coalition)

variable {E : Type} {ι : Type} {G : OracleSpec ι}

/-- The local calls of an operator program with the table `c`. A round and a call of a functionality
do not change. -/
def partyTable (c : HiddenCache C) : QueryImpl (PartySpec C E G) (OracleComp (PartySpec C E G)) := fun t =>
  match t with
  | .inl (.inl t) => liftComp (tableLocal D c t) (PartySpec C E G)
  | t => (query (spec := PartySpec C E G) t : OracleComp (PartySpec C E G) _)

/-- The program `p` with the table `c` in the place of each stream under a hidden name. -/
def tableProgram (c : HiddenCache C) {α : Type} (p : PartyM C E G α) : PartyM C E G α :=
  OptionT.mk (simulateQ (partyTable D c) p.run)

/-- The PRSS keys `prss` of operator `i` are the keys `term` and `pair` at each name that `i` reads. -/
def HoldsDealt (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (i : C.Party) (prss : PrssKeys C) : Prop :=
  (∀ T, i ∈ C.holders T → prss.term T = (dealtPrssKeys term pair i).term T) ∧
    ∀ j, j ≠ i → prss.pair j = (dealtPrssKeys term pair i).pair j

end Copies

end ThresholdLeanXmssSecurity.RealNetworkE1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support
attribute [local instance] inhabitedField

/-! ## The copies -/

section Copies

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

theorem tableProgram_eq (D : C.Coalition) (c : HiddenCache C) {α : Type} (p : PartyM C E G α) :
    tableProgram D c p = RealNetworkN3.tableProgram D c p := rfl

end Copies

end ThresholdLeanXmssSecurity.RealNetworkE1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1g

open RealNetworkE1s RealNetworkE1r

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-! ## The wrapper of a batch -/

section Wrapper

variable (K : Constants C E) (D : C.Coalition) {Ia L R : Type} (A : Adversary C E Ia L R)
  (mode : ReshareMode) (jobs : List Circuit) (L₁ tg : ℕ)

/-- The stream index of the call at position `n` of a check with `R` halvings (`realCheckBuildingBlocks`).
`extendMult` reads stream 0. `coin` and `randElements` read stream 1. -/
def checkStream (R n : ℕ) : ℕ :=
  if n ≤ 2 * R then (if n % 2 = 1 then 0 else 1) else if n = 2 * R + 2 then 0 else 1

end Wrapper

end ThresholdLeanXmssSecurity.RealNetworkE1g

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1o

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- One position of a stream is one call of `H` at `streamKey key` and a function of its answer. The
name, the label, the stream index and the position do not enter the cache. -/
theorem prgAnswer_run (x : PrgInput C) (s : HashCache C) :
    (prgAnswer prims x).run s = (hashAnswer prims (.streamKey x.2.1)).run s >>= fun p =>
      pure (prims.aes.eval (truncateHash p.1) x.2.2, p.2) := by
  simp only [prgAnswer, StateT.run_bind, StateT.run_pure]

variable {E : Type} [Field E] [Algebra Bit E]

end ThresholdLeanXmssSecurity.RealNetworkE1o

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1o

open RealNetworkE1s RealNetworkE1r RealNetworkE1g RealNetworkALP

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-- The known rows over `E` of the check at the label `Lc`, for the receivers `live`. -/
def knownRowsE (K : Constants C E) (D : C.Coalition) (live : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (Lc count : ℕ) :
    OracleComp (LocalSpec C) (ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) :=
  (fun rows n => rows.getD n (fun _ _ => 0, fun _ _ _ => 0)) <$>
    (List.range (RealNetworkV3.checkLabels count)).mapM fun n =>
      liftComp (knownStreams D live (elementCodec K) term pair (Lc + n) (checkStream (halvings count) n) 2)
        (LocalSpec C)

/-- The known row of the salts of the check at the label `Lc`, for the receivers `live`. -/
def knownRowsB (D : C.Coalition) (live : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (Lc count : ℕ) :
    OracleComp (LocalSpec C) (Shares C Bit × (C.Party → C.Party → ℕ → Bit)) :=
  liftComp (knownStreams D live (bitCodec (E := E)) term pair (Lc + (2 * halvings count + 3)) 2 256) (LocalSpec C)

/-- The tables of the check at the label `Lc`, read from the table `table` under the keys `term` and
`pair`. -/
def rowTables (K : Constants C E) (table : HiddenCache C) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (Lc count : ℕ) :
    RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels count) where
  freshE k T g := K.encode.symm fun e => tableBit table term pair (.term T) (Lc + k.val)
    (checkStream (halvings count) k.val) (elementBits * g.val + e.val)
  freshPairE k p g := K.encode.symm fun e => tableBit table term pair (.pair p) (Lc + k.val)
    (checkStream (halvings count) k.val) (elementBits * g.val + e.val)
  freshB T g := tableBit table term pair (.term T) (Lc + (2 * halvings count + 3)) 2 g.val
  freshPairB p g := tableBit table term pair (.pair p) (Lc + (2 * halvings count + 3)) 2 g.val

/-- The check on drawn values of operator `i` from the state `rs`, with the state at its end. -/
def drawnCheckFrom {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : RealNetworkV3.DrawTables C E m)
    (i : C.Party) (tuples : List (Tuple C)) (rs : RunState C) : PartyM C E RealSpec (Unit × RunState C) :=
  (check K (localContext i) (RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB tables i) tuples).run rs

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- `drawnCheckAt` is `drawnCheckFrom` at the state `filledHistory`, with no kept state. -/
theorem drawnCheckAt_eq {m : ℕ} (K : Constants C E) (D : C.Coalition) (L tg : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : RealNetworkV3.DrawTables C E m)
    (x : C.Party → List (Tuple C)) (i : C.Party) :
    RealNetworkV3.drawnCheckAt K D L tg knownE knownB tables x i =
      Prod.fst <$> drawnCheckFrom K D L knownE knownB tables i (x i) ⟨filledHistory K i (x i), L, tg⟩ := rfl

end ThresholdLeanXmssSecurity.RealNetworkE1o

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1l

open RealNetworkE1s RealNetworkE1r RealNetworkE1g

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee}

/-- The output of `F_rand` at an honest operator reads the fresh tables only at the hidden names. -/
theorem frandShare_hidden {R : Type} [Zero R] (D : C.Coalition) (count : ℕ) (known : Shares C R)
    (knownPairs : C.Party → C.Party → ℕ → R) (t t' : C.Term → Fin count → R) (u u' : C.Pair → Fin count → R)
    (ht : ∀ T, Hidden D (.term T) → t T = t' T) (hu : ∀ p, Hidden D (.pair p) → u p = u' p)
    (i : C.Party) (hi : i ∉ D.1) :
    frandShare D count known knownPairs t u i = frandShare D count known knownPairs t' u' i := by
  unfold frandShare
  refine Prod.ext (funext fun T => ?_) (funext fun j => ?_)
  · by_cases hk : KnownTo D.1 T
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte, ht T hk]
  · by_cases hij : i = j
    · simp only [hij, ↓reduceDIte]
    · by_cases hj : j ∈ D.1
      · simp only [hij, ↓reduceDIte, hj, ↓reduceIte]
      · have hp : Hidden D (.pair (C.pairOf i j hij)) := by
          unfold Committee.pairOf
          split_ifs
          · exact ⟨hi, hj⟩
          · exact ⟨hj, hi⟩
        simp only [hij, ↓reduceDIte, hj, ↓reduceIte, hu _ hp]

end ThresholdLeanXmssSecurity.RealNetworkE1l

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1join

open RealNetworkE1s RealNetworkE1r RealNetworkE1g RealNetworkALP RealNetworkE1o RealNetworkE1l

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

/-! ## The join on one fixed table after a prefix -/

section Join

variable {Ia Lk Rk α π γ : Type}

/-- The real check phase of a batch on the table `table`. -/
def realCheckPhase (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia Lk Rk)
    (F : Functionality C PEmpty PEmpty Lk Rk) (keys : C.Party → Keys C) (table : HiddenCache C) (fuel : ℕ)
    (inputs : C.Party → Option α) (tuples : α → List (Tuple C)) (rs : α → RunState C) (prss : α → PrssKeys C)
    (st : W.State) : OracleComp (LocalSpec C) (W.State × (C.Party → Option (α × Unit × RunState C))) :=
  executePhase localRoles D W F fuel st fun i => (inputs i).elim failure fun v =>
    tableProgram D table
      ((check K ⟨i, keys i, prss v⟩ (realCheckBuildingBlocks K ⟨i, keys i, prss v⟩) (tuples v)).run (rs v) >>=
        fun h => pure (v, h))

/-- The check phase on drawn values with the tables `tables`, with the known rows read first. -/
def drawnCheckPhase (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia Lk Rk) (L count : ℕ)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (tables : RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels count)) (fuel : ℕ)
    (inputs : C.Party → Option α) (tuples : α → List (Tuple C)) (rs : α → RunState C) (st : W.State) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option (α × Unit × RunState C))) :=
  knownRowsE K D (RealNetworkGP.liveSet D inputs) term pair L count >>= fun knownE =>
    knownRowsB (E := E) D (RealNetworkGP.liveSet D inputs) term pair L count >>= fun knownB =>
      executePhase localRoles D (checkAdversary W) noFunctionality fuel st fun i =>
        (inputs i).elim failure fun v =>
          drawnCheckFrom K D L knownE knownB tables i (tuples v) (rs v) >>= fun h => pure (v, h)

/-- Two sets of tables agree at each hidden name. -/
def HiddenAgree (D : C.Coalition) {m : ℕ} (t t' : RealNetworkV3.DrawTables C E m) : Prop :=
  (∀ k T, Hidden D (.term T) → t.freshE k T = t'.freshE k T) ∧
    (∀ k p, Hidden D (.pair p) → t.freshPairE k p = t'.freshPairE k p) ∧
    (∀ T, Hidden D (.term T) → t.freshB T = t'.freshB T) ∧
    (∀ p, Hidden D (.pair p) → t.freshPairB p = t'.freshPairB p)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The check phase on drawn values reads the tables only at the hidden names. -/
theorem drawnCheckPhase_hidden (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia Lk Rk)
    (L count : ℕ) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (t t' : RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels count)) (h : HiddenAgree D t t') (fuel : ℕ)
    (inputs : C.Party → Option α) (tuples : α → List (Tuple C)) (rs : α → RunState C) (st : W.State) :
    drawnCheckPhase K D W L count term pair t fuel inputs tuples rs st =
      drawnCheckPhase K D W L count term pair t' fuel inputs tuples rs st := by
  unfold drawnCheckPhase
  refine bind_congr fun knownE => bind_congr fun knownB => ?_
  refine executePhase_congr _ _ _ _ _ _ _ fun i hi => ?_
  have hb : RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB t i =
      RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB t' i := by
    have hE : ∀ k, RealNetworkV3.drawnE D knownE t k i = RealNetworkV3.drawnE D knownE t' k i := fun k => by
      unfold RealNetworkV3.drawnE
      split_ifs with hk
      · exact frandShare_hidden D 2 _ _ _ _ _ _ (h.1 ⟨k, hk⟩) (h.2.1 ⟨k, hk⟩) i hi
      · rfl
    unfold RealNetworkV3.drawnCheckBuildingBlocks
    simp only [hE, frandShare_hidden D 256 knownB.1 knownB.2 _ _ _ _ h.2.2.1 h.2.2.2 i hi]
  unfold drawnCheckFrom
  rw [hb]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A draw before two reads and a run moves behind the two reads. -/
theorem draw_behind (prims : Primitives) {τ κ₁ κ₂ δ δ' : Type} (draw : OracleComp (LocalSpec C) τ)
    (read₁ : OracleComp (LocalSpec C) κ₁) (read₂ : OracleComp (LocalSpec C) κ₂)
    (P : τ → κ₁ → κ₂ → OracleComp (LocalSpec C) δ) (post : δ → OracleComp (LocalSpec C) γ)
    (Q : κ₁ → κ₂ → τ → OracleComp (LocalSpec C) δ') (post' : δ' → OracleComp (LocalSpec C) γ)
    (h : ∀ t a b, SameRun prims (P t a b >>= post) (Q a b t >>= post')) :
    SameRun prims (draw >>= fun t => (read₁ >>= fun a => read₂ >>= fun b => P t a b) >>= post)
      (read₁ >>= fun a => read₂ >>= fun b => (draw >>= fun t => Q a b t) >>= post') := by
  simp only [bind_assoc]
  refine (sameRun_swap prims draw read₁ _).trans (SameRun.bind_right _ fun a => ?_)
  refine (sameRun_swap prims draw read₂ _).trans (SameRun.bind_right _ fun b => ?_)
  exact SameRun.bind_right _ fun t => h t a b

omit [Fintype E] [DecidableEq E] in
/-- The branch `full` of the join after the prefix is `c1Real` with the known rows read first, for the
fuel `checkRounds`. The premise `hphase` is the bridge of the phase. It has the first history
`filledHistory` of `drawnCheckAt` and the map of the outputs to `Option Unit`. -/
theorem drawnBranch_c1Real (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (W : Adversary C E Ia Lk Rk) (counts : List ℕ) (L tg : ℕ) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (inputs : C.Party → Option α) (tuples : α → List (Tuple C))
    (rs : α → RunState C) (st : W.State) (x : C.Party → List (Tuple C))
    (post : W.State × (C.Party → Option (α × Unit × RunState C)) → OracleComp (LocalSpec C) γ)
    (post' : W.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) γ)
    (hphase : ∀ knownE knownB (tables : RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels counts.sum)),
      SameRun prims
      (executePhase localRoles D (checkAdversary W) noFunctionality (checkRounds counts.sum) st (fun i =>
        (inputs i).elim failure fun v =>
          drawnCheckFrom K D L knownE knownB tables i (tuples v) (rs v) >>= fun h => pure (v, h)) >>= post)
      (executePhase localRoles D (checkAdversary W) noFunctionality (checkRounds counts.sum) st
        (RealNetworkV3.drawnCheckAt K D L tg knownE knownB tables x) >>= post')) :
    SameRun prims
      (RealNetworkV3.drawTables (RealNetworkV3.checkLabels counts.sum) >>= fun tables =>
        drawnCheckPhase K D W L counts.sum term pair tables (checkRounds counts.sum) inputs tuples rs st >>= post)
      (knownRowsE K D (RealNetworkGP.liveSet D inputs) term pair L counts.sum >>= fun knownE =>
        knownRowsB (E := E) D (RealNetworkGP.liveSet D inputs) term pair L counts.sum >>= fun knownB =>
          RealNetworkC1s.c1Real K D (checkAdversary W) knownE knownB counts L tg x st >>= post') := by
  unfold drawnCheckPhase RealNetworkC1s.c1Real
  exact draw_behind prims (RealNetworkV3.drawTables (RealNetworkV3.checkLabels counts.sum))
    (knownRowsE K D (RealNetworkGP.liveSet D inputs) term pair L counts.sum)
    (knownRowsB (E := E) D (RealNetworkGP.liveSet D inputs) term pair L counts.sum) _ post _ post'
    fun tables knownE knownB => hphase knownE knownB tables

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A run in front that no later run uses gives nothing to the result. The final cache is not the same. -/
theorem unused_run_drop (prims : Primitives) {κ β : Type} (reads : OracleComp (LocalSpec C) κ)
    (R : OracleComp (LocalSpec C) β) (cache : HashCache C) :
    (simulateQ (localAnswer prims) (reads >>= fun _ => R)).run' cache =ᵈ
      (simulateQ (localAnswer prims) R).run' cache := by
  have h := sameRun_swap prims reads R fun _ b => pure b
  simp only [bind_pure] at h
  have h1 := (h cache).map Prod.fst
  refine (by simpa only [← StateT.run'_eq] using h1 :
    (simulateQ (localAnswer prims) (reads >>= fun _ => R)).run' cache =ᵈ
      (simulateQ (localAnswer prims) (R >>= fun b => reads >>= fun _ => pure b)).run' cache).trans ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind,
    map_pure]
  rw [map_eq_bind_pure_comp]
  exact OracleComp.EvalDistEq.bind_congr_of_support _ fun z _ =>
    OracleComp.EvalDistEq.bind_const ((simulateQ (localAnswer prims) reads).run z.2) (pure z.1)

end Join

/-! ## Corner cases -/

section LiftTest

attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

end LiftTest

end ThresholdLeanXmssSecurity.RealNetworkE1join

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.streamWorld_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.streamWorld_replay

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.streamWorld_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.streamWorld_table

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.streamWorld_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.streamWorld_exit

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.tablePush' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.tablePush

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.reshare_clipOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.reshare_clipOutput

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.extendMult_randCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.extendMult_randCall

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkN3.coinWith_clipOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkN3.coinWith_clipOutput

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkE1o.drawnCheckAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkE1o.drawnCheckAt_eq

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkE1join.drawnBranch_c1Real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkE1join.drawnBranch_c1Real
