import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Bottom
import ThresholdLeanXmssSecurity.Proof.PrssRealRand

/-!
# The end of the hybrid of the hop on the used keys, the statements

`drawGame` is the hybrid with the draw of the fresh keys of a slot as a parameter, and `tableGame F`
is the game with the uniform table `F` of keys that is drawn before the game. `EagerDraw`,
`KeyProvenance`, `KeyParametric` and `CellsCount` state the four facts of the game that the bound of
`HybridEnd` needs. `hybridEnd_of_renaming` proves `HybridEnd` from them with `KeyRenaming` in the place
of `KeyParametric`, through `prob_tableHit_le`, the bound of a hit of a uniform table.
`keyRenaming_of_parts` gives `KeyRenaming` from `KeyParametric` and `WorldRenaming`.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## Uniform tables -/

/-- A search of at most `q` candidates from an observation that does not depend on one coordinate of
a uniform table guesses that coordinate with probability at most `q / 2^256`. -/
theorem prob_uniformTable_guess_le {Ω V : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (x : Ω) (view : (Ω → HashOutput) → V)
    (hv : ∀ table u, view (Function.update table x u) = view table)
    (search : V → ProbComp (Finset HashOutput)) (q : ℕ)
    (hq : ∀ v s, s ∈ support (search v) → s.card ≤ q) :
    Pr{let z ← ($ᵗ (Ω → HashOutput)) >>= fun table =>
      search (view table) >>= fun s => pure (decide (table x ∈ s))}[z = true] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have he := (seedGenUniform_update_bind x (fun table =>
    search (view table) >>= fun s => pure (decide (table x ∈ s)))).symm
  simp only [hv, Function.update_self] at he
  have hs := he.trans ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
    (EvalDistEq.bind_right _ fun table => OracleComp.EvalDistEq.bind_bind_swap _ _ _))
  rw [hs.prEvent_eq (· = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro table _
  apply prEvent_bind_le_of_forall_le_of_support
  intro candidates hc
  have hm : (($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ candidates)) : ProbComp Bool) =
      (fun u : HashOutput => decide (u ∈ candidates)) <$> ($ᵗ HashOutput) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hm, prEvent_map]
  simp only [decide_eq_true_eq, SampleableType.prEvent_uniformSample]
  have hb := hq (view table) candidates hc
  norm_num [HashOutput]
  gcongr

end ThresholdLeanXmssSecurity

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

/-- An entry of the table `F` is in `cells`, or two entries of `F` are equal. -/
def TableHit {Ω : Type} (F : Ω → HashOutput) (cells : Finset HashOutput) : Prop :=
  ∃ x, F x ∈ cells ∨ ∃ y, y ≠ x ∧ F y = F x

/-- A table with two equal entries has a hit for each list of cells. -/
theorem tableHit_of_not_injective {Ω : Type} {F : Ω → HashOutput} (h : ¬ Function.Injective F)
    (cells : Finset HashOutput) : TableHit F cells := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨x, y, hxy, hne⟩ := h
  exact ⟨y, Or.inr ⟨x, hne, hxy⟩⟩

/-- The candidates of entry `x`, namely the cells and each other entry of the table. -/
def candidates {Ω : Type} [Fintype Ω] (x : Ω) (F : Ω → HashOutput) (cells : Finset HashOutput) :
    Finset HashOutput :=
  cells ∪ (Finset.univ.erase x).image (Function.update F x 0)

theorem tableHit_iff_candidates {Ω : Type} [Fintype Ω] (F : Ω → HashOutput) (cells : Finset HashOutput) :
    TableHit F cells ↔ ∃ x ∈ (Finset.univ : Finset Ω), F x ∈ candidates x F cells := by
  simp only [TableHit, candidates, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, Finset.mem_erase,
    and_true]
  refine exists_congr fun x => or_congr Iff.rfl (exists_congr fun y => and_congr_right fun hy => ?_)
  rw [Function.update_of_ne hy]

/-- One entry of a uniform table is a candidate with probability at most `(β + |Ω|) / 2^256`, when the
cells do not depend on the table. -/
theorem prob_candidate_le {Ω : Type} [Fintype Ω] [SampleableType (Ω → HashOutput)]
    (view : ProbComp (Finset HashOutput)) (β : ℕ) (hβ : ∀ c ∈ support view, c.card ≤ β) (x : Ω) :
    Pr{let p ← (do let F ← $ᵗ (Ω → HashOutput); let c ← view; pure (F, c))}[p.1 x ∈ candidates x p.1 p.2] ≤
      ((β + Fintype.card Ω : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have h := prob_uniformTable_guess_le x (fun F : Ω → HashOutput => Function.update F x 0)
    (fun table u => Function.update_idem _ _ _)
    (fun v => view >>= fun c => pure (c ∪ (Finset.univ.erase x).image v)) (β + Fintype.card Ω) (by
      intro v s hs
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hs
      obtain ⟨c, hc, rfl⟩ := hs
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add (hβ c hc) ?_)
      exact Finset.card_image_le.trans ((Finset.card_erase_le).trans (le_of_eq Finset.card_univ)))
  have he : (($ᵗ (Ω → HashOutput)) >>= fun table =>
      (view >>= fun c => pure (c ∪ (Finset.univ.erase x).image (Function.update table x 0))) >>= fun s =>
        pure (decide (table x ∈ s))) =
      (fun p : (Ω → HashOutput) × Finset HashOutput => decide (p.1 x ∈ candidates x p.1 p.2)) <$>
        (do let F ← $ᵗ (Ω → HashOutput); let c ← view; pure (F, c)) := by
    simp only [map_bind, map_pure, bind_assoc, pure_bind, candidates]
    congr!
  rw [he, prEvent_map] at h
  simpa only [decide_eq_true_eq] using h

/-- A uniform table has a hit with probability at most `|Ω| (β + |Ω|) / 2^256`, when the cells do not
depend on the table. The bound is the sum of the bounds of the entries. -/
theorem prob_tableHit_le {Ω : Type} [Fintype Ω] [SampleableType (Ω → HashOutput)]
    (view : ProbComp (Finset HashOutput)) (β : ℕ) (hβ : ∀ c ∈ support view, c.card ≤ β) :
    Pr{let p ← (do let F ← $ᵗ (Ω → HashOutput); let c ← view; pure (F, c))}[TableHit p.1 p.2] ≤
      ((Fintype.card Ω * (β + Fintype.card Ω) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  simp only [tableHit_iff_candidates]
  refine (prEvent_exists_finset_le_card_mul _ _ _ fun x _ => prob_candidate_le view β hβ x).trans (le_of_eq ?_)
  rw [Finset.card_univ, ← mul_div_assoc, Nat.cast_mul]

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The hybrid with the draw as a parameter -/

/-- One run of `tree`, as `hybridTreeRun`, with the draw `draw` of the fresh keys of a slot. -/
def drawTreeRun (draw : ℕ → ProbComp (Option (FreshKeys C))) (monitor : TreeMonitor C) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) : RealM C net.State Unit := do
  let s ← get
  let fresh ← StateT.lift (free (liftComp ((List.range (treeSetups tree)).mapM fun c =>
    draw (setupsBefore s.runs + c)) _))
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
    s.adversary fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) tree)
  let bad ← StateT.lift (monitor (fun i => (s.operators i).keys) tree outputs)
  let operators := fun i => (s.operators i).keep (outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad⟩ : RealState C net.State)

/-- At most `count` runs of `tree`, as `hybridTreeRuns`. -/
def drawTreeRuns (draw : ℕ → ProbComp (Option (FreshKeys C))) (monitor : TreeMonitor C) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) : ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      drawTreeRun K circuits settings draw monitor D net tree
      drawTreeRuns draw monitor D net tree count

/-- A request of bottom tree `b`, as `hybridTreeRequest`. -/
def drawTreeRequest (draw : ℕ → ProbComp (Option (FreshKeys C))) (monitor : TreeMonitor C) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    RealM C net.State (Option (BottomTree × Digest)) := do
  drawTreeRuns K circuits settings runLimit draw monitor D net (.bottom b) 1
  let s ← get
  match heldBottom D s.operators b with
  | some tree => pure (some (tree, ← gameValue D s.operators (.randomizer topLayer (topKey b))))
  | none => pure none

/-- The signing oracles, as `hybridOracles`. -/
def drawOracles (draw : ℕ → ProbComp (Option (FreshKeys C))) (monitor : TreeMonitor C) (D : C.Coalition)
    (A : DkgTsigAdversary C E) : QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => StateT.lift (drawTreeRequest K circuits settings runLimit draw monitor D A.net b)
  | .round1 i J e message => signRequest D i e (.round1 i J e message)
  | .round2 i J e message parts => signRequest D i e (.round2 i J e message parts)

/-- The signing phase, as `hybridSigning`. -/
def drawSigning (draw : ℕ → ProbComp (Option (FreshKeys C))) (monitor : TreeMonitor C) (D : C.Coalition)
    (A : DkgTsigAdversary C E) : RealM C A.net.State Bool := do
  let s ← get
  let some (keys, top) := topHolder D s.operators | pure false
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  let (forgery, st) ← (simulateQ (forger + (drawOracles K circuits settings runLimit draw monitor D A + cell))
    (A.forge ⟨top.root, keys.parameter⟩ top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
  let s ← get
  forgeryWins realLift (canonicalDealt D s.operators keys.parameter top) st forgery

/-- The run of the game, as `hybridRun`. -/
def drawRun (draw : ℕ → ProbComp (Option (FreshKeys C))) (monitor : TreeMonitor C) (D : C.Coalition)
    (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) (Bool × Bool) := do
  let (state, keys) ← realExecution D A.net noFunctionality setupRounds
    (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) []
  let (win, s) ← (do
      drawTreeRuns K circuits settings runLimit draw monitor D A.net .top runLimit
      drawSigning K circuits settings runLimit draw monitor D A).run (startState D state keys)
  pure (win, s.flag)

/-- The hybrid game with the draw `draw` of the fresh keys of a slot. -/
def drawGame (draw : ℕ → ProbComp (Option (FreshKeys C))) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) Bool :=
  Prod.snd <$> drawRun K circuits settings runLimit draw (wrongOutput D) D A

/-- An entry of the table of the fresh keys, namely a slot below `n` and a term or a pair. -/
abbrev Entry (C : Committee) (n : ℕ) := Fin n × (C.Term ⊕ C.Pair)

/-- The table of the fresh keys of `n` slots. -/
abbrev Table (C : Committee) (n : ℕ) := Entry C n → HashOutput

/-- The name of the key of a term or of a pair. -/
def entryName : C.Term ⊕ C.Pair → KeyName C := Sum.elim .term .pair

/-- The fresh keys of slot `slot` in the table `F`. A slot from `n` on has no fresh keys. -/
def tableFresh {n : ℕ} (F : Table C n) (slot : ℕ) : Option (FreshKeys C) :=
  if h : slot < n then some (fun T => F (⟨slot, h⟩, .inl T), fun p => F (⟨slot, h⟩, .inr p)) else none

/-- The hybrid game with the keys of the table `F` in each slot. It draws no fresh key. -/
def tableGame (F : Table C (gameSetups runLimit)) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    OracleComp (WorldSpec C) Bool :=
  drawGame K circuits settings runLimit (fun slot => pure (tableFresh F slot)) D A

/-- The keys with a stream cell in the public cache. -/
def streamCells (cache : HashCache C) : Finset HashOutput :=
  Finset.univ.filter fun k => cache (.streamKey k) ≠ none

variable (prims : Primitives)

/-- The run of `game` in `jointKeyWorld` from the start state, as in `usedHitProb`. -/
abbrev jointRun (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ProbComp (Bool × KeyJointState C) :=
  (simulateQ (jointKeyWorld prims D false) game).run keyJointInitial

/-! ## The statements -/

/-- The eager draw. The hybrid in which each slot has fresh keys has the law of the game with a
uniform table that is drawn before the game. A run takes each slot one time, and each slot of an
allowed run is below `gameSetups`. -/
def EagerDraw : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    jointRun prims D (hybridGame K circuits settings runLimit (gameSetups runLimit) D A) =ᵈ
      (do
        let F ← $ᵗ (Table C (gameSetups runLimit))
        jointRun prims D (tableGame K circuits settings runLimit F D A))

/-- The provenance of the hidden keys. Each key of the private table of `jointKeyWorld` at the end of
the game with the table `F` is an entry of `F`, under the name of the entry. -/
def KeyProvenance : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (F : Table C (gameSetups runLimit)),
    ∀ r ∈ support (jointRun prims D (tableGame K circuits settings runLimit F D A)),
      ∀ n k, r.2.keys (n, k) ≠ none → ∃ x : Entry C (gameSetups runLimit), entryName x.2 = n ∧ F x = k

/-- The research step. The stream cells of the public cache have one law for each table without two
equal entries. A hidden key is only an index of the private table of `jointKeyWorld`, and the answer
at an index does not depend on the key. -/
def KeyRenaming : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (F F' : Table C (gameSetups runLimit)),
    Function.Injective F → Function.Injective F' →
      (fun r => streamCells r.2.hash) <$> jointRun prims D (tableGame K circuits settings runLimit F D A) =ᵈ
        (fun r => streamCells r.2.hash) <$> jointRun prims D (tableGame K circuits settings runLimit F' D A)

/-- The count of the stream cells. The public cache has at most `q` stream cells from the adversary
and one for each honest known key. The count is by key, and an honest operator draws many times under
one known key. -/
def CellsCount : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ (F : Table C (gameSetups runLimit)),
      ∀ r ∈ support (jointRun prims D (tableGame K circuits settings runLimit F D A)),
        (streamCells r.2.hash).card ≤ q + honestKnownKeys runLimit C

/-! ## The glue -/

omit [Fintype E] [DecidableEq E] in
/-- With the provenance, `UsedHit` at the end of the game with the table `F` is a hit of the table on
the stream cells. -/
theorem tableHit_of_usedHit (prov : KeyProvenance K circuits settings runLimit prims) (D : C.Coalition)
    (A : DkgTsigAdversary C E) (F : Table C (gameSetups runLimit)) (r : Bool × KeyJointState C)
    (hr : r ∈ support (jointRun prims D (tableGame K circuits settings runLimit F D A))) (h : UsedHit D r.2) :
    TableHit F (streamCells r.2.hash) := by
  have hinv := (jointKeyWorld_false_run_inv prims D _ keyJointInitial (freeInv_initial D) r hr).1
  rcases h with ⟨k, n, hn, hc⟩ | ⟨n, n', k, -, -, hne, hk, hk'⟩
  · obtain ⟨x, -, rfl⟩ := prov D A F r hr n k (hinv.1 k n hn).2
    exact ⟨x, Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)⟩
  · obtain ⟨x, hx, rfl⟩ := prov D A F r hr n k hk
    obtain ⟨y, hy, hyk⟩ := prov D A F r hr n' _ hk'
    exact ⟨x, Or.inr ⟨y, fun e => hne (by rw [← hx, ← hy, e]), hyk⟩⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The table has at most `gameSetups * prssKeyCount` entries. -/
theorem card_entry_le : Fintype.card (Entry C (gameSetups runLimit)) ≤ gameSetups runLimit * prssKeyCount C := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, card_term, prssKeyCount, termCount]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (card_pair_le C) _)

omit [Fintype E] [DecidableEq E] in
/-- The four statements give `HybridEnd`. The union is over the entries of the table, so the bound is
the sum of the bounds of the entries, `|Ω| (q + honestKnownKeys + |Ω|) / 2^256` with
`|Ω| ≤ gameSetups * prssKeyCount`. -/
theorem hybridEnd_of_renaming (eager : EagerDraw K circuits settings runLimit prims)
    (prov : KeyProvenance K circuits settings runLimit prims)
    (rename : KeyRenaming K circuits settings runLimit prims)
    (count : CellsCount K circuits settings runLimit prims) :
    HybridEnd K circuits settings runLimit prims := by
  intro D A q bounded
  unfold hybridProb usedHitProb
  let ref : ProbComp (Finset HashOutput) :=
    if h : ∃ F₀ : Table C (gameSetups runLimit), Function.Injective F₀ then
      (fun r => streamCells r.2.hash) <$> jointRun prims D (tableGame K circuits settings runLimit h.choose D A)
    else pure ∅
  have href : ∀ c ∈ support ref, c.card ≤ q + honestKnownKeys runLimit C := by
    intro c hc
    by_cases h : ∃ F₀ : Table C (gameSetups runLimit), Function.Injective F₀
    · simp only [ref, h, ↓reduceDIte, support_map, Set.mem_image] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      exact count D A q bounded _ r hr
    · simp only [ref, h, ↓reduceDIte, support_pure, Set.mem_singleton_iff] at hc
      subst hc
      simp
  have hstep : Pr{let r ← jointRun prims D (hybridGame K circuits settings runLimit (gameSetups runLimit) D A)}[
        UsedHit D r.2] ≤
      Pr{let p ← (do let F ← $ᵗ (Table C (gameSetups runLimit)); let c ← ref; pure (F, c))}[TableHit p.1 p.2] := by
    rw [(eager D A).prEvent_eq]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun F _ => ?_
    rw [bind_pure_comp, prEvent_map]
    by_cases hF : Function.Injective F
    · have h : ∃ F₀ : Table C (gameSetups runLimit), Function.Injective F₀ := ⟨F, hF⟩
      calc Pr{let r ← jointRun prims D (tableGame K circuits settings runLimit F D A)}[UsedHit D r.2]
          ≤ Pr{let r ← jointRun prims D (tableGame K circuits settings runLimit F D A)}[
              TableHit F (streamCells r.2.hash)] :=
            prEvent_mono_of_support _ _ _ fun r hr hu =>
              tableHit_of_usedHit K circuits settings runLimit prims prov D A F r hr hu
        _ = Pr{let c ← (fun r => streamCells r.2.hash) <$>
              jointRun prims D (tableGame K circuits settings runLimit F D A)}[TableHit F c] := by
            rw [prEvent_map]
        _ = Pr{let c ← ref}[TableHit F c] := by
            rw [(rename D A F h.choose hF h.choose_spec).prEvent_eq]
            simp only [ref, h, ↓reduceDIte]
    · refine (prEvent_le_one _).trans (le_of_eq ?_)
      symm
      rw [OracleComp.prEvent_eq_one_iff]
      exact fun c _ => tableHit_of_not_injective hF c
  have hbound := hstep.trans (prob_tableHit_le ref (q + honestKnownKeys runLimit C) href)
  have hcard := card_entry_le (C := C) runLimit
  have hnat : Fintype.card (Entry C (gameSetups runLimit)) *
      (q + honestKnownKeys runLimit C + Fintype.card (Entry C (gameSetups runLimit))) ≤
      gameSetups runLimit * (prssKeyCount C *
        (q + honestKnownKeys runLimit C + gameSetups runLimit * prssKeyCount C + prssKeyCount C)) := by
    calc _ ≤ gameSetups runLimit * prssKeyCount C *
          (q + honestKnownKeys runLimit C + gameSetups runLimit * prssKeyCount C) :=
          Nat.mul_le_mul hcard (Nat.add_le_add_left hcard _)
      _ ≤ _ := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  refine (ENNReal.toReal_mono (by simp only [ne_eq, ENNReal.div_eq_top, ENNReal.natCast_ne_top, false_and,
    pow_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, or_self, not_false_eq_true]) hbound).trans ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat, freshKeyError,
    prssRandHashError, ← mul_div_assoc, ← Nat.cast_mul]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by positivity)

/-! ## The renaming of the hidden keys -/

/-- The honest calls of `PRG` under a hidden name with the key `σ key` in place of `key`. Each other
call is the same. -/
def renameImpl (D : C.Coalition) (σ : Equiv.Perm HashOutput) : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) :=
  fun t => match t with
  | .inr (.inr (.inr x)) =>
      if Hidden D x.1 then OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inr (x.1, σ x.2.1, x.2.2)))))
      else OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inr x))))
  | t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) t)

/-- A computation of the world with the hidden keys of the honest calls renamed by `σ`. -/
def renameComp (D : C.Coalition) (σ : Equiv.Perm HashOutput) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    OracleComp (WorldSpec C) α :=
  simulateQ (renameImpl D σ) oa

/-- A fact on the code of the game. The game with the table
`σ ∘ F` is the game with the table `F` with the hidden keys of the honest calls renamed by `σ`. An
operator reads a fresh key only as the key of a call of `PRG` under the hidden name of the key
(`prssRandomness`, `prssOverlay`). -/
def KeyParametric : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (F : Table C (gameSetups runLimit)) (σ : Equiv.Perm HashOutput),
    tableGame K circuits settings runLimit (fun x => σ (F x)) D A =
      renameComp D σ (tableGame K circuits settings runLimit F D A)

/-- The second part of the research step, a fact on `jointKeyWorld` for each computation. A renaming of
the hidden keys of the honest calls by a permutation keeps the law of the result and of the public
cache. The private table has the entry of `(n, σ k)` in place of `(n, k)`. -/
def WorldRenaming : Prop :=
  ∀ (D : C.Coalition) (σ : Equiv.Perm HashOutput) {α : Type} (oa : OracleComp (WorldSpec C) α),
    (fun r => (r.1, r.2.hash)) <$> (simulateQ (jointKeyWorld prims D false) (renameComp D σ oa)).run keyJointInitial =ᵈ
      (fun r => (r.1, r.2.hash)) <$> (simulateQ (jointKeyWorld prims D false) oa).run keyJointInitial

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Two tables without two equal entries differ by a permutation of the keys. -/
theorem exists_perm_of_injective {Ω : Type} (F F' : Ω → HashOutput) (hF : Function.Injective F)
    (hF' : Function.Injective F') : ∃ σ : Equiv.Perm HashOutput, ∀ x, σ (F x) = F' x := by
  let e : { k // k ∈ Set.range F } ≃ { k // k ∈ Set.range F' } :=
    (Equiv.ofInjective F hF).symm.trans (Equiv.ofInjective F' hF')
  refine ⟨e.extendSubtype, fun x => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (F x) (Set.mem_range_self x)]
  simp [e, Equiv.ofInjective_symm_apply]

omit [Fintype E] [DecidableEq E] in
/-- The two parts give the research step. -/
theorem keyRenaming_of_parts (param : KeyParametric K circuits settings runLimit)
    (world : WorldRenaming (C := C) prims) : KeyRenaming K circuits settings runLimit prims := by
  intro D A F F' hF hF'
  obtain ⟨σ, hσ⟩ := exists_perm_of_injective F F' hF hF'
  have hF'eq : F' = fun x => σ (F x) := funext fun x => (hσ x).symm
  rw [hF'eq, param D A F σ]
  have h := ((world D σ (tableGame K circuits settings runLimit F D A)).symm).map
    fun p : Bool × HashCache C => streamCells p.2
  simpa only [Functor.map_map] using h

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.prob_tableHit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.prob_tableHit_le

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.hybridEnd_of_renaming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.hybridEnd_of_renaming
