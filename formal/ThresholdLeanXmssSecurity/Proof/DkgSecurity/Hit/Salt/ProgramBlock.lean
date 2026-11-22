import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.ProgramBase
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Shift
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.HiddenPlaces

/-!
# The salt draws and the digest calls of one check

The block of a check is the draws of the salts of the held terms (`termDrawsOn`), the pair draws, and
the digest calls of the held terms (`digestsAt`), with a continuation that does not read the salts.

* `prov_prgBits_run`, the rewrite of the draw of one salt puts one entry with the salt into the queue.
* `prov_termDraws_run`, the draws of the held terms put their entries into the queue, in the order of
  the terms.
* `prov_digests_run`, the digest calls take the entries out, and a call with a private entry goes to
  the salt plus `δ`.
* `prov_block`, the block from the empty queue is the shifted block and ends with the empty queue.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_mapM
  noCall_query)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (D : C.Coalition) (δ : Fin 256 → Bit)

/-! ## The pieces of the block -/

section Pieces

variable (self : C.Party) (keyOf : C.Term → HashOutput) (ρ : ℕ)

/-- The draws of the salts of the held terms of `l`. -/
def termDrawsOn (l : List C.Term) : OracleComp (RoSpec C) (List (ℕ → Bit)) :=
  l.mapM fun T => if self ∈ C.holders T then prgBits (.term T) (keyOf T) ρ 2 256 else pure fun _ => 0

/-- The digest calls of the held terms of `l` at the salts `addr`. -/
def digestsAt (l : List C.Term) (addr : C.Term → List Bit) (hist : C.Term → List Bit) :
    OracleComp (RoSpec C) (List HashOutput) :=
  l.mapM fun T => if self ∈ C.holders T then
    hashQuery (.history (hist T)) >>= fun x => hashQuery (.digest (addr T) x) else pure 0

/-- The entries of the held terms of `l` with the salts `addr`. -/
def entriesOn (l : List C.Term) (addr : C.Term → List Bit) : ProvQueue C :=
  l.filterMap fun T => if self ∈ C.holders T then some (((.term T, keyOf T), ρ), addr T) else none

end Pieces

/-! ## Calls on the free copy -/

theorem free_liftComp_hashQuery_bind {α : Type} (q : Query C) (k : HashOutput → OracleComp (RoSpec C) α) :
    free (liftComp (hashQuery q >>= k) (LocalSpec C)) =
      (liftM ((WorldSpec C).query (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) _) >>= fun u =>
        free (liftComp (k u) (LocalSpec C)) := by
  rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
  rfl

theorem free_liftComp_readCell (x : PrgInput C) :
    free (liftComp (readCell x) (LocalSpec C)) = (liftM ((WorldSpec C).query (.inr (.inr (.inr x)))) : OracleComp (WorldSpec C) Bit) := by
  simpa using free_liftComp_readCell_bind x pure

theorem free_liftComp_hashQuery (q : Query C) :
    free (liftComp (hashQuery q) (LocalSpec C)) = (liftM ((WorldSpec C).query (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) HashOutput) := by
  simpa using free_liftComp_hashQuery_bind q pure

theorem free_liftComp_pure {α : Type} (a : α) : free (liftComp (pure a : OracleComp (RoSpec C) α) (LocalSpec C)) = pure a := by
  rw [liftComp_pure, ThresholdLeanXmssSecurity.free_pure]

theorem free_liftComp_bind {α β : Type} (X : OracleComp (RoSpec C) α) (k : α → OracleComp (RoSpec C) β) :
    free (liftComp (X >>= k) (LocalSpec C)) = free (liftComp X (LocalSpec C)) >>= fun a => free (liftComp (k a) (LocalSpec C)) := by
  rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]

theorem provShift_stream_run (x : PrgInput C) (Q : ProvQueue C) :
    (simulateQ (provShift D δ) (liftM ((WorldSpec C).query (.inr (.inr (.inr x)))) : OracleComp (WorldSpec C) Bit)).run Q =
      (fun b => (b, pushRead x b Q)) <$> (liftM ((WorldSpec C).query (.inr (.inr (.inr x)))) : OracleComp (WorldSpec C) Bit) := by
  rw [simulateQ_spec_query]
  rfl

theorem provShift_history_run (y : List Bit) (Q : ProvQueue C) :
    (simulateQ (provShift D δ) (liftM ((WorldSpec C).query (.inr (.inr (.inl (.history y))))) :
      OracleComp (WorldSpec C) HashOutput)).run Q =
      (fun r => (r, Q)) <$> (liftM ((WorldSpec C).query (.inr (.inr (.inl (.history y))))) : OracleComp (WorldSpec C) HashOutput) := by
  rw [simulateQ_spec_query]
  rfl

theorem provShift_digest_run (salt : List Bit) (history : HashOutput) (e : ((KeyName C × HashOutput) × ℕ) × List Bit)
    (Q : ProvQueue C) :
    (simulateQ (provShift D δ) (liftM ((WorldSpec C).query (.inr (.inr (.inl (.digest salt history))))) :
      OracleComp (WorldSpec C) HashOutput)).run (e :: Q) =
      (fun r => (r, Q)) <$> (liftM ((WorldSpec C).query (.inr (.inr (.inl
        (.digest (if Private D e salt then addSalt δ salt else salt) history))))) : OracleComp (WorldSpec C) HashOutput) := by
  rw [simulateQ_spec_query]
  rfl

/-- A program on the free copy with no call of `Touch` on the local oracles has no call of `Touch`. -/
theorem noTouch_free_liftComp {α : Type} (X : OracleComp (RoSpec C) α)
    (h : NoCall (fun t => Touch (C := C) (.inr (.inr t))) X) : NoCall Touch (free (liftComp X (LocalSpec C))) := by
  rw [noCall_iff] at h ⊢
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ Touch (C := C) (.inr (.inr t)) := h.1.resolve_right (by omega)
    have e : free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inr t))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl ht, fun u => by simpa [ht] using ih u (by simpa [ht] using h.2 u)⟩

/-- A program of the local hash with no read of a stream has no translation. -/
theorem shiftRo_of_noStream (σ : HiddenCell C → Bit) {α : Type} (X : OracleComp (RoSpec C) α)
    (h : NoCall (fun t : (RoSpec C).Domain => ∃ x, t = .inr x) X) : simulateQ (shiftRo D σ) X = X := by
  rw [noCall_iff] at h
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ ∃ x, t = .inr x := h.1.resolve_right (by omega)
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with q | x
    · exact bind_congr fun u => ih u (by simpa [ht] using h.2 u)
    · exact absurd ⟨x, rfl⟩ ht

theorem noStream_digestsAt (self : C.Party) (l : List C.Term) (addr : C.Term → List Bit) (hist : C.Term → List Bit) :
    NoCall (fun t : (RoSpec C).Domain => ∃ x, t = .inr x) (digestsAt self l addr hist) := by
  unfold digestsAt
  refine noCall_mapM _ _ _ fun T => ?_
  split
  · exact noCall_bind _ (noCall_query _ _ fun ⟨x, h⟩ => by cases h) fun _ =>
      noCall_query _ _ fun ⟨x, h⟩ => by cases h
  · exact noCall_pure _ _

/-! ## The draw of one salt -/

section Draw

variable (T : C.Term) (key : HashOutput) (ρ : ℕ)

/-- The reads of a salt from a position `p ≥ 1` extend the last entry of the queue. -/
theorem prov_reads_run : ∀ (m p : ℕ) (Q : ProvQueue C) (acc : List Bit), acc.length = p → 1 ≤ p →
    (simulateQ (provShift D δ) (free (liftComp ((List.range' p m).mapM fun position =>
      readCell (.term T, key, ρ, 2, position)) (LocalSpec C)))).run (Q ++ [(((.term T, key), ρ), acc)]) =
      free (liftComp ((List.range' p m).mapM fun position => readCell (.term T, key, ρ, 2, position)) (LocalSpec C)) >>=
        fun bs => pure (bs, Q ++ [(((.term T, key), ρ), acc ++ bs)])
  | 0, p, Q, acc, _, _ => by simp
  | m + 1, p, Q, acc, hl, hp => by
    have hpush : ∀ b, pushRead ((.term T, key, ρ, 2, p) : PrgInput C) b (Q ++ [(((.term T, key), ρ), acc)]) =
        Q ++ [(((.term T, key), ρ), acc ++ [b])] := fun b => by
      have hp0 : p ≠ 0 := by omega
      simp [pushRead, hp0, hl]
    rw [List.range'_succ, List.mapM_cons]
    simp only [free_liftComp_bind, free_liftComp_readCell, free_liftComp_pure, simulateQ_bind, simulateQ_pure,
     StateT.run_pure,
      StateT.run_bind, provShift_stream_run, bind_map_left, bind_assoc, pure_bind]
    refine bind_congr fun b => ?_
    rw [hpush b, prov_reads_run m (p + 1) Q (acc ++ [b]) (by simp [hl]) (by omega)]
    simp only [bind_assoc, pure_bind, List.append_assoc, List.singleton_append]

/-- The reads of the positions `range' p m` give lists of length `m`. -/
theorem reads_length : ∀ (m p : ℕ), ∀ bs ∈ support (free (liftComp ((List.range' p m).mapM fun position =>
    readCell (.term T, key, ρ, 2, position)) (LocalSpec C)) : OracleComp (WorldSpec C) (List Bit)), bs.length = m
  | 0, p, bs, h => by simpa [free_liftComp_pure] using h
  | m + 1, p, bs, h => by
    rw [List.range'_succ, List.mapM_cons, free_liftComp_readCell_bind, mem_support_bind_iff] at h
    obtain ⟨b, -, h⟩ := h
    rw [free_liftComp_bind, mem_support_bind_iff] at h
    obtain ⟨bs', hbs', h⟩ := h
    rw [free_liftComp_pure] at h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [reads_length m (p + 1) bs' hbs']

theorem vector_getD (bs : List Bit) (n : ℕ) (h : bs.length = n) : vector n (fun g => bs.getD g 0) = bs := by
  subst h
  refine List.ext_getElem (by simp [vector]) fun k h₁ h₂ => ?_
  simp [vector, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The rewrite of the draw of one salt puts one entry with the salt into the queue. -/
theorem prov_prgBits_run (Q : ProvQueue C) :
    (simulateQ (provShift D δ) (free (liftComp (prgBits (.term T) key ρ 2 256) (LocalSpec C)))).run Q =
      free (liftComp (prgBits (.term T) key ρ 2 256) (LocalSpec C)) >>= fun f =>
        pure (f, Q ++ [(((.term T, key), ρ), vector 256 f)]) := by
  have hp : prgBits (.term T) key ρ 2 256 = ((0 :: List.range' 1 255).mapM fun position =>
      readCell (.term T, key, ρ, 2, position)) >>= fun bits => pure fun g => bits.getD g 0 := by
    have hr : List.range 256 = 0 :: List.range' 1 255 := by
      rw [List.range_eq_range']
      rfl
    unfold prgBits
    rw [hr]
    rfl
  have hpush : ∀ b, pushRead ((.term T, key, ρ, 2, 0) : PrgInput C) b Q = Q ++ [(((.term T, key), ρ), [b])] :=
    fun b => by simp [pushRead]
  rw [hp, List.mapM_cons]
  simp only [free_liftComp_bind, free_liftComp_readCell, free_liftComp_pure, simulateQ_bind, simulateQ_pure,
     StateT.run_pure,
    StateT.run_bind, provShift_stream_run, bind_map_left, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  rw [hpush b, prov_reads_run D δ T key ρ 255 1 Q [b] rfl le_rfl]
  simp only [bind_assoc, pure_bind]
  refine bind_congr_of_forall_mem_support _ fun bs hbs => ?_
  have hl := reads_length T key ρ 255 1 bs hbs
  rw [vector_getD (b :: bs) 256 (by simp [hl])]
  rfl

end Draw

/-! ## The draws of the held terms and the digest calls -/

section Terms

variable (self : C.Party) (keyOf : C.Term → HashOutput) (ρ : ℕ)

/-- The draws of the held terms put their entries into the queue, in the order of the terms. -/
theorem prov_termDraws_run : ∀ (l : List C.Term), l.Nodup → ∀ Q : ProvQueue C,
    (simulateQ (provShift D δ) (free (liftComp (termDrawsOn self keyOf ρ l) (LocalSpec C)))).run Q =
      free (liftComp (termDrawsOn self keyOf ρ l) (LocalSpec C)) >>= fun r =>
        pure (r, Q ++ entriesOn self keyOf ρ l fun T => vector 256 (r.getD (l.idxOf T) fun _ => 0))
  | [], _, Q => by simp [termDrawsOn, entriesOn]
  | T :: l, hl, Q => by
    have hT : T ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    have hent : ∀ (f : ℕ → Bit) (rs : List (ℕ → Bit)),
        entriesOn self keyOf ρ (T :: l) (fun T' => vector 256 ((f :: rs).getD ((T :: l).idxOf T') fun _ => 0)) =
          (if self ∈ C.holders T then [(((KeyName.term T, keyOf T), ρ), vector 256 f)] else []) ++
            entriesOn self keyOf ρ l (fun T' => vector 256 (rs.getD (l.idxOf T') fun _ => 0)) := by
      intro f rs
      unfold entriesOn
      rw [List.filterMap_cons]
      have hrest : List.filterMap (fun T' => if self ∈ C.holders T' then
            some (((KeyName.term T', keyOf T'), ρ), vector 256 ((f :: rs).getD ((T :: l).idxOf T') fun _ => 0))
            else none) l =
          List.filterMap (fun T' => if self ∈ C.holders T' then
            some (((KeyName.term T', keyOf T'), ρ), vector 256 (rs.getD (l.idxOf T') fun _ => 0)) else none) l := by
        refine List.filterMap_congr fun T' hT' => ?_
        have hne : T ≠ T' := fun e => hT (e ▸ hT')
        rw [List.idxOf_cons_ne l hne]
        rfl
      rw [hrest]
      by_cases hs : self ∈ C.holders T
      · simp [hs]
      · simp [hs]
    have ih := fun Q' => prov_termDraws_run l hl' Q'
    unfold termDrawsOn at ih ⊢
    rw [List.mapM_cons]
    by_cases hs : self ∈ C.holders T
    · simp only [hs, ↓reduceIte, free_liftComp_bind, free_liftComp_pure, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      rw [prov_prgBits_run D δ T (keyOf T) ρ Q, bind_assoc]
      refine bind_congr fun f => ?_
      simp only [pure_bind]
      rw [ih, bind_assoc]
      refine bind_congr fun rs => ?_
      simp only [pure_bind]
      rw [hent f rs]
      simp only [hs, ↓reduceIte, List.append_assoc, List.singleton_append]
    · simp only [hs, ↓reduceIte, free_liftComp_bind, free_liftComp_pure, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
      rw [ih]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun rs => ?_
      rw [hent _ rs]
      simp only [hs, ↓reduceIte, List.nil_append]

/-- The rewritten salt of a digest call with the entry of its own term. -/
def provAddr (addr : C.Term → List Bit) (T : C.Term) : List Bit :=
  if Private D (((.term T, keyOf T), ρ), addr T) (addr T) then addSalt δ (addr T) else addr T

/-- The digest calls take the entries out, and a call with a private entry goes to the salt plus
`δ`. -/
theorem prov_digests_run (addr : C.Term → List Bit) (hist : C.Term → List Bit) :
    ∀ (l : List C.Term) (Q : ProvQueue C),
      (simulateQ (provShift D δ) (free (liftComp (digestsAt self l addr hist) (LocalSpec C)))).run
          (entriesOn self keyOf ρ l addr ++ Q) =
        (fun ds => (ds, Q)) <$> free (liftComp (digestsAt self l (provAddr D δ keyOf ρ addr) hist) (LocalSpec C))
  | [], Q => by simp [digestsAt, entriesOn]
  | T :: l, Q => by
    have ih := prov_digests_run addr hist l Q
    unfold digestsAt entriesOn at ih ⊢
    rw [List.mapM_cons, List.mapM_cons, List.filterMap_cons]
    by_cases hs : self ∈ C.holders T
    · simp only [hs, ↓reduceIte, List.cons_append, free_liftComp_bind, free_liftComp_hashQuery, free_liftComp_pure,
        simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, map_bind,
        provShift_history_run, bind_map_left]
      refine bind_congr fun x => ?_
      rw [provShift_digest_run, bind_map_left]
      refine bind_congr fun d => ?_
      rw [ih]
      simp only [bind_map_left, map_pure]
    · simp only [hs, ↓reduceIte, free_liftComp_bind, free_liftComp_pure, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, pure_bind, map_bind]
      rw [ih]
      simp only [bind_map_left, map_pure]

/-! ## The shifted block -/

/-- The translation of the draws of the salts of the held terms. -/
def termShift (T : C.Term) : ℕ → Bit :=
  if self ∈ C.holders T then prgShift D (saltShift D δ) (.term T) (keyOf T) ρ 2 256 else 0

theorem shiftQ_termDraws (l : List C.Term) :
    shiftQ D (saltShift D δ) (free (liftComp (termDrawsOn self keyOf ρ l) (LocalSpec C))) =
      free (liftComp (l.mapM fun T => (· + termShift D δ self keyOf ρ T) <$>
        (if self ∈ C.holders T then prgBits (.term T) (keyOf T) ρ 2 256 else pure fun _ => 0)) (LocalSpec C)) := by
  rw [shiftQ_free_liftComp]
  congr 2
  unfold termDrawsOn
  erw [simulateQ_list_mapM]
  congr 1
  funext T
  by_cases hs : self ∈ C.holders T
  · simp only [termShift, hs, ↓reduceIte, shiftRo_prgBits]
  · simp [termShift, hs]

theorem shiftQ_digestsAt (l : List C.Term) (addr : C.Term → List Bit) (hist : C.Term → List Bit) :
    shiftQ D (saltShift D δ) (free (liftComp (digestsAt self l addr hist) (LocalSpec C))) =
      free (liftComp (digestsAt self l addr hist) (LocalSpec C)) := by
  rw [shiftQ_free_liftComp, shiftRo_of_noStream D _ _ (noStream_digestsAt self l addr hist)]

theorem digestsAt_congr (l : List C.Term) {addr addr' : C.Term → List Bit} (hist : C.Term → List Bit)
    (h : ∀ T, self ∈ C.holders T → addr T = addr' T) : digestsAt self l addr hist = digestsAt self l addr' hist := by
  unfold digestsAt
  congr 1
  funext T
  by_cases hs : self ∈ C.holders T
  · simp only [hs, ↓reduceIte, h T hs]
  · simp only [hs, ↓reduceIte]

theorem free_liftComp_map {α β : Type} (f : α → β) (X : OracleComp (RoSpec C) α) :
    free (liftComp (f <$> X) (LocalSpec C)) = f <$> free (liftComp X (LocalSpec C)) := by
  rw [map_eq_bind_pure_comp, free_liftComp_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_def, free_liftComp_pure]

/-- The rewritten salt of a held term is the shifted salt. -/
theorem provAddr_eq (F : ℕ → Bit) (T : C.Term) (hs : self ∈ C.holders T) :
    provAddr D δ keyOf ρ (fun _ => vector 256 F) T = vector 256 (F + termShift D δ self keyOf ρ T) := by
  have hlen : (vector 256 F).length = 256 := by simp only [vector, List.length_map, List.length_range]
  unfold provAddr
  by_cases hT : Hidden D (KeyName.term T)
  · have hp : Private D (((KeyName.term T, keyOf T), ρ), vector 256 F) (vector 256 F) := ⟨hT, hlen, rfl⟩
    rw [ite_eq_left_iff.2 fun h => absurd hp h]
    refine List.ext_getElem (by simp only [addSalt, vector, List.length_ofFn, List.length_map, List.length_range])
      fun k h₁ h₂ => ?_
    have hk : k < 256 := by simpa only [addSalt, List.length_ofFn] using h₁
    have hσ : saltShift D δ ((KeyName.term T, keyOf T), ρ, 2, k) = δ ⟨k, hk⟩ := by
      have h : ¬ KnownTo D.1 T ∧ (2 : ℕ) = 2 ∧ k < 256 := ⟨hT, rfl, hk⟩
      simp only [saltShift, h, not_false_eq_true, and_self, ↓reduceDIte]
    simp only [addSalt, vector, List.getElem_ofFn, List.getElem_map, List.getElem_range, Pi.add_apply,
      RealNetworkN3.getD_map_range, hk, ↓reduceIte, termShift, hs, prgShift, hT, and_self, hσ]
  · have hp : ¬ Private D (((KeyName.term T, keyOf T), ρ), vector 256 F) (vector 256 F) := fun h => hT h.1
    rw [ite_eq_right_iff.2 fun h => absurd h hp]
    show vector 256 F = _
    congr 1
    funext g
    simp only [Pi.add_apply, termShift, hs, ↓reduceIte, prgShift, hT, false_and, add_zero]

/-- The block of a check from the empty queue is the shifted block and ends with the empty queue. -/
theorem prov_block {Z β : Type} (pairs : OracleComp (RoSpec C) Z)
    (hpairs : NoCall (fun t => Touch (C := C) (.inr (.inr t))) pairs) (hist : C.Term → List Bit)
    (k : Z → List HashOutput → OracleComp (WorldSpec C) β) (hk : ∀ z ds, Prov D δ [] (k z ds)) :
    Prov D δ [] (free (liftComp (termDrawsOn self keyOf ρ C.terms) (LocalSpec C)) >>= fun r =>
      free (liftComp pairs (LocalSpec C)) >>= fun z =>
        free (liftComp (digestsAt self C.terms (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) hist)
          (LocalSpec C)) >>= fun ds => k z ds) := by
  have hnd : (C.terms).Nodup := Finset.nodup_toList _
  have hpw := noTouch_free_liftComp pairs hpairs
  unfold Prov
  rw [simulateQ_bind, StateT.run_bind, prov_termDraws_run D δ self keyOf ρ C.terms hnd [], bind_assoc]
  simp only [pure_bind, List.nil_append]
  rw [shiftQ_bind, shiftQ_termDraws, map_bind]
  -- the left side as a function of the salts
  have hL : ∀ r : List (ℕ → Bit), (simulateQ (provShift D δ) (free (liftComp pairs (LocalSpec C)) >>= fun z =>
      free (liftComp (digestsAt self C.terms (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) hist)
        (LocalSpec C)) >>= fun ds => k z ds)).run
        (entriesOn self keyOf ρ C.terms fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) =
      free (liftComp pairs (LocalSpec C)) >>= fun z =>
        free (liftComp (digestsAt self C.terms (provAddr D δ keyOf ρ
          (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0))) hist) (LocalSpec C)) >>= fun ds =>
            (fun a => (a, [])) <$> shiftQ D (saltShift D δ) (k z ds) := by
    intro r
    rw [simulateQ_bind, StateT.run_bind, prov_of_noTouch D δ _ _ hpw, shiftQ_of_noTouch D δ _ hpw, bind_map_left]
    refine bind_congr fun z => ?_
    have hd := prov_digests_run D δ self keyOf ρ (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) hist
      C.terms []
    rw [List.append_nil] at hd
    rw [simulateQ_bind, StateT.run_bind, hd, bind_map_left]
    exact bind_congr fun ds => hk z ds
  simp only [hL]
  -- the right side as a function of the salts
  let G : (ℕ → (ℕ → Bit)) → OracleComp (WorldSpec C) (β × ProvQueue C) := fun Fn =>
    free (liftComp pairs (LocalSpec C)) >>= fun z =>
      free (liftComp (digestsAt self C.terms (fun T => vector 256 (Fn (C.terms.idxOf T))) hist)
        (LocalSpec C)) >>= fun ds => (fun a => (a, [])) <$> shiftQ D (saltShift D δ) (k z ds)
  have hR : ∀ r : List (ℕ → Bit), (fun a => (a, ([] : ProvQueue C))) <$> shiftQ D (saltShift D δ)
      (free (liftComp pairs (LocalSpec C)) >>= fun z =>
        free (liftComp (digestsAt self C.terms (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) hist)
          (LocalSpec C)) >>= fun ds => k z ds) = G fun i => r.getD i 0 := by
    intro r
    rw [shiftQ_bind, shiftQ_of_noTouch D δ _ hpw, map_bind]
    refine bind_congr fun z => ?_
    rw [shiftQ_bind, shiftQ_digestsAt, map_bind]
    rfl
  simp only [hR]
  have e : ∀ X : OracleComp (WorldSpec C) (List (ℕ → Bit)),
      (X >>= fun a => G fun i => a.getD i 0) = ((fun r i => r.getD i 0) <$> X) >>= G :=
    fun X => (bind_map_left _ _ _).symm
  rw [e, ← free_liftComp_map, map_getD_mapM_add, free_liftComp_map, bind_map_left]
  refine bind_congr fun r => ?_
  refine bind_congr fun z => ?_
  rw [digestsAt_congr self C.terms hist (addr' := fun T => vector 256 ((fun g => r.getD g 0 +
    (C.terms.map (termShift D δ self keyOf ρ)).getD g 0) (C.terms.idxOf T))) fun T hs => ?_]
  have hmem : T ∈ C.terms := Finset.mem_toList.mpr (Finset.mem_univ T)
  have hget : (C.terms.map (termShift D δ self keyOf ρ)).getD (C.terms.idxOf T) 0 = termShift D δ self keyOf ρ T :=
    list_map_getD_idxOf C.terms _ _ T hmem
  change provAddr D δ keyOf ρ (fun T => vector 256 (r.getD (C.terms.idxOf T) fun _ => 0)) T =
    vector 256 (r.getD (C.terms.idxOf T) 0 + (C.terms.map (termShift D δ self keyOf ρ)).getD (C.terms.idxOf T) 0)
  rw [hget]
  exact provAddr_eq D δ self keyOf ρ (r.getD (C.terms.idxOf T) fun _ => 0) T hs

end Terms

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.prov_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.prov_block
