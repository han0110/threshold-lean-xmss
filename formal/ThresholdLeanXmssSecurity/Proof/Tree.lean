import ThresholdLeanXmssSecurity.Proof.Main
import ThresholdLeanXmssSecurity.Proof.SeedGen
import ThresholdLeanXmssSecurity.Proof.Check

/-!
# The ceremonies of a tree

`jointTreeRun_toReal_le` bounds the probability that the honest run of the ceremonies of a tree,
batch by batch, differs from the dealer of the tree. `setup_chunks_step` joins the two ceremonies of a bottom tree. The second PRSS setup keeps the
cache invariant `CacheOK`, and the counters continue. The dealer claims `DealerTreeCorrectnessStatement` and
`DealerTreeSuccessStatement` follow from `dealerTreeCorrectness` and `dealerTreeSuccess` in `Dealer`.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

/-! ## Tree completeness, the statement as two local runs -/

namespace ThresholdLeanXmssSecurity

open scoped ENNReal

attribute [local instance] Classical.propDecidable

section TreeStatement

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The real ceremonies of a tree on dealt keys as a local computation. -/
def realTree (top : TopTree) (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) : OracleComp (LocalSpec C) (C.Party → Option TreeOutput) :=
  honestStart (fun i => (newTree K circuits settings i (dealtKeys parameter seeds pairKeys i) top tree :
      PartyM C E RealSpec TreeOutput)) >>=
    honestRounds noFunctionality (fun l => l.elim) (setupRounds + ceremonyFuel circuits settings)

/-- The dealer of a tree as a local computation, with its output at every operator. -/
def idealTree (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    OracleComp (LocalSpec C) (C.Party → Option TreeOutput) :=
  liftComp ((fun r (_ : C.Party) => r.1) <$> dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C)

/-- The dealer of a tree, then the real ceremonies of the tree, from the cache `s`. The first output
is the real one. -/
def jointTreeRun (top : TopTree) (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (s : HashCache C) : ProbComp ((C.Party → Option TreeOutput) × (C.Party → Option TreeOutput)) :=
  (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree >>= fun a =>
    realTree K circuits settings top tree parameter seeds pairKeys >>= fun z => pure (z, a))).run' s

end TreeStatement

/-! ## Tree completeness, the PRSS setup of an honest ceremony -/

section PrssSetup

variable {C : Committee} {E : Type} (prims : Primitives) {I O L R α : Type}

theorem prssSetup_eq (i : C.Party) :
    (prssSetup i : PartyM C E (CallSpec I O) (PrssKeys C)) =
      localStep (liftComp sampleParts _) >>= fun own =>
        commitRevealEcho .prss i own >>= fun keys => pure ⟨keys.2.1, keys.2.2⟩ := rfl

/-- The PRSS keys of operator `i` in an honest setup with `H` fixed to `h`. -/
def honestPrssKeys (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) : PrssKeys C :=
  ⟨fun T => if i ∈ C.holders T then h (termInput .prss parts T) else 0,
    fun j => if hj : j = i then 0 else h (pairInput .prss parts (C.pairOf i j (Ne.symm hj)))⟩

end PrssSetup

/-! ## Tree completeness, the real building blocks with `H` fixed -/

section RealBuildingBlocks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) {ι : Type} {G : OracleSpec ι}

/-- The terms `r_T` that operator `ctx.self` draws in round `ρ`. -/
def termDraws {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (List (ℕ → R)) :=
  C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) ρ idx count else pure fun _ => 0

/-- The pair streams `Z_ij` that operator `ctx.self` draws in round `ρ`. -/
def pairDraws {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (List (ℕ → R)) :=
  C.parties.mapM fun j => if h : j = ctx.self then pure fun _ => 0
    else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) ρ idx count

omit [Field E] [Algebra Bit E] in
theorem prssRandomness_eq {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) :
    (prssRandomness (G := G) ctx codec idx count) = (do
      let ρ ← freshLabel
      let r ← StateT.lift (oracleStep (termDraws ctx codec ρ idx count))
      let Z ← StateT.lift (oracleStep (pairDraws ctx codec ρ idx count))
      pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)) := rfl

end RealBuildingBlocks

/-! ### An honest peer reshare -/

section HonestReshare

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {R : Type} [Field R]

/-- The terms of an honest PRSS round at operator `i`. -/
def honestR (rr : C.Term → ℕ → R) (i : C.Party) : Shares C R :=
  fun T => if i ∈ C.holders T then rr T else fun _ => 0

/-- The pair streams of an honest PRSS round at operator `i`. -/
def honestZ (zz : C.Pair → ℕ → R) (i : C.Party) : C.Party → ℕ → R :=
  fun j => if hj : j = i then fun _ => 0 else zz (C.pairOf i j (Ne.symm hj))

variable (ctx : C.Party → Context C) (rr : C.Term → ℕ → R) (zz : C.Pair → ℕ → R) (v : C.Party → ℕ → R)

/-- The sharing that an honest peer reshare gives, before the restriction to the held terms. -/
def honestShare (T : C.Term) (g : ℕ) : R :=
  if T ∈ filledTerms K then
    ∑ j ∈ Finset.univ.filter (K.filled · = T), reshareU K (ctx j) (honestR rr j) (honestZ zz j) (v j) g
  else rr T g

/-- An honest peer reshare shares the sum of the inputs (GS20, Lemma 4, with no corrupt operator). -/
theorem sum_honestShare [CharP R 2] (hctx : ∀ i, (ctx i).self = i) (g : ℕ) :
    ∑ T, honestShare K ctx rr zz v T g = ∑ i, v i g := by
  set u := fun j => reshareU K (ctx j) (honestR rr j) (honestZ zz j) (v j) g
  have hfill : ∑ T ∈ filledTerms K, ∑ j ∈ Finset.univ.filter (K.filled · = T), u j = ∑ j, u j := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := filledTerms K) (g := K.filled)
      (fun j _ => by simp [filledTerms])]
  have hpairs : ∑ j : C.Party, ∑ k ∈ Finset.univ.erase (ctx j).self, honestZ zz j k g = 0 := by
    have := sum_pairs_eq_zero (R := R) (C := C) Finset.univ fun p => zz p g
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [dite_eq_left rfl, add_zero, hctx]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp only [honestZ, dite_eq_right hki, dite_eq_right (Ne.symm hki)]
  have hown : ∑ j : C.Party, ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = (ctx j).self),
      honestR rr j T g = ∑ T ∈ Finset.univ.filter (· ∉ filledTerms K), rr T g := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (· ∉ filledTerms K))
      (t := Finset.univ) (g := K.owner) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hctx, Finset.filter_filter]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT' := (Finset.mem_filter.mp hT).2
    simp only [honestR, ite_eq_left (hT'.2 ▸ K.owner_held T)]
  have hu : ∑ j, u j = ∑ i, v i g + ∑ T ∈ Finset.univ.filter (· ∉ filledTerms K), rr T g := by
    simp only [u, reshareU, Finset.sum_add_distrib, hpairs, add_zero, hown]
  unfold honestShare
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, hfill, hu, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

/-- Each honest operator gets its held terms of `honestShare`. -/
theorem reshareZ_honest (codec : Codec C E R) (hcodec : CodecRoundTrip codec) (hctx : ∀ i, (ctx i).self = i)
    (count : ℕ) (i : C.Party) (T : C.Term) (g : ℕ) :
    reshareZ K (ctx i) codec (honestR rr i) (honestZ zz i) (v i) count
        (fun k => reshareOut K (ctx k) codec (honestR rr k) (honestZ zz k) (v k) count i) T g =
      if i ∈ C.holders T ∧ g < count then honestShare K ctx rr zz v T g else 0 := by
  unfold reshareZ honestShare
  rw [hctx]
  by_cases hiT : i ∈ C.holders T
  · by_cases hg : g < count
    · have h1 : ¬ (i ∉ C.holders T ∨ count ≤ g) := by simp [hiT]; omega
      rw [ite_eq_right h1, ite_eq_left (show i ∈ C.holders T ∧ g < count from ⟨hiT, hg⟩)]
      by_cases hT : T ∈ filledTerms K
      · simp only [hT, ite_true]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjT : K.filled j = T := (Finset.mem_filter.mp hj).2
        by_cases hji : j = i
        · rw [ite_eq_left hji, hji]
        · rw [ite_eq_right hji]
          have h2 : j ≠ (ctx j).self → False := fun h => h (hctx j).symm
          simp only [reshareOut, hctx, ne_eq, Ne.symm hji, not_false_eq_true, hjT, hiT, and_self, ite_true]
          rw [(hcodec _ g).1, List.getD_eq_getElem?_getD, vector, List.getElem?_map, List.getElem?_range hg]
          rfl
      · simp [hT, honestR, hiT]
    · rw [ite_eq_left (Or.inr (by omega)), ite_eq_right (by tauto)]
  · rw [ite_eq_left (Or.inl hiT), ite_eq_right (by tauto)]

end HonestReshare

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RunFacts

variable {C : Committee} (prims : Primitives)

/-- A run of computations of `H` and `PRG` of all operators gives the values with one `H` that is
`Th` on the inputs of the MPC and agrees with the final cache. -/
theorem localRun_D {β : Type} {n : ℕ} (oa : Fin n → OracleComp (RoSpec C) β) (s : HashCache C) (hs : NoMpc s)
    (z) (hz : z ∈ support ((simulateQ (localAnswer prims)
      (OverPermutation.sequenceFin fun i => liftComp (oa i) (LocalSpec C))).run s)) :
    s ≤ z.2 ∧ NoMpc z.2 ∧ ∃ h, Good prims h ∧ Agrees h z.2 ∧ ∀ i, z.1 i = D prims h (oa i) := by
  obtain ⟨hle, hn, hsupp⟩ := localRun_support _ s z hz
  have hn' := hn hs
  refine ⟨hle, hn', hashOf prims z.2, good_hashOf prims z.2, agrees_hashOf prims hn', ?_⟩
  have := hsupp _ (good_hashOf prims z.2) (agrees_hashOf prims hn')
  rw [simulateQ_sequenceFin] at this
  simp only [simulateQ_fixedLocal_liftComp] at this
  rw [sequenceFin_pure] at this
  simp only [support_pure, Set.mem_singleton_iff] at this
  intro i
  rw [this]

/-- A run of one computation of `H` and `PRG`. -/
theorem localRun_D_one {β : Type} (oa : OracleComp (RoSpec C) β) (s : HashCache C) (hs : NoMpc s)
    (z) (hz : z ∈ support ((simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s)) :
    s ≤ z.2 ∧ NoMpc z.2 ∧ ∃ h, Good prims h ∧ Agrees h z.2 ∧ z.1 = D prims h oa := by
  obtain ⟨hle, hn, hsupp⟩ := localRun_support _ s z hz
  have hn' := hn hs
  refine ⟨hle, hn', hashOf prims z.2, good_hashOf prims z.2, agrees_hashOf prims hn', ?_⟩
  have := hsupp _ (good_hashOf prims z.2) (agrees_hashOf prims hn')
  rw [simulateQ_fixedLocal_liftComp] at this
  simpa using this

/-- A coin key or an expansion, the queries that the bounds of the checks track. -/
def IsCoin (q : Query C) : Prop := (∃ k idx, q = .expand k idx) ∨ (∃ tag ρ v, q = .coinKey tag ρ v)

/-- A computation of `H` and `PRG` that keeps the coin entries of the cache. -/
def FrameR {β : Type} (oa : OracleComp (RoSpec C) β) : Prop :=
  ∀ s z, z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) oa).run s) →
    ∀ q, IsCoin q → z.2 q = s q

/-- A local computation that keeps the coin entries of the cache. -/
def FrameL {β : Type} (oa : OracleComp (LocalSpec C) β) : Prop :=
  ∀ s z, z ∈ support ((simulateQ (localAnswer prims) oa).run s) → ∀ q, IsCoin q → z.2 q = s q

variable {prims}

theorem FrameR.pure {β : Type} (b : β) : FrameR prims (pure b : OracleComp (RoSpec C) β) := by
  intro s z hz q _
  simp at hz; rw [hz]

theorem FrameR.bind {β γ : Type} {oa : OracleComp (RoSpec C) β} {f : β → OracleComp (RoSpec C) γ}
    (h : FrameR prims oa) (hf : ∀ b, FrameR prims (f b)) : FrameR prims (oa >>= f) := by
  intro s z hz q hq
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rw [hf y.1 y.2 z hz q hq, h s y hy q hq]

theorem FrameR.map {β γ : Type} {oa : OracleComp (RoSpec C) β} (f : β → γ) (h : FrameR prims oa) :
    FrameR prims (f <$> oa) := by
  rw [map_eq_bind_pure_comp]; exact h.bind fun _ => FrameR.pure _

theorem FrameR.hashQuery {q : Query C} (hq : ¬ IsCoin q) : FrameR prims (hashQuery q) := by
  intro s z hz q' hq'
  have hne : q' ≠ q := fun e => hq (e ▸ hq')
  by_cases hfix : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hfix
    have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (ThresholdLeanXmss.hashQuery (.hash input)) =
        hashAnswer prims (.hash input) := (simulateQ_query _ _).trans (id_map _)
    rw [h1, hashAnswer_of_isFixed prims hm] at hz
    simp at hz; rw [hz]
  · rcases hs : s q' with _ | u
    · by_contra hc
      rcases support_hashQuery_entries prims hfix s z hz q' hc with h | h
      · exact h hs
      · exact hne h
    · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (ThresholdLeanXmss.hashQuery q) =
          hashAnswer prims q := (simulateQ_query _ _).trans (id_map _)
      rw [h1] at hz
      exact grows_hashAnswer prims q s z hz hs

theorem FrameR.prg (x : PrgInput C) :
    FrameR prims (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) := by
  intro s z hz q hq
  have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) = prgAnswer prims x :=
    (simulateQ_query _ _).trans (id_map _)
  rw [h1] at hz
  simp [prgAnswer] at hz
  obtain ⟨a, b, hp, rfl⟩ := hz
  have h2 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (ThresholdLeanXmss.hashQuery (.streamKey x.2.1)) = hashAnswer prims (.streamKey x.2.1) :=
    (simulateQ_query _ _).trans (id_map _)
  exact FrameR.hashQuery (prims := prims) (q := .streamKey x.2.1)
    (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h) s (a, b) (by rw [h2]; exact hp) q hq

theorem FrameR.mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, FrameR prims (f a)) :
    ∀ l : List α, FrameR prims (l.mapM f)
  | [] => FrameR.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (FrameR.mapM f hf l).bind fun _ => FrameR.pure _

theorem FrameR.ite {β : Type} (c : Prop) [Decidable c] {a b : OracleComp (RoSpec C) β}
    (ha : FrameR prims a) (hb : FrameR prims b) : FrameR prims (if c then a else b) := by
  split_ifs <;> assumption

theorem FrameR.tweakable {β : Type} (oa : OracleComp HashSpec β) : FrameR prims (tweakable (C := C) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b => exact FrameR.pure b
  | query_bind t k ih =>
    unfold ThresholdLeanXmss.tweakable at ih ⊢
    rw [simulateQ_bind]
    refine FrameR.bind ?_ ih
    rw [simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)

theorem FrameL.liftComp {β : Type} {oa : OracleComp (RoSpec C) β} (h : FrameR prims oa) :
    FrameL prims (liftComp oa (LocalSpec C)) := by
  intro s z hz
  rw [simulateQ_localAnswer_liftComp] at hz
  exact h s z hz

theorem FrameL.pure {β : Type} (b : β) : FrameL prims (pure b : OracleComp (LocalSpec C) β) := by
  intro s z hz q _
  simp at hz; rw [hz]

theorem FrameL.bind {β γ : Type} {oa : OracleComp (LocalSpec C) β} {f : β → OracleComp (LocalSpec C) γ}
    (h : FrameL prims oa) (hf : ∀ b, FrameL prims (f b)) : FrameL prims (oa >>= f) := by
  intro s z hz q hq
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rw [hf y.1 y.2 z hz q hq, h s y hy q hq]

theorem FrameL.sequenceFin {β : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) β),
    (∀ i, FrameL prims (f i)) → FrameL prims (OverPermutation.sequenceFin f)
  | 0, f, _ => by simp only [OverPermutation.sequenceFin]; exact FrameL.pure _
  | n + 1, f, hf => by
    simp only [OverPermutation.sequenceFin]
    exact (hf 0).bind fun _ => (FrameL.sequenceFin _ fun i => hf i.succ).bind fun _ => FrameL.pure _

theorem cacheOK_of_frame {Ks : Finset HashOutput} {L : ℕ} {s s' : HashCache C} (hs : CacheOK Ks L s)
    (h : ∀ q, IsCoin q → s' q = s q) : CacheOK Ks L s' := by
  intro q hq
  refine ⟨fun k idx hk => ?_, fun tag ρ v hk => ?_⟩
  · have hc : IsCoin q := Or.inl ⟨k, idx, hk⟩
    exact (hs q (by rw [← h q hc]; exact hq)).1 k idx hk
  · have hc : IsCoin q := Or.inr ⟨tag, ρ, v, hk⟩
    exact (hs q (by rw [← h q hc]; exact hq)).2 tag ρ v hk

end RunFacts

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The PRSS outputs that operator `ctx.self` draws in round `ρ`. -/
def prssDraw {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (PrssOutput C R) := do
  let r ← termDraws ctx codec ρ idx count
  let Z ← pairDraws ctx codec ρ idx count
  pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)

omit [Field E] [Algebra Bit E] in
@[simp] theorem oracleStep_pure {α : Type} (a : α) :
    (oracleStep (C := C) (E := E) (G := G) (pure a : OracleComp (RoSpec C) α)) = pure a := by
  simp [oracleStep, localStep]

/-- The state after one round label. -/
def nextLabel (st : RunState C) : RunState C := ⟨st.history, st.label + 1, st.tag⟩

omit [Field E] [Algebra Bit E] in
theorem prssRandomness_run {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ)
    {α : Type} (f : PrssOutput C R → RunM C E G α) (st : RunState C) :
    (prssRandomness ctx codec idx count >>= f).run st =
      oracleStep (prssDraw ctx codec st.label idx count) >>= fun o => (f o).run (nextLabel st) := by
  simp only [prssRandomness_eq, prssDraw, freshLabel, bind_assoc, oracleStep_bind]
  simp [StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, nextLabel]

def openShareN (i : C.Party) (v : ℕ → E) (inbox : Mail C E) : C.Party → ℕ → E := fun j g =>
  if j = i then v g else Msg.elementAt (inbox j) g

def OpenAgreesN (i : C.Party) (v : ℕ → E) (count : ℕ) (inbox : Mail C E) : Prop :=
  ∀ j : C.Party, ∀ g < count, openShareN i v inbox j g =
    ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K (K.point j) l * openShareN i v inbox l g

def openValueN (i : C.Party) (v : ℕ → E) (inbox : Mail C E) : ℕ → E := fun g =>
  ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * openShareN i v inbox l g

theorem openSh_eqN (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    (openSh (G := G) K ctx v count) = exchange (openOut ctx.self v count) >>= fun inbox =>
      require (OpenAgreesN K ctx.self v count inbox) >>= fun _ => pure (openValueN K ctx.self v inbox) := rfl

omit [Algebra Bit E] in
theorem openShareN_honest (v : C.Party → ℕ → E) (count : ℕ) (i j : C.Party) (g : ℕ) (hg : g < count) :
    openShareN i (v i) (fun k => openOut (E := E) k (v k) count i) j g = v j g := by
  unfold openShareN
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, openOut, Ne.symm hj, Msg.elementAt, vector, hg]

theorem openShN_honest (v : C.Party → ℕ → E) (vals : ℕ → E) (count : ℕ)
    (hv : ∀ g < count, IsShamir K (fun i => v i g) (vals g)) (i : C.Party) :
    OpenAgreesN K i (v i) count (fun k => openOut (E := E) k (v k) count i) ∧
      ∀ g < count, openValueN K i (v i) (fun k => openOut (E := E) k (v k) count i) g = vals g := by
  constructor
  · intro j g hg
    obtain ⟨P, hP, -, hPi⟩ := hv g hg
    simp only [openShareN_honest v count i _ g hg, hPi]
    exact (sum_lagrangeFirst_mul_eval K P hP _).symm
  · intro g hg
    obtain ⟨P, hP, hP0, hPi⟩ := hv g hg
    simp only [openValueN, openShareN_honest v count i _ g hg, hPi]
    rw [sum_lagrangeFirst_mul_eval K P hP, hP0]

omit [Field E] [Algebra Bit E] in
theorem isAbort_openOutboxN (k : C.Party) (v : ℕ → E) (count : ℕ) (j : C.Party) :
    Msg.isAbort (openOut (E := E) k v count j) = false := by
  unfold openOut; split_ifs <;> rfl

end RealSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealRuns

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The running values after `record` of a peer reshare at operator `i`. -/
def recordPeer {R : Type} (codec : Codec C E R) (i : C.Party) (h : C.Term → List Bit) (z : Shares C R) (count : ℕ) :
    C.Term → List Bit := fun T =>
  if i ∈ C.holders T then
    h T ++ ((List.range count).filter fun g => (filler K .peer T g).isSome).flatMap (codec.toBits ∘ z T)
  else h T

theorem reshare_run {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R) (r : Shares C R)
    (Zs : C.Party → ℕ → R) (v : ℕ → R) (count : ℕ) (st : RunState C) :
    (reshare (G := G) K ctx codec (r, Zs) v count).run st =
      exchange (reshareOut K ctx codec r Zs v count) >>= fun inbox =>
        pure (reshareZ K ctx codec r Zs v count inbox,
          ⟨recordPeer K codec ctx.self st.history (reshareZ K ctx codec r Zs v count inbox) count, st.label, st.tag⟩) := by
  unfold reshare
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  simp only [record, StateT.run_modify, StateT.run_pure, pure_bind]
  rfl

/-- The products of an extended multiplication as additive shares. -/
def contextProductValues (ctx : Context C) (products : List (Product C E)) : ℕ → E :=
  fun g => match products[g]? with | some p => productShare K ctx p | none => 0

theorem realExtendMult_run (ctx : Context C) (products : List (Product C E)) (st : RunState C) :
    ((realCheckBuildingBlocks (G := G) K ctx).extendMult products).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 0 products.length) >>= fun o =>
        exchange (reshareOut K ctx (elementCodec K) o.1 o.2 (contextProductValues K ctx products) products.length) >>=
          fun inbox => pure (reshareZ K ctx (elementCodec K) o.1 o.2 (contextProductValues K ctx products) products.length inbox,
            ⟨recordPeer K (elementCodec K) ctx.self st.history (reshareZ K ctx (elementCodec K) o.1 o.2
              (contextProductValues K ctx products) products.length inbox) products.length, st.label + 1, st.tag⟩) := by
  have := prssRandomness_run (G := G) ctx (elementCodec K) 0 products.length
    (fun o => reshare K ctx (elementCodec K) o (contextProductValues K ctx products) products.length) st
  exact this.trans (congrArg (_ >>= ·) (funext fun o => by
    rw [show o = (o.1, o.2) from rfl, reshare_run]; rfl))

theorem realCoin_run (ctx : Context C) (count : ℕ) (st : RunState C) :
    ((realCheckBuildingBlocks (G := G) K ctx).coin count).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 count) >>= fun o =>
        openSh K ctx (conv K ctx o.1) count >>= fun opened => pure (vector count opened, nextLabel st) := by
  have := prssRandomness_run (G := G) ctx (elementCodec K) 1 count (fun o => coinWith K ctx o count) st
  simp only [realCheckBuildingBlocks]
  rw [this]
  refine congrArg (_ >>= ·) (funext fun o => ?_)
  simp [coinWith, StateT.run_lift]

theorem realRand_run {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) (st : RunState C) :
    (prssRandomness (G := G) ctx codec idx count).run st =
      oracleStep (prssDraw ctx codec st.label idx count) >>= fun o => pure (o, nextLabel st) := by
  have := prssRandomness_run (G := G) ctx codec idx count pure st
  simpa using this

theorem realChallenge_run (ctx : Context C) (st : RunState C) :
    (challenge K (realCheckBuildingBlocks (G := G) K ctx)).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 2) >>= fun o =>
        openSh K ctx (conv K ctx o.1) 2 >>= fun opened =>
          oracleStep (challengeQuery K st.tag st.label (vector 2 opened)) >>= fun r => match r with
            | some r => pure (r, nextLabel st)
            | none => failure := by
  simp only [challenge, coinKey, challengeQuery, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  rw [realCoin_run]
  simp only [bind_assoc, pure_bind, oracleStep_bind]
  refine congrArg (_ >>= ·) (funext fun o => congrArg (_ >>= ·) (funext fun opened => ?_))
  simp only [StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun key => congrArg (_ >>= ·) (funext fun r => ?_))
  rcases r with _ | r
  · simp [StateT.run_lift]
  · rfl

theorem realTau_run (ctx : Context C) (count : ℕ) (st : RunState C) :
    (coinKey K (realCheckBuildingBlocks (G := G) K ctx) >>= fun key => expand K key count).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 2) >>= fun o =>
        openSh K ctx (conv K ctx o.1) 2 >>= fun opened =>
          oracleStep (tauQuery K st.tag st.label (vector 2 opened) count) >>= fun τ => pure (τ, nextLabel st) := by
  simp only [coinKey, expand, tauQuery, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  rw [realCoin_run]
  simp only [bind_assoc, pure_bind, oracleStep_bind]
  refine congrArg (_ >>= ·) (funext fun o => congrArg (_ >>= ·) (funext fun opened => ?_))
  simp [StateT.run_lift]

end RealRuns

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section PrssValues

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives)

/-- Operator `i` with its keys and the PRSS keys `kT` of its held terms and `kP` of its pairs. -/
def prssCtx (keys : C.Party → Keys C) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party) :
    Context C :=
  ⟨i, keys i, ⟨fun T => if i ∈ C.holders T then kT T else 0,
    fun j => if hj : j = i then 0 else kP (C.pairOf i j (Ne.symm hj))⟩⟩

omit [Field E] [Algebra Bit E] in
theorem D_prssDraw {R : Type} [Field R] (h : Query C → HashOutput) (keys : C.Party → Keys C)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party) (codec : Codec C E R) (ρ idx count : ℕ) :
    D prims h (prssDraw (prssCtx keys kT kP i) codec ρ idx count) =
      (honestR (fun T => D prims h (codec.draw (.term T) (kT T) ρ idx count)) i,
        honestZ (fun p => D prims h (codec.draw (.pair p) (kP p) ρ idx count)) i) := by
  unfold prssDraw
  simp only [D_bind, D_pure]
  refine Prod.ext (funext fun T => ?_) (funext fun j => ?_)
  · show (D prims h (termDraws _ codec ρ idx count)).getD (C.terms.idxOf T) (fun _ => 0) = _
    unfold termDraws
    rw [D_mapM, getD_terms_idxOf]
    by_cases hi : i ∈ C.holders T
    · simp [honestR, prssCtx, hi]
    · simp [honestR, prssCtx, hi, D_pure]
  · show (D prims h (pairDraws _ codec ρ idx count)).getD j.val (fun _ => 0) = _
    unfold pairDraws
    rw [D_mapM, getD_parties]
    by_cases hj : j = i
    · simp [honestZ, prssCtx, hj, D_pure]
    · simp [honestZ, prssCtx, hj]

variable {prims}

theorem FrameR.prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    FrameR prims (prgBits name key ρ idx count) := by
  unfold ThresholdLeanXmss.prgBits
  exact (FrameR.mapM _ (fun position => FrameR.prg (name, key, ρ, idx, position)) _).bind fun _ => FrameR.pure _

omit [Field E] [Algebra Bit E] in
theorem FrameR.bitDraw (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    FrameR prims ((bitCodec (C := C) (E := E)).draw name key ρ idx count) := FrameR.prgBits _ _ _ _ _

theorem FrameR.elementDraw (K : Constants C E) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    FrameR prims ((elementCodec K).draw name key ρ idx count) :=
  (FrameR.prgBits _ _ _ _ _).bind fun _ => FrameR.pure _

omit [Field E] [Algebra Bit E] in
theorem FrameR.prssDraw {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (hdraw : ∀ name key ρ idx count, FrameR prims (codec.draw name key ρ idx count)) (ρ idx count : ℕ) :
    FrameR prims (prssDraw ctx codec ρ idx count) := by
  unfold ThresholdLeanXmssSecurity.prssDraw termDraws pairDraws
  refine (FrameR.mapM _ (fun T => FrameR.ite _ (hdraw _ _ _ _ _) (FrameR.pure _)) _).bind fun _ =>
    (FrameR.mapM _ (fun j => ?_) _).bind fun _ => FrameR.pure _
  split_ifs
  · exact FrameR.pure _
  · exact hdraw _ _ _ _ _

end PrssValues

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section DrawStep

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after an own computation of `H` and `PRG` of each operator that keeps the
coin entries. Each operator continues with the value of its computation under one `H`. -/
theorem draw_step {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (RoSpec C) β) (hframe : ∀ i, FrameR prims (oa i))
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (h₀ : Query C → HashOutput) (s' : HashCache C), Good prims h₀ → Agrees h₀ s' → NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (D prims h₀ (oa i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  refine probEvent_honest_local prims F reply fuel oa g event s ε fun z hz => ?_
  obtain ⟨hle, hn', h₀, hg, ha, hv⟩ := localRun_D prims oa s hn z hz
  have hfr := FrameL.sequenceFin (prims := prims) (fun i => liftComp (oa i) (LocalSpec C))
    (fun i => FrameL.liftComp (hframe i)) s z hz
  have : z.1 = fun i => D prims h₀ (oa i) := funext hv
  rw [this]
  exact h h₀ z.2 hg ha hn' hle hfr

end DrawStep

section RealBuildingBlockSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type} (prims : Primitives)
  (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput)

theorem vector_congr' {R' : Type} (count : ℕ) (a b : ℕ → R') (h : ∀ g < count, a g = b g) :
    vector count a = vector count b := by
  unfold vector
  exact List.map_congr_left fun g hg => h g (List.mem_range.1 hg)

theorem conv_prssCtx (i : C.Party) (x : Shares C E) :
    conv K (prssCtx keys kT kP i) x = conv K (localContext i) x := rfl

/-- An honest opening of a Shamir vector. Every operator continues with the opened values. -/
theorem openSh_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (v : C.Party → ℕ → E) (vals : ℕ → E) (count : ℕ) (hv : ∀ g < count, IsShamir K (fun i => v i g) (vals g))
    (g : C.Party → (ℕ → E) → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (ε : ℝ≥0∞)
    (h : Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (openValueN K i (v i) (fun k => openOut (E := E) k (v k) count i))) >>=
          honestRounds F reply fuel)).run' s}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => openSh K (localContext i) (v i) count >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  simp only [openSh_eqN, bind_assoc, localContext]
  rw [honestRounds_exchange F reply fuel (fun i => openOut i (v i) count) _
    fun k j => isAbort_openOutboxN k _ _ j]
  simp only [require_bind_of (openShN_honest K v vals count hv _).1, pure_bind]
  exact h

theorem openSh_prssCtx {ι : Type} {G : OracleSpec ι} (i : C.Party) :
    openSh (G := G) K (prssCtx keys kT kP i) = openSh K (localContext i) := rfl

theorem isShamir_honestR [CharP E 2] (rr : C.Term → ℕ → E) (k : ℕ) :
    IsShamir K (fun i => conv K (localContext i) (honestR rr i) k) (∑ T, rr T k) :=
  (isShamir_conv rr k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [honestR, hT]).symm) rfl

/-- Honest real PRSS outputs of one round, which need no message. -/
theorem rand_step {R' : Type} [Field R'] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (codec : Codec C E R') (hdraw : ∀ name key ρ idx count, FrameR prims (codec.draw name key ρ idx count))
    (idx count : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → PrssOutput C R' → RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (rr : C.Term → ℕ → R') (zz : C.Pair → ℕ → R') (s' : HashCache C), NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (honestR rr i, honestZ zz i) (nextLabel (st i))) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (prssRandomness (prssCtx keys kT kP i) codec idx count).run (st i) >>= fun p =>
        g i p.1 p.2) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  simp only [realRand_run, hL, bind_assoc, pure_bind]
  refine draw_step prims F reply fuel _ (fun i => FrameR.prssDraw _ _ hdraw _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  exact h _ _ s' hn' hle hfr

theorem isAbort_reshareOut {R' : Type} [Field R'] (codec : Codec C E R') (hcodec : CodecRoundTrip codec)
    (ctx : Context C) (r : Shares C R') (Zs : C.Party → ℕ → R') (v : ℕ → R') (count : ℕ) (j : C.Party) :
    Msg.isAbort (reshareOut K ctx codec r Zs v count j) = false := by
  unfold reshareOut; split_ifs
  · exact (hcodec _ 0).2
  · rfl

/-- An honest real extended multiplication. Every operator continues with its held terms of one
sharing of the sum of the additive shares. -/
theorem extendMult_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (products : C.Party → List (Product C E)) (n : ℕ) (hlen : ∀ i, (products i).length = n)
    (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C E → RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (Z : Shares C E), (∀ k, ∑ T, Z T k = ∑ i, extendMultShare K i (products i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0)
          ⟨recordHistory K i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0) n,
            lab + 1, (st i).tag⟩) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realCheckBuildingBlocks K (prssCtx keys kT kP i)).extendMult (products i)).run (st i) >>=
        fun p => g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  have := charP_two (E := E)
  simp only [realExtendMult_run, hL, hlen, bind_assoc, pure_bind]
  refine draw_step prims F reply (fuel + 1) _ (fun i => FrameR.prssDraw _ _ (FrameR.elementDraw K) _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  set rr := fun T => D prims h₀ ((elementCodec K).draw (.term T) (kT T) lab 0 n)
  set zz := fun p => D prims h₀ ((elementCodec K).draw (.pair p) (kP p) lab 0 n)
  rw [honestRounds_exchange F reply fuel (fun i => reshareOut K (prssCtx keys kT kP i) (elementCodec K)
    (honestR rr i) (honestZ zz i) (contextProductValues K (prssCtx keys kT kP i) (products i)) n) _
    fun k j => isAbort_reshareOut K _ (elementCodec_roundTrip K) _ _ _ _ _ _]
  set Z := honestShare K (prssCtx keys kT kP) rr zz (fun i => contextProductValues K (prssCtx keys kT kP i) (products i))
  have hz : ∀ i, reshareZ K (prssCtx keys kT kP i) (elementCodec K) (honestR rr i) (honestZ zz i)
      (contextProductValues K (prssCtx keys kT kP i) (products i)) n
        (fun k => reshareOut K (prssCtx keys kT kP k) (elementCodec K) (honestR rr k) (honestZ zz k)
          (contextProductValues K (prssCtx keys kT kP k) (products k)) n i) =
      fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0 := fun i => funext fun T => funext fun k =>
    reshareZ_honest K (prssCtx keys kT kP) rr zz _ (elementCodec K) (elementCodec_roundTrip K) (fun _ => rfl) n i T k
  simp only [hz]
  exact h Z (fun k => sum_honestShare K (prssCtx keys kT kP) rr zz _ (fun _ => rfl) k) s' hn' hle hfr

end RealBuildingBlockSteps

section CommonFailure

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

theorem honestRounds_failure (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) :
    honestStart (fun _ => (failure : PartyM C E (CallSpec I O) α)) >>= honestRounds F reply fuel =
      pure (fun _ => none) := by
  simp only [honestStart, advance_run_failure, sequenceFin_pure, pure_bind]
  rw [honestRounds_done]
  · rfl
  · exact fun _ => trivial

/-- An event that is false when no operator has an output has probability zero after a common
failure. -/
theorem probEvent_failure_zero [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (event : (C.Party → Option α) → Prop) (hnone : ¬ event fun _ => none) (s : HashCache C) (ε : ℝ≥0∞) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun _ => (failure : PartyM C E (CallSpec I O) α)) >>= honestRounds F reply fuel)).run' s}[event z] ≤
      ε := by
  rw [honestRounds_failure]
  simp [hnone]

end CommonFailure

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section TauKs

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] (prims : Primitives)
  (K : Constants C E)

/-- The coins `τ` start with `m` nonzero values, except with probability `|Ks| / 2^256 + m / |E|`,
when the cache holds expansions only of the keys `Ks`. -/
theorem tauQuery_zero_le_Ks (tag ρ : ℕ) (v : List E) (count m : ℕ) (hm : m ≤ count) (Ks : Finset HashOutput)
    (L : ℕ) (hρ : L ≤ ρ) (s : HashCache C) (hs : CacheOK Ks L s) :
    Pr{let z ←
      (simulateQ (localAnswer prims) (liftComp (tauQuery K tag ρ v count) (LocalSpec C))).run s}[¬ ∀ b < m, z.1.getD b 0 ≠ 0] ≤
      Ks.card / 2 ^ 256 + m / Fintype.card E := by
  rw [simulateQ_localAnswer_liftComp, tauQuery, simulateQ_bind, StateT.run_bind]
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z : HashOutput × HashCache C => ¬ z.1 ∉ Ks) _
    fun z hz hkey => ?_).trans (add_le_add ?_ le_rfl)
  rotate_left
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq (coinKey_fresh hρ hs tag _) Ks
  · rw [not_not] at hkey
    rw [List.range_eq_range']
    refine probEvent_expand_zero prims K z.1 count 0 m z.2 hm fun i _ => ?_
    by_contra hne
    rcases support_hashQuery_entries prims hq s z hz _ hne with h | h
    · exact hkey ((hs _ h).1 _ i rfl)
    · cases h

omit [Fintype E] [DecidableEq E] in
/-- After the coins `τ`, the cache holds expansions of one more key. -/
theorem tauQuery_cache_Ks (tag ρ : ℕ) (v : List E) (count : ℕ) (Ks : Finset HashOutput) (L : ℕ) (hρ : L ≤ ρ)
    (s : HashCache C) (hs : CacheOK Ks L s) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (liftComp (tauQuery K tag ρ v count) (LocalSpec C))).run s)) :
    ∃ k, CacheOK (insert k Ks) (ρ + 1) z.2 := by
  rw [simulateQ_localAnswer_liftComp, tauQuery, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨key, s₁⟩, h₁, hz⟩ := hz
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hs₁ := support_hashQuery_entries prims hq s _ h₁
  have hs₂ := support_expand_entries prims K key _ _ _ hz
  refine ⟨key, fun q hq' => ?_⟩
  rcases hs₂ q hq' with h | ⟨i, rfl⟩
  · rcases hs₁ q h with h | rfl
    · obtain ⟨h1, h2⟩ := hs q h
      exact ⟨fun k idx hk => Finset.mem_insert_of_mem (h1 k idx hk), fun tag' ρ' v' hk => by
        have := h2 tag' ρ' v' hk; omega⟩
    · exact ⟨fun k idx hk => (by cases hk), fun tag' ρ' v' hk => by cases hk; omega⟩
  · exact ⟨fun k idx hk => by cases hk; exact Finset.mem_insert_self _ _, fun tag' ρ' v' hk => by cases hk⟩

end TauKs

section CoinSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

omit [Fintype E] [DecidableEq E] in
/-- The coin part of a challenge or of the coins `τ`, up to the common query of `H`. -/
theorem coinPart_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (lab : ℕ)
    (g : C.Party → List E → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (v : List E) (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i v) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (prssDraw (prssCtx keys kT kP i) (elementCodec K) lab 1 2) >>= fun o =>
        openSh K (prssCtx keys kT kP i) (conv K (prssCtx keys kT kP i) o.1) 2 >>= fun opened =>
          g i (vector 2 opened)) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  have := charP_two (E := E)
  simp only [openSh_prssCtx]
  refine draw_step prims F reply (fuel + 1) _ (fun i => FrameR.prssDraw _ _ (FrameR.elementDraw K) _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw, conv_prssCtx]
  set rr := fun T => D prims h₀ ((elementCodec K).draw (.term T) (kT T) lab 1 2)
  refine openSh_step prims K F reply fuel (fun i => conv K (localContext i) (honestR rr i)) (fun k => ∑ T, rr T k) 2
    (fun k _ => isShamir_honestR K rr k) _ event s' ε ?_
  have hvec : ∀ i, vector 2 (openValueN K i (conv K (localContext i) (honestR rr i))
      (fun k => openOut (E := E) k (conv K (localContext k) (honestR rr k)) 2 i)) = vector 2 (fun k => ∑ T, rr T k) :=
    fun i => vector_congr' 2 _ _ ((openShN_honest K _ _ 2 (fun k _ => isShamir_honestR K rr k) i).2)
  simp only [hvec]
  exact h _ s' hn' hle hfr

/-- An honest real challenge. It fails with probability at most `|Ks| / 2^256 + (2 / |E|)^tries`, and
the bound charges it with the weight `δ`. A failed challenge makes every operator abort, so an event
that is false when no operator has an output needs no charge and takes `δ = 0`. -/
theorem challenge_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (r : E) (Ks' : Finset HashOutput) (s' : HashCache C), Ks'.card ≤ Ks.card + 1 →
      CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i r (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (challenge K (realCheckBuildingBlocks K (prssCtx keys kT kP i))).run (st i) >>= fun p =>
        g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤
      δ * (Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + ε := by
  simp only [realChallenge_run, hL, hT, bind_assoc]
  refine coinPart_step prims K keys kT kP F reply fuel lab (fun i v => oracleStep (challengeQuery K tg lab v) >>=
    fun x => (match x with | some r => pure (r, nextLabel (st i)) | none => failure) >>= fun p => g i p.1 p.2)
    event s hn _ fun v s' hn' hle hfr => ?_
  have hs' := cacheOK_of_frame hs hfr
  by_cases hnone : event fun _ => none
  · refine (probEvent_honest_common prims F reply fuel (challengeQuery K tg lab v) _ event
      (fun z => z.1 = none) s' ε fun z hz hbad => ?_).trans
        (add_le_add ((challengeQuery_none_le prims K tg lab v Ks Lk hLk s' hs').trans
          (le_mul_of_one_le_left' (hδ hnone))) le_rfl)
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hbad
    obtain ⟨k, hk⟩ := challengeQuery_cache prims K tg lab v Ks Lk hLk s' hs' z hz
    obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
    simp only [hr, pure_bind]
    exact h r (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')
  · refine (probEvent_honest_common prims F reply fuel (challengeQuery K tg lab v) _ event
      (fun _ => False) s' ε fun z hz _ => ?_).trans (by simp)
    rcases hr : z.1 with _ | r
    · simp only [failure_bind]
      exact probEvent_failure_zero prims F reply fuel event hnone z.2 ε
    obtain ⟨k, hk⟩ := challengeQuery_cache prims K tg lab v Ks Lk hLk s' hs' z hz
    obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
    simp only [pure_bind]
    exact h r (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')

/-- The honest real coins `τ`. The first `sliceBits` are nonzero, except with probability at most
`|Ks| / 2^256 + sliceBits / |E|`, and the bound charges it with the weight `δ`. With `δ < 1` the
bound charges nothing and the continuation takes every `τ`. -/
theorem tau_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (d : ℕ)
    (hd : sliceBits ≤ d)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → List E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (_hδ : event (fun _ => none) → 1 ≤ δ)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (τ : List E), (1 ≤ δ → ∀ b < sliceBits, τ.getD b 0 ≠ 0) →
      ∀ (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i τ (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (coinKey K (realCheckBuildingBlocks K (prssCtx keys kT kP i)) >>= fun key =>
        expand K key d).run (st i) >>= fun p => g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤
      δ * (Ks.card / 2 ^ 256 + sliceBits / Fintype.card E) + ε := by
  simp only [realTau_run, hL, hT, bind_assoc, pure_bind]
  refine coinPart_step prims K keys kT kP F reply fuel lab (fun i v => oracleStep (tauQuery K tg lab v d) >>=
    fun τ => g i τ (nextLabel (st i))) event s hn _ fun v s' hn' hle hfr => ?_
  have hs' := cacheOK_of_frame hs hfr
  by_cases hone : 1 ≤ δ
  · refine (probEvent_honest_common prims F reply fuel (tauQuery K tg lab v d) _ event
      (fun z => ¬ ∀ b < sliceBits, z.1.getD b 0 ≠ 0) s' ε fun z hz hbad => ?_).trans
        (add_le_add ((tauQuery_zero_le_Ks prims K tg lab v d sliceBits hd Ks Lk hLk s' hs').trans
          (le_mul_of_one_le_left' hone)) le_rfl)
    rw [not_not] at hbad
    obtain ⟨k, hk⟩ := tauQuery_cache_Ks prims K tg lab v d Ks Lk hLk s' hs' z hz
    obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
    exact h z.1 (fun _ => hbad) (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')
  · refine (probEvent_honest_common prims F reply fuel (tauQuery K tg lab v d) _ event
      (fun _ => False) s' ε fun z hz _ => ?_).trans (by simp)
    obtain ⟨k, hk⟩ := tauQuery_cache_Ks prims K tg lab v d Ks Lk hLk s' hs' z hz
    obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
    exact h z.1 (fun h' => absurd h' hone) (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn''
      (hle.trans hle')

@[simp] theorem prssCtx_self (i : C.Party) : (prssCtx keys kT kP i).self = i := rfl

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
theorem compareDigests_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (salts : Shares C Bit) (st : RunState C) :
    (compareDigests (G := G) ctx salts).run st =
      oracleStep (digestQuery ctx.self salts st.history) >>= fun ds =>
        exchange (digestOutbox (E := E) ctx.self ds) >>= fun inbox =>
          require (DigestsAgree (E := E) ctx.self ds inbox) >>= fun _ => pure ((), st) := by
  simp only [compareDigests, StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind]
  rfl

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- Honest digests, whose comparison passes. -/
theorem digest_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (hh : HistAgree fun i => (st i).history)
    (salts : C.Party → Shares C Bit) (S : Shares C Bit) (hS : ∀ i T, i ∈ C.holders T → salts i T = S T)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hs : CacheOK Ks Lk s) (ε : ℝ≥0∞)
    (h : ∀ (s' : HashCache C), CacheOK Ks Lk s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (st i)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (compareDigests (prssCtx keys kT kP i) (salts i)).run (st i) >>= fun p =>
        g i p.2) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  simp only [compareDigests_run, prssCtx_self, bind_assoc, pure_bind]
  refine probEvent_honest_local prims F reply (fuel + 1) (fun i => digestQuery i (salts i) (st i).history) _ event s ε
    fun z hz => ?_
  obtain ⟨hok, hlen, hag⟩ := digests_agree prims salts S hS _ hh Ks Lk s hs z hz
  obtain ⟨hle, hn', -⟩ := localRun_D prims _ s hn z hz
  rw [honestRounds_exchange F reply fuel (fun i => digestOutbox (E := E) i (z.1 i)) _
    fun k j => by unfold digestOutbox; split_ifs <;> rfl]
  simp only [require_bind_of (digestsAgree_honest z.1 hlen hag _)]
  exact h z.2 hok hn' hle

end CoinSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealFinal

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

omit [Fintype E] [DecidableEq E] in
@[simp] theorem realCheckBuildingBlocks_randElements {ι : Type} {G : OracleSpec ι} (ctx : Context C) (c : ℕ) :
    (realCheckBuildingBlocks (G := G) K ctx).randElements c = prssRandomness ctx (elementCodec K) 1 c := rfl

omit [Fintype E] [DecidableEq E] in
@[simp] theorem realCheckBuildingBlocks_randBits {ι : Type} {G : OracleSpec ι} (ctx : Context C) (c : ℕ) :
    (realCheckBuildingBlocks (G := G) K ctx).randBits c = prssRandomness ctx bitCodec 2 c := rfl

omit [Fintype E] [DecidableEq E] in
theorem rand_step' {R' : Type} [Field R'] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (codec : Codec C E R') (hdraw : ∀ name key ρ idx count, FrameR prims (codec.draw name key ρ idx count))
    (idx count : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → PrssOutput C R' × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (rr : C.Term → ℕ → R') (zz : C.Pair → ℕ → R') (s' : HashCache C), NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((honestR rr i, honestZ zz i), nextLabel (st i))) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (prssRandomness (prssCtx keys kT kP i) codec idx count).run (st i) >>= g i) >>=
        honestRounds F reply fuel)).run' s}[event z] ≤ ε :=
  rand_step prims keys kT kP F reply fuel codec hdraw idx count st lab hL (fun i a b => g i (a, b)) event s hn ε h

omit [Fintype E] [DecidableEq E] in
theorem extendMult_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (products : C.Party → List (Product C E)) (n : ℕ) (hlen : ∀ i, (products i).length = n)
    (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C E × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (Z : Shares C E), (∀ k, ∑ T, Z T k = ∑ i, extendMultShare K i (products i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0),
          ⟨recordHistory K i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0) n,
            lab + 1, (st i).tag⟩)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realCheckBuildingBlocks K (prssCtx keys kT kP i)).extendMult (products i)).run (st i) >>=
        g i) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε :=
  extendMult_step prims K keys kT kP F reply fuel products n hlen st lab hL (fun i a b => g i (a, b)) event s hn ε h

theorem digest_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (hh : HistAgree fun i => (st i).history)
    (salts : C.Party → Shares C Bit) (S : Shares C Bit) (hS : ∀ i T, i ∈ C.holders T → salts i T = S T)
    (g : C.Party → Unit × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hs : CacheOK Ks Lk s) (ε : ℝ≥0∞)
    (h : ∀ (s' : HashCache C), CacheOK Ks Lk s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((), st i)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (compareDigests (prssCtx keys kT kP i) (salts i)).run (st i) >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε :=
  digest_step prims keys kT kP F reply fuel st hh salts S hS (fun i b => g i ((), b)) event s hn Ks Lk hs ε h

theorem challenge_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → E × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (r : E) (Ks' : Finset HashOutput) (s' : HashCache C), Ks'.card ≤ Ks.card + 1 →
      CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (r, nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (challenge K (realCheckBuildingBlocks K (prssCtx keys kT kP i))).run (st i) >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s}[event z] ≤
      δ * (Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + ε :=
  challenge_step prims K keys kT kP F reply fuel st lab tg hL hT (fun i a b => g i (a, b)) event δ hδ s hn Ks Lk hLk
    hs ε h

theorem tau_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (d : ℕ)
    (hd : sliceBits ≤ d)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → List E × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (τ : List E), (1 ≤ δ → ∀ b < sliceBits, τ.getD b 0 ≠ 0) →
      ∀ (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (τ, nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (coinKey K (realCheckBuildingBlocks K (prssCtx keys kT kP i)) >>= fun key =>
        expand K key d).run (st i) >>= g i) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤
      δ * (Ks.card / 2 ^ 256 + sliceBits / Fintype.card E) + ε :=
  tau_step prims K keys kT kP F reply fuel d hd st lab tg hL hT (fun i a b => g i (a, b)) event δ hδ s hn Ks Lk hLk
    hs ε h

theorem real_final_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (A B : C.Party → ℕ → E) (D : C.Party → E) (a b : E)
    (hA : IsShamir K (fun i => A i 0) a) (hB : IsShamir K (fun i => B i 0) b) (hD : IsShamir K D (a * b))
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg : ℕ)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 4) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ⟨hist' i, lab + 4, tg⟩) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (finalStep K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i))
        (A i, B i, D i)).run ⟨hist i, lab, tg⟩ >>= fun p => g i p.2) >>= honestRounds F reply (fuel + 4))).run' s}[event z] ≤
      δ * (Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + ε := by
  have := charP_two (E := E)
  simp only [finalStep, StateT.run_bind, bind_assoc, realCheckBuildingBlocks_randElements,
      realCheckBuildingBlocks_randBits]
  refine rand_step' prims keys kT kP F reply (fuel + 4) (elementCodec K) (FrameR.elementDraw K) 1 2 _ lab
    (fun _ => rfl) _ event s hn _ fun r₁ zz₁ s₁ hn₁ hle₁ hfr₁ => ?_
  dsimp only [nextLabel]
  simp only [conv_prssCtx]
  set wa := fun i => conv K (localContext i) (honestR r₁ i) 0
  set wb := fun i => conv K (localContext i) (honestR r₁ i) 1
  refine extendMult_step' prims K keys kT kP F reply (fuel + 3) (fun i => [.shamir (fun _ => wa i) (fun _ => wb i) 1,
    .shamir (fun _ => wa i + A i 0) (fun _ => wb i + B i 0) 1]) 2 (fun _ => rfl) _ (lab + 1) (fun _ => rfl) _
    event s₁ hn₁ _ fun Z₂ hZ₂ s₂ hn₂ hle₂ hfr₂ => ?_
  dsimp only
  refine rand_step' prims keys kT kP F reply (fuel + 3) bitCodec (FrameR.bitDraw) 2 256 _ (lab + 1 + 1)
    (fun _ => rfl) _ event s₂ hn₂ _ fun r₃ zz₃ s₃ hn₃ hle₃ hfr₃ => ?_
  dsimp only [nextLabel]
  have hs₃ : CacheOK Ks Lk s₃ := cacheOK_of_frame (cacheOK_of_frame (cacheOK_of_frame hs hfr₁) hfr₂) hfr₃
  have hh₄ := histAgree_record K hist hh (fun i T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) Z₂ 2
    (fun i T g hi hg => by simp [hi, hg])
  refine digest_step' prims keys kT kP F reply (fuel + 2) _ hh₄ (fun i => honestR r₃ i) r₃
    (fun i T hT => by simp [honestR, hT]) _ event s₃ hn₃ Ks Lk hs₃ _ fun s₄ hs₄ hn₄ hle₄ => ?_
  dsimp only
  refine challenge_step' prims K keys kT kP F reply (fuel + 1) _ (lab + 1 + 1 + 1) tg (fun _ => rfl) (fun _ => rfl) _
    event δ hδ s₄ hn₄ Ks Lk (by omega) hs₄ ε fun r Ks' s₅ hKs' hs₅ hn₅ hle₅ => ?_
  dsimp only [nextLabel]
  simp only [StateT.run_lift, bind_assoc, pure_bind, openSh_prssCtx]
  have hwa : IsShamir K wa (∑ T, r₁ T 0) := isShamir_honestR K r₁ 0
  have hwb : IsShamir K wb (∑ T, r₁ T 1) := isShamir_honestR K r₁ 1
  have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
      (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) k) (∑ T, Z₂ T k) := fun k hk =>
    (isShamir_conv Z₂ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
  have hq0 : ∑ T, Z₂ T 0 = (∑ T, r₁ T 0) * (∑ T, r₁ T 1) := by
    rw [hZ₂ 0]
    simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext, Finset.sum_range_one]
    exact sum_lagrangeAll_shamir K hwa hwb
  have hq1 : ∑ T, Z₂ T 1 = ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) := by
    rw [hZ₂ 1]
    simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
      localContext, Finset.sum_range_one]
    exact sum_lagrangeAll_shamir K (hwa.add hA) (hwb.add hB)
  set vals : ℕ → E := fun k => match k with
    | 0 => (∑ T, r₁ T 0) + r * ((∑ T, r₁ T 0) + a)
    | 1 => (∑ T, r₁ T 1) + r * ((∑ T, r₁ T 1) + b)
    | _ => (∑ T, r₁ T 0) * (∑ T, r₁ T 1) +
        (a * b + (∑ T, r₁ T 0) * (∑ T, r₁ T 1) + ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b)) * r +
        ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) * r ^ 2 with hvals
  have hv : ∀ k < 3, IsShamir K (fun i => (fun k => match k with
      | 0 => wa i + r * (wa i + A i 0)
      | 1 => wb i + r * (wb i + B i 0)
      | _ => conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 0 +
          (D i + conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 0 +
            conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 1) * r +
          conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 1 * r ^ 2 : ℕ → E) k)
      (vals k) := by
    intro k hk
    interval_cases k
    · exact (hwa.add ((hwa.add hA).mul_left r)).congr (fun i => rfl) rfl
    · exact (hwb.add ((hwb.add hB).mul_left r)).congr (fun i => rfl) rfl
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add (((hD.add h0).add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1]; rfl
  have hfinal : vals 0 * vals 1 = vals 2 := by
    have two : (2 : E) = 0 := CharTwo.two_eq_zero
    simp only [hvals]
    linear_combination (-(a * b * r)) * two
  refine openSh_step prims K F reply fuel _ vals 3 hv _ event s₅ ε ?_
  have hc : ∀ i, openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 0 *
      openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 1 =
      openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 2 := fun i => by
    have hval := (openShN_honest K _ vals 3 hv i).2
    rw [hval 0 (by norm_num), hval 1 (by norm_num), hval 2 (by norm_num), hfinal]
  simp only [require_bind_of (hc _)]
  exact h _ Ks' s₅ hKs' hs₅ hn₅ (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans hle₅))))

end RealFinal

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealHalving

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem real_halving_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (width : ℕ)
    (hwidth : 1 ≤ width) :
    ∀ (n j₀ : ℕ), j₀ + n = halvingSteps width → ∀ (A B : C.Party → ℕ → E) (D : C.Party → E) (Av Bv : ℕ → E),
      (∀ k, IsShamir K (fun i => A i k) (Av k)) → (∀ k, IsShamir K (fun i => B i k) (Bv k)) →
      IsShamir K D (∑ k ∈ range (halvedLength^[j₀] width), Av k * Bv k) →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞),
      (event (fun _ => none) → 1 ≤ δ) → ∀ (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + n + 1 → CacheOK Ks' (lab + 2 * n + 4) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i ⟨hist' i, lab + 2 * n + 4, tg⟩) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (halvingStep K (prssCtx keys kT kP i)
          (realCheckBuildingBlocks K (prssCtx keys kT kP i)) width) (A i, B i, D i)).run ⟨hist i, lab, tg⟩ >>= fun x =>
            (finalStep K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i)) x.1).run
                x.2 >>=
              fun p => g i p.2) >>= honestRounds F reply (fuel + 2 * n + 4))).run' s}[event z] ≤ δ * chalErr E c (n + 1) + ε := by
  intro n
  induction n with
  | zero =>
    intro j₀ hj A B D Av Bv hA hB hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_zero] at hj
    subst hj
    rw [iterate_halvingSteps width hwidth, Finset.sum_range_one] at hD
    refine (real_final_bound prims K keys kT kP F reply fuel A B D (Av 0) (Bv 0) (hA 0) (hB 0) hD hist hh lab tg g
      event δ hδ s hn Ks Lk hLk hs ε fun hist' Ks' s' h1 h2 h3 h4 => h hist' Ks' s' (by omega) h2 h3 h4).trans ?_
    simp only [chalErr, zero_add, Finset.sum_range_one, Nat.add_zero]
    gcongr
  | succ n ih =>
    intro j₀ hj A B D Av Bv hA hB hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    have := charP_two (E := E)
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 4 = (fuel + 2 * n + 5) + 1 by ring]
    simp only [List.foldlM_cons, halvingStep, bind_assoc, pure_bind, StateT.run_bind]
    set ℓ := halvedLength^[j₀] width with hℓ
    set half := halvedLength ℓ with hhalf
    let hiv := fun (v : ℕ → E) k => if k + half < ℓ then v (k + half) else 0
    refine extendMult_step' prims K keys kT kP F reply (fuel + 2 * n + 5) (fun i => [.shamir (A i) (B i) half,
      .shamir (fun k => A i k + hiv (A i) k) (fun k => B i k + hiv (B i) k) half]) 2 (fun _ => rfl) _ lab
      (fun _ => rfl) _ event s hn _ fun Z₁ hZ₁ s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hs₁ := cacheOK_of_frame hs hfr₁
    rw [chalErr_succ]
    have hKc : (Ks.card : ℝ≥0∞) / 2 ^ 256 ≤ c / 2 ^ 256 := by gcongr
    refine le_trans (challenge_step' prims K keys kT kP F reply (fuel + 2 * n + 4) _ (lab + 1) tg (by intro; rfl)
      (by intro; rfl) _ event δ hδ s₁ hn₁ Ks Lk (by omega) hs₁ (δ * chalErr E (c + 1) (n + 1) + ε) ?_) ?_
    swap
    · rw [mul_add δ _ (chalErr E (c + 1) (n + 1)), ← add_assoc]
      gcongr
    intro r Ks₂ s₂ hKs₂ hs₂ hn₂ hle₂
    dsimp only [nextLabel]
    have hhi : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => hiv (f i) k) (hiv a k) := fun f a hf k => (hf (k + half)).ite K _
    have hfold : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => f i k + r * (f i k + hiv (f i) k)) (a k + r * (a k + hiv a k)) :=
      fun f a hf k => (hf k).add (((hf k).add (hhi f a hf k)).mul_left r)
    have hsum : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => f i k + hiv (f i) k) (a k + hiv a k) :=
      fun f a hf k => (hf k).add (hhi f a hf k)
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, Av k * Bv k := by
      rw [hZ₁ 0]
      simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext]
      exact sum_lagrangeAll_shamir_sum K hA hB half
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, (Av k + hiv Av k) * (Bv k + hiv Bv k) := by
      rw [hZ₁ 1]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
        localContext]
      exact sum_lagrangeAll_shamir_sum K (hsum A Av hA) (hsum B Bv hB) half
    simp only [conv_prssCtx]
    refine ih (j₀ + 1) (by omega) _ _ _ (fun k => Av k + r * (Av k + hiv Av k))
      (fun k => Bv k + r * (Bv k + hiv Bv k)) (hfold A Av hA) (hfold B Bv hB) ?_ _
      (histAgree_record K hist hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (lab + 1 + 1) tg (lab + 1 + 1)
      (c + 1) Ks₂ le_rfl (by omega) s₂ hn₂ hs₂ fuel g event δ hδ ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add ((hD.add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1, Function.iterate_succ_apply', ← hℓ, ← hhalf, sum_range_halving_fold, sum_range_padded Av Bv ℓ]
    · have hlab : lab + 1 + 1 + 2 * n + 4 = lab + 2 * (n + 1) + 4 := by ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans (hle₂.trans h4))

end RealHalving

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealSlice

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem real_slice_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (τ : List E) (count : ℕ)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0) (hwidth : 0 < sliceWidth count) :
    ∀ (n j₀ : ℕ), j₀ + n = sliceBits → ∀ (xs ys : C.Party → Shares C E) (D : C.Party → E) (XS YS : Shares C E),
      (∀ i T, i ∈ C.holders T → xs i T = XS T ∧ ys i T = YS T) →
      IsShamir K D (∑ k ∈ range (sliceWidth count * 2 ^ (sliceBits - j₀)),
        coinProduct τ 0 (sliceBits - j₀) (k / sliceWidth count) * (∑ T, XS T k) * ∑ T, YS T k) →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞),
      (event (fun _ => none) → 1 ≤ δ) → ∀ (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + n + halvingSteps (sliceWidth count) + 1 →
        CacheOK Ks' (lab + 2 * n + 2 * halvingSteps (sliceWidth count) + 4) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i ⟨hist' i, lab + 2 * n + 2 * halvingSteps (sliceWidth count) + 4, tg⟩) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (sliceStep K (prssCtx keys kT kP i)
          (realCheckBuildingBlocks K (prssCtx keys kT kP i)) τ count) (xs i, ys i, D i)).run ⟨hist i, lab, tg⟩ >>= fun p =>
            ((List.range (halvingSteps (sliceWidth count))).foldlM (halvingStep K (prssCtx keys kT kP i)
              (realCheckBuildingBlocks K (prssCtx keys kT kP i)) (sliceWidth count))
              (conv K (prssCtx keys kT kP i) p.1.1, conv K (prssCtx keys kT kP i) p.1.2.1, p.1.2.2)).run p.2 >>= fun x =>
            (finalStep K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i)) x.1).run
                x.2 >>=
              fun q => g i q.2) >>=
          honestRounds F reply (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 4))).run' s}[event z] ≤
        δ * chalErr E c (n + halvingSteps (sliceWidth count) + 1) + ε := by
  have := charP_two (E := E)
  intro n
  induction n with
  | zero =>
    intro j₀ hj xs ys D XS YS hxy hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, Nat.mul_zero, Nat.add_zero, zero_add]
    rw [Nat.add_zero] at hj
    subst hj
    rw [List.range_eq_range']
    simp only [conv_prssCtx]
    refine real_halving_bound prims K keys kT kP F reply (sliceWidth count) hwidth _ 0 (by omega) _ _ D
      (fun k => ∑ T, XS T k) (fun k => ∑ T, YS T k) (fun k => (isShamir_conv XS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).1]).symm) rfl)
      (fun k => (isShamir_conv YS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).2]).symm) rfl) ?_ hist hh lab tg Lk c Ks hLk hKs s hn hs
      fuel g event δ hδ ε fun hist' Ks' s' h1 h2 h3 h4 => h hist' Ks' s' (by omega) h2 h3 h4
    refine hD.congr (fun i => rfl) ?_
    simp only [Nat.sub_self, pow_zero, mul_one, Function.iterate_zero, id, coinProduct_zero_width, one_mul]
  | succ n ih =>
    intro j₀ hj xs ys D XS YS hxy hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 2 * halvingSteps (sliceWidth count) + 4 =
      (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5) + 1 by ring]
    simp only [List.foldlM_cons, sliceStep, bind_assoc, pure_bind, StateT.run_bind]
    set width := sliceWidth count with hwidth_def
    set half := width * 2 ^ (sliceBits - 1 - j₀) with hhalf
    set rest := fun k => coinProduct τ 0 (sliceBits - 1 - j₀) (k / width) with hrest
    refine extendMult_step' prims K keys kT kP F reply (fuel + 2 * n + 2 * halvingSteps width + 5)
      (fun i => [.replicated (fun T k => rest k * xs i T k) (ys i) half,
        .replicated (fun T k => rest k * (xs i T k + xs i T (k + half))) (fun T k => ys i T k + ys i T (k + half)) half])
      2 (fun _ => rfl) _ lab (fun _ => rfl) _ event s hn _ fun Z₁ hZ₁ s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hs₁ := cacheOK_of_frame hs hfr₁
    rw [show n + 1 + halvingSteps width + 1 = (n + halvingSteps width + 1) + 1 by ring, chalErr_succ]
    have hKc : (Ks.card : ℝ≥0∞) / 2 ^ 256 ≤ c / 2 ^ 256 := by gcongr
    refine le_trans (challenge_step' prims K keys kT kP F reply (fuel + 2 * n + 2 * halvingSteps width + 4) _
      (lab + 1) tg (by intro; rfl) (by intro; rfl) _ event δ hδ s₁ hn₁ Ks Lk (by omega) hs₁
      (δ * chalErr E (c + 1) (n + halvingSteps width + 1) + ε) ?_) ?_
    swap
    · rw [mul_add δ _ (chalErr E (c + 1) (n + halvingSteps width + 1)), ← add_assoc]
      gcongr
    intro r Ks₂ s₂ hKs₂ hs₂ hn₂ hle₂
    dsimp only [nextLabel]
    have hw : sliceBits - 1 - j₀ = n := by omega
    set cc := τ.getD (sliceBits - 1 - j₀) 0 with hcc
    have hc : cc ≠ 0 := hτ _ (by omega)
    let Xv := fun k => ∑ T, XS T k
    let Yv := fun k => ∑ T, YS T k
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, rest k * Xv k * Yv k := by
      rw [hZ₁ 0]
      simp only [extendMultShare, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * XS T k) YS half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => (hxy i T hT).2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum]
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, rest k * (Xv k + Xv (k + half)) * (Yv k + Yv (k + half)) := by
      rw [hZ₁ 1]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * (XS T k + XS T (k + half)))
        (fun T k => YS T k + YS T (k + half)) half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => by funext k; rw [(hxy i T hT).2])]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsplit := slice_sum_split τ width (sliceBits - 1 - j₀) hwidth Xv Yv
    rw [show sliceBits - 1 - j₀ + 1 = sliceBits - j₀ by omega] at hsplit
    simp only [conv_prssCtx]
    refine ih (j₀ + 1) (by omega) _ _ _ (fun T k => XS T k + r * (XS T k + XS T (k + half)))
      (fun T k => YS T k + r * (YS T k + YS T (k + half)))
      (fun i T hT => ⟨by funext k; rw [(hxy i T hT).1], by funext k; rw [(hxy i T hT).2]⟩) ?_ _
      (histAgree_record K hist hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (lab + 1 + 1) tg (lab + 1 + 1)
      (c + 1) Ks₂ le_rfl (by omega) s₂ hn₂ hs₂ fuel g event δ hδ ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine (((h0.mul_left (1 + r)).add (((hD.add h0).div cc).mul_left r)).add (h1.mul_left (r * (1 + r)))).congr
        (fun i => rfl) ?_
      rw [hq0, hq1, show sliceBits - (j₀ + 1) = sliceBits - 1 - j₀ by omega]
      rw [sum_range_slice_fold rest Xv Yv half r cc _ hc hsplit]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    · have hlab : lab + 1 + 1 + 2 * n + 2 * halvingSteps width + 4 =
          lab + 2 * (n + 1) + 2 * halvingSteps width + 4 := by ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans (hle₂.trans h4))

end RealSlice

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealCheck

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

omit [Fintype E] [DecidableEq E] in
theorem tau_split {ι : Type} {G : OracleSpec ι} {β : Type} (ctx : Context C) (d : ℕ) (st : RunState C)
    (f : List E × RunState C → PartyM C E G β) :
    ((coinKey K (realCheckBuildingBlocks (G := G) K ctx)).run st >>= fun x => (expand K x.1 d).run x.2 >>=
        f) =
      (coinKey K (realCheckBuildingBlocks K ctx) >>= fun key => expand K key d).run st >>= f := by
  rw [StateT.run_bind, bind_assoc]

/-- An honest real check of correct tuples. It aborts only on a coin. -/
theorem real_check_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R)
    (tuples : C.Party → List (Tuple C)) (cnt : ℕ) (hcnt : ∀ i, ((tuples i).map (·.count)).sum = cnt) (hpos : cnt ≠ 0)
    (LX LY LZ : Shares C E)
    (hag : ∀ i T, i ∈ C.holders T → liftedPart (E := E) (tuples i) (·.x) T = LX T ∧
      liftedPart (E := E) (tuples i) (·.y) T = LY T ∧ liftedPart (E := E) (tuples i) (·.z) T = LZ T)
    (hprod : ∀ k, ∑ T, LZ T k = (∑ T, LX T k) * ∑ T, LY T k)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + halvings cnt + 2 → CacheOK Ks' (lab + 2 * halvings cnt + 5) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ⟨hist' i, lab + 2 * halvings cnt + 5, tg⟩) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (check K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i))
        (tuples i)).run ⟨hist i, lab, tg⟩ >>= fun p => g i p.2) >>=
          honestRounds F reply (fuel + 2 * halvings cnt + 5))).run' s}[event z] ≤
      δ * (Ks.card / 2 ^ 256 + sliceBits / Fintype.card E) + (δ * chalErr E (c + 1) (halvings cnt + 1) + ε) := by
  have := charP_two (E := E)
  have hne : ∀ i, ((tuples i).map (·.count)).sum ≠ 0 := fun i => by rw [hcnt i]; exact hpos
  simp only [check_eq _ _ _ _ (hne _), hcnt, StateT.run_bind, bind_assoc]
  rw [show fuel + 2 * halvings cnt + 5 = (fuel + 2 * halvings cnt + 4) + 1 by ring]
  simp only [tau_split]
  refine tau_step' prims K keys kT kP F reply (fuel + 2 * halvings cnt + 4) (coins cnt) (sliceBits_le_coins hpos) _
    lab tg (by intro; rfl) (by intro; rfl) _ event δ hδ s hn Ks Lk hLk hs _ ?_
  intro τ hτ' Ks₁ s₁ hKs₁ hs₁ hn₁ hle₁
  dsimp only [nextLabel]
  by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
  swap
  · simp only [StateT.run_lift, require, hτ, ↓reduceIte, failure_bind]
    exact probEvent_failure_zero prims F reply _ event (fun he => hτ (hτ' (hδ he))) s₁ _
  simp only [StateT.run_lift, require_bind_of hτ, pure_bind]
  have hR : halvings cnt = sliceBits + halvingSteps (sliceWidth cnt) := rfl
  rw [show List.range sliceBits = List.range' 0 sliceBits from List.range_eq_range',
    show halvings cnt - sliceBits = halvingSteps (sliceWidth cnt) by omega,
    show fuel + 2 * halvings cnt + 4 = fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth cnt) + 4 by omega,
    show halvings cnt + 1 = sliceBits + halvingSteps (sliceWidth cnt) + 1 by omega]
  refine real_slice_bound prims K keys kT kP F reply τ cnt hτ (sliceWidth_pos hpos) sliceBits 0 (by simp) _ _ _
    (fun T k => wordWeightOf K τ cnt k * LX T k) LY
    (fun i T hT => ⟨by funext k; simp only [(hag i T hT).1], (hag i T hT).2.1⟩) ?_ hist hh (lab + 1) tg (lab + 1)
    (c + 1) Ks₁ le_rfl (by omega) s₁ hn₁ hs₁ fuel g event δ hδ ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
  · refine (isShamir_conv (claimOf K τ cnt LZ) 0).congr (fun i => (conv_congr i _ _ 0 fun T hT => by
      simp only [claimOf, (hag i T hT).2.2]).symm) ?_
    simp only [claimOf, Nat.sub_zero]
    rw [Finset.sum_comm, mul_comm (sliceWidth cnt)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, hprod k, ← Finset.mul_sum]
    simp only [sliceOf]
    ring
  · have hlab : lab + 1 + 2 * sliceBits + 2 * halvingSteps (sliceWidth cnt) + 4 = lab + 2 * halvings cnt + 5 := by
      omega
    rw [hlab] at h2 ⊢
    exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans h4)

end RealCheck

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Collector

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The running values after `record` of a reshare in `mode` at operator `i`. -/
def recordMode (mode : ReshareMode) (i : C.Party) (h : C.Term → List Bit) (z : Shares C Bit) (count : ℕ) :
    C.Term → List Bit := fun T =>
  if i ∈ C.holders T then
    h T ++ ((List.range count).filter fun g => (filler K mode T g).isSome).flatMap ((bitCodec (C := C) (E := E)).toBits ∘ z T)
  else h T

theorem reshareCollector_run (ctx : Context C) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit)
    (count : ℕ) (st : RunState C) :
    (reshareCollector (G := G) K ctx (r, Zs) v count).run st =
      exchange (colOut1 K ctx.self r Zs v count) >>= fun inbox =>
        exchange (colOut2 K ctx.self r Zs v count inbox) >>= fun forward =>
          pure (colZ K ctx.self r Zs v count inbox forward,
            ⟨recordMode K .collector ctx.self st.history (colZ K ctx.self r Zs v count inbox forward) count,
              st.label, st.tag⟩) := by
  unfold reshareCollector
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  refine congrArg (_ >>= ·) (funext fun forward => ?_)
  simp only [record, StateT.run_modify, StateT.run_pure, pure_bind]
  rfl

theorem getD_map_idxOf' {l : List ℕ} {g : ℕ} (hg : g ∈ l) (f : ℕ → Bit) : (l.map f).getD (l.idxOf g) 0 = f g := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hg)]
  simp [List.getElem_idxOf]

variable (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit) (v : C.Party → ℕ → Bit)

/-- The sharing that an honest collector reshare gives, before the restriction to the held terms. -/
def colShare (T : C.Term) (g : ℕ) : Bit :=
  if T = (K.collector g).1 then ∑ j, colU K j (honestR rr j) (honestZ zz j) (v j) g else rr T g

theorem sum_colShare (g : ℕ) : ∑ T, colShare K rr zz v T g = ∑ i, v i g := by
  set star := (K.collector g).1
  have hpairs : ∑ j : C.Party, ∑ k ∈ Finset.univ.erase j, honestZ zz j k g = 0 := by
    have := sum_pairs_eq_zero (R := Bit) (C := C) Finset.univ fun p => zz p g
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [dite_eq_left rfl, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp only [honestZ, dite_eq_right hki, dite_eq_right (Ne.symm hki)]
  have hown : ∑ j : C.Party, ∑ T ∈ Finset.univ.filter (fun T => T ≠ star ∧ K.owner T = j), honestR rr j T g =
      ∑ T ∈ Finset.univ.filter (· ≠ star), rr T g := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (· ≠ star))
      (t := Finset.univ) (g := K.owner) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT' := (Finset.mem_filter.mp hT).2
    simp only [honestR, ite_eq_left (hT'.2 ▸ K.owner_held T)]
  have hu : ∑ j, colU K j (honestR rr j) (honestZ zz j) (v j) g =
      ∑ i, v i g + ∑ T ∈ Finset.univ.filter (· ≠ star), rr T g := by
    simp only [colU, Finset.sum_add_distrib, hpairs, add_zero]
    exact congrArg (_ + ·) hown
  unfold colShare
  rw [Finset.sum_ite, Finset.filter_eq' Finset.univ star, ite_eq_left (Finset.mem_univ _), Finset.sum_singleton, hu,
    add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Each honest operator gets its held terms of `colShare`. -/
theorem colZ_honest (count : ℕ) (i : C.Party) (T : C.Term) (g : ℕ) :
    colZ K i (honestR rr i) (honestZ zz i) (v i) count
        (fun k => colOut1 K k (honestR rr k) (honestZ zz k) (v k) count i)
        (fun k => colOut2 K k (honestR rr k) (honestZ zz k) (v k) count
          (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (v k') count k) i) T g =
      if i ∈ C.holders T ∧ g < count then colShare K rr zz v T g else 0 := by
  have hsum : ∀ κ g, g < count → (K.collector g).2 = κ →
      colSum K κ (honestR rr κ) (honestZ zz κ) (v κ) count
        (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (v k') count κ) g =
        ∑ j, colU K j (honestR rr j) (honestZ zz j) (v j) g := by
    intro κ g hg hκ
    have hmem : g ∈ collectedBy K count κ := List.mem_filter.2 ⟨List.mem_range.2 hg, by simp [hκ]⟩
    unfold colSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ κ)]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjκ : j ≠ κ := Finset.ne_of_mem_erase hj
    simp only [colOut1, ne_eq, Ne.symm hjκ, not_false_eq_true, ite_true, Msg.bitAt]
    exact getD_map_idxOf' hmem _
  unfold colZ
  by_cases hiT : i ∈ C.holders T
  · by_cases hg : g < count
    · have h1 : ¬ (i ∉ C.holders T ∨ count ≤ g) := by simp [hiT]; omega
      rw [ite_eq_right h1, ite_eq_left (show i ∈ C.holders T ∧ g < count from ⟨hiT, hg⟩)]
      unfold colShare
      by_cases hT : T = (K.collector g).1
      · rw [ite_eq_left hT, ite_eq_left hT]
        by_cases hκ : (K.collector g).2 = i
        · rw [ite_eq_left hκ, hsum i g hg hκ]
        · rw [ite_eq_right hκ]
          have hmem : g ∈ forwardedTo K count (K.collector g).2 i :=
            List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_range.2 hg, by simp⟩, by simpa [← hT] using hiT⟩
          simp only [colOut2, ne_eq, Ne.symm hκ, not_false_eq_true, ite_true, Msg.bitAt]
          rw [getD_map_idxOf' hmem, hsum _ g hg rfl]
      · rw [ite_eq_right hT, ite_eq_right hT]
        simp [honestR, hiT]
    · rw [ite_eq_left (Or.inr (by omega)), ite_eq_right (by tauto)]
  · rw [ite_eq_left (Or.inl hiT), ite_eq_right (by tauto)]

theorem isAbort_colOut1 (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v' : ℕ → Bit) (count : ℕ)
    (j : C.Party) : Msg.isAbort (colOut1 (E := E) K i r Zs v' count j) = false := by
  unfold colOut1; split_ifs <;> rfl

theorem isAbort_colOut2 (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v' : ℕ → Bit) (count : ℕ)
    (inbox : Mail C E) (j : C.Party) : Msg.isAbort (colOut2 K i r Zs v' count inbox j) = false := by
  unfold colOut2; split_ifs <;> rfl

end Collector

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section MultSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem realMult_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit)
    (count : ℕ) (st : RunState C) {β : Type} (f : Shares C Bit × RunState C → PartyM C E G β) :
    ((realRunBuildingBlocks K ctx mode).mult x y count).run st >>= f =
      oracleStep (prssDraw ctx (bitCodec (E := E)) st.label 0 count) >>= fun o =>
        (reshareWith K ctx mode o (mulRep K ctx x y) count).run (nextLabel st) >>= f := by
  simp only [realRunBuildingBlocks]
  rw [prssRandomness_run, bind_assoc]

theorem realRerand_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit)
    (count : ℕ) (st : RunState C) {β : Type} (f : Shares C Bit × RunState C → PartyM C E G β) :
    ((realRunBuildingBlocks K ctx mode).rerand v count).run st >>= f =
      oracleStep (prssDraw ctx (bitCodec (E := E)) st.label 0 count) >>= fun o =>
        (reshare K ctx (bitCodec (E := E)) o (ownerSum K ctx v) count).run (nextLabel st) >>= f := by
  simp only [realRunBuildingBlocks]
  rw [prssRandomness_run, bind_assoc]

/-- An honest real multiplication in `mode`. Every operator continues with its held terms of one
sharing of the sum of the `MulRep` shares. -/
theorem mult_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (mode : ReshareMode)
    (X Y : C.Party → Shares C Bit) (n : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C Bit × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (z : Shares C Bit), (∀ k, ∑ T, z T k = ∑ i, mulRep K (localContext i) (X i) (Y i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let y ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0),
          ⟨recordMode K mode i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0) n,
            lab + 1, (st i).tag⟩)) >>= honestRounds F reply fuel)).run' s'}[event y] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realRunBuildingBlocks K (prssCtx keys kT kP i) mode).mult (X i) (Y i) n).run (st i) >>=
        g i) >>= honestRounds F reply (fuel + mode.rounds))).run' s}[event z] ≤ ε := by
  simp only [realMult_run, hL]
  refine draw_step prims F reply _ _ (fun i => FrameR.prssDraw _ _ FrameR.bitDraw _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  set rr := fun T => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.term T) (kT T) lab 0 n)
  set zz := fun p => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.pair p) (kP p) lab 0 n)
  cases mode with
  | peer =>
    simp only [reshareWith, reshare_run, bind_assoc, pure_bind, ReshareMode.rounds]
    rw [honestRounds_exchange F reply fuel (fun i => reshareOut K (prssCtx keys kT kP i) bitCodec
      (honestR rr i) (honestZ zz i) (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n) _
      fun k j => isAbort_reshareOut K _ bitCodec_roundTrip _ _ _ _ _ _]
    set Z := honestShare K (prssCtx keys kT kP) rr zz (fun i => mulRep K (prssCtx keys kT kP i) (X i) (Y i))
    have hz : ∀ i, reshareZ K (prssCtx keys kT kP i) bitCodec (honestR rr i) (honestZ zz i)
        (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n
          (fun k => reshareOut K (prssCtx keys kT kP k) bitCodec (honestR rr k) (honestZ zz k)
            (mulRep K (prssCtx keys kT kP k) (X k) (Y k)) n i) =
        fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0 := fun i => funext fun T => funext fun k =>
      reshareZ_honest K (prssCtx keys kT kP) rr zz _ bitCodec bitCodec_roundTrip (fun _ => rfl) n i T k
    simp only [hz, nextLabel, hL, prssCtx_self]
    exact h Z (fun k => sum_honestShare K (prssCtx keys kT kP) rr zz _ (fun _ => rfl) k) s' hn' hle hfr
  | collector =>
    simp only [reshareWith, reshareCollector_run, bind_assoc, pure_bind, ReshareMode.rounds, prssCtx_self]
    rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
    rw [honestRounds_exchange F reply (fuel + 1) (fun i => colOut1 K i (honestR rr i) (honestZ zz i)
      (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n) _ fun k j => isAbort_colOut1 K _ _ _ _ _ _]
    rw [honestRounds_exchange F reply fuel (fun i => colOut2 K i (honestR rr i) (honestZ zz i)
      (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n
        (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (mulRep K (prssCtx keys kT kP k') (X k') (Y k')) n i))
      _ fun k j => isAbort_colOut2 K _ _ _ _ _ _ _]
    have hz : ∀ j, colZ K j (honestR rr j) (honestZ zz j) (mulRep K (prssCtx keys kT kP j) (X j) (Y j)) n
        (fun k => colOut1 K k (honestR rr k) (honestZ zz k) (mulRep K (prssCtx keys kT kP k) (X k) (Y k)) n j)
        (fun k => colOut2 K k (honestR rr k) (honestZ zz k) (mulRep K (prssCtx keys kT kP k) (X k) (Y k)) n
          (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (mulRep K (prssCtx keys kT kP k') (X k') (Y k')) n k)
          j) = fun T k => if j ∈ C.holders T ∧ k < n then
            colShare K rr zz (fun i => mulRep K (prssCtx keys kT kP i) (X i) (Y i)) T k else 0 :=
      fun j => funext fun T => funext fun k =>
        colZ_honest K rr zz (fun i => mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n j T k
    simp only [hz, nextLabel, hL]
    exact h _ (fun k => sum_colShare K rr zz _ k) s' hn' hle hfr

end MultSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section ReplaySteps

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- A run of a computation of `H` and `PRG` gives the value under every `H` that agrees with a later
cache. -/
theorem replay_D {β : Type} {n : ℕ} (oa : Fin n → OracleComp (RoSpec C) β) (s : HashCache C)
    (z) (hz : z ∈ support ((simulateQ (localAnswer prims)
      (OverPermutation.sequenceFin fun i => liftComp (oa i) (LocalSpec C))).run s))
    (h : Query C → HashOutput) (hg : Good prims h) (s' : HashCache C) (hle : z.2 ≤ s') (ha : Agrees h s') :
    ∀ i, z.1 i = D prims h (oa i) := by
  obtain ⟨-, -, hsupp⟩ := localRun_support _ s z hz
  have := hsupp h hg (ha.mono hle)
  rw [simulateQ_sequenceFin] at this
  simp only [simulateQ_fixedLocal_liftComp] at this
  rw [sequenceFin_pure] at this
  simp only [support_pure, Set.mem_singleton_iff] at this
  intro i
  rw [this]

/-- `draw_step` whose continuation knows the values under every later `H`. -/
theorem draw_step2 {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (RoSpec C) β) (hframe : ∀ i, FrameR prims (oa i))
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (w : C.Party → β) (s' : HashCache C), (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        ∀ i, w i = D prims h' (oa i)) → NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (w i)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  refine probEvent_honest_local prims F reply fuel oa g event s ε fun z hz => ?_
  obtain ⟨hle, hn', -⟩ := localRun_D prims oa s hn z hz
  have hfr := FrameL.sequenceFin (prims := prims) (fun i => liftComp (oa i) (LocalSpec C))
    (fun i => FrameL.liftComp (hframe i)) s z hz
  exact h z.1 z.2 (fun h' s'' hg hle' ha => replay_D prims oa s z hz h' hg s'' hle' ha) hn' hle hfr

end ReplaySteps

section RepSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem FrameR.copyHashes (count : ℕ) (v : Shares C Bit) :
    FrameR prims (C.terms.mapM fun T => ThresholdLeanXmss.hashQuery (C := C) (.copy (vector count (v T)))) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)) _

theorem isAbort_repOutbox (i : C.Party) (v : Shares C Bit) (count : ℕ) (ds : List HashOutput) (j : C.Party) :
    Msg.isAbort (repOutbox (E := E) K i v count ds j) = false := by
  unfold repOutbox; split_ifs <;> rfl

/-- An honest `OpenRep`. Each operator opens the shared value at the positions below `count`. -/
theorem openRep_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (vr : C.Party → Shares C Bit) (w : Shares C Bit) (count : ℕ)
    (hvr : ∀ i T g, i ∈ C.holders T → g < count → vr i T g = w T g)
    (f : C.Party → (ℕ → Bit) → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (V : C.Party → ℕ → Bit), (∀ i g, g < count → V i g = ∑ T, w T g) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => f i (V i)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => openRep K (localContext i) (vr i) count >>= f i) >>=
        honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  simp only [openRep_eq, bind_assoc]
  refine draw_step2 prims F reply (fuel + 1) _ (fun i => FrameR.copyHashes prims count (vr i)) _ event s hn ε
    fun ds s₁ hds hn₁ hle₁ hfr₁ => ?_
  rw [honestRounds_exchange F reply fuel (fun i => repOutbox (E := E) K i (vr i) count (ds i)) _
    fun k j => isAbort_repOutbox K _ _ _ _ _]
  have hcopy : ∀ i T, vector count (repCopy K i (vr i) count (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) T) =
      vector count (w T) := fun i T => vector_congr' _ _ _ fun g hg => openCopy_eq K i _ w vr hvr ds T g hg
  simp only [hcopy]
  refine draw_step2 prims F reply fuel (fun i => C.terms.mapM fun T => hashQuery (C := C) (.copy (vector count (w T))))
    (fun i => FrameR.copyHashes prims count w) _ event s₁ hn₁ ε fun cs s₂ hcs hn₂ hle₂ hfr₂ => ?_
  obtain ⟨h₂, hg₂, ha₂⟩ : ∃ h₂, Good prims h₂ ∧ Agrees h₂ s₂ := ⟨hashOf prims s₂, good_hashOf prims s₂,
    agrees_hashOf prims hn₂⟩
  have hcs' : ∀ i, cs i = C.terms.map fun T => h₂ (.copy (vector count (w T))) := fun i => by
    rw [hcs h₂ s₂ hg₂ le_rfl ha₂ i, D_mapM]; simp [D_hashQuery]
  have hds' : ∀ i, ds i = C.terms.map fun T => h₂ (.copy (vector count (vr i T))) := fun i => by
    rw [hds h₂ s₂ hg₂ hle₂ ha₂ i, D_mapM]; simp [D_hashQuery]
  have hcheck : ∀ i, repCheck K i (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) (cs i) := fun i => by
    rw [hcs' i]
    refine repCheck_honest K i count vr ds (fun T => h₂ (.copy (vector count (w T)))) (fun j => by simp [hds' j])
      fun j T hj => ?_
    rw [hds' j, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_terms T))]
    simp only [Option.map_some, List.getElem_idxOf]
    rw [vector_congr' count _ _ fun g hg => hvr j T g hj hg]
  simp only [require_bind_of (hcheck _), pure_bind]
  refine h _ (fun i g hg => Finset.sum_congr rfl fun T _ => openCopy_eq K i _ w vr hvr ds T g hg) s₂ hn₂
    (hle₁.trans hle₂) fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)

end RepSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RerandStep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- An honest real `Rerand`, a peer reshare of the owner sums. -/
theorem rerand_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (mode : ReshareMode)
    (V : C.Party → Shares C Bit) (n : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C Bit × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (z : Shares C Bit), (∀ k, ∑ T, z T k = ∑ i, ownerSum K (localContext i) (V i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let y ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0),
          ⟨recordMode K .peer i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0) n,
            lab + 1, (st i).tag⟩)) >>= honestRounds F reply fuel)).run' s'}[event y] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => ((realRunBuildingBlocks K (prssCtx keys kT kP i) mode).rerand (V i) n).run (st i) >>=
        g i) >>= honestRounds F reply (fuel + 1))).run' s}[event z] ≤ ε := by
  simp only [realRerand_run, hL]
  refine draw_step prims F reply _ _ (fun i => FrameR.prssDraw _ _ FrameR.bitDraw _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  set rr := fun T => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.term T) (kT T) lab 0 n)
  set zz := fun p => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.pair p) (kP p) lab 0 n)
  simp only [reshare_run, bind_assoc, pure_bind]
  rw [honestRounds_exchange F reply fuel (fun i => reshareOut K (prssCtx keys kT kP i) bitCodec
    (honestR rr i) (honestZ zz i) (ownerSum K (prssCtx keys kT kP i) (V i)) n) _
    fun k j => isAbort_reshareOut K _ bitCodec_roundTrip _ _ _ _ _ _]
  set Z := honestShare K (prssCtx keys kT kP) rr zz (fun i => ownerSum K (prssCtx keys kT kP i) (V i))
  have hz : ∀ i, reshareZ K (prssCtx keys kT kP i) bitCodec (honestR rr i) (honestZ zz i)
      (ownerSum K (prssCtx keys kT kP i) (V i)) n
        (fun k => reshareOut K (prssCtx keys kT kP k) bitCodec (honestR rr k) (honestZ zz k)
          (ownerSum K (prssCtx keys kT kP k) (V k)) n i) =
      fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0 := fun i => funext fun T => funext fun k =>
    reshareZ_honest K (prssCtx keys kT kP) rr zz (fun i => ownerSum K (prssCtx keys kT kP i) (V i)) bitCodec
      bitCodec_roundTrip (fun _ => rfl) n i T k
  simp only [hz, nextLabel, hL, prssCtx_self]
  exact h Z (fun k => sum_honestShare K (prssCtx keys kT kP) rr zz
    (fun i => ownerSum K (prssCtx keys kT kP i) (V i)) (fun _ => rfl) k) s' hn' hle hfr

/-- The owner sums of views that agree on the held terms sum to the shared value. -/
theorem sum_ownerSum (Vv : C.Party → Shares C Bit) (W : Shares C Bit) (hV : ∀ i T, i ∈ C.holders T → Vv i T = W T)
    (k : ℕ) : ∑ i, ownerSum K (localContext i) (Vv i) k = shareValue W k := by
  unfold ownerSum shareValue
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := K.owner)
    (fun _ _ => Finset.mem_univ _) (f := fun T => W T k)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr ?_ fun T hT => ?_
  · ext T; rw [Finset.mem_filter, Finset.mem_filter]; simp [localContext]
  · have hT' : K.owner T = i := by simpa [localContext] using (Finset.mem_filter.mp hT).2
    rw [hV i T (hT' ▸ K.owner_held T)]

end RerandStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Lifted

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem liftedPart_nil (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart (E := E) [] part T k = 0 := by
  simp [liftedPart]

theorem liftedPart_cons (τ : Tuple C) (Ts : List (Tuple C)) (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart (E := E) (τ :: Ts) part T k =
      if k < τ.count then algebraMap Bit E (part τ T k) else liftedPart Ts part T (k - τ.count) := by
  unfold liftedPart
  rw [List.flatMap_cons]
  split_ifs with hk
  · rw [getD_append_of_lt _ _ _ _ (by simp [vector]; exact hk)]
    simp [vector, List.getD_eq_getElem?_getD, hk]
  · rw [getD_append_of_le _ _ _ _ (by simp [vector]; omega)]
    simp [vector]

/-- Tuples that agree at the held terms give the same lifted vectors there. -/
theorem liftedPart_agree' (i : C.Party) : ∀ (vs Ts : List (Tuple C)) (hlen : vs.length = Ts.length),
    (∀ m (hm : m < Ts.length), TupleAgrees i (vs[m]'(by rw [hlen]; exact hm)) Ts[m]) →
    ∀ T, i ∈ C.holders T → liftedPart (E := E) vs (·.x) T = liftedPart Ts (·.x) T ∧
      liftedPart (E := E) vs (·.y) T = liftedPart Ts (·.y) T ∧ liftedPart (E := E) vs (·.z) T = liftedPart Ts (·.z) T
  | [], [], _, _, T, _ => ⟨rfl, rfl, rfl⟩
  | v :: vs, τ :: Ts, hlen, hag, T, hT => by
    have h0 := hag 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hxyz, hc, -⟩ := h0
    obtain ⟨hx, hy, hz⟩ := hxyz T hT
    obtain ⟨ihx, ihy, ihz⟩ := liftedPart_agree' i vs Ts (by simpa using hlen)
      (fun m hm => by have := hag (m + 1) (by simpa using hm); simpa [List.getElem_cons_succ] using this) T hT
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      simp only [liftedPart_cons, hc, hx, hy, hz, ihx, ihy, ihz]

/-- Products give lifted vectors whose shared values multiply. -/
theorem liftedPart_product : ∀ (Ts : List (Tuple C)), (∀ τ ∈ Ts, IsProduct τ) → ∀ k,
    ∑ T, liftedPart (E := E) Ts (·.z) T k = (∑ T, liftedPart (E := E) Ts (·.x) T k) * ∑ T, liftedPart (E := E) Ts (·.y) T k
  | [], _, k => by simp [liftedPart_nil]
  | τ :: Ts, hp, k => by
    simp only [liftedPart_cons]
    split_ifs with hk
    · have := hp τ (List.mem_cons_self ..) k hk
      unfold shareValue at this
      rw [← map_sum, ← map_sum, ← map_sum, this, map_mul]
    · exact liftedPart_product Ts (fun τ' h => hp τ' (List.mem_cons_of_mem _ h)) _

end Lifted

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-- The bound of the aborts of a check of `cnt` tuples, when the cache holds expansions of `kc ≤ c` keys. -/
def checkCost (E : Type) [Fintype E] (c cnt kc : ℕ) : ℝ≥0∞ :=
  if cnt = 0 then 0 else ((kc : ℝ≥0∞) / 2 ^ 256 + sliceBits / Fintype.card E) + chalErr E (c + 1) (halvings cnt + 1)

/-- The coin keys of a check of `cnt` tuples. -/
def checkKeys (cnt : ℕ) : ℕ := if cnt = 0 then 0 else halvings cnt + 2

/-- The rounds and the round labels of a check of `cnt` tuples. -/
def checkLabels (cnt : ℕ) : ℕ := if cnt = 0 then 0 else 2 * halvings cnt + 5

theorem CacheOK.mono_label {C : Committee} {Ks : Finset HashOutput} {L L' : ℕ} {s : HashCache C}
    (h : CacheOK Ks L s) (hL : L ≤ L') : CacheOK Ks L' s := fun q hq =>
  ⟨(h q hq).1, fun tag ρ v hv => by have := (h q hq).2 tag ρ v hv; omega⟩

section CheckAny

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

omit [Fintype E] [DecidableEq E] in
theorem check_zero_run {ι : Type} {G : OracleSpec ι} (ctx : Context C)
    (buildingBlocks : CheckBuildingBlocks C E G)
    (tuples : List (Tuple C)) (h0 : (tuples.map (·.count)).sum = 0) (st : RunState C) :
    (check K ctx buildingBlocks tuples).run st = pure ((), st) := by
  simp [check, h0]

/-- An honest real check of correct tuples, with no tuple or with some tuples. -/
theorem real_check_any [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R)
    (tuples : C.Party → List (Tuple C)) (cnt : ℕ) (hcnt : ∀ i, ((tuples i).map (·.count)).sum = cnt)
    (LX LY LZ : Shares C E)
    (hag : ∀ i T, i ∈ C.holders T → liftedPart (E := E) (tuples i) (·.x) T = LX T ∧
      liftedPart (E := E) (tuples i) (·.y) T = LY T ∧ liftedPart (E := E) (tuples i) (·.z) T = LZ T)
    (hprod : ∀ k, ∑ T, LZ T k = (∑ T, LX T k) * ∑ T, LY T k)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → Unit × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + checkKeys cnt → CacheOK Ks' (lab + checkLabels cnt) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((), ⟨hist' i, lab + checkLabels cnt, tg⟩)) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart
          (fun i => (check K (prssCtx keys kT kP i) (realCheckBuildingBlocks K (prssCtx keys kT kP i))
        (tuples i)).run ⟨hist i, lab, tg⟩ >>= g i) >>=
          honestRounds F reply (fuel + checkLabels cnt))).run' s}[event z] ≤ δ * checkCost E c cnt Ks.card + ε := by
  by_cases hpos : cnt = 0
  · have h0 : ∀ i, ((tuples i).map (·.count)).sum = 0 := fun i => by rw [hcnt i, hpos]
    simp only [check_zero_run _ _ _ _ (h0 _), pure_bind, checkCost, checkLabels, checkKeys, ite_eq_left hpos, mul_zero, zero_add,
      Nat.add_zero] at h ⊢
    exact h hist Ks s (by omega) (hs.mono_label hLk) hn le_rfl
  · simp only [checkCost, checkLabels, checkKeys, ite_eq_right hpos] at h ⊢
    rw [mul_add δ _ (chalErr E (c + 1) (halvings cnt + 1)), add_assoc]
    exact real_check_bound prims K keys kT kP F reply tuples cnt hcnt hpos LX LY LZ hag hprod hist hh lab tg Lk c Ks
      hLk hKs s hn hs fuel (fun i st => g i ((), st)) event δ hδ ε h

end CheckAny

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Tail

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

omit [Fintype E] [DecidableEq E] in
theorem histAgree_recordMode (mode : ReshareMode) (h : C.Party → C.Term → List Bit) (hh : HistAgree h)
    (zv : C.Party → Shares C Bit) (Z : Shares C Bit) (n : ℕ)
    (hz : ∀ i T g, i ∈ C.holders T → g < n → zv i T g = Z T g) :
    HistAgree (fun i => recordMode K mode i (h i) (zv i) n) := by
  intro T i hi j hj
  simp only [recordMode, ite_eq_left hi, ite_eq_left hj, hh T i hi j hj]
  congr 1
  refine List.flatMap_congr fun g hg => ?_
  have hg' : g < n := List.mem_range.1 (List.mem_filter.1 hg).1
  simp only [Function.comp_apply, hz i T g hi hg', hz j T g hj hg']

omit [Fintype E] [DecidableEq E] in
theorem openRep_prssCtx {ι : Type} {G : OracleSpec ι} (i : C.Party) :
    openRep (G := G) K (prssCtx keys kT kP i) = openRep K (localContext i) := rfl

theorem map_count_of_agree (i : C.Party) (vs Ts : List (Tuple C)) (hlen : vs.length = Ts.length)
    (hag : ∀ m (hm : m < Ts.length), TupleAgrees i (vs[m]'(by rw [hlen]; exact hm)) Ts[m]) :
    vs.map (·.count) = Ts.map (·.count) :=
  List.ext_getElem (by simp [hlen]) fun m h₁ h₂ => by
    simp only [List.getElem_map]
    exact (hag m (by simpa using h₂)).2.1

/-- The tail of an honest real batch: `Rerand`, the check and `OpenRep`. Every operator gets the
outputs of the circuits. -/
theorem tail_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit))
    (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit)) (Ts : List (Tuple C))
    (hinv : LayerInv jobs x (depth jobs) p W Ts) (cnt : ℕ)
    (hcnt : (Ts.map (·.count)).sum + (outputsOf jobs).length = cnt)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + checkKeys cnt → CacheOK Ks' (lab + 1 + checkLabels cnt) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (mainOutputs jobs x, ⟨hist' i, lab + 1 + checkLabels cnt, tg⟩)) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (tailBody K (realRunBuildingBlocks K (prssCtx keys kT kP i) mode) jobs (p i)).run
        ⟨hist i, lab, tg⟩ >>= g i) >>= honestRounds F reply (fuel + 1 + checkLabels cnt + 1))).run' s}[event z] ≤
      δ * checkCost E c cnt Ks.card + ε := by
  set n := (outputsOf jobs).length with hn_def
  simp only [tailBody, StateT.run_bind, bind_assoc]
  refine rerand_step prims K keys kT kP F reply (fuel + 1 + checkLabels cnt) mode
    (fun i => outputShares K jobs (p i).1) n _ lab (fun _ => rfl) _ event s hn _ fun z hz s₁ hn₁ hle₁ hfr₁ => ?_
  dsimp only
  have hO : ∀ i T, i ∈ C.holders T → outputShares K jobs (p i).1 T = outputShares K jobs W T :=
    fun i T h => outputShares_congr K jobs _ _ T (hinv.agree i T h)
  have hsum : ∀ k, ∑ T, z T k = shareValue (outputShares K jobs W) k := fun k => by
    rw [hz k, sum_ownerSum K _ _ hO]
  set zv : C.Party → Shares C Bit := fun i T k => if i ∈ C.holders T ∧ k < n then z T k else 0 with hzv
  set w : Shares C Bit := fun T k => if k < n then z T k else 0 with hw
  set Ts' := Ts ++ [(⟨outputShares K jobs W, one K, w, n, .peer⟩ : Tuple C)] with hTs'
  have hlen' : ∀ i, ((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)]).length = Ts'.length :=
    fun i => by simp [hTs', hinv.length_tuples]
  have hag' : ∀ i, ∀ m (hm : m < Ts'.length), TupleAgrees i
      (((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)])[m]'(by rw [hlen' i]; exact hm)) Ts'[m] :=
    fun i => tupleAgrees_append i _ _ _ _ (hinv.length_tuples i) (hinv.agree_tuples i)
      ⟨fun T hT => ⟨hO i T hT, rfl, funext fun g => by simp [hzv, hw, hT]⟩, rfl, rfl⟩
  have hprodTs : ∀ τ ∈ Ts', IsProduct τ := by
    intro τ hτ
    rcases List.mem_append.1 hτ with hτ | hτ
    · exact hinv.product τ hτ
    · simp only [List.mem_singleton] at hτ
      subst hτ
      intro g hg
      rw [shareValue_one, mul_one, ← hsum g]
      simp only [shareValue, hw, ite_eq_left hg]
  have hcnt' : ∀ i, (((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)]).map (·.count)).sum = cnt :=
    fun i => by
      rw [map_count_of_agree i _ _ (hlen' i) (hag' i), hTs', List.map_append, List.sum_append, ← hcnt]
      simp
  have hh₁ := histAgree_recordMode K .peer hist hh zv z n (fun i T g hi hg => by simp [hzv, hi, hg])
  simp only [realRunBuildingBlocks]
  rw [show fuel + 1 + checkLabels cnt = (fuel + 1) + checkLabels cnt from rfl]
  refine real_check_any prims K keys kT kP F reply _ cnt hcnt' (liftedPart Ts' (·.x)) (liftedPart Ts' (·.y))
    (liftedPart Ts' (·.z)) (fun i T hT => liftedPart_agree' i _ Ts' (hlen' i) (hag' i) T hT)
    (liftedPart_product Ts' hprodTs) _ hh₁ (lab + 1) tg Lk c Ks (by omega) hKs s₁ hn₁ (cacheOK_of_frame hs hfr₁)
    (fuel + 1) _ event δ hδ ε fun hist' Ks' s₂ hKs₂ hs₂ hn₂ hle₂ => ?_
  dsimp only
  simp only [StateT.run_lift, bind_assoc, pure_bind, openRep_prssCtx]
  refine openRep_step prims K F reply fuel zv w n (fun i T g hi hg => by simp [hzv, hw, hi, hg]) _ event s₂ hn₂ ε
    fun V hV s₃ hn₃ hle₃ hfr₃ => ?_
  have hA : ∀ i, assemble jobs (V i) = mainOutputs jobs x := fun i =>
    assemble_eq K jobs x p W Ts hinv (V i) fun g hg => by
      rw [hV i g hg, ← hsum g]; simp only [hw]; exact Finset.sum_congr rfl fun T _ => ite_eq_left hg
  simp only [hA]
  have hs₃ : CacheOK Ks' (lab + 1 + checkLabels cnt) s₃ := cacheOK_of_frame hs₂ hfr₃
  exact h hist' Ks' s₃ hKs₂ hs₃ hn₃ (hle₁.trans (hle₂.trans hle₃))

end Tail

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Batch

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem tupleCount_eq (jobs : List Circuit) :
    tupleCount jobs = ((List.range (depth jobs)).map fun l => (gatesAt jobs l).length).sum + (outputsOf jobs).length := by
  unfold tupleCount
  congr 1
  · congr 1
    refine List.map_congr_left fun l _ => ?_
    rw [gatesAt_eq, length_flatIdx, List.map_map]
    rfl
  · rw [outputsOf_eq, length_flatIdx, List.map_map]
    rfl

theorem layers_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit)) :
    ∀ (k l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
      (Ts : List (Tuple C)), l + k = depth jobs → LayerInv jobs x l p W Ts →
      (Ts.map (·.count)).sum = ((List.range l).map fun l' => (gatesAt jobs l').length).sum →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
      (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞), (event (fun _ => none) → 1 ≤ δ) → ∀ (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + checkKeys (tupleCount jobs) →
        CacheOK Ks' (lab + k + 1 + checkLabels (tupleCount jobs)) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i (mainOutputs jobs x, ⟨hist' i, lab + k + 1 + checkLabels (tupleCount jobs), tg⟩)) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' l k).foldlM (layerBody K (realRunBuildingBlocks K (prssCtx keys kT kP i) mode) jobs)
          (p i)).run ⟨hist i, lab, tg⟩ >>= fun q =>
            (tailBody K (realRunBuildingBlocks K (prssCtx keys kT kP i) mode) jobs q.1).run q.2 >>= g i) >>=
          honestRounds F reply (fuel + k * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1))).run' s}[event z] ≤
        δ * checkCost E c (tupleCount jobs) Ks.card + ε := by
  intro k
  induction k with
  | zero =>
    intro l p W Ts hl hinv hTs hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, zero_mul, Nat.add_zero] at h ⊢
    rw [Nat.add_zero] at hl
    subst hl
    exact tail_bound prims K keys kT kP F reply mode jobs x p W Ts hinv (tupleCount jobs)
      (by rw [hTs, tupleCount_eq]) hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
  | succ k ih =>
    intro l p W Ts hl hinv hTs hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    rw [List.range'_succ, show fuel + (k + 1) * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1 =
      (fuel + k * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1) + mode.rounds by ring]
    simp only [List.foldlM_cons, layerBody, StateT.run_bind, bind_assoc, pure_bind]
    refine mult_step prims K keys kT kP F reply _ mode (fun i => layerX K jobs l (p i).1)
      (fun i => layerY K jobs l (p i).1) (gatesAt jobs l).length _ lab (fun _ => rfl) _ event s hn _
      fun z hz s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hinv' := layerInv_step K jobs x mode l p W Ts hinv z hz
    simp only [realRunBuildingBlocks] at hinv' ⊢
    refine ih (l + 1) _ _ _ (by omega) hinv' ?_ _
      (histAgree_recordMode K mode hist hh _ z _ fun i T g hi hg => by simp [hi, hg]) (lab + 1) tg Lk c Ks
      (by omega) hKs s₁ hn₁ (cacheOK_of_frame hs hfr₁) fuel g event δ hδ ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · rw [List.map_append, List.sum_append, hTs, List.range_succ, List.map_append, List.sum_append]
      simp
    · have hlab : lab + 1 + k + 1 + checkLabels (tupleCount jobs) = lab + (k + 1) + 1 + checkLabels (tupleCount jobs) := by
        ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' h1 h2 h3 (hle₁.trans h4)

end Batch

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Bits

theorem getD_bitsOfDigest (d : Digest) (b : ℕ) (hb : b < digestBits) :
    (bitsOfDigest d).getD b 0 = if d.getLsbD b then 1 else 0 := by
  simp [bitsOfDigest, List.getD_eq_getElem?_getD, hb]

theorem bit_xor (a b : Bool) : ((if (a ^^ b) then 1 else 0 : Bit)) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem getD_bitsOfDigest_xor (d e : Digest) (b : ℕ) (hb : b < digestBits) :
    (bitsOfDigest (d ^^^ e)).getD b 0 = (bitsOfDigest d).getD b 0 + (bitsOfDigest e).getD b 0 := by
  rw [getD_bitsOfDigest _ _ hb, getD_bitsOfDigest _ _ hb, getD_bitsOfDigest _ _ hb, BitVec.getLsbD_xor, bit_xor]

theorem getD_bitsOfDigest_foldl (ds : List Digest) (acc : Digest) (b : ℕ) (hb : b < digestBits) :
    (bitsOfDigest (ds.foldl (· ^^^ ·) acc)).getD b 0 =
      (bitsOfDigest acc).getD b 0 + (ds.map fun d => (bitsOfDigest d).getD b 0).sum := by
  induction ds generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, getD_bitsOfDigest_xor _ _ _ hb, List.map_cons, List.sum_cons, add_assoc]

theorem bitsOfDigest_zero_getD (b : ℕ) : (bitsOfDigest (0 : Digest)).getD b 0 = 0 := by
  by_cases hb : b < digestBits
  · rw [getD_bitsOfDigest _ _ hb]; simp
  · simp [bitsOfDigest, List.getD_eq_getElem?_getD, hb]

/-- An entry of a concatenation of blocks of one length. -/
theorem getD_flatMap_block {β : Type} (f : β → List Bit) (w : ℕ) (hf : ∀ x, (f x).length = w) :
    ∀ (L : List β) (m b : ℕ) (hm : m < L.length), b < w → (L.flatMap f).getD (w * m + b) 0 = (f L[m]).getD b 0
  | [], m, _, hm, _ => absurd hm (by simp)
  | x :: L, m, b, hm, hb => by
    rw [List.flatMap_cons]
    rcases m with _ | m
    · rw [getD_append_of_lt _ _ _ _ (by rw [hf]; omega)]; simp
    · rw [getD_append_of_le _ _ _ _ (by rw [hf]; nlinarith), hf,
        show w * (m + 1) + b - w = w * m + b by rw [Nat.mul_succ]; omega]
      exact getD_flatMap_block f w hf L m b (by simpa using hm) hb

theorem length_flatMap_block {β : Type} (f : β → List Bit) (w : ℕ) (hf : ∀ x, (f x).length = w) (L : List β) :
    (L.flatMap f).length = w * L.length := by
  induction L with
  | nil => simp
  | cons x L ih => simp [hf, ih]; ring

end Bits

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Inputs

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι} (prims : Primitives)

/-- The queries of `inputShares`. -/
def inputQuery (ctx : Context C) (job : Job) : OracleComp (RoSpec C) (C.Term → List Bit) := do
  let terms ← C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
    else pure []
  pure fun T => terms.getD (C.terms.idxOf T) []

omit [Field E] [Algebra Bit E] in
theorem inputShares_eq (ctx : Context C) (job : Job) :
    (inputShares (E := E) (G := G) ctx job) = oracleStep (inputQuery ctx job) := by
  simp only [inputShares, inputQuery]
  rw [oracleStep_bind]
  simp only [oracleStep_pure]

omit [Field E] [Algebra Bit E] in
theorem mapM_oracleStep {α β : Type} (q : α → OracleComp (RoSpec C) β) :
    ∀ l : List α, l.mapM (fun a => (oracleStep (E := E) (G := G) (q a))) = oracleStep (l.mapM q)
  | [] => by simp [oracleStep_pure]
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, oracleStep_bind, mapM_oracleStep q l]
    refine congrArg (_ >>= ·) (funext fun b => ?_)
    rw [oracleStep_bind]
    simp only [oracleStep_pure]

theorem D_flatMapM {α β : Type} (h : Query C → HashOutput) (f : α → OracleComp (RoSpec C) (List β)) :
    ∀ l : List α, D prims h (l.flatMapM f) = l.flatMap fun a => D prims h (f a)
  | [] => rfl
  | a :: l => by
    rw [List.flatMapM_cons, D_bind, D_bind, D_flatMapM h f l, D_pure, List.flatMap_cons]

/-- The view of term `T` of the input wires of a job, with `H` fixed to `h`. -/
def inputBits (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (job : Job) (T : C.Term) : List Bit :=
  job.points.flatMap fun x => bitsOfDigest (truncateHash (h (.prf (seeds T) x)))

theorem D_inputQuery (h : Query C → HashOutput) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party)
    (job : Job) (T : C.Term) :
    D prims h (inputQuery (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) job) T =
      if i ∈ C.holders T then inputBits h seeds job T else [] := by
  unfold inputQuery
  simp only [D_bind, D_pure, D_mapM]
  rw [getD_terms_idxOf]
  by_cases hi : i ∈ C.holders T
  · simp only [prssCtx, ite_eq_left hi, D_flatMapM, prf, D_map, D_hashQuery, inputBits, dealtKeys]
  · simp [prssCtx, hi, D_pure]

end Inputs

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section InputValues

variable {C : Committee} (prims : Primitives)

/-- The inputs of an honest batch with `H` fixed to `h`. -/
def batchInputs (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (jobs : List Job) :
    C.Party → List (C.Term → List Bit) :=
  fun i => jobs.map fun job T => if i ∈ C.holders T then inputBits h seeds job T else []

theorem length_inputBits (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (job : Job) (T : C.Term) :
    (inputBits h seeds job T).length = digestBits * job.points.length := by
  unfold inputBits
  exact length_flatMap_block _ _ (fun _ => length_bitsOfDigest _) _

theorem batchInputs_main (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (circuits : Circuits)
    (parameter : PublicParameter) (jobs : List Job) :
    MainInputs (jobs.map (circuits parameter ·.kind)) noCoalition (batchInputs h seeds jobs) := by
  refine ⟨jobs.map fun job => digestBits * job.points.length, by simp, fun i _ => ⟨by simp [batchInputs], ?_⟩, ?_⟩
  · intro k hk T
    simp only [List.length_map] at hk
    simp only [batchInputs, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
    split_ifs with hi
    · rw [length_inputBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    · rfl
  · intro k T i hi j hj _ _
    simp only [batchInputs, List.getElem?_map]
    rcases jobs[k]? with _ | job
    · rfl
    · simp [hi, hj]

theorem sum_terms_eq {M : Type} [AddCommMonoid M] (f : C.Term → M) : (C.terms.map f).sum = ∑ T, f T := by
  unfold Committee.terms
  exact Finset.sum_map_toList _ _

theorem inputValue_inputBits (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (job : Job) :
    inputValue (inputBits h seeds job) =
      (job.points.map fun x => (C.terms.map fun T => truncateHash (h (.prf (seeds T) x))).foldl (· ^^^ ·) 0).flatMap
        bitsOfDigest := by
  obtain ⟨T₀, -⟩ := lackedTerm_empty (C := C)
  have hne : C.terms ≠ [] := List.ne_nil_of_mem (mem_terms T₀)
  unfold inputValue
  rw [foldl_max_const _ (digestBits * job.points.length) (by simpa using hne)
    (fun a ha => by obtain ⟨T, -, rfl⟩ := List.mem_map.1 ha; exact length_inputBits h seeds job T)]
  refine List.ext_getElem (by rw [List.length_map, List.length_range,
    length_flatMap_block _ _ (fun _ => length_bitsOfDigest _), List.length_map]) fun g h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  simp only [List.length_map, List.length_range] at h₁
  have hd : 0 < digestBits := by decide
  obtain ⟨m, b, hb, rfl⟩ : ∃ m b, b < digestBits ∧ g = digestBits * m + b :=
    ⟨g / digestBits, g % digestBits, Nat.mod_lt _ hd, (Nat.div_add_mod g digestBits).symm⟩
  have hm : m < job.points.length := by
    by_contra hc; push Not at hc; nlinarith
  rw [List.getElem_eq_getD 0, getD_flatMap_block _ _ (fun _ => length_bitsOfDigest _) _ m b (by simpa using hm) hb]
  simp only [List.getElem_map, getD_bitsOfDigest_foldl _ _ _ hb, bitsOfDigest_zero_getD, zero_add, List.map_map]
  rw [sum_terms_eq]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold inputBits
  rw [getD_flatMap_block _ _ (fun _ => length_bitsOfDigest _) _ m b hm hb]
  rfl

theorem D_evalJob (h : Query C → HashOutput) (circuits : Circuits) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (job : Job) :
    D prims h (evalJob circuits parameter seeds job) = (circuits parameter job.kind).eval
      ((job.points.map fun x => (C.terms.map fun T => truncateHash (h (.prf (seeds T) x))).foldl (· ^^^ ·) 0).flatMap
        bitsOfDigest) := by
  simp only [evalJob, prfValue, prf, D_bind, D_pure, D_mapM, D_map, D_hashQuery]

theorem mainOutputs_batch (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (circuits : Circuits)
    (parameter : PublicParameter) (jobs : List Job) :
    mainOutputs (jobs.map (circuits parameter ·.kind)) (batchInputs h seeds jobs) =
      jobs.map fun job => D prims h (evalJob circuits parameter seeds job) := by
  unfold mainOutputs
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.length_map] at h₂
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add, D_evalJob]
  congr 1
  rw [← inputValue_inputBits]
  congr 1
  funext T
  refine reconstruct_of_agree _ T _ fun i hi => ⟨fun T => if i ∈ C.holders T then inputBits h seeds jobs[k] T else [],
    ?_, by simp [hi]⟩
  simp only [batchInputs, List.getElem?_map, List.getElem?_eq_getElem h₂, Option.map_some]

end InputValues

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section BatchStep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E)

theorem FrameR.flatMapM {α β : Type} (f : α → OracleComp (RoSpec C) (List β)) (hf : ∀ a, FrameR prims (f a)) :
    ∀ l : List α, FrameR prims (l.flatMapM f)
  | [] => FrameR.pure _
  | a :: l => by
    rw [List.flatMapM_cons]
    exact (hf a).bind fun _ => (FrameR.flatMapM f hf l).bind fun _ => FrameR.pure _

theorem FrameR.inputQuery (ctx : Context C) (job : Job) : FrameR prims (inputQuery ctx job) := by
  unfold ThresholdLeanXmssSecurity.inputQuery
  refine (FrameR.mapM _ (fun T => FrameR.ite _ (FrameR.flatMapM prims _ (fun x => ?_) _) (FrameR.pure _)) _).bind
    fun _ => FrameR.pure _
  exact (FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)).map _ |>.map _

omit [Fintype E] [DecidableEq E] in
theorem inputShares_fun {ι : Type} {G : OracleSpec ι} (ctx : Context C) :
    (inputShares (E := E) (G := G) ctx) = fun job => oracleStep (inputQuery ctx job) :=
  funext (inputShares_eq ctx)

/-- One honest real batch of a ceremony, from its inputs on. Every operator gets the outputs of the
jobs in the clear. -/
theorem batch_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (jobs : List Job)
    (lab tg Lk c : ℕ) (Ks : Finset HashOutput) (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ) (ε : ℝ≥0∞)
    (h : ∀ (outs : List (List Bit)) (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        outs = jobs.map fun job => D prims h' (evalJob circuits parameter seeds job)) →
      Ks'.card ≤ c + checkKeys (tupleCount (jobs.map (circuits parameter ·.kind))) →
      CacheOK Ks' (lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
        checkLabels (tupleCount (jobs.map (circuits parameter ·.kind)))) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (outs, ⟨hist' i, lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))), tg⟩)) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => (jobs.mapM (inputShares (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i))) >>=
        fun inputs => (runJobs K (realRunBuildingBlocks K (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) mode)
          (jobs.map (circuits parameter ·.kind)) inputs).run ⟨fun _ => [], lab, tg⟩ >>= g i) >>=
        honestRounds F reply (fuel + depth (jobs.map (circuits parameter ·.kind)) * mode.rounds + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1))).run' s}[event z] ≤
      δ * checkCost E c (tupleCount (jobs.map (circuits parameter ·.kind))) Ks.card + ε := by
  set circs := jobs.map (circuits parameter ·.kind) with hcircs
  simp only [inputShares_fun, mapM_oracleStep]
  refine draw_step2 prims F reply _ (fun i => jobs.mapM (inputQuery (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)))
    (fun i => FrameR.mapM _ (fun job => FrameR.inputQuery prims _ job) _) _ event s hn _
    fun w s₁ hw hn₁ hle₁ hfr₁ => ?_
  have hwv : ∀ h' s'', Good prims h' → s₁ ≤ s'' → Agrees h' s'' → ∀ i, w i = batchInputs h' seeds jobs i := by
    intro h' s'' hg hle ha i
    rw [hw h' s'' hg hle ha i, D_mapM]
    exact List.map_congr_left fun job _ => funext fun T => D_inputQuery prims h' parameter seeds pairKeys kT kP i job T
  obtain ⟨h₁, hg₁, ha₁⟩ : ∃ h₁, Good prims h₁ ∧ Agrees h₁ s₁ := ⟨hashOf prims s₁, good_hashOf prims s₁,
    agrees_hashOf prims hn₁⟩
  have hw₁ : w = batchInputs h₁ seeds jobs := funext (hwv h₁ s₁ hg₁ le_rfl ha₁)
  rw [hw₁]
  simp only [runJobs_eq, StateT.run_bind, bind_assoc]
  rw [List.range_eq_range']
  have hW := layerInv_zero (jobs := circs) (x := batchInputs h₁ seeds jobs)
    (batchInputs_main h₁ seeds circuits parameter jobs)
  refine layers_bound prims K (dealtKeys parameter seeds pairKeys) kT kP F reply mode circs (batchInputs h₁ seeds jobs)
    (depth circs) 0 _ _ [] (by simp) hW (by simp) (fun _ _ => []) (fun _ _ _ _ _ => rfl) lab tg Lk c Ks hLk hKs s₁ hn₁
    (cacheOK_of_frame hs hfr₁) fuel g event δ hδ ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
  refine h _ hist' Ks' s' (fun h' s'' hg hle ha => ?_) h1 (by simpa using h2) h3 (hle₁.trans h4)
  rw [← mainOutputs_batch prims h' seeds circuits parameter jobs, ← hw₁]
  congr 1
  exact funext (hwv h' s'' hg (h4.trans hle) ha)

end BatchStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Chunks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (mode : ReshareMode)

/-- One batch of a real ceremony at operator `ctx.self`. -/
def realBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))) := do
  let (label, k) ← get
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let (outputs, state) ← StateT.lift ((runJobs K (realRunBuildingBlocks K ctx mode) (jobs.map (circuits parameter ·.kind))
    inputs).run ⟨fun _ => [], label, k⟩)
  set (state.label, k + 1)
  pure (some outputs)

omit [Fintype E] [DecidableEq E] in
theorem realBatch_run (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ) :
    (realBatch K circuits mode ctx parameter jobs).run st =
      jobs.mapM (inputShares ctx) >>= fun inputs =>
        (runJobs K (realRunBuildingBlocks K ctx mode) (jobs.map (circuits parameter ·.kind)) inputs).run
          ⟨fun _ => [], st.1, st.2⟩ >>= fun r => pure (some r.1, (r.2.label, st.2 + 1)) := by
  simp only [realBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    StateT.run_pure]

/-- The tuple bits of a batch of jobs. -/
def batchCount (parameter : PublicParameter) (jobs : List Job) : ℕ := tupleCount (jobs.map (circuits parameter ·.kind))

/-- The rounds of a batch of jobs. -/
def batchRounds (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  depth (jobs.map (circuits parameter ·.kind)) * mode.rounds + 1 + checkLabels (batchCount circuits parameter jobs) + 1

/-- The round labels of a batch of jobs. -/
def batchLabels (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  depth (jobs.map (circuits parameter ·.kind)) + 1 + checkLabels (batchCount circuits parameter jobs)

/-- The bound of the aborts of the batches `js` when `c` coin keys came before. -/
def chunksCost (E : Type) [Fintype E] (parameter : PublicParameter) : ℕ → List (List Job) → ℝ≥0∞
  | _, [] => 0
  | c, jobs :: js => checkCost E c (batchCount circuits parameter jobs) c +
      chunksCost E parameter (c + checkKeys (batchCount circuits parameter jobs)) js

omit [Field E] [Algebra Bit E] [DecidableEq E] in
theorem checkCost_mono (c cnt kc : ℕ) (h : kc ≤ c) : checkCost E c cnt kc ≤ checkCost E c cnt c := by
  unfold checkCost
  split_ifs
  · exact le_rfl
  · gcongr

theorem chunks_step [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) {α : Type} :
    ∀ (js : List (List Job)) (lab k Lk c : ℕ) (Ks : Finset HashOutput), Lk ≤ lab → Ks.card ≤ c →
      ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → List (Option (List (List Bit))) × (ℕ × ℕ) → PartyM C E RealSpec α)
      (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞), (event (fun _ => none) → 1 ≤ δ) → ∀ (ε : ℝ≥0∞),
      (∀ (outs : List (Option (List (List Bit)))) (Ks' : Finset HashOutput) (s' : HashCache C),
        (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
          outs = js.map fun jobs => some (jobs.map fun job => D prims h' (evalJob circuits parameter seeds job))) →
        Ks'.card ≤ c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum →
        CacheOK Ks' (lab + (js.map (batchLabels circuits parameter)).sum) s' → NoMpc s' → s ≤ s' →
        Pr{let z ← (simulateQ (localAnswer prims)
          (honestStart (fun i => g i (outs, (lab + (js.map (batchLabels circuits parameter)).sum, k + js.length))) >>=
            honestRounds F reply fuel)).run' s'}[event z] ≤ ε) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => (js.mapM (realBatch K circuits mode (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)
          parameter)).run (lab, k) >>= g i) >>=
          honestRounds F reply (fuel + (js.map (batchRounds circuits mode parameter)).sum))).run' s}[event z] ≤
        δ * chunksCost circuits E parameter c js + ε := by
  intro js
  induction js with
  | nil =>
    intro lab k Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    simp only [List.mapM_nil, StateT.run_pure, pure_bind, List.map_nil, List.sum_nil, Nat.add_zero, chunksCost,
      mul_zero, zero_add, List.length_nil] at h ⊢
    exact h [] Ks s (fun _ _ _ _ _ => rfl) hKs (hs.mono_label hLk) hn le_rfl
  | cons jobs js ih =>
    intro lab k Lk c Ks hLk hKs s hn hs fuel g event δ hδ ε h
    simp only [List.mapM_cons, StateT.run_bind, realBatch_run, bind_assoc, pure_bind, StateT.run_pure]
    rw [show fuel + ((jobs :: js).map (batchRounds circuits mode parameter)).sum =
      (fuel + (js.map (batchRounds circuits mode parameter)).sum) + depth (jobs.map (circuits parameter ·.kind)) * mode.rounds +
        1 + checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1 by
      simp only [List.map_cons, List.sum_cons, batchRounds, batchCount]; ring]
    refine le_trans (batch_step prims K F reply mode circuits parameter seeds pairKeys kT kP jobs lab k Lk c Ks hLk hKs s hn hs
      _ _ event δ hδ (δ * chunksCost circuits E parameter (c + checkKeys (batchCount circuits parameter jobs)) js + ε) ?_) ?_
    · intro outs hist' Ks' s' houts hKs' hs' hn' hle'
      dsimp only
      refine ih _ (k + 1) _ (c + checkKeys (batchCount circuits parameter jobs)) Ks' le_rfl hKs' s' hn' hs' fuel _ event δ hδ ε ?_
      intro outs' Ks'' s'' houts' hKs'' hs'' hn'' hle''
      dsimp only
      have hlab : lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + (js.map (batchLabels circuits parameter)).sum =
          lab + ((jobs :: js).map (batchLabels circuits parameter)).sum := by
        simp only [List.map_cons, List.sum_cons, batchLabels, batchCount]; ring
      have hk : k + 1 + js.length = k + (jobs :: js).length := by simp; ring
      rw [hlab, hk]
      refine h _ Ks'' s'' (fun h' s₃ hg hle ha => ?_) (by simp only [List.map_cons, List.sum_cons]; omega) (hlab ▸ hs'') hn''
        (hle'.trans hle'')
      rw [List.map_cons, houts h' s₃ hg (hle''.trans hle) ha, houts' h' s₃ hg hle ha]
    · rw [chunksCost, mul_add δ (checkCost E c _ c), add_assoc]
      gcongr
      exact checkCost_mono _ _ _ hKs

end Chunks

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section LocalStep

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after an own local computation of each operator. -/
theorem local_step {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (LocalSpec C) β) (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support ((simulateQ (localAnswer prims) (OverPermutation.sequenceFin oa)).run s),
      Pr{let y ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (z.1 i)) >>= honestRounds F reply fuel)).run' z.2}[event y] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => localStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  have hsame : SameRun prims (honestStart (fun i => localStep (oa i) >>= g i) >>= honestRounds F reply fuel)
      (OverPermutation.sequenceFin oa >>= fun b => honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel) := by
    have hstart : SameRun prims (honestStart fun i => localStep (oa i) >>= g i)
        (OverPermutation.sequenceFin oa >>= fun b => honestStart fun i => g i (b i)) := by
      unfold honestStart
      simp only [advance_localStep_bind]
      have h := sameRun_sequenceFin_dep prims oa (fun i u => advance (g i u).run) (fun _ _ v => v)
      refine (SameRun.of_eq ?_).trans (h.trans (SameRun.of_eq (bind_congr fun x => bind_pure _)))
      simp only [bind_pure]
    refine (hstart.bind fun _ => SameRun.refl _ _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  have hrun : Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => localStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] =
      Pr{let z ← (simulateQ (localAnswer prims) (OverPermutation.sequenceFin oa >>= fun b =>
        honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel)).run' s}[event z] := by
    simp only [StateT.run'_eq]
    exact ((hsame s).map _).prEvent_eq _
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  have := h z hz
  rwa [StateT.run'_eq] at this

/-- Each operator samples its own value from `p`, and the cache stays. -/
theorem sample_step {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (p : ProbComp β)
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ b : C.Party → β, Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => localStep (liftComp p (LocalSpec C)) >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  refine local_step prims F reply fuel _ g event s ε fun z hz => ?_
  have hp : IsLocalProb (C := C) (OverPermutation.sequenceFin fun _ : C.Party => liftComp p (LocalSpec C)) := by
    rw [← liftComp_sequenceFin]; exact IsLocalProb.liftComp _
  rw [(IsLocalProb.support_run prims hp s z hz).1]
  exact h z.1

end LocalStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section SetupStep

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

theorem FrameR.hashQuery' {q : Query C} (hq : ∀ k idx, q ≠ .expand k idx) (hq' : ∀ t ρ v, q ≠ .coinKey t ρ v) :
    FrameR prims (ThresholdLeanXmss.hashQuery q) :=
  FrameR.hashQuery (by rintro (⟨k, idx, h⟩ | ⟨t, ρ, v, h⟩); exacts [hq k idx h, hq' t ρ v h])

theorem FrameR.commitQueries (phase : Phase) (i : C.Party) (own : Parts C) : FrameR prims (commitQueries phase i own) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)) _

theorem FrameR.openQueries (phase : Phase) (i : C.Party) (revealed : Mail C E) :
    FrameR prims (openQueries phase i revealed) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)) _

theorem FrameR.sharedQueries (phase : Phase) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : FrameR prims (sharedQueries phase i keys) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)) _

theorem FrameR.deriveKeys (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    FrameR prims (deriveKeys phase i view) := by
  unfold ThresholdLeanXmss.deriveKeys
  have hq : ∀ (k : KeyKind) (l : List HashOutput), FrameR prims (ThresholdLeanXmss.hashQuery (C := C) (.derive phase k l)) :=
    fun _ _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
  have hrest : ∀ parameter : HashOutput, FrameR prims (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else Pure.pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then Pure.pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      Pure.pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun (j : C.Party) => pair.getD j.val 0)) := fun parameter =>
    (FrameR.mapM _ (fun T => by split_ifs; exacts [hq _ _, FrameR.pure _]) _).bind fun _ =>
      (FrameR.mapM _ (fun j => by split_ifs; exacts [FrameR.pure _, hq _ _]) _).bind fun _ => FrameR.pure _
  split_ifs
  · exact (hq _ _).bind hrest
  · exact (FrameR.pure _).bind hrest

/-- The PRSS keys of operator `i` from the keys `kT` of the terms and `kP` of the pairs. -/
def prssKeysOf (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party) : PrssKeys C :=
  ⟨fun T => if i ∈ C.holders T then kT T else 0, fun j => if hj : j = i then 0 else kP (C.pairOf i j (Ne.symm hj))⟩

/-- An honest PRSS setup. Every operator continues with its PRSS keys of one dealing. -/
theorem setup_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (f : C.Party → PrssKeys C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (s' : HashCache C), NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => f i (prssKeysOf kT kP i)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => prssSetup i >>= f i) >>= honestRounds F reply (fuel + 3))).run' s}[event z] ≤ ε := by
  simp only [prssSetup_eq, bind_assoc, commitRevealEcho_eq]
  refine sample_step prims F reply _ sampleParts _ event s ε fun parts => ?_
  refine draw_step2 prims F reply _ (fun i => commitQueries .prss i (parts i)) (fun i => FrameR.commitQueries prims _ _ _)
    _ event s hn ε fun cs s₁ hcs hn₁ hle₁ hfr₁ => ?_
  rw [show fuel + 3 = (fuel + 2) + 1 from rfl, honestRounds_exchange F reply (fuel + 2) (fun i => commitOutbox i (cs i)) _
    fun k j => isAbort_commitOutbox k _ j]
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl, honestRounds_exchange F reply (fuel + 1)
    (fun i => revealOutbox .prss i (parts i)) _ fun k j => isAbort_revealOutbox _ k _ j]
  refine draw_step2 prims F reply _ (fun i => openQueries .prss i (honestReveals (E := E) .prss parts i))
    (fun i => FrameR.openQueries prims _ _ _) _ event s₁ hn₁ ε fun os s₂ hos hn₂ hle₂ hfr₂ => ?_
  obtain ⟨h₂, hg₂, ha₂⟩ : ∃ h₂, Good prims h₂ ∧ Agrees h₂ s₂ := ⟨hashOf prims s₂, good_hashOf prims s₂,
    agrees_hashOf prims hn₂⟩
  have hcs' : cs = fun i => D prims h₂ (commitQueries .prss i (parts i)) := funext (hcs h₂ s₂ hg₂ hle₂ ha₂)
  have hos' : os = fun i => D prims h₂ (openQueries .prss i (honestReveals (E := E) .prss parts i)) :=
    funext (hos h₂ s₂ hg₂ le_rfl ha₂)
  have hopen : ∀ i, openCheck .prss i (parts i) (fun k => commitOutbox (E := E) k (cs k) i)
      (fun k => revealOutbox .prss k (parts k) i) (os i) := fun i => by
    rw [hcs', hos']; exact openCheck_honest prims h₂ .prss parts i
  simp only [require_bind_of (hopen _), pure_bind]
  refine draw_step2 prims F reply _ (fun i => deriveKeys .prss i (setupView .prss i (parts i)
    (fun k => revealOutbox (E := E) .prss k (parts k) i))) (fun i => FrameR.deriveKeys prims _ _ _) _ event s₂ hn₂ ε
    fun ks s₃ hks hn₃ hle₃ hfr₃ => ?_
  refine draw_step2 prims F reply _ (fun i => sharedQueries .prss i (ks i)) (fun i => FrameR.sharedQueries prims _ _ _)
    _ event s₃ hn₃ ε fun sh s₄ hsh hn₄ hle₄ hfr₄ => ?_
  rw [honestRounds_exchange F reply fuel (fun i => echoOutbox (E := E) .prss i (ks i) (sh i)) _
    fun k j => isAbort_echoOutbox _ k _ _ j]
  obtain ⟨h₄, hg₄, ha₄⟩ : ∃ h₄, Good prims h₄ ∧ Agrees h₄ s₄ := ⟨hashOf prims s₄, good_hashOf prims s₄,
    agrees_hashOf prims hn₄⟩
  have hks' : ks = fun i => D prims h₄ (deriveKeys .prss i (honestView (E := E) .prss parts i)) :=
    funext (hks h₄ s₄ hg₄ hle₄ ha₄)
  have hsh' : sh = fun i => D prims h₄ (sharedQueries .prss i (ks i)) := funext (hsh h₄ s₄ hg₄ le_rfl ha₄)
  have hecho : ∀ i, echoCheck .prss i (ks i) (sh i) (fun k => echoOutbox (E := E) .prss k (ks k) (sh k) i) := fun i => by
    rw [hsh', hks']; exact echoCheck_honest prims h₄ .prss parts i
  simp only [require_bind_of (hecho _)]
  have hkeys : ∀ i, (⟨(ks i).2.1, (ks i).2.2⟩ : PrssKeys C) =
      prssKeysOf (fun T => h₄ (termInput .prss parts T)) (fun p => h₄ (pairInput .prss parts p)) i := fun i => by
    rw [hks']; simp only [D_deriveKeys_honest]; rfl
  simp only [hkeys]
  exact h _ _ s₄ hn₄ (hle₁.trans (hle₂.trans (hle₃.trans hle₄))) fun q hq =>
    (hfr₄ q hq).trans ((hfr₃ q hq).trans ((hfr₂ q hq).trans (hfr₁ q hq)))

end SetupStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section CeremonyPieces

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after one computation of `H` that every operator runs. Each operator
continues with the common value. -/
theorem common_step [Nonempty C.Party] {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : OracleComp (RoSpec C) β) (hframe : FrameR prims oa)
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (v : β) (s' : HashCache C), (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' → v = D prims h' oa) →
      NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i v) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)).run' s}[event z] ≤ ε := by
  refine draw_step2 prims F reply fuel (fun _ => oa) (fun _ => hframe) g event s hn ε fun w s' hw hn' hle hfr => ?_
  obtain ⟨h', hg', ha'⟩ : ∃ h', Good prims h' ∧ Agrees h' s' := ⟨hashOf prims s', good_hashOf prims s',
    agrees_hashOf prims hn'⟩
  have hcst : w = fun _ => D prims h' oa := funext (hw h' s' hg' le_rfl ha')
  rw [hcst]
  exact h _ s' (fun h'' s'' hg hle ha => by
    have := hw h'' s'' hg hle ha (Classical.arbitrary _); rw [hcst] at this; exact this) hn' hle hfr

theorem chunks_flatten_aux {β : Type} (size : ℕ) (l : List β) :
    ∀ m, ((List.range m).map fun k => (l.drop (size * k)).take size).flatten = l.take (size * m)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, chunks_flatten_aux size l m]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [show size * (m + 1) = size * m + size by ring, List.take_add]

theorem chunks_flatten {β : Type} (size : ℕ) (hsize : 0 < size) (l : List β) : (chunks size l).flatten = l := by
  unfold chunks
  rw [chunks_flatten_aux]
  refine List.take_of_length_le ?_
  have := Nat.div_add_mod (l.length + size - 1) size
  have := Nat.mod_lt (l.length + size - 1) hsize
  nlinarith [Nat.sub_add_cancel (show 1 ≤ l.length + size by omega)]

theorem foldlM_some_append {β : Type} : ∀ (L : List (List β)) (acc : List β),
    (L.map some).foldlM (fun acc batch => batch.map (acc ++ ·)) acc = some (acc ++ L.flatten)
  | [], acc => by simp
  | b :: L, acc => by
    simp only [List.map_cons, List.foldlM_cons, Option.map_some, Option.bind_eq_bind]
    show List.foldlM _ (acc ++ b) (List.map some L) = _
    rw [foldlM_some_append L (acc ++ b), List.flatten_cons, List.append_assoc]

end CeremonyPieces

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section CeremonyMap

theorem id_mapM {β γ : Type} (f : β → Id γ) : ∀ l : List β, (l.mapM f : Id (List γ)) = l.map f
  | [] => rfl
  | b :: l => by rw [List.mapM_cons, id_mapM f l]; rfl

theorem id_bind_eq {β γ : Type} (x : Id β) (f : β → Id γ) : x >>= f = f x := rfl

theorem id_pure_eq {β : Type} (b : β) : (pure b : Id β) = b := rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m] (φ : ∀ {β : Type}, m β → β)
  (hpure : ∀ {β : Type} (b : β), φ (pure b : m β) = b)
  (hbind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ (f (φ x)))

include hpure hbind in
theorem map_mapM {β γ : Type} (f : β → m γ) : ∀ l : List β, φ (l.mapM f) = l.map fun b => φ (f b)
  | [] => by simp [hpure]
  | b :: l => by rw [List.mapM_cons, hbind, hbind, map_mapM f l, hpure]; rfl

include hpure hbind in
theorem map_batched (size : ℕ) (run : List Job → m (Option (List (List Bit)))) (jobs : List Job) :
    φ (batched size run jobs) = batched (m := Id) size (fun js => φ (run js)) jobs := by
  unfold batched
  rw [hbind, hpure, map_mapM φ hpure hbind]
  rw [id_mapM]; rfl

include hpure hbind in
theorem map_map' {β γ : Type} (f : β → γ) (x : m β) : φ (f <$> x) = f (φ x) := by
  rw [map_eq_bind_pure_comp, hbind, Function.comp, hpure]

include hpure hbind in
/-- A monad map to `Id` that keeps `pure` and `bind` commutes with `ceremonyOutput`. -/
theorem map_ceremonyOutput (lift : ∀ {β : Type}, OracleComp HashSpec β → m β) (parameter : PublicParameter)
    (run : List Job → m (Option (List (List Bit)))) (top : TopTree) (tree : Tree) :
    φ (ceremonyOutput lift parameter run top tree) =
      ceremonyOutput (m := Id) (fun oa => φ (lift oa)) parameter (fun js => φ (run js)) top tree := by
  have hmap : ∀ {β γ : Type} (f : β → γ) (x : m β), φ (f <$> x) = f (φ x) := fun f x => map_map' φ hpure hbind f x
  have hrun : ∀ js, (φ (β := Id (Option (List (List Bit)))) (run js)) = (φ (β := Option (List (List Bit))) (run js)) :=
    fun _ => rfl
  have hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), (φ (β := Id β) (lift oa)) = (φ (β := β) (lift oa)) :=
    fun _ => rfl
  cases tree with
  | top =>
    simp only [ceremonyOutput, hbind, id_bind_eq, hrun, hlift]
    cases hr : φ (run topJobs) with
    | none => simp only [hpure]; rfl
    | some outputs => simp only [hbind, hpure, id_pure_eq]
  | bottom b =>
    simp only [ceremonyOutput, hbind, id_bind_eq, hrun, hlift]
    cases hr : φ (run (bottomJobs b)) with
    | none => simp only [hpure]; rfl
    | some outputs =>
      simp only [hbind, id_pure_eq]
      split
      · rename_i randomness encoding heq
        simp only [hbind]
        cases hv : φ (run (signJobs b encoding)) with
        | none => simp only [hpure]
        | some values =>
          simp only [hbind]
          split <;> simp only [hpure]
      · rename_i heq
        simp only [hpure]

end CeremonyMap

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Dealer

variable {C : Committee} (prims : Primitives) (circuits : Circuits) (settings : Settings)

theorem batched_id (size : ℕ) (hsize : 0 < size) (f : Job → List Bit) (jobs : List Job) :
    batched (m := Id) size (fun js => some (js.map f)) jobs = some (jobs.map f) := by
  unfold batched
  rw [id_bind_eq, id_mapM]
  have := foldlM_some_append ((chunks size jobs).map fun js => js.map f) []
  simp only [List.map_map, Function.comp_def] at this
  rw [id_pure_eq]
  refine this.trans ?_
  rw [List.nil_append, ← List.map_flatten, chunks_flatten size hsize]

/-- The outputs of a run in the clear with `H` fixed to `h`. -/
@[irreducible] def evalRun (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (jobs : List Job) : Option (List (List Bit)) :=
  some (jobs.map fun job => D prims h (evalJob circuits parameter seeds job))

theorem evalRun_eq (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (jobs : List Job) :
    evalRun prims circuits parameter seeds h jobs = some (jobs.map fun job => D prims h (evalJob circuits parameter seeds job)) := by
  unfold evalRun; rfl

/-- A tree with `H` fixed to `h`, computed in the clear. -/
def ceremonyAt (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (tree : Tree) : Option TreeOutput :=
  ceremonyOutput (m := Id) (fun oa => D prims h (tweakable oa)) parameter (evalRun prims circuits parameter seeds h) top tree

theorem D_dealerCeremony (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (tree : Tree) (hsize : 0 < settings.batchSize) :
    (D prims h (dealerCeremony circuits settings parameter seeds top tree)).1 =
      ceremonyAt prims circuits parameter seeds h top tree := by
  let φ : ∀ {β : Type}, WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β → β :=
    fun x => (D prims h x.run).1
  have hpure : ∀ {β : Type} (b : β), φ (pure b) = b := fun b => rfl
  have hbind : ∀ {β γ : Type} (x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β)
      (f : β → WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) γ), φ (x >>= f) = φ (f (φ x)) := by
    intro β γ x f
    simp only [φ, WriterT.run_bind, D_bind, D_map]
  unfold dealerCeremony ceremonyAt
  rw [show ∀ x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) (Option TreeOutput),
    (D prims h x.run).1 = φ x from fun _ => rfl, map_ceremonyOutput φ hpure hbind]
  congr 1
  · funext β oa
    simp only [φ, WriterT.run_liftM, D_map]
  funext js
  refine (map_batched φ hpure hbind _ _ _).trans ?_
  rw [evalRun_eq, ← batched_id settings.batchSize hsize (fun job => D prims h (evalJob circuits parameter seeds job))]
  congr 1
  funext js'
  have hl : ∀ {β : Type} (x : OracleComp (RoSpec C) β),
      φ (liftM x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β) = D prims h x := fun x => by
    simp only [φ, WriterT.run_liftM, D_map]
  show φ _ = _
  erw [hbind, hbind, hpure, hl, D_mapM]

theorem ceremonyOutput_closed {m : Type → Type} [Monad m] (P : ∀ {β : Type}, m β → Prop)
    (hpure : ∀ {β : Type} (b : β), P (pure b : m β))
    (hbind : ∀ {β γ : Type} (x : m β) (f : β → m γ), P x → (∀ b, P (f b)) → P (x >>= f))
    (lift : ∀ {β : Type}, OracleComp HashSpec β → m β) (hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), P (lift oa))
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit)))) (hrun : ∀ js, P (run js))
    (top : TopTree) (tree : Tree) : P (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    refine hbind _ _ (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · exact hbind _ _ (hlift _) fun _ => hpure _
  | bottom b =>
    refine hbind _ _ (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · refine hbind _ _ (hlift _) fun root => hbind _ _ (hlift _) fun base => hbind _ _ (hlift _) fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · exact hpure _
      · refine hbind _ _ (hrun _) fun o' => ?_
        rcases o' with _ | values
        · exact hpure _
        · refine hbind _ _ (hlift _) fun path => hbind _ _ (hlift _) fun topRoot => ?_
          split <;> exact hpure _

theorem FrameR.evalJob (parameter : PublicParameter) (seeds : C.Term → HashOutput) (job : Job) :
    FrameR prims (evalJob circuits parameter seeds job) := by
  unfold ThresholdLeanXmss.evalJob prfValue prf
  refine (FrameR.mapM _ (fun x => (FrameR.mapM _ (fun T => ?_) _).bind fun _ => FrameR.pure _) _).bind
    fun _ => FrameR.pure _
  exact (FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)).map _

theorem FrameR.dealerCeremony (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (tree : Tree) : FrameR prims (dealerCeremony circuits settings parameter seeds top tree) := by
  unfold ThresholdLeanXmss.dealerCeremony
  refine ceremonyOutput_closed (fun {β} (x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β) => FrameR prims x.run) (fun b => FrameR.pure _)
    (fun x f hx hf => ?_) _ (fun oa => ?_) _ _ (fun js => ?_) top tree
  · show FrameR prims ((x >>= f).run)
    rw [WriterT.run_bind]
    exact hx.bind fun p => (hf p.1).map _
  · show FrameR prims (WriterT.run (liftM (ThresholdLeanXmss.tweakable oa)))
    rw [WriterT.run_liftM]
    exact (FrameR.tweakable oa).map _
  · have hW : ∀ {β γ : Type} (f : β → WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) γ),
        (∀ b, FrameR prims (f b).run) → ∀ l : List β, FrameR prims (l.mapM f).run := by
      intro β γ f hf l
      induction l with
      | nil => exact FrameR.pure _
      | cons b l ih =>
        rw [List.mapM_cons, WriterT.run_bind]
        refine (hf b).bind fun p => FrameR.map _ ?_
        rw [WriterT.run_bind]
        exact ih.bind fun q => FrameR.map _ (FrameR.pure _)
    show FrameR prims (WriterT.run (batched _ _ js))
    unfold batched
    rw [WriterT.run_bind]
    refine (hW _ (fun js' => ?_) _).bind fun p => FrameR.map _ (FrameR.pure _)
    rw [WriterT.run_bind]
    refine FrameR.bind ?_ fun p => FrameR.map _ ?_
    · rw [WriterT.run_liftM]
      exact (FrameR.mapM _ (fun job => FrameR.evalJob prims circuits _ _ job) _).map _
    · rw [WriterT.run_bind]
      exact FrameR.pure _ |>.bind fun _ => FrameR.map _ (FrameR.pure _)

end Dealer

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Body

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- The real ceremony of `jobs` on dealt keys, from the counters `st`. It is the PRSS setup and then
the batches of `jobs` with the new PRSS keys. -/
theorem ceremonyRun_run (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (i : C.Party) (jobs : List Job) (st : ℕ × ℕ) :
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i
        (dealtKeys parameter seeds pairKeys i) jobs : StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run st =
      prssSetup i >>= fun prss => ((chunks settings.batchSize jobs).mapM (realBatch K circuits settings.mode
        ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run st >>= fun p =>
          pure (p.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], p.2) := by
  simp only [ceremonyRun, batched, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure]
  rfl

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- An honest PRSS setup from a cache with `CacheOK`. Every operator continues with its PRSS keys of
one dealing, and the cache keeps `CacheOK` for the same keys and the same label bound. -/
theorem setup_step_cacheOK [Nonempty C.Party] {I O L R α : Type} (F : Functionality C I O L R) (reply : L → R)
    (fuel : ℕ) (f : C.Party → PrssKeys C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (Ks : Finset HashOutput) (Lk : ℕ) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (ε : ℝ≥0∞)
    (h : ∀ (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (s' : HashCache C), NoMpc s' → s ≤ s' →
      CacheOK Ks Lk s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => f i (prssKeysOf kT kP i)) >>= honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => prssSetup i >>= f i) >>= honestRounds F reply (fuel + 3))).run' s}[event z] ≤ ε :=
  setup_step prims F reply fuel f event s hn ε fun kT kP s' hn' hle hfr =>
    h kT kP s' hn' hle (cacheOK_of_frame hs hfr)

/-- The join of two ceremonies of a tree. From a cache with `CacheOK Ks Lk` and the counters
`(lab, k)` of the ceremony before, a new PRSS setup and then the batches `js` abort with probability
at most `chunksCost`, as the batches of one ceremony do, and the bound charges it with the weight
`δ`. The counters and the coin keys continue, and only the PRSS keys are new. -/
theorem setup_chunks_step [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (mode : ReshareMode) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    {α : Type} (js : List (List Job)) (lab k Lk c : ℕ) (Ks : Finset HashOutput) (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (Option (List (List Bit))) × (ℕ × ℕ) → PartyM C E RealSpec α)
    (event : (C.Party → Option α) → Prop) (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ) (ε : ℝ≥0∞)
    (h : ∀ (outs : List (Option (List (List Bit)))) (Ks' : Finset HashOutput) (s' : HashCache C),
      (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        outs = js.map fun jobs => some (jobs.map fun job => D prims h' (evalJob circuits parameter seeds job))) →
      Ks'.card ≤ c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum →
      CacheOK Ks' (lab + (js.map (batchLabels circuits parameter)).sum) s' → NoMpc s' → s ≤ s' →
      Pr{let z ← (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (outs, (lab + (js.map (batchLabels circuits parameter)).sum, k + js.length))) >>=
          honestRounds F reply fuel)).run' s'}[event z] ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => prssSetup i >>= fun prss =>
        (js.mapM (realBatch K circuits mode ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run (lab, k) >>=
          g i) >>=
        honestRounds F reply (fuel + (js.map (batchRounds circuits mode parameter)).sum + 3))).run' s}[event z] ≤
      δ * chunksCost circuits E parameter c js + ε := by
  refine setup_step_cacheOK prims F reply _ _ event Ks Lk s hn hs _ fun kT kP s₁ hn₁ hle₁ hs₁ => ?_
  exact chunks_step prims K circuits mode F reply parameter seeds pairKeys kT kP js lab k Lk c Ks hLk hKs s₁ hn₁ hs₁
    fuel g event δ hδ ε fun outs Ks' s' houts hKs' hs' hn' hle' => h outs Ks' s' houts hKs' hs' hn' (hle₁.trans hle')

end Body

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section TopBody

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The chain ends of the top tree from the outputs of its run. -/
def topChainEnd (outputs : List (List Bit)) : KeyIndex → ChainIndex → Digest := fun e l =>
  digestAt (outputs.getD (((List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange chainCount).map fun l => (topKey b, l)).idxOf (e, l)) []) 0

/-- The top tree after the batches of its ceremony. -/
def topRest (parameter : PublicParameter) (outs : List (Option (List (List Bit)))) (_st : ℕ × ℕ) :
    PartyM C E RealSpec TreeOutput :=
  match outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
  | some outputs => oracleStep (tweakable (merkleNode parameter topLayer (topChainEnd outputs) layerHeight 0)) >>=
      fun root => pure (.top ⟨topChainEnd outputs, root⟩)
  | none => failure

omit [Fintype E] [DecidableEq E] in
/-- The ceremony of the top tree is its PRSS setup, its batches and the local root. -/
theorem newTree_top (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) (i : C.Party) :
    (newTree K circuits settings i (dealtKeys parameter seeds pairKeys i) top .top : PartyM C E RealSpec TreeOutput) =
      prssSetup i >>= fun prss => ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
        ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run (0, 0) >>= fun p =>
          topRest parameter p.1 p.2 := by
  unfold newTree
  simp only [ceremonyOutput]
  rw [StateT.run'_eq, StateT.run_bind]
  simp only [ceremonyRun_run, bind_assoc, pure_bind, map_bind]
  refine bind_congr fun prss => bind_congr fun p => ?_
  unfold topRest
  split
  · rename_i outputs heq
    rw [heq]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure, map_pure, map_bind]
    rfl
  · rename_i hne
    simp only [StateT.run_pure, map_pure, pure_bind]
    split
    · rename_i o h
      exact absurd h (hne o)
    · rfl

theorem flatten_chunks_map {β γ : Type} (size : ℕ) (hsize : 0 < size) (f : β → γ) (l : List β) :
    ((chunks size l).map fun js => js.map f).flatten = l.map f := by
  rw [← List.map_flatten, chunks_flatten size hsize]

theorem ceremonyAt_top (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) :
    ceremonyAt prims circuits parameter seeds h top .top =
      some (.top ⟨topChainEnd (topJobs.map fun job => D prims h (evalJob circuits parameter seeds job)),
        D prims h (tweakable (merkleNode parameter topLayer
          (topChainEnd (topJobs.map fun job => D prims h (evalJob circuits parameter seeds job))) layerHeight 0))⟩) := by
  unfold ceremonyAt
  rw [ceremonyOutput, evalRun_eq]
  rfl

theorem top_body_bound [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top .top)
    (event : (C.Party → Option TreeOutput) → Prop) (hev : ¬ event fun _ => o₀)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (hsize : 0 < settings.batchSize) (fuel : ℕ) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          topRest (E := E) parameter p.1 p.2) >>=
        honestRounds F reply (fuel + ((chunks settings.batchSize topJobs).map
          (batchRounds circuits settings.mode parameter)).sum))).run' s}[event z] ≤
      δ * chunksCost circuits E parameter 0 (chunks settings.batchSize topJobs) := by
  rw [← add_zero (δ * chunksCost circuits E parameter 0 _)]
  refine chunks_step prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _ 0 0 0 0 ∅ le_rfl (by simp)
    s hn hs fuel (fun i p => topRest parameter p.1 p.2) _ δ hδ 0 fun outs Ks' s' houts hKs' hs' hn' hle' => ?_
  dsimp only
  obtain ⟨h₀, hg₀, ha₀⟩ : ∃ h₀, Good prims h₀ ∧ Agrees h₀ s' := ⟨hashOf prims s', good_hashOf prims s',
    agrees_hashOf prims hn'⟩
  set W := topJobs.map fun job => D prims h₀ (evalJob circuits parameter seeds job) with hW
  have hfold : outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some W := by
    rw [houts h₀ s' hg₀ le_rfl ha₀]
    have := foldlM_some_append ((chunks settings.batchSize topJobs).map fun js =>
      js.map fun job => D prims h₀ (evalJob circuits parameter seeds job)) []
    simp only [List.map_map, Function.comp_def] at this
    rw [this, List.nil_append, flatten_chunks_map _ hsize]
  simp only [topRest, hfold]
  refine common_step prims F reply fuel _ (FrameR.tweakable _) _ _ s' hn' 0 fun v s'' hv hn'' hle'' _ => ?_
  rw [honestRounds_pure]
  obtain ⟨h₁, hg₁, ha₁⟩ : ∃ h₁, Good prims h₁ ∧ Agrees h₁ s'' := ⟨hashOf prims s'', good_hashOf prims s'',
    agrees_hashOf prims hn''⟩
  have hW₁ : W = topJobs.map fun job => D prims h₁ (evalJob circuits parameter seeds job) := by
    have e₀ := houts h₀ s' hg₀ le_rfl ha₀
    have e₁ := houts h₁ s'' hg₁ hle'' ha₁
    rw [e₀] at e₁
    have := congrArg (fun L => (L.map fun o => o.getD []).flatten) e₁
    simp only [List.map_map, Function.comp_def, Option.getD_some, flatten_chunks_map _ hsize] at this
    exact this
  have ho₁ := ho h₁ s'' hg₁ (hle'.trans hle'') ha₁
  rw [ceremonyAt_top prims circuits parameter seeds h₁ top, ← hW₁, ← hv h₁ s'' hg₁ le_rfl ha₁] at ho₁
  rw [ho₁] at hev
  simp [hev]

end TopBody

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Cost

variable {C : Committee} {E : Type} [Fintype E] (circuits : Circuits)

/-- The terms of the checks of one batch, other than its coin keys. -/
def freshCost (E : Type) [Fintype E] (R : ℕ) : ℝ≥0∞ :=
  (sliceBits : ℝ≥0∞) / Fintype.card E + ((R + 1 : ℕ) : ℝ≥0∞) * (2 / Fintype.card E) ^ challengeTries

theorem two_mul_sum_range_add (c k : ℕ) : 2 * ∑ j ∈ range k, (c + j) ≤ (c + k) ^ 2 - c ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h1 : (c + k) ^ 2 ≤ (c + (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : c ^ 2 ≤ (c + k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : (c + (k + 1)) ^ 2 = (c + k) ^ 2 + 2 * (c + k) + 1 := by ring
    omega

theorem chalErr_eq (c r : ℕ) : chalErr E c r = (∑ j ∈ range r, ((c + j : ℕ) : ℝ≥0∞)) / 2 ^ 256 +
    (r : ℝ≥0∞) * (2 / Fintype.card E) ^ challengeTries := by
  unfold chalErr
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem checkCost_le (c cnt R : ℕ) (hR : halvings cnt ≤ R) :
    checkCost E c cnt c ≤ (((c + checkKeys cnt) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 + freshCost E R := by
  unfold checkCost checkKeys freshCost
  split_ifs with h0
  · simp
  · set k := halvings cnt
    rw [chalErr_eq]
    have hsum : ((c : ℝ≥0∞) / 2 ^ 256 + (∑ j ∈ range (k + 1), ((c + 1 + j : ℕ) : ℝ≥0∞)) / 2 ^ 256) =
        ((∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
      rw [ENNReal.div_add_div_same, Finset.sum_range_succ' (fun j => c + j) (k + 1)]
      push_cast
      rw [add_comm]
      congr 1
      simp only [add_zero]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hle : ((∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
        (((c + (k + 2)) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
      have e : ((∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 256 =
          ((2 * ∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
        rw [show (2 : ℝ≥0∞) ^ 257 = 2 * 2 ^ 256 by rw [← pow_succ'], Nat.cast_mul, Nat.cast_ofNat,
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
      rw [e]
      gcongr
      exact two_mul_sum_range_add c (k + 2)
    have hf : ((k + 1 : ℕ) : ℝ≥0∞) ≤ ((R + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : k + 1 ≤ R + 1)
    calc (c : ℝ≥0∞) / 2 ^ 256 + ↑sliceBits / ↑(Fintype.card E) +
          ((∑ j ∈ range (k + 1), ((c + 1 + j : ℕ) : ℝ≥0∞)) / 2 ^ 256 + ((k + 1 : ℕ) : ℝ≥0∞) * (2 / ↑(Fintype.card E)) ^ challengeTries)
        = ((c : ℝ≥0∞) / 2 ^ 256 + (∑ j ∈ range (k + 1), ((c + 1 + j : ℕ) : ℝ≥0∞)) / 2 ^ 256) +
            (↑sliceBits / ↑(Fintype.card E) + ((k + 1 : ℕ) : ℝ≥0∞) * (2 / ↑(Fintype.card E)) ^ challengeTries) := by ring
      _ ≤ _ := by
        rw [hsum]
        gcongr

theorem chunksCost_le (parameter : PublicParameter) (R : ℕ) : ∀ (js : List (List Job)) (c : ℕ),
    (∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) →
    chunksCost circuits E parameter c js ≤
      (((c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 +
        js.length * freshCost E R
  | [], c, _ => by simp [chunksCost]
  | jobs :: js, c, hR => by
    rw [chunksCost]
    have h1 := checkCost_le (E := E) c (batchCount circuits parameter jobs) R (hR jobs (List.mem_cons_self ..))
    have h2 := chunksCost_le parameter R js (c + checkKeys (batchCount circuits parameter jobs))
      fun j hj => hR j (List.mem_cons_of_mem _ hj)
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    set k := checkKeys (batchCount circuits parameter jobs)
    set K := (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum
    have hsq : (c + k) ^ 2 - c ^ 2 + ((c + k + K) ^ 2 - (c + k) ^ 2) = (c + (k + K)) ^ 2 - c ^ 2 := by
      have h₁ : c ^ 2 ≤ (c + k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h₂ : (c + k) ^ 2 ≤ (c + k + K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [show c + (k + K) = c + k + K by ring]
      omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [← hsq, Nat.cast_add, ← ENNReal.div_add_div_same]
    push_cast
    ring

end Cost

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

section BottomBody

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

def bCpk (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : KeyIndex → ChainIndex → Digest × Digest × Digest :=
  fun e l => let bits := outputs.getD ((bottomKeys b).idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)

def bCommitment (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : KeyIndex → Digest :=
  fun e => digestAt (outputs.getD ((bottomKeys b).length + e.val % 2 ^ layerHeight) []) 0

def bRho (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : Digest :=
  digestAt (outputs.getD ((bottomKeys b).length + 2 ^ layerHeight) []) 0

/-- A bottom tree after the batches of its signature ceremony. -/
def bottomRest2 (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (root : Digest) (randomness : Randomizer) (outs : List (Option (List (List Bit)))) :
    PartyM C E RealSpec TreeOutput :=
  match outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
  | some values => oracleStep (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) >>= fun path =>
      oracleStep (tweakable (Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 root)
        ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) >>= fun topRoot =>
      if topRoot ≠ some top.root then failure else
      pure (.bottom ⟨bCpk b outputs, bCommitment b outputs, root, ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩)
  | none => failure

/-- A bottom tree after its first ceremony. `signRun` is the signature ceremony at an encoding, from
the counters that the first ceremony leaves. -/
def bottomRest (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (signRun : Encoding → ℕ × ℕ → PartyM C E RealSpec (List (Option (List (List Bit))) × (ℕ × ℕ)))
    (outs : List (Option (List (List Bit)))) (st : ℕ × ℕ) : PartyM C E RealSpec TreeOutput :=
  match outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
  | some outputs =>
      oracleStep (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)) >>=
        fun root => oracleStep (tweakable (truncateHash <$> Verification.oracleHashWithHash (randomizerInput parameter topLayer
          (topKey b) (bRho b outputs) (littleEndianBytes 16 root)))) >>= fun base =>
        oracleStep (tweakable (grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base randomizerAttemptLimit 0)) >>=
        fun g => match g with
          | some (randomness, encoding) => signRun encoding st >>= fun p =>
              bottomRest2 parameter top b outputs root randomness p.1
          | none => failure
  | none => failure

/-- The signature ceremony of bottom tree `b` at operator `i` on dealt keys, namely its own PRSS setup
and then its batches from the counters `st`. -/
def signRun (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (b : Fin (2 ^ layerHeight)) (i : C.Party) (encoding : Encoding) (st : ℕ × ℕ) :
    PartyM C E RealSpec (List (Option (List (List Bit))) × (ℕ × ℕ)) :=
  prssSetup i >>= fun prss => ((chunks settings.batchSize (signJobs b encoding)).mapM (realBatch K circuits settings.mode
    ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run st

omit [Fintype E] [DecidableEq E] in
/-- The ceremonies of a bottom tree are the PRSS setup and the batches of the first ceremony, the
local steps, and then the signature ceremony with its own PRSS setup. -/
theorem newTree_bottom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (i : C.Party) :
    (newTree K circuits settings i (dealtKeys parameter seeds pairKeys i) top (.bottom b) : PartyM C E RealSpec TreeOutput) =
      prssSetup i >>= fun prss => ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
        ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run (0, 0) >>= fun p =>
          bottomRest parameter top b (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2 := by
  unfold newTree
  simp only [ceremonyOutput]
  rw [StateT.run'_eq, StateT.run_bind]
  simp only [ceremonyRun_run, bind_assoc, pure_bind, map_bind]
  refine bind_congr fun prss => bind_congr fun p => ?_
  unfold bottomRest
  split
  · rename_i outputs heq
    rw [heq]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind, bCpk, bRho, bottomKeys]
    refine bind_congr fun root => ?_
    refine bind_congr fun base => ?_
    refine bind_congr fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · simp only [StateT.run_pure, map_pure, pure_bind]
    · simp only [StateT.run_bind, bind_assoc, map_bind, ceremonyRun_run, signRun, pure_bind]
      refine bind_congr fun prss' => bind_congr fun q => ?_
      unfold bottomRest2
      split
      · rename_i values heq'
        rw [heq']
        simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun path => ?_
        refine bind_congr fun topRoot => ?_
        split_ifs <;> simp only [StateT.run_pure, map_pure, pure_bind]; rfl
      · rename_i hne'
        simp only [StateT.run_pure, map_pure, pure_bind]
        split
        · rename_i o h
          exact absurd h (hne' o)
        · rfl
  · rename_i hne
    simp only [StateT.run_pure, map_pure, pure_bind]
    split
    · rename_i o h
      exact absurd h (hne o)
    · rfl

/-- The ceremonies of a tree at operator `i` after its first PRSS setup with the keys `prss`. -/
def treeRest (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) : Tree → C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput
  | .top, i, prss => ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
      ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run (0, 0) >>= fun p => topRest parameter p.1 p.2
  | .bottom b, i, prss => ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
      ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩ parameter)).run (0, 0) >>= fun p =>
        bottomRest parameter top b (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2

omit [Fintype E] [DecidableEq E] in
/-- The ceremonies of a tree on dealt keys start with one PRSS setup. -/
theorem newTree_eq (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) (tree : Tree) (i : C.Party) :
    (newTree K circuits settings i (dealtKeys parameter seeds pairKeys i) top tree : PartyM C E RealSpec TreeOutput) =
      prssSetup i >>= treeRest K circuits settings parameter seeds pairKeys top tree i := by
  cases tree with
  | top => exact newTree_top K circuits settings parameter seeds pairKeys top i
  | bottom b => exact newTree_bottom K circuits settings parameter seeds pairKeys top b i

end BottomBody

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
variable {C : Committee} (prims : Primitives) (circuits : Circuits)

def bottomAt (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : Id (Option TreeOutput) := do
  let root ← (D prims h (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)) : Id Digest)
  let base ← (D prims h (tweakable (truncateHash <$> Verification.oracleHashWithHash (randomizerInput parameter topLayer
    (topKey b) (bRho b outputs) (littleEndianBytes 16 root)))) : Id Randomizer)
  let some (randomness, encoding) ← (D prims h (tweakable (grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base randomizerAttemptLimit 0)) : Id _) | pure none
  let some values ← (evalRun prims circuits parameter seeds h (signJobs b encoding) : Id _) | pure none
  let path ← (D prims h (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) : Id _)
  let topRoot ← (D prims h (tweakable (Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 root)
    ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) : Id _)
  if topRoot ≠ some top.root then pure none else
    pure (some (.bottom ⟨bCpk b outputs, bCommitment b outputs, root,
      ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩))

theorem ceremonyAt_bottom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    ceremonyAt prims circuits parameter seeds h top (.bottom b) =
      bottomAt prims circuits parameter seeds h top b
        ((bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job)) := by
  unfold ceremonyAt
  rw [ceremonyOutput, evalRun_eq]
  rfl
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
attribute [local irreducible] D
variable {C : Committee} {E : Type} (prims : Primitives) (circuits : Circuits)

theorem chunks_outputs {β : Type} (size : ℕ) (hsize : 0 < size) (jobs : List Job) (f : Job → β) :
    ((chunks size jobs).map fun js => some (js.map f)).foldlM (fun acc batch => batch.map (acc ++ ·)) [] =
      some (jobs.map f) := by
  have := foldlM_some_append ((chunks size jobs).map fun js => js.map f) []
  simp only [List.map_map, Function.comp_def] at this
  rw [this, List.nil_append, flatten_chunks_map _ hsize]

def bottomResult (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (g : Option (Randomizer × Encoding)) : Id (Option TreeOutput) := do
  let some (randomness, encoding) ← (g : Id _) | pure none
  let some values ← (evalRun prims circuits parameter seeds h (signJobs b encoding) : Id _) | pure none
  let path ← (D prims h (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) : Id _)
  let topRoot ← (D prims h (tweakable (Verification.layerRootWithHash parameter topLayer (topKey b) (littleEndianBytes 16 root)
    ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) : Id _)
  if topRoot ≠ some top.root then pure none else
    pure (some (.bottom ⟨bCpk b outputs, bCommitment b outputs, root,
      ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩))

theorem ceremonyAt_bottom_values (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest) (base : Randomizer)
    (g : Option (Randomizer × Encoding))
    (hw : outputs = (bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job))
    (hr : root = D prims h (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)))
    (hb : base = D prims h (tweakable (truncateHash <$> Verification.oracleHashWithHash (randomizerInput parameter topLayer
      (topKey b) (bRho b outputs) (littleEndianBytes 16 root)))))
    (hg : g = D prims h (tweakable (grind parameter topLayer (topKey b) (littleEndianBytes 16 root) base randomizerAttemptLimit 0))) :
    ceremonyAt prims circuits parameter seeds h top (.bottom b) =
      bottomResult prims circuits parameter seeds h top b outputs root g := by
  rw [ceremonyAt_bottom, ← hw]
  subst root base g
  rfl

variable [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (settings : Settings)

theorem bottom_body_bound [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top (.bottom b))
    (event : (C.Party → Option TreeOutput) → Prop) (hev : ¬ event fun _ => o₀)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (hsize : 0 < settings.batchSize) (fuel Y : ℕ) (ε : ℝ≥0∞)
    (hY : ∀ enc, ((chunks settings.batchSize (signJobs b enc)).map (batchRounds circuits settings.mode parameter)).sum ≤ Y)
    (hε : ∀ enc, chunksCost circuits E parameter
      (((chunks settings.batchSize (bottomJobs b)).map fun js => checkKeys (batchCount circuits parameter js)).sum)
      (chunks settings.batchSize (signJobs b enc)) ≤ ε) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          bottomRest parameter top b (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2) >>=
        honestRounds F reply (fuel + Y + 3 + ((chunks settings.batchSize (bottomJobs b)).map
          (batchRounds circuits settings.mode parameter)).sum))).run' s}[event z] ≤
      δ * (chunksCost circuits E parameter 0 (chunks settings.batchSize (bottomJobs b)) + ε) := by
  rw [mul_add]
  refine chunks_step prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _ 0 0 0 0 ∅ le_rfl (by simp)
    s hn hs (fuel + Y + 3) (fun i p => bottomRest parameter top b
      (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2)
      _ δ hδ (δ * ε) fun outs Ks₁ s₁ houts hKs₁ hs₁ hn₁ hle₁ => ?_
  dsimp only
  let h₁ := hashOf prims s₁
  have hg₁ := good_hashOf prims s₁
  have ha₁ := agrees_hashOf prims hn₁
  set W := (bottomJobs b).map fun job => D prims h₁ (evalJob circuits parameter seeds job) with hW
  have hfold : outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some W := by
    rw [houts h₁ s₁ hg₁ le_rfl ha₁, chunks_outputs _ hsize]
  have hW' : ∀ h s', Good prims h → s₁ ≤ s' → Agrees h s' →
      W = (bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job) := by
    intro h s' hg hle ha
    have hf := hfold
    rw [houts h s' hg hle ha, chunks_outputs _ hsize] at hf
    exact (Option.some.inj hf).symm
  simp only [bottomRest, hfold]
  refine common_step prims F reply (fuel + Y + 3) _ (FrameR.tweakable _) _ _ s₁ hn₁ (δ * ε)
    fun root s₂ hr hn₂ hle₂ hfr₂ => ?_
  refine common_step prims F reply (fuel + Y + 3) _ (FrameR.tweakable _) _ _ s₂ hn₂ (δ * ε)
    fun base s₃ hb hn₃ hle₃ hfr₃ => ?_
  refine common_step prims F reply (fuel + Y + 3) _ (FrameR.tweakable _) _ _ s₃ hn₃ (δ * ε)
    fun g s₄ hg hn₄ hle₄ hfr₄ => ?_
  have ho₄ : ∀ h s', Good prims h → s₄ ≤ s' → Agrees h s' →
      o₀ = bottomResult prims circuits parameter seeds h top b W root g := by
    intro h s' hgood hle ha
    rw [ho h s' hgood (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans hle)))) ha]
    exact ceremonyAt_bottom_values prims circuits parameter seeds h top b W root base g
      (hW' h s' hgood (hle₂.trans (hle₃.trans (hle₄.trans hle))) ha)
      (hr h s' hgood (hle₃.trans (hle₄.trans hle)) ha)
      (hb h s' hgood (hle₄.trans hle) ha) (hg h s' hgood hle ha)
  rcases g with _ | ⟨randomness, encoding⟩
  · have ho' := ho₄ (hashOf prims s₄) s₄ (good_hashOf prims s₄) le_rfl (agrees_hashOf prims hn₄)
    simp only [bottomResult, id_bind_eq, id_pure_eq] at ho'
    rw [ho'] at hev
    rw [honestRounds_failure]
    simp [hev]
  · have hs₄ := cacheOK_of_frame (cacheOK_of_frame (cacheOK_of_frame hs₁ hfr₂) hfr₃) hfr₄
    have hfuel : fuel + Y + 3 = (fuel + (Y - ((chunks settings.batchSize (signJobs b encoding)).map
        (batchRounds circuits settings.mode parameter)).sum)) +
          ((chunks settings.batchSize (signJobs b encoding)).map (batchRounds circuits settings.mode parameter)).sum + 3 := by
      have := hY encoding; omega
    rw [hfuel]
    simp only [signRun, bind_assoc]
    refine le_trans (setup_chunks_step prims K circuits F reply settings.mode parameter seeds pairKeys _
      _ _ _ _ Ks₁ le_rfl hKs₁ s₄ hn₄ hs₄ _ (fun _ p => bottomRest2 parameter top b W root randomness p.1)
        _ δ hδ 0 fun vals Ks₅ s₅ hvals hKs₅ hs₅ hn₅ hle₅ => ?_) (by simpa using mul_le_mul_of_nonneg_left (hε encoding) zero_le)
    dsimp only
    let h₅ := hashOf prims s₅
    set V := (signJobs b encoding).map fun job => D prims h₅ (evalJob circuits parameter seeds job) with hV
    have hvfold : vals.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some V := by
      rw [hvals h₅ s₅ (good_hashOf prims s₅) le_rfl (agrees_hashOf prims hn₅), chunks_outputs _ hsize]
    have hV' : ∀ h s', Good prims h → s₅ ≤ s' → Agrees h s' →
        V = (signJobs b encoding).map fun job => D prims h (evalJob circuits parameter seeds job) := by
      intro h s' hg hle ha
      have hf := hvfold
      rw [hvals h s' hg hle ha, chunks_outputs _ hsize] at hf
      exact (Option.some.inj hf).symm
    simp only [bottomRest2, hvfold]
    refine common_step prims F reply _ _ (FrameR.tweakable _) _ _ s₅ hn₅ 0
      fun path s₆ hp hn₆ hle₆ _ => ?_
    refine common_step prims F reply _ _ (FrameR.tweakable _) _ _ s₆ hn₆ 0
      fun topRoot s₇ ht hn₇ hle₇ _ => ?_
    let h₇ := hashOf prims s₇
    have hgood := good_hashOf prims s₇
    have ha := agrees_hashOf prims hn₇
    have ho' := ho₄ h₇ s₇ hgood (hle₅.trans (hle₆.trans hle₇)) ha
    have hpath := hp h₇ s₇ hgood hle₇ ha
    have htop := ht h₇ s₇ hgood le_rfl ha
    have hval := hV' h₇ s₇ hgood (hle₆.trans hle₇) ha
    unfold bottomResult at ho'
    simp only [id_bind_eq, id_pure_eq] at ho'
    rw [evalRun_eq, ← hval] at ho'
    simp only [] at ho'
    erw [← hpath, ← htop] at ho'
    split_ifs with hbad
    · rw [ite_eq_left hbad] at ho'
      rw [ho'] at hev
      rw [honestRounds_failure]
      simp [hev]
    · rw [ite_eq_right hbad] at ho'
      rw [honestRounds_pure]
      simp
      convert hev using 2
      rw [ho']
      simp [List.getD_eq_getElem?_getD]
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
variable {C : Committee} (prims : Primitives) (circuits : Circuits) (settings : Settings)

theorem cacheOK_empty : CacheOK (C := C) ∅ 0 ∅ := by
  intro q hq
  exact (hq rfl).elim

theorem idealTree_value (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
    (hsize : 0 < settings.batchSize) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s) (z)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree)).run s)) :
    NoMpc z.2 ∧ CacheOK ∅ 0 z.2 ∧ ∃ o₀, z.1 = (fun _ => o₀) ∧
      ∀ h s', Good prims h → z.2 ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree := by
  obtain ⟨hle, hn₀, hsupp⟩ := localRun_support _ s z hz
  have hn' := hn₀ hn
  have hfr : FrameL prims (idealTree circuits settings parameter seeds top tree) :=
    FrameL.liftComp ((FrameR.dealerCeremony prims circuits settings parameter seeds top tree).map _)
  refine ⟨hn', cacheOK_of_frame hs (hfr s z hz), ?_⟩
  have hval : ∀ h s', Good prims h → z.2 ≤ s' → Agrees h s' →
      z.1 = fun _ => ceremonyAt prims circuits parameter seeds h top tree := by
    intro h s' hg hle' ha
    have hv := hsupp h hg (ha.mono hle')
    simp only [idealTree, simulateQ_fixedLocal_liftComp, D_map, support_pure, Set.mem_singleton_iff] at hv
    rw [D_dealerCeremony prims circuits settings parameter seeds h top tree hsize] at hv
    exact hv
  let h₀ := hashOf prims z.2
  have heq := hval h₀ z.2 (good_hashOf prims z.2) le_rfl (agrees_hashOf prims hn')
  refine ⟨ceremonyAt prims circuits parameter seeds h₀ top tree, heq, ?_⟩
  intro h s' hg hle' ha
  have e := hval h s' hg hle' ha
  rw [heq] at e
  exact congrFun e ⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
variable (circuits : Circuits) (settings : Settings)

theorem measure_le_maxBatch (measure : List Circuit → ℕ) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (enc : Encoding) (jobs : List Job)
    (hj : jobs ∈ chunks settings.batchSize topJobs ∨ jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc)) :
    measure (runCircuits circuits parameter jobs) ≤ maxBatch circuits settings measure := by
  unfold maxBatch
  refine Finset.le_sup_of_le (b := (parameter, b, enc)) (s := Finset.univ)
    (f := fun x : PublicParameter × Fin (2 ^ layerHeight) × Encoding =>
      (([topJobs, bottomJobs x.2.1, signJobs x.2.1 x.2.2].flatMap (chunks settings.batchSize)).map
        fun js => measure (runCircuits circuits x.1 js)).foldl max 0) ?_ ?_
  · apply Finset.mem_univ
  apply (le_foldl_max _ 0).2
  apply List.mem_map.mpr
  refine ⟨jobs, ?_, rfl⟩
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] using hj

theorem length_chunks {α : Type} (size : ℕ) (js : List α) :
    (chunks size js).length = (js.length + size - 1) / size := by
  simp only [chunks, List.length_map, List.length_range]

theorem length_bottomJobs (b : Fin (2 ^ layerHeight)) :
    (bottomJobs b).length = (bottomJobs (0 : Fin (2 ^ layerHeight))).length := by
  simp [bottomJobs, List.length_flatMap]

theorem length_signJobs (b b' : Fin (2 ^ layerHeight)) (enc enc' : Encoding) :
    (signJobs b enc).length = (signJobs b' enc').length := by
  simp only [signJobs, List.length_map]

theorem length_chunks_signJobs (b b' : Fin (2 ^ layerHeight)) (enc enc' : Encoding) :
    (chunks settings.batchSize (signJobs b enc)).length =
      (chunks settings.batchSize (signJobs b' enc')).length := by
  rw [length_chunks, length_chunks, length_signJobs b b' enc enc']

theorem treeBatches_le_ceremonyBatches (tree : Tree) : treeBatches settings tree ≤ ceremonyBatches settings := by
  cases tree with
  | top => exact le_max_left _ _
  | bottom b =>
    simp only [treeBatches, ceremonyBatches]
    rw [length_chunks_signJobs settings b 0 (fun _ => digit 0) (fun _ => digit 0)]
    simp only [length_chunks, length_bottomJobs]
    exact le_max_right _ _

theorem sum_map_le_length_mul {α : Type} (f : α → ℕ) (l : List α) (R : ℕ) (h : ∀ x ∈ l, f x ≤ R) :
    (l.map f).sum ≤ l.length * R := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem batchRounds_le_runRounds (mode : ReshareMode) (parameter : PublicParameter) (jobs : List Job) :
    batchRounds circuits mode parameter jobs ≤ runRounds mode (runCircuits circuits parameter jobs) := by
  unfold batchRounds batchCount checkLabels runRounds runCircuits
  split_ifs <;> omega

theorem chunks_rounds_le (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (enc : Encoding)
    (js : List (List Job))
    (hj : ∀ jobs ∈ js, jobs ∈ chunks settings.batchSize topJobs ∨ jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc)) :
    (js.map (batchRounds circuits settings.mode parameter)).sum ≤
      js.length * maxBatch circuits settings (runRounds settings.mode) :=
  sum_map_le_length_mul _ _ _ fun jobs hmem =>
    (batchRounds_le_runRounds circuits settings.mode parameter jobs).trans
      (measure_le_maxBatch circuits settings _ parameter b enc jobs (hj jobs hmem))

variable {E : Type} [Fintype E]

def chunksBudget (E : Type) [Fintype E] (R B c : ℕ) : ℝ≥0∞ :=
  (((c + B * (R + 2)) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 + B * freshCost E R

theorem checkKeys_le (cnt R : ℕ) (h : halvings cnt ≤ R) : checkKeys cnt ≤ R + 2 := by
  unfold checkKeys
  split_ifs <;> omega

theorem chunks_keys_le (parameter : PublicParameter) (R : ℕ) (js : List (List Job))
    (h : ∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) :
    (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum ≤ js.length * (R + 2) :=
  sum_map_le_length_mul _ _ _ fun jobs hj => checkKeys_le _ _ (h jobs hj)

theorem chunksCost_le_budget (parameter : PublicParameter) (R B c : ℕ) (js : List (List Job))
    (hB : js.length ≤ B) (h : ∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) :
    chunksCost circuits E parameter c js ≤ chunksBudget E R B c := by
  refine (chunksCost_le circuits parameter R js c h).trans ?_
  unfold chunksBudget
  have hkeys := (chunks_keys_le circuits parameter R js h).trans (Nat.mul_le_mul_right (R + 2) hB)
  gcongr

theorem chunksCost_prefix_budget (parameter : PublicParameter) (R B : ℕ) (js : List (List Job))
    (h : ∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) :
    chunksCost circuits E parameter 0 js +
      chunksBudget E R B ((js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum) ≤
        chunksBudget E R (js.length + B) 0 := by
  refine (add_le_add (chunksCost_le (E := E) circuits parameter R js 0 h) le_rfl).trans ?_
  set c := (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum
  have hsq : c ^ 2 ≤ (c + B * (R + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have heq : c ^ 2 + ((c + B * (R + 2)) ^ 2 - c ^ 2) = (c + B * (R + 2)) ^ 2 := by omega
  unfold chunksBudget
  simp only [zero_add, zero_pow (by omega : 2 ≠ 0), Nat.sub_zero]
  calc
    (c ^ 2 : ℕ) / (2 : ℝ≥0∞) ^ 257 + js.length * freshCost E R +
        (((c + B * (R + 2)) ^ 2 - c ^ 2 : ℕ) / (2 : ℝ≥0∞) ^ 257 + B * freshCost E R)
      = ((c + B * (R + 2)) ^ 2 : ℕ) / (2 : ℝ≥0∞) ^ 257 + (js.length + B) * freshCost E R := by
        calc _ = ((↑(c ^ 2) + (↑((c + B * (R + 2)) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞)) / (2 : ℝ≥0∞) ^ 257) +
            (↑js.length + ↑B) * freshCost E R := by rw [← ENNReal.div_add_div_same]; ring
          _ = _ := by rw [← Nat.cast_add, heq]
    _ ≤ _ := by
      have hc := chunks_keys_le circuits parameter R js h
      have hc' : c + B * (R + 2) ≤ (js.length + B) * (R + 2) := by
        dsimp only [c]; rw [Nat.add_mul]; omega
      gcongr
      all_goals first | exact hc' | simp only [Nat.cast_add, le_refl]

theorem freshCost_ne_top [Nonempty E] (R : ℕ) : freshCost E R ≠ ⊤ := by
  have hc : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (2 : ℝ≥0∞) / Fintype.card E ≠ ⊤ := ENNReal.div_ne_top (by simp) hc
  unfold freshCost
  finiteness

theorem chunksBudget_ne_top [Nonempty E] (R B c : ℕ) : chunksBudget E R B c ≠ ⊤ := by
  unfold chunksBudget
  have := freshCost_ne_top (E := E) R
  finiteness

theorem freshCost_toReal [Nonempty E] (R : ℕ) :
    (freshCost E R).toReal = (sliceBits : ℝ) / Fintype.card E + (R + 1 : ℕ) * (2 / Fintype.card E : ℝ) ^ challengeTries := by
  have hc : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (2 : ℝ≥0∞) / Fintype.card E ≠ ⊤ := ENNReal.div_ne_top (by simp) hc
  unfold freshCost
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul]

theorem chunksBudget_toReal [Nonempty E] (tree : Tree) :
    (chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js))
      (treeBatches settings tree) 0).toReal = treeAbortError (E := E) circuits settings tree := by
  have hf := freshCost_ne_top (E := E) (maxBatch circuits settings fun js => halvings (tupleCount js))
  unfold chunksBudget treeAbortError coinFailure coinKeyCollision
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, zero_add, zero_pow (by omega : 2 ≠ 0), Nat.sub_zero, freshCost_toReal]
  ring
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ D
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem treeRest_bound [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree)
    (event : (C.Party → Option TreeOutput) → Prop) (hev : ¬ event fun _ => o₀)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (hsize : 0 < settings.batchSize) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => treeRest K circuits settings parameter seeds pairKeys top tree i (prssKeysOf kT kP i)) >>=
        honestRounds F reply (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) + 3))).run' s}[event z] ≤
      δ * chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
  let M := maxBatch circuits settings (runRounds settings.mode)
  let H := maxBatch circuits settings fun js => halvings (tupleCount js)
  have hround := chunks_rounds_le circuits settings parameter
  have hhalves : ∀ b enc jobs,
      (jobs ∈ chunks settings.batchSize topJobs ∨ jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
        jobs ∈ chunks settings.batchSize (signJobs b enc)) → halvings (batchCount circuits parameter jobs) ≤ H := by
    intro b enc jobs hj
    exact measure_le_maxBatch circuits settings (fun js => halvings (tupleCount js)) parameter b enc jobs hj
  cases tree with
  | top =>
    let js := chunks settings.batchSize topJobs
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    have hx : X ≤ ceremonyBatches settings * M :=
      (hround 0 (fun _ => digit 0) js (fun jobs hj => Or.inl hj)).trans
        (Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings .top))
    have hfuel : ceremonyBatches settings * M + 3 = (ceremonyBatches settings * M + 3 - X) + X := by omega
    change Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          topRest (E := E) parameter p.1 p.2) >>=
        honestRounds F reply (ceremonyBatches settings * M + 3))).run' s}[event z] ≤ _
    rw [hfuel]
    refine (top_body_bound prims K circuits settings F reply parameter seeds pairKeys kT kP top o₀ s hn hs ho event hev δ hδ hsize
      (ceremonyBatches settings * M + 3 - X)).trans ?_
    exact mul_le_mul_of_nonneg_left (chunksCost_le_budget circuits parameter H js.length 0 js le_rfl
      (fun jobs hj => hhalves 0 (fun _ => digit 0) jobs (Or.inl hj))) zero_le
  | bottom b =>
    let js := chunks settings.batchSize (bottomJobs b)
    let B := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    let Y := B * M
    let c := (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum
    have hX : X ≤ js.length * M := hround b (fun _ => digit 0) js (fun jobs hj => Or.inr (Or.inl hj))
    have hY : ∀ enc, ((chunks settings.batchSize (signJobs b enc)).map
        (batchRounds circuits settings.mode parameter)).sum ≤ Y := by
      intro enc
      have h := hround b enc (chunks settings.batchSize (signJobs b enc)) (fun jobs hj => Or.inr (Or.inr hj))
      rw [length_chunks_signJobs settings b b enc (fun _ => digit 0)] at h
      exact h
    have hXY : X + Y ≤ ceremonyBatches settings * M := by
      calc X + Y ≤ js.length * M + B * M := add_le_add hX le_rfl
        _ = (treeBatches settings (.bottom b)) * M := by change js.length * M + B * M = (js.length + B) * M; ring
        _ ≤ _ := Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings (.bottom b))
    have hfuel : ceremonyBatches settings * M + 3 = (ceremonyBatches settings * M - (X + Y)) + Y + 3 + X := by omega
    change Pr{let z ← (simulateQ (localAnswer prims)
      (honestStart (fun i => ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          bottomRest parameter top b (signRun K circuits settings parameter seeds pairKeys b i) p.1 p.2) >>=
        honestRounds F reply (ceremonyBatches settings * M + 3))).run' s}[event z] ≤ _
    rw [hfuel]
    refine (bottom_body_bound (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      F reply parameter seeds pairKeys kT kP top b o₀ s hn hs ho event hev δ hδ hsize (ceremonyBatches settings * M - (X + Y)) Y
        (chunksBudget E H B c) hY ?_).trans ?_
    · intro enc
      exact chunksCost_le_budget circuits parameter H B c (chunks settings.batchSize (signJobs b enc))
        (le_of_eq (length_chunks_signJobs settings b b enc (fun _ => digit 0)))
        (fun jobs hj => hhalves b enc jobs (Or.inr (Or.inr hj)))
    · exact mul_le_mul_of_nonneg_left (chunksCost_prefix_budget circuits parameter H B js
        (fun jobs hj => hhalves b (fun _ => digit 0) jobs (Or.inr (Or.inl hj)))) zero_le

theorem realTree_bound [Nonempty C.Party] (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree)
    (event : (C.Party → Option TreeOutput) → Prop) (hev : ¬ event fun _ => o₀)
    (δ : ℝ≥0∞) (hδ : event (fun _ => none) → 1 ≤ δ)
    (hsize : 0 < settings.batchSize) :
    Pr{let z ← (simulateQ (localAnswer prims)
      (realTree K circuits settings top tree parameter seeds pairKeys)).run' s}[event z] ≤
      δ * chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
  unfold realTree
  simp only [newTree_eq]
  rw [show setupRounds + ceremonyFuel circuits settings =
    (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) + 3) + 3 by
      unfold ceremonyFuel setupRounds; omega]
  refine setup_step prims noFunctionality (fun l => l.elim) _ _ _ s hn _
    fun kT kP s' hn' hle hfr => ?_
  exact treeRest_bound prims K circuits settings noFunctionality (fun l => l.elim)
    parameter seeds pairKeys kT kP top tree o₀ s' hn' (cacheOK_of_frame hs hfr)
      (fun h s'' hg hle' ha => ho h s'' hg (hle.trans hle') ha) event hev δ hδ hsize

theorem jointTreeRun_bound [Nonempty C.Party] (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (hsize : 0 < settings.batchSize)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s) :
    Pr{let p ← jointTreeRun prims K circuits settings top tree parameter seeds pairKeys s}[p.1 ≠ p.2] ≤
      chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
  unfold jointTreeRun
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  obtain ⟨hn', hs', o₀, heq, ho⟩ := idealTree_value prims circuits settings parameter seeds top tree hsize s hn hs z hz
  have hbound := realTree_bound prims K circuits settings parameter seeds pairKeys top tree o₀ z.2 hn' hs' ho
    (· ≠ fun _ => o₀) (by simp) 1 (fun _ => le_rfl) hsize
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure, heq]
  rw [bind_pure_comp]
  simpa only [StateT.run'_eq, prEvent_map, Function.comp_def, one_mul] using hbound

/-- From a cache with no cell of an MPC input and no coin cell, the real ceremonies of a tree differ
from the dealer of the tree in one joint run with probability at most `treeAbortError tree`. -/
theorem jointTreeRun_toReal_le (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (hsize : 0 < settings.batchSize)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s) :
    (Pr{let p ← jointTreeRun prims K circuits settings top tree parameter seeds pairKeys s}[p.1 ≠ p.2]).toReal ≤
      treeAbortError (E := E) circuits settings tree := by
  let : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩⟩
  have hbound := jointTreeRun_bound prims K circuits settings top tree parameter seeds pairKeys hsize s hn hs
  have hreal := ENNReal.toReal_mono (chunksBudget_ne_top (E := E)
    (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0) hbound
  rwa [chunksBudget_toReal circuits settings tree] at hreal

end ThresholdLeanXmssSecurity

section HonestProgramRelabeling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α β : Type} {ι : Type} {G : OracleSpec ι}

section CeremonyHom
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

theorem monadHom_list_mapM (h : m →ᵐ n) (f : α → m β) (xs : List α) :
    h (xs.mapM f) = xs.mapM (fun x => h (f x)) := by
  induction xs with
  | nil => exact h.toFun_pure' _
  | cons x xs ih => simp only [List.mapM_cons, MonadHom.mmap_bind, MonadHom.mmap_pure, ih]

theorem monadHom_batched (h : m →ᵐ n) (size : ℕ) (run : List Job → m (Option (List (List Bit))))
    (jobs : List Job) :
    h (batched size run jobs) = batched size (fun js => h (run js)) jobs := by
  simp only [batched, MonadHom.mmap_bind, MonadHom.mmap_pure, monadHom_list_mapM]

omit [LawfulMonad m] [LawfulMonad n] in
/-- The tree assembly only composes its hash computations and its batch interface. -/
theorem monadHom_ceremonyOutput (h : m →ᵐ n) (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit))))
    (top : TopTree) (tree : Tree) :
    h (ceremonyOutput lift parameter run top tree) =
      ceremonyOutput (fun oa => h (lift oa)) parameter (fun js => h (run js)) top tree := by
  cases tree with
  | top =>
    simp only [ceremonyOutput, MonadHom.mmap_bind]
    congr 1
    funext out
    cases out <;> simp only [MonadHom.mmap_pure, MonadHom.mmap_bind]
  | bottom b =>
    simp only [ceremonyOutput, MonadHom.mmap_bind]
    congr 1
    funext out
    cases out with
    | none => exact h.toFun_pure' _
    | some outputs =>
      simp only [MonadHom.mmap_bind]
      congr 1
      funext root
      congr 1
      funext base
      congr 1
      funext result
      cases result with
      | none => exact h.toFun_pure' _
      | some pair =>
        rcases pair with ⟨randomness,encoding⟩
        simp only [MonadHom.mmap_bind]
        congr 1
        funext values
        cases values with
        | none => exact h.toFun_pure' _
        | some vals =>
          simp only [MonadHom.mmap_bind]
          congr 1
          funext path
          congr 1
          funext topRoot
          split <;> exact h.toFun_pure' _

end CeremonyHom

end ThresholdLeanXmssSecurity
end HonestProgramRelabeling
