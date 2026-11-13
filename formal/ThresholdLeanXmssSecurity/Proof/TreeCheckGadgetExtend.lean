import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetBlocks
import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetPass

/-! # The check's two-product peer transitions

`coupled_extend` handles a shared hash prefix followed by a two-product
extension, including missing inputs and selective aborts. `coupled_finalMask`
handles the two scalar mask observations and the conditional extension in one
real round and two hybrid rounds.

The peer interaction retains its real named mask table along with the shared
rushing state and optional outputs. The continuation uses that installed
hidden cache. The first final-mask block remains installed when the second
block is sampled; field-row comparisons use only positions below two.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckGadgetExtend
open TreeCheckKernelCoupling TreeCheckWalkRecipe TreeCheckWalkTransport
open TreeCheckWalkCoupling TreeCheckRandRows TreeCheckGadgetBlocks TreeCheckGadgetPass
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
local instance : SampleableType E := SampleableType.ofFintype E

/-- The actual named rows remain available after coupling the full peer interaction. -/
theorem peer_rows_coupling {σ : Type} (count : ℕ)
    (known : Shares C E) (pairs : C.Party → C.Party → ℕ → E)
    (v : C.Party → ℕ → E)
    (answer : (C.Party → C.Party → Option (Msg E)) →
      ProbComp (σ × (C.Party → C.Party → Option (Msg E)))) :
    RelTriple
      (do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        let b ← answer (realMsgs K D (elementCodec K) known pairs (termTable vals) (pairTable vals) v)
        pure (vals, b.1, realOut K D (elementCodec K) known pairs (termTable vals) (pairTable vals) v b.2))
      (do
        let r ← $ᵗ (C.Term → Fin count → E)
        let p ← $ᵗ (C.Pair → Fin count → E)
        let w ← $ᵗ (C.Term → Fin count → E)
        let b ← answer (realMsgs K D (elementCodec K) known pairs r p (fun _ _ => 0))
        pure (b.1, idealOut D (filler K .peer)
          (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
          (peerReply K D (elementCodec K) known pairs r p b.2) w))
      (fun a b => a.2 = b) := by
  letI : CharP E 2 := charTwo
  apply relTriple_of_map_left (f := Prod.snd)
  have h := treeSim_peer_round (c := count) K D (elementCodec K) (elementCodec_roundTrip K)
    known pairs v (filler K .peer) (fun T g => filler_peer_corrupt K D T g) answer
  apply relTriple_of_evalDist_eq_left _ h
  simp only [map_bind, map_pure]
  let f := fun rp : (C.Term → Fin count → E) × (C.Pair → Fin count → E) => do
    let b ← answer (realMsgs K D (elementCodec K) known pairs rp.1 rp.2 v)
    pure (b.1, realOut K D (elementCodec K) known pairs rp.1 rp.2 v b.2)
  have he := evalDist_keyName_tables (C := C) (R := E) count
  have hh := congrArg (fun d => d >>= fun rp => 𝒟[f rp]) he
  simpa only [← evalDist_bind, bind_map_left, bind_assoc, pure_bind, f] using hh

/-- A fresh installation extends the old cache without modifying any retained cell. -/
theorem cacheFin_grows {n : ℕ} (addr : Fin n → HiddenAddress C) (vals : Fin n → Bit)
    (c : HiddenCache C) (fresh : ∀ i, c (addr i) = none) : c ≤ cacheFin addr vals c := by
  intro x v hx
  rw [cacheFin_of_not_mem addr vals c x (fun i he => by
    rw [he, fresh i] at hx
    cases hx)]
  exact hx

/-- The second final-mask block retains the complete first block. -/
theorem finalMask_cache_grows (keys : KeyName C → HashOutput) (label : ℕ)
    (first second : KeyName C → Fin 2 → E) (c : HiddenCache C)
    (fresh : TreeSimFutureEmpty label c) :
    treeSimCheckPrssCache K D keys label 1 2 first c ≤
      treeSimCheckPrssCache K D keys (label + 1) 0 2 second
        (treeSimCheckPrssCache K D keys label 1 2 first c) := by
  apply cacheFin_grows
  intro i
  exact next_fieldBlock_fresh K D keys keys label 1 2 0 2 first c fresh i

/-- After the actual draw, only the party identity from the context is used. -/
theorem contextProductValues_self (ctx : Context C) (i : C.Party) (self : ctx.self = i)
    (products : List (Product C E)) :
    contextProductValues K ctx products = contextProductValues K (localContext i) products := by
  funext g
  unfold contextProductValues
  split
  · rename_i p hp
    cases p <;> simp only [productShare, mulRep, mulSh, self, localContext]
  · rfl

/-- The real and hybrid records use the same peer history update. -/
theorem recordPeer_eq (i : C.Party) (history : C.Term → List Bit) (out : Shares C E) (count : ℕ) :
    recordPeer K (elementCodec K) i history out count = recordHistory K i history out count := rfl

/-- A bounded field-row agreement fixes the entire suspended peer step. -/
theorem peerStep_below {β : Type} (ctx : Context C) (a b : PrssOutput C E)
    (v : ℕ → E) (count : ℕ) (st : RunState C)
    (k : Shares C E × RunState C → PartyM C E RealSpec β)
    (terms : ∀ T g, g < count → a.1 T g = b.1 T g)
    (pairs : ∀ j g, g < count → a.2 j g = b.2 j g) :
    treeSimPeerStep K ctx (elementCodec K) a v count st k =
      treeSimPeerStep K ctx (elementCodec K) b v count st k := by
  unfold treeSimPeerStep
  rw [reshareOut_below K ctx (elementCodec K) a b v v terms pairs (fun _ _ => rfl)]
  congr 1
  apply congrArg exchangeResume
  funext inbox
  rw [reshareZ_below K ctx (elementCodec K) a b v v inbox terms pairs (fun _ _ => rfl)]

def peerProgram {β : Type} (i : C.Party) (rnd : PrssOutput C E) (v : ℕ → E)
    (st : RunState C) (k : Shares C E × RunState C → PartyM C E RealSpec β) :
    PartyM C E RealSpec β :=
  exchange (reshareOut K (localContext i) (elementCodec K) rnd.1 rnd.2 v 2) >>= fun inbox =>
    let out := reshareZ K (localContext i) (elementCodec K) rnd.1 rnd.2 v 2 inbox
    k (out, ⟨recordHistory K i st.history out 2, st.label + 1, st.tag⟩)

def resumeReal {β : Type} (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec β)
    (out : C.Party → Option (Shares C E)) : C.Party → PartyM C E RealSpec β := fun i =>
  match out i with
  | none => failure
  | some z => k i (z, ⟨recordHistory K i (st i).history z 2, (st i).label + 1, (st i).tag⟩)

theorem peerProgram_advance {β : Type} (i : C.Party) (rnd : PrssOutput C E) (v : ℕ → E)
    (st : RunState C) (k : Shares C E × RunState C → PartyM C E RealSpec β) :
    advance (peerProgram K i rnd v st k).run =
      pure (treeSimPeerStep K (localContext i) (elementCodec K) rnd v 2 st k) := by
  rw [peerProgram, advance_exchange_bind]
  rfl

/-- Ready installed rows replace the actual extended-multiplication draw. -/
theorem extend_pass {β : Type} (prss : C.Party → PrssKeys C) (cache0 : HashCache C)
    (ctx : Context C) (i : C.Party) (honest : i ∉ D.1) (self : ctx.self = i)
    (terms : ∀ T, i ∈ C.holders T → ctx.prss.term T = streamKey D prss (.term T))
    (pairs : ∀ j (hj : j ≠ i), ctx.prss.pair j = streamKey D prss (.pair (C.pairOf i j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (label : ℕ) (vals : KeyName C → Fin 2 → E)
    (products : List (Product C E)) (width : products.length = 2)
    (st : RunState C) (labels : st.label = label)
    (k : Shares C E × RunState C → PartyM C E RealSpec β)
    (h : HashCache C) (c c' : HiddenCache C) (grow : cache0 ≤ h)
    (installed : treeSimCheckPrssCache K D (streamKey D prss) label 0 2 vals c ≤ c') :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((((realCheckGadgets K ctx).extendMult products).run st >>= k).run)))).run (h, c') =
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (peerProgram K i
        (frandShare D 2 (knownRows D (fieldRow prims K D prss cache0 label 0 2)).1
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).2 (termTable vals) (pairTable vals) i)
        (contextProductValues K (localContext i) products) st k).run))).run (h, c') := by
  have ready := prssDraw_rows_used prims K D prss cache0 h ctx (self ▸ honest)
    (fun T hT => terms T (self ▸ hT)) (by simpa only [self] using pairs)
    cached grow label 0 2 vals c c' installed
  have ready' : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) st.label 0 products.length) (LocalSpec C)))).run
      (h, c') = pure (treeSimCheckPrssRows prims K D (derivedKey D prss cache0) label 0 2 vals i, (h, c')) := by
    simpa only [labels, width, self] using ready
  rw [treeSim_extendMult_start prims K D ctx products st k _ _ ready', width,
    contextProductValues_self K ctx i self products]
  have below := prssRows_frandShare_below prims K D prss cache0 label 0 2 vals i honest
  rw [peerStep_below K ctx _ _ _ 2 st k
    (fun T g hg => (below g hg).1 T) (fun j g hg => (below g hg).2 j)]
  rw [peerProgram_advance]
  simp only [worldRoles, free_pure, simulateQ_pure, StateT.run_pure]
  subst i
  rfl

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- Changing only corrupt programs cannot change the real execution. -/
theorem realRun_congr_honest {β : Type} (n : ℕ) (stA : A.State)
    (P Q : C.Party → PartyM C E RealSpec β)
    (same : ∀ i, i ∉ D.1 → P i = Q i) (w : HashCache C × HiddenCache C) :
    realRun prims D A n stA P w = realRun prims D A n stA Q w := by
  unfold realRun
  have starts : startSteps worldRoles D P = startSteps worldRoles D Q := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp only [hi, if_true, if_false]
    rw [same i hi]
  rw [starts]

/-- The normalized real peer interaction retains its full future execution. -/
theorem realRun_peer {β : Type} (n : ℕ) (stA : A.State)
    (known : Shares C E) (pairs : C.Party → C.Party → ℕ → E)
    (r : C.Term → Fin 2 → E) (p : C.Pair → Fin 2 → E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec β)
    (h : HashCache C) (c : HiddenCache C) :
    realRun prims D A (n + 1) stA
      (fun i => peerProgram K i (frandShare D 2 known pairs r p i) (v i) (st i) (k i)) (h, c) =
      ((simulateQ (localAnswer prims) (A.round stA (realMsgs K D (elementCodec K) known pairs r p v))).run h >>= fun b =>
        realRun prims D A n b.1.1 (resumeReal K st k (realOut K D (elementCodec K) known pairs r p v b.1.2)) (b.2, c)) := by
  let rnd := frandShare D 2 known pairs r p
  let outbox := fun i => some (reshareOut K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2 (v i) 2)
  let cont := fun i inbox =>
    let out := reshareZ K (localContext i) (elementCodec K) (rnd i).1 (rnd i).2 (v i) 2 inbox
    k i (out, ⟨recordHistory K i (st i).history out 2, (st i).label + 1, (st i).tag⟩)
  change realRun prims D A (n + 1) stA (fun i => optionalExchange (outbox i) (cont i)) (h, c) = _
  rw [realRun_exchange prims D A n stA outbox cont (h, c) (by
    obtain ⟨i, hi⟩ := exists_honest D
    exact ⟨i, hi, rfl⟩)]
  rw [adversary_run]
  simp only [bind_map_left]
  apply bind_congr
  intro b
  apply realRun_congr_honest
  intro i hi
  simp only [afterExchange, outbox, Option.getD_some, realOut, if_neg hi, resumeReal, rnd, cont,
    anyAbort]
  split <;> rfl

variable (x : C.Party → Keys C) (prss : C.Party → PrssKeys C)
  (cache0 : HashCache C) (label0 : ℕ)

/-- The extension's total is the sum of the actual local product shares. -/
theorem extendTotal_eq (products : C.Party → List (Product C E)) :
    extendTotal K D (fun i => if i ∈ D.1 then none else some (products i)) =
      fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), contextProductValues K (localContext i) (products i) g := by
  funext g
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [if_neg hi, Option.map_some, Option.getD_some, contextProductValues]
  rfl

/-- The frozen adapter's extend answer has the full zero-input peer view. -/
theorem adapter_extend_answer (stA : A.State) (label : ℕ)
    (view : C.Party → List (Product C E)) :
    (rightAdversary (leftAdversary (adapter prims K D A x prss cache0 label0))).answer
      (stA, label) view = (do
        let r ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
        let p ← liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C)
        let b ← A.round stA (realMsgs K D (elementCodec K)
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).1
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).2 r p (fun _ _ => 0))
        pure ((b.1, label + 1), peerReply K D (elementCodec K)
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).1
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).2 r p b.2)) := by
  simp only [rightAdversary, leftAdversary, adapter, checkAdversary, peerSimAnswer_eq,
    randomAdversary, pure_bind, bind_assoc]
  rfl

/-- The exact hybrid extension, including the adapter label and returned hash cache. -/
theorem hybRun_extend (n : ℕ) (stA : A.State) (label : ℕ)
    (products : C.Party → List (Product C E))
    (width : ∀ i, i ∉ D.1 → (products i).length = 2)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C E → RunM C E (CheckSpec C E) Unit) (h : HashCache C) :
    hybRun prims K D (adapter prims K D A x prss cache0 label0) (n + 1) (stA, label)
      (fun i => ((hybridCheckGadgets K i).extendMult (products i) >>= k i).run' (st i)) h = (do
        let r ← $ᵗ (C.Term → Fin 2 → E)
        let p ← $ᵗ (C.Pair → Fin 2 → E)
        let b ← (simulateQ (localAnswer prims) (A.round stA (realMsgs K D (elementCodec K)
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).1
          (knownRows D (fieldRow prims K D prss cache0 label 0 2)).2 r p (fun _ _ => 0)))).run h
        let w ← $ᵗ (C.Term → Fin 2 → E)
        let out := idealOut D (filler K .peer)
          (fun g => ∑ i ∈ Finset.univ.filter (· ∉ D.1), contextProductValues K (localContext i) (products i) g)
          (peerReply K D (elementCodec K)
            (knownRows D (fieldRow prims K D prss cache0 label 0 2)).1
            (knownRows D (fieldRow prims K D prss cache0 label 0 2)).2 r p b.1.2) w
        hybRun prims K D (adapter prims K D A x prss cache0 label0) n (b.1.1, label + 1)
          (fun i => afterExtend K i (products i).length (st i) (k i) (out i)) b.2) := by
  have hw : (firstInput (fun i => if i ∈ D.1 then none else some (products i))).length = 2 := by
    obtain ⟨i, hi, he⟩ := firstInput_honest D products
    rw [he, width i hi]
  unfold hybRun
  rw [executePhase_extend, runFunctionality_extend_local K D _ _ _ (by
    intro i hi
    simp only [if_neg hi, Option.isSome_some]), hw, adapter_extend_answer]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_local_sample, bind_map_left]
  rw [extendTotal_eq]
  rfl

set_option maxHeartbeats 1000000 in
/-- The all-live two-product extension retains its sampled cache through the continuation. -/
theorem coupled_extend_all {β : Type}
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' label : ℕ)
    (products : C.Party → List (Product C E))
    (width : ∀ i, i ∉ D.1 → (products i).length = 2)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (kR : C.Party → Shares C E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → Shares C E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ out : C.Party → Option (Shares C E),
      Coupled prims K D A x prss cache0 label0 n n' (label + 1)
        (resumeReal K st kR out)
        (fun i => afterExtend K i (products i).length (hs i) (kH i) (out i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 1) label
      (fun i => ((realCheckGadgets K (ctx i)).extendMult (products i)).run (st i) >>= kR i)
      (fun i => ((hybridCheckGadgets K i).extendMult (products i) >>= kH i).run' (hs i)) := by
  intro stA h c grow fresh
  let known := knownRows D (fieldRow prims K D prss cache0 label 0 2)
  let inst := fun vals => treeSimCheckPrssCache K D (streamKey D prss) label 0 2 vals c
  let v := fun i => contextProductValues K (localContext i) (products i)
  let ans := fun view => (fun b : (A.State × (C.Party → Mail C E)) × HashCache C =>
    ((b.1.1,b.2),b.1.2)) <$> (simulateQ (localAnswer prims) (A.round stA view)).run h
  have step := peer_rows_coupling K D 2 known.1 known.2 v ans
  have grown := relTriple_support_left step (P := fun a => h ≤ a.2.1.2) (by
    intro a ha
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at ha
    obtain ⟨vals, hv, b, hb, he⟩ := ha
    subst a
    simp only [ans, support_map, Set.mem_image] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact (grows_localAnswer prims).simulateQ _ h z hz)
  have full := relTriple_bind grown (S := Final D A)
    (fa := fun a => realRun prims D A n a.2.1.1 (resumeReal K st kR a.2.2) (a.2.1.2, inst a.1))
    (fb := fun b => hybRun prims K D (adapter prims K D A x prss cache0 label0) n'
      (b.1.1, label + 1) (fun i => afterExtend K i (products i).length (hs i) (kH i) (b.2 i)) b.1.2) (by
        rintro a b ⟨he, hg⟩
        subst b
        exact next a.2.2 a.2.1.1 a.2.1.2 (inst a.1) (grow.trans hg)
          (futureEmpty_block K D (streamKey D prss) label 0 2 a.1 c fresh))
  apply relTriple_of_evalDist_eq_left
    (realRun_presample_fields prims K D A (n+1) stA _ (streamKey D prss) label 0 2 h c fresh)
  have real : ∀ vals : KeyName C → Fin 2 → E,
      realRun prims D A (n+1) stA
        (fun i => ((realCheckGadgets K (ctx i)).extendMult (products i)).run (st i) >>= kR i) (h,inst vals) =
      (ans (realMsgs K D (elementCodec K) known.1 known.2 (termTable vals) (pairTable vals) v) >>= fun b =>
        realRun prims D A n b.1.1
          (resumeReal K st kR (realOut K D (elementCodec K) known.1 known.2 (termTable vals) (pairTable vals) v b.2))
          (b.1.2,inst vals)) := by
    intro vals
    rw [realRun_localPass_congr prims D A cache0 (inst vals) _
      (fun i => peerProgram K i (frandShare D 2 known.1 known.2 (termTable vals) (pairTable vals) i)
        (v i) (st i) (kR i)) (by
        intro i hi s hg hc
        exact extend_pass prims K D prss cache0 (ctx i) i hi (self i hi)
          (fun T ht => terms i hi T ((self i hi).symm ▸ ht))
          (by simpa only [self i hi] using pairs i hi) cached label vals (products i)
          (width i hi) (st i) (labels i hi) (kR i) s.1 c s.2 hg hc) (n+1) stA (h,inst vals) grow le_rfl,
      realRun_peer]
    simp only [ans, bind_map_left]
  rw [funext real, hybRun_extend prims K D A x prss cache0 label0 n' stA label products width]
  simp only [bind_assoc, pure_bind, ans, bind_map_left] at full ⊢
  apply relTriple_of_evalDist_eq_right _ full
  apply evalDist_bind_congr' _
  intro r
  apply evalDist_bind_congr' _
  intro p
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

/-- An actual extension always reaches an abort-aware exchange. -/
theorem extend_exchange {β : Type} (ctx : Context C) (products : List (Product C E))
    (st : RunState C) (k : Shares C E × RunState C → PartyM C E RealSpec β) :
    TreeSimCheckExchange (((realCheckGadgets K ctx).extendMult products).run st >>= k) := by
  rw [realExtendMult_run, bind_assoc]
  apply TreeSimCheckExchange.oracle_bind
  intro rnd
  simp only [bind_assoc, pure_bind]
  exact TreeSimCheckExchange.exchange_bind _ _

/-- The extension includes partially live entries and every selective output abort. -/
theorem coupled_extend_core {β : Type}
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' label : ℕ) (live : C.Party → Prop)
    (products : C.Party → List (Product C E))
    (width : ∀ i, i ∉ D.1 → (products i).length = 2)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (kR : C.Party → Shares C E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → Shares C E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ out : C.Party → Option (Shares C E),
      Coupled prims K D A x prss cache0 label0 n n' (label + 1)
        (resumeReal K st kR out)
        (fun i => afterExtend K i (products i).length (hs i) (kH i) (out i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 1) label
      (fun i => if live i then ((realCheckGadgets K (ctx i)).extendMult (products i)).run (st i) >>= kR i else failure)
      (fun i => if live i then ((hybridCheckGadgets K i).extendMult (products i) >>= kH i).run' (hs i) else failure) := by
  by_cases all : ∀ i, i ∉ D.1 → live i
  · intro stA h c grow fresh
    rw [realRun_congr_honest prims D A _ _ _ _ (fun i hi => if_pos (all i hi))]
    unfold hybRun
    rw [executePhase_congr_honest D _ _ _ _ _ _ (fun i hi => if_pos (all i hi))]
    exact coupled_extend_all prims K D A x prss cache0 label0 ctx self terms pairs cached
      n n' label products width st hs labels kR kH next stA h c grow fresh
  · push Not at all
    intro stA h c grow fresh
    apply doomed_post prims D K A (adapter prims K D A x prss cache0 label0) n n' stA (stA,label) _ _ (h,c) h
    · intro i hi
      by_cases hl : live i
      · rw [if_pos hl]
        exact extend_exchange K (ctx i) (products i) (st i) (kR i)
      · rw [if_neg hl]
        intro step hh
        have he : step = .done none := by simpa only [advance_run_failure, advance_pure, support_pure, Set.mem_singleton_iff] using hh
        subst step
        rfl
    · obtain ⟨i, hi, hl⟩ := all
      exact ⟨i, hi, if_neg hl⟩

/-- Restricting a named table commutes with any later probabilistic computation.
Proof ported from TreeCheckGadgetCoin.named_tables_bind (lines 21–31). -/
theorem named_tables_bind {α : Type} (count : ℕ)
    (f : (C.Term → Fin count → E) → (C.Pair → Fin count → E) → ProbComp α) :
    𝒟[($ᵗ (KeyName C → Fin count → E)) >>= fun vals => f (termTable vals) (pairTable vals)] =
      𝒟[($ᵗ (C.Term → Fin count → E)) >>= fun t => ($ᵗ (C.Pair → Fin count → E)) >>= f t] := by
  calc
    _ = 𝒟[((fun vals : KeyName C → Fin count → E => (termTable vals, pairTable vals)) <$>
        ($ᵗ (KeyName C → Fin count → E))) >>= fun a => f a.1 a.2] := by
      simp only [bind_map_left]
    _ = _ := by
      rw [evalDist_bind, evalDist_keyName_tables, ← evalDist_bind]
      simp only [bind_assoc, pure_bind]

/-- The hybrid's first mask call retains its complete subsequent execution. -/
theorem hybRun_masks (n : ℕ) (stA : A.State) (label : ℕ)
    (hs : C.Party → RunState C)
    (k : C.Party → PrssOutput C E → RunM C E (CheckSpec C E) Unit) (h : HashCache C) :
    hybRun prims K D (adapter prims K D A x prss cache0 label0) (n + 1) (stA,label)
      (fun i => ((hybridCheckGadgets K i).randElements 2 >>= k i).run' (hs i)) h = (do
        let r ← $ᵗ (C.Term → Fin 2 → E)
        let p ← $ᵗ (C.Pair → Fin 2 → E)
        hybRun prims K D (adapter prims K D A x prss cache0 label0) n (stA,label+1)
          (fun i => (k i (frandShare D 2
            (knownRows D (fieldRow prims K D prss cache0 label 1 2)).1
            (knownRows D (fieldRow prims K D prss cache0 label 1 2)).2 r p i)).run' (nextLabel (hs i))) h) := by
  have hw : firstInput (fun i : C.Party => if i ∈ D.1 then none else some 2) = 2 := by
    obtain ⟨i, hi, he⟩ := firstInput_honest D (fun _ => 2)
    exact he
  unfold hybRun
  rw [executePhase_randElements, runFunctionality_rand_local D _ _ _ (by
    intro i hi
    simp only [if_neg hi, Option.isSome_some]), hw]
  simp only [leftAdversary, rightAdversary, adapter, checkAdversary, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_local_sample, StateT.run_bind, bind_map_left]
  apply bind_congr
  intro r
  apply bind_congr
  intro p
  apply congrArg (fun q => (simulateQ (localAnswer prims) q).run h)
  apply executePhase_congr_honest
  intro i hi
  simp only [afterRandom, randFinish, if_neg hi]
  rfl

/-- The two observed mask coordinates determine the actual final extension. -/
def maskProgram {β : Type} (ctx : Context C) (st : RunState C)
    (products : E → E → List (Product C E))
    (k : E → E → Shares C E × RunState C → PartyM C E RealSpec β) : PartyM C E RealSpec β :=
  ((realCheckGadgets K ctx).randElements 2).run st >>= fun a =>
    let wa := conv K ctx a.1.1 0
    let wb := conv K ctx a.1.1 1
    ((realCheckGadgets K ctx).extendMult (products wa wb)).run a.2 >>= k wa wb

/-- Readiness of the first block fixes precisely the coordinates observed by the check. -/
theorem mask_pass {β : Type}
    (ctx : Context C) (i : C.Party) (honest : i ∉ D.1) (self : ctx.self = i)
    (terms : ∀ T, ctx.self ∈ C.holders T → ctx.prss.term T = streamKey D prss (.term T))
    (pairs : ∀ j (hj : j ≠ ctx.self),
      ctx.prss.pair j = streamKey D prss (.pair (C.pairOf ctx.self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (label : ℕ) (vals : KeyName C → Fin 2 → E)
    (st : RunState C) (labels : st.label = label)
    (products : E → E → List (Product C E))
    (k : E → E → Shares C E × RunState C → PartyM C E RealSpec β)
    (h : HashCache C) (c c' : HiddenCache C) (grow : cache0 ≤ h)
    (installed : treeSimCheckPrssCache K D (streamKey D prss) label 1 2 vals c ≤ c') :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (maskProgram K ctx st products k).run))).run (h,c') =
    let rnd := frandShare D 2 (knownRows D (fieldRow prims K D prss cache0 label 1 2)).1
      (knownRows D (fieldRow prims K D prss cache0 label 1 2)).2 (termTable vals) (pairTable vals) i
    let wa := conv K (localContext i) rnd.1 0
    let wb := conv K (localContext i) rnd.1 1
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (((realCheckGadgets K ctx).extendMult (products wa wb)).run (nextLabel st) >>= k wa wb).run))).run (h,c') := by
  let actual := treeSimCheckPrssRows prims K D (derivedKey D prss cache0) label 1 2 vals i
  let rnd := frandShare D 2 (knownRows D (fieldRow prims K D prss cache0 label 1 2)).1
    (knownRows D (fieldRow prims K D prss cache0 label 1 2)).2 (termTable vals) (pairTable vals) i
  have ready : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) st.label 1 2) (LocalSpec C)))).run (h,c') =
      pure (actual,(h,c')) := by
    rw [labels]
    simpa only [self] using prssDraw_rows_used prims K D prss cache0 h ctx (self ▸ honest)
      terms pairs cached grow label 1 2 vals c c' installed
  have agree : ∀ g, g < 2 → conv K ctx actual.1 g = conv K (localContext i) rnd.1 g := by
    intro g hg
    rw [conv_below K ctx actual.1 rnd.1
      (fun T g hg => (prssRows_frandShare_below prims K D prss cache0 label 1 2 vals i honest g hg).1 T) g hg]
    subst i
    rfl
  unfold maskProgram
  change (simulateQ (streamWorld prims D) (worldRoles.honest
    (advance (((prssRandomness ctx (elementCodec K) 1 2).run st) >>= _).run))).run (h,c') = _
  rw [realRand_run, bind_assoc]
  simp only [pure_bind]
  rw [advance_ready_bind prims D _ actual _ (h,c') ready]
  rw [agree 0 (by decide), agree 1 (by decide)]

set_option maxHeartbeats 1000000 in
/-- The first mask and the conditional peer extension consume one real and two hybrid rounds. -/
theorem coupled_finalMask_all {β : Type}
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' label : ℕ)
    (products : C.Party → E → E → List (Product C E))
    (width : ∀ i, i ∉ D.1 → ∀ wa wb, (products i wa wb).length = 2)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (kR : C.Party → E → E → Shares C E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → E → E → Shares C E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ (wa wb : C.Party → E) (out : C.Party → Option (Shares C E)),
      Coupled prims K D A x prss cache0 label0 n n' (label + 2)
        (resumeReal K (fun i => nextLabel (st i)) (fun i => kR i (wa i) (wb i)) out)
        (fun i => afterExtend K i (products i (wa i) (wb i)).length (nextLabel (hs i))
          (kH i (wa i) (wb i)) (out i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 2) label
      (fun i => maskProgram K (ctx i) (st i) (products i) (kR i))
      (fun i => ((hybridCheckGadgets K i).randElements 2 >>= fun rnd =>
        let wa := conv K (localContext i) rnd.1 0
        let wb := conv K (localContext i) rnd.1 1
        (hybridCheckGadgets K i).extendMult (products i wa wb) >>= kH i wa wb).run' (hs i)) := by
  intro stA h c grow fresh
  let known := knownRows D (fieldRow prims K D prss cache0 label 1 2)
  let inst := fun vals => treeSimCheckPrssCache K D (streamKey D prss) label 1 2 vals c
  let rnd := fun vals => frandShare D 2 known.1 known.2 (termTable vals) (pairTable vals)
  let wa := fun vals i => conv K (localContext i) (rnd vals i).1 0
  let wb := fun vals i => conv K (localContext i) (rnd vals i).1 1
  apply relTriple_of_evalDist_eq_left
    (realRun_presample_fields prims K D A (n+1) stA _ (streamKey D prss) label 1 2 h c fresh)
  rw [show n' + 2 = (n' + 1) + 1 from rfl, hybRun_masks]
  apply relTriple_of_evalDist_eq_right (named_tables_bind 2 _)
  apply relTriple_bind (relTriple_refl ($ᵗ (KeyName C → Fin 2 → E)))
  rintro vals _ rfl
  rw [realRun_localPass_congr prims D A cache0 (inst vals) _
    (fun i => ((realCheckGadgets K (ctx i)).extendMult (products i (wa vals i) (wb vals i))).run
      (nextLabel (st i)) >>= kR i (wa vals i) (wb vals i)) (by
      intro i hi s hg hc
      exact mask_pass prims K D prss cache0 (ctx i) i hi (self i hi) (terms i hi) (pairs i hi)
        cached label vals (st i) (labels i hi) (products i) (kR i) s.1 c s.2 hg hc)
    (n+1) stA (h,inst vals) grow le_rfl]
  exact coupled_extend_all prims K D A x prss cache0 label0 ctx self terms pairs cached
    n n' (label+1) (fun i => products i (wa vals i) (wb vals i))
    (fun i hi => width i hi _ _) (fun i => nextLabel (st i)) (fun i => nextLabel (hs i))
    (fun i hi => by simp only [nextLabel, labels i hi])
    (fun i => kR i (wa vals i) (wb vals i)) (fun i => kH i (wa vals i) (wb vals i))
    (next (wa vals) (wb vals)) stA h (inst vals) grow
    (futureEmpty_block K D (streamKey D prss) label 1 2 vals c fresh)

/-- Two local draws followed by the peer exchange still propagate every abort. -/
theorem mask_exchange {β : Type} (ctx : Context C) (st : RunState C)
    (products : E → E → List (Product C E))
    (k : E → E → Shares C E × RunState C → PartyM C E RealSpec β) :
    TreeSimCheckExchange (maskProgram K ctx st products k) := by
  unfold maskProgram
  change TreeSimCheckExchange (((prssRandomness ctx (elementCodec K) 1 2).run st) >>= _)
  rw [realRand_run, bind_assoc]
  simp only [pure_bind]
  apply TreeSimCheckExchange.oracle_bind
  intro rnd
  exact extend_exchange K ctx _ _ _

/-- A pure suspended residual lets the full real hash prefix be factored out. -/
theorem realRun_pure_prefix {X β : Type} [Inhabited X] (n : ℕ) (stA : A.State)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (P : C.Party → X → PartyM C E RealSpec β) (steps : C.Party → X → Step C E RealSpec β)
    (pureP : ∀ i a, advance (P i a).run = pure (steps i a))
    (h : HashCache C) (c : HiddenCache C) :
    realRun prims D A n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= P i) (h,c) =
      ((simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        realRun prims D A n stA (fun i => P i ((r.1 i).getD default)) (r.2,c)) := by
  rw [realRun_prefix prims D A n stA W P steps pureP]
  apply bind_congr_of_forall_mem_support
  intro r hr
  have shape := hashPrefix_support D W r.1 (by
    apply OracleComp.support_simulateQ_run'_subset (localAnswer prims)
    rw [StateT.run'_eq, support_map]
    exact ⟨r,hr,rfl⟩)
  have start : startSteps worldRoles D (fun i => P i ((r.1 i).getD default)) =
      pure (prefixSteps steps r.1) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, prefixSteps, (shape i).1 hi]
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((shape i).2 hi)
      simp only [if_neg hi, ha, Option.getD_some, pureP, worldRoles, free_pure, prefixSteps]
  simp only [realRun, start, pure_bind]

/-- The hybrid prefix exposes the same shared vector of hash answers. -/
theorem hybRun_pure_prefix {X : Type} [Inhabited X]
    (Ad : CheckAdversary C E (List (Tuple C))) (n : ℕ) (stA : Ad.State)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (P : C.Party → X → PartyM C E (CheckSpec C E) Unit)
    (steps : C.Party → X → Step C E (CheckSpec C E) Unit)
    (pureP : ∀ i a, advance (P i a).run = pure (steps i a)) (h : HashCache C) :
    hybRun prims K D Ad n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= P i) h =
      ((simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        hybRun prims K D Ad n stA (fun i => P i ((r.1 i).getD default)) r.2) := by
  rw [hybRun_prefix prims D K Ad n stA W P steps pureP]
  apply bind_congr_of_forall_mem_support
  intro r hr
  have shape := hashPrefix_support D W r.1 (by
    apply OracleComp.support_simulateQ_run'_subset (localAnswer prims)
    rw [StateT.run'_eq, support_map]
    exact ⟨r,hr,rfl⟩)
  have start : startSteps localRoles D (fun i => P i ((r.1 i).getD default)) =
      pure (prefixSteps steps r.1) := by
    unfold startSteps
    apply sequenceFin_congr_pure
    intro i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, prefixSteps, (shape i).1 hi]
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((shape i).2 hi)
      simp only [if_neg hi, ha, Option.getD_some, pureP, localRoles, prefixSteps]
  simp only [hybRun, executePhase, start, pure_bind]

/-- An installed local-pass equality remains valid after arbitrary hash queries. -/
theorem prefix_pass_congr {X β : Type} (base : HashCache C) (inst : HiddenCache C)
    (W : OracleComp (Query C →ₒ HashOutput) X)
    (P Q : X → PartyM C E RealSpec β)
    (same : ∀ a s, base ≤ s.1 → inst ≤ s.2 →
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (P a).run))).run s =
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (Q a).run))).run s)
    (s : HashCache C × HiddenCache C) (grow : base ≤ s.1) (installed : inst ≤ s.2) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (oracleStep (liftComp W (RoSpec C)) >>= P).run))).run s =
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance (oracleStep (liftComp W (RoSpec C)) >>= Q).run))).run s := by
  simp only [worldRoles, advance_oracleStep_bind, free_bind, simulateQ_bind, StateT.run_bind]
  apply bind_congr_of_forall_mem_support
  intro r hr
  exact same r.1 r.2 (grow.trans (treeSim_stream_grows prims D _ s r hr))
    (installed.trans (treeSim_hidden_grows prims D _ s r hr))

set_option maxHeartbeats 1000000 in
/-- Presampling a ready field block factors a hash prefix without losing the cache correlations. -/
theorem realRun_field_prefix {X β : Type} [Inhabited X] (n : ℕ) (stA : A.State)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X)
    (P : C.Party → X → PartyM C E RealSpec β) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) (h : HashCache C) (c : HiddenCache C)
    (grow : cache0 ≤ h) (fresh : TreeSimFutureEmpty label c)
    (Q : (KeyName C → Fin count → E) → C.Party → X → PartyM C E RealSpec β)
    (steps : (KeyName C → Fin count → E) → C.Party → X → Step C E RealSpec β)
    (pureQ : ∀ vals i a, advance (Q vals i a).run = pure (steps vals i a))
    (same : ∀ vals i, i ∉ D.1 → ∀ a s, cache0 ≤ s.1 →
      treeSimCheckPrssCache K D keys label idx count vals c ≤ s.2 →
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (P i a).run))).run s =
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (Q vals i a).run))).run s) :
    𝒟[realRun prims D A n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= P i) (h,c)] =
      𝒟[(simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        realRun prims D A n stA (fun i => P i ((r.1 i).getD default)) (r.2,c)] := by
  let inst := fun vals => treeSimCheckPrssCache K D keys label idx count vals c
  calc
    _ = 𝒟[($ᵗ (KeyName C → Fin count → E)) >>= fun vals =>
        realRun prims D A n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= Q vals i)
          (h,inst vals)] := by
      rw [realRun_presample_fields prims K D A n stA _ keys label idx count h c fresh]
      apply evalDist_bind_congr' _
      intro vals
      rw [realRun_localPass_congr prims D A cache0 (inst vals) _ _ (by
        intro i hi s hg hc
        exact prefix_pass_congr prims D cache0 (inst vals) (W i) (P i) (Q vals i)
          (same vals i hi) s hg hc) n stA (h,inst vals) grow le_rfl]
    _ = 𝒟[(simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        ($ᵗ (KeyName C → Fin count → E)) >>= fun vals =>
          realRun prims D A n stA (fun i => Q vals i ((r.1 i).getD default)) (r.2,inst vals)] := by
      simp_rw [realRun_pure_prefix prims D A n stA W _ _ (pureQ _)]
      exact prefix_sample_comm prims D W h _
    _ = _ := by
      apply evalDist_bind_congr
      intro r hr
      have hg := grow.trans ((grows_localAnswer prims).simulateQ _ h r hr)
      symm
      rw [realRun_presample_fields prims K D A n stA _ keys label idx count r.2 c fresh]
      apply evalDist_bind_congr' _
      intro vals
      rw [realRun_localPass_congr prims D A cache0 (inst vals) _ _ (by
        intro i hi s hs hc
        exact same vals i hi _ s hs hc) n stA (r.2,inst vals) hg le_rfl]

/-- The final mask segment includes all missing-input and selective-abort cases. -/
theorem coupled_finalMask {β : Type}
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' label : ℕ) (live : C.Party → Prop)
    (products : C.Party → E → E → List (Product C E))
    (width : ∀ i, i ∉ D.1 → ∀ wa wb, (products i wa wb).length = 2)
    (st hs : C.Party → RunState C) (labels : ∀ i, i ∉ D.1 → (st i).label = label)
    (kR : C.Party → E → E → Shares C E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → E → E → Shares C E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ (wa wb : C.Party → E) (out : C.Party → Option (Shares C E)),
      Coupled prims K D A x prss cache0 label0 n n' (label + 2)
        (resumeReal K (fun i => nextLabel (st i)) (fun i => kR i (wa i) (wb i)) out)
        (fun i => afterExtend K i (products i (wa i) (wb i)).length (nextLabel (hs i))
          (kH i (wa i) (wb i)) (out i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 2) label
      (fun i => if live i then maskProgram K (ctx i) (st i) (products i) (kR i) else failure)
      (fun i => if live i then ((hybridCheckGadgets K i).randElements 2 >>= fun rnd =>
        let wa := conv K (localContext i) rnd.1 0
        let wb := conv K (localContext i) rnd.1 1
        (hybridCheckGadgets K i).extendMult (products i wa wb) >>= kH i wa wb).run' (hs i) else failure) := by
  by_cases all : ∀ i, i ∉ D.1 → live i
  · intro stA h c grow fresh
    rw [realRun_congr_honest prims D A _ _ _ _ (fun i hi => if_pos (all i hi))]
    unfold hybRun
    rw [executePhase_congr_honest D _ _ _ _ _ _ (fun i hi => if_pos (all i hi))]
    exact coupled_finalMask_all prims K D A x prss cache0 label0 ctx self terms pairs cached
      n n' label products width st hs labels kR kH next stA h c grow fresh
  · push Not at all
    intro stA h c grow fresh
    apply doomed_post prims D K A (adapter prims K D A x prss cache0 label0) n (n'+1) stA (stA,label) _ _ (h,c) h
    · intro i hi
      by_cases hl : live i
      · rw [if_pos hl]
        exact mask_exchange K (ctx i) (st i) (products i) (kR i)
      · rw [if_neg hl]
        intro step hh
        have he : step = .done none := by simpa only [advance_run_failure, advance_pure, support_pure, Set.mem_singleton_iff] using hh
        subst step
        rfl
    · obtain ⟨i, hi, hl⟩ := all
      exact ⟨i, hi, if_neg hl⟩

/-- The hybrid extension is pure up to its functionality suspension. -/
theorem extend_pure (i : C.Party) (products : List (Product C E)) (st : RunState C)
    (k : Shares C E → RunM C E (CheckSpec C E) Unit) :
    ∃ step, advance (((hybridCheckGadgets K i).extendMult products >>= k).run' st).run = pure step := by
  rw [extendMult_run', advance_call_bind]
  exact ⟨_,rfl⟩

set_option maxHeartbeats 1000000 in
/-- A shared hash prefix followed by the actual two-product extension and its continuation. -/
theorem coupled_extend {X β : Type} [Inhabited X]
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X) (live : C.Party → X → Prop)
    (products : C.Party → X → List (Product C E))
    (width : ∀ i, i ∉ D.1 → ∀ a, (products i a).length = 2)
    (st hs : C.Party → X → RunState C) (labels : ∀ i, i ∉ D.1 → ∀ a, (st i a).label = label)
    (kR : C.Party → X → Shares C E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → X → Shares C E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ (xs : C.Party → X) (out : C.Party → Option (Shares C E)),
      Coupled prims K D A x prss cache0 label0 n n' (label + 1)
        (resumeReal K (fun i => st i (xs i)) (fun i => kR i (xs i)) out)
        (fun i => afterExtend K i (products i (xs i)).length (hs i (xs i)) (kH i (xs i)) (out i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 1) label
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        if live i a then ((realCheckGadgets K (ctx i)).extendMult (products i a)).run (st i a) >>= kR i a else failure)
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        if live i a then ((hybridCheckGadgets K i).extendMult (products i a) >>= kH i a).run' (hs i a) else failure) := by
  intro stA h c grow fresh
  let P := fun i a => if live i a then
    ((realCheckGadgets K (ctx i)).extendMult (products i a)).run (st i a) >>= kR i a else failure
  let H := fun i a => if live i a then
    ((hybridCheckGadgets K i).extendMult (products i a) >>= kH i a).run' (hs i a) else failure
  let known := knownRows D (fieldRow prims K D prss cache0 label 0 2)
  let Q := fun vals i a => if live i a then peerProgram K i
    (frandShare D 2 known.1 known.2 (termTable vals) (pairTable vals) i)
    (contextProductValues K (localContext i) (products i a)) (st i a) (kR i a) else failure
  have pureQ : ∀ vals i a, ∃ step, advance (Q vals i a).run = pure step := by
    intro vals i a
    by_cases hl : live i a
    · simp only [Q, if_pos hl, peerProgram_advance]
      exact ⟨_,rfl⟩
    · simp only [Q, if_neg hl, advance_run_failure]
      exact ⟨_,rfl⟩
  have pureH : ∀ i a, ∃ step, advance (H i a).run = pure step := by
    intro i a
    by_cases hl : live i a
    · simp only [H, if_pos hl]
      exact extend_pure K i _ _ _
    · simp only [H, if_neg hl, advance_run_failure]
      exact ⟨_,rfl⟩
  apply relTriple_of_evalDist_eq_left
    (realRun_field_prefix prims K D A cache0 (n+1) stA W P (streamKey D prss) label 0 2 h c grow fresh
      Q (fun vals i a => (pureQ vals i a).choose) (fun vals i a => (pureQ vals i a).choose_spec) (by
        intro vals i hi a s hg hc
        by_cases hl : live i a
        · simp only [P,Q,if_pos hl]
          exact extend_pass prims K D prss cache0 (ctx i) i hi (self i hi)
            (fun T ht => terms i hi T ((self i hi).symm ▸ ht))
            (by simpa only [self i hi] using pairs i hi) cached label vals (products i a)
            (width i hi a) (st i a) (labels i hi a) (kR i a) s.1 c s.2 hg hc
        · simp only [P,Q,if_neg hl]))
  change RelTriple _ (hybRun prims K D (adapter prims K D A x prss cache0 label0) (n'+1)
    (stA,label) (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= H i) h) (Final D A)
  rw [hybRun_pure_prefix prims K D (adapter prims K D A x prss cache0 label0) (n'+1) (stA,label) W H
    (fun i a => (pureH i a).choose) (fun i a => (pureH i a).choose_spec)]
  apply relTriple_bind (relTriple_support_left (relTriple_refl _)
    (P := fun r => h ≤ r.2) (fun r hr => (grows_localAnswer prims).simulateQ _ h r hr))
  rintro r _ ⟨rfl,hg⟩
  exact coupled_extend_core prims K D A x prss cache0 label0 ctx self terms pairs cached
    n n' label (fun i => live i ((r.1 i).getD default))
    (fun i => products i ((r.1 i).getD default)) (fun i hi => width i hi _)
    (fun i => st i ((r.1 i).getD default)) (fun i => hs i ((r.1 i).getD default))
    (fun i hi => labels i hi _) (fun i => kR i ((r.1 i).getD default))
    (fun i => kH i ((r.1 i).getD default)) (next (fun i => (r.1 i).getD default))
    stA r.2 c (grow.trans hg) fresh

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.peer_rows_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms peer_rows_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.finalMask_cache_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalMask_cache_grows

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.extend_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extend_pass

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.realRun_peer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_peer

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.hybRun_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hybRun_extend

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.coupled_extend_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_extend_all

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.coupled_extend_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_extend_core

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.mask_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mask_pass

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.coupled_finalMask_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_finalMask_all

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.realRun_field_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_field_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.coupled_finalMask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_finalMask

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetExtend.coupled_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_extend

end ThresholdLeanXmssSecurity.TreeCheckGadgetExtend
