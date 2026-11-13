import ThresholdLeanXmssSecurity.Proof.TreeCheckRandRows

/-! # Installed random blocks for the check gadgets

Fresh named field and bit tables can be sampled before the real execution.
The installed cells remain in the hidden cache. Honest PRSS draws replay the
same rows at every extending state, and preserve both caches. Field rows
retain the codec's padding; bit rows agree with the complete `frandShare`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks
open TreeCheckKernelCoupling TreeCheckWalkRecipe TreeCheckWalkTransport
open TreeCheckWalkCoupling TreeCheckRandRows
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
local instance : SampleableType E := SampleableType.ofFintype E

/-- Presample the hidden field rows and retain their cells for the full real run. -/
theorem realRun_presample_fields {β : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (stA : A.State)
    (P : C.Party → PartyM C E RealSpec β) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) (h : HashCache C) (c : HiddenCache C)
    (fresh : TreeSimFutureEmpty label c) :
    𝒟[realRun prims D A n stA P (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (KeyName C → Fin count → E)
        realRun prims D A n stA P (h, treeSimCheckPrssCache K D keys label idx count vals c))] := by
  exact treeSimCheck_world_presample_field_rows prims K D _ count
    (treeSimCheckPrssAddress D keys label idx count)
    (treeSimCheckPrssAddress_injective D keys label idx count)
    (treeSimCheckPrssSource D count) (treeSimCheckPrssSource_injective D count)
    (treeSimCheckPrssAddress_hidden D keys label idx count) h c (fun _ => fresh _ le_rfl)

abbrev BitIndex (D : C.Coalition) (count : ℕ) :=
  {name : KeyName C // Hidden D name} × Fin count

-- Port of TreeSimCheck.treeSimCheckPrssSource, for bit rather than field positions.
def bitSource (count : ℕ) :
    Fin (Fintype.card (BitIndex D count)) → KeyName C × Fin count :=
  fun i => let a := (Fintype.equivFin (BitIndex D count)).symm i
           (a.1.1, a.2)

theorem bitSource_injective (count : ℕ) : Function.Injective (bitSource D count) := by
  intro i j he
  apply (Fintype.equivFin (BitIndex D count)).symm.injective
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst he
  · exact congrArg (fun a : KeyName C × Fin count => a.2) he

def bitAddress (keys : KeyName C → HashOutput) (label idx count : ℕ) :
    Fin (Fintype.card (BitIndex D count)) → HiddenAddress C :=
  fun i => let a := bitSource D count i
           ((a.1, keys a.1), label, idx, a.2.val)

theorem bitAddress_injective (keys : KeyName C → HashOutput) (label idx count : ℕ) :
    Function.Injective (bitAddress D keys label idx count) := by
  intro i j he
  apply bitSource_injective D count
  apply Prod.ext
  · exact congrArg (fun a => a.1.1) he
  · apply Fin.ext
    exact congrArg (fun a => a.2.2.2) he

theorem bitAddress_hidden (keys : KeyName C → HashOutput) (label idx count : ℕ)
    (i : Fin (Fintype.card (BitIndex D count))) :
    Hidden D (bitAddress D keys label idx count i).1.1 :=
  ((Fintype.equivFin (BitIndex D count)).symm i).1.2

def bitCache (keys : KeyName C → HashOutput) (label idx count : ℕ)
    (vals : KeyName C → Fin count → Bit) (c : HiddenCache C) : HiddenCache C :=
  cacheFin (bitAddress D keys label idx count)
    (fun i => vals (bitSource D count i).1 (bitSource D count i).2) c

theorem bitCache_at (keys : KeyName C → HashOutput) (label idx count : ℕ)
    (vals : KeyName C → Fin count → Bit) (c : HiddenCache C)
    (name : KeyName C) (hidden : Hidden D name) (g : Fin count) :
    bitCache D keys label idx count vals c ((name, keys name), label, idx, g.val) =
      some (vals name g) := by
  let i := Fintype.equivFin (BitIndex D count) (⟨name, hidden⟩, g)
  have hs : bitSource D count i = (name, g) := by simp [bitSource, i]
  have ha : bitAddress D keys label idx count i = ((name, keys name), label, idx, g.val) := by
    simp only [bitAddress, hs]
  have hc := cacheFin_at (bitAddress D keys label idx count)
    (bitAddress_injective D keys label idx count)
    (fun i => vals (bitSource D count i).1 (bitSource D count i).2) c i
  rw [ha] at hc
  simpa only [bitCache, hs] using hc

-- Bit port of TreeSimCheck.treeSimCheck_field_rows_uniform.
theorem bit_rows_uniform (count : ℕ) :
    𝒟[(fun vals : KeyName C → Fin count → Bit =>
      fun i => vals (bitSource D count i).1 (bitSource D count i).2) <$>
      ($ᵗ (KeyName C → Fin count → Bit))] =
      𝒟[$ᵗ (Fin (Fintype.card (BitIndex D count)) → Bit)] := by
  let e := (Equiv.curry (KeyName C) (Fin count) Bit).symm
  have he := evalDist_map_bijective_uniform_cross
    (α := KeyName C → Fin count → Bit) e e.bijective
  have hp := evalDist_uniformSample_map_comp_injective (R := Bit) (bitSource_injective D count)
  rw [bind_pure_comp] at hp
  calc
    _ = 𝒟[(fun bits => bits ∘ bitSource D count) <$>
        (e <$> ($ᵗ (KeyName C → Fin count → Bit)))] := by
      simp only [Functor.map_map]
      rfl
    _ = _ := by rw [evalDist_map, he, ← evalDist_map]; exact hp

/-- Presample named bit rows without removing the installed cells afterwards. -/
theorem realRun_presample_bits {β : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (stA : A.State)
    (P : C.Party → PartyM C E RealSpec β) (keys : KeyName C → HashOutput)
    (label idx count : ℕ) (h : HashCache C) (c : HiddenCache C)
    (fresh : TreeSimFutureEmpty label c) :
    𝒟[realRun prims D A n stA P (h, c)] =
      𝒟[(do
        let vals ← $ᵗ (KeyName C → Fin count → Bit)
        realRun prims D A n stA P (h, bitCache D keys label idx count vals c))] := by
  unfold realRun bitCache
  rw [treeSimCheck_world_presample_table prims D _ (bitAddress D keys label idx count)
    (bitAddress_injective D keys label idx count) (bitAddress_hidden D keys label idx count)
    h c (fun _ => fresh _ le_rfl), evalDist_bind, ← bit_rows_uniform D count,
    ← evalDist_bind, bind_map_left]

/-- A block at one label leaves every larger label empty. -/
theorem futureEmpty_block (keys : KeyName C → HashOutput) (label idx count : ℕ)
    (vals : KeyName C → Fin count → E) (c : HiddenCache C)
    (fresh : TreeSimFutureEmpty label c) :
    TreeSimFutureEmpty (label + 1) (treeSimCheckPrssCache K D keys label idx count vals c) :=
  cacheFin_freshLabel _ label (fun _ => rfl) _ c fresh

theorem futureEmpty_bitBlock (keys : KeyName C → HashOutput) (label idx count : ℕ)
    (vals : KeyName C → Fin count → Bit) (c : HiddenCache C)
    (fresh : TreeSimFutureEmpty label c) :
    TreeSimFutureEmpty (label + 1) (bitCache D keys label idx count vals c) :=
  cacheFin_freshLabel _ label (fun _ => rfl) _ c fresh

/-- The next field block is fresh after installing the preceding block. -/
theorem next_fieldBlock_fresh (keys keys' : KeyName C → HashOutput)
    (label idx count idx' count' : ℕ) (vals : KeyName C → Fin count → E)
    (c : HiddenCache C) (fresh : TreeSimFutureEmpty label c)
    (i : Fin (Fintype.card (TreeSimCheckPrssIndex D count'))) :
    treeSimCheckPrssCache K D keys label idx count vals c
      (treeSimCheckPrssAddress D keys' (label + 1) idx' count' i) = none :=
  futureEmpty_block K D keys label idx count vals c fresh _ le_rfl

/-- Only the visible term and pair names read by an honest operator need cached keys. -/
theorem used_visible_keys (prss : C.Party → PrssKeys C) (cache0 h : HashCache C)
    (cached : UsedKeysCached D prss cache0) (grow : cache0 ≤ h)
    (i : C.Party) (honest : i ∉ D.1) :
    (∀ T, ¬ Hidden D (.term T) →
      h (.streamKey (streamKey D prss (.term T))) = some (derivedKey D prss cache0 (.term T))) ∧
    (∀ j (ne : i ≠ j), ¬ Hidden D (.pair (C.pairOf i j ne)) →
      h (.streamKey (streamKey D prss (.pair (C.pairOf i j ne)))) =
        some (derivedKey D prss cache0 (.pair (C.pairOf i j ne)))) := by
  constructor
  · intro T visible
    have known : KnownTo D.1 T := not_not.mp visible
    obtain ⟨key, hk⟩ := cached.1 T known
    simpa only [derivedKey, hk, Option.getD_some] using grow hk
  · intro j ne visible
    have corrupt : j ∈ D.1 := by
      by_contra hj
      apply visible
      unfold Hidden Committee.pairOf
      split_ifs <;> exact ⟨by assumption, by assumption⟩
    obtain ⟨key, hk⟩ := cached.2 i j honest corrupt ne
    simpa only [derivedKey, hk, Option.getD_some] using grow hk

/-- A populated field row replays at every extension of the installed cache. -/
theorem fieldDraw_row_grows (keys derived : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E)
    (h : HashCache C) (c c' : HiddenCache C)
    (installed : treeSimCheckPrssCache K D keys label idx count vals c ≤ c')
    (name : KeyName C) (visible : ¬ Hidden D name → h (.streamKey (keys name)) = some (derived name)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name (keys name) label idx count) (LocalSpec C)))).run
        (h, c') = pure (treeSimCheckPrssRow prims K D derived label idx count vals name, (h, c')) := by
  by_cases hidden : Hidden D name
  · simp only [treeSimCheckPrssRow, if_pos hidden]
    exact treeSimCheck_elementDraw_cached prims K D name (keys name) hidden label idx count
      (vals name) h c' (fun g => installed (treeSimCheckPrssCache_at K D keys label idx count vals c name hidden g))
  · simp only [treeSimCheckPrssRow, if_neg hidden]
    apply treeSim_elementDraw_ready prims K D name (keys name) label idx count _ h c'
    simp only [TreeSimStreamReady, if_neg hidden]
    exact ⟨derived name, visible hidden, fun _ _ => rfl⟩

/-- Honest PRSS field draws need only the checkpoint keys actually used by their streams. -/
theorem prssDraw_rows_used (prss : C.Party → PrssKeys C) (cache0 h : HashCache C)
    (ctx : Context C) (honest : ctx.self ∉ D.1)
    (terms : ∀ T, ctx.self ∈ C.holders T → ctx.prss.term T = streamKey D prss (.term T))
    (pairs : ∀ j (hj : j ≠ ctx.self),
      ctx.prss.pair j = streamKey D prss (.pair (C.pairOf ctx.self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (grow : cache0 ≤ h)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E) (c c' : HiddenCache C)
    (installed : treeSimCheckPrssCache K D (streamKey D prss) label idx count vals c ≤ c') :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run (h, c') =
      pure (treeSimCheckPrssRows prims K D (derivedKey D prss cache0) label idx count vals ctx.self, (h, c')) := by
  have visible := used_visible_keys D prss cache0 h cached grow ctx.self honest
  let r := fun T => treeSimCheckPrssRow prims K D (derivedKey D prss cache0) label idx count vals (.term T)
  let z := fun j => if hj : j = ctx.self then (fun _ => 0) else
    treeSimCheckPrssRow prims K D (derivedKey D prss cache0) label idx count vals
      (.pair (C.pairOf ctx.self j (Ne.symm hj)))
  have he := treeSim_prssDraw_replay prims D ctx (elementCodec K) label idx count r z (h, c')
  have ht T (hT : ctx.self ∈ C.holders T) : (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw (.term T) (ctx.prss.term T) label idx count) (LocalSpec C)))).run
        (h, c') = pure (r T, (h, c')) := by
    rw [terms T hT]
    exact fieldDraw_row_grows prims K D _ _ label idx count vals h c c' installed _ (visible.1 T)
  have hp j (hj : j ≠ ctx.self) : (simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) label idx count) (LocalSpec C)))).run
        (h, c') = pure (z j, (h, c')) := by
    rw [pairs j hj]
    simp only [z, dif_neg hj]
    exact fieldDraw_row_grows prims K D _ _ label idx count vals h c c' installed _
      (visible.2 j (Ne.symm hj))
  rw [he ht hp]
  congr 3
  funext j
  by_cases hj : j = ctx.self <;> simp [z, hj]

/-- Hidden bit rows use the sampled table; visible rows use their cached AES key. -/
def treeCheckBitRow (derived : KeyName C → HashOutput) (label idx count : ℕ)
    (vals : KeyName C → Fin count → Bit) (name : KeyName C) : ℕ → Bit :=
  if Hidden D name then fun g => if hg : g < count then vals name ⟨g, hg⟩ else 0
  else fun g => ((List.range count).map fun k =>
    prims.aes.eval (truncateHash (derived name)) (label, idx, k)).getD g 0

def treeCheckBitRows (derived : KeyName C → HashOutput) (label idx count : ℕ)
    (vals : KeyName C → Fin count → Bit) (i : C.Party) : PrssOutput C Bit :=
  (fun T => if i ∈ C.holders T then treeCheckBitRow prims D derived label idx count vals (.term T)
      else fun _ => 0,
    fun j => if hj : j = i then fun _ => 0 else
      treeCheckBitRow prims D derived label idx count vals (.pair (C.pairOf i j (Ne.symm hj))))

private theorem bitPad_list (count : ℕ) (vals : Fin count → Bit) :
    (fun g => ((List.range count).map (fun k => if hk : k < count then vals ⟨k, hk⟩ else 0)).getD g 0) =
      (fun g => if hg : g < count then vals ⟨g, hg⟩ else 0) := by
  funext g
  by_cases hg : g < count <;>
    simp [List.getD_eq_getElem?_getD, hg]

/-- Bit draws retain the complete current caches, including unrelated later cells. -/
theorem bitDraw_row_grows (keys derived : KeyName C → HashOutput)
    (label idx count : ℕ) (vals : KeyName C → Fin count → Bit)
    (h : HashCache C) (c c' : HiddenCache C)
    (installed : bitCache D keys label idx count vals c ≤ c')
    (name : KeyName C) (visible : ¬ Hidden D name → h (.streamKey (keys name)) = some (derived name)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name (keys name) label idx count) (LocalSpec C)))).run
        (h, c') = pure (treeCheckBitRow prims D derived label idx count vals name, (h, c')) := by
  by_cases hidden : Hidden D name
  · simp only [treeCheckBitRow, if_pos hidden]
    have ready : TreeSimStreamReady prims D name (keys name) label idx count
        (fun g => if hg : g < count then vals name ⟨g, hg⟩ else 0) h c' := by
      simp only [TreeSimStreamReady, if_pos hidden]
      intro g hg
      simp only [dif_pos hg]
      exact installed (bitCache_at D keys label idx count vals c name hidden ⟨g, hg⟩)
    rw [treeSim_prgBits_ready prims D _ _ _ _ _ _ h c' ready, bitPad_list]
  · simp only [treeCheckBitRow, if_neg hidden]
    apply treeSim_prgBits_ready prims D name (keys name) label idx count _ h c'
    simp only [TreeSimStreamReady, if_neg hidden]
    exact ⟨derived name, visible hidden, fun _ _ => rfl⟩

/-- Honest bit PRSS replays the installed rows using only its checkpoint keys. -/
theorem prssBits_rows_used (prss : C.Party → PrssKeys C) (cache0 h : HashCache C)
    (ctx : Context C) (honest : ctx.self ∉ D.1)
    (terms : ∀ T, ctx.self ∈ C.holders T → ctx.prss.term T = streamKey D prss (.term T))
    (pairs : ∀ j (hj : j ≠ ctx.self),
      ctx.prss.pair j = streamKey D prss (.pair (C.pairOf ctx.self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (grow : cache0 ≤ h)
    (label idx count : ℕ) (vals : KeyName C → Fin count → Bit) (c c' : HiddenCache C)
    (installed : bitCache D (streamKey D prss) label idx count vals c ≤ c') :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) label idx count) (LocalSpec C)))).run (h, c') =
      pure (treeCheckBitRows prims D (derivedKey D prss cache0) label idx count vals ctx.self, (h, c')) := by
  have visible := used_visible_keys D prss cache0 h cached grow ctx.self honest
  let r := fun T => treeCheckBitRow prims D (derivedKey D prss cache0) label idx count vals (.term T)
  let z := fun j => if hj : j = ctx.self then (fun _ => 0) else
    treeCheckBitRow prims D (derivedKey D prss cache0) label idx count vals
      (.pair (C.pairOf ctx.self j (Ne.symm hj)))
  have he := treeSim_prssDraw_replay prims D ctx (bitCodec (E := E)) label idx count r z (h, c')
  have ht T (hT : ctx.self ∈ C.holders T) : (simulateQ (streamWorld prims D)
      (free (liftComp ((bitCodec (E := E)).draw (.term T) (ctx.prss.term T) label idx count) (LocalSpec C)))).run
        (h, c') = pure (r T, (h, c')) := by
    rw [terms T hT]
    exact bitDraw_row_grows prims D _ _ label idx count vals h c c' installed _ (visible.1 T)
  have hp j (hj : j ≠ ctx.self) : (simulateQ (streamWorld prims D)
      (free (liftComp ((bitCodec (E := E)).draw (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) label idx count) (LocalSpec C)))).run
        (h, c') = pure (z j, (h, c')) := by
    rw [pairs j hj]
    simp only [z, dif_neg hj]
    exact bitDraw_row_grows prims D _ _ label idx count vals h c c' installed _
      (visible.2 j (Ne.symm hj))
  rw [he ht hp]
  congr 3
  funext j
  by_cases hj : j = ctx.self <;> simp [z, hj]

/-- Bit rows agree everywhere with `frandShare`, including their zero-padded tails. -/
theorem bitRows_frandShare (prss : C.Party → PrssKeys C) (cache0 : HashCache C)
    (label idx count : ℕ) (vals : KeyName C → Fin count → Bit)
    (i : C.Party) (honest : i ∉ D.1) :
    treeCheckBitRows prims D (derivedKey D prss cache0) label idx count vals i =
      frandShare D count (knownRows D (bitRow prims D prss cache0 label idx count)).1
        (knownRows D (bitRow prims D prss cache0 label idx count)).2
        (termTable vals) (pairTable vals) i := by
  apply Prod.ext
  · funext T g
    by_cases held : i ∈ C.holders T
    · by_cases known : KnownTo D.1 T <;>
        simp [treeCheckBitRows, treeCheckBitRow, Hidden, frandShare, knownRows,
          held, known, termTable, bitRow, derivedKey]
    · simp [treeCheckBitRows, frandShare, held]
  · funext j g
    by_cases same : i = j
    · subst j
      simp [treeCheckBitRows, frandShare]
    · by_cases corrupt : j ∈ D.1
      · have visible := pair_visible D i j same corrupt
        simp [treeCheckBitRows, treeCheckBitRow, frandShare, knownRows,
          same, Ne.symm same, corrupt, visible, bitRow, derivedKey]
      · have hidden : Hidden D (.pair (C.pairOf i j same)) := by
          unfold Hidden Committee.pairOf
          split_ifs <;> exact ⟨by assumption, by assumption⟩
        simp [treeCheckBitRows, treeCheckBitRow, frandShare, knownRows,
          same, Ne.symm same, corrupt, hidden, pairTable]

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.realRun_presample_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_presample_fields

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.realRun_presample_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_presample_bits

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.futureEmpty_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms futureEmpty_block

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.futureEmpty_bitBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms futureEmpty_bitBlock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.prssDraw_rows_used' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prssDraw_rows_used

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.prssBits_rows_used' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prssBits_rows_used

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks.bitRows_frandShare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bitRows_frandShare

end ThresholdLeanXmssSecurity.TreeCheckGadgetBlocks
