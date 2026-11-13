import ThresholdLeanXmssSecurity.Proof.SigningJointEager
import ThresholdLeanXmssSecurity.Proof.TreeSim

/-! # The real tree builds in the order of the compiler builds

- `realBottomBuild` is the real bottom ceremony in the order of `sourceBottomTreeX`.
  `realBottom_eq` states that it is the bottom tree of the dealer.
- `realTopBuild` is the real top ceremony in the order of `deferredTopTree`. `realTop_eq` states
  that the top ceremony of the dealer never fails and is this build.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningCompilerO1RealBuild

open SigningSecurityProof

variable {C : Committee}

/-- One row of the real first run. It reads the three PRF values and then walks the chain three
times from the start. -/
def realRow (P : PublicParameter) (seeds : C.Term → HashOutput) (e : KeyIndex) (l : ChainIndex) :
    OracleComp (WorldSpec C) (Digest × Digest × Digest) := do
  let v₀ ← liftFree (prfValue seeds (.chain bottomLayer e l (digit 0)))
  let v₁ ← liftFree (prfValue seeds (.chain bottomLayer e l (digit 1)))
  let v₂ ← liftFree (prfValue seeds (.chain bottomLayer e l (digit 2)))
  let y₁ ← liftFree (tweakable (Concrete.chainWalk P bottomLayer e l 0 1 v₀))
  let y₂ ← liftFree (tweakable (Concrete.chainWalk P bottomLayer e l 0 2 v₀))
  let y₃ ← liftFree (tweakable (Concrete.chainWalk P bottomLayer e l 0 3 v₀))
  pure (y₁ ^^^ v₁, y₂ ^^^ v₂, y₃)

/-- One commitment of the real first run. -/
def realCommitment (P : PublicParameter) (seeds : C.Term → HashOutput) (e : KeyIndex) :
    OracleComp (WorldSpec C) Digest := do
  let ρ ← liftFree (prfValue seeds (.randomizer bottomLayer e))
  truncateHash <$> liftFree (tweakable (Concrete.oracleHash (commitmentInput P e ρ)))

/-- One chain value of the real second run. -/
def realTopValue (P : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight))
    (l : ChainIndex) (p : Digit) : OracleComp (WorldSpec C) Digest := do
  let v₀ ← liftFree (prfValue seeds (.chain topLayer (topKey b) l (digit 0)))
  liftFree (tweakable (Concrete.chainWalk P topLayer (topKey b) l 0 p.val v₀))

/-- The real bottom ceremony of the dealer in the order of `sourceBottomTreeX`. The `cpk` default
is the first commitment, as `ceremonyOutput` gives it. The real ceremony has no branch for a second
decode that differs from the codeword of the search. -/
def realBottomBuild (P : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : OracleComp (WorldSpec C) (Option BottomTree) := do
  let indices := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let rows ← indices.mapM fun el => realRow P seeds el.1 el.2
  let commitments ← (List.finRange (2 ^ layerHeight)).mapM fun k =>
    realCommitment P seeds (bottomKey b k)
  let ρ ← liftFree (prfValue seeds (.randomizer topLayer (topKey b)))
  let cpk := fun e l => rows.getD (indices.idxOf (e, l)) (commitments.getD 0 0, 0, 0)
  let commitment := fun (e : KeyIndex) => commitments.getD (e.val % 2 ^ layerHeight) 0
  let root ← liftFree (tweakable
    (merkleNode P bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val))
  let message := bytesLE 16 root
  let base ← liftFree (tweakable
    (truncateHash <$> Concrete.oracleHash (randomizerInput P topLayer (topKey b) ρ message)))
  let some (randomness, encoding) ← liftFree (tweakable
    (grind P topLayer (topKey b) message base randomizerAttemptLimit 0)) | pure none
  let values ← Concrete.sequenceFin fun l => realTopValue P seeds b l (encoding l)
  let path ← liftFree (tweakable (merklePath P topLayer top.chainEnd (topKey b)))
  let digest ← liftFree (tweakable
    (Concrete.messageDigest P topLayer (topKey b) message randomness))
  let some checked := Codeword.decode digest | pure none
  let ends ← Concrete.sequenceFin fun l => liftFree (tweakable
    (Concrete.recoverChain P topLayer (topKey b) l (checked l) (values l)))
  let leaf ← liftFree (tweakable (Concrete.leafHash P topLayer (topKey b) ends))
  let topRoot ← liftFree (tweakable
    (Concrete.treeFold P topLayer (topKey b) path layerHeight leaf))
  if topRoot ≠ top.root then pure none else
    pure (some ⟨cpk, commitment, root, ⟨randomness, values, path⟩⟩)

/-- One chain end of the real top ceremony. -/
def realTopEnd (P : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight))
    (l : ChainIndex) : OracleComp (WorldSpec C) Digest := do
  let v₀ ← liftFree (prfValue seeds (.chain topLayer (topKey b) l (digit 0)))
  liftFree (tweakable (Concrete.chainWalk P topLayer (topKey b) l 0 3 v₀))

/-- The real top ceremony of the dealer in the order of `deferredTopTree`. -/
def realTopBuild (P : PublicParameter) (seeds : C.Term → HashOutput) :
    OracleComp (WorldSpec C) TopTree := do
  let indices := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange numChains).map fun l => (b, l)
  let ends ← indices.mapM fun bl => realTopEnd P seeds bl.1 bl.2
  let keys := indices.map fun bl => (topKey bl.1, bl.2)
  let chainEnd := fun e l => ends.getD (keys.idxOf (e, l)) 0
  let root ← liftFree (tweakable (merkleNode P topLayer chainEnd layerHeight 0))
  pure ⟨chainEnd, root⟩

/-- Two continuations of a `mapM` give the same computation when they agree on each list of the
length of the input list. -/
theorem mapM_bind_congr_length {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ : Type}
    (f : α → m β) : ∀ (l : List α) (k k' : List β → m γ),
      (∀ rs : List β, rs.length = l.length → k rs = k' rs) → l.mapM f >>= k = l.mapM f >>= k'
  | [], k, k', h => by simp [h [] rfl]
  | a :: l, k, k', h => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    refine bind_congr fun x => ?_
    exact mapM_bind_congr_length f l _ _ fun rs hrs => h (x :: rs) (by simp [hrs])

/-- The verification of a layer signature gives no root when the digest is no codeword. -/
theorem layerRoot_unfold {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]
    (P : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) :
    Concrete.layerRoot (m := m) P lay key message part = (do
      let digest ← Concrete.messageDigest P lay key message part.randomness
      match Codeword.decode digest with
      | none => pure none
      | some encoding => do
        let ends ← Concrete.sequenceFin fun l =>
          Concrete.recoverChain P lay key l (encoding l) (part.chainValues l)
        let leaf ← Concrete.leafHash P lay key ends
        let root ← Concrete.treeFold P lay key part.path layerHeight leaf
        pure (some root)) := by
  simp only [Concrete.layerRoot, Concrete.otsLeaf, bind_assoc]
  refine bind_congr fun digest => ?_
  cases Codeword.decode digest <;> simp

/-- The first digest of an output read from a list of digests is the entry of the list. -/
theorem digestAt_getD_map (L : List Digest) (i : ℕ) :
    digestAt ((L.map bitsOfDigest).getD i []) 0 = L.getD i 0 := by
  rcases Nat.lt_or_ge i L.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
    simp [digestAt_bits]
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ h]
    simp [digestAt, digestOfBits]

/-- The output bits of a chain row. -/
def rowBits (y : Digest × Digest × Digest) : List Bit :=
  bitsOfDigest y.1 ++ bitsOfDigest y.2.1 ++ bitsOfDigest y.2.2

/-- The `cpk` entry that `ceremonyOutput` reads from the outputs of the first run. A key outside the
rows reads the first commitment. -/
theorem rowBits_read {κ : Type} [BEq κ] [LawfulBEq κ] (rows : List (Digest × Digest × Digest)) (keys : List κ)
    (hrows : rows.length = keys.length) (commitments : List Digest) (hcommitments : commitments ≠ [])
    (rest : List (List Bit)) (key : κ) :
    (digestAt ((rows.map rowBits ++ commitments.map bitsOfDigest ++ rest).getD (keys.idxOf key) []) 0,
      digestAt ((rows.map rowBits ++ commitments.map bitsOfDigest ++ rest).getD (keys.idxOf key) []) 1,
      digestAt ((rows.map rowBits ++ commitments.map bitsOfDigest ++ rest).getD (keys.idxOf key) []) 2) =
      rows.getD (keys.idxOf key) (commitments.getD 0 0, 0, 0) := by
  have hle : keys.idxOf key ≤ rows.length := hrows ▸ List.idxOf_le_length
  rcases Nat.lt_or_ge (keys.idxOf key) rows.length with h | h
  · rw [List.append_assoc, List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ h,
      List.getD_eq_getElem _ _ (by simpa using h)]
    simp [rowBits, List.append_assoc, digestAt_zero, digestAt_succ, digestAt_bits]
  · obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hcommitments
    have hi : keys.idxOf key = rows.length := le_antisymm hle h
    rw [hi, List.getD_eq_default _ _ le_rfl, List.append_assoc,
      List.getD_append_right _ _ _ _ (by simp)]
    have hnil : ∀ k, digestAt [] k = 0 := fun k => by simp [digestAt, digestOfBits]
    have h1 : digestAt (bitsOfDigest c) 1 = 0 := by
      rw [← List.append_nil (bitsOfDigest c), digestAt_succ, hnil]
    have h2 : digestAt (bitsOfDigest c) 2 = 0 := by
      rw [← List.append_nil (bitsOfDigest c), digestAt_succ, hnil]
    simp [digestAt_bits, h1, h2]

/-- The commitment that `ceremonyOutput` reads from the outputs of the first run. -/
theorem commitment_read (rows : List (List Bit)) (n : ℕ) (hn : rows.length = n)
    (commitments : List Digest) (rest : List (List Bit)) (j : ℕ) (hj : j < commitments.length) :
    digestAt ((rows ++ commitments.map bitsOfDigest ++ rest).getD (n + j) []) 0 =
      commitments.getD j 0 := by
  subst hn
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using hj), digestAt_getD_map]

/-- The randomizer value that `ceremonyOutput` reads from the outputs of the first run. -/
theorem randomizer_read (rows : List (List Bit)) (n : ℕ) (hn : rows.length = n)
    (commitments : List Digest) (m : ℕ) (hm : commitments.length = m) (ρ : Digest) :
    digestAt ((rows ++ commitments.map bitsOfDigest ++ [bitsOfDigest ρ]).getD (n + m) []) 0 = ρ := by
  subst hn hm
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [digestAt_bits]

/-- A `mapM` of mapped computations is the map of the `mapM`. -/
theorem mapM_fmap {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ : Type} (g : β → γ)
    (f : α → m β) : ∀ l : List α, l.mapM (fun a => g <$> f a) = List.map g <$> l.mapM f
  | [] => by simp
  | a :: l => by simp [List.mapM_cons, mapM_fmap g f l]

/-- The top ceremony of the dealer never fails, and it is the real build in the order of the
compiler build. -/
theorem realTop_eq (x : Keys3 C) :
    referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      (fun top => some (.top top)) <$> realTopBuild x.1 x.2.1 := by
  have htop : topJobs = ((List.finRange (2 ^ layerHeight)).flatMap fun b =>
      (List.finRange numChains).map fun l => (b, l)).map
        fun bl => (⟨.chainEnd (topKey bl.1) bl.2, [.chain topLayer (topKey bl.1) bl.2 (digit 0)]⟩ : Job) := by
    simp only [topJobs, List.map_flatMap, List.map_map]
    rfl
  have hjob : ∀ bl : Fin (2 ^ layerHeight) × ChainIndex,
      referenceJob (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p)) x.1
        (⟨.chainEnd (topKey bl.1) bl.2, [.chain topLayer (topKey bl.1) bl.2 (digit 0)]⟩ : Job) =
        bitsOfDigest <$> realTopEnd x.1 x.2.1 bl.1 bl.2 := by
    intro bl
    simp [referenceJob, realTopEnd]
  simp only [referenceTree, ceremonyOutput, realTopBuild]
  rw [htop, List.mapM_map]
  simp only [Function.comp_def, hjob, mapM_fmap, map_bind, bind_map_left, map_pure,
    digestAt_getD_map, List.map_flatMap, List.map_map]

/-- The bottom tree of the dealer is the real build in the order of the compiler build. -/
theorem realBottom_eq (x : Keys3 C) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    (SigningJointEagerProof.dealtOf x top).bottom b = realBottomBuild x.1 x.2.1 top b := by
  have hrow : ∀ el : KeyIndex × ChainIndex,
      referenceJob (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p)) x.1
        (⟨.chainRow el.1 el.2, [.chain bottomLayer el.1 el.2 (digit 0),
          .chain bottomLayer el.1 el.2 (digit 1), .chain bottomLayer el.1 el.2 (digit 2)]⟩ : Job) =
        rowBits <$> realRow x.1 x.2.1 el.1 el.2 := by
    intro el
    simp [referenceJob, realRow, rowBits]
  have hcommitment : ∀ k : Fin (2 ^ layerHeight),
      referenceJob (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p)) x.1
        (⟨.commitment (bottomKey b k), [.randomizer bottomLayer (bottomKey b k)]⟩ : Job) =
        bitsOfDigest <$> realCommitment x.1 x.2.1 (bottomKey b k) := by
    intro k
    simp [referenceJob, realCommitment, Function.comp_def]
  have hvalue : ∀ (encoding : Encoding) (l : ChainIndex),
      referenceJob (fun oa => liftFree (tweakable oa)) (fun p => liftFree (prfValue x.2.1 p)) x.1
        (⟨.chainValue (topKey b) l (encoding l), [.chain topLayer (topKey b) l (digit 0)]⟩ : Job) =
        bitsOfDigest <$> realTopValue x.1 x.2.1 b l (encoding l) := by
    intro encoding l
    simp [referenceJob, realTopValue]
  simp only [SigningJointEagerProof.dealtOf, dealtWith, referenceTree, ceremonyOutput,
    realBottomBuild]
  rw [bottomJobs_eq]
  simp only [List.mapM_append, List.mapM_map, Function.comp_def, hrow, hcommitment, signJobs,
    hvalue, mapM_fmap, List.mapM_cons, List.mapM_nil, ← treeSim_sequenceFin_mapM]
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, map_bind, bind_assoc, bind_map_left,
    pure_bind, map_pure, layerRoot_unfold, tweakable_bind, φ_bind]
  refine mapM_bind_congr_length _ _ _ _ fun rows hrows => ?_
  refine bind_congr fun commitments => ?_
  refine bind_congr fun ρ => ?_
  have hcpk := fun e l => rowBits_read rows (bottomKeys b) hrows (List.ofFn commitments)
    (by simp) [bitsOfDigest ρ] (e, l)
  have hcpk2 : ∀ e l, _ := fun e l => congrArg (fun y => y.2.2) (hcpk e l)
  dsimp only at hcpk2
  have hlength : (rows.map rowBits).length = (bottomKeys b).length := by simp [hrows]
  have hcommitment := fun e : KeyIndex => commitment_read (rows.map rowBits) _ hlength
    (List.ofFn commitments) [bitsOfDigest ρ] (e.val % 2 ^ layerHeight)
    (by simpa using Nat.mod_lt _ (Nat.two_pow_pos layerHeight))
  have hρ := randomizer_read (rows.map rowBits) _ hlength (List.ofFn commitments) (2 ^ layerHeight)
    (by simp) ρ
  simp only [List.getD_cons_zero, hcpk]
  simp only [hcpk2, hcommitment, hρ]
  refine bind_congr fun root => bind_congr fun base => bind_congr fun found => ?_
  rcases found with _ | ⟨randomness, encoding⟩
  · simp
  simp only [map_bind]
  refine bind_congr fun values => bind_congr fun path => bind_congr fun digest => ?_
  have hvalues : ∀ l : ChainIndex,
      digestAt (((List.ofFn values).map bitsOfDigest).getD l.val []) 0 = values l := by
    intro l
    rw [digestAt_getD_map, List.getD_eq_getElem _ _ (by simp)]
    simp
  rcases Codeword.decode digest with _ | checked
  · simp [tweakable_pure, φ_pure]
  simp only [hvalues, tweakable_bind, tweakable_sequenceFin, tweakable_pure, φ_bind, φ_sequenceFin,
    φ_pure, bind_assoc, pure_bind]
  refine bind_congr fun ends => bind_congr fun leaf => bind_congr fun topRoot => ?_
  split_ifs <;> simp_all

/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.realBottom_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms realBottom_eq

/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.realTop_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms realTop_eq

/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.mapM_bind_congr_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms mapM_bind_congr_length
/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.layerRoot_unfold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms layerRoot_unfold
/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.digestAt_getD_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms digestAt_getD_map
/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.rowBits_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rowBits_read
/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.commitment_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms commitment_read
/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.randomizer_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms randomizer_read
/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1RealBuild.mapM_fmap' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms mapM_fmap

end SigningCompilerO1RealBuild
end ThresholdLeanXmssSecurity
