import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Cores
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutRun
import ThresholdLeanXmssSecurity.Proof.Pilot.Join

/-!
# The walk of a ceremony to its stop at a check

`CutWalk` states the ends and the stops on each path of a program on the counters. The walk goes
through `cutBatch` and `cutRun`, and `cutWalk_cutRun` gives the label and the counters at the stop
from the public job list. `runJobs_label` gives the label that one full batch adds. The section
`SetupCut` cuts the ceremony after its PRSS setup (`cutRun_eq`), and `executePhase_reach` follows each
honest operator to the end of that setup.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

attribute [local instance] inhabitedField

/-! ## The record of the head of a batch -/

section Record

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The run state after one reshare of `n` positions in `mode` at operator `i`. -/
def afterReply (mode : ReshareMode) (i : C.Party) (n : ℕ) (hs : RunState C) (z : Shares C Bit) : RunState C :=
  ⟨fun T => if i ∈ C.holders T then hs.history T ++
    ((List.range n).filter fun g => (filler K mode T g).isSome).map (z T)
    else hs.history T, hs.label + 1, hs.tag⟩

/-- One record step appends one tuple to the filled history. -/
theorem record_history (i : C.Party) (ts : List (Tuple C)) (τ : Tuple C) (L tg : ℕ) :
    afterReply K τ.mode i τ.count ⟨filledHistory K i ts, L, tg⟩ τ.z =
      ⟨filledHistory K i (ts ++ [τ]), L + 1, tg⟩ := by
  unfold afterReply
  congr 1
  funext T
  by_cases h : i ∈ C.holders T <;> simp [filledHistory, h]

/-- The draw of the randomness and the reshare of one call of `F_mult` end in `afterReply`. It is
`draw_record`. -/
theorem draw_record {ι : Type} {G : OracleSpec ι} (ctx : Context C) (mode : ReshareMode) (v : ℕ → Bit) (n : ℕ)
    (hs : RunState C) :
    ((do let rnd ← prssRandomness ctx bitCodec 0 n
         reshareWith K ctx mode rnd v n : RunM C E G _).run hs) =
      ((do let rnd ← prssRandomness ctx bitCodec 0 n
           reshareWith K ctx mode rnd v n : RunM C E G _).run hs) >>= fun p =>
        pure (p.1, afterReply K mode ctx.self n hs p.1) := by
  cases mode <;>
    simp only [prssRandomness, freshLabel, StateT.run_bind, StateT.run_modifyGet,
      StateT.run_lift, pure_bind, bind_assoc]
  all_goals
    apply bind_congr
    intro r
    apply bind_congr
    intro Z
  · simp only [reshareWith, reshare, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    apply bind_congr
    intro inbox
    simp [record, StateT.run_modify, StateT.run_pure, afterReply, bitCodec,
      Function.comp_def]
    simp only [List.map_eq_flatMap]
  · simp only [reshareWith, reshareCollector, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    apply bind_congr
    intro inbox
    apply bind_congr
    intro forward
    simp [record, StateT.run_modify, StateT.run_pure, afterReply, bitCodec,
      Function.comp_def]
    simp only [List.map_eq_flatMap]

end Record

/-! ## Paths of a run -/

section Paths

variable {C : Committee} {E : Type}

theorem mem_support_run_bind {α β : Type} (p : RunM C E RealSpec α) (q : α → RunM C E RealSpec β)
    (st : RunState C) (r : β × RunState C) (h : some r ∈ support ((p >>= q).run st).run) :
    ∃ a, some a ∈ support (p.run st).run ∧ some r ∈ support ((q a.1).run a.2).run := by
  rw [StateT.run_bind] at h
  rcases mem_support_optionT_bind _ _ _ h with h | ⟨a, ha, hr⟩
  · cases h
  · exact ⟨a, ha, hr⟩

theorem mem_support_run_pure {α : Type} (a : α) (st : RunState C) (r : α × RunState C)
    (h : some r ∈ support ((pure a : RunM C E RealSpec α).run st).run) : r = (a, st) := by
  simpa using h

theorem mem_support_of_eq_map {γ : Type} (x : PartyM C E RealSpec γ) (g : γ → γ)
    (hx : x = x >>= fun p => pure (g p)) (r : γ) (h : some r ∈ support x.run) : ∃ p, r = g p := by
  rw [hx] at h
  rcases mem_support_optionT_bind _ _ _ h with h | ⟨a, -, hr⟩
  · cases h
  · exact ⟨a, by simpa using hr⟩

end Paths

/-! ## The head of a batch -/

section Head

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

theorem runJobsHead_eq {ι : Type} {G : OracleSpec ι} (bb : RunBuildingBlocks C E G) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    runJobsHead K bb jobs inputs =
      (List.range (depth jobs)).foldlM (layerBody K bb jobs) (inputs, []) >>= fun p =>
        bb.rerand (outputShares K jobs p.1) (outputsOf jobs).length >>= fun v' =>
          pure (p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩], v',
            (outputsOf jobs).length, jobs.map (·.outputs.length)) :=
  rfl

/-- Each path of one call of the real `F_mult` ends in `afterReply`. -/
theorem mult_support (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit) (n : ℕ) (st : RunState C)
    (a : Shares C Bit × RunState C)
    (ha : some a ∈ support (((realRunBuildingBlocks (G := RealSpec) K ctx mode).mult x y n).run st).run) :
    a.2 = afterReply K mode ctx.self n st a.1 := by
  have hd := draw_record (G := RealSpec) K ctx mode (mulRep K ctx x y) n st
  change ((realRunBuildingBlocks K ctx mode).mult x y n).run st = _ at hd
  obtain ⟨p, rfl⟩ := mem_support_of_eq_map _ _ hd a ha
  rfl

/-- Each path of one call of the real `Rerand` ends in `afterReply` in peer mode. -/
theorem rerand_support (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (n : ℕ) (st : RunState C)
    (a : Shares C Bit × RunState C)
    (ha : some a ∈ support (((realRunBuildingBlocks (G := RealSpec) K ctx mode).rerand v n).run st).run) :
    a.2 = afterReply K .peer ctx.self n st a.1 := by
  have hd := draw_record (G := RealSpec) K ctx .peer (ownerSum K ctx v) n st
  change ((realRunBuildingBlocks K ctx mode).rerand v n).run st = _ at hd
  obtain ⟨p, rfl⟩ := mem_support_of_eq_map _ _ hd a ha
  rfl

/-- The layers keep the run state at the filled history of the tuples so far, with one label for each
tuple. -/
theorem layers_support (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit) :
    ∀ (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (L tg : ℕ) r,
      some r ∈ support (((ls.foldlM (layerBody K (realRunBuildingBlocks (G := RealSpec) K ctx mode) jobs) p).run
        ⟨filledHistory K ctx.self p.2, L + p.2.length, tg⟩).run) →
      r.2 = ⟨filledHistory K ctx.self r.1.2, L + r.1.2.length, tg⟩ ∧
        r.1.2.map (·.count) = p.2.map (·.count) ++ ls.map fun l => (gatesAt jobs l).length
  | [], p, L, tg, r, hr => by
    rw [List.foldlM_nil] at hr
    obtain rfl := mem_support_run_pure _ _ _ hr
    simp
  | l :: ls, p, L, tg, r, hr => by
    rw [List.foldlM_cons] at hr
    obtain ⟨a, ha, hr⟩ := mem_support_run_bind _ _ _ _ hr
    unfold layerBody at ha
    obtain ⟨b, hb, ha⟩ := mem_support_run_bind _ _ _ _ ha
    obtain rfl := mem_support_run_pure _ _ _ ha
    have hs := mult_support K ctx mode _ _ _ _ b hb
    have hrec := record_history K ctx.self p.2
      ⟨layerX K jobs l p.1, layerY K jobs l p.1, b.1, (gatesAt jobs l).length, mode⟩ (L + p.2.length) tg
    simp only at hrec
    rw [hrec] at hs
    have hlen : L + p.2.length + 1 = L + (p.2 ++ [(⟨layerX K jobs l p.1, layerY K jobs l p.1, b.1,
        (gatesAt jobs l).length, mode⟩ : Tuple C)]).length := by simp [Nat.add_assoc]
    rw [hlen] at hs
    rw [hs] at hr
    obtain ⟨h1, h2⟩ := layers_support ctx mode jobs ls _ L tg r hr
    refine ⟨h1, ?_⟩
    rw [h2]
    simp

/-- On each path of the head of a real batch from the label `L` and the tag `tg`, the run state at the
end is the filled history of the tuples of the head, the label `L` plus the number of the tuples, and
the tag `tg`. The counts of the tuples are `headCounts`. -/
theorem runJobsHead_support (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) (L tg : ℕ) r
    (hr : some r ∈ support ((runJobsHead K (realRunBuildingBlocks (G := RealSpec) K ctx mode) jobs inputs).run
      ⟨fun _ => [], L, tg⟩).run) :
    r.2 = ⟨filledHistory K ctx.self r.1.1, L + r.1.1.length, tg⟩ ∧ r.1.1.map (·.count) = headCounts jobs := by
  have he : (⟨fun _ => [], L, tg⟩ : RunState C) =
      ⟨filledHistory K ctx.self ([] : List (Tuple C)), L + ([] : List (Tuple C)).length, tg⟩ := by
    congr 1
    funext T
    simp [filledHistory]
  rw [he, runJobsHead_eq] at hr
  obtain ⟨p, hp, hr⟩ := mem_support_run_bind _ _ _ _ hr
  obtain ⟨hps, hpc⟩ := layers_support K ctx mode jobs _ _ L tg p hp
  rw [hps] at hr
  obtain ⟨v, hv, hr⟩ := mem_support_run_bind _ _ _ _ hr
  obtain rfl := mem_support_run_pure _ _ _ hr
  have hs := rerand_support K ctx mode _ _ _ v hv
  rw [record_history K ctx.self p.1.2 ⟨outputShares K jobs p.1.1, one K, v.1, (outputsOf jobs).length, .peer⟩] at hs
  refine ⟨?_, ?_⟩
  · rw [hs]
    simp [Nat.add_assoc]
  · simp only [List.map_append, hpc, headCounts]
    simp

end Head

/-! ## The labels of a full batch -/

section Labels

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

omit [Field E] [Algebra Bit E] in
/-- Each path of a program that `Moves` with `R` ends in a state with `R`. -/
theorem moves_support {R : RunState C → RunState C → Prop} {α : Type} {p : RunM C E RealSpec α}
    (hp : Moves R p) (st : RunState C) (r : α × RunState C) (hr : some r ∈ support (p.run st).run) :
    R st r.2 := by
  have h := hp st (fun x => if R st x.2 then pure x else failure) (fun x => pure x) fun a s hs => by
    simp only [hs, ↓reduceIte]
  rw [bind_pure] at h
  rw [← h] at hr
  rcases mem_support_optionT_bind _ _ _ hr with h | ⟨a, -, ha⟩
  · cases h
  · by_cases hR : R st a.2
    · simp only [hR, ↓reduceIte] at ha
      have : r = a := by simpa using ha
      exact this ▸ hR
    · simp [hR, OptionT.run_failure] at ha

omit [Field E] [Algebra Bit E] in
theorem moves_prssRandomness {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) :
    Moves (LabelAdds 1) (prssRandomness (G := RealSpec) ctx codec idx count) := by
  unfold prssRandomness
  exact moves_label_bind moves_freshLabel (fun _ => moves_label_bind (moves_lift labelAdds_zero _)
    (fun _ => moves_label_bind (moves_lift labelAdds_zero _) (fun _ => moves_pure labelAdds_zero _) rfl) rfl) rfl

/-- Each real building block of the check takes one label. -/
theorem oneLabelBlocks_real (ctx : Context C) : OneLabelBlocks (realCheckBuildingBlocks (G := RealSpec) K ctx) where
  coin n := moves_label_bind (moves_prssRandomness ctx _ 1 n) (fun _ => moves_coinWith K _ _ n) rfl
  extendMult _ := moves_label_bind (moves_prssRandomness ctx _ 0 _) (fun _ => moves_reshare K _ _ _ _ _) rfl
  randElements n := moves_prssRandomness ctx _ 1 n
  randBits n := moves_prssRandomness ctx bitCodec 2 n

/-- On each path of the real check, the label grows by `checkLabels` of the count. -/
theorem check_label (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) (r : Unit × RunState C)
    (hr : some r ∈ support ((check K ctx (realCheckBuildingBlocks (G := RealSpec) K ctx) tuples).run st).run) :
    r.2.label = st.label + checkLabels (tuples.map (·.count)).sum := by
  by_cases h : (tuples.map (·.count)).sum = 0
  · rw [check_run_zero K ctx tuples h] at hr
    have : r = ((), st) := by simpa using hr
    subst this
    simp [checkLabels, h]
  · have hB : BlocksAgree (0 : ℕ) (tuples.map (·.count)).sum (realCheckBuildingBlocks (G := RealSpec) K ctx)
        (realCheckBuildingBlocks K ctx) :=
      ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    have hm := (agree_check K ctx tuples hB (oneLabelBlocks_real K ctx) h).2
    have := moves_support hm st r hr
    unfold LabelAdds at this
    rw [this]
    simp [checkLabels, h]

/-- On each path of the full real run of a batch from the label `L`, the label at the end is `L` plus
`batchLabel`. -/
theorem runJobs_label (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) (L tg : ℕ) r
    (hr : some r ∈ support ((runJobs K (realRunBuildingBlocks (G := RealSpec) K ctx mode) jobs inputs).run
      ⟨fun _ => [], L, tg⟩).run) :
    r.2.label = L + batchLabel jobs := by
  rw [runJobs_eq_head] at hr
  obtain ⟨h, hh, hr⟩ := mem_support_run_bind _ _ _ _ hr
  obtain ⟨hs, hc⟩ := runJobsHead_support K ctx mode jobs inputs L tg h hh
  obtain ⟨c, hcr, hr⟩ := mem_support_run_bind _ _ _ _ hr
  have hcl := check_label K ctx _ _ c hcr
  obtain ⟨o, hor, hr⟩ := mem_support_run_bind _ _ _ _ hr
  obtain rfl := mem_support_run_pure _ _ _ hr
  rw [output_run] at hor
  rcases mem_support_optionT_bind _ _ _ hor with h' | ⟨a, -, ha⟩
  · cases h'
  · have : o = (a, c.2) := by simpa using ha
    subst this
    dsimp only
    rw [hcl, hs, hc]
    simp only [batchLabel, ← hc, List.length_map]
    omega

end Labels

/-! ## Paths of a program that stops at a check -/

section Walk

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {K : Constants C E}

/-- On each path of `x` from the counters `st`, an end with the value and the counters `r` has
`P st r`, and a stop at the start of a check `point` has `Q st point`. -/
def CutWalk {α : Type} (P : ℕ × ℕ → α × (ℕ × ℕ) → Prop) (Q : ℕ × ℕ → CheckPoint C → Prop) (x : CutM K α) :
    Prop :=
  ∀ st o, o ∈ support (x.run st).run.run →
    (∀ r, o = some (.inl r) → P st r) ∧ (∀ point rest, o = some (.inr (point, rest)) → Q st point)

theorem cutWalk_mono {α : Type} {P P' : ℕ × ℕ → α × (ℕ × ℕ) → Prop} {Q Q' : ℕ × ℕ → CheckPoint C → Prop}
    {x : CutM K α} (hx : CutWalk P Q x) (hP : ∀ st r, P st r → P' st r) (hQ : ∀ st point, Q st point → Q' st point) :
    CutWalk P' Q' x := fun st o ho =>
  ⟨fun r h => hP st r ((hx st o ho).1 r h), fun point rest h => hQ st point ((hx st o ho).2 point rest h)⟩

theorem cutWalk_bind {α β : Type} {P₁ : ℕ × ℕ → α × (ℕ × ℕ) → Prop} {Q₁ : ℕ × ℕ → CheckPoint C → Prop}
    {x : CutM K α} {f : α → CutM K β} {P₂ : α → ℕ × ℕ → β × (ℕ × ℕ) → Prop}
    {Q₂ : α → ℕ × ℕ → CheckPoint C → Prop} (hx : CutWalk P₁ Q₁ x) (hf : ∀ a, CutWalk (P₂ a) (Q₂ a) (f a)) :
    CutWalk (fun st r => ∃ a, P₁ st a ∧ P₂ a.1 a.2 r) (fun st point => Q₁ st point ∨ ∃ a, P₁ st a ∧ Q₂ a.1 a.2 point)
      (x >>= f) := by
  intro st o ho
  rw [StateT.run_bind, Paused.run_bind] at ho
  rcases mem_support_optionT_bind _ _ _ ho with rfl | ⟨a, ha, ho⟩
  · exact ⟨fun r h => (by cases h), fun point rest h => (by cases h)⟩
  rcases a with ⟨b, st'⟩ | ⟨point', rest'⟩
  · have hP := (hx st _ ha).1 (b, st') rfl
    have h := hf b st' o ho
    exact ⟨fun r hr => ⟨(b, st'), hP, h.1 r hr⟩, fun point rest hr => Or.inr ⟨(b, st'), hP, h.2 point rest hr⟩⟩
  · have hQ := (hx st _ ha).2 point' rest' rfl
    simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff] at ho
    subst ho
    refine ⟨fun r hr => (by cases hr), fun point rest hr => ?_⟩
    simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at hr
    exact Or.inl (hr.1 ▸ hQ)

theorem cutWalk_pure {α : Type} (a : α) (Q : ℕ × ℕ → CheckPoint C → Prop) :
    CutWalk (fun st r => r = (a, st)) Q (pure a : CutM K α) := by
  intro st o ho
  simp only [StateT.run_pure, Paused.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  refine ⟨fun r hr => ?_, fun point rest hr => by cases hr⟩
  simp only [Option.some.injEq, Sum.inl.injEq] at hr
  exact hr.symm

theorem cutWalk_get (Q : ℕ × ℕ → CheckPoint C → Prop) :
    CutWalk (fun st r => r = (st, st)) Q (get : CutM K (ℕ × ℕ)) := by
  intro st o ho
  simp only [StateT.run_get, Paused.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  refine ⟨fun r hr => ?_, fun point rest hr => by cases hr⟩
  simp only [Option.some.injEq, Sum.inl.injEq] at hr
  exact hr.symm

theorem cutWalk_lift {α : Type} (y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) (Q : ℕ × ℕ → CheckPoint C → Prop) :
    CutWalk (fun st r => some r ∈ support (y.run st).run) Q (CutM.lift (K := K) y) := by
  intro st o ho
  rw [CutM.lift_run] at ho
  simp only [Paused.lift, OptionT.run_map, support_map, Set.mem_image] at ho
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨fun r hr => ?_, fun point rest hr => ?_⟩
  · rcases o' with _ | o'
    · cases hr
    · simp only [Option.map_some, Option.some.injEq, Sum.inl.injEq] at hr
      exact hr ▸ ho'
  · rcases o' with _ | o' <;> cases hr

/-- A walk over a list of batches. Each batch `b` adds `f b` to the label and one to the tag, or it
stops with the tag `k` and `G b`. Then the walk over `l` adds the sum, or it stops in a batch `b` of
`l` with `G b` at the label of the batches before `b`. -/
theorem cutWalk_mapM {β γ : Type} (run : β → CutM K γ) (k : ℕ) (f : β → ℕ) (G : β → ℕ → CheckPoint C → Prop)
    (hrun : ∀ b, CutWalk (fun st r => r.2 = (st.1 + f b, st.2 + 1)) (fun st point => st.2 = k ∧ G b st.1 point)
      (run b)) :
    ∀ l : List β, CutWalk (fun st r => r.2 = (st.1 + (l.map f).sum, st.2 + l.length))
      (fun st point => ∃ pre b suf, l = pre ++ b :: suf ∧ st.2 + pre.length = k ∧
        G b (st.1 + (pre.map f).sum) point) (l.mapM run)
  | [] => cutWalk_mono (cutWalk_pure [] (fun _ _ => False)) (fun st r h => by simp [h]) fun _ _ h => h.elim
  | b :: l => by
    rw [List.mapM_cons]
    refine cutWalk_mono (cutWalk_bind (hrun b) fun x =>
      cutWalk_bind (cutWalk_mapM run k f G hrun l) fun xs => cutWalk_pure (x :: xs) (fun _ _ => False)) ?_ ?_
    · rintro st r ⟨a, ha, c, hc, rfl⟩
      rw [hc, ha]
      simp only [List.map_cons, List.sum_cons, List.length_cons, Prod.mk.injEq]
      constructor <;> ring
    · rintro st point (⟨hk, hG⟩ | ⟨a, ha, h⟩)
      · exact ⟨[], b, l, rfl, by simpa using hk, by simpa using hG⟩
      · rcases h with ⟨pre, b', suf, rfl, hk, hG⟩ | ⟨c, -, h⟩
        · rw [ha] at hk hG
          refine ⟨b :: pre, b', suf, rfl, ?_, ?_⟩
          · simp only [List.length_cons] at hk ⊢
            omega
          · simp only [List.map_cons, List.sum_cons] at hG ⊢
            rwa [Nat.add_assoc] at hG
        · exact h.elim

theorem cutWalk_pure_true {α : Type} (a : α) (Q : ℕ × ℕ → CheckPoint C → Prop) :
    CutWalk (fun _ _ => True) Q (pure a : CutM K α) :=
  cutWalk_mono (cutWalk_pure a Q) (fun _ _ _ => trivial) fun _ _ h => h

/-- A step with no stop that keeps the counters, then a walk with the stops `Q`. -/
theorem cutWalk_lift_bind {α β : Type} (y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) (f : α → CutM K β)
    (Q : ℕ × ℕ → CheckPoint C → Prop) (hy : ∀ st a, some a ∈ support (y.run st).run → a.2 = st)
    (hf : ∀ a, CutWalk (fun _ _ => True) Q (f a)) : CutWalk (fun _ _ => True) Q (CutM.lift y >>= f) := by
  refine cutWalk_mono (cutWalk_bind (cutWalk_lift y (fun _ _ => False)) hf) (fun _ _ _ => trivial) ?_
  rintro st point (h | ⟨a, ha, h⟩)
  · exact h.elim
  · rw [hy st a ha] at h
    exact h

/-- A walk run from the counters `st` and cut to its value stops only with `Q st`. -/
theorem cutWalk_run' {α : Type} {P : ℕ × ℕ → α × (ℕ × ℕ) → Prop} {Q : ℕ × ℕ → CheckPoint C → Prop}
    {x : CutM K α} (hx : CutWalk P Q x) (st : ℕ × ℕ) :
    ∀ o ∈ support (x.run' st).run.run, ∀ point rest, o = some (.inr (point, rest)) → Q st point := by
  intro o ho point rest h
  subst h
  rw [StateT.run'_eq, map_eq_bind_pure_comp, Paused.run_bind] at ho
  rcases mem_support_optionT_bind _ _ _ ho with h | ⟨a, ha, ho⟩
  · cases h
  rcases a with a | ⟨point', rest'⟩
  · simp [Paused.run_pure] at ho
  · simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, Sum.inr.injEq,
      Prod.mk.injEq] at ho
    obtain ⟨rfl, -⟩ := ho
    exact (hx st _ ha).2 point rest' rfl

end Walk

/-! ## The stop of one batch -/

section Batch

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

/-- The start of a check of operator `i` with the context `ctx` at the label `L + n` and the tag `tg`,
where `n` is the number of the tuples, whose counts are `counts`. Its run state holds the filled
history of its tuples. -/
def PointAt (i : C.Party) (ctx : Context C) (counts : List ℕ) (L tg : ℕ) (point : CheckPoint C) : Prop :=
  point.ctx = ctx ∧ point.tuples.map (·.count) = counts ∧
    point.state = ⟨filledHistory K i point.tuples, L + point.tuples.length, tg⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem mem_support_lift_run {α : Type} (y : PartyM C E RealSpec α) (st : ℕ × ℕ) (r : α × (ℕ × ℕ))
    (h : some r ∈ support ((StateT.lift y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α).run st).run) :
    r.2 = st ∧ some r.1 ∈ support y.run := by
  rw [StateT.run_lift] at h
  rcases mem_support_optionT_bind _ _ _ h with h | ⟨a, ha, hr⟩
  · cases h
  · have : r = (a, st) := by simpa using hr
    subst this
    exact ⟨rfl, ha⟩

omit [Fintype E] [DecidableEq E] in
/-- The cut batch only stops, and it stops at the filled history of its tuples, with the label and the
tag of its counters. -/
theorem cutWalk_cutBatch (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (js : List Job) :
    CutWalk (fun _ _ => False)
      (fun st point => PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind))) st.1 st.2 point)
      (cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js) := by
  intro st o ho
  unfold cutBatch at ho
  simp only [StateT.run_bind, StateT.run_get, CutM.lift_run, StateT.run_lift, Paused.run_bind,
    Paused.lift, Paused.stop, map_bind, map_pure, pure_bind, bind_assoc] at ho
  rcases mem_support_optionT_bind _ _ _ ho with rfl | ⟨inputs, -, ho⟩
  · exact ⟨fun r h => (by cases h), fun point rest h => (by cases h)⟩
  rcases mem_support_optionT_bind _ _ _ ho with rfl | ⟨q, hq, ho⟩
  · exact ⟨fun r h => (by cases h), fun point rest h => (by cases h)⟩
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff] at ho
  subst ho
  refine ⟨fun r h => (by cases h), fun point rest h => ?_⟩
  simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨hs, hc⟩ := runJobsHead_support K _ _ _ _ _ _ q hq
  exact ⟨rfl, hc, hs⟩

omit [Fintype E] [DecidableEq E] in
/-- On each path of a full real batch, the label grows by `jobLabel` and the tag by one. -/
theorem realBatch_support (ctx : Context C) (parameter : PublicParameter) (js : List Job) (st : ℕ × ℕ)
    (r : Option (List (List Bit)) × (ℕ × ℕ))
    (hr : some r ∈ support ((realBatch K circuits settings.mode ctx parameter js).run st).run) :
    r.2 = (st.1 + jobLabel circuits parameter js, st.2 + 1) := by
  rw [realBatch_run] at hr
  rcases mem_support_optionT_bind _ _ _ hr with h | ⟨inputs, -, hr⟩
  · cases h
  rcases mem_support_optionT_bind _ _ _ hr with h | ⟨q, hq, hr⟩
  · cases h
  have : r = (some q.1, (q.2.label, st.2 + 1)) := by simpa using hr
  subst this
  rw [runJobs_label K ctx settings.mode _ inputs st.1 st.2 q hq]
  rfl

/-- One batch of `cutRun`. A batch with the tag `k` stops at the filled history of its tuples, and
another batch adds `jobLabel` to the label and one to the tag. -/
theorem cutWalk_batch (k : ℕ) (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (js : List Job) :
    CutWalk (fun st r => r.2 = (st.1 + jobLabel circuits keys.parameter js, st.2 + 1))
      (fun st point => st.2 = k ∧
        PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind))) st.1 k point)
      (do
        let (_, tag) ← get
        if tag = k then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js
        else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter js)) := by
  refine cutWalk_mono (cutWalk_bind (cutWalk_get (fun _ _ => False))
    (P₂ := fun _ st r => r.2 = (st.1 + jobLabel circuits keys.parameter js, st.2 + 1))
    (Q₂ := fun p st point => p.2 = k ∧
      PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind))) st.1 st.2 point)
    fun p => ?_) ?_ ?_
  · rcases p with ⟨_, tag⟩
    dsimp only
    split_ifs with h
    · refine cutWalk_mono (cutWalk_cutBatch K circuits settings i keys prss js) (fun _ _ h => h.elim) ?_
      intro st point hp
      exact ⟨h, hp⟩
    · exact cutWalk_mono (cutWalk_lift _ _) (fun st r hr => realBatch_support K circuits settings _ _ _ st r hr)
        (fun _ _ h => h)
  · rintro st r ⟨a, rfl, h⟩
    exact h
  · rintro st point (h | ⟨a, rfl, h, hp⟩)
    · exact h.elim
    · exact ⟨h, h ▸ hp⟩

/-- One ceremony of `cutRun` on the jobs `jobs`. It adds `jobLabel` of each batch to the label and the
number of the batches to the tag, or it stops in a batch `js` with the tag `k` at the filled history of
its tuples. The label at the stop is the label at the start plus `jobLabel` of the batches before `js`. -/
theorem cutWalk_cutRun (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    CutWalk (fun st r => r.2 = (st.1 + ((chunks settings.batchSize jobs).map (jobLabel circuits keys.parameter)).sum,
        st.2 + (chunks settings.batchSize jobs).length))
      (fun st point => ∃ prss pre js suf, chunks settings.batchSize jobs = pre ++ js :: suf ∧ st.2 + pre.length = k ∧
        PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind)))
          (st.1 + (pre.map (jobLabel circuits keys.parameter)).sum) k point)
      (cutRun K circuits settings k i keys jobs) := by
  unfold cutRun batched
  refine cutWalk_mono (cutWalk_bind (cutWalk_lift _ (fun _ _ => False))
    (P₂ := fun _ st r => r.2 = (st.1 + ((chunks settings.batchSize jobs).map (jobLabel circuits keys.parameter)).sum,
        st.2 + (chunks settings.batchSize jobs).length))
    (Q₂ := fun prss st point => ∃ pre js suf, chunks settings.batchSize jobs = pre ++ js :: suf ∧
        st.2 + pre.length = k ∧ PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind)))
          (st.1 + (pre.map (jobLabel circuits keys.parameter)).sum) k point)
    fun prss => ?_) ?_ ?_
  · refine cutWalk_mono (cutWalk_bind (cutWalk_mapM _ k (jobLabel circuits keys.parameter)
      (fun js L point => PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind))) L k point)
      (fun js => cutWalk_batch K circuits settings k i keys prss js) _)
      fun outputs => cutWalk_pure _ (fun _ _ => False)) ?_ ?_
    · rintro st r ⟨a, ha, rfl⟩
      exact ha
    · rintro st point (h | ⟨a, -, h⟩)
      · exact h
      · exact h.elim
  · rintro st r ⟨a, ha, h⟩
    obtain ⟨hst, -⟩ := mem_support_lift_run _ _ _ ha
    rw [h, hst]
  · rintro st point (h | ⟨a, ha, h⟩)
    · exact h.elim
    · obtain ⟨hst, -⟩ := mem_support_lift_run _ _ _ ha
      rw [hst] at h
      exact ⟨a.1, h⟩

end Batch

/-! ## The stop of a tree -/

section Tree

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem lift_counters {α : Type} (y : PartyM C E RealSpec α) (st : ℕ × ℕ) (a : α × (ℕ × ℕ))
    (h : some a ∈ support ((StateT.lift y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α).run st).run) : a.2 = st :=
  (mem_support_lift_run y st a h).1

end Tree

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace SetupCut

attribute [local instance] Classical.propDecidable

/-! ## The setup at the head of a cut program -/

section Walk

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

/-- The batches of `cutRun` after its PRSS setup, with the PRSS keys `prss`. -/
def cutBatches (k : ℕ) (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (jobs : List Job) :
    CutM K (Option (List (List Bit))) :=
  batched settings.batchSize (fun js => do
    let (_, tag) ← get
    if tag = k then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js
    else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter js)) jobs

omit [Fintype E] [DecidableEq E] in
theorem cutRun_eq (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    cutRun K circuits settings k i keys jobs =
      CutM.lift (StateT.lift (prssSetup i)) >>= fun prss => cutBatches K circuits settings k i keys prss jobs :=
  rfl

/-- The batches after the setup stop only with the PRSS keys of the setup, and they add the number of
the batches to the tag. -/
theorem cutWalk_cutBatches (k : ℕ) (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (jobs : List Job) :
    CutWalk (fun st r => r.2 = (st.1 + ((chunks settings.batchSize jobs).map (jobLabel circuits keys.parameter)).sum,
        st.2 + (chunks settings.batchSize jobs).length))
      (fun _ point => point.ctx.prss = prss) (cutBatches K circuits settings k i keys prss jobs) := by
  unfold cutBatches batched
  refine cutWalk_mono (cutWalk_bind (cutWalk_mapM _ k (jobLabel circuits keys.parameter)
      (fun js L point => PointAt K i ⟨i, keys, prss⟩ (headCounts (js.map (circuits keys.parameter ·.kind))) L k point)
      (fun js => cutWalk_batch K circuits settings k i keys prss js) _)
      fun outputs => cutWalk_pure _ (fun _ _ => False)) ?_ ?_
  · rintro st r ⟨a, ha, rfl⟩
    exact ha
  · rintro st point (⟨pre, js, suf, -, -, hp⟩ | ⟨a, -, h⟩)
    · rw [hp.1]
    · exact h.elim

/-- The ceremonies of a tree start with the PRSS setup of the first ceremony. The rest after the
batches of the first ceremony stops only at a tag at least its start tag. -/
theorem ceremonyOutput_setup (k : ℕ) (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    ∃ rest : Option (List (List Bit)) → CutM K (Option TreeOutput),
      ceremonyOutput (m := CutM K) (fun oa => CutM.lift (StateT.lift (oracleStep (tweakable oa))))
          keys.parameter (cutRun K circuits settings k i keys) top tree =
        (CutM.lift (StateT.lift (prssSetup i)) >>= fun prss =>
          cutBatches K circuits settings k i keys prss (CheckTiming.firstJobs tree) >>= rest) ∧
      ∀ o, CutWalk (fun _ _ => True) (fun st _ => st.2 ≤ k) (rest o) := by
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    rw [cutRun_eq, bind_assoc]
    refine ⟨_, rfl, fun o => ?_⟩
    rcases o with _ | outputs
    · exact cutWalk_pure_true _ _
    · exact cutWalk_lift_bind _ _ _ (lift_counters _) fun _ => cutWalk_pure_true _ _
  | bottom b =>
    simp only [ceremonyOutput]
    rw [cutRun_eq, bind_assoc]
    refine ⟨_, rfl, fun o => ?_⟩
    rcases o with _ | outputs
    · exact cutWalk_pure_true _ _
    refine cutWalk_lift_bind _ _ _ (lift_counters _) fun _ => cutWalk_lift_bind _ _ _ (lift_counters _) fun _ =>
      cutWalk_lift_bind _ _ _ (lift_counters _) fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · exact cutWalk_pure_true _ _
    refine cutWalk_mono (cutWalk_bind (cutWalk_cutRun K circuits settings k i keys (signJobs b encoding))
      (P₂ := fun _ _ _ => True) (Q₂ := fun _ _ _ => False) fun o => ?_) (fun _ _ _ => trivial) ?_
    · rcases o with _ | values
      · exact cutWalk_pure_true _ _
      refine cutWalk_lift_bind _ _ _ (lift_counters _) fun _ => cutWalk_lift_bind _ _ _ (lift_counters _) fun _ => ?_
      split_ifs
      · exact cutWalk_pure_true _ _
      · exact cutWalk_pure_true _ _
    · rintro st point (⟨prss, pre, js, suf, -, hk, -⟩ | ⟨_, _, h⟩)
      · omega
      · exact h.elim

/-- An operator that runs the PRSS setup of the first ceremony of `tree`. It has keys, and for a
bottom tree a top tree. -/
def SetupLive (operator : OperatorState C) : Tree → Prop
  | .top => operator.keys.isSome
  | .bottom _ => operator.keys.isSome ∧ operator.top.isSome

end Walk

/-! ## An honest output is an output of its program -/

section Reach

variable {C : Committee} {E : Type}

/-- Each output of the program that the step stands for is an output of `program`. -/
def Reach {α : Type} (program : OracleComp (PartySpec C E RealSpec) (Option α)) (step : Step C E RealSpec α) :
    Prop :=
  ∀ a, some a ∈ support (stepProgram step) → some a ∈ support program

theorem reach_advance {α : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α)) :
    ∀ step ∈ support (advance oa), Reach oa step := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro step hs
    rw [advance_pure, support_pure, Set.mem_singleton_iff] at hs
    subst hs
    intro a ha
    simpa [stepProgram] using ha
  | query_bind t k ih =>
    intro step hs
    rcases t with (q | outbox) | input
    · change step ∈ support (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)) at hs
      rw [mem_support_bind_iff] at hs
      obtain ⟨r, -, hr⟩ := hs
      intro a ha
      rw [mem_support_bind_iff]
      exact ⟨r, by simp, ih r step hr a ha⟩
    · change step ∈ support (pure (Step.wait outbox k) : OracleComp (LocalSpec C) _) at hs
      rw [support_pure, Set.mem_singleton_iff] at hs
      subst hs
      exact fun a ha => ha
    · exact input.elim

theorem reach_output {α : Type} {program : OracleComp (PartySpec C E RealSpec) (Option α)}
    {step : Step C E RealSpec α} (h : Reach program step) {a : α} (ha : step.output = some a) :
    some a ∈ support program := by
  rcases step with out | _ | _
  · cases ha
    exact h a (by simp [stepProgram])
  · cases ha
  · cases ha

variable {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)

theorem stepRound_reach {α : Type} (st : A.State) (steps : C.Party → Step C E RealSpec α)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α))
    (hon : ∀ i ∉ D.1, Reach (program i) (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A noFunctionality st steps), ∀ i ∉ D.1, Reach (program i) (r.2.1 i) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  intro r hr i hi
  unfold stepRound at hr
  rw [ite_eq_right hno] at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨fo, -, steps', hs', rfl⟩ := hr
  have h := mem_support_sequenceFin_oc _ _ hs' i
  have hpi := hon i hi
  change Reach (program i) (steps' i)
  rcases hsi : steps i with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · rw [hsi] at h hpi
    simp only [support_pure, Set.mem_singleton_iff] at h
    rw [h]
    exact hpi
  · rw [hsi] at h hpi
    simp only [hi, ↓reduceIte, worldRoles] at h
    have hr := reach_advance _ _ (support_free_subset _ h)
    intro a ha
    refine hpi a ?_
    simp only [stepProgram]
    rw [mem_support_bind_iff]
    exact ⟨_, by simp, hr a ha⟩
  · exact input.elim

theorem executeRounds_reach {α : Type} (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α)) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α),
      (∀ i ∉ D.1, Reach (program i) (steps i)) →
      ∀ z ∈ support (executeRounds worldRoles D A noFunctionality fuel st steps), ∀ i ∉ D.1, ∀ a,
        z.2 i = some a → some a ∈ support (program i)
  | 0, st, steps, hon => by
    intro z hz i hi a ha
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact reach_output (hon i hi) ha
  | fuel + 1, st, steps, hon => by
    intro z hz i hi a ha
    unfold executeRounds at hz
    split_ifs at hz with hdone
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact reach_output (hon i hi) ha
    · simp only [support_bind, Set.mem_iUnion] at hz
      obtain ⟨q, hq, hz⟩ := hz
      exact executeRounds_reach program fuel q.1 q.2.1 (stepRound_reach D A st steps program hon q hq) z hz i hi a ha

/-- Each honest output of a phase on the network is an output of the program of its operator, under
each answer of the oracles. -/
theorem executePhase_reach {α : Type} (fuel : ℕ) (st : A.State) (program : C.Party → PartyM C E RealSpec α) :
    ∀ z ∈ support (executePhase worldRoles D A noFunctionality fuel st program), ∀ i ∉ D.1, ∀ a,
      z.2 i = some a → some a ∈ support (program i).run := by
  intro z hz
  unfold executePhase at hz
  simp only [support_bind, Set.mem_iUnion] at hz
  obtain ⟨s0, hs0, hz⟩ := hz
  refine executeRounds_reach D A (fun j => (program j).run) fuel st s0 (fun j hj => ?_) z hz
  have h := mem_support_sequenceFin_oc _ _ hs0 j
  simp only [hj, ↓reduceIte, worldRoles] at h
  exact reach_advance _ _ (support_free_subset _ h)

end Reach

/-! ## The setup cut in the first ceremony -/

section Cut

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings) (prims : Primitives) (budget : StartBudget) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A PRSS setup takes `setupRounds` rounds and makes no local query after the last one. -/
theorem timedQuiet_prssSetup (i : C.Party) :
    TimedQuiet setupRounds (prssSetup (E := E) (G := RealSpec) i).run := by
  unfold prssSetup prssSetupWith
  refine TimedQuiet.localStep_bind 2 _ _ fun own => ?_
  exact (timedQuiet_commitRevealEcho (E := E) (G := RealSpec) .prss i own).bind (n := 0) fun _ => timedQuiet_pure _

end Cut

end SetupCut

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutWalk_cutRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.cutWalk_cutRun
