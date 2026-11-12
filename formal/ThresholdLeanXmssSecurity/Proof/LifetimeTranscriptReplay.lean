import ThresholdLeanXmssSecurity.Proof.LifetimeEmulation

/-! A local program records its oracle answers in the auxiliary input. Following the
program with those answers recovers its output, without making further queries. -/

noncomputable section

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity.LifetimeTranscriptReplay

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Every local program has an auxiliary transcript preserving its output and budget. -/
def TranscriptReplay (C : Committee) : Prop :=
  ∀ {α : Type} (p : OracleComp (LocalSpec C) α),
    ∃ (record : OracleComp (LocalSpec C) (α × Aux)) (replay : Aux → Option α),
      Prod.fst <$> record = p ∧
      (∀ q : ℕ, IsQueryBoundP p Counted q → IsQueryBoundP record Counted q) ∧
      ∀ (prims : Primitives) (g : HashCache C),
        ∀ r ∈ support ((simulateQ (localAnswer prims) record).run g),
          replay r.1.2 = some r.1.1

private def answerCode (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t) : ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _) u

private def answerDecode (t : (LocalSpec C).Domain) (n : ℕ) : Option ((LocalSpec C).Range t) :=
  @Encodable.decode _ (Encodable.ofCountable _) n

private theorem answerDecode_code (t : (LocalSpec C).Domain) (u : (LocalSpec C).Range t) :
    answerDecode t (answerCode t u) = some u :=
  @Encodable.encodek _ (Encodable.ofCountable _) u

/-- The queries are determined by the program and the preceding answers. Only the
answers therefore need encoding. This is the local-spec form of the transcript
consumption in `SigningHitProof.transcriptResidual`. -/
def replayAnswers {α : Type} (p : OracleComp (LocalSpec C) α) : List ℕ → Option α
  | [] => match p with
    | .pure a => some a
    | .queryBind _ _ => none
  | n :: ns => match p with
    | .pure _ => none
    | .queryBind t k => (answerDecode t n).bind (fun u => replayAnswers (k u) ns)

private def answerCodes (log : QueryLog (LocalSpec C)) : List ℕ :=
  log.map (fun e => answerCode e.1 e.2)

private theorem replayAnswers_logged {α : Type} (p : OracleComp (LocalSpec C) α) :
    ∀ r ∈ support (simulateQ (LocalSpec C).loggingOracle p).run,
      replayAnswers p (answerCodes r.2) = some r.1 := by
  induction p using OracleComp.inductionOn with
  | pure a =>
      intro r hr
      simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst r
      rfl
  | query_bind t k ih =>
      intro r hr
      rw [run_simulateQ_loggingOracle_query_bind] at hr
      simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image] at hr
      obtain ⟨u, _, s, hs, rfl⟩ := hr
      change replayAnswers (.queryBind t k)
        (answerCode t u :: answerCodes s.2) = some s.1
      simpa [replayAnswers, answerDecode_code] using ih u s hs

/-- The recording program makes exactly the original queries. -/
def record {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (LocalSpec C) (α × Aux) :=
  (fun r => (r.1, encodeAux (answerCodes r.2))) <$>
    (simulateQ (LocalSpec C).loggingOracle p).run

/-- Pure replay of the answer transcript stored in the auxiliary input. -/
def replay {α : Type} (p : OracleComp (LocalSpec C) α) (z : Aux) : Option α :=
  (decodeAux z).bind (replayAnswers p)

theorem record_fst {α : Type} (p : OracleComp (LocalSpec C) α) :
    Prod.fst <$> record p = p := by
  simp [record, Functor.map_map]

theorem record_bound {α : Type} (p : OracleComp (LocalSpec C) α) (q : ℕ)
    (h : IsQueryBoundP p Counted q) : IsQueryBoundP (record p) Counted q :=
  (isQueryBoundP_iff_of_map_eq (p := Counted) (record_fst p)).mpr h

theorem replay_record {α : Type} (p : OracleComp (LocalSpec C) α)
    (prims : Primitives) (g : HashCache C)
    (r : (α × Aux) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (record p)).run g)) :
    replay p r.1.2 = some r.1.1 := by
  have h : r.1 ∈ support (record p) := by
    apply support_simulateQ_run'_subset (localAnswer prims) (record p) g
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hr
  simp only [record, support_map, Set.mem_image] at h
  obtain ⟨s, hs, he⟩ := h
  rw [← he]
  simp only [replay, decodeAux_encodeAux, Option.bind_some]
  exact replayAnswers_logged p s hs

theorem transcriptReplay (C : Committee) : TranscriptReplay C := by
  intro α p
  exact ⟨record p, replay p, record_fst p, record_bound p, replay_record p⟩

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTranscriptReplay.record_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms record_fst

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTranscriptReplay.record_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms record_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTranscriptReplay.replay_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_record

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTranscriptReplay.transcriptReplay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transcriptReplay

end ThresholdLeanXmssSecurity.LifetimeTranscriptReplay
