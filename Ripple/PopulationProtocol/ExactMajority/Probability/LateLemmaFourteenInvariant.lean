import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaThirteenSmallGap
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaFourteenSpreads

noncomputable section

open Set

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenInvariant

open TimeTheorem TraceDrain
open Phase7Convergence
open LateLemmaThirteenDeterministic
open LateLemmaThirteenRoute
open LateLemmaThirteenSmallGap

variable {L K : ℕ}

/-- `sigma` is the eliminated sign. Its opposite is the strict verdict. -/
def majorityOutput : Sign → Output
  | .neg => .A
  | .pos => .B

/-- The Phase-9 part of the invariant. -/
def PhaseNineAgent (sigma : Sign) (a : AgentState L K) : Prop :=
  a.phase.val = 9 ∧
    ¬ minoritySt sigma a ∧
    LateLemmaFourteenSpreads.opinionCompatible
      (majorityOutput sigma) a.opinions ∧
    (majorityBiasedSt sigma a →
      LateLemmaFourteenSpreads.opinionCarrier
        (majorityOutput sigma) a.opinions)

/-- Phase 8 carries no opinion-mask obligation; Phase 9 carries the corrected one. -/
def CorridorAgent (sigma : Sign) (a : AgentState L K) : Prop :=
  (a.phase.val = 8 ∧ ¬ minoritySt sigma a) ∨ PhaseNineAgent sigma a

/-- Full deterministic handoff invariant. -/
def CorridorInvariant (sigma : Sign)
    (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, CorridorAgent sigma a) ∧
    0 < majorityBiasedCount sigma c

/-- Per-pair result used to replace an applicable source pair. -/
structure CorridorPairResult (sigma : Sign)
    (s t : AgentState L K) : Prop where
  left : CorridorAgent sigma (Transition L K s t).1
  right : CorridorAgent sigma (Transition L K s t).2
  left_role : (Transition L K s t).1.role = s.role
  left_bias : (Transition L K s t).1.bias = s.bias
  right_role : (Transition L K s t).2.role = t.role
  right_bias : (Transition L K s t).2.bias = t.bias

private def phaseNine : Fin 11 := ⟨9, by decide⟩
private def neutralOpinion : Fin 8 := ⟨2, by decide⟩

/-- The genuine 8-to-9 entry: set the phase, then run the repaired Init 9. -/
def enterNine (a : AgentState L K) : AgentState L K :=
  phaseInit L K phaseNine { a with phase := phaseNine }

@[simp] private theorem enterNine_phase (a : AgentState L K) :
    (enterNine a).phase.val = 9 := by
  by_cases hm : a.role = .main <;> simp [enterNine, phaseNine, phaseInit, hm]

@[simp] private theorem enterNine_role (a : AgentState L K) :
    (enterNine a).role = a.role := by
  by_cases hm : a.role = .main <;> simp [enterNine, phaseNine, phaseInit, hm]

@[simp] private theorem enterNine_bias (a : AgentState L K) :
    (enterNine a).bias = a.bias := by
  by_cases hm : a.role = .main <;> simp [enterNine, phaseNine, phaseInit, hm]

/-- Exact repaired Init-9 read: live dyadic `bias`, never `smallBias`. -/
theorem enterNine_opinions_live (a : AgentState L K) :
    (enterNine a).opinions =
      if a.role = .main then phase9InitialOpinions L a.bias
      else neutralOpinion := by
  by_cases hm : a.role = .main <;> simp [enterNine, phaseNine, neutralOpinion, phaseInit, hm]

/-- Changing only the stale small-bias field cannot affect Init 9. -/
theorem phaseInit_nine_ignores_smallBias
    (a : AgentState L K) (small : Fin 7) :
    (enterNine { a with smallBias := small }).opinions =
      (enterNine a).opinions := by
  simp [enterNine_opinions_live]

private theorem minoritySt_static_iff
    (sigma : Sign) {a b : AgentState L K}
    (hr : b.role = a.role) (hb : b.bias = a.bias) :
    minoritySt sigma b ↔ minoritySt sigma a := by
  simp [minoritySt, hr, hb]

private theorem majorityBiasedSt_static_iff
    (sigma : Sign) {a b : AgentState L K}
    (hr : b.role = a.role) (hb : b.bias = a.bias) :
    majorityBiasedSt sigma b ↔ majorityBiasedSt sigma a := by
  simp [majorityBiasedSt, minoritySt, hr, hb]

private theorem enterNine_bits
    (sigma : Sign) (a : AgentState L K)
    (hno : ¬ minoritySt sigma a) :
    LateLemmaFourteenSpreads.opinionCompatible
        (majorityOutput sigma) (enterNine a).opinions ∧
      (majorityBiasedSt sigma a →
        LateLemmaFourteenSpreads.opinionCarrier
          (majorityOutput sigma) (enterNine a).opinions) := by
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        cases sigma <;>
          simp [majorityOutput, LateLemmaFourteenSpreads.opinionCompatible,
            LateLemmaFourteenSpreads.opinionCarrier, enterNine_opinions_live,
            hm, hb, majorityBiasedSt, minoritySt, neutralOpinion, hasMinusOne, hasPlusOne]
    | dyadic sign i =>
        cases sigma <;> cases sign <;>
          simp_all [majorityOutput, LateLemmaFourteenSpreads.opinionCompatible,
            LateLemmaFourteenSpreads.opinionCarrier, enterNine_opinions_live,
            hm, hb, majorityBiasedSt, minoritySt, neutralOpinion,
            phase9InitialOpinions, hasMinusOne, hasPlusOne]
  · cases sigma <;>
      simp [majorityOutput, LateLemmaFourteenSpreads.opinionCompatible,
        LateLemmaFourteenSpreads.opinionCarrier, enterNine_opinions_live,
        hm, majorityBiasedSt, minoritySt, neutralOpinion,
        hasMinusOne, hasPlusOne]

private theorem enterNine_agent
    (sigma : Sign) (a : AgentState L K)
    (hno : ¬ minoritySt sigma a) :
    PhaseNineAgent sigma (enterNine a) := by
  have hbits := enterNine_bits sigma a hno
  refine ⟨enterNine_phase a, ?_, hbits.1, ?_⟩
  · intro hminor
    exact hno ((minoritySt_static_iff sigma
      (enterNine_role a) (enterNine_bias a)).mp hminor)
  · intro hmajor
    exact hbits.2 ((majorityBiasedSt_static_iff sigma
      (enterNine_role a) (enterNine_bias a)).mp hmajor)

/-- Clause (d): compatible Phase-9 masks cannot trigger backup. -/
theorem phaseNine_union_does_not_backup
    (sigma : Sign) (s t : AgentState L K)
    (hs : PhaseNineAgent sigma s) (ht : PhaseNineAgent sigma t) :
    (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
      hasPlusOne (opinionsUnion s.opinions t.opinions)) = false :=
  LateLemmaFourteenSpreads.opinionCompatible_union_not_conflicting
    (majorityOutput sigma) s.opinions t.opinions
    hs.2.2.1 ht.2.2.1

private theorem samePhaseEpidemic_eq_self
    (s t : AgentState L K) (hphase : s.phase = t.phase) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  classical
  have hbad : ¬ ((t.phase.val < 10 ∨ t.phase.val < 10) ∧
      (t.phase.val = 10 ∨ t.phase.val = 10)) := by omega
  unfold phaseEpidemicUpdate
  rw [hphase, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

private theorem runInitsBetween_eight_nine (a : AgentState L K) :
    runInitsBetween L K 8 9 a = phaseInit L K phaseNine a := by rfl

private theorem epidemic_eight_nine_left
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 9) :
    phaseEpidemicUpdate L K s t = (enterNine s, t) := by
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
  have htp : t.phase = phaseNine := Fin.ext ht
  unfold phaseEpidemicUpdate
  simp only [hsp, htp, phaseNine, Fin.val_mk, max_eq_right (by decide : (⟨8, by decide⟩ : Fin 11) ≤ ⟨9, by decide⟩)]
  rw [runInitsBetween_eight_nine, runInitsBetween_self]
  split_ifs with hbad
  · change (8 < 10 ∨ 9 < 10) ∧ ((enterNine s).phase.val = 10 ∨ 9 = 10) at hbad
    have := enterNine_phase s
    omega
  · change (enterNine s, { t with phase := phaseNine }) = (enterNine s, t)
    have htself : { t with phase := phaseNine } = t := by
      rw [← htp]
    rw [htself]

private theorem epidemic_eight_nine_right
    (s t : AgentState L K)
    (hs : s.phase.val = 9) (ht : t.phase.val = 8) :
    phaseEpidemicUpdate L K s t = (s, enterNine t) := by
  have hsp : s.phase = phaseNine := Fin.ext hs
  have htp : t.phase = ⟨8, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  simp only [hsp, htp, phaseNine, Fin.val_mk, max_eq_left (by decide : (⟨8, by decide⟩ : Fin 11) ≤ ⟨9, by decide⟩)]
  rw [runInitsBetween_self, runInitsBetween_eight_nine]
  split_ifs with hbad
  · change (9 < 10 ∨ 8 < 10) ∧ (9 = 10 ∨ (enterNine t).phase.val = 10) at hbad
    have := enterNine_phase t
    omega
  · change ({ s with phase := phaseNine }, enterNine t) = (s, enterNine t)
    have hsself : { s with phase := phaseNine } = s := by
      rw [← hsp]
    rw [hsself]

private theorem transition_eight_nine_left
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 9) :
    Transition L K s t = Transition L K (enterNine s) t := by
  have hepi := epidemic_eight_nine_left s t hs ht
  have hsame := samePhaseEpidemic_eq_self (enterNine s) t
    (Fin.ext (by simp [ht]))
  unfold Transition
  rw [hepi, hsame]

private theorem transition_eight_nine_right
    (s t : AgentState L K)
    (hs : s.phase.val = 9) (ht : t.phase.val = 8) :
    Transition L K s t = Transition L K s (enterNine t) := by
  have hepi := epidemic_eight_nine_right s t hs ht
  have hsame := samePhaseEpidemic_eq_self s (enterNine t)
    (Fin.ext (by simp [hs]))
  unfold Transition
  rw [hepi, hsame]

private theorem absorbConsume_eq_self_of_no_minority
    (sigma : Sign) (s t : AgentState L K)
    (hsMain : s.role = .main) (htMain : t.role = .main)
    (hsNo : ¬ minoritySt sigma s) (htNo : ¬ minoritySt sigma t) :
    absorbConsume L K s t = (s, t) := by
  cases hsBias : s.bias with
  | zero => simp [absorbConsume, hsBias]
  | dyadic ss i =>
      cases htBias : t.bias with
      | zero => simp [absorbConsume, hsBias, htBias]
      | dyadic st j =>
          cases sigma <;> cases ss <;> cases st <;>
            simp_all [absorbConsume, minoritySt]

private def phaseEightLocal (a : AgentState L K) : AgentState L K :=
  if a.role = .clock then stdCounterSubroutine L K a else a

private theorem phaseEightLocal_spec
    (sigma : Sign) (a : AgentState L K)
    (hphase : a.phase.val = 8) (hno : ¬ minoritySt sigma a) :
    CorridorAgent sigma (phaseEightLocal a) ∧
      (phaseEightLocal a).role = a.role ∧
      (phaseEightLocal a).bias = a.bias := by
  by_cases hc : a.role = .clock
  · by_cases hz : a.counter.val = 0
    · have hph : a.phase = ⟨8, by decide⟩ := Fin.ext hphase
      have heq : phaseEightLocal a = enterNine a := by
        simp [phaseEightLocal, hc, stdCounterSubroutine, hz,
          enterNine, phaseNine, advancePhaseWithInit, advancePhase, hph]
      rw [heq]
      exact ⟨Or.inr (enterNine_agent sigma a hno),
        enterNine_role a, enterNine_bias a⟩
    · refine ⟨Or.inl ⟨?_, ?_⟩, ?_, ?_⟩
      · simp [phaseEightLocal, hc, stdCounterSubroutine, hz, hphase]
      · simp [phaseEightLocal, hc, stdCounterSubroutine, hz,
          minoritySt, hc]
      · simp [phaseEightLocal, hc, stdCounterSubroutine, hz]
      · simp [phaseEightLocal, hc, stdCounterSubroutine, hz]
  · simp [phaseEightLocal, hc, CorridorAgent, hphase, hno]

private theorem phaseEightTransition_eq_local
    (sigma : Sign) (s t : AgentState L K)
    (hsNo : ¬ minoritySt sigma s) (htNo : ¬ minoritySt sigma t) :
    Phase8Transition L K s t =
      (phaseEightLocal s, phaseEightLocal t) := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · have habs := absorbConsume_eq_self_of_no_minority
      sigma s t hm.1 hm.2 hsNo htNo
    simp [Phase8Transition, phaseEightLocal, hm, habs]
  · simp [Phase8Transition, phaseEightLocal, hm]

private theorem transition_phase_eight_pair
    (sigma : Sign) (s t : AgentState L K)
    (hs : s.phase.val = 8 ∧ ¬ minoritySt sigma s)
    (ht : t.phase.val = 8 ∧ ¬ minoritySt sigma t) :
    CorridorPairResult sigma s t := by
  have hsLocal := phaseEightLocal_spec sigma s hs.1 hs.2
  have htLocal := phaseEightLocal_spec sigma t ht.1 ht.2
  have hcore := phaseEightTransition_eq_local sigma s t hs.2 ht.2
  have hepi := Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
    (L := L) (K := K) s t hs.1 ht.1
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs.1
  have hsNot : (phaseEightLocal s).phase.val ≠ 10 := by
    rcases hsLocal.1 with h | h
    · omega
    · have := h.1; omega
  have htNot : (phaseEightLocal t).phase.val ≠ 10 := by
    rcases htLocal.1 with h | h
    · omega
    · have := h.1; omega
  have heq : Transition L K s t =
      (phaseEightLocal s, phaseEightLocal t) := by
    simp only [Transition, hepi, hsp, hcore,
      finishPhase10Entry_eq_self_of_after_ne_10 L K s _ hsNot,
      finishPhase10Entry_eq_self_of_after_ne_10 L K t _ htNot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [heq]
  · exact hsLocal.1
  · exact htLocal.1
  · exact hsLocal.2.1
  · exact hsLocal.2.2
  · exact htLocal.2.1
  · exact htLocal.2.2

private theorem transition_phase_nine_pair
    (sigma : Sign) (s t : AgentState L K)
    (hs : PhaseNineAgent sigma s) (ht : PhaseNineAgent sigma t) :
    CorridorPairResult sigma s t := by
  have hbits := LateLemmaFourteenSpreads.Transition_phase_nine_carrier_pair
    (majorityOutput sigma) s t hs.1 ht.1 hs.2.2.1 ht.2.2.1
  have hstatic := Transition_role_bias_preserved_of_phase_ge_nine
    (L := L) (K := K) s t (by have := hs.1; omega) (by have := ht.1; omega)
  refine
    { left := Or.inr ⟨hbits.1.1, ?_, hbits.1.2, ?_⟩
      right := Or.inr ⟨hbits.2.1.1, ?_, hbits.2.1.2, ?_⟩
      left_role := hstatic.1
      left_bias := hstatic.2.1
      right_role := hstatic.2.2.1
      right_bias := hstatic.2.2.2 }
  · intro hminor
    exact hs.2.1 ((minoritySt_static_iff sigma
      hstatic.1 hstatic.2.1).mp hminor)
  · intro hmajor
    have hsMajor := (majorityBiasedSt_static_iff sigma
      hstatic.1 hstatic.2.1).mp hmajor
    exact (hbits.2.2 (Or.inl (hs.2.2.2 hsMajor))).1
  · intro hminor
    exact ht.2.1 ((minoritySt_static_iff sigma
      hstatic.2.2.1 hstatic.2.2.2).mp hminor)
  · intro hmajor
    have htMajor := (majorityBiasedSt_static_iff sigma
      hstatic.2.2.1 hstatic.2.2.2).mp hmajor
    exact (hbits.2.2 (Or.inr (ht.2.2.2 htMajor))).2

private theorem transition_mixed_left
    (sigma : Sign) (s t : AgentState L K)
    (hs : s.phase.val = 8 ∧ ¬ minoritySt sigma s)
    (ht : PhaseNineAgent sigma t) :
    CorridorPairResult sigma s t := by
  have hp := transition_phase_nine_pair sigma (enterNine s) t
    (enterNine_agent sigma s hs.2) ht
  have heq := transition_eight_nine_left s t hs.1 ht.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [heq]
  · exact hp.left
  · exact hp.right
  · exact hp.left_role.trans (enterNine_role s)
  · exact hp.left_bias.trans (enterNine_bias s)
  · exact hp.right_role
  · exact hp.right_bias

private theorem transition_mixed_right
    (sigma : Sign) (s t : AgentState L K)
    (hs : PhaseNineAgent sigma s)
    (ht : t.phase.val = 8 ∧ ¬ minoritySt sigma t) :
    CorridorPairResult sigma s t := by
  have hp := transition_phase_nine_pair sigma s (enterNine t)
    hs (enterNine_agent sigma t ht.2)
  have heq := transition_eight_nine_right s t hs.1 ht.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [heq]
  · exact hp.left
  · exact hp.right
  · exact hp.left_role
  · exact hp.left_bias
  · exact hp.right_role.trans (enterNine_role t)
  · exact hp.right_bias.trans (enterNine_bias t)

/-- Actual pair closure for every source pair in phases 8..9. -/
theorem Transition_corridor_pair
    (sigma : Sign) (s t : AgentState L K)
    (hs : CorridorAgent sigma s) (ht : CorridorAgent sigma t) :
    CorridorPairResult sigma s t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact transition_phase_eight_pair sigma s t hs ht
  · exact transition_mixed_left sigma s t hs ht
  · exact transition_mixed_right sigma s t hs ht
  · exact transition_phase_nine_pair sigma s t hs ht

private theorem majority_pair_count_eq
    (sigma : Sign) (s t : AgentState L K)
    (h : CorridorPairResult sigma s t) :
    @Multiset.countP _ (majorityBiasedSt sigma) (fun _ => Classical.propDecidable _)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) =
      @Multiset.countP _ (majorityBiasedSt sigma) (fun _ => Classical.propDecidable _)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  have hl := majorityBiasedSt_static_iff sigma h.left_role h.left_bias
  have hr := majorityBiasedSt_static_iff sigma h.right_role h.right_bias
  rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
    show ({(Transition L K s t).1, (Transition L K s t).2} :
      Multiset (AgentState L K)) =
        (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl]
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  by_cases hs : majorityBiasedSt sigma s <;>
    by_cases ht : majorityBiasedSt sigma t <;> simp_all

/-- Source-guarded actual-step relation requested by Lemma 14. -/
def CorridorStep (sigma : Sign)
    (c d : Config (AgentState L K)) : Prop :=
  ∃ s t, Protocol.Applicable c s t ∧
    CorridorAgent sigma s ∧ CorridorAgent sigma t ∧
    d = Protocol.stepOrSelf (NonuniformMajority L K) c s t

/-- One actual scheduled pair preserves the invariant. -/
theorem CorridorInvariant_stepOrSelf
    (sigma : Sign) (c : Config (AgentState L K))
    (hInv : CorridorInvariant sigma c) (s t : AgentState L K) :
    CorridorInvariant sigma
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hsMem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have htMem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hp := Transition_corridor_pair sigma s t
      (hInv.1 s hsMem) (hInv.1 t htMem)
    have hc : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    refine ⟨?_, ?_⟩
    · rw [hc]
      intro a ha
      have ha' : a = (Transition L K s t).1 ∨
          a ∈ c - {s, t} ∨ a = (Transition L K s t).2 := by
        simpa using ha
      rcases ha' with rfl | haold | rfl
      · exact hp.left
      · exact hInv.1 a
          (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold)
      · exact hp.right
    · have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
      have hsplit : Multiset.countP (majorityBiasedSt sigma) c =
          Multiset.countP (majorityBiasedSt sigma) (c - {s, t}) +
            Multiset.countP (majorityBiasedSt sigma)
              ({s, t} : Multiset (AgentState L K)) := by
        rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
      have hcount : majorityBiasedCount sigma
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
          majorityBiasedCount sigma c := by
        unfold majorityBiasedCount
        rw [hc, Multiset.countP_add,
          majority_pair_count_eq sigma s t hp]
        exact hsplit.symm
      rw [hcount]
      exact hInv.2
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hInv

/-- Closure for the explicit source-guarded relation. -/
theorem CorridorInvariant_corridorStep
    (sigma : Sign) {c d : Config (AgentState L K)}
    (hInv : CorridorInvariant sigma c)
    (hstep : CorridorStep sigma c d) :
    CorridorInvariant sigma d := by
  rcases hstep with ⟨s, t, _, _, _, rfl⟩
  exact CorridorInvariant_stepOrSelf sigma c hInv s t

/-- Every concrete protocol step induces the source-guarded relation. -/
theorem corridorStep_of_stepRel
    (sigma : Sign) {c d : Config (AgentState L K)}
    (hInv : CorridorInvariant sigma c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    CorridorStep sigma c d := by
  classical
  rcases hstep with ⟨s, t, happ, hd⟩
  dsimp at hd
  have hsMem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htMem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have heq : Protocol.stepOrSelf (NonuniformMajority L K) c s t = d := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hd.symm
  exact ⟨s, t, happ, hInv.1 s hsMem, hInv.1 t htMem, heq.symm⟩

/-- Invariant closure under one actual `StepRel`. -/
theorem CorridorInvariant_stepRel
    (sigma : Sign) {c d : Config (AgentState L K)}
    (hInv : CorridorInvariant sigma c)
    (hstep : (NonuniformMajority L K).StepRel c d) :
    CorridorInvariant sigma d :=
  CorridorInvariant_corridorStep sigma hInv
    (corridorStep_of_stepRel sigma hInv hstep)

/-- Invariant closure along every finite actual execution. -/
theorem CorridorInvariant_reachable
    (sigma : Sign) {c d : Config (AgentState L K)}
    (hInv : CorridorInvariant sigma c)
    (hreach : (NonuniformMajority L K).Reachable c d) :
    CorridorInvariant sigma d := by
  induction hreach with
  | refl => exact hInv
  | tail _ hstep ih => exact CorridorInvariant_stepRel sigma ih hstep

/-- Clause (a) extracted globally. -/
theorem CorridorInvariant_minorityU_eq_zero
    (sigma : Sign) (c : Config (AgentState L K))
    (hInv : CorridorInvariant sigma c) :
    minorityU sigma c = 0 := by
  classical
  unfold minorityU
  rw [Multiset.countP_eq_zero]
  intro a ha hminor
  rcases hInv.1 a ha with h | h
  · exact h.2 hminor
  · exact h.2.1 hminor

/-- Once a majority-biased Main is in Phase 9, its correct bit is present. -/
theorem majority_bit_of_phaseNineAgent
    (sigma : Sign) (a : AgentState L K)
    (h : PhaseNineAgent sigma a)
    (hmajor : majorityBiasedSt sigma a) :
    LateLemmaFourteenSpreads.opinionCarrier
      (majorityOutput sigma) a.opinions :=
  h.2.2.2 hmajor

/-- All-Phase-9 handoff to the already landed spread invariant. -/
theorem opinionSpreadPre_of_corridor_all_nine
    (sigma : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : CorridorInvariant sigma c)
    (hcard : c.card = n)
    (hall : ∀ a ∈ c, a.phase.val = 9) :
    LateLemmaFourteenSpreads.OpinionSpreadPre
      (majorityOutput sigma) n c := by
  classical
  have hmajor := hInv.2
  unfold majorityBiasedCount at hmajor
  rw [Multiset.countP_pos] at hmajor
  obtain ⟨a, ha, hma⟩ := hmajor
  have haInv := hInv.1 a ha
  have haNine : PhaseNineAgent sigma a := by
    rcases haInv with haEight | haNine
    · have := hall a ha
      have := haEight.1
      omega
    · exact haNine
  refine ⟨hcard, ?_, ?_⟩
  · intro b hb
    have hbInv := hInv.1 b hb
    rcases hbInv with hbEight | hbNine
    · have := hall b hb
      have := hbEight.1
      omega
    · exact ⟨hbNine.1, hbNine.2.2.1⟩
  · unfold LateLemmaFourteenSpreads.opinionCount
    exact Nat.succ_le_of_lt (Multiset.countP_pos.mpr ⟨a, ha, haNine.2.2.2 hma⟩)

section LemmaThirteenHandoff

variable {n M R : ℕ}
variable {init : InputCfg n} {omega : InputLog n}
variable {completed seven homogeneousSeven eight homogeneousEight t : ℕ}
variable {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
variable {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
variable {sigma tau : Sign}

/-- The invariant is already true at the exact Lemma-13 handoff time. -/
theorem corridorInvariant_at_lemmaThirteenTime
    (h : LemmaThirteenSmallGapReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight homogeneousEight t
      ell hell sigma tau) :
    CorridorInvariant
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      sigma (trace init omega t) := by
  classical
  have htWork : t ≤ phaseEightWorkEnd n homogeneousEight := by
    simpa [phaseEightWorkEnd, phaseEightDrainHorizon] using h.deadline
  have hb := lemmaThirteenRouteReceipt_bounds_at
    h.route h.homogeneous_le htWork
  have hNo : ∀ a ∈ trace init omega t, ¬ minoritySt sigma a := by
    have hz := h.no_minority
    unfold minorityU at hz
    rw [Multiset.countP_eq_zero] at hz
    exact hz
  have hn : 0 < n := by
    have hnlarge := (time_population_bounds h.route.twelve.path.good_input.1).2
    omega
  have hscaled := hb.2.2.2.2
  rw [h.no_minority, Nat.sub_zero] at hscaled
  have havail : 0 < availableMajorityCount sigma (trace init omega t) := by
    omega
  have hmajor : 0 < majorityBiasedCount sigma (trace init omega t) := by
    unfold availableMajorityCount at havail
    rw [Multiset.countP_pos] at havail
    obtain ⟨a, ha, hma⟩ := havail
    unfold majorityBiasedCount
    rw [Multiset.countP_pos]
    exact ⟨a, ha, hma.1⟩
  refine ⟨?_, hmajor⟩
  intro a ha
  exact Or.inl ⟨h.phase_win.2 a ha, hNo a ha⟩

/-- Propagation along the actual trace, with no additional corridor premise. -/
theorem corridorInvariant_trace_from_lemmaThirteen
    (h : LemmaThirteenSmallGapReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight homogeneousEight t
      ell hell sigma tau)
    {u : ℕ} (htu : t ≤ u) :
    CorridorInvariant
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      sigma (trace init omega u) :=
  CorridorInvariant_reachable sigma
    (corridorInvariant_at_lemmaThirteenTime h)
    (trace_reachable init omega htu)

end LemmaThirteenHandoff

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenInvariant

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenInvariant
open TimeTheorem TraceDrain LateLemmaThirteenSmallGap LateLemmaFourteenSpreads
open LateLemmaFourteenCleanup LateTimerProtectionOriginalLaw

variable {n M R : ℕ}
variable {init : InputCfg n} {omega : InputLog n}
variable {completed seven homogeneousSeven eight homogeneousEight t : ℕ}
variable {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
variable {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
variable {sigma tau : Sign}

/-- Every state after the Lemma 13 handoff stays below backup. -/
theorem phase_ceiling_of_lemmaThirteen
    (h : LemmaThirteenSmallGapReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight homogeneousEight t
      ell hell sigma tau)
    {u : ℕ} (htu : t ≤ u) :
    ∀ a ∈ trace init omega u, a.phase.val ≤ 9 := by
  intro a ha
  rcases (corridorInvariant_trace_from_lemmaThirteen h htu).1 a ha with he | hn
  · have := he.1
    omega
  · have := hn.1
    omega

/-- The first spread and the receipt produce a homogeneous, compatible state with a majority carrier. -/
theorem opinionSpreadPre_of_receipt
    (h : LemmaThirteenSmallGapReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight homogeneousEight t
      ell hell sigma tau)
    (firstNine : ℕ) (hcard : init.card = n)
    (hfirst : phaseSeedTime init 9 omega = (firstNine : WithTop ℕ))
    (hthreshold : omega ∉ phaseNineSpreadFailure init) :
    OpinionSpreadPre (majorityOutput sigma) n
      (trace init omega (firstNine + logWindow n 4)) := by
  have htfirst : t < firstNine := by
    have hb := h.before_nine
    rw [hfirst] at hb
    exact_mod_cast hb
  have htend : t ≤ firstNine + logWindow n 4 := by omega
  have hentry := phase_ceiling_of_lemmaThirteen h (Nat.le_of_lt htfirst)
  have hceiling := phase_ceiling_of_lemmaThirteen h htend
  have hall := phaseNineExactly_of_time_and_ceiling init omega firstNine
    hfirst hentry hthreshold hceiling
  apply opinionSpreadPre_of_corridor_all_nine sigma n _
    (corridorInvariant_trace_from_lemmaThirteen h htend) _ hall
  have hc := Protocol.reachable_card_eq
    (trace_reachable init omega (s := 0) (t := firstNine + logWindow n 4) (by omega))
  simpa only [TimeTheorem.trace_zero, hcard] using hc

/-- The Lemma 13 receipt supplies every observed premise of the two-spread cleanup bound. -/
theorem lemma_fourteen_cleanup_start_le_of_receipt
    (h : LemmaThirteenSmallGapReceipt (M := M) (R := R)
      init omega completed seven homogeneousSeven eight homogeneousEight t
      ell hell sigma tau)
    (firstNine : ℕ) (hcard : init.card = n)
    (hfirst : phaseSeedTime init 9 omega = (firstNine : WithTop ℕ))
    (hthreshold : omega ∉ phaseNineSpreadFailure init)
    (hbit : omega ∉ majorityBitSpreadFailure init (majorityOutput sigma)) :
    cleanupStart init (majorityOutput sigma) n omega ≤
      ((firstNine + logWindow n 4 + logWindow n 4 : ℕ) : WithTop ℕ) := by
  have htfirst : t < firstNine := by
    have hb := h.before_nine
    rw [hfirst] at hb
    exact_mod_cast hb
  have hentry := phase_ceiling_of_lemmaThirteen h (Nat.le_of_lt htfirst)
  have htend : t ≤ firstNine + logWindow n 4 := by omega
  have hceiling := phase_ceiling_of_lemmaThirteen h htend
  have hall := phaseNineExactly_of_time_and_ceiling init omega firstNine
    hfirst hentry hthreshold hceiling
  have hInv := corridorInvariant_trace_from_lemmaThirteen h htend
  have hnone : NoOppositeBit (majorityOutput sigma)
      (trace init omega (firstNine + logWindow n 4)) := by
    intro a ha
    rcases hInv.1 a ha with he | hn
    · have := hall a ha
      have := he.1
      omega
    · exact hn.2.2.1
  have hseed : ∃ a ∈ trace init omega (firstNine + logWindow n 4),
      opinionCarrier (majorityOutput sigma) a.opinions := by
    classical
    have hm := hInv.2
    unfold LateLemmaThirteenDeterministic.majorityBiasedCount at hm
    obtain ⟨a, ha, hmajor⟩ := Multiset.countP_pos.mp hm
    refine ⟨a, ha, ?_⟩
    rcases hInv.1 a ha with he | hn
    · have := hall a ha
      have := he.1
      omega
    · exact hn.2.2.2 hmajor
  exact lemma_fourteen_cleanup_start_le init (majorityOutput sigma) omega firstNine
    hcard hfirst hentry hceiling hnone hseed hthreshold hbit

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenInvariant

end
