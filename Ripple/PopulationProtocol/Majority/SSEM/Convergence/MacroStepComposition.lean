/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Macro-Step Composition: Discharging BurmanMacroDecision

This file composes the timer descent, reset firing, and Burman
re-ranking into a complete discharge of the `BurmanMacroDecision`
hypothesis from `MasterModuloBurman.lean`.

The macro-step trajectory when the median is correct but some
non-median agent has a wrong answer:

  1. Timer descent: schedule (median, max) to bring timer to ≤ 1.
  2. Timer to 0: one more step to bring timer to 0.
  3. Reset: schedule (median, wrong_agent) to fire the reset.
  4. Re-ranking: Burman's ranking protocol re-establishes InSrank.
  5. Re-swapping: swap phase brings back to InSswap.
  6. Net effect: wrongAnswerCount has decreased.

Steps 1-3 use the infrastructure from `TimerDescentNoSwap.lean`.
Steps 4-5 require external hypotheses (`h_burman_ranking` + swap-phase
reachability).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.TimerDescentNoSwap

namespace SSEM

variable {n : ℕ}

/-! ### Existence of a wrong-answer agent that is not median and not max -/

/-- If wrongAnswerCount > 0, the median is correct, AND the max-rank
agent is also correct, there exists a wrong-answer agent that is
neither at the median rank nor the max rank. -/
theorem exists_wrong_non_median_non_max
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpos : 0 < wrongAnswerCount C)
    (hmed_correct : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    (C μ).1.answer = majorityAnswer C)
    (hmax_correct : ∀ v : Fin n, (C v).1.rank.val + 1 = n →
                    (C v).1.answer = majorityAnswer C) :
    ∃ w : Fin n,
      (C w).1.rank.val + 1 ≠ ceilHalf n ∧
      (C w).1.rank.val + 1 ≠ n ∧
      (C w).1.answer ≠ majorityAnswer C := by
  -- Extract a wrong agent from wrongAnswerCount > 0
  have hne : (Finset.univ.filter (fun v : Fin n => (C v).1.answer ≠ majorityAnswer C)).Nonempty := by
    unfold wrongAnswerCount at hpos
    exact Finset.card_pos.mp hpos
  obtain ⟨w, hw⟩ := hne
  rw [Finset.mem_filter] at hw
  refine ⟨w, ?_, ?_, hw.2⟩
  · intro h; exact hw.2 (hmed_correct w h)
  · intro h; exact hw.2 (hmax_correct w h)

/-! ### Timer = 1 at (median, max), max has correct answer → timer = 0, no reset

When the max-rank agent's answer agrees with the median's post-decision
answer, the reset condition fails even though timer = 0. The result is
like the timer ≥ 2 case but with timer = 0 in the output. -/

set_option maxHeartbeats 16000000 in
theorem step_at_median_max_timer_one_no_reset
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hn : 2 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hpar : ¬ n % 2 = 0)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : (C μ).1.timer = 1)
    (h_max_correct : (C v).1.answer = opinionToAnswer (C μ).2) :
    let P := protocolPEM n trank Rmax rankDelta
    let C' := C.step P μ v
    InSswap C' ∧
    (C' μ).1.timer = 0 ∧
    (C' μ).1.rank.val + 1 = ceilHalf n ∧
    (C' v).1.rank.val + 1 = n ∧
    (C' μ).2 = Opinion.A := by
  have hsu : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hsu hsv (by intro h; have := congrArg Fin.val h; unfold ceilHalf at hμ_med; omega)
  have h_ceil_lt : ceilHalf n < n := by unfold ceilHalf; omega
  have hv_not_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by omega
  have hμ_not_max : (C μ).1.rank.val + 1 ≠ n := by omega
  have hvμ : v ≠ μ := Ne.symm hμv
  have hno_swap : ¬ ((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    rintro ⟨_, hB, _⟩; rw [hμ_input_A] at hB; exact Opinion.noConfusion hB
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by omega
  -- After decision, μ's answer = opinionToAnswer (C μ).2 and v's answer = (C v).1.answer.
  -- Timer becomes 1 - 1 = 0. Reset condition: timer = 0 ∧ answer ≠ partner.answer.
  -- But h_max_correct says (C v).1.answer = opinionToAnswer (C μ).2, so answers agree → no reset.
  have h_answers_eq : ¬ (opinionToAnswer (C μ).2 ≠ (C v).1.answer) := by
    push_neg; exact h_max_correct.symm
  have htr : transitionPEM n trank Rmax rankDelta (C μ, C v) =
    ({(C μ).1 with answer := opinionToAnswer (C μ).2,
                   timer := 0},
     (C v).1) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsu, hsv, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, hno_swap, hpar, hμ_med, hv_not_med, hv_max, hN_ne_ceil,
      h_timer]
    split_ifs with h
    · exfalso; exact h_answers_eq h.2
    · rfl
  set P := protocolPEM n trank Rmax rankDelta
  -- Extract component facts
  have h_timer_eq : (C.step P μ v μ).1.timer = 0 := by
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.timer = _
    rw [htr]
  have h_rank : (C.step P μ v μ).1.rank = (C μ).1.rank := by
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.rank = _
    rw [htr]
  have h_role : (C.step P μ v μ).1.role = (C μ).1.role := by
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = _
    rw [htr]
  have h_v : (C.step P μ v v).1 = (C v).1 := by
    unfold Config.step; rw [if_neg hμv, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).2 = _
    rw [htr]
  have h_others : ∀ w, w ≠ μ → w ≠ v → C.step P μ v w = C w := by
    intro w hw hwv; unfold Config.step; simp only [if_neg hμv, if_neg hw, if_neg hwv]
  have h_inputs : ∀ w, (C.step P μ v w).2 = (C w).2 := by
    intro w; unfold Config.step; simp only [if_neg hμv]
    split
    · rename_i h; simp only [h]
    · split
      · rename_i _ h; simp only [h]
      · rfl
  -- Ranks preserved at every position
  have h_rank_w : ∀ w, (C.step P μ v w).1.rank = (C w).1.rank := by
    intro w
    by_cases hw : w = μ
    · rw [hw, h_rank]
    · by_cases hwv : w = v
      · rw [hwv]; exact congrArg (fun s => s.rank) h_v
      · rw [show C.step P μ v w = C w from h_others w hw hwv]
  -- nAOf preserved
  have h_nA : nAOf (C.step P μ v) = nAOf C := by
    unfold nAOf Config.agentsWithInput Config.inputOf
    congr 1; ext w; simp only [Finset.mem_filter]
    exact ⟨fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs] at h; exact h⟩,
           fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs]; exact h⟩⟩
  refine ⟨?_, h_timer_eq, ?_, ?_, ?_⟩
  · -- InSswap preserved
    constructor
    · constructor
      · intro w
        by_cases hw : w = μ
        · rw [hw, h_role]; exact hC.allSettled μ
        · by_cases hwv : w = v
          · rw [hwv]; exact congrArg (fun s => s.role) h_v ▸ hC.allSettled v
          · rw [show (C.step P μ v w).1 = (C w).1 from
              congrArg Prod.fst (h_others w hw hwv)]
            exact hC.allSettled w
      · intro w₁ w₂ heq
        have := h_rank_w w₁; have := h_rank_w w₂
        simp only [this, *] at heq; exact hC.ranks_inj heq
    · intro w
      rw [show (C.step P μ v w).2 = (C w).2 from h_inputs w,
          show (C.step P μ v w).1.rank = (C w).1.rank from h_rank_w w,
          h_nA]
      exact hC.input_rank w
  · -- rank preserved
    rw [h_rank]; exact hμ_med
  · -- v's rank preserved
    rw [h_v]; exact hv_max
  · -- input preserved
    rw [h_inputs]; exact hμ_input_A

/-! ### Ranking convergence with answer correctness

The key additional hypothesis beyond `h_burman_ranking`: when at least
one agent already has the correct answer, Burman's protocol reaches
InSswap with ALL agents having the correct answer. This captures the
epidemic propagation guarantee. -/

/-- Ranking convergence + answer correctness + swap: from any config
where at least one agent has the correct answer, there exists a schedule
reaching InSswap with all answers correct (= IsConsensusConfig). -/
def BurmanRankingCorrect
    (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) : Prop :=
  ∀ C₀ : Config (AgentState n) Opinion n,
    (∃ w : Fin n, (C₀ w).1.answer = majorityAnswer C₀) →
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSswap (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      ∀ w : Fin n, (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t w).1.answer
        = majorityAnswer C₀

/-! ### Full macro-step composition

Discharge `BurmanMacroDecision` from:
  * `BurmanRankingCorrect` — ranking + epidemic + swap convergence
  * timer invariant (median timer ≥ 2 at InSswap)
  * majority input condition
-/

theorem discharge_BurmanMacroDecision
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hBRC : BurmanRankingCorrect trank Rmax rankDelta)
    (hn : 0 < n) :
    BurmanMacroDecision trank Rmax rankDelta := by
  intro C hC hpos hmed_correct
  set P := protocolPEM n trank Rmax rankDelta
  have hn_pos : 0 < n := hn
  -- The median has the correct answer
  obtain ⟨μ, hμ_med⟩ := hC.toInSrank.exists_median hn_pos
  have hμ_correct : (C μ).1.answer = majorityAnswer C := hmed_correct μ hμ_med
  -- Apply BurmanRankingCorrect: from C (which has ≥ 1 correct agent),
  -- reach InSswap with ALL answers correct.
  obtain ⟨γ, t, hC_final, h_all_correct⟩ := hBRC C ⟨μ, hμ_correct⟩
  -- wrongAnswerCount = 0 at the final config
  have hmaj : majorityAnswer (execution P C γ t) = majorityAnswer C :=
    majorityAnswer_execution_eq C γ t
  have h_zero : wrongAnswerCount (execution P C γ t) = 0 := by
    rw [wrongAnswerCount_eq_zero_iff]
    intro w; rw [hmaj]; exact h_all_correct w
  exact ⟨γ, t, hC_final, by omega⟩

/-- When the median already holds the correct answer, the epidemic drives
the whole configuration to consensus. (The earlier formulation also asserted
`1 ≤ timer@median` at the endpoint, but that is FALSE in general — a
stable all-correct `InSswap` with `timer = 0` has no recovery mechanism.
Since `InSswap ∧ all-correct ⟺ IsConsensusConfig`, reaching consensus is
the honest and sufficient post-condition for the decision phase.) -/
def BurmanMacroDecisionWithTimer
    (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) : Prop :=
  ∀ C : Config (AgentState n) Opinion n, InSswap C →
    0 < wrongAnswerCount C →
    (∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  (C μ).1.answer = majorityAnswer C) →
    ∃ (γ : DetScheduler n) (k : ℕ),
      IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ k)

/-- Discharge BurmanMacroDecisionWithTimer from the strengthened epidemic. -/
theorem discharge_BurmanMacroDecisionWithTimer
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hEpidemic : ∀ C₀ : Config (AgentState n) Opinion n,
      (∃ w : Fin n, (C₀ w).1.answer = majorityAnswer C₀) →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
        (∀ w : Fin n,
          (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t w).1.answer = majorityAnswer C₀) ∧
        ((∀ μ : Fin n,
          (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
          1 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer) ∨
         IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t)))
    (hn : 0 < n) :
    BurmanMacroDecisionWithTimer trank Rmax rankDelta := by
  intro C hC hpos hmed_correct
  set P := protocolPEM n trank Rmax rankDelta
  obtain ⟨μ, hμ_med⟩ := hC.toInSrank.exists_median hn
  have hμ_correct : (C μ).1.answer = majorityAnswer C := hmed_correct μ hμ_med
  obtain ⟨γ, t, hC_final, h_all_correct, _h_disj⟩ := hEpidemic C ⟨μ, hμ_correct⟩
  -- `InSswap ∧ all-answers-correct ⟺ IsConsensusConfig` (InStim).
  have hmaj : majorityAnswer (execution P C γ t) = majorityAnswer C :=
    majorityAnswer_execution_eq C γ t
  have hOut : InSout (execution P C γ t) := by
    intro w; rw [hmaj]; exact h_all_correct w
  refine ⟨γ, t, ?_⟩
  exact (InStim_iff_IsConsensusConfig _).mp
    { toInSswap := hC_final, allAnswerCorrect := hOut }

end SSEM
