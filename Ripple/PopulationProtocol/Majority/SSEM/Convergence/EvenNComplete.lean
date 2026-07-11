/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Even-n Master Theorem Without hStrictMajority

Eliminates the `hStrictMajority` hypothesis from the even-n master
theorem by handling ties (nA = nB) via `DecisionTieCase` and strict
majority via the existing `DecisionReach` infrastructure.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.TieCaseWitness
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.MacroStepComposition

namespace SSEM

variable {n : ℕ}

/-- Even-n decision phase reachability WITHOUT strict-majority hypothesis.
Case-splits on tie vs strict majority internally. -/
theorem decision_reaches_consensus_full_even_no_strict_majority
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : n % 2 = 0)
    (hn_ge_4 : 4 ≤ n)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply decision_reaches_consensus_of_macroStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  classical
  by_cases h_med_wrong : ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                       (C μ).1.answer ≠ majorityAnswer C
  · -- Median is wrong. Sub-case on tie vs strict majority.
    by_cases hTie : nAOf C = nBOf C
    · -- TIE case: use disagreed-inputs decision step
      obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
        evenCase_witness_when_median_wrong_tie hC hpar hn_ge_4 hTie h_med_wrong
      refine ⟨fun _ => (u, v), 1, ?_, ?_⟩
      · exact (decision_step_at_median_pair_even_tie_decreases
          hRank hC huv hpar hu_med hv_upper h_disagree hTie hn_ge_4 h_wrong).1
      · exact (decision_step_at_median_pair_even_tie_decreases
          hRank hC huv hpar hu_med hv_upper h_disagree hTie hn_ge_4 h_wrong).2
    · -- STRICT MAJORITY case: use existing agreed-inputs decision step
      have hne : nAOf C ≠ nBOf C := hTie
      obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
        evenCase_witness_when_median_wrong hC hpar hn_ge_4 hne h_med_wrong
      refine ⟨fun _ => (u, v), 1, ?_, ?_⟩
      · exact (decision_step_at_median_pair_even_decreases
          hRank hC huv hpar hu_med hv_upper h_agree hne hn_ge_4 h_wrong).1
      · exact (decision_step_at_median_pair_even_decreases
          hRank hC huv hpar hu_med hv_upper h_agree hne hn_ge_4 h_wrong).2
  · -- Median is correct. Use Burman macro-step.
    push_neg at h_med_wrong
    exact hBurman C hC hpos h_med_wrong

/-- Even-n SolvesSSEM WITHOUT hStrictMajority. -/
theorem P_EM_solves_SSEM_even_no_strict_majority
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : n % 2 = 0)
    (hn_ge_4 : 4 ≤ n)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_via_phases hRank h_burman_ranking
    (swap_reaches_Sswap_via_8way_with_timer_invariant hRank hn_ge_4 h_inv_swap)
    (decision_reaches_consensus_full_even_no_strict_majority hRank hpar hn_ge_4 hBurman)

/-- **Combined parity-agnostic SolvesSSEM WITHOUT hStrictMajority.**
This replaces `P_EM_solves_SSEM_fully_discharged_modulo_burman` with
one fewer hypothesis. -/
theorem P_EM_solves_SSEM_no_strict_majority
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer)
    (h_inv_dec : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                  ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  1 ≤ (C μ).1.timer) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  by_cases hpar : n % 2 = 0
  · exact P_EM_solves_SSEM_even_no_strict_majority
      hRank hpar hn4 hBurman h_burman_ranking h_inv_swap
  · exact P_EM_solves_SSEM_fully_discharged_odd_modulo_burman
      hRank hpar hn4 hBurman h_burman_ranking h_inv_swap h_inv_dec

/-- `h_inv_dec` (timer ≥ 1 at InSswap) follows from `h_inv_swap`
(timer ≥ 2 at InSrank) because InSswap ⊆ InSrank. -/
theorem h_inv_dec_of_h_inv_swap
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (C μ).1.timer :=
  fun C hC μ hμ => le_trans (by omega : 1 ≤ 2) (h_inv_swap C hC.toInSrank μ hμ)

/-- **Ultimate Theorem 4: P_EM solves SSEM.**

Takes only THREE external hypotheses:
  1. `BurmanRankingCorrect` — ranking + epidemic + swap convergence
  2. `h_burman_ranking` — raw ranking convergence (from any config)
  3. `h_inv_swap` — timer ≥ 2 at InSrank (median agent)

`h_inv_dec` is derived from `h_inv_swap` (InSswap ⊆ InSrank).
`hStrictMajority` eliminated via tie-case handling.
`BurmanMacroDecision` discharged from `BurmanRankingCorrect`. -/
theorem P_EM_solves_SSEM_ultimate
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (hBRC : BurmanRankingCorrect trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (h_inv_swap : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                    2 ≤ (C μ).1.timer) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_no_strict_majority hRank hn4
    (discharge_BurmanMacroDecision hBRC (by omega))
    h_burman_ranking h_inv_swap (h_inv_dec_of_h_inv_swap h_inv_swap)

end SSEM
