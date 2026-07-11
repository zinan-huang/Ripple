/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Master Theorem 4 modulo Burman 2021

This file consolidates the complete formal proof of Theorem 4 of Kanaya
et al. (2025) into one statement, modulo a single Burman-2021 hypothesis
that bundles three external pieces:

  1. Burman's ranking convergence (PODC 2021).
  2. Reset-cycle return to `InSrank`.
  3. Macro-step decision-phase progress when the median is already
     correct but some non-median agent is wrong.

The first three components correspond to phases A, B, C of the
macro-step plan; the fourth component (decision-phase progress for the
median-wrong case) is closed unconditionally in `DecisionReach.lean`
and used by name here.

## Master statements

  * `P_EM_solves_SSEM_full_odd_modulo_burman`
  * `P_EM_solves_SSEM_full_even_modulo_burman`
  * `P_EM_solves_SSEM_full_modulo_burman`

Each takes the bundled Burman hypothesis and the structural witnesses
(four-way swap-step existence, median-wrong/median-pair decision-step
existence) and concludes `SolvesSSEM`.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.DecisionReach

namespace SSEM

variable {n : ℕ}

/-! ### The bundled Burman + reset-cycle hypothesis

`hBurmanMacro` says: from any `InSswap` configuration with some non-median
agent's answer differing from the majority (and the median already
correct), some multi-step trajectory exists that returns to `InSswap`
with strictly smaller `wrongAnswerCount`.

This is the residue of phases A, B, C of the macro-step plan: timer
descent, reset firing, epidemic propagation, and Burman re-settle all
combine to give this multi-step decrease.  Treating it as a single named
hypothesis lets us close `Theorem 4` modulo precisely one external
assumption tied to Burman 2021.
-/

/-- The bundled Burman + reset-cycle hypothesis. -/
def BurmanMacroDecision
    (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) : Prop :=
  ∀ C : Config (AgentState n) Opinion n, InSswap C →
    0 < wrongAnswerCount C →
    (∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                  (C μ).1.answer = majorityAnswer C) →
    ∃ (γ : DetScheduler n) (k : ℕ),
      InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ k) ∧
      wrongAnswerCount (execution (protocolPEM n trank Rmax rankDelta) C γ k)
        < wrongAnswerCount C

/-! ### Decision-phase reachability — full (modulo Burman) -/

/-- From `BurmanMacroDecision` and a witness for the median-wrong-decision
single-step (odd `n`), every `InSswap` configuration reaches a consensus
configuration. -/
theorem decision_reaches_consensus_full_odd
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : ¬ n % 2 = 0)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (hMedianWrongExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                            0 < wrongAnswerCount C →
                            (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                          (C μ).1.answer ≠ majorityAnswer C) →
                            ∃ μ v : Fin n, μ ≠ v ∧
                              (C μ).1.rank.val + 1 = ceilHalf n ∧
                              (C v).1.rank.val + 1 ≠ ceilHalf n ∧
                              (C v).1.rank.val + 1 ≠ n ∧
                              (C v).1.rank < (C μ).1.rank ∧
                              1 ≤ (C μ).1.timer ∧
                              (C μ).1.answer ≠ majorityAnswer C) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply decision_reaches_consensus_of_macroStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  classical
  -- Case-split on whether the median is correct or wrong.
  by_cases h_med_wrong :
      ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                   (C μ).1.answer ≠ majorityAnswer C
  · -- Median is wrong.  Use the single-step lemma.
    obtain ⟨μ, v, hμv, hμ_med, hv_no_med, hv_no_max, h_rank_gt, h_timer, h_μ_wrong⟩ :=
      hMedianWrongExists C hC hpos h_med_wrong
    refine ⟨fun _ => (μ, v), 1, ?_, ?_⟩
    · show InSswap ((execution (protocolPEM n trank Rmax rankDelta) C
        (fun _ => (μ, v)) 0).step (protocolPEM n trank Rmax rankDelta) μ v)
      show InSswap (C.step (protocolPEM n trank Rmax rankDelta) μ v)
      exact (decision_step_at_median_no_swap_odd_decreases
        hRank hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong).1
    · show wrongAnswerCount ((execution (protocolPEM n trank Rmax rankDelta) C
        (fun _ => (μ, v)) 0).step (protocolPEM n trank Rmax rankDelta) μ v) < _
      show wrongAnswerCount (C.step (protocolPEM n trank Rmax rankDelta) μ v) < _
      exact (decision_step_at_median_no_swap_odd_decreases
        hRank hC hμv hpar hμ_med hv_no_med hv_no_max h_rank_gt h_timer h_μ_wrong).2
  · -- Median is correct.  Use Burman macro-step.
    push_neg at h_med_wrong
    -- After push_neg, h_med_wrong : ∀ μ, (C μ).1.rank.val + 1 = ceilHalf n →
    --                                    (C μ).1.answer = majorityAnswer C.
    exact hBurman C hC hpos h_med_wrong

/-! ### Master Theorem 4 (modulo Burman, odd n) -/

/-- Theorem 4 for odd `n`, modulo the bundled `BurmanMacroDecision`
hypothesis, the four-way swap-step existence, the median-wrong-decision
existence, and Burman's ranking convergence. -/
theorem P_EM_solves_SSEM_full_odd_modulo_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : ¬ n % 2 = 0)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hSwapExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    0 < misorderedCount C →
                    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
                       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)))
    (hMedianWrongExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                            0 < wrongAnswerCount C →
                            (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                          (C μ).1.answer ≠ majorityAnswer C) →
                            ∃ μ v : Fin n, μ ≠ v ∧
                              (C μ).1.rank.val + 1 = ceilHalf n ∧
                              (C v).1.rank.val + 1 ≠ ceilHalf n ∧
                              (C v).1.rank.val + 1 ≠ n ∧
                              (C v).1.rank < (C μ).1.rank ∧
                              1 ≤ (C μ).1.timer ∧
                              (C μ).1.answer ≠ majorityAnswer C) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_via_phases hRank h_burman_ranking
    (swap_reaches_Sswap_via_four_way hRank hSwapExists)
    (decision_reaches_consensus_full_odd hRank hpar hBurman hMedianWrongExists)

/-! ### Decision-phase reachability — full (modulo Burman, even n) -/

/-- Even-n companion of `decision_reaches_consensus_full_odd`.  Uses
the median-pair decision-step lemma when the lower median is wrong, and
`BurmanMacroDecision` otherwise. -/
theorem decision_reaches_consensus_full_even
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : n % 2 = 0)
    (hn_ge_4 : 4 ≤ n)
    (hStrictMajority : ∀ C : Config (AgentState n) Opinion n,
                          InSswap C → nAOf C ≠ nBOf C)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (hMedianPairExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                            0 < wrongAnswerCount C →
                            (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                          (C μ).1.answer ≠ majorityAnswer C) →
                            ∃ u v : Fin n, u ≠ v ∧
                              (C u).1.rank.val + 1 = n / 2 ∧
                              (C v).1.rank.val + 1 = n / 2 + 1 ∧
                              (C u).2 = (C v).2 ∧
                              ((C u).1.answer ≠ majorityAnswer C ∨
                               (C v).1.answer ≠ majorityAnswer C)) :
    ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply decision_reaches_consensus_of_macroStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  classical
  by_cases h_med_wrong :
      ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                   (C μ).1.answer ≠ majorityAnswer C
  · obtain ⟨u, v, huv, hu_med, hv_upper, h_inputs_agree, h_one_wrong⟩ :=
      hMedianPairExists C hC hpos h_med_wrong
    refine ⟨fun _ => (u, v), 1, ?_, ?_⟩
    · show InSswap (C.step (protocolPEM n trank Rmax rankDelta) u v)
      exact (decision_step_at_median_pair_even_decreases
        hRank hC huv hpar hu_med hv_upper h_inputs_agree (hStrictMajority C hC)
        hn_ge_4 h_one_wrong).1
    · show wrongAnswerCount (C.step (protocolPEM n trank Rmax rankDelta) u v) < _
      exact (decision_step_at_median_pair_even_decreases
        hRank hC huv hpar hu_med hv_upper h_inputs_agree (hStrictMajority C hC)
        hn_ge_4 h_one_wrong).2
  · push_neg at h_med_wrong
    exact hBurman C hC hpos h_med_wrong

/-! ### Master Theorem 4 (modulo Burman, even n) -/

/-- Theorem 4 for even `n`, modulo the bundled Burman hypotheses. -/
theorem P_EM_solves_SSEM_full_even_modulo_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hpar : n % 2 = 0)
    (hn_ge_4 : 4 ≤ n)
    (hStrictMajority : ∀ C : Config (AgentState n) Opinion n,
                          InSswap C → nAOf C ≠ nBOf C)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hSwapExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    0 < misorderedCount C →
                    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
                       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)))
    (hMedianPairExists : ∀ C : Config (AgentState n) Opinion n, InSswap C →
                            0 < wrongAnswerCount C →
                            (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                          (C μ).1.answer ≠ majorityAnswer C) →
                            ∃ u v : Fin n, u ≠ v ∧
                              (C u).1.rank.val + 1 = n / 2 ∧
                              (C v).1.rank.val + 1 = n / 2 + 1 ∧
                              (C u).2 = (C v).2 ∧
                              ((C u).1.answer ≠ majorityAnswer C ∨
                               (C v).1.answer ≠ majorityAnswer C)) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_via_phases hRank h_burman_ranking
    (swap_reaches_Sswap_via_four_way hRank hSwapExists)
    (decision_reaches_consensus_full_even hRank hpar hn_ge_4 hStrictMajority hBurman
      hMedianPairExists)

/-! ### Master Theorem 4 (parity-combined, modulo Burman) -/

/-- The combined Theorem 4 statement: `P_EM` solves SSEM modulo:
  * `RankDeltaSettledFix` (trivial),
  * Burman ranking convergence (`h_burman_ranking`),
  * Bundled `BurmanMacroDecision` (median-correct macro-step),
  * `hSwapExists` (four-way swap-step witness),
  * `hMedianWitnessExists` — for ANY parity, when median wrong, we can
    find a witness pair appropriate for the parity's single-step lemma.

For odd `n` (n % 2 = 1) the witness uses the no-swap (μ, v) form;
for even `n` (n % 2 = 0) the witness uses the median-pair form.  Both
are provided uniformly via two clauses inside the same hypothesis. -/
theorem P_EM_solves_SSEM_full_modulo_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hBurman : BurmanMacroDecision trank Rmax rankDelta)
    (h_burman_ranking : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hSwapExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                    0 < misorderedCount C →
                    ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                      (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                       (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
                       (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)))
    (hOddCase : ¬ n % 2 = 0 → ∀ C : Config (AgentState n) Opinion n, InSswap C →
                  0 < wrongAnswerCount C →
                  (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                (C μ).1.answer ≠ majorityAnswer C) →
                  ∃ μ v : Fin n, μ ≠ v ∧
                    (C μ).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧
                    (C v).1.rank < (C μ).1.rank ∧
                    1 ≤ (C μ).1.timer ∧
                    (C μ).1.answer ≠ majorityAnswer C)
    (hEvenCase : n % 2 = 0 → 4 ≤ n →
                  (∀ C : Config (AgentState n) Opinion n, InSswap C → nAOf C ≠ nBOf C) →
                  ∀ C : Config (AgentState n) Opinion n, InSswap C →
                  0 < wrongAnswerCount C →
                  (∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧
                                (C μ).1.answer ≠ majorityAnswer C) →
                  ∃ u v : Fin n, u ≠ v ∧
                    (C u).1.rank.val + 1 = n / 2 ∧
                    (C v).1.rank.val + 1 = n / 2 + 1 ∧
                    (C u).2 = (C v).2 ∧
                    ((C u).1.answer ≠ majorityAnswer C ∨
                     (C v).1.answer ≠ majorityAnswer C))
    (hEvenAux : n % 2 = 0 → 4 ≤ n ∧
                  (∀ C : Config (AgentState n) Opinion n, InSswap C → nAOf C ≠ nBOf C)) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  by_cases hpar : n % 2 = 0
  · obtain ⟨hn_ge_4, hStrictMaj⟩ := hEvenAux hpar
    exact P_EM_solves_SSEM_full_even_modulo_burman hRank hpar hn_ge_4
      hStrictMaj hBurman h_burman_ranking hSwapExists
      (hEvenCase hpar hn_ge_4 hStrictMaj)
  · exact P_EM_solves_SSEM_full_odd_modulo_burman hRank hpar hBurman
      h_burman_ranking hSwapExists (hOddCase hpar)

end SSEM
