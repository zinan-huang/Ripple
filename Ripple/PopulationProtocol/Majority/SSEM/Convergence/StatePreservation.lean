/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# State-Field Preservation through `transitionPEM`

`.role` and `.rank` are preserved by `transitionPEM` at a consensus
pair: every Phase-4 sub-case in which the propagation reset branch
would fire has `b₀.answer = b₁.answer` post-decision (by record
projection), so the reset trigger `b₀.answer ≠ b₁.answer` is `rfl`-false
and `split_ifs` can discharge those branches.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.AnswerPreservation

namespace SSEM

variable {n : ℕ}

set_option maxHeartbeats 16000000 in
/-- `.role` and `.rank` are preserved by `transitionPEM` at a consensus pair. -/
theorem transitionPEM_consensus_pair_role_rank
    {trank Rmax nA : ℕ} {a : Answer}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (hpair : ConsensusPair s₀ s₁ x₀ x₁ a nA)
    (hne : s₀.rank ≠ s₁.rank) :
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.role = s₀.role ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.role = s₁.role ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).1.rank = s₀.rank ∧
    (transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))).2.rank = s₁.rank := by
  have hRD : rankDelta (s₀, s₁) = (s₀, s₁) :=
    hRank s₀ s₁ hpair.settled₀ hpair.settled₁ hne
  have hs0 := hpair.settled₀
  have hs1 := hpair.settled₁
  have ha0 := hpair.answer₀
  have ha1 := hpair.answer₁
  have hswap := hpair.swap_fails
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hs0, hs1, hswap, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true]
  -- Closure tactic for each split_ifs leaf: success or reset-impossibility.
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true]
    by_cases h_lu : s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1
    · obtain ⟨hr0, hr1⟩ := h_lu
      simp only [hr0, hr1, and_self, if_true]
      by_cases hxx : x₀ = x₁
      · simp only [hxx, if_true]
        split_ifs <;>
          first
            | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
            | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›; exact hne rfl)
      · simp only [hxx, if_false]
        split_ifs <;>
          first
            | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
            | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›; exact hne rfl)
    · simp only [show ¬ (s₀.rank.val + 1 = n / 2 ∧ s₁.rank.val + 1 = n / 2 + 1)
        from h_lu, if_false]
      by_cases h_ul : s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1
      · obtain ⟨hr1, hr0⟩ := h_ul
        simp only [hr1, hr0, and_self, if_true]
        by_cases hxx : x₁ = x₀
        · simp only [hxx, if_true]
          split_ifs <;>
            first
              | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
              | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›; exact hne rfl)
        · simp only [hxx, if_false]
          split_ifs <;>
            first
              | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
              | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›; exact hne rfl)
      · simp only [show ¬ (s₁.rank.val + 1 = n / 2 ∧ s₀.rank.val + 1 = n / 2 + 1)
          from h_ul, if_false]
        -- Decision is no-op: b₀ = s₀, b₁ = s₁; ha0, ha1 give answer-equality.
        have hEq : s₀.answer = s₁.answer := ha0.trans ha1.symm
        first
          | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
          | (split_ifs <;>
              first
                | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
                | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›;
                    first | exact hne hEq | exact hne hEq.symm))
  · simp only [hpar, if_false]
    by_cases hb0 : s₀.rank.val + 1 = ceilHalf n
    · by_cases hb1 : s₁.rank.val + 1 = ceilHalf n
      · simp only [hb0, hb1, if_true]
        have hma0 := (hpair.decision_odd_match hpar).1 hb0
        have hma1 := (hpair.decision_odd_match hpar).2 hb1
        have hEq : opinionToAnswer x₀ = opinionToAnswer x₁ := hma0.trans hma1.symm
        split_ifs <;>
          first
            | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
            | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›;
                first | exact hne hEq | exact hne hEq.symm)
      · simp only [hb0, hb1, if_true, if_false]
        have hma0 := (hpair.decision_odd_match hpar).1 hb0
        have hEq : opinionToAnswer x₀ = s₁.answer := hma0.trans ha1.symm
        split_ifs <;>
          first
            | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
            | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›;
                first | exact hne hEq | exact hne hEq.symm)
    · by_cases hb1 : s₁.rank.val + 1 = ceilHalf n
      · simp only [hb0, hb1, if_true, if_false]
        have hma1 := (hpair.decision_odd_match hpar).2 hb1
        have hEq : s₀.answer = opinionToAnswer x₁ := ha0.trans hma1.symm
        split_ifs <;>
          first
            | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
            | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›;
                first | exact hne hEq | exact hne hEq.symm)
      · simp only [hb0, hb1, if_false]
        have hEq : s₀.answer = s₁.answer := ha0.trans ha1.symm
        first
          | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
          | (split_ifs <;>
              first
                | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
                | (exfalso; obtain ⟨_, hne⟩ := ‹_ ∧ _›;
                    first | exact hne hEq | exact hne hEq.symm))

end SSEM
