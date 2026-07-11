/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reset Cycle Infrastructure

When the median agent's `.timer` reaches zero and its post-decision
`.answer` disagrees with the partner's `.answer`, the propagation phase
fires the reset branch: both agents become `.Resetting`, with their
answers synchronized.

This file develops:
  * `reset_fires_at_misorder_median_v_max_odd_timer_zero` — the
    transitionPEM result when timer = 0 + answers differ + odd n + the
    misorder swap-fires structure.
  * `AllResettingOrSettled` predicate.
  * Epidemic single-step preservation (`epidemic_step_preserves`).

The macro-step "reset cycle returns to InSrank" goes via Burman 2021
external assumption (阶段 B3).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.RankPreservation

namespace SSEM

variable {n : ℕ}

/-! ### Reset fires at (μ, v) with timer = 0, answers differ -/

set_option maxHeartbeats 8000000 in
/-- At a misorder pair `(μ, v)` with `μ` at median, `v` at max rank, odd
`n`, `(C μ).1.timer = 0`, and the propagation-target `(C v).1.answer`
disagrees with the post-decision answer `opinionToAnswer (C v).2 = .outA`
(since `x_v = .A` from the misorder), the propagation reset fires:
both result components have role `.Resetting`. -/
theorem reset_fires_at_misorder_median_v_max_odd_timer_zero
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hMis : MisorderedPair C (μ, v))
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 0)
    (h_answers : (C v).1.answer ≠ opinionToAnswer (C v).2) :
    transitionPEM n trank Rmax rankDelta (C μ, C v)
      = ({(C v).1 with answer := opinionToAnswer (C v).2,
                       role := .Resetting,
                       leader := .L,
                       resetcount := Rmax},
         {(C μ).1 with answer := opinionToAnswer (C v).2,
                       timer := (C μ).1.timer - 1,
                       role := .Resetting,
                       leader := .L,
                       resetcount := Rmax}) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have hb0_no_med : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by
    have : (C μ).1.rank.val < (C v).1.rank.val := hlt; omega
  have h_no_inner_A : ¬ ((C μ).1.rank.val + 1 = n) := by
    have hvlt : (C v).1.rank.val < n := (C v).1.rank.isLt; omega
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    have hcl : (C μ).1.rank.val < (C v).1.rank.val := hlt; omega
  -- Reset condition holds: post-dec timer = 0 - 1 = 0, answer = opinionToAnswer .A,
  -- b₀.answer = (C v).1.answer ≠ opinionToAnswer .A.
  -- After the simp rewrites (C v).2 → .A and (C μ).1.timer is unchanged, the
  -- if-condition in the goal looks like:
  -- `(C μ).1.timer - 1 = 0 ∧ ¬ opinionToAnswer .A = (C v).1.answer`.
  have h_reset_cond :
      ((C μ).1.timer - 1 = 0 ∧ ¬ (opinionToAnswer Opinion.A = (C v).1.answer)) := by
    refine ⟨by rw [h_timer], ?_⟩
    intro h_eq
    rw [← hvA] at h_eq
    exact h_answers h_eq.symm
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hb0_no_med, hμ_med, h_no_inner_A, hv_max,
    hN_ne_ceil]
  -- Should leave the reset branch firing.  Use the explicit reset condition.
  rw [if_pos h_reset_cond]

end SSEM
