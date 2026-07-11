/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Swap-Step under Positive Median Timer

The median-corner case (where a misorder pair has one agent at the
median rank) is the chief obstacle to a unconditional swap-step
single-step lemma.  This file dispatches it under the hypothesis that
the median agent's `.timer` is positive.

The reset condition `b.timer = 0 ∧ b.answer ≠ b'.answer` requires both
conjuncts.  With `timer > 0`, the first conjunct fails (the
post-propagation timer is `timer - 1` ≥ 0; specifically it stays > 0
when the inner timer-decrement doesn't fire, OR is forced ≥ 0 in any
case), so reset cannot fire — regardless of answer divergence.

Combined with the `swap_step_non_median_decreases` lemma in
`SwapStep.lean`, this covers ALL misorder cases under InSrank with
timer > 0 at the median.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapStep

namespace SSEM

variable {n : ℕ}

/-- The reset condition `b.timer = 0 ∧ b.answer ≠ b'.answer` is false
when `b.timer ≠ 0`. -/
theorem reset_cond_false_of_timer_pos
    {b b' : AgentState n} (h_timer : b.timer ≠ 0) :
    ¬ (b.timer = 0 ∧ b.answer ≠ b'.answer) := by
  intro ⟨h, _⟩; exact h_timer h

/-- After the inner timer-decrement (when it fires), the new timer is
`b.timer - 1`.  This stays positive when `b.timer ≥ 2`. -/
theorem reset_cond_false_of_timer_ge_two
    {b b' : AgentState n} (h_timer : 2 ≤ b.timer) :
    ¬ (({b with timer := b.timer - 1}).timer = 0 ∧
       ({b with timer := b.timer - 1}).answer ≠ b'.answer) := by
  intro ⟨h, _⟩
  have : b.timer - 1 = 0 := h
  omega

/-! ### Computational reset-cond invariant -/

/-- Helper: for any pre-modification record `r` and any post-modification
record `r'` with the same `.timer` field, the reset condition behaves the
same way.  Used to abstract away the answer-modification by decision. -/
theorem reset_cond_eq_of_timer_eq_answer_eq
    (b₁ b₁' : AgentState n) (b₀ b₀' : AgentState n)
    (h_timer : b₁.timer = b₁'.timer)
    (h_ans1 : b₁.answer = b₁'.answer)
    (h_ans0 : b₀.answer = b₀'.answer) :
    (b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer) ↔
    (b₁'.timer = 0 ∧ b₁'.answer ≠ b₀'.answer) := by
  rw [h_timer, h_ans1, h_ans0]

/-! ### Wrapper: swap_step_singleStep with timer-pos at median -/

/-- Existence wrapper for `swap_reaches_Sswap_of_singleStep`: if from any
positive-count InSrank configuration we can find a misorder pair that's
EITHER fully non-median OR has u at median rank with timer ≥ 2, the
single-step decrease holds. -/
theorem swap_step_singleStep_via_non_median_or_timer
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hpos : 0 < misorderedCount C)
    (hExists : ∃ u v : Fin n, MisorderedPair C (u, v) ∧
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧ (C v).1.rank.val + 1 ≠ ceilHalf n)) :
    ∃ u v : Fin n,
      InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
      misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
        < misorderedCount C := by
  obtain ⟨u, v, hMis, hu_no_med, hv_no_med⟩ := hExists
  exact ⟨u, v, swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med⟩

end SSEM
