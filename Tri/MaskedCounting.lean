/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Progress

/-!
# A two-counter tail bound for masked adapted trials

`exposure` counts the steps on which a trial is offered, while `success`
counts successful offered trials.  The exponential potential
`η^exposure * w^success` supports occupation-time arguments without any
independence hypothesis.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- The exponential potential for a masked success counter. -/
noncomputable def maskedCountPotential
    (exposure success : α → ℕ) (η w : ℝ≥0∞) (s : α) : ℝ≥0∞ :=
  η ^ exposure s * w ^ success s

/-- A finite-horizon lower tail indexed by the number of exposed trials.

If the masked exponential potential is a one-step supermartingale, then the
mass of states with at least `H` exposures but at most `m` successes is bounded
by the initial potential divided by `η^H w^m`. -/
theorem masked_count_tail
    (K : α → PMF α) (exposure success : α → ℕ)
    (η w : ℝ≥0∞)
    (hη1 : 1 ≤ η) (hηtop : η ≠ ⊤)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hstep : ∀ s,
      expect (K s) (maskedCountPotential exposure success η w) ≤
        maskedCountPotential exposure success η w s)
    (T H m : ℕ) (s₀ : α) :
    ∑' z, (if H ≤ exposure z ∧ success z ≤ m then
        iter K T s₀ z else 0) ≤
      maskedCountPotential exposure success η w s₀ /
        (η ^ H * w ^ m) := by
  have hη0 : η ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hη1)
  have hwtop : w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hθ0 : η ^ H * w ^ m ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hη0) (pow_ne_zero _ hw0)
  have hθtop : η ^ H * w ^ m ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hηtop)
      (ENNReal.pow_ne_top hwtop)
  have hsub : ∀ z,
      (if H ≤ exposure z ∧ success z ≤ m then iter K T s₀ z else 0) ≤
        (if η ^ H * w ^ m ≤
            maskedCountPotential exposure success η w z then
          iter K T s₀ z else 0) := by
    intro z
    by_cases hz : H ≤ exposure z ∧ success z ≤ m
    · have hηpow : η ^ H ≤ η ^ exposure z :=
        pow_le_pow_right' hη1 hz.1
      have hwpow : w ^ m ≤ w ^ success z :=
        pow_le_pow_right_of_le_one' hw1 hz.2
      have hpot :
          η ^ H * w ^ m ≤
            maskedCountPotential exposure success η w z := by
        unfold maskedCountPotential
        exact mul_le_mul hηpow hwpow bot_le bot_le
      simp [hz, hpot]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div (iter K T s₀)
      (maskedCountPotential exposure success η w)
      (η ^ H * w ^ m) hθ0 hθtop) ?_
  exact ENNReal.div_le_div_right
    (by
      simpa using
        (expect_iter_le K
          (maskedCountPotential exposure success η w) 1
          (by simpa using hstep) T s₀))
    (η ^ H * w ^ m)

end Tri

#print axioms Tri.masked_count_tail
