/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

/-!
# The one-step bracket

Every drift estimate in the analysis of `Tri` passes through one scalar
quantity. If a productive step moves a geometric potential `ρ^•` down with
probability `s` and up with probability `1 - s`, the potential is multiplied in
expectation by the **bracket**

    bracket ρ s = s / ρ + (1 - s) * ρ.

This file collects the scalar facts about it. They are deliberately separated
from all probability: they are inequalities about real numbers, and isolating
them keeps the kernel-level inductions free of real-analysis noise.

## The two engines

The design distinguishes a *safety* engine from a *progress* engine, following
the paper's own Lemma 3, whose proof produces a ruin term and a Chernoff term
separately. Trying to serve both with a single potential base is a mistake: the
bracket-minimising base makes the Markov threshold factor cancel the contraction
at leading order (see `design/08-cancellation.md`).

* **Safety** uses the harmonic base `ρ_F = p / (1 - p)`, for which
  `bracket_harmonic` shows the bracket is *exactly* `1`. The potential is then a
  martingale, which is what gives Feller's ruin bound its clean form.
* **Progress** uses a separately optimised tilt; `bracket_small_bias` is the
  reusable estimate for the weak-bias regime of phase 1.

## Main results

* `bracket_antitone` — the bracket is antitone in the success probability.
  This single inequality is the entire formal content of the informal
  "stochastic domination" step in the paper.
* `bracket_harmonic` — at `ρ = p/(1-p)` the bracket equals `1`.
* `bracket_small_bias` — the weak-bias estimate, tight at its own hypothesis.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemmas 1–3.
-/

namespace Tri

/-- The expected multiplier applied to a geometric potential `ρ^•` by one
productive step that moves down with probability `s` and up with probability
`1 - s`. -/
noncomputable def bracket (ρ s : ℝ) : ℝ := s / ρ + (1 - s) * ρ

/-- **The domination step.** The bracket is antitone in the success
probability: a step that succeeds more often cannot multiply the potential by
more. Every appearance of "we may view this as a walk with success probability
at least `p`" in the paper reduces to this one inequality, which is why no
coupling and no stochastic order needs to be formalized. -/
theorem bracket_antitone {ρ p s : ℝ} (hρ : 1 ≤ ρ) (hps : p ≤ s) :
    bracket ρ s ≤ bracket ρ p := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have key : bracket ρ p - bracket ρ s = (s - p) * (ρ - 1 / ρ) := by
    unfold bracket
    field_simp
    ring
  have h1 : 0 ≤ s - p := sub_nonneg.mpr hps
  have h2 : 0 ≤ ρ - 1 / ρ := by
    rw [sub_nonneg, div_le_iff₀ hρ0]
    nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- **The safety base.** At the harmonic base `ρ = p/(1-p)` the bracket is
exactly `1`, so the potential `ρ^•` is a martingale. This exact identity — not
an inequality — is what makes Feller's ruin bound come out as the clean
`((1-p)/p)^b`, and it is the reason the safety engine must not share a base with
the progress engine. -/
theorem bracket_harmonic {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    bracket (p / (1 - p)) p = 1 := by
  have hp1 : 0 < 1 - p := sub_pos.mpr h1
  have hne : p / (1 - p) ≠ 0 := by positivity
  unfold bracket
  field_simp
  ring

/-- The bracket is positive whenever the base is. -/
theorem bracket_pos {ρ s : ℝ} (hρ : 0 < ρ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < bracket ρ s := by
  unfold bracket
  have : 0 ≤ (1 - s) * ρ := mul_nonneg (by linarith) hρ.le
  rcases eq_or_lt_of_le hs0 with h | h
  · simpa [← h] using mul_pos (by linarith : (0:ℝ) < 1 - s) hρ
  · have : 0 < s / ρ := div_pos h hρ
    linarith

/-- **The weak-bias estimate**, for the regime of phase 1 where the drift
advantage `r - 1/2` is small.

For `0 < ε ≤ 2r - 1`,

    r/(1+ε) + (1-r)(1+ε) ≤ 1 - ε(2r-1)/2.

The hypothesis `ε ≤ 2r - 1` is exactly what the conclusion needs: clearing
denominators reduces the claim to `ε/2 ≤ (2r-1)/2`. So the estimate is tight at
its own hypothesis, and the constant `1/2` on the right cannot be improved
without shrinking the range of `ε`.

Note the bias hypotheses `1/2 < r` and `r ≤ 1` are *not* required: `0 < ε` and
`ε ≤ 2r - 1` already force `2r - 1 > 0`, hence `r > 1/2`, and no upper bound on
`r` is used. Stating the lemma without them keeps dead hypotheses out of every
downstream call site — see `bracket_small_bias_pos` for the derived bias. -/
theorem bracket_small_bias {r ε : ℝ} (he0 : 0 < ε) (he1 : ε ≤ 2 * r - 1) :
    bracket (1 + ε) r ≤ 1 - ε * (2 * r - 1) / 2 := by
  have hpos : (0:ℝ) < 1 + ε := by linarith
  rw [bracket, div_add' _ _ _ hpos.ne', div_le_iff₀ hpos]
  nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he1), sq_nonneg ε,
    mul_nonneg he0.le he0.le]

/-- The hypotheses of `bracket_small_bias` already entail a genuine bias. -/
theorem bracket_small_bias_pos {r ε : ℝ} (he0 : 0 < ε) (he1 : ε ≤ 2 * r - 1) :
    1 / 2 < r := by linarith

/-- **The one-step drift inequality**, in scalar form.

If a chain sits at level `k` and moves to `k-1`, `k`, `k+1` with probabilities
`p0, p1, p2`, then the geometric potential `u^level` does not increase precisely
when `p0 ≤ p2 · u`.

This is the exact condition — the proof factors as `p0(1-u) ≤ p2·u(1-u)` — so
for the Tri chain, where `Tri.odds_cross_mul` gives the odds ratio `p2/p0` as
exactly `(x-1)/(y-1)`, the potential is *conserved* at `u = (y-1)/(x-1)` and
*decreases* for any smaller `u`.

Note the minimal hypotheses: no nonnegativity of `p0` or `p2` is needed, and no
upper bound on `p1`. Only that the three masses sum to one and `0 ≤ u ≤ 1`. -/
theorem three_term_drift {p0 p1 p2 u : ℝ} (hsum : p0 + p1 + p2 = 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hdrift : p0 ≤ p2 * u) :
    p0 + p1 * u + p2 * u ^ 2 ≤ u := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hu1) hu0]

/-- At the harmonic base the drift inequality is an *equality*: the potential is
exactly conserved. This is the scalar shadow of `Tri.bracket_harmonic`, and it
is why the safety engine needs no contraction. -/
theorem three_term_drift_eq {p0 p1 p2 u : ℝ} (hsum : p0 + p1 + p2 = 1)
    (hdrift : p0 = p2 * u) :
    p0 + p1 * u + p2 * u ^ 2 = u := by
  have hp1 : p1 = 1 - p0 - p2 := by linarith
  rw [hp1, hdrift]; ring

section Sanity

/-! Guards pinning the bracket at the values the design relies on. These are the
numbers that decide which phases a fixed base may be used in. -/

/-- At `ρ = 2` the bracket is `2 - 3r/2`, so it contracts exactly when
`r > 2/3`. This is why a fixed base `ρ = 2` is usable in phases 2 and 3 but
*not* in phase 1, where `r` is close to `1/2`. -/
theorem bracket_two (r : ℝ) : bracket 2 r = 2 - 3 * r / 2 := by
  unfold bracket; ring

example : bracket 2 (1/2) = 5/4 := by rw [bracket_two]; norm_num
example : bracket 2 (3/4) = 7/8 := by rw [bracket_two]; norm_num
example : bracket 2 (7/8) = 11/16 := by rw [bracket_two]; norm_num

/-- The contraction threshold for the fixed base `ρ = 2`. -/
theorem bracket_two_lt_one_iff (r : ℝ) : bracket 2 r < 1 ↔ 2 / 3 < r := by
  rw [bracket_two]; constructor <;> intro h <;> linarith

end Sanity

end Tri
