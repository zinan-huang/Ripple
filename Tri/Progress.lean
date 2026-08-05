/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Freeze

/-!
# The progress engine: a Chernoff lower tail for adapted trials

This is the second of the two engines, and the paper's Lemma 2. The design
requires it to be run with a **different** base from the safety engine — sharing
one makes the resulting bound vacuous (`design/08-cancellation.md`).

The pleasant discovery is that it has the *same shape* as the safety engine, only
with the geometric potential taken in the **success counter** rather than in the
state. Writing `w = e^{-t}`, the exponential moment `E[e^{-t·count}]` is
`E[w^count]`, so the whole Chernoff argument runs on `expect_iter_le` and
`markov` — the machinery already built — with no new probabilistic infrastructure
and no measure theory.

Crucially the trials need **not** be independent: as in the safety engine, only a
*pointwise* lower bound on the conditional success probability is used. That is
what makes this applicable to a CRN trajectory, where the success probability
depends on the current configuration and hence on the whole history.

## Main results

* `step_factor_antitone` — the one-step exponential factor is antitone in the
  success probability. This is the progress-engine analogue of
  `Tri.bracket_antitone`, and again it is the entire content of the informal
  "we may assume success probability exactly `p`" step.
* `count_tail` — the Chernoff lower tail: if each step increments the counter
  with conditional probability at least `p`, then after `T` steps the counter is
  at most `m` with probability at most `((1-p) + p·w)^T / w^m`, for every
  `w ≤ 1`.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemma 2.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- **The one-step exponential factor is antitone in the success probability.**

If a step increments the counter with probability `q` and leaves it alone with
probability `q'` (so `q + q' = 1`), the geometric potential `w^count` is
multiplied in expectation by `q' + q·w`. For `w ≤ 1` this is *decreasing* in `q`:
more successes means a smaller potential.

Hence a *lower* bound `p ≤ q` on the conditional success probability yields an
*upper* bound on the factor — which is exactly what the Chernoff argument
consumes, and why no independence assumption is needed anywhere.

Stated over `ℝ` and with the complementary masses carried explicitly rather than
as `1 - q`, so that no truncated subtraction appears. -/
theorem step_factor_antitone {p p' q q' w : ℝ}
    (hp : p + p' = 1) (hq : q + q' = 1) (hw : w ≤ 1) (hpq : p ≤ q) :
    q' + q * w ≤ p' + p * w := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hw)]

/-- The `ℝ≥0∞` form of `step_factor_antitone`, obtained by transfer. As in the
safety engine, the scalar inequality is proved over `ℝ` because `ℝ≥0∞`'s
truncated subtraction blocks the factoring, and everything in sight is finite. -/
theorem step_factor_antitone_ennreal {p p' q q' w : ℝ≥0∞}
    (hp : p + p' = 1) (hq : q + q' = 1) (hw : w ≤ 1) (hpq : p ≤ q) :
    q' + q * w ≤ p' + p * w := by
  have hple : p ≤ 1 := by rw [← hp]; exact le_add_right le_rfl
  have hp'le : p' ≤ 1 := by rw [← hp]; exact le_add_left le_rfl
  have hqle : q ≤ 1 := by rw [← hq]; exact le_add_right le_rfl
  have hq'le : q' ≤ 1 := by rw [← hq]; exact le_add_left le_rfl
  have fp : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hple
  have fp' : p' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp'le
  have fq : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hqle
  have fq' : q' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq'le
  have fw : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  rw [← ENNReal.toReal_le_toReal
        (ENNReal.add_ne_top.mpr ⟨fq', ENNReal.mul_ne_top fq fw⟩)
        (ENNReal.add_ne_top.mpr ⟨fp', ENNReal.mul_ne_top fp fw⟩)]
  rw [ENNReal.toReal_add fq' (ENNReal.mul_ne_top fq fw),
      ENNReal.toReal_add fp' (ENNReal.mul_ne_top fp fw),
      ENNReal.toReal_mul, ENNReal.toReal_mul]
  refine step_factor_antitone ?_ ?_ ?_ ?_
  · have := congrArg ENNReal.toReal hp
    rwa [ENNReal.toReal_add fp fp', ENNReal.toReal_one] at this
  · have := congrArg ENNReal.toReal hq
    rwa [ENNReal.toReal_add fq fq', ENNReal.toReal_one] at this
  · exact (ENNReal.toReal_le_toReal fw ENNReal.one_ne_top).mpr hw |>.trans_eq ENNReal.toReal_one
  · exact (ENNReal.toReal_le_toReal fp fq).mpr hpq

/-- **The Chernoff lower tail for adapted trials.**

`count` measures progress. If one step multiplies the potential `w^count` by at
most `φ` in expectation from every state, then after `T` steps the counter fails
to exceed `m` with probability at most `φ^T / w^m`.

This is the raw Chernoff bound *before* optimizing `w`. Optimizing it is a
separate scalar exercise, deliberately kept out of the probabilistic layer.

No independence is assumed: the hypothesis is a pointwise one-step bound, exactly
as in the safety engine. -/
theorem count_tail (K : α → PMF α) (count : α → ℕ) (w φ : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hstep : ∀ s, expect (K s) (fun z => w ^ count z) ≤ φ * w ^ count s)
    (T m : ℕ) (s₀ : α) :
    ∑' z, (if count z ≤ m then iter K T s₀ z else 0)
      ≤ φ ^ T * w ^ count s₀ / w ^ m := by
  have hwtop : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set θ : ℝ≥0∞ := w ^ m with hθdef
  have hθ : θ ≠ 0 := pow_ne_zero _ hw0
  have htop : θ ≠ ⊤ := ENNReal.pow_ne_top hwtop
  -- the bad set `count ≤ m` sits inside the large-potential set, since `w ≤ 1`
  have hsub : ∀ z, (if count z ≤ m then iter K T s₀ z else 0)
      ≤ (if θ ≤ w ^ count z then iter K T s₀ z else 0) := by
    intro z
    by_cases hz : count z ≤ m
    · have : θ ≤ w ^ count z := pow_le_pow_right_of_le_one' hw1 hz
      simp [hz, this]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div (iter K T s₀) (fun z => w ^ count z) θ hθ htop) ?_
  exact ENNReal.div_le_div_right
    (expect_iter_le K (fun z => w ^ count z) φ hstep T s₀) θ

/-- **From a two-atom step to the Chernoff hypothesis.**

A step that either increments the counter or leaves it alone, with success mass
at least `p`, satisfies `count_tail`'s hypothesis with factor `p' + p·w`.

The success mass `q` is allowed to depend on the state `s` — only the *uniform
lower bound* `p ≤ q` is used. That is precisely the adaptedness the CRN needs. -/
theorem count_step_of_masses {K : α → PMF α} {count : α → ℕ} {w : ℝ≥0∞} {s : α}
    {q q' p p' : ℝ≥0∞}
    (hq : q + q' = 1) (hp : p + p' = 1) (hw : w ≤ 1) (hpq : p ≤ q)
    (hdecomp : expect (K s) (fun z => w ^ count z)
        = q' * w ^ count s + q * w ^ (count s + 1)) :
    expect (K s) (fun z => w ^ count z) ≤ (p' + p * w) * w ^ count s := by
  rw [hdecomp]
  have factor : q' * w ^ count s + q * w ^ (count s + 1)
      = (q' + q * w) * w ^ count s := by ring
  rw [factor]
  exact mul_le_mul_left (step_factor_antitone_ennreal hp hq hw hpq) _

/-- **The Chernoff lower tail for Bernoulli-type adapted trials** — the paper's
Lemma 2, before the exponential optimization.

If every step increments the counter with conditional probability at least `p`,
then after `T` steps the counter fails to exceed `m` with probability at most

    (p' + p·w)^T · w^{count s₀} / w^m       for every `w ≤ 1`, where `p + p' = 1`.

Choosing `w` optimally turns this into the familiar `exp(−2T(p−a)²)`; that step
is pure scalar analysis and is deliberately not mixed into the probabilistic
layer. -/
theorem count_tail_bernoulli (K : α → PMF α) (count : α → ℕ) (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hstep : ∀ s, expect (K s) (fun z => w ^ count z) ≤ (p' + p * w) * w ^ count s)
    (T m : ℕ) (s₀ : α) :
    ∑' z, (if count z ≤ m then iter K T s₀ z else 0)
      ≤ (p' + p * w) ^ T * w ^ count s₀ / w ^ m :=
  count_tail K count w (p' + p * w) hw1 hw0 hstep T m s₀


end Tri
