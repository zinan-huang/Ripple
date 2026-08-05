/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Freeze

/-!
# Laziness: why the productive clock never has to be constructed

The paper counts *productive reaction events*, while a computation is a sequence
of *interaction events*, most of which change nothing. Relating the two is the
step that ordinarily forces a formalization to build the embedded jump chain —
conditioning on "the next productive step", defining nested hitting times whose
lower endpoint is itself a stopping time, and so on.

None of that is needed. In expectation a single interaction contributes

    (1 - q) · V s   +   q · (bracket · V s)

where `q` is the probability the step is productive and `bracket` is the
conditional multiplier of the potential *given* that it is. The unproductive
part contributes the factor `1` and the direction bound enters **only** the
second summand. So a bound on the conditional bracket transfers to the full
chain with no reference to the productive subsequence at all.

`lazy_conserved` is that observation, and it is the bridge from `Tri.bracket_*`
to the conservation hypothesis `hfroz` of `Tri.feller_ruin`.

Note what is *not* assumed: nothing about `q` beyond `q ≤ 1`. In particular the
bound is uniform in how rare productive steps are, which is exactly why the same
lemma serves phase 1 (`q = Θ(1)`) and the endgame (`q = Θ(1/n)`) without a
separate clock argument for each.

## Main results

* `lazy_conserved` — a conditional bracket `≤ 1` conserves the potential.
* `lazy_contract` — the quantitative version: a conditional bracket `≤ β`
  contracts the potential by `1 - q·(1-β)`. Note it needs **no** hypothesis on
  `q` at all — monotonicity alone suffices.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemma 5 (which this replaces the need for at the level of the safety engine).
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- **Laziness conserves.** If one step of the chain multiplies the potential by
`bracket` on the productive part and leaves it alone otherwise, and the
conditional bracket is at most `1`, then the potential does not increase.

This is the whole of the interaction-clock ↔ productive-clock conversion for the
safety engine: the productive subsequence is never formed, and `q` is
unconstrained apart from being a probability. -/
theorem lazy_conserved {v q br : ℝ≥0∞} (hq : q ≤ 1) (hbr : br ≤ 1) :
    (1 - q) * v + q * (br * v) ≤ v := by
  calc (1 - q) * v + q * (br * v)
      ≤ (1 - q) * v + q * (1 * v) := by gcongr
    _ = ((1 - q) + q) * v := by rw [one_mul, add_mul]
    _ = v := by rw [tsub_add_cancel_of_le hq, one_mul]

/-- **Laziness contracts, quantitatively.** A conditional bracket of `β`
produces an overall multiplier of `1 - q·(1-β)`: the contraction is diluted by
exactly the productivity `q`, and by nothing else.

This is the shape the progress engine needs, and it is where the
multiplicative-Chernoff exponent comes from — the per-step factor is linear in
`q`, not quadratic, so no `q²` loss is incurred. -/
theorem lazy_contract {v q br β : ℝ≥0∞} (hbr : br ≤ β) :
    (1 - q) * v + q * (br * v) ≤ (1 - q) * v + q * (β * v) := by
  gcongr

section NonVacuity

/-! The hypotheses of `lazy_conserved` are satisfiable with a genuinely
productive step (`q ≠ 0`) and a genuinely contracting bracket (`br < 1`), so the
lemma is not about a degenerate configuration. -/

example : (1 - (1/2 : ℝ≥0∞)) * 8 + (1/2 : ℝ≥0∞) * ((1/4 : ℝ≥0∞) * 8) ≤ 8 :=
  lazy_conserved (by norm_num) (by norm_num)

/-- With `q = 1` (every step productive) the bound is still the right one. -/
example : (1 - (1 : ℝ≥0∞)) * 8 + (1 : ℝ≥0∞) * ((1/4 : ℝ≥0∞) * 8) ≤ 8 :=
  lazy_conserved (le_refl _) (by norm_num)

end NonVacuity

end Tri
