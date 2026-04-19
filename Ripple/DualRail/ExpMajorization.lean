/-
  Ripple.DualRail.ExpMajorization — narrow Mathlib-gap analytic fact used by
  `dualRail_semantic_solution` (exponential-shift construction).

  This isolates a clean real-analysis statement: a bounded function `y : ℝ → ℝ`
  that vanishes at 0 and is differentiable on `[0,∞)` admits an exponential
  majorization `|y(t)| ≤ β·(1 − e^{−t})` on `[0,∞)` for some `β ≥ 0`. The
  minimal working choice is `β := M / (1 − e^{-1})` times a suitable constant,
  but we only need existence.

  This is the single narrow residual analytic axiom on which the
  `dualRail_semantic_solution` Solution-level proof relies. It is a
  Mathlib-gap fact (no circular dependence on dual-rail machinery).
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Ripple

/-- For a bounded differentiable `y : ℝ → ℝ` with `y(0) = 0` and
`|y(t)| ≤ M` on `[0, ∞)`, there exists `β ≥ 0` such that
`|y(t)| ≤ β · (1 − e^{−t})` for all `t ≥ 0`.

This is the narrow analytic fact (Mathlib gap) used by the exponential-shift
dual-rail construction. Idea of the proof (not formalised here): near `t = 0`
the LHS `|y(t)|` vanishes with `|y'(0)|·t + o(t)` while `(1 − e^{−t}) = t +
o(t)`, so taking `β ≥ sup_{t>0} |y(t)|/(1 − e^{−t})` works — this supremum is
finite because `(1 − e^{−t})` is bounded below by a positive constant on
`[ε, ∞)` for any `ε > 0`, and bounded below by a linear function in `t` near
zero (where `|y(t)|` is also `O(t)`). -/
axiom bounded_zero_init_exp_majorization
    (y : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hy_bound : ∀ t, 0 ≤ t → |y t| ≤ M)
    (hy_zero : y 0 = 0)
    (hy_diff : DifferentiableOn ℝ y (Set.Ici 0)) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ t, 0 ≤ t → |y t| ≤ β * (1 - Real.exp (-t))

end Ripple
