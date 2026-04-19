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
import Ripple.Core.BoundedTime

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

/-! ## Per-coordinate β extraction for a zero-init `BoundedTimeComputable` -/

/-- Per-coordinate differentiability of the trajectory of a
`BoundedTimeComputable`, as a `DifferentiableOn` statement on `[0, ∞)`. -/
theorem BoundedTimeComputable.coord_differentiableOn {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) (j : Fin d) :
    DifferentiableOn ℝ (fun t => btc.sol.trajectory t j) (Set.Ici 0) := by
  intro t ht
  have hderiv : HasDerivAt (fun s => btc.sol.trajectory s j)
      (btc.pivp.field (btc.sol.trajectory t) j) t :=
    (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) j
  exact hderiv.differentiableAt.differentiableWithinAt

/-- Per-coordinate uniform bound on the trajectory of a
`BoundedTimeComputable`, extracted from its global `bounded` field. -/
theorem BoundedTimeComputable.coord_bound {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, 0 ≤ t → ∀ j : Fin d, |btc.sol.trajectory t j| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := btc.bounded
  refine ⟨M, le_of_lt hMpos, fun t ht j => ?_⟩
  have h1 : ‖btc.sol.trajectory t j‖ ≤ ‖btc.sol.trajectory t‖ :=
    norm_le_pi_norm _ _
  have h2 : ‖btc.sol.trajectory t‖ ≤ M := hM t ht
  have : |btc.sol.trajectory t j| ≤ M := by
    rw [← Real.norm_eq_abs]; linarith
  exact this

/-- Per-coordinate `β` majorization for a zero-init `BoundedTimeComputable`:
for every coordinate `j`, there is `β_j ≥ 0` with `|y_j(t)| ≤ β_j (1 − e^{−t})`
on `[0, ∞)`. Obtained from `bounded_zero_init_exp_majorization` applied
coordinatewise. -/
noncomputable def BoundedTimeComputable.dualRailBeta {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) :
    Fin d → ℝ :=
  fun j =>
    Classical.choose
      (bounded_zero_init_exp_majorization
        (fun t => btc.sol.trajectory t j)
        (Classical.choose btc.coord_bound)
        (Classical.choose_spec btc.coord_bound).1
        (fun t ht =>
          (Classical.choose_spec btc.coord_bound).2 t ht j)
        (by
          change btc.sol.trajectory 0 j = 0
          have := congrFun btc.sol.init_cond j
          rw [this, h_zero j])
        (btc.coord_differentiableOn j))

theorem BoundedTimeComputable.dualRailBeta_nonneg {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) (j : Fin d) :
    0 ≤ btc.dualRailBeta h_zero j :=
  (Classical.choose_spec
    (bounded_zero_init_exp_majorization
      (fun t => btc.sol.trajectory t j)
      (Classical.choose btc.coord_bound)
      (Classical.choose_spec btc.coord_bound).1
      (fun t ht =>
        (Classical.choose_spec btc.coord_bound).2 t ht j)
      (by
        change btc.sol.trajectory 0 j = 0
        have := congrFun btc.sol.init_cond j
        rw [this, h_zero j])
      (btc.coord_differentiableOn j))).1

theorem BoundedTimeComputable.dualRailBeta_majorizes {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_zero : ∀ j, btc.pivp.init j = 0) (j : Fin d) :
    ∀ t, 0 ≤ t →
      |btc.sol.trajectory t j| ≤ btc.dualRailBeta h_zero j *
        (1 - Real.exp (-t)) :=
  (Classical.choose_spec
    (bounded_zero_init_exp_majorization
      (fun t => btc.sol.trajectory t j)
      (Classical.choose btc.coord_bound)
      (Classical.choose_spec btc.coord_bound).1
      (fun t ht =>
        (Classical.choose_spec btc.coord_bound).2 t ht j)
      (by
        change btc.sol.trajectory 0 j = 0
        have := congrFun btc.sol.init_cond j
        rw [this, h_zero j])
      (btc.coord_differentiableOn j))).2

end Ripple
