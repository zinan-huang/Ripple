/-
  Ripple.Number.Euler — e is real-time CRN-computable

  Theorem 3.3.2 from Huang's PhD thesis (Iowa State, 2020):
  The PIVP  x' = -x, y' = -xy  with  x(0) = 1, y(0) = 1
  has solution  x(t) = e^{-t}, y(t) = e^{1-e^{-t}},
  so y(t) → e exponentially.

  By Theorem 3.2.10 (ℝ_RTCRN = ℝ_RTGPAC) and Theorem 3.3.1
  (integer ICs suffice), e ∈ ℝ_RTCRN.
-/

import Ripple.Core.BoundedTime
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Order.Basic

namespace Ripple.Number

open Real

/-! ## The PIVP for e

  The 2-dimensional system:
    x'(t) = -x(t)
    y'(t) = -x(t) · y(t)

  with x(0) = 1, y(0) = 1.

  Solution: x(t) = e^{-t}, y(t) = e^{1 - e^{-t}}.
-/

/-- The PIVP computing e: dimension 2, output = component 1. -/
noncomputable def eulerPIVP : Ripple.PIVP 2 where
  field := fun y => ![- y 0, y 0 * y 1]
  init := ![1, 1]
  output := 1

/-- The closed-form solution of the Euler PIVP. -/
noncomputable def eulerSolution : ℝ → Fin 2 → ℝ :=
  fun t => ![exp (-t), exp (1 - exp (-t))]

/-- x(t) = e^{-t}. -/
theorem euler_sol_x (t : ℝ) : eulerSolution t 0 = exp (-t) := by
  simp [eulerSolution, Matrix.cons_val_zero]

/-- y(t) = e^{1 - e^{-t}}. -/
theorem euler_sol_y (t : ℝ) : eulerSolution t 1 = exp (1 - exp (-t)) := by
  simp [eulerSolution, Matrix.cons_val_one]

/-- The solution satisfies the initial condition. -/
theorem euler_sol_init : eulerSolution 0 = eulerPIVP.init := by
  ext i
  fin_cases i <;> simp [eulerSolution, eulerPIVP, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- x(t) is bounded: 0 < x(t) ≤ 1 for all t ≥ 0. -/
theorem euler_x_pos (t : ℝ) : 0 < eulerSolution t 0 := by
  rw [euler_sol_x]
  exact exp_pos _

theorem euler_x_le_one {t : ℝ} (ht : 0 ≤ t) : eulerSolution t 0 ≤ 1 := by
  rw [euler_sol_x]
  rw [← exp_zero]
  exact exp_le_exp.mpr (neg_nonpos.mpr ht)

/-- y(t) is bounded: 1 ≤ y(t) ≤ e for all t ≥ 0. -/
theorem euler_y_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ eulerSolution t 1 := by
  rw [euler_sol_y]
  have h1 : exp (-t) ≤ 1 := by
    calc exp (-t) ≤ exp 0 := exp_le_exp.mpr (neg_nonpos.mpr ht)
    _ = 1 := exp_zero
  have h2 : 0 ≤ 1 - exp (-t) := by linarith
  calc (1 : ℝ) = exp 0 := exp_zero.symm
  _ ≤ exp (1 - exp (-t)) := exp_le_exp.mpr h2

theorem euler_y_le_e {t : ℝ} (_ht : 0 ≤ t) : eulerSolution t 1 ≤ exp 1 := by
  rw [euler_sol_y]
  apply exp_le_exp.mpr
  have : 0 < exp (-t) := exp_pos _
  linarith

/-- The PIVP is bounded: ‖sol(t)‖ ≤ e + 1 for all t ≥ 0. -/
theorem euler_bounded : eulerPIVP.IsBounded eulerSolution := by
  refine ⟨exp 1 + 1, by positivity, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · -- component 0: ‖e^{-t}‖ ≤ e+1
    simp [eulerSolution, Matrix.cons_val_zero, norm_of_nonneg (le_of_lt (exp_pos _))]
    calc exp (-t) ≤ 1 := by rw [← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)
    _ ≤ exp 1 + 1 := by linarith [exp_pos 1]
  · -- component 1: ‖e^{1-e^{-t}}‖ ≤ e+1
    simp [eulerSolution, Matrix.cons_val_one, norm_of_nonneg (le_of_lt (exp_pos _))]
    calc exp (1 - exp (-t)) ≤ exp 1 := euler_y_le_e ht
    _ ≤ exp 1 + 1 := le_add_of_nonneg_right (by norm_num)

/-- Key convergence estimate: |y(t) - e| ≤ e · e^{-t} for t ≥ 0.

  Proof:
    y(t) = e^{1 - e^{-t}}
    |y(t) - e| = e - e^{1 - e^{-t}}      (since y(t) ≤ e)
              = e · (1 - e^{-e^{-t}})
              ≤ e · e^{-t}               (since e^x ≥ 1+x gives e^{-a} ≥ 1-a)
-/
theorem euler_convergence (t : ℝ) (ht : 0 ≤ t) :
    |eulerSolution t 1 - exp 1| ≤ exp 1 * exp (-t) := by
  rw [euler_sol_y]
  -- y(t) ≤ e, so the difference is non-positive
  have hle : exp (1 - exp (-t)) ≤ exp 1 := euler_y_le_e ht
  rw [abs_of_nonpos (by linarith)]
  -- Goal: -(exp(1 - exp(-t)) - exp 1) ≤ exp 1 * exp(-t)
  -- i.e., exp 1 - exp(1 - exp(-t)) ≤ exp 1 * exp(-t)
  -- Factor: exp(1 - exp(-t)) = exp 1 * exp(-exp(-t))
  have hfactor : exp (1 - exp (-t)) = exp 1 * exp (-exp (-t)) := by
    rw [← exp_add]; ring_nf
  -- From add_one_le_exp: -exp(-t) + 1 ≤ exp(-exp(-t))
  -- So exp(-exp(-t)) ≥ 1 - exp(-t)
  -- So exp 1 * exp(-exp(-t)) ≥ exp 1 * (1 - exp(-t))
  -- So exp 1 - exp 1 * exp(-exp(-t)) ≤ exp 1 - exp 1 * (1 - exp(-t)) = exp 1 * exp(-t)
  have key := add_one_le_exp (-exp (-t))
  -- key: -exp(-t) + 1 ≤ exp(-exp(-t))
  -- i.e., 1 - exp(-t) ≤ exp(-exp(-t))
  have he1 : 0 < exp 1 := exp_pos 1
  linarith [mul_le_mul_of_nonneg_left key (le_of_lt he1)]

/-- The semantic record for `e` (closed-form solution, modulus `r + 2`). -/
noncomputable def eulerBTC : Ripple.SemanticBTC 2 (exp 1) := {
      pivp := eulerPIVP
      sol := {
        trajectory := eulerSolution
        init_cond := euler_sol_init
        is_solution := fun t _ => by
          have hfield : eulerPIVP.field (eulerSolution t) =
              ![- exp (-t), exp (-t) * exp (1 - exp (-t))] := by
            ext i; fin_cases i <;>
              simp [eulerPIVP, eulerSolution, Matrix.cons_val_zero,
                Matrix.cons_val_one]
          rw [hfield, hasDerivAt_pi]
          have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
            simpa [id] using (hasDerivAt_id t).neg
          intro i; fin_cases i
          · -- d/dt exp(-t) = -exp(-t)
            change HasDerivAt (fun s => exp (-s)) (-exp (-t)) t
            convert h_neg.exp using 1; ring
          · -- d/dt exp(1-exp(-t)) = exp(-t)*exp(1-exp(-t))
            change HasDerivAt (fun s => exp (1 - exp (-s)))
              (exp (-t) * exp (1 - exp (-t))) t
            convert ((hasDerivAt_const t (1:ℝ)).sub h_neg.exp).exp using 1
            simp [Pi.sub_apply]; ring
      }
      -- Time modulus μ(r) = r + 2: for t > r+2, |y(t) - e| < e^{-r}
      modulus := fun r => ↑r + 2
      bounded := euler_bounded
      convergence := by
        intro r t htr
        -- |y(t) - e| ≤ e * exp(-t) < e * exp(-(r+2)) = exp(-r-1) < exp(-r)
        have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
        have ht_pos : 0 ≤ t := by linarith
        calc |eulerSolution t 1 - exp 1|
            ≤ exp 1 * exp (-t) := euler_convergence t ht_pos
          _ < exp 1 * exp (-(↑r + 2)) := by
              apply mul_lt_mul_of_pos_left _ (exp_pos 1)
              exact exp_lt_exp.mpr (by linarith)
          _ = exp (-(↑r : ℝ) - 1) := by rw [← exp_add]; ring_nf
          _ < exp (-(↑r : ℝ)) := by
              apply exp_lt_exp.mpr; linarith
    }

/-! ## The ℚ-polynomial presentation -/

open MvPolynomial in
/-- The syntactic `PolyPIVP 2` whose semantic image is `eulerPIVP`:
`x' = -x`, `y' = x·y`, `x(0) = y(0) = 1`. -/
noncomputable def eulerPolyPIVP : Ripple.PolyPIVP 2 where
  field := ![-X 0, X 0 * X 1]
  init := ![1, 1]
  output := 1

theorem eulerPolyPIVP_evalField (x : Fin 2 → ℝ) :
    eulerPolyPIVP.evalField x = eulerPIVP.field x := by
  funext i
  fin_cases i <;>
    simp [Ripple.PolyPIVP.evalField, eulerPolyPIVP, eulerPIVP, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]

theorem eulerSolution_continuous : Continuous eulerSolution := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous fun t => eulerSolution t 0
    simp only [euler_sol_x]
    exact Real.continuous_exp.comp continuous_neg
  · change Continuous fun t => eulerSolution t 1
    simp only [euler_sol_y]
    exact Real.continuous_exp.comp
      (continuous_const.sub (Real.continuous_exp.comp continuous_neg))

/-- e is real-time computable ([RTCRN2] Thm 4): the ℚ-polynomial system `x' = -x`,
`y' = x·y`, `x(0) = y(0) = 1` with `y(t) = e^{1 - e^{-t}}`, modulus `r + 2`. -/
theorem euler_is_realtime : Ripple.IsRealTimeComputable (exp 1) := by
  refine ⟨2, eulerBTC.certify eulerPolyPIVP eulerPolyPIVP_evalField (fun i => ?_) rfl
    eulerSolution_continuous, 2, by norm_num, fun r => ?_⟩
  · fin_cases i <;> simp [eulerPolyPIVP, eulerBTC, eulerPIVP]
  · change (r : ℝ) + 2 ≤ 2 * ((r : ℝ) + 1)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith

end Ripple.Number
