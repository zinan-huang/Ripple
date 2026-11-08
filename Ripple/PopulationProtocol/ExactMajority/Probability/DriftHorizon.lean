/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Horizon calibration for multiplicative-drift survival

This file calibrates the geometric term consumed by `driftSurvivalPhase`.
If the one-step contraction factor is

  `r = 1 - B / (n(n-1))`,

then a horizon

  `ceil((n(n-1)/B) * (log Φmax + log(D n²)))`

makes `r^T * Φmax` at most `1/(D n²)`.  The parameter `D` exposes the
internal failure-budget split: for example, `D = 2` leaves half of the
`n⁻²` slot budget for window escape.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftSurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace DriftSurvival

open scoped ENNReal NNReal

/-- A horizon that makes multiplicative drift at rate `B / (n(n-1))`
pay both the initial-potential factor and a `1/(D n²)` tail budget. -/
noncomputable def driftHorizon (B : ℝ) (n Φmax D : ℕ) : ℕ :=
  ⌈(((n : ℝ) * ((n : ℝ) - 1)) / B) *
      (Real.log (Φmax : ℝ) + Real.log ((D : ℝ) * (n : ℝ) ^ 2))⌉₊

/-- The `1/(D n²)` drift budget in the `NNReal` type required by
`driftSurvivalPhase`. -/
noncomputable def driftBudgetNN (D n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / ((D : ℝ) * (n : ℝ) ^ 2))

/-- Casting `driftBudgetNN` to `ENNReal` recovers its `ofReal` form. -/
theorem coe_driftBudgetNN (D n : ℕ) :
    (driftBudgetNN D n : ℝ≥0∞) =
      ENNReal.ofReal (1 / ((D : ℝ) * (n : ℝ) ^ 2)) := by
  rw [driftBudgetNN, ENNReal.ofReal]

/-- Multiplying the `D`-th share by all `D` shares recovers the full
inverse-square budget. -/
theorem natCast_mul_driftBudgetNN_eq_inv_sq
    {D n : ℕ} (hD : 1 ≤ D) (hn : 1 ≤ n) :
    (D : ℝ≥0∞) * (driftBudgetNN D n : ℝ≥0∞) =
      1 / (n : ℝ≥0∞) ^ 2 := by
  have hDR : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hreal :
      (D : ℝ) * (1 / ((D : ℝ) * (n : ℝ) ^ 2)) =
        1 / (n : ℝ) ^ 2 := by
    field_simp [hDR.ne', hnR.ne']
  have hrhs : ENNReal.ofReal (1 / (n : ℝ) ^ 2) =
      1 / (n : ℝ≥0∞) ^ 2 := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1)]
    rw [ENNReal.ofReal_inv_of_pos]
    · rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (n : ℝ))]
      norm_num
    · positivity
  rw [coe_driftBudgetNN, ← ENNReal.ofReal_natCast D,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D : ℝ)), hreal, hrhs]

/-- The calibrated multiplicative-drift tail bound.

The assumptions say that the population and budget divisor are nondegenerate,
the potential ceiling is positive, and `B / (n(n-1))` is a valid contraction
fraction in `(0,1]`. -/
theorem drift_pow_le_budget
    {B : ℝ} {n Φmax D : ℕ}
    (hn : 2 ≤ n) (hΦ : 1 ≤ Φmax) (hD : 1 ≤ D)
    (hB0 : 0 < B)
    (hB : B ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    (ENNReal.ofReal (1 - B / ((n : ℝ) * ((n : ℝ) - 1)))) ^
          (driftHorizon B n Φmax D) * (Φmax : ℝ≥0∞)
      ≤ ENNReal.ofReal (1 / ((D : ℝ) * (n : ℝ) ^ 2)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn0 hnm1
  have hΦR : (1 : ℝ) ≤ (Φmax : ℝ) := by exact_mod_cast hΦ
  have hΦ0 : (0 : ℝ) < (Φmax : ℝ) := lt_of_lt_of_le zero_lt_one hΦR
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le zero_lt_one hDR
  have hDn0 : (0 : ℝ) < (D : ℝ) * (n : ℝ) ^ 2 :=
    mul_pos hD0 (sq_pos_of_pos hn0)
  set x : ℝ := B / ((n : ℝ) * ((n : ℝ) - 1)) with hx
  have hx0 : 0 < x := by
    rw [hx]
    positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hN0]
    exact hB
  set r : ℝ := 1 - x with hr
  have hr0 : 0 ≤ r := by linarith
  have hceil :
      (((n : ℝ) * ((n : ℝ) - 1)) / B) *
          (Real.log (Φmax : ℝ) + Real.log ((D : ℝ) * (n : ℝ) ^ 2))
        ≤ (driftHorizon B n Φmax D : ℝ) := by
    exact Nat.le_ceil _
  have hxT :
      Real.log (Φmax : ℝ) + Real.log ((D : ℝ) * (n : ℝ) ^ 2)
        ≤ x * (driftHorizon B n Φmax D : ℝ) := by
    have hcancel :
        x * (((n : ℝ) * ((n : ℝ) - 1)) / B) = 1 := by
      rw [hx]
      field_simp
    calc
      Real.log (Φmax : ℝ) + Real.log ((D : ℝ) * (n : ℝ) ^ 2)
          = 1 * (Real.log (Φmax : ℝ) +
              Real.log ((D : ℝ) * (n : ℝ) ^ 2)) := by rw [one_mul]
      _ = (x * (((n : ℝ) * ((n : ℝ) - 1)) / B)) *
              (Real.log (Φmax : ℝ) +
                Real.log ((D : ℝ) * (n : ℝ) ^ 2)) := by rw [hcancel]
      _ = x * ((((n : ℝ) * ((n : ℝ) - 1)) / B) *
              (Real.log (Φmax : ℝ) +
                Real.log ((D : ℝ) * (n : ℝ) ^ 2))) := by ring
      _ ≤ x * (driftHorizon B n Φmax D : ℝ) :=
          mul_le_mul_of_nonneg_left hceil hx0.le
  have hr_exp : r ≤ Real.exp (-x) := by
    rw [hr]
    linarith [Real.add_one_le_exp (-x)]
  have hpow :
      r ^ driftHorizon B n Φmax D ≤
        Real.exp (-x) ^ driftHorizon B n Φmax D :=
    pow_le_pow_left₀ hr0 hr_exp _
  have hexp_pow :
      Real.exp (-x) ^ driftHorizon B n Φmax D =
        Real.exp (-(x * (driftHorizon B n Φmax D : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexp_mono :
      Real.exp (-(x * (driftHorizon B n Φmax D : ℝ))) ≤
        Real.exp (-(Real.log (Φmax : ℝ) +
          Real.log ((D : ℝ) * (n : ℝ) ^ 2))) := by
    rw [Real.exp_le_exp]
    linarith
  have hexp_eval :
      Real.exp (-(Real.log (Φmax : ℝ) +
          Real.log ((D : ℝ) * (n : ℝ) ^ 2))) * (Φmax : ℝ)
        = 1 / ((D : ℝ) * (n : ℝ) ^ 2) := by
    rw [neg_add_rev, Real.exp_add, Real.exp_neg, Real.exp_neg,
      Real.exp_log hDn0, Real.exp_log hΦ0]
    field_simp
  have hreal :
      r ^ driftHorizon B n Φmax D * (Φmax : ℝ)
        ≤ 1 / ((D : ℝ) * (n : ℝ) ^ 2) := by
    calc
      r ^ driftHorizon B n Φmax D * (Φmax : ℝ)
          ≤ Real.exp (-x) ^ driftHorizon B n Φmax D * (Φmax : ℝ) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = Real.exp (-(x * (driftHorizon B n Φmax D : ℝ))) *
            (Φmax : ℝ) := by rw [hexp_pow]
      _ ≤ Real.exp (-(Real.log (Φmax : ℝ) +
              Real.log ((D : ℝ) * (n : ℝ) ^ 2))) * (Φmax : ℝ) :=
            mul_le_mul_of_nonneg_right hexp_mono (by positivity)
      _ = 1 / ((D : ℝ) * (n : ℝ) ^ 2) := hexp_eval
  rw [← ENNReal.ofReal_natCast Φmax, ← ENNReal.ofReal_pow hr0,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- `NNReal`-budget form, ready for the `hdrainε` field of
`driftSurvivalPhase`. -/
theorem drift_pow_le_budget_nn
    {B : ℝ} {n Φmax D : ℕ}
    (hn : 2 ≤ n) (hΦ : 1 ≤ Φmax) (hD : 1 ≤ D)
    (hB0 : 0 < B)
    (hB : B ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    (ENNReal.ofReal (1 - B / ((n : ℝ) * ((n : ℝ) - 1)))) ^
          (driftHorizon B n Φmax D) * (Φmax : ℝ≥0∞)
      ≤ (driftBudgetNN D n : ℝ≥0∞) := by
  rw [coe_driftBudgetNN]
  exact drift_pow_le_budget hn hΦ hD hB0 hB

/-- Equivalent form with the contraction factor written as an `ENNReal`
subtraction.  This is the shape produced by the weighted-drift engine when its
drop fraction is `ENNReal.ofReal (B / (n(n-1)))`. -/
theorem drift_pow_le_budget_sub
    {B : ℝ} {n Φmax D : ℕ}
    (hn : 2 ≤ n) (hΦ : 1 ≤ Φmax) (hD : 1 ≤ D)
    (hB0 : 0 < B)
    (hB : B ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    (1 - ENNReal.ofReal (B / ((n : ℝ) * ((n : ℝ) - 1)))) ^
          (driftHorizon B n Φmax D) * (Φmax : ℝ≥0∞)
      ≤ (driftBudgetNN D n : ℝ≥0∞) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hq0 : 0 ≤ B / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg hB0.le (mul_pos hn0 hnm1).le
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub (1 : ℝ) hq0]
  exact drift_pow_le_budget_nn hn hΦ hD hB0 hB

#print axioms drift_pow_le_budget
#print axioms drift_pow_le_budget_nn
#print axioms drift_pow_le_budget_sub
#print axioms natCast_mul_driftBudgetNN_eq_inv_sq

end DriftSurvival
end Ripple.PopulationProtocol.ExactMajority
