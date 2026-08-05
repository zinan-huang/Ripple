/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Error
import Tri.Theorem6Parameters
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Power-law envelope for the fixed Theorem 6 error

The activation error has exponent `q / 16`.  Comparing the real logarithm
with the floor binary logarithm turns this exponential into an inverse power
of the population.  It can then be combined with the ordinary-Tri error by
taking the smaller exponent.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Explicit inverse-power exponent supplied by the activation route. -/
def theorem6FixedActivationExponent : ℝ :=
  1 / 32

theorem theorem6FixedActivationExponent_pos :
    0 < theorem6FixedActivationExponent := by
  norm_num [theorem6FixedActivationExponent]

/-- The natural logarithm of an integer is at most twice its floor binary
logarithm once the integer is at least three. -/
theorem real_log_nat_le_two_mul_natLog
    (n : ℕ)
    (h3 : 3 ≤ n) :
    Real.log (n : ℝ) ≤
      2 * (Nat.log 2 n : ℝ) := by
  let ell := Nat.log 2 n
  have hnpos : 0 < n := by omega
  have hellpos : 0 < ell := by
    dsimp [ell]
    exact Nat.log_pos (by norm_num) (by omega)
  have hell1 : 1 ≤ ell := hellpos
  have hnlt : n < 2 ^ (ell + 1) := by
    simpa [ell, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self
        (b := 2) (by norm_num) n)
  have hnposR : 0 < (n : ℝ) := by
    exact_mod_cast hnpos
  rw [Real.log_le_iff_le_exp hnposR]
  calc
    (n : ℝ) ≤ (2 : ℝ) ^ (ell + 1) := by
      exact_mod_cast hnlt.le
    _ ≤ (Real.exp 1) ^ (ell + 1) := by
      gcongr
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    _ = Real.exp (((ell + 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ Real.exp (2 * (ell : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact_mod_cast
        (show ell + 1 ≤ 2 * ell by omega)

/-- The fixed activation error is at most
`n⁻¹ ^ ((1 / 32) * γ)`. -/
theorem infectionActivationFinalError_le_power
    (n γ : ℕ)
    (h3 : 3 ≤ n)
    (hγ : 1 ≤ γ) :
    infectionActivationFinalError
        (theorem6Q n γ) ≤
      (n : ℝ≥0∞)⁻¹ ^
        (theorem6FixedActivationExponent * (γ : ℝ)) := by
  have hlog := real_log_nat_le_two_mul_natLog n h3
  have hγR : 0 < (γ : ℝ) := by
    exact_mod_cast hγ
  have hmul :
      (γ : ℝ) * Real.log (n : ℝ) ≤
        (γ : ℝ) *
          (2 * (Nat.log 2 n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog hγR.le
  have hreal :
      -(((theorem6Q n γ : ℕ) : ℝ) / 16) ≤
        theorem6FixedActivationExponent * (γ : ℝ) *
          (-Real.log (n : ℝ)) := by
    norm_num [theorem6FixedActivationExponent,
      theorem6Q, Nat.cast_mul] at ⊢
    nlinarith [hmul]
  have hn0 : n ≠ 0 := by omega
  have hn0E : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hn0
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := by simp
  unfold infectionActivationFinalError
  rw [← EReal.exp_coe]
  rw [EReal.ENNReal.rpow_eq_exp_mul_log]
  rw [EReal.exp_le_exp_iff]
  rw [ENNReal.log_inv,
    ENNReal.log_pos_real hn0E hntop]
  simp only [ENNReal.toReal_natCast]
  norm_cast

/-- The activation and ordinary-Tri errors fit twice the slower inverse-power
envelope. -/
theorem theorem6FixedError_le_two_power
    (n γ : ℕ)
    (c : ℝ)
    (h3 : 3 ≤ n)
    (hγ : 1 ≤ γ) :
    infectionActivationFinalError
          (theorem6Q n γ) +
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ)) ≤
      2 * ((n : ℝ≥0∞)⁻¹ ^
        (min theorem6FixedActivationExponent c *
          (γ : ℝ))) := by
  let base : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹
  have hact :
      infectionActivationFinalError
          (theorem6Q n γ) ≤
        base ^
          (theorem6FixedActivationExponent *
            (γ : ℝ)) := by
    simpa [base] using
      infectionActivationFinalError_le_power
        n γ h3 hγ
  have hbase : base ≤ 1 := by
    dsimp [base]
    rw [ENNReal.inv_le_one]
    exact_mod_cast (show 1 ≤ n by omega)
  have hγR : 0 ≤ (γ : ℝ) := by positivity
  have hminAct :
      min theorem6FixedActivationExponent c *
          (γ : ℝ) ≤
        theorem6FixedActivationExponent * (γ : ℝ) :=
    mul_le_mul_of_nonneg_right
      (min_le_left _ _) hγR
  have hminC :
      min theorem6FixedActivationExponent c *
          (γ : ℝ) ≤
        c * (γ : ℝ) :=
    mul_le_mul_of_nonneg_right
      (min_le_right _ _) hγR
  have hactPow :
      base ^
          (theorem6FixedActivationExponent *
            (γ : ℝ)) ≤
        base ^
          (min theorem6FixedActivationExponent c *
            (γ : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge
      hbase hminAct
  have hcPow :
      base ^ (c * (γ : ℝ)) ≤
        base ^
          (min theorem6FixedActivationExponent c *
            (γ : ℝ)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge
      hbase hminC
  calc
    infectionActivationFinalError
          (theorem6Q n γ) +
        (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))
        ≤ base ^
              (theorem6FixedActivationExponent *
                (γ : ℝ)) +
            base ^ (c * (γ : ℝ)) := by
          simpa [base] using add_le_add hact le_rfl
    _ ≤ base ^
            (min theorem6FixedActivationExponent c *
              (γ : ℝ)) +
          base ^
            (min theorem6FixedActivationExponent c *
              (γ : ℝ)) :=
      add_le_add hactPow hcPow
    _ = 2 * (base ^
          (min theorem6FixedActivationExponent c *
            (γ : ℝ))) := by ring

end

end Tri

#print axioms Tri.theorem6FixedActivationExponent_pos
#print axioms Tri.real_log_nat_le_two_mul_natLog
#print axioms Tri.infectionActivationFinalError_le_power
#print axioms Tri.theorem6FixedError_le_two_power
