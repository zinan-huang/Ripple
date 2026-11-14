import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar calibration for the activation clock-height estimate

This file proves only the numerical estimate. It makes no claim that the
concrete effective-minute potential has the required one-step growth.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

open TimeTheorem

def heightRate (n : ℕ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (14 / (25 * (n : ℝ)))

def heightThreshold (L : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (16 * (L + 1))

theorem one_le_heightRate (n : ℕ) : 1 ≤ heightRate n :=
  le_add_of_nonneg_right zero_le

/-- The ceilings are absorbed by the spare 7/25 logarithmic margin.
For n ≥ 4, n ln n ≥ 4. No fractional real powers are needed. -/
theorem activation_growth_exponent {n : ℕ} (hn : 4 ≤ n) :
    (14 / (25 * (n : ℝ))) * (StageEventSpec.activationHorizon n : ℝ) ≤
      7 * Real.log (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (n : ℝ) :=
        Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_three])
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  have hscale : (4 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc (4 : ℝ) ≤ n := hnR
      _ = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlog hnpos.le
  have hceil : (logWindow n 6 : ℝ) ≤
      (6 : ℝ) * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    unfold logWindow
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have htime : (StageEventSpec.activationHorizon n : ℝ) ≤
      (12 : ℝ) * (n : ℝ) * Real.log (n : ℝ) + 2 := by
    unfold StageEventSpec.activationHorizon
    push_cast
    nlinarith only [hceil]
  calc (14 / (25 * (n : ℝ))) * (StageEventSpec.activationHorizon n : ℝ) =
      (14 * (StageEventSpec.activationHorizon n : ℝ)) / (25 * (n : ℝ)) := by ring
    _ ≤ 7 * Real.log (n : ℝ) := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith only [htime, hscale]

theorem activation_height_scalar {n L : ℕ} (hn : 4 ≤ n) (hsize : n ≤ 2 ^ L) :
    heightRate n ^ StageEventSpec.activationHorizon n * (n : ℝ≥0∞) ≤
      heightThreshold L * ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  let T := StageEventSpec.activationHorizon n
  let r : ℝ := 14 / (25 * (n : ℝ))
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hrzero : 0 ≤ r := by dsimp [r]; positivity
  have hrate : heightRate n = ENNReal.ofReal (1 + r) := by
    rw [ENNReal.ofReal_add (by norm_num) hrzero, ENNReal.ofReal_one] <;> rfl
  have hpower : (1 + r) ^ T ≤ Real.exp (r * (T : ℝ)) := by
    calc (1 + r) ^ T ≤ Real.exp r ^ T :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp r]) T
      _ = Real.exp (r * (T : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hcal : r * (T : ℝ) ≤ 7 * Real.log (n : ℝ) :=
    activation_growth_exponent hn
  have hexp : Real.exp ((7 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ 7 := by
    simpa only [Real.exp_log hnpos] using (Real.exp_nat_mul (Real.log (n : ℝ)) 7)
  have hreal : (1 + r) ^ T * (n : ℝ) ≤ (n : ℝ) ^ 8 := by
    calc (1 + r) ^ T * (n : ℝ) ≤ Real.exp (r * (T : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hpower hnpos.le
      _ ≤ Real.exp (7 * Real.log (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcal) hnpos.le
      _ = (n : ℝ) ^ 8 := by rw [hexp]; ring
  have hsizeR : (n : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hsize
  have hnextPow : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ (L + 1) := by
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
  have hfloor : (n : ℝ) ^ 16 ≤ (2 : ℝ) ^ (16 * (L + 1)) := by
    calc (n : ℝ) ^ 16 ≤ ((2 : ℝ) ^ (L + 1)) ^ 16 :=
        pow_le_pow_left₀ hnpos.le (hsizeR.trans hnextPow) 16
      _ = (2 : ℝ) ^ (16 * (L + 1)) := by
        rw [← pow_mul]
        congr 1
        omega
  have hmul : (n : ℝ) ^ 8 * (n : ℝ) ^ 8 ≤ (2 : ℝ) ^ (16 * (L + 1)) := by
    nlinarith only [hfloor]
  have hquot : (n : ℝ) ^ 8 ≤
      (2 : ℝ) ^ (16 * (L + 1)) / (n : ℝ) ^ 8 :=
    (le_div_iff₀ (pow_pos hnpos 8)).2 hmul
  have hscale : (n : ℝ) ^ 8 ≤
      (2 : ℝ) ^ (16 * (L + 1)) * (1 / (n : ℝ) ^ 8) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hquot
  calc heightRate n ^ StageEventSpec.activationHorizon n * (n : ℝ≥0∞) =
      ENNReal.ofReal ((1 + r) ^ T * (n : ℝ)) := by
        rw [hrate, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_natCast n,
          ← ENNReal.ofReal_mul (pow_nonneg (by positivity) T)]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ 8) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal
        ((2 : ℝ) ^ (16 * (L + 1)) * (1 / (n : ℝ) ^ 8)) :=
      ENNReal.ofReal_le_ofReal hscale
    _ = heightThreshold L * ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      norm_num [heightThreshold]

theorem activation_height_ratio {n L : ℕ} (hn : 4 ≤ n) (hsize : n ≤ 2 ^ L) :
    heightRate n ^ StageEventSpec.activationHorizon n * (n : ℝ≥0∞) /
        heightThreshold L ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
  have hzero : heightThreshold L ≠ 0 := pow_ne_zero _ (by norm_num)
  have htop : heightThreshold L ≠ ⊤ :=
    (ENNReal.pow_lt_top (by norm_num : (2 : ℝ≥0∞) < ⊤)).ne
  exact (ENNReal.div_le_iff' hzero htop).2 (activation_height_scalar hn hsize)

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

end
