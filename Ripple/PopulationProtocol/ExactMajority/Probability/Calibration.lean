import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Scalar population calibration

The population bound remains symbolic. Clock and late-phase calibration records
contain only real inequalities, independent of any stochastic event.
-/

namespace Ripple.PopulationProtocol.ExactMajority.Calibration

/-- The common population threshold for the stabilization estimates. -/
def populationThreshold : ℕ := 5 * 2 ^ (2 ^ 23)

/-- A symbolic exponent wrapper prevents evaluation of the population bound. -/
def populationThresholdAt (e : ℕ) : ℕ := 5 * 2 ^ e

/-- The scalar inputs used by the clock estimates. -/
structure ClockCalibration (x y d Q : ℝ) : Prop where
  x_lower : 4194304 ≤ x
  log_mono : x ≤ y
  log_ratio : y ≤ x + 2
  width_lower : 38 ≤ d
  width_upper : d ≤ x / 80000
  cap_upper : Q ≤ 1024 * x

/-- The common late-phase logarithmic floor. -/
structure LateCalibration (y : ℝ) : Prop where
  log_lower : 500000 ≤ y

/-- A power lower bound supplies the common logarithmic floor. -/
theorem logarithm_lower_of_power {C : ℝ} {e : ℕ}
    (he : 2 ^ 23 ≤ e) (hbase : (2 : ℝ) ^ e ≤ C) :
    (4194304 : ℝ) ≤ Real.log C := by
  have hp : 0 < (2 : ℝ) ^ e := pow_pos (by norm_num) e
  have hlog := Real.log_le_log hp hbase
  rw [Real.log_pow] at hlog
  have heReal : (8388608 : ℝ) ≤ e := by exact_mod_cast he
  have htwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    linarith only [h]
  have hmul := mul_le_mul heReal htwo (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (Nat.cast_nonneg e)
  linarith only [hlog, hmul]

/-- The logarithmic floor follows without expanding the population threshold. -/
theorem population_log_lower_of_exponent {n e : ℕ}
    (he : 2 ^ 23 ≤ e) (hn : populationThresholdAt e ≤ n) :
    (4194304 : ℝ) ≤ Real.log (n : ℝ) := by
  change 5 * 2 ^ e ≤ n at hn
  have hnreal : (5 : ℝ) * (2 : ℝ) ^ e ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hp : 0 < (2 : ℝ) ^ e := pow_pos (by norm_num) e
  have hbase : (2 : ℝ) ^ e ≤ (n : ℝ) := by nlinarith only [hnreal, hp]
  exact logarithm_lower_of_power he hbase

theorem population_log_lower {n : ℕ} (hn : populationThreshold ≤ n) :
    (4194304 : ℝ) ≤ Real.log (n : ℝ) := by
  exact population_log_lower_of_exponent (e := 2 ^ 23) le_rfl hn

theorem lateCalibration_of_threshold {n : ℕ} (hn : populationThreshold ≤ n) :
    LateCalibration (Real.log (n : ℝ)) := by
  constructor
  linarith only [population_log_lower hn]

end Ripple.PopulationProtocol.ExactMajority.Calibration
