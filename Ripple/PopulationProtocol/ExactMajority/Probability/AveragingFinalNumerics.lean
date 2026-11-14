-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingFinalNumerics.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingGlobalFailureSplice

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingFinalNumerics

open TimeTheorem AveragingNumerics AveragingObservedHourTails

/-- Every charged N13 term, including the N12 hypothesis used by the final
 assembly, is inside `3/n^2` at the plan threshold. -/
theorem averaging_complete_error_budget {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    ENNReal.ofReal (8 / (n : ℝ) ^ 5) +
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n +
      2 * hourError n + ENNReal.ofReal (1 / (n : ℝ) ^ 4) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ 2) := by
  obtain ⟨hnforty, hnpos, -, -, -, hhours⟩ := time_hour_calibration hn
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hnforty
  have hL : PhaseThreeModel.Numeric.hourIndex n + 1 =
      PhaseThreeModel.Numeric.clockHours n := by rfl
  have hhourReal :
      (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
          (n : ℝ) ^ 20 ≤ 1 / (n : ℝ) ^ 4 := by
    have hcoef : 5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2 ≤
        10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
      rw [← hL]
      push_cast
      linarith
    calc
      (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
          (n : ℝ) ^ 20 ≤
        10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) /
          (n : ℝ) ^ 20 :=
        div_le_div_of_nonneg_right hcoef (pow_pos hnpos 20).le
      _ ≤ 1 / (n : ℝ) ^ 4 := hour_test_union_scalar hn
  have hrest :
      8 / (n : ℝ) ^ 5 + 2 / (n : ℝ) ^ 4 ≤ 1 / (n : ℝ) ^ 2 := by
    clear hn hhourReal
    have hcubic : (16 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 40) hnR 3
      norm_num at this
      linarith
    have hsquare : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 40) hnR 2
      norm_num at this
      linarith
    have hpow : 8 / (n : ℝ) ^ 5 ≤ 1 / (2 * (n : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ (pow_pos hnpos 5)
        (mul_pos (by norm_num) (pow_pos hnpos 2))).2
      have h5 : (n : ℝ) ^ 5 = (n : ℝ) ^ 2 * (n : ℝ) ^ 3 := by ring
      have := mul_le_mul_of_nonneg_left hcubic (sq_nonneg (n : ℝ))
      rw [h5]
      linarith
    have hfour : 2 / (n : ℝ) ^ 4 ≤ 1 / (2 * (n : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ (pow_pos hnpos 4)
        (mul_pos (by norm_num) (pow_pos hnpos 2))).2
      have h4 : (n : ℝ) ^ 4 = (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
      have := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (n : ℝ))
      rw [h4]
      linarith
    calc
      _ ≤ 1 / (2 * (n : ℝ) ^ 2) + 1 / (2 * (n : ℝ) ^ 2) :=
        add_le_add hpow hfour
      _ = 1 / (n : ℝ) ^ 2 := by ring
  have hreal :
      8 / (n : ℝ) ^ 5 + 2 / (n : ℝ) ^ 2 +
        (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
          (n : ℝ) ^ 20 + 1 / (n : ℝ) ^ 4 ≤
        3 / (n : ℝ) ^ 2 := by
    clear hn
    simp only [div_eq_mul_inv] at hhourReal hrest ⊢
    linarith only [hhourReal, hrest]
  have hhourCast :
      5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n +
          2 * hourError n =
        ENNReal.ofReal
          ((5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
            (n : ℝ) ^ 20) := by
    unfold hourError
    have h1 : ENNReal.ofReal (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) =
        5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) + 2 := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast,
        ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    have h2 : ((5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
        (n : ℝ) ^ 20) =
        (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) * (1 / (n : ℝ) ^ 20) := by
      ring
    rw [h2, ENNReal.ofReal_mul (by positivity), h1]
    ring
  have hsum :
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) + ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        ENNReal.ofReal ((5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
          (n : ℝ) ^ 20) + ENNReal.ofReal (1 / (n : ℝ) ^ 4) =
      ENNReal.ofReal (8 / (n : ℝ) ^ 5 + 2 / (n : ℝ) ^ 2 +
        (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ) + 2) /
          (n : ℝ) ^ 20 + 1 / (n : ℝ) ^ 4) := by
    rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
  calc
    _ = ENNReal.ofReal (8 / (n : ℝ) ^ 5) + ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        (5 * (PhaseThreeModel.Numeric.hourIndex n : ℝ≥0∞) * hourError n +
          2 * hourError n) + ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by ring
    _ = _ := by rw [hhourCast, hsum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end Ripple.PopulationProtocol.ExactMajority.AveragingFinalNumerics

end
