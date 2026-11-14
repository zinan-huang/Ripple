-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarkCalibration.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Model

noncomputable section

open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkCalibration

open PhaseThreeModel.Numeric

noncomputable def immigrationBudget (n C : ℕ) : ℝ :=
  (2 * (earlyCutoff C : ℝ) ^ 2 / (n : ℝ) ^ 2) *
      (activationHalfHorizon n : ℝ) +
    (2 * (earlyCutoff C : ℝ) ^ 2 / (C : ℝ) ^ 2) * (fineTicks C : ℝ)

noncomputable def growthBudget (n C : ℕ) : ℝ :=
  (561 / 1000 : ℝ) * ((activationHalfHorizon n : ℝ) / (n : ℝ)) +
    2 * (fineTicks C : ℝ) / ((C : ℝ) - 1)

noncomputable def risingCoefficient (n C : ℕ) : ℝ :=
  (3 * (markOrder C : ℝ)) ^ markOrder C *
      Real.exp ((markOrder C : ℝ) * growthBudget n C) /
    ((C : ℝ) ^ (1 / 3 : ℝ)) ^ markOrder C

theorem rpow_square (x u : ℝ) (hx : 0 ≤ x) :
    (x ^ u) ^ 2 = x ^ (2 * u) := by
  rw [← Real.rpow_natCast (x ^ u) 2, ← Real.rpow_mul hx]
  congr 1
  ring

theorem markOrder_bounds {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    1 ≤ markOrder C ∧
      (C : ℝ) ^ (1 / 25 : ℝ) ≤ (markOrder C : ℝ) ∧
      (markOrder C : ℝ) ≤ 2 * (C : ℝ) ^ (1 / 25 : ℝ) := by
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCone : (1 : ℝ) ≤ C := by linarith
  have hone := rpow_ge_one hCone (show (0 : ℝ) ≤ 1 / 25 by norm_num)
  have hlo : (C : ℝ) ^ (1 / 25 : ℝ) ≤ (markOrder C : ℝ) := Nat.le_ceil _
  have hhi : (markOrder C : ℝ) < (C : ℝ) ^ (1 / 25 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hC.le _)
  refine ⟨?_, hlo, by linarith⟩
  have hreal : (1 : ℝ) ≤ markOrder C := hone.trans hlo
  exact_mod_cast hreal

theorem earlyCutoff_square_bound {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    (earlyCutoff C : ℝ) ^ 2 ≤ 4 * (C : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ) := by
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCone : (1 : ℝ) ≤ C := by linarith
  have hone := rpow_ge_one hCone (show (0 : ℝ) ≤ 51 / 100 by norm_num)
  have hceil : (earlyCutoff C : ℝ) < (C : ℝ) ^ (51 / 100 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hC.le _)
  have hw : (earlyCutoff C : ℝ) ≤ 2 * (C : ℝ) ^ (51 / 100 : ℝ) := by linarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (earlyCutoff C) : (0 : ℝ) ≤ _) hw 2
  have hpower : ((C : ℝ) ^ (51 / 100 : ℝ)) ^ 2 =
      (C : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ) := by
    rw [rpow_square _ _ hC.le]
    rw [show (2 : ℝ) * (51 / 100) = 1 + 1 / 50 by ring,
      Real.rpow_add hC, Real.rpow_one]
  nlinarith only [hsq, hpower]

theorem markOrder_lt_mark_threshold {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    (markOrder C : ℝ) < (C : ℝ) ^ (1 / 3 : ℝ) := by
  have ha := (markOrder_bounds hC hx).2.2
  have hlinear := rpow_linear_lower hC (22 / 75 : ℝ)
  have htwo : (2 : ℝ) < (C : ℝ) ^ (22 / 75 : ℝ) := by linarith
  have hp : 0 < (C : ℝ) ^ (1 / 25 : ℝ) := Real.rpow_pos_of_pos hC _
  calc
    (markOrder C : ℝ) ≤ 2 * (C : ℝ) ^ (1 / 25 : ℝ) := ha
    _ < (C : ℝ) ^ (1 / 25 : ℝ) * (C : ℝ) ^ (22 / 75 : ℝ) := by
      simpa only [mul_comm] using mul_lt_mul_of_pos_left htwo hp
    _ = (C : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hC]
      congr 1
      ring

theorem initial_mark_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    1 ≤ markOrder C ∧ smallActivation C + 1 ≤ markOrder C ∧
      (markOrder C : ℝ) < (C : ℝ) ^ (1 / 3 : ℝ) ∧
      0 < (C : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hn hlo hCn
  exact ⟨(markOrder_bounds hC hx).1, (cutoff_calibration hC hx hCn).1,
    markOrder_lt_mark_threshold hC hx, Real.rpow_pos_of_pos hC _⟩

theorem half_horizon_bound (n : ℕ) (hn : (1 : ℝ) ≤ n)
    (hy : 8 ≤ Real.log (n : ℝ)) :
    (activationHalfHorizon n : ℝ) ≤
      (5 / 8 : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by linarith
  have hypos : 0 ≤ Real.log (n : ℝ) := by linarith
  have hceil : (activationHalfHorizon n : ℝ) <
      (n : ℝ) * Real.log (n : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hmul := mul_nonneg (sub_nonneg.mpr hn) hypos
  nlinarith only [hceil, hmul, hy]

theorem immigration_mean_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    immigrationBudget n C ≤ (markOrder C : ℝ) / 4 := by
  obtain ⟨hC, hx, hxy, hyx, -⟩ := logarithmic_inputs hn hlo hCn
  have hCnR : (C : ℝ) ≤ n := by exact_mod_cast hCn
  have hnp : 0 < (n : ℝ) := hC.trans_le hCnR
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hnOne : (1 : ℝ) ≤ n := by linarith
  have hy : 8 ≤ Real.log (n : ℝ) := by linarith
  have hypos : 0 ≤ Real.log (n : ℝ) := by linarith
  have hN := half_horizon_bound n hnOne hy
  have hw := earlyCutoff_square_bound hC hx
  let U : ℝ := (C : ℝ) ^ (1 / 50 : ℝ)
  have hU : 0 ≤ U := Real.rpow_nonneg hC.le _
  have hraw :
      (2 * (earlyCutoff C : ℝ) ^ 2 / (n : ℝ) ^ 2) *
          (activationHalfHorizon n : ℝ) ≤
        5 * Real.log (n : ℝ) * U := by
    have hcoef :
        2 * (earlyCutoff C : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
          8 * (C : ℝ) * U / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by dsimp only [U]; nlinarith only [hw]) (sq_nonneg _)
    have hratio : (C : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnp).2 hCnR
    calc
      _ ≤ (8 * (C : ℝ) * U / (n : ℝ) ^ 2) *
          (activationHalfHorizon n : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
      _ ≤ (8 * (C : ℝ) * U / (n : ℝ) ^ 2) *
          ((5 / 8 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = (5 * U * Real.log (n : ℝ)) * ((C : ℝ) / (n : ℝ)) := by
        field_simp [ne_of_gt hnp]
        <;> ring
      _ ≤ (5 * U * Real.log (n : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have htick :
      (2 * (earlyCutoff C : ℝ) ^ 2 / (C : ℝ) ^ 2) * (fineTicks C : ℝ) ≤
        1600 * (frontWidth C : ℝ) * U := by
    have hcoef :
        2 * (earlyCutoff C : ℝ) ^ 2 / (C : ℝ) ^ 2 ≤
          8 * (C : ℝ) * U / (C : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by dsimp only [U]; nlinarith only [hw]) (sq_nonneg _)
    calc
      _ ≤ (8 * (C : ℝ) * U / (C : ℝ) ^ 2) * (fineTicks C : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
      _ = _ := by
        simp only [fineTicks, Nat.cast_mul, Nat.cast_ofNat]
        field_simp [ne_of_gt hC]
        <;> ring
  have hd := (frontWidth_bounds hx).2.1.trans (frontWidth_bounds hx).2.2
  have htime : 5 * Real.log (n : ℝ) + 1600 * (frontWidth C : ℝ) ≤
      10 * Real.log (C : ℝ) := by
    linarith only [hyx, hd, hx]
  have hpower : 40 * Real.log (C : ℝ) ≤ U := (new_power_calibration hC hx).1
  have hproduct := mul_le_mul_of_nonneg_right hpower hU
  have hsquare : U ^ 2 = (C : ℝ) ^ (1 / 25 : ℝ) := by
    dsimp only [U]
    rw [rpow_square _ _ hC.le]
    norm_num
  have ha : (C : ℝ) ^ (1 / 25 : ℝ) ≤ (markOrder C : ℝ) := Nat.le_ceil _
  have hfinal : 10 * Real.log (C : ℝ) * U ≤ (markOrder C : ℝ) / 4 := by
    nlinarith only [hproduct, hsquare, ha]
  calc
    immigrationBudget n C ≤
        5 * Real.log (n : ℝ) * U + 1600 * (frontWidth C : ℝ) * U :=
      add_le_add hraw htick
    _ = (5 * Real.log (n : ℝ) + 1600 * (frontWidth C : ℝ)) * U := by ring
    _ ≤ (10 * Real.log (C : ℝ)) * U := mul_le_mul_of_nonneg_right htime hU
    _ ≤ _ := hfinal

theorem immigration_exponential_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    Real.exp (immigrationBudget n C - Real.log 2 * (markOrder C : ℝ)) ≤
      Real.exp (-(markOrder C : ℝ) / 3) := by
  have hm := immigration_mean_calibration hn hlo hCn
  have hlog := mul_le_mul_of_nonneg_right log_two_bounds.1
    (Nat.cast_nonneg (markOrder C))
  apply Real.exp_le_exp.mpr
  have ha : (0 : ℝ) ≤ markOrder C := Nat.cast_nonneg _
  linarith only [hm, hlog, ha]

theorem growth_budget_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    growthBudget n C ≤ (29 / 100 : ℝ) * Real.log (C : ℝ) :=
  (horizon_calibration hn hlo hCn).2.2

theorem rising_coefficient_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    risingCoefficient n C ≤ Real.exp (-(markOrder C : ℝ)) := by
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hn hlo hCn
  have ha := (markOrder_bounds hC hx).2.2
  have hg := growth_budget_calibration hn hlo hCn
  have he :
      Real.exp (growthBudget n C) ≤ (C : ℝ) ^ (29 / 100 : ℝ) := by
    calc
      _ ≤ Real.exp ((29 / 100 : ℝ) * Real.log (C : ℝ)) := Real.exp_le_exp.mpr hg
      _ = _ := by
        rw [Real.rpow_def_of_pos hC]
        congr 1
        ring
  have hnum :
      3 * (markOrder C : ℝ) * Real.exp (growthBudget n C) ≤
        6 * (C : ℝ) ^ (33 / 100 : ℝ) := by
    calc
      _ ≤ (6 * (C : ℝ) ^ (1 / 25 : ℝ)) * Real.exp (growthBudget n C) :=
        mul_le_mul_of_nonneg_right (by linarith only [ha]) (Real.exp_nonneg _)
      _ ≤ (6 * (C : ℝ) ^ (1 / 25 : ℝ)) * (C : ℝ) ^ (29 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by
        rw [show (33 / 100 : ℝ) = 1 / 25 + 29 / 100 by ring, Real.rpow_add hC]
        ring
  have hbase :
      3 * (markOrder C : ℝ) * Real.exp (growthBudget n C) /
          (C : ℝ) ^ (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    calc
      _ ≤ 6 * (C : ℝ) ^ (33 / 100 : ℝ) / (C : ℝ) ^ (1 / 3 : ℝ) :=
        div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hC.le _)
      _ = 6 * (C : ℝ) ^ (-(1 / 300 : ℝ)) := by
        rw [show -(1 / 300 : ℝ) = 33 / 100 - 1 / 3 by ring, Real.rpow_sub hC]
        ring
      _ ≤ _ := (exponential_error_calibration hC hx).2.2
  have hbaseNonneg :
      0 ≤ 3 * (markOrder C : ℝ) * Real.exp (growthBudget n C) /
        (C : ℝ) ^ (1 / 3 : ℝ) := by positivity
  calc
    risingCoefficient n C =
        (3 * (markOrder C : ℝ) * Real.exp (growthBudget n C) /
          (C : ℝ) ^ (1 / 3 : ℝ)) ^ markOrder C := by
      unfold risingCoefficient
      rw [Real.exp_nat_mul, ← mul_pow, ← div_pow]
    _ ≤ (Real.exp (-1)) ^ markOrder C :=
      pow_le_pow_left₀ hbaseNonneg hbase (markOrder C)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem negative_hundred_rpow_eq (C : ℕ) :
    (C : ℝ) ^ (-100 : ℝ) = 1 / (C : ℝ) ^ 100 := by
  calc
    (C : ℝ) ^ (-100 : ℝ) = ((C : ℝ) ^ (100 : ℝ))⁻¹ :=
      Real.rpow_neg (Nat.cast_nonneg C) 100
    _ = _ := by first | rw [Real.rpow_ofNat, one_div] | simp [one_div]

theorem two_period_error_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    Real.exp (immigrationBudget n C - Real.log 2 * (markOrder C : ℝ)) +
        risingCoefficient n C ≤ 1 / (C : ℝ) ^ 100 := by
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hn hlo hCn
  calc
    _ ≤ Real.exp (-(markOrder C : ℝ) / 3) + Real.exp (-(markOrder C : ℝ)) :=
      add_le_add (immigration_exponential_calibration hn hlo hCn)
        (rising_coefficient_calibration hn hlo hCn)
    _ ≤ (C : ℝ) ^ (-100 : ℝ) := (exponential_error_calibration hC hx).1
    _ = _ := negative_hundred_rpow_eq C

theorem two_period_error_ennreal_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    ENNReal.ofReal (Real.exp (immigrationBudget n C - Real.log 2 * (markOrder C : ℝ))) +
        ENNReal.ofReal (risingCoefficient n C) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) := by
  have hr : 0 ≤ risingCoefficient n C := by unfold risingCoefficient; positivity
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) hr]
  exact ENNReal.ofReal_le_ofReal (two_period_error_calibration hn hlo hCn)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkCalibration

end
