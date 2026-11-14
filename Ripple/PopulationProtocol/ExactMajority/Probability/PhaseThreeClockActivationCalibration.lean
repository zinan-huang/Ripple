-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationCalibration.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Model
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationHarmonic

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationCalibration

open PhaseThreeModel.Numeric PhaseThreeClockActivationHarmonic

def activationProbability (n j : ℕ) : ℝ :=
  2 * (j : ℝ) * ((n : ℝ) - (j : ℝ)) /
    ((n : ℝ) * ((n : ℝ) - 1))

noncomputable def macroThreshold (n : ℕ) : ℕ :=
  Nat.ceil ((99 : ℝ) * (n : ℝ) / 100)

def activationTheta (n C : ℕ) : ℝ :=
  (smallActivation C : ℝ) / (1000 * (n : ℝ))

noncomputable def activationMean (n C : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico (smallActivation C) (macroThreshold n),
    1 / activationProbability n j

theorem macroThreshold_le_population (n : ℕ) : macroThreshold n ≤ n := by
  unfold macroThreshold
  apply Nat.ceil_le.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem macroThreshold_gap (n : ℕ) :
    (n : ℝ) / 100 ≤ ((n + 1 - macroThreshold n : ℕ) : ℝ) := by
  have hb := macroThreshold_le_population n
  have hceil : (macroThreshold n : ℝ) < (99 : ℝ) * (n : ℝ) / 100 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [Nat.cast_sub (by omega : macroThreshold n ≤ n + 1),
    Nat.cast_add, Nat.cast_one]
  linarith

structure CalibrationData (n C : ℕ) : Prop where
  population_pos : 0 < (n : ℝ)
  clock_pos : 0 < (C : ℝ)
  population_large : 1000 ≤ n
  log_population_large : 1000 ≤ Real.log (n : ℝ)
  small_pos : 1 ≤ smallActivation C
  small_fraction : (smallActivation C : ℝ) ≤ (n : ℝ) / 100
  small_large : (199800000 : ℝ) ≤ smallActivation C
  small_le_macro : smallActivation C ≤ macroThreshold n
  macro_le_population : macroThreshold n ≤ n
  log_ratio :
    Real.log (n : ℝ) - Real.log (smallActivation C : ℝ) ≤
      (99 / 100 : ℝ) * Real.log (n : ℝ) + 1 / 50
  log_clock_le_population : Real.log (C : ℝ) ≤ Real.log (n : ℝ)

theorem activation_calibration_data {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    CalibrationData n C := by
  obtain ⟨hCp, hx, hxy, hyx, -⟩ := logarithmic_inputs hn hlo hCn
  have hCnR : (C : ℝ) ≤ n := by exact_mod_cast hCn
  have hnp : 0 < (n : ℝ) := hCp.trans_le hCnR
  have hCsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hCp] at hCsize
  have hnlarge : 1000 ≤ n := by
    have h : (1000 : ℝ) ≤ n := by linarith
    exact_mod_cast h
  have hylarge : 1000 ≤ Real.log (n : ℝ) := by linarith
  have hrfrac := (cutoff_calibration hCp hx hCn).2.1
  have hrceil : (C : ℝ) ^ (1 / 100 : ℝ) ≤ (smallActivation C : ℝ) := Nat.le_ceil _
  have hrpower := (new_power_calibration hCp hx).2.2.2
  have hrlarge : (199800000 : ℝ) ≤ smallActivation C := by linarith
  have hrpos : 1 ≤ smallActivation C := by
    have h : (1 : ℝ) ≤ smallActivation C := by linarith
    exact_mod_cast h
  have hblog : (99 : ℝ) * (n : ℝ) / 100 ≤ (macroThreshold n : ℝ) := Nat.le_ceil _
  have hrb : smallActivation C ≤ macroThreshold n := by
    have h : (smallActivation C : ℝ) ≤ macroThreshold n := by linarith
    exact_mod_cast h
  have hrlog := Real.log_le_log (Real.rpow_pos_of_pos hCp (1 / 100 : ℝ)) hrceil
  rw [Real.log_rpow hCp] at hrlog
  have hratio :
      Real.log (n : ℝ) - Real.log (smallActivation C : ℝ) ≤
        (99 / 100 : ℝ) * Real.log (n : ℝ) + 1 / 50 := by
    linarith only [hrlog, hyx]
  exact ⟨hnp, hCp, hnlarge, hylarge, hrpos, hrfrac, hrlarge, hrb,
    macroThreshold_le_population n, hratio, hxy⟩

theorem activation_probability_floor_aux (n r j : ℕ)
    (hn : 2 ≤ n) (hr : (r : ℝ) ≤ (n : ℝ) / 100)
    (hrj : r ≤ j) (hjb : j < macroThreshold n) :
    (r : ℝ) / (n : ℝ) ≤ activationProbability n j := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  have hnm : 0 < (n : ℝ) - 1 := by linarith
  have hrjR : (r : ℝ) ≤ j := by exact_mod_cast hrj
  have hjR : (j : ℝ) < (99 : ℝ) * (n : ℝ) / 100 := Nat.lt_ceil.mp hjb
  have hcore : (r : ℝ) * ((n : ℝ) - 1) ≤
      2 * (j : ℝ) * ((n : ℝ) - (j : ℝ)) := by
    by_cases hhalf : 2 * (j : ℝ) ≤ n
    · have hprod := mul_nonneg (Nat.cast_nonneg j)
        (show (0 : ℝ) ≤ (n : ℝ) - 2 * (j : ℝ) + 1 by linarith)
      have hmono := mul_le_mul_of_nonneg_right hrjR hnm.le
      nlinarith only [hprod, hmono]
    · have hprod := mul_nonneg
        (show (0 : ℝ) ≤ 2 * (j : ℝ) - (n : ℝ) by linarith)
        (show (0 : ℝ) ≤ (n : ℝ) - (j : ℝ) by linarith)
      have hsmall := mul_nonneg (Nat.cast_nonneg n)
        (show (0 : ℝ) ≤ (n : ℝ) - (j : ℝ) - (r : ℝ) by linarith)
      have hrnon : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith only [hprod, hsmall, hrnon]
  have hdivide : (r : ℝ) ≤
      2 * (j : ℝ) * ((n : ℝ) - (j : ℝ)) / ((n : ℝ) - 1) :=
    (le_div_iff₀ hnm).2 hcore
  unfold activationProbability
  rw [mul_comm (n : ℝ) ((n : ℝ) - 1), div_mul_eq_div_div]
  exact div_le_div_of_nonneg_right hdivide hnp.le

theorem activation_probability_floor {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n)
    (j : ℕ) (hrj : smallActivation C ≤ j) (hjb : j < macroThreshold n) :
    (smallActivation C : ℝ) / (n : ℝ) ≤ activationProbability n j := by
  have hd := activation_calibration_data hn hlo hCn
  exact activation_probability_floor_aux n (smallActivation C) j
    (by have h := hd.population_large; omega) hd.small_fraction hrj hjb

theorem activation_probability_reciprocal (n j : ℕ)
    (hj : 1 ≤ j) (hjn : j < n) :
    1 / activationProbability n j =
      ((n : ℝ) - 1) / 2 * (1 / (j : ℝ) + 1 / ((n : ℝ) - (j : ℝ))) := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hdiff : 0 < (n : ℝ) - (j : ℝ) := by
    have h : (j : ℝ) < n := by exact_mod_cast hjn
    linarith
  unfold activationProbability
  rw [one_div_div]
  field_simp [ne_of_gt hjp, ne_of_gt hdiff]
  <;> ring

theorem activation_mean_log_bound (n r b : ℕ)
    (hr : 1 ≤ r) (hrb : r ≤ b) (hbn : b ≤ n)
    (hgap : (n : ℝ) / 100 ≤ ((n + 1 - b : ℕ) : ℝ)) :
    (∑ j ∈ Finset.Ico r b, 1 / activationProbability n j) ≤
      (n : ℝ) / 2 *
        (Real.log (n : ℝ) - Real.log (r : ℝ) + Real.log (100 : ℝ) + 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hfront := sum_reciprocal_Ico_le_log_population n r b hr hrb hbn
  have hback := sum_reverse_reciprocal_le_log_hundred n r b hr hrb hbn hgap
  have hsum :
      (∑ j ∈ Finset.Ico r b, 1 / (j : ℝ)) +
        (∑ j ∈ Finset.Ico r b, 1 / ((n : ℝ) - (j : ℝ))) ≤
      Real.log (n : ℝ) - Real.log (r : ℝ) + Real.log (100 : ℝ) + 2 := by
    linarith only [hfront, hback]
  have hlog := Real.log_le_log
    (by exact_mod_cast (show 0 < r by omega) : 0 < (r : ℝ))
    (by exact_mod_cast (hrb.trans hbn) : (r : ℝ) ≤ n)
  have hloghundred : 0 ≤ Real.log (100 : ℝ) := Real.log_nonneg (by norm_num)
  have hbar : 0 ≤ Real.log (n : ℝ) - Real.log (r : ℝ) + Real.log (100 : ℝ) + 2 := by
    linarith only [hlog, hloghundred]
  calc
    _ = ∑ j ∈ Finset.Ico r b,
        ((n : ℝ) - 1) / 2 * (1 / (j : ℝ) + 1 / ((n : ℝ) - (j : ℝ))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h := Finset.mem_Ico.mp hj
      exact activation_probability_reciprocal n j (by omega) (by omega)
    _ = ((n : ℝ) - 1) / 2 *
        ((∑ j ∈ Finset.Ico r b, 1 / (j : ℝ)) +
          (∑ j ∈ Finset.Ico r b, 1 / ((n : ℝ) - (j : ℝ)))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ((n : ℝ) - 1) / 2 *
        (Real.log (n : ℝ) - Real.log (r : ℝ) + Real.log (100 : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hbar

theorem activation_mean_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    activationMean n C ≤
      (499 / 1000 : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by
  have hd := activation_calibration_data hn hlo hCn
  have hmean := activation_mean_log_bound n (smallActivation C) (macroThreshold n)
    hd.small_pos hd.small_le_macro hd.macro_le_population (macroThreshold_gap n)
  have hbar :
      Real.log (n : ℝ) - Real.log (smallActivation C : ℝ) + Real.log (100 : ℝ) + 2 ≤
        (499 / 500 : ℝ) * Real.log (n : ℝ) := by
    have hratio := hd.log_ratio
    have hy := hd.log_population_large
    have hhundred := log_small_bounds.2.2
    linarith only [hratio, hy, hhundred]
  calc
    activationMean n C ≤ (n : ℝ) / 2 *
        (Real.log (n : ℝ) - Real.log (smallActivation C : ℝ) +
          Real.log (100 : ℝ) + 2) := hmean
    _ ≤ (n : ℝ) / 2 * ((499 / 500 : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hbar (by positivity)
    _ = _ := by ring

theorem activation_rate_mgf_inputs {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    0 ≤ activationTheta n C ∧
      ∀ j ∈ Finset.Ico (smallActivation C) (macroThreshold n),
        0 < activationProbability n j ∧
          activationTheta n C / activationProbability n j ≤ (1 / 1000 : ℝ) := by
  have hd := activation_calibration_data hn hlo hCn
  have hθ : 0 ≤ activationTheta n C := by unfold activationTheta; positivity
  refine ⟨hθ, ?_⟩
  intro j hj
  obtain ⟨hrj, hjb⟩ := Finset.mem_Ico.mp hj
  have hf := activation_probability_floor hn hlo hCn j hrj hjb
  have hrp : 0 < (smallActivation C : ℝ) := by
    exact_mod_cast (show 0 < smallActivation C by have h := hd.small_pos; omega)
  have hp : 0 < activationProbability n j := (div_pos hrp hd.population_pos).trans_le hf
  refine ⟨hp, (div_le_iff₀ hp).2 ?_⟩
  have hsmall : activationTheta n C ≤ activationProbability n j / 1000 := by
    unfold activationTheta
    rw [mul_comm (1000 : ℝ) (n : ℝ), div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hf (by norm_num)
  linarith only [hsmall]

theorem activation_exponential_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    Real.exp (-(smallActivation C : ℝ) * Real.log (n : ℝ) / 1998000) ≤
      1 / (C : ℝ) ^ 100 := by
  have hd := activation_calibration_data hn hlo hCn
  have hx : 0 ≤ Real.log (C : ℝ) := by
    have h := (logarithmic_inputs hn hlo hCn).2.1
    linarith
  have hprod := mul_le_mul_of_nonneg_right hd.small_large hx
  have hlogs := mul_le_mul_of_nonneg_left hd.log_clock_le_population
    (Nat.cast_nonneg (smallActivation C))
  have harg : -(smallActivation C : ℝ) * Real.log (n : ℝ) / 1998000 ≤
      -(100 * Real.log (C : ℝ)) := by
    linarith only [hprod, hlogs]
  calc
    _ ≤ Real.exp (-(100 * Real.log (C : ℝ))) := Real.exp_le_exp.mpr harg
    _ = _ := by
      rw [Real.exp_neg, show (100 : ℝ) * Real.log (C : ℝ) = ((100 : ℕ) : ℝ) * Real.log (C : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hd.clock_pos, one_div]

theorem activation_mgf_coefficient_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ (C : ℝ)) (hCn : C ≤ n) :
    Real.exp ((1000 / 999 : ℝ) * activationTheta n C *
        (∑ j ∈ Finset.Ico (smallActivation C) (macroThreshold n),
          1 / activationProbability n j) -
      activationTheta n C * (activationHalfHorizon n : ℝ)) ≤
        1 / (C : ℝ) ^ 100 := by
  have hd := activation_calibration_data hn hlo hCn
  have hθ := (activation_rate_mgf_inputs hn hlo hCn).1
  have hmean := activation_mean_calibration hn hlo hCn
  have hN : (n : ℝ) * Real.log (n : ℝ) / 2 ≤ (activationHalfHorizon n : ℝ) :=
    Nat.le_ceil _
  have hmulMean := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ (1000 / 999 : ℝ) * activationTheta n C by positivity)
  have hmulN := mul_le_mul_of_nonneg_left hN hθ
  have heq :
      (1000 / 999 : ℝ) * activationTheta n C *
          ((499 / 1000 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) -
        activationTheta n C * ((n : ℝ) * Real.log (n : ℝ) / 2) =
      -(smallActivation C : ℝ) * Real.log (n : ℝ) / 1998000 := by
    unfold activationTheta
    field_simp [ne_of_gt hd.population_pos]
    <;> ring
  have harg :
      (1000 / 999 : ℝ) * activationTheta n C * activationMean n C -
          activationTheta n C * (activationHalfHorizon n : ℝ) ≤
        -(smallActivation C : ℝ) * Real.log (n : ℝ) / 1998000 := by
    linarith only [hmulMean, hmulN, heq]
  exact (Real.exp_le_exp.mpr harg).trans (activation_exponential_calibration hn hlo hCn)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationCalibration

end
