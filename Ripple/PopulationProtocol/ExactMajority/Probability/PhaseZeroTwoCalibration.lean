import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoDispatchAmplification
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongGapBackupTail

/-!
# Exact early-stage time and error calibration

These scalar lemmas use the actual clockHours and literal ceiling horizons.
The population threshold is consumed only through the public calibration
lemmas; its enormous numeral is never unfolded.

The probability budget records Phase 0, weak drain, the actual phase-one
timer, the first threshold flood, two dispatch blocks, Phase-3 activation,
and the strong-gap backup tail. This file asserts no missing producer.
-/

noncomputable section

open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseZeroTwoCalibration

open TimeTheorem PhaseOneDrain
open PhaseThreeModel.Numeric

theorem log_le_hour_fraction (n : ℕ) :
    Real.log (n : ℝ) ≤ (25 / 36 : ℝ) * (clockHours n : ℝ) :=
  PhaseThreeModel.Numeric.log_le_hour_fraction n

theorem log_add_one_le_clockHours (n : ℕ) :
    Real.log (n : ℝ) + 1 ≤ (clockHours n : ℝ) := by
  have htwo : 0 < Real.log (2 : ℝ) := by linarith only [log_two_bounds.1]
  have hindex : Real.log (n : ℝ) ≤ (hourIndex n : ℝ) * Real.log 2 := by
    apply (div_le_iff₀ htwo).mp
    rw [hourIndex_eq_real_ceiling]
    exact Nat.le_ceil _
  have hlogone : Real.log (2 : ℝ) ≤ 1 := by linarith only [log_two_bounds.2]
  have hmul := mul_le_mul_of_nonneg_left hlogone
    (Nat.cast_nonneg (hourIndex n) : (0 : ℝ) ≤ _)
  simp only [clockHours, Nat.cast_add, Nat.cast_one]
  nlinarith only [hindex, hmul]

theorem population_le_hour_power (n : ℕ) : n ≤ 2 ^ hourIndex n := by
  simpa only [hourIndex] using Nat.le_pow_clog (by norm_num : 1 < 2) n

theorem population_hours_lower (n : ℕ) (hn : 40 ≤ n) :
    (40 : ℝ) ≤ (n : ℝ) * (clockHours n : ℝ) := by
  have hH : 1 ≤ clockHours n := by unfold clockHours; omega
  have hp : 40 ≤ n * clockHours n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hn hH
  exact_mod_cast hp

theorem logWindow_cast_le (n u : ℕ) (hn : 1 ≤ n) :
    (logWindow n u : ℝ) ≤ (u : ℝ) * (n : ℝ) * Real.log (n : ℝ) + 1 := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  unfold logWindow
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem activationHorizon_le_nine_hours (n : ℕ) (hn : 40 ≤ n) :
    StageEventSpec.activationHorizon n ≤ 9 * n * clockHours n := by
  have hceil := logWindow_cast_le n 6 (by omega)
  have hlog := mul_le_mul_of_nonneg_left (log_le_hour_fraction n)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  have hprod := population_hours_lower n hn
  have hreal : (StageEventSpec.activationHorizon n : ℝ) ≤
      9 * (n : ℝ) * (clockHours n : ℝ) := by
    simp only [StageEventSpec.activationHorizon, Nat.cast_mul, Nat.cast_ofNat]
    push_cast at hceil hlog ⊢
    linarith [hceil, hlog, hprod]
  exact_mod_cast hreal

theorem weakHorizon_le_ten_hours {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    weakHorizon n ≤ 10 * n * clockHours n := by
  obtain ⟨hnpos, hloglarge⟩ := population_calibration hn
  have hweak := weakHorizon_le_log hnpos hloglarge
  have hlog := mul_le_mul_of_nonneg_left (log_le_hour_fraction n) hnpos.le
  have hnonneg : 0 ≤ (n : ℝ) * (clockHours n : ℝ) := by positivity
  have hreal : (weakHorizon n : ℝ) ≤
      10 * (n : ℝ) * (clockHours n : ℝ) := by
    nlinarith only [hweak, hlog, hnonneg]
  exact_mod_cast hreal

theorem backupHorizon_le_five_hundred_nine_hours (n : ℕ) (hn : 40 ≤ n) :
    StrongGapBackup.backupHorizon n ≤ 509 * n * clockHours n := by
  have hsix := logWindow_cast_le n 6 (by omega)
  have hlarge := logWindow_cast_le n 240 (by omega)
  have hlog := mul_le_mul_of_nonneg_left (log_le_hour_fraction n)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  have hprod := population_hours_lower n hn
  have hreal : (StrongGapBackup.backupHorizon n : ℝ) ≤
      509 * (n : ℝ) * (clockHours n : ℝ) := by
    simp only [StrongGapBackup.backupHorizon, StrongGapBackup.threeStageHorizon,
      StageEventSpec.activationHorizon, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    push_cast at hsix hlarge hlog ⊢
    linarith [hsix, hlarge, hlog, hprod]
  exact_mod_cast hreal

theorem dispatchHorizon_le_hours {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n) :
    PhaseTwoDispatchAmplification.dispatchHorizon init n hn ≤
      38 * n * clockHours n := by
  have hlog : Real.log (n : ℝ) + 1 ≤ (hourIndex n + 1 : ℝ) := by
    simpa only [clockHours, Nat.cast_add, Nat.cast_one] using
      log_add_one_le_clockHours n
  simpa only [clockHours] using
    PhaseTwoDispatchAmplification.dispatchHorizon_le_thirty_eight
      init n (hourIndex n) hn hlog (population_le_hour_power n)

/-- A common envelope includes both activation windows, the weak drain, and
the backup path. Individual branches use only some of these offsets. -/
def combinedHorizon {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n) : ℕ :=
  350 * n * clockHours n + weakHorizon n + PhaseOneTimer.timerHorizon n +
    2 * StageEventSpec.activationHorizon n +
    PhaseTwoDispatchAmplification.dispatchHorizon init n hn +
    StrongGapBackup.backupHorizon n

theorem combinedHorizon_le_hours {n : ℕ} (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n) (hnsmall : 2 ≤ n) :
    combinedHorizon init hnsmall ≤ 965 * n * clockHours n := by
  have hnforty := (time_population_bounds hn).2
  have hweak := weakHorizon_le_ten_hours hn
  have hact := activationHorizon_le_nine_hours n hnforty
  have hdispatch := dispatchHorizon_le_hours init hnsmall
  have hbackup := backupHorizon_le_five_hundred_nine_hours n hnforty
  unfold combinedHorizon PhaseOneTimer.timerHorizon
  nlinarith only [hweak, hact, hdispatch, hbackup]

theorem combinedHorizon_le_earlyHorizon {n : ℕ} (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n) (hnsmall : 2 ≤ n) :
    combinedHorizon init hnsmall ≤ earlyHorizon n := by
  calc
    combinedHorizon init hnsmall ≤ 965 * n * clockHours n :=
      combinedHorizon_le_hours init hn hnsmall
    _ ≤ earlyHorizon n := by
      unfold earlyHorizon
      gcongr
      norm_num

theorem entry_error_budget_real (n : ℕ) (hn : 40 ≤ n) :
    1 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 1 / (n : ℝ) ^ 4 +
      5 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 8 ≤ 2 / (n : ℝ) ^ 2 := by
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hpower (k : ℕ) (hk : 3 ≤ k) : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < n) hk
  have hinv (k : ℕ) (hk : 3 ≤ k) :
      1 / (n : ℝ) ^ k ≤ 1 / (n : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hnpos k) (pow_pos hnpos 3)).2
    simpa only [one_mul] using hpower k hk
  have hfour := hinv 4 (by omega)
  have hfive : 5 / (n : ℝ) ^ 5 ≤ 5 / (n : ℝ) ^ 3 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (hinv 5 (by omega)) (by norm_num : (0 : ℝ) ≤ 5)
  have height := hinv 8 (by omega)
  have htwenty : 20 / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hnpos 3) (pow_pos hnpos 2)).2
    have hmul := mul_le_mul_of_nonneg_right
      (show (20 : ℝ) ≤ n by linarith) (sq_nonneg (n : ℝ))
    nlinarith only [hmul]
  calc
    1 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 1 / (n : ℝ) ^ 4 +
        5 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 8 ≤
      1 / (n : ℝ) ^ 2 + 20 / (n : ℝ) ^ 3 := by
        simp only [div_eq_mul_inv] at hfour hfive height ⊢
        linarith only [hfour, hfive, height]
    _ ≤ 2 / (n : ℝ) ^ 2 := by
      simp only [div_eq_mul_inv] at htwenty ⊢
      linarith only [htwenty]

/-- Literal sum of all proposed producers, including the separate activation
height budget. Its presence in this scalar sum is not a producer theorem. -/
def probabilityBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (8 / (n : ℝ) ^ 3) +
    1 / (n : ℝ≥0∞) ^ 2 +
    1 / (n : ℝ≥0∞) ^ 5 +
    ENNReal.ofReal (2 / (n : ℝ) ^ 5) +
    1 / (n : ℝ≥0∞) ^ 4 +
    (ENNReal.ofReal (2 / (n : ℝ) ^ 5) + 1 / (n : ℝ≥0∞) ^ 8) +
    ENNReal.ofReal (5 / (n : ℝ) ^ 3)

theorem probabilityBudget_eq (n : ℕ) (hn : 1 ≤ n) :
    probabilityBudget n =
      ENNReal.ofReal
        (1 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 1 / (n : ℝ) ^ 4 +
          5 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 8) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hinv (k : ℕ) :
      1 / (n : ℝ≥0∞) ^ k = ENNReal.ofReal (1 / (n : ℝ) ^ k) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hnpos k), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  unfold probabilityBudget
  rw [hinv 2, hinv 5, hinv 4, hinv 8]
  repeat' rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem probabilityBudget_le (n : ℕ) (hn : 40 ≤ n) :
    probabilityBudget n ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  rw [probabilityBudget_eq n (by omega)]
  exact ENNReal.ofReal_le_ofReal (entry_error_budget_real n hn)


/-- Scalar calibration when the two actual Phase-1 start times are bounded
separately. Each path uses only one outcome window; the union bound pays
both observed-start failure events. -/
theorem entry_two_start_error_budget_real (n : ℕ) (hn : 40 ≤ n) :
    1 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 2 / (n : ℝ) ^ 4 +
      8 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 8 ≤ 2 / (n : ℝ) ^ 2 := by
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hpower (k : ℕ) (hk : 3 ≤ k) : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < n) hk
  have hinv (k : ℕ) (hk : 3 ≤ k) :
      1 / (n : ℝ) ^ k ≤ 1 / (n : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hnpos k) (pow_pos hnpos 3)).2
    simpa only [one_mul] using hpower k hk
  have hfour : 2 / (n : ℝ) ^ 4 ≤ 2 / (n : ℝ) ^ 3 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (hinv 4 (by omega)) (by norm_num : (0 : ℝ) ≤ 2)
  have hfive : 8 / (n : ℝ) ^ 5 ≤ 8 / (n : ℝ) ^ 3 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (hinv 5 (by omega)) (by norm_num : (0 : ℝ) ≤ 8)
  have height := hinv 8 (by omega)
  have htwentyfour : 24 / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hnpos 3) (pow_pos hnpos 2)).2
    have hmul := mul_le_mul_of_nonneg_right
      (show (24 : ℝ) ≤ n by linarith) (sq_nonneg (n : ℝ))
    nlinarith only [hmul]
  calc
    1 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 2 / (n : ℝ) ^ 4 +
        8 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 8 ≤
      1 / (n : ℝ) ^ 2 + 24 / (n : ℝ) ^ 3 := by
        simp only [div_eq_mul_inv] at hfour hfive height ⊢
        linarith only [hfour, hfive, height]
    _ ≤ 2 / (n : ℝ) ^ 2 := by
      simp only [div_eq_mul_inv] at htwentyfour ⊢
      linarith only [htwentyfour]

def two_start_probabilityBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (8 / (n : ℝ) ^ 3) +
    1 / (n : ℝ≥0∞) ^ 2 +
    (1 / (n : ℝ≥0∞) ^ 4 + 3 / (n : ℝ≥0∞) ^ 5) +
    (1 / (n : ℝ≥0∞) ^ 4 + 3 / (n : ℝ≥0∞) ^ 5) +
    (ENNReal.ofReal (2 / (n : ℝ) ^ 5) + 1 / (n : ℝ≥0∞) ^ 8) +
    ENNReal.ofReal (5 / (n : ℝ) ^ 3)

theorem two_start_probabilityBudget_eq (n : ℕ) (hn : 1 ≤ n) :
    two_start_probabilityBudget n =
      ENNReal.ofReal
        (1 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 2 / (n : ℝ) ^ 4 +
          8 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 8) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast (m k : ℕ) :
      (m : ℝ≥0∞) / (n : ℝ≥0∞) ^ k =
        ENNReal.ofReal ((m : ℝ) / (n : ℝ) ^ k) := by
    simp only [ENNReal.ofReal_div_of_pos (pow_pos hnpos k),
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  unfold two_start_probabilityBudget
  have h12 : (1 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 = ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    simpa using hcast 1 2
  have h14 : (1 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 4 = ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
    simpa using hcast 1 4
  have h35 : (3 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 5 = ENNReal.ofReal (3 / (n : ℝ) ^ 5) := by
    simpa using hcast 3 5
  have h18 : (1 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 8 = ENNReal.ofReal (1 / (n : ℝ) ^ 8) := by
    simpa using hcast 1 8
  rw [h12, h14, h35, h18]
  repeat' rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem two_start_probabilityBudget_le (n : ℕ) (hn : 40 ≤ n) :
    two_start_probabilityBudget n ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  rw [two_start_probabilityBudget_eq n (by omega)]
  exact ENNReal.ofReal_le_ofReal (entry_two_start_error_budget_real n hn)

end Ripple.PopulationProtocol.ExactMajority.PhaseZeroTwoCalibration

end
