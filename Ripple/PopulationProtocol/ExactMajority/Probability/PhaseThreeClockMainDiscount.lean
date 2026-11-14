import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainProcess

/-!
# Discount calibration for the Main barrier

For every population above `PhaseThreeModel.Numeric.populationThreshold`, every
admissible Main seed and every age `≤ logWindow n 30`, the barrier rise is below
the discount divided by `10000`.  The proof shows `κ · age ≤ (2/25) log n`
from `25 M ≤ 13 n` and `age ≤ 30 n log n + 1`, then `(1 + κ)^(-age) ≥ n^(-2/25)`.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcess

open TimeTheorem PhaseThreeClockMainTerminal
open PhaseThreeModel.Numeric

/-- Exponent-parametric wrapper, so the large power is never reduced. -/
private def thresholdAt (e : ℕ) : ℕ := 5 * 2 ^ e

private theorem threshold_eq_at :
    PhaseThreeModel.Numeric.populationThreshold = thresholdAt (2 ^ 23) := by
  rfl

private theorem thousand_le_at {e : ℕ} (he : 10 ≤ e) : 1000 ≤ thresholdAt e :=
  calc 1000 ≤ 2 ^ 10 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    _ ≤ thresholdAt e := Nat.le_mul_of_pos_left _ (by norm_num)

/-- The threshold gives `1000 ≤ n`, without evaluating the large power. -/
theorem thousand_le_of_threshold {n : ℕ}
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) : 1000 ≤ n := by
  rw [threshold_eq_at] at hn
  exact (thousand_le_at (by norm_num)).trans hn

/-- The scalar core: `κ · age ≤ (2/25) log n`. -/
theorem kappa_age_le {M n age : ℕ} (hn : 1000 ≤ n) (hM : 25 * M ≤ 13 * n)
    (hage : age ≤ logWindow n 30) :
    12 * (M : ℝ) / (2500 * ((n : ℝ) * ((n : ℝ) - 1))) * (age : ℝ) ≤
      (2 / 25 : ℝ) * Real.log (n : ℝ) := by
  have hnr : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hMr : 25 * (M : ℝ) ≤ 13 * n := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hL1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have h1 : Real.exp 1 ≤ (n : ℝ) := by
      linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hL0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hageR : (age : ℝ) ≤ 30 * n * Real.log (n : ℝ) + 1 := by
    have h1 : (logWindow n 30 : ℝ) ≤ 30 * n * Real.log (n : ℝ) + 1 := by
      unfold logWindow
      push_cast
      exact (Nat.ceil_lt_add_one (by positivity)).le
    exact le_trans (by exact_mod_cast hage) h1
  have hnL : 1 ≤ (n : ℝ) * Real.log (n : ℝ) := by nlinarith
  have hage31 : (age : ℝ) ≤ 31 * n * Real.log (n : ℝ) := by nlinarith
  have hage0 : (0 : ℝ) ≤ age := Nat.cast_nonneg age
  have hden : 0 < 2500 * ((n : ℝ) * ((n : ℝ) - 1)) := by
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have h1 : 12 * (M : ℝ) * age ≤ 12 * (13 * n / 25) * (31 * n * Real.log (n : ℝ)) := by
    have hM' : (M : ℝ) ≤ 13 * n / 25 := by linarith
    have := mul_le_mul hM' hage31 hage0 (by positivity)
    nlinarith
  have h2 : 0 ≤ (n : ℝ) * Real.log (n : ℝ) * (n - 1000) :=
    mul_nonneg (mul_nonneg (by linarith) hL0) (by linarith)
  nlinarith

/-- The scalar calibration of the discount against the barrier rise. -/
theorem main_discount_calibration {n : ℕ}
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    {init : InputCfg n} (seed : MainSeed init) {age : ℕ}
    (hage : age ≤ logWindow n 30) :
    mainBarrierRise n ≤ mainDiscount init seed age / 10000 := by
  have hn1000 := thousand_le_of_threshold hn
  clear hn
  have hM : 25 * mainSeedM init seed ≤ 13 * n := seed.2.main_upper
  have hkey := kappa_age_le hn1000 hM hage
  have hnpos : (0 : ℝ) < n := by
    have : (1000 : ℝ) ≤ n := by exact_mod_cast hn1000
    linarith
  set κ : ℝ := mainKappa init seed with hκ
  have hκdef : κ = 12 * (mainSeedM init seed : ℝ) /
      (2500 * mainPairDenominator n) := rfl
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    have : (1000 : ℝ) ≤ n := by exact_mod_cast hn1000
    have hd : 0 < 2500 * mainPairDenominator n := by
      unfold mainPairDenominator
      have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
    positivity
  have hκage : κ * (age : ℝ) ≤ (2 / 25 : ℝ) * Real.log (n : ℝ) := by
    rw [hκdef]
    unfold mainPairDenominator
    exact hkey
  -- the discount is at least exp (-(2/25) log n)
  have hQ : mainQ init seed ≤ Real.exp κ := by
    unfold mainQ
    rw [← hκ]
    linarith [Real.add_one_le_exp κ]
  have hQ0 : 0 ≤ mainQ init seed := by unfold mainQ; rw [← hκ]; linarith
  have hQpos : 0 < mainQ init seed := by unfold mainQ; rw [← hκ]; linarith
  have hpow : mainQ init seed ^ age ≤ Real.exp ((2 / 25 : ℝ) * Real.log (n : ℝ)) := by
    calc mainQ init seed ^ age ≤ Real.exp κ ^ age := pow_le_pow_left₀ hQ0 hQ age
      _ = Real.exp ((age : ℝ) * κ) := (Real.exp_nat_mul κ age).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hdisc : Real.exp (-((2 / 25 : ℝ) * Real.log (n : ℝ))) ≤
      mainDiscount init seed age := by
    unfold mainDiscount
    rw [inv_pow, Real.exp_neg]
    exact inv_anti₀ (pow_pos hQpos age) hpow
  have hrise : mainBarrierRise n =
      9 / 100000 * Real.exp (-((2 / 25 : ℝ) * Real.log (n : ℝ))) := by
    unfold mainBarrierRise
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hnpos]
    congr 2
    ring
  have hpos : 0 < Real.exp (-((2 / 25 : ℝ) * Real.log (n : ℝ))) := Real.exp_pos _
  rw [hrise]
  linarith

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcess

end

