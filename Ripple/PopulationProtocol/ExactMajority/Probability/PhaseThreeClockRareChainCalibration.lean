-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRareChainCalibration.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRareDrips
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkCalibration

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareChainCalibration

open TimeTheorem PairLog PhaseThreeModel.Numeric
  PhaseThreeClockRareDrips PhaseThreeClockEarlyMarkCalibration

def sparseUpper (C : ℕ) : ℕ := shapeCutoff C ^ 2 / C

def rareMean (C : ℕ) : ℝ :=
  20000 * Real.log (C : ℝ) * (C : ℝ) ^ (-(7 / 25 : ℝ))

def rareExponent (C : ℕ) : ℝ :=
  -(27 / 100 : ℝ) * ((frontWidth C - 1 : ℕ) : ℝ)

theorem sparseUpper_bound {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ)) :
    (sparseUpper C : ℝ) ≤ 4 * (C : ℝ) ^ (9 / 25 : ℝ) := by
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCone : (1 : ℝ) ≤ C := by linarith
  have hone := rpow_ge_one hCone (show (0 : ℝ) ≤ 17 / 25 by norm_num)
  have hceil : (shapeCutoff C : ℝ) <
      (C : ℝ) ^ (17 / 25 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hC.le _)
  have hw : (shapeCutoff C : ℝ) ≤ 2 * (C : ℝ) ^ (17 / 25 : ℝ) := by
    linarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (shapeCutoff C) : (0 : ℝ) ≤ _) hw 2
  have hpower : ((C : ℝ) ^ (17 / 25 : ℝ)) ^ 2 =
      (C : ℝ) * (C : ℝ) ^ (9 / 25 : ℝ) := by
    rw [rpow_square _ _ hC.le,
      show (2 : ℝ) * (17 / 25) = 1 + 9 / 25 by ring,
      Real.rpow_add hC, Real.rpow_one]
  have hdiv : sparseUpper C * C ≤ shapeCutoff C ^ 2 :=
    Nat.div_mul_le_self _ _
  have hdivR : (sparseUpper C : ℝ) * (C : ℝ) ≤ (shapeCutoff C : ℝ) ^ 2 := by
    exact_mod_cast hdiv
  refine le_of_mul_le_mul_right ?_ hC
  nlinarith only [hsq, hpower, hdivR]

theorem rare_rate_bound {m C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ))
    (hCm : C ≤ m) :
    2 * (sparseUpper C : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤
      32 * (C : ℝ) ^ (-(32 / 25 : ℝ)) := by
  have hCmR : (C : ℝ) ≤ m := by exact_mod_cast hCm
  have hm : 0 < (m : ℝ) := hC.trans_le hCmR
  have hB := sparseUpper_bound hC hx
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (sparseUpper C) : (0 : ℝ) ≤ _) hB 2
  have hCpow : ((C : ℝ) ^ (9 / 25 : ℝ)) ^ 2 =
      (C : ℝ) ^ (18 / 25 : ℝ) := by
    rw [rpow_square _ _ hC.le]
    norm_num
  have hden : (C : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 :=
    pow_le_pow_left₀ hC.le hCmR 2
  calc
    2 * (sparseUpper C : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤
        2 * (sparseUpper C : ℝ) ^ 2 / (C : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ (32 * (C : ℝ) ^ (18 / 25 : ℝ)) / (C : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith only [hsq, hCpow]) (sq_nonneg _)
    _ = 32 * (C : ℝ) ^ (-(32 / 25 : ℝ)) := by
      rw [show -(32 / 25 : ℝ) = 18 / 25 - 2 by ring,
        Real.rpow_sub hC, Real.rpow_two]
      ring

theorem rare_actual_mean_bound {m C : ℕ}
    (hm : populationThreshold ≤ m)
    (hlo : (6 / 25 : ℝ) * (m : ℝ) ≤ C) (hCm : C ≤ m) :
    (2 * (sparseUpper C : ℝ) ^ 2 / (m : ℝ) ^ 2) *
        (firstHitHorizon m : ℝ) ≤
      4160 * Real.log (C : ℝ) * (C : ℝ) ^ (-(7 / 25 : ℝ)) := by
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hm hlo hCm
  have hN := (horizon_calibration hm hlo hCm).1.trans
    (horizon_calibration hm hlo hCm).2.1
  have hrate := rare_rate_bound hC hx hCm
  have hpower : (C : ℝ) ^ (-(32 / 25 : ℝ)) * (C : ℝ) =
      (C : ℝ) ^ (-(7 / 25 : ℝ)) := by
    calc
      (C : ℝ) ^ (-(32 / 25 : ℝ)) * (C : ℝ) =
          (C : ℝ) ^ (-(32 / 25 : ℝ)) * (C : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hC]
        congr 1
        ring
  calc
    _ ≤ (32 * (C : ℝ) ^ (-(32 / 25 : ℝ))) * (firstHitHorizon m : ℝ) :=
      mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)
    _ ≤ (32 * (C : ℝ) ^ (-(32 / 25 : ℝ))) *
        (130 * (C : ℝ) * Real.log (C : ℝ)) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = 4160 * Real.log (C : ℝ) *
        ((C : ℝ) ^ (-(32 / 25 : ℝ)) * (C : ℝ)) := by ring
    _ = _ := by rw [hpower]

theorem rareMean_calibration {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ)) :
    0 < rareMean C ∧
      rareMean C ≤ ((frontWidth C - 1 : ℕ) : ℝ) ∧
      (Real.exp 1 * rareMean C / ((frontWidth C - 1 : ℕ) : ℝ)) ^
          ((frontWidth C - 1 : ℕ) : ℝ) ≤
        (C : ℝ) ^ rareExponent C := by
  have hxpos : 0 < Real.log (C : ℝ) := by linarith
  have hμ : 0 < rareMean C := by
    unfold rareMean
    exact mul_pos (mul_pos (by norm_num) hxpos) (Real.rpow_pos_of_pos hC _)
  have hd := (frontWidth_bounds hx).1
  have hr : (44 : ℝ) ≤ ((frontWidth C - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 44 ≤ frontWidth C - 1 by omega)
  have hrpos : (0 : ℝ) < ((frontWidth C - 1 : ℕ) : ℝ) := by linarith
  have hpower := (new_power_calibration hC hx).2.2.2
  have hμsmall : rareMean C ≤ (C : ℝ) ^ (-(27 / 100 : ℝ)) := by
    calc
      rareMean C ≤ (C : ℝ) ^ (1 / 100 : ℝ) *
          (C : ℝ) ^ (-(7 / 25 : ℝ)) :=
        mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hC.le _)
      _ = _ := by
        rw [← Real.rpow_add hC]
        congr 1
        ring
  have hpowone : (C : ℝ) ^ (-(27 / 100 : ℝ)) ≤ 1 := by
    rw [Real.rpow_def_of_pos hC]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hxpos.le (by norm_num))
  have hbase : Real.exp 1 * rareMean C / ((frontWidth C - 1 : ℕ) : ℝ) ≤
      (C : ℝ) ^ (-(27 / 100 : ℝ)) := by
    apply le_trans _ hμsmall
    apply (div_le_iff₀ hrpos).mpr
    have he : Real.exp 1 ≤ ((frontWidth C - 1 : ℕ) : ℝ) :=
      exp_one_bounds.2.le.trans (by linarith)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right he hμ.le
  refine ⟨hμ, (hμsmall.trans hpowone).trans (by linarith), ?_⟩
  calc
    _ ≤ ((C : ℝ) ^ (-(27 / 100 : ℝ))) ^
        ((frontWidth C - 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase hrpos.le
    _ = (C : ℝ) ^ rareExponent C := by
      rw [← Real.rpow_mul hC.le]
      rfl

theorem rareDrip_calibrated_prefix_tail {n : ℕ} (init : InputCfg n)
    (C : ℕ) (hn : populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ C) (hCm : C ≤ init.card)
    (k u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E) :
    law init (E ∩ {ω | ((frontWidth C - 1 : ℕ) : ℝ) ≤
      rareDripCount init k (shapeCutoff C) (sparseUpper C)
        u (firstHitHorizon init.card) ω}) ≤
      ENNReal.ofReal ((C : ℝ) ^ rareExponent C) * law init E := by
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hn hlo hCm
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hmR : (C : ℝ) ≤ init.card := by exact_mod_cast hCm
  have hc : 2 ≤ init.card := by
    have : (2 : ℝ) ≤ init.card := by linarith
    exact_mod_cast this
  obtain ⟨hμ, hμr, hcal⟩ := rareMean_calibration hC hx
  have hmean :
      (2 * (sparseUpper C : ℝ) ^ 2 / (init.card : ℝ) ^ 2) *
        (firstHitHorizon init.card : ℝ) ≤ rareMean C := by
    apply (rare_actual_mean_bound hn hlo hCm).trans
    unfold rareMean
    have hnonneg : 0 ≤ Real.log (C : ℝ) * (C : ℝ) ^ (-(7 / 25 : ℝ)) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hC.le _)
    nlinarith only [hnonneg]
  exact (rareDrip_prefix_chernoff init hc k (shapeCutoff C) (sparseUpper C)
    u (firstHitHorizon init.card) E hE (rareMean C)
      ((frontWidth C - 1 : ℕ) : ℝ) hμ hμr hmean).trans
        (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hcal) _)

theorem rare_level_union_calibration {C Q : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ))
    (hQC : Q ≤ C) :
    (Q : ℝ) * (C : ℝ) ^ rareExponent C ≤
      (C : ℝ) ^ (-(272 / 25 : ℝ)) := by
  have hd := (frontWidth_bounds hx).1
  have hr : (44 : ℝ) ≤ ((frontWidth C - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 44 ≤ frontWidth C - 1 by omega)
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCone : (1 : ℝ) ≤ C := by linarith
  have hexp : 1 + rareExponent C ≤ -(272 / 25 : ℝ) := by
    unfold rareExponent
    linarith
  calc
    (Q : ℝ) * (C : ℝ) ^ rareExponent C ≤
        (C : ℝ) * (C : ℝ) ^ rareExponent C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQC)
        (Real.rpow_nonneg hC.le _)
    _ = (C : ℝ) ^ (1 + rareExponent C) := by
      rw [Real.rpow_add hC, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hCone hexp

theorem rare_population_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * (n : ℝ) ≤ C) (hCn : C ≤ n) :
    (C : ℝ) ^ (-(272 / 25 : ℝ)) ≤
      1 / (2 * (n : ℝ) ^ 10) := by
  obtain ⟨hC, hx, -, hxy, -⟩ := logarithmic_inputs hn hlo hCn
  have hnp : 0 < (n : ℝ) := hC.trans_le (by exact_mod_cast hCn)
  have hlogtwo : Real.log 2 ≤ (1 : ℝ) := log_two_bounds.2.trans (by norm_num)
  have hexponent :
      Real.log (C : ℝ) * (-(272 / 25 : ℝ)) ≤
        -(Real.log 2 + 10 * Real.log (n : ℝ)) := by
    linarith only [hx, hxy, hlogtwo]
  calc
    _ = Real.exp (Real.log (C : ℝ) * (-(272 / 25 : ℝ))) :=
      Real.rpow_def_of_pos hC _
    _ ≤ Real.exp (-(Real.log 2 + 10 * Real.log (n : ℝ))) :=
      Real.exp_le_exp.mpr hexponent
    _ = 1 / (2 * (n : ℝ) ^ 10) := by
      rw [Real.exp_neg, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2),
        show (10 : ℝ) * Real.log (n : ℝ) =
          ((10 : ℕ) : ℝ) * Real.log (n : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hnp, one_div]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareChainCalibration

end
