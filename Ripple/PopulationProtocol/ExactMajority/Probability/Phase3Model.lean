import Ripple.PopulationProtocol.ExactMajority.Probability.Calibration
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar
import Ripple.PopulationProtocol.ExactMajority.Probability.ClockRealMixed
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3GoodClockRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.ProtocolTraceLaw
import Mathlib.Data.Multiset.Fintype
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Phase-3 numerical calibration and model interfaces

The scheduler section constructs canonical occurrence labels and proves their
one-step and finite-cylinder configuration laws. The Clock section gives the
one-draw tick probability, its joint configuration marginal, and initialized
Clock-pair front facts. Persistent-label stopping-time coupling and the gated
asynchronous front law are not asserted here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeModel

/-! ## Exact numerical calibration for P1 -/

namespace Numeric

def populationThreshold : ℕ := Calibration.populationThreshold

def hourIndex (n : ℕ) : ℕ := Nat.clog 2 n

def clockHours (n : ℕ) : ℕ := hourIndex n + 1

def clockCap (n : ℕ) : ℕ := 256 * clockHours n

noncomputable def frontWidth (C : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (Real.log (C : ℝ))) + 16

theorem hourIndex_eq_real_ceiling (n : ℕ) :
    hourIndex n = Nat.ceil (Real.log (n : ℝ) / Real.log 2) := by
  simpa [hourIndex, Real.logb] using
    (Real.natCeil_logb_natCast 2 n).symm

theorem log_two_bounds :
    (2 / 3 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (25 / 36 : ℝ) := by
  have hlo := Real.le_log_one_add_of_nonneg
    (x := (1 : ℝ)) (by norm_num)
  have hhi := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith

/-- A rational lower bound for the binary logarithm conversion. -/
theorem log_two_lower_bound : (56 / 81 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- Convert logarithmic windows to the clock-hour scale. -/
theorem log_le_hour_fraction (n : ℕ) :
    Real.log (n : ℝ) ≤ (25 / 36 : ℝ) * (clockHours n : ℝ) := by
  have htwo : 0 < Real.log (2 : ℝ) := by
    linarith only [log_two_bounds.1]
  have hindex : Real.log (n : ℝ) ≤ (hourIndex n : ℝ) * Real.log 2 := by
    apply (div_le_iff₀ htwo).mp
    rw [hourIndex_eq_real_ceiling]
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left log_two_bounds.2
    (Nat.cast_nonneg (hourIndex n) : (0 : ℝ) ≤ _)
  simp only [clockHours, Nat.cast_add, Nat.cast_one]
  nlinarith only [hindex, hmul]

/-- The sharper hour conversion valid at the stabilization-time threshold. -/
theorem clockHours_le_log_fraction {n : ℕ}
    (hy : 560 ≤ Real.log (n : ℝ)) :
    (clockHours n : ℝ) ≤ (29 / 20 : ℝ) * Real.log (n : ℝ) := by
  have hyzero : 0 ≤ Real.log (n : ℝ) := by linarith
  have htwo : 0 < Real.log (2 : ℝ) := by
    linarith only [log_two_lower_bound]
  have hceil : (hourIndex n : ℝ) < Real.log (n : ℝ) / Real.log 2 + 1 := by
    rw [hourIndex_eq_real_ceiling]
    exact Nat.ceil_lt_add_one (div_nonneg hyzero htwo.le)
  have hdiv : Real.log (n : ℝ) / Real.log 2 ≤
      (81 / 56 : ℝ) * Real.log (n : ℝ) := by
    rw [div_le_iff₀ htwo]
    have hmul := mul_nonneg hyzero (sub_nonneg.mpr log_two_lower_bound)
    nlinarith only [hmul]
  simp only [clockHours, Nat.cast_add, Nat.cast_one]
  linarith only [hceil, hdiv, hy]

theorem exp_one_bounds :
    (8 / 3 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 3 := by
  have hlo := Real.sum_le_exp_of_nonneg
    (x := (1 : ℝ)) (by norm_num) 5
  have hhi := Real.exp_bound' (x := (1 : ℝ))
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  constructor <;> linarith

theorem log_small_bounds :
    Real.log 6 < 2 ∧
      Real.log (125 / 3) < 4 ∧
      Real.log 100 < 5 := by
  constructor
  · apply (Real.log_lt_iff_lt_exp
      (by norm_num : (0 : ℝ) < 6)).2
    have h := Real.sum_le_exp_of_nonneg
      (x := (2 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  constructor
  · apply (Real.log_lt_iff_lt_exp
      (by norm_num : (0 : ℝ) < 125 / 3)).2
    have h := Real.sum_le_exp_of_nonneg
      (x := (4 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  · apply (Real.log_lt_iff_lt_exp
      (by norm_num : (0 : ℝ) < 100)).2
    have h := Real.sum_le_exp_of_nonneg
      (x := (5 : ℝ)) (by norm_num) 7
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith

/-- An exponent-parametric wrapper, kept as a regular definition. -/
private def populationThresholdAt (e : ℕ) : ℕ :=
  5 * 2 ^ e

private theorem populationThreshold_eq_at :
    populationThreshold = populationThresholdAt (2 ^ 23) := by
  rfl

/-- Derive logarithmic inputs while the large exponent remains a variable. -/
private theorem logarithmic_inputs_of_exponent {n C e : ℕ}
    (he : 2 ^ 23 ≤ e)
    (hn : populationThresholdAt e ≤ n)
    (hlo : (6 / 25 : ℝ) * n ≤ C)
    (hCn : C ≤ n) :
    0 < (C : ℝ) ∧
    4194304 ≤ Real.log (C : ℝ) ∧
    Real.log (C : ℝ) ≤ Real.log (n : ℝ) ∧
    Real.log (n : ℝ) ≤ Real.log (C : ℝ) + 2 ∧
    Real.log (C : ℝ) + 2 ≤ 2 * Real.log (C : ℝ) := by
  change 5 * 2 ^ e ≤ n at hn
  have hn' :
      (5 : ℝ) * (2 : ℝ) ^ e ≤ (n : ℝ) := by
    have hreal :
        ((5 * 2 ^ e : ℕ) : ℝ) ≤ (n : ℝ) :=
      Nat.cast_le.mpr hn
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      using hreal
  have hp : 0 < (2 : ℝ) ^ e :=
    pow_pos (by norm_num : (0 : ℝ) < 2) e
  have hbase : (2 : ℝ) ^ e ≤ (C : ℝ) := by
    nlinarith only [hn', hlo, hp]
  have hCp : 0 < (C : ℝ) := lt_of_lt_of_le hp hbase
  have hCn' : (C : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hCn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le hCp hCn'
  have hx : 4194304 ≤ Real.log (C : ℝ) :=
    Calibration.logarithm_lower_of_power he hbase
  have hxy : Real.log (C : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hCp hCn'
  have hratio : (n : ℝ) ≤ (25 / 6 : ℝ) * C := by
    linarith only [hlo]
  have hy := Real.log_le_log hnp hratio
  rw [Real.log_mul (by norm_num : (25 / 6 : ℝ) ≠ 0)
    (ne_of_gt hCp)] at hy
  have hsmall : Real.log (25 / 6 : ℝ) ≤ 2 :=
    (Real.log_le_log
      (by norm_num : (0 : ℝ) < 25 / 6)
      (by norm_num : (25 / 6 : ℝ) ≤ 6)).trans
        log_small_bounds.1.le
  exact ⟨hCp, hx, hxy,
    by linarith only [hy, hsmall],
    by linarith only [hx]⟩

theorem logarithmic_inputs {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * n ≤ C)
    (hCn : C ≤ n) :
    0 < (C : ℝ) ∧
    4194304 ≤ Real.log (C : ℝ) ∧
    Real.log (C : ℝ) ≤ Real.log (n : ℝ) ∧
    Real.log (n : ℝ) ≤ Real.log (C : ℝ) + 2 ∧
    Real.log (C : ℝ) + 2 ≤ 2 * Real.log (C : ℝ) := by
  have hnAt : populationThresholdAt (2 ^ 23) ≤ n :=
    (congrArg (fun q : ℕ => q ≤ n) populationThreshold_eq_at).mp hn
  exact logarithmic_inputs_of_exponent
    (e := 2 ^ 23) le_rfl hnAt hlo hCn

theorem frontWidth_bounds {C : ℕ}
    (hx : 4194304 ≤ Real.log (C : ℝ)) :
    38 ≤ frontWidth C ∧
    (frontWidth C : ℝ) ≤
      2 * Real.log (Real.log (C : ℝ)) + 17 ∧
    2 * Real.log (Real.log (C : ℝ)) + 17 ≤
      Real.log (C : ℝ) / 80000 := by
  let x : ℝ := Real.log (C : ℝ)
  have hx' : 4194304 ≤ x := hx
  have hxp : 0 < x := by
    linarith
  have hlp : 0 < Real.log 2 := by
    linarith [log_two_bounds.1]
  have hlx : 0 ≤ Real.log x :=
    Real.log_nonneg (by linarith)
  have hlb : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg
      (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hceil := Nat.ceil_lt_add_one hlb
  have hceil_lower :
      Real.logb 2 x ≤ (Nat.ceil (Real.logb 2 x) : ℝ) :=
    Nat.le_ceil _
  have hpow : (2 : ℝ) ^ 22 ≤ x := by
    simpa only [show (2 : ℝ) ^ 22 = 4194304 by norm_num] using hx'
  have hlogx := Real.log_le_log
    (by positivity : 0 < (2 : ℝ) ^ 22) hpow
  rw [Real.log_pow] at hlogx
  norm_num only [Nat.cast_ofNat] at hlogx
  have hlower : (22 : ℝ) ≤ Real.logb 2 x := by
    rw [Real.logb, le_div_iff₀ hlp]
    exact hlogx
  have hdiv : Real.logb 2 x ≤ 2 * Real.log x := by
    rw [Real.logb, div_le_iff₀ hlp]
    have h := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 2 * Real.log 2 by
        linarith [log_two_bounds.1]) hlx
    nlinarith
  have hdlo : (38 : ℝ) ≤ (frontWidth C : ℝ) := by
    simp only [frontWidth, Nat.cast_add, Nat.cast_ofNat]
    change (38 : ℝ) ≤
      (Nat.ceil (Real.logb 2 x) : ℝ) + 16
    linarith
  have hdhi :
      (frontWidth C : ℝ) ≤ 2 * Real.log x + 17 := by
    simp only [frontWidth, Nat.cast_add, Nat.cast_ofNat]
    change (Nat.ceil (Real.logb 2 x) : ℝ) + 16 ≤
      2 * Real.log x + 17
    linarith
  have hratio := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < x / 4194304 by positivity)
  rw [Real.log_div (ne_of_gt hxp)
    (by norm_num : (4194304 : ℝ) ≠ 0)] at hratio
  have hbaseLog :
      Real.log (4194304 : ℝ) = 22 * Real.log 2 := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      congrArg Real.log
        (show (4194304 : ℝ) = (2 : ℝ) ^ 22 by norm_num)
  rw [hbaseLog] at hratio
  have hlast : 2 * Real.log x + 17 ≤ x / 80000 := by
    linarith [log_two_bounds.2]
  refine ⟨?_, hdhi, hlast⟩
  exact_mod_cast hdlo

theorem hour_bounds {n : ℕ} (hnp : 0 < (n : ℝ))
    (hy : 6 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) ≤ (clockHours n : ℝ) ∧
    (clockHours n : ℝ) ≤
      (11 / 6 : ℝ) * Real.log (n : ℝ) ∧
    clockHours n ≤ n := by
  let y : ℝ := Real.log (n : ℝ)
  have hy' : 6 ≤ y := hy
  have hy0 : 0 ≤ y := by
    linarith
  have hlp : 0 < Real.log 2 := by
    linarith [log_two_bounds.1]
  have hdiv0 : 0 ≤ y / Real.log 2 :=
    div_nonneg hy0 hlp.le
  have hlo : y / Real.log 2 ≤ (hourIndex n : ℝ) := by
    rw [hourIndex_eq_real_ceiling]
    exact Nat.le_ceil _
  have hhi : (hourIndex n : ℝ) < y / Real.log 2 + 1 := by
    rw [hourIndex_eq_real_ceiling]
    exact Nat.ceil_lt_add_one hdiv0
  have hdivlo : y ≤ y / Real.log 2 := by
    rw [le_div_iff₀ hlp]
    exact mul_le_of_le_one_right hy0
      (by linarith [log_two_bounds.2])
  have hdivhi : y / Real.log 2 ≤ (3 / 2 : ℝ) * y := by
    rw [div_le_iff₀ hlp]
    have h := mul_nonneg hy0
      (sub_nonneg.mpr log_two_bounds.1)
    nlinarith
  have hHlo : y ≤ (clockHours n : ℝ) := by
    simp only [clockHours, Nat.cast_add, Nat.cast_one]
    change y ≤ (hourIndex n : ℝ) + 1
    linarith
  have hHhi : (clockHours n : ℝ) ≤ (11 / 6 : ℝ) * y := by
    simp only [clockHours, Nat.cast_add, Nat.cast_one]
    change (hourIndex n : ℝ) + 1 ≤ (11 / 6 : ℝ) * y
    linarith
  have hquad := Real.quadratic_le_exp_of_nonneg hy0
  change 1 + y + y ^ 2 / 2 ≤ Real.exp y at hquad
  have he : Real.exp y = (n : ℝ) := Real.exp_log hnp
  rw [he] at hquad
  have hHn : (clockHours n : ℝ) ≤ (n : ℝ) := by
    have hprod := mul_nonneg hy0
      (show 0 ≤ y - 2 by linarith)
    nlinarith
  exact ⟨hHlo, hHhi, by exact_mod_cast hHn⟩

/-- Equations (20)--(22), with the natural parameter used by the
implementation. The density assumptions are precisely the Clock-count
consequences used by these inequalities. -/
theorem numeric_calibration_core {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * n ≤ C)
    (hCn : C ≤ n) :
    0 < (C : ℝ) ∧
    4194304 ≤ Real.log (C : ℝ) ∧
    Real.log (C : ℝ) ≤ Real.log (n : ℝ) ∧
    Real.log (n : ℝ) ≤ Real.log (C : ℝ) + 2 ∧
    Real.log (C : ℝ) + 2 ≤ 2 * Real.log (C : ℝ) ∧
    38 ≤ frontWidth C ∧
    (frontWidth C : ℝ) ≤
      2 * Real.log (Real.log (C : ℝ)) + 17 ∧
    2 * Real.log (Real.log (C : ℝ)) + 17 ≤
      Real.log (C : ℝ) / 80000 ∧
    (clockHours n : ℝ) ≤
      (11 / 6 : ℝ) * Real.log (n : ℝ) ∧
    (clockCap n : ℝ) ≤ 1024 * Real.log (C : ℝ) ∧
    1024 * Real.log (C : ℝ) ≤ (C : ℝ) ∧
    clockCap n ≤ C ∧
    clockHours n ≤ n ∧
    2 * frontWidth C + 20 < clockCap n := by
  obtain ⟨hCp, hx, hxy, hyx, hxdouble⟩ :=
    logarithmic_inputs hn hlo hCn
  clear hn
  obtain ⟨hdlo, hdmiddle, hdlast⟩ := frontWidth_bounds hx
  have hCn' : (C : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hCn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le hCp hCn'
  obtain ⟨hHlo, hHhi, hHn⟩ :=
    hour_bounds hnp (by linarith only [hx, hxy])
  have hx0 : 0 ≤ Real.log (C : ℝ) := by
    linarith only [hx]
  have hquad := Real.quadratic_le_exp_of_nonneg hx0
  rw [Real.exp_log hCp] at hquad
  have hsquare :
      2048 * Real.log (C : ℝ) ≤
        (Real.log (C : ℝ)) ^ 2 := by
    have h := mul_nonneg hx0
      (show 0 ≤ Real.log (C : ℝ) - 2048 by
        linarith only [hx])
    nlinarith only [h]
  have hxC :
      1024 * Real.log (C : ℝ) ≤ (C : ℝ) := by
    linarith only [hquad, hsquare, hx0]
  have hQ :
      (clockCap n : ℝ) ≤ 1024 * Real.log (C : ℝ) := by
    simp only [clockCap, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hHhi, hyx, hxdouble, hx0]
  have hQC : clockCap n ≤ C := by
    exact_mod_cast hQ.trans hxC
  have hwidth :
      (2 : ℝ) * frontWidth C + 20 < (clockCap n : ℝ) := by
    simp only [clockCap, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hdmiddle, hdlast, hHlo, hxy, hx]
  refine ⟨hCp, hx, hxy, hyx, hxdouble, hdlo, hdmiddle,
    hdlast, hHhi, hQ, hxC, hQC, hHn, ?_⟩
  exact_mod_cast hwidth

/-- Package the scalar clock inputs at the common population threshold. -/
theorem clockCalibration_of_threshold {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * n ≤ C) (hCn : C ≤ n) :
    Calibration.ClockCalibration (Real.log (C : ℝ)) (Real.log (n : ℝ))
      (frontWidth C : ℝ) (clockCap n : ℝ) := by
  obtain ⟨_, hx, hxy, hyx, _, hdlo, hdmiddle, hdlast, _, hQ, _⟩ :=
    numeric_calibration_core hn hlo hCn
  exact ⟨hx, hxy, hyx, by exact_mod_cast hdlo, hdmiddle.trans hdlast, hQ⟩

theorem rpow_linear_lower {C : ℝ} (hC : 0 < C) (a : ℝ) :
    Real.log C * a + 1 ≤ C ^ a := by
  rw [Real.rpow_def_of_pos hC]
  exact Real.add_one_le_exp _

theorem rpow_quadratic_lower {C : ℝ} (hC : 0 < C)
    (hx : 0 ≤ Real.log C) {a : ℝ} (ha : 0 ≤ a) :
    (Real.log C * a) ^ 2 / 2 ≤ C ^ a := by
  rw [Real.rpow_def_of_pos hC]
  have h := Real.pow_div_factorial_le_exp
    (Real.log C * a) (mul_nonneg hx ha) 2
  norm_num [Nat.factorial] at h
  exact h

/-- Cubic Taylor lower bound for powers with small positive exponents. -/
theorem rpow_cubic_lower {C : ℝ} (hC : 0 < C)
    (hx : 0 ≤ Real.log C) {a : ℝ} (ha : 0 ≤ a) :
    (Real.log C * a) ^ 3 / 6 ≤ C ^ a := by
  rw [Real.rpow_def_of_pos hC]
  have h := Real.pow_div_factorial_le_exp
    (Real.log C * a) (mul_nonneg hx ha) 3
  norm_num [Nat.factorial] at h
  exact h

/-- The cubic certificate shared by the small-power comparisons. -/
theorem logarithm_cube_lower {x : ℝ} (hx : 4194304 ≤ x) :
    17592186044416 * x ≤ x ^ 3 := by
  have hxzero : 0 ≤ x := by linarith
  have hsquare : (17592186044416 : ℝ) ≤ x ^ 2 := by nlinarith
  have h := mul_nonneg hxzero (sub_nonneg.mpr hsquare)
  nlinarith only [h]

/-- The four new power comparisons in equation (24b). -/
theorem new_power_calibration {C : ℝ} (hC : 0 < C)
    (hx : 4194304 ≤ Real.log C) :
    40 * Real.log C ≤ C ^ (1 / 50 : ℝ) ∧
    102 * Real.log C ≤
      (9 / 100 : ℝ) * C ^ (1 / 50 : ℝ) ∧
    303 * Real.log C ≤ C ^ (1 / 25 : ℝ) ∧
    20000 * Real.log C ≤ C ^ (1 / 100 : ℝ) := by
  have hxzero : 0 ≤ Real.log C := by linarith
  have hcube := logarithm_cube_lower hx
  have hsmall := rpow_cubic_lower hC hxzero
    (show (0 : ℝ) ≤ 1 / 50 by norm_num)
  have hmedium := rpow_cubic_lower hC hxzero
    (show (0 : ℝ) ≤ 1 / 25 by norm_num)
  have hlarge := rpow_cubic_lower hC hxzero
    (show (0 : ℝ) ≤ 1 / 100 by norm_num)
  constructor
  · nlinarith only [hsmall, hcube, hxzero]
  constructor
  · nlinarith only [hsmall, hcube, hxzero]
  constructor
  · nlinarith only [hmedium, hcube, hxzero]
  · nlinarith only [hlarge, hcube, hxzero]

/-- The logarithmic cap is absorbed by the additional rare-chain power. -/
theorem rare_power_calibration {C : ℝ} (hC : 0 < C)
    (hx : 4194304 ≤ Real.log C) :
    20000 * Real.log C ≤ C ^ (1 / 200 : ℝ) := by
  have hxzero : 0 ≤ Real.log C := by linarith
  have hcube := logarithm_cube_lower hx
  have hpower := rpow_cubic_lower hC hxzero
    (show (0 : ℝ) ≤ 1 / 200 by norm_num)
  nlinarith only [hpower, hcube, hxzero]

/-- Equation (24), and the two single-power comparisons in (23). -/
theorem elementary_power_calibration {C : ℕ}
    (hC : 0 < (C : ℝ))
    (hx : 4194304 ≤ Real.log (C : ℝ)) :
    (6400 : ℝ) * frontWidth C ≤
      (C : ℝ) ^ (1 / 50 : ℝ) ∧
    (20000 : ℝ) ≤ (C : ℝ) ^ (1 / 10 : ℝ) ∧
    102 * Real.log (C : ℝ) ≤
      (9 / 100 : ℝ) * Real.exp (Real.log (C : ℝ) / 10) ∧
    102 * Real.log (C : ℝ) ≤
      (1 / 6 : ℝ) * Real.exp (Real.log (C : ℝ) / 10) ∧
    102 * Real.log (C : ℝ) ≤
      Real.exp (Real.log (C : ℝ)) / 1000000 ∧
    (4000 : ℝ) * frontWidth C ≤ (C : ℝ) := by
  obtain ⟨_, hdmiddle, hdlast⟩ := frontWidth_bounds hx
  have hx0 : 0 ≤ Real.log (C : ℝ) := by
    linarith
  have hxx :
      4194304 * Real.log (C : ℝ) ≤
        (Real.log (C : ℝ)) ^ 2 := by
    have h := mul_nonneg hx0 (sub_nonneg.mpr hx)
    nlinarith
  have hsmall := rpow_quadratic_lower hC hx0
    (show (0 : ℝ) ≤ 1 / 50 by norm_num)
  have htenth := rpow_linear_lower hC (1 / 10 : ℝ)
  have hquad := Real.pow_div_factorial_le_exp
    (Real.log (C : ℝ) / 10)
    (show 0 ≤ Real.log (C : ℝ) / 10 by positivity) 2
  norm_num [Nat.factorial] at hquad
  have hfull := Real.pow_div_factorial_le_exp (Real.log (C : ℝ)) hx0 3
  norm_num [Nat.factorial] at hfull
  have hcube := logarithm_cube_lower hx
  have hexp :
      Real.exp (Real.log (C : ℝ)) = (C : ℝ) :=
    Real.exp_log hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith only [hquad, hxx, hx0]
  · nlinarith only [hquad, hxx, hx0]
  · nlinarith
  · rw [hexp] at hfull
    nlinarith

noncomputable def markOrder (C : ℕ) : ℕ :=
  Nat.ceil ((C : ℝ) ^ (1 / 25 : ℝ))

noncomputable def smallActivation (C : ℕ) : ℕ :=
  Nat.ceil ((C : ℝ) ^ (1 / 100 : ℝ))

noncomputable def earlyCutoff (C : ℕ) : ℕ :=
  Nat.ceil ((C : ℝ) ^ (51 / 100 : ℝ))

noncomputable def shapeCutoff (C : ℕ) : ℕ :=
  Nat.ceil ((C : ℝ) ^ (17 / 25 : ℝ))

noncomputable def bulkCount (C : ℕ) : ℕ :=
  Nat.ceil ((C : ℝ) / 10)

noncomputable def sparseCount (C : ℕ) : ℕ :=
  Nat.floor ((C : ℝ) / 1000)

noncomputable def firstHitHorizon (n : ℕ) : ℕ :=
  Nat.ceil (30 * (n : ℝ) * Real.log (n : ℝ))

noncomputable def activationHalfHorizon (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) * Real.log (n : ℝ) / 2)

noncomputable def fineTicks (C : ℕ) : ℕ :=
  200 * frontWidth C * C

theorem rational_margins :
    (25 / 36 : ℝ) < 7 / 10 ∧
    (2816 / 3 : ℝ) < 1024 ∧
    (155775 / 1200 : ℝ) < 130 ∧
    (802000 : ℝ) < 2 ^ 20 := by
  norm_num

theorem exp_taylor_lower_bounds {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 200 ≤ Real.exp (x / 10) ∧
    x ^ 3 / 6 ≤ Real.exp x := by
  constructor
  · have h := Real.pow_div_factorial_le_exp
      (x / 10) (show 0 ≤ x / 10 by positivity) 2
    norm_num [Nat.factorial] at h
    calc
      x ^ 2 / 200 = (x / 10) ^ 2 / 2 := by ring
      _ ≤ Real.exp (x / 10) := h
  · have h := Real.pow_div_factorial_le_exp x hx 3
    norm_num [Nat.factorial] at h
    exact h

theorem rpow_scale {C : ℝ} (hC : 0 < C) (u v : ℝ) {k : ℝ}
    (hk : k ≤ C ^ v) :
    k * C ^ u ≤ C ^ (u + v) := by
  rw [Real.rpow_add hC]
  have h := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hC.le u)
  nlinarith

theorem rpow_ge_one {C : ℝ} (hC : 1 ≤ C) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ C ^ u := by
  simpa using Real.rpow_le_rpow_of_exponent_le hC hu

/-- The remaining two comparisons in (23). -/
theorem rounded_power_calibration {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    (Nat.ceil ((C : ℝ) ^ (3 / 25 : ℝ)) : ℝ) *
        (2 : ℝ) ^ (4000 * frontWidth C) ≤ (C : ℝ) ^ (4 / 25 : ℝ) ∧
    (C : ℝ) ^ (4 / 25 : ℝ) ≤ (1 / 10 : ℝ) * (C : ℝ) ^ (1 / 5 : ℝ) := by
  have hx0 : 0 ≤ Real.log (C : ℝ) := by linarith
  have hCge : (1 : ℝ) ≤ C := by
    have h := Real.add_one_le_exp (Real.log (C : ℝ))
    rw [Real.exp_log hC] at h
    linarith
  have hone := rpow_ge_one hCge (show (0 : ℝ) ≤ 3 / 25 by norm_num)
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg hC.le (3 / 25 : ℝ))
  have hceil' : (Nat.ceil ((C : ℝ) ^ (3 / 25 : ℝ)) : ℝ) ≤
      2 * (C : ℝ) ^ (3 / 25 : ℝ) := by linarith
  obtain ⟨_, hdmiddle, hdlast⟩ := frontWidth_bounds hx
  have hd0 : (0 : ℝ) ≤ frontWidth C := Nat.cast_nonneg _
  have hprod : (frontWidth C : ℝ) * Real.log 2 ≤
      (25 / 36 : ℝ) * frontWidth C := by
    have h := mul_le_mul_of_nonneg_left log_two_bounds.2 hd0
    nlinarith only [h]
  have hexponent :
      Real.log 2 + Real.log (C : ℝ) * (3 / 25 : ℝ) +
        (4000 * (frontWidth C : ℝ)) * Real.log 2 ≤
      Real.log (C : ℝ) * (4 / 25 : ℝ) := by
    linarith [log_two_bounds.2]
  have heq :
      (2 * (C : ℝ) ^ (3 / 25 : ℝ)) *
          (2 : ℝ) ^ (4000 * frontWidth C) =
        Real.exp (Real.log 2 + Real.log (C : ℝ) * (3 / 25 : ℝ) +
          (4000 * (frontWidth C : ℝ)) * Real.log 2) := by
    rw [Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_def_of_pos hC]
    congr 1
    have hc : 4000 * (frontWidth C : ℝ) =
        ((4000 * frontWidth C : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hc, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  constructor
  · calc
      _ ≤ (2 * (C : ℝ) ^ (3 / 25 : ℝ)) *
          (2 : ℝ) ^ (4000 * frontWidth C) :=
        mul_le_mul_of_nonneg_right hceil' (by positivity)
      _ = _ := heq
      _ ≤ Real.exp (Real.log (C : ℝ) * (4 / 25 : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = _ := (Real.rpow_def_of_pos hC _).symm
  · have hten : (10 : ℝ) ≤ (C : ℝ) ^ (1 / 25 : ℝ) := by
      have h := rpow_linear_lower hC (1 / 25 : ℝ)
      linarith
    have h := rpow_scale hC (4 / 25 : ℝ) (1 / 25 : ℝ) hten
    norm_num at h
    linarith

/-- All six rounded/geometric comparisons in (24a). -/
theorem cutoff_calibration {n C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ))
    (hCn : C ≤ n) :
    smallActivation C + 1 ≤ markOrder C ∧
    (smallActivation C : ℝ) ≤ (n : ℝ) / 100 ∧
    earlyCutoff C ≤ shapeCutoff C ∧
    shapeCutoff C < bulkCount C ∧
    shapeCutoff C < sparseCount C ∧
    (C : ℝ) ^ (1 / 3 : ℝ) ≤
      (1 / 10 : ℝ) * (C : ℝ) ^ (9 / 25 : ℝ) := by
  have hCbig : (4001 : ℝ) ≤ C := by
    have h := Real.add_one_le_exp (Real.log (C : ℝ))
    rw [Real.exp_log hC] at h
    linarith
  have hCone : (1 : ℝ) ≤ C := by linarith
  have hrone := rpow_ge_one hCone (show (0 : ℝ) ≤ 1 / 100 by norm_num)
  have hwone := rpow_ge_one hCone (show (0 : ℝ) ≤ 17 / 25 by norm_num)
  have hrceil : (smallActivation C : ℝ) <
      (C : ℝ) ^ (1 / 100 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hC.le _)
  have hwceil : (shapeCutoff C : ℝ) <
      (C : ℝ) ^ (17 / 25 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hC.le _)
  have ha : (C : ℝ) ^ (1 / 25 : ℝ) ≤ (markOrder C : ℝ) :=
    Nat.le_ceil _
  have hthree : (3 : ℝ) ≤ (C : ℝ) ^ (3 / 100 : ℝ) := by
    have h := rpow_linear_lower hC (3 / 100 : ℝ)
    linarith
  have hmark := rpow_scale hC (1 / 100 : ℝ) (3 / 100 : ℝ) hthree
  norm_num at hmark
  have htwohundred : (200 : ℝ) ≤ (C : ℝ) ^ (99 / 100 : ℝ) := by
    have h := rpow_linear_lower hC (99 / 100 : ℝ)
    linarith
  have hsmall := rpow_scale hC (1 / 100 : ℝ) (99 / 100 : ℝ) htwohundred
  norm_num at hsmall
  have hfour : (4000 : ℝ) ≤ (C : ℝ) ^ (8 / 25 : ℝ) := by
    have h := rpow_linear_lower hC (8 / 25 : ℝ)
    linarith
  have hshape := rpow_scale hC (17 / 25 : ℝ) (8 / 25 : ℝ) hfour
  norm_num at hshape
  have hwbound : (shapeCutoff C : ℝ) ≤ (C : ℝ) / 2000 := by
    linarith
  have hbulk : (C : ℝ) / 10 ≤ (bulkCount C : ℝ) := Nat.le_ceil _
  have hsparse : (C : ℝ) / 1000 - 1 < (sparseCount C : ℝ) :=
    Nat.sub_one_lt_floor _
  have hCn' : (C : ℝ) ≤ (n : ℝ) := by exact_mod_cast hCn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (smallActivation C : ℝ) + 1 ≤ (markOrder C : ℝ) := by
      linarith
    exact_mod_cast h
  · linarith
  · exact Nat.ceil_mono
      (Real.rpow_le_rpow_of_exponent_le hCone
        (show (51 / 100 : ℝ) ≤ 17 / 25 by norm_num))
  · have h : (shapeCutoff C : ℝ) < (bulkCount C : ℝ) := by linarith
    exact_mod_cast h
  · have h : (shapeCutoff C : ℝ) < (sparseCount C : ℝ) := by linarith
    exact_mod_cast h
  · have hten : (10 : ℝ) ≤ (C : ℝ) ^ (2 / 75 : ℝ) := by
      have h := rpow_linear_lower hC (2 / 75 : ℝ)
      linarith
    have h := rpow_scale hC (1 / 3 : ℝ) (2 / 75 : ℝ) hten
    norm_num at h
    linarith

/-- The two horizon comparisons in (24c), using the document's ceilings. -/
theorem horizon_calibration {n C : ℕ}
    (hn : populationThreshold ≤ n)
    (hlo : (6 / 25 : ℝ) * n ≤ C)
    (hCn : C ≤ n) :
    (firstHitHorizon n : ℝ) ≤ 31 * (n : ℝ) * Real.log (n : ℝ) ∧
    31 * (n : ℝ) * Real.log (n : ℝ) ≤
      130 * (C : ℝ) * Real.log (C : ℝ) ∧
    (561 / 1000 : ℝ) * ((activationHalfHorizon n : ℝ) / n) +
        2 * (fineTicks C : ℝ) / ((C : ℝ) - 1) ≤
      (29 / 100 : ℝ) * Real.log (C : ℝ) := by
  obtain ⟨hCp, hx, hxy, hyx, _⟩ := logarithmic_inputs hn hlo hCn
  clear hn
  obtain ⟨_, hdmiddle, hdlast⟩ := frontWidth_bounds hx
  have hx0 : 0 ≤ Real.log (C : ℝ) := by linarith
  have hy0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hCbig : (4001 : ℝ) ≤ C := by
    have h := Real.add_one_le_exp (Real.log (C : ℝ))
    rw [Real.exp_log hCp] at h
    linarith
  have hCn' : (C : ℝ) ≤ (n : ℝ) := by exact_mod_cast hCn
  have hnge : (1 : ℝ) ≤ n := by linarith
  have hnp : 0 < (n : ℝ) := by linarith
  have hny : (1 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have h := mul_nonneg hnp.le
      (show 0 ≤ Real.log (n : ℝ) - 1 by linarith)
    nlinarith
  have hU : (firstHitHorizon n : ℝ) <
      30 * (n : ℝ) * Real.log (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hT : (activationHalfHorizon n : ℝ) <
      (n : ℝ) * Real.log (n : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hTdiv : (activationHalfHorizon n : ℝ) / n ≤
      Real.log (n : ℝ) / 2 + 1 := by
    rw [div_le_iff₀ hnp]
    nlinarith
  have hnr : (n : ℝ) ≤ (25 / 6 : ℝ) * C := by linarith
  have hyr : Real.log (n : ℝ) ≤ (201 / 200 : ℝ) * Real.log (C : ℝ) := by
    linarith
  have hprod := mul_le_mul hnr hyr hy0
    (by positivity : (0 : ℝ) ≤ (25 / 6 : ℝ) * C)
  have hCx : 0 ≤ (C : ℝ) * Real.log (C : ℝ) :=
    mul_nonneg hCp.le hx0
  have hden : (0 : ℝ) < (C : ℝ) - 1 := by linarith
  have hratio : (400 : ℝ) * C / ((C : ℝ) - 1) ≤ 401 := by
    rw [div_le_iff₀ hden]
    linarith
  have hD : 2 * (fineTicks C : ℝ) / ((C : ℝ) - 1) ≤
      401 * (frontWidth C : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hratio
      (Nat.cast_nonneg (frontWidth C) : (0 : ℝ) ≤ _)
    calc
      _ = (frontWidth C : ℝ) *
          ((400 : ℝ) * C / ((C : ℝ) - 1)) := by
        simp only [fineTicks, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ (frontWidth C : ℝ) * 401 := hm
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · linarith

/-- Equation (24d), with a = ceiling(C^(1/25)). -/
theorem exponential_error_calibration {C : ℕ}
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    Real.exp (-(markOrder C : ℝ) / 3) + Real.exp (-(markOrder C : ℝ)) ≤
      (C : ℝ) ^ (-100 : ℝ) ∧
    Real.exp (-(9 / 100 : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ)) ≤
      (C : ℝ) ^ (-100 : ℝ) ∧
    6 * (C : ℝ) ^ (-(1 / 300 : ℝ)) ≤ Real.exp (-1) := by
  have hx0 : 0 ≤ Real.log (C : ℝ) := by linarith
  obtain ⟨_, hsmall, hmark, _⟩ := new_power_calibration hC hx
  have ha : (C : ℝ) ^ (1 / 25 : ℝ) ≤ (markOrder C : ℝ) :=
    Nat.le_ceil _
  have hA : Real.exp (-(markOrder C : ℝ) / 3) ≤
      Real.exp (-101 * Real.log (C : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (-(markOrder C : ℝ)) ≤
      Real.exp (-101 * Real.log (C : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp (Real.log (C : ℝ)) := by
    have h := Real.add_one_le_exp (Real.log (C : ℝ))
    linarith
  constructor
  · calc
      _ ≤ 2 * Real.exp (-101 * Real.log (C : ℝ)) := by linarith
      _ ≤ Real.exp (Real.log (C : ℝ)) *
          Real.exp (-101 * Real.log (C : ℝ)) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (Real.log (C : ℝ) * (-100)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := (Real.rpow_def_of_pos hC _).symm
  constructor
  · calc
      Real.exp (-(9 / 100 : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ)) ≤
          Real.exp (Real.log (C : ℝ) * (-100)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := (Real.rpow_def_of_pos hC _).symm
  · calc
      6 * (C : ℝ) ^ (-(1 / 300 : ℝ)) =
          Real.exp (Real.log 6 + Real.log (C : ℝ) * (-(1 / 300 : ℝ))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 6),
          Real.rpow_def_of_pos hC]
      _ ≤ Real.exp (-1) :=
        Real.exp_le_exp.mpr (by linarith [log_small_bounds.1])

end Numeric

/-! ## Uniform occurrence labels and configuration cylinders -/


namespace OccurrenceScheduler

open Preorder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- A state and occurrence index distinguish equal-state agents. -/
abbrev OccurrenceLabel (Λ : Type*) := Λ × ℕ

abbrev OccurrencePair (Λ : Type*) :=
  OccurrenceLabel Λ × OccurrenceLabel Λ

def occurrencePairs (c : Config Λ) : Finset (OccurrencePair Λ) :=
  c.toEnumFinset.offDiag

def occurrenceStatePair (p : OccurrencePair Λ) : Λ × Λ :=
  (p.1.1, p.2.1)

def occurrenceFiber (c : Config Λ) (s : Λ) : Finset (OccurrenceLabel Λ) :=
  c.toEnumFinset.filter fun a => a.1 = s

@[simp] theorem occurrenceFiber_card (c : Config Λ) (s : Λ) :
    (occurrenceFiber c s).card = c.count s := by
  unfold occurrenceFiber
  rw [Multiset.toEnumFinset_filter_eq]
  simp [Config.count]

@[simp] theorem occurrencePairs_card (c : Config Λ) :
    (occurrencePairs c).card = c.totalPairs := by
  simp [occurrencePairs, Finset.offDiag_card, Multiset.card_toEnumFinset,
    Config.totalPairs, Nat.mul_sub_left_distrib]

theorem occurrencePairs_nonempty (c : Config Λ) (hc : 2 ≤ c.card) :
    (occurrencePairs c).Nonempty := by
  apply Finset.card_pos.mp
  rw [occurrencePairs_card]
  exact Config.totalPairs_pos hc

theorem occurrence_pair_fiber_card (c : Config Λ) (s t : Λ) :
    ((occurrencePairs c).filter
      (fun p => (s, t) = occurrenceStatePair p)).card =
        c.interactionCount s t := by
  classical
  by_cases hst : s = t
  · subst t
    have hf :
        (occurrencePairs c).filter
            (fun p => (s, s) = occurrenceStatePair p) =
          (occurrenceFiber c s).offDiag := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
        obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
        have hfirst : p.1.1 = s :=
          (congrArg Prod.fst heq).symm
        have hsecond : p.2.1 = s :=
          (congrArg Prod.snd heq).symm
        exact Finset.mem_offDiag.mpr
          ⟨Finset.mem_filter.mpr ⟨ha, hfirst⟩,
           Finset.mem_filter.mpr ⟨hb, hsecond⟩, hne⟩
      · intro hp
        obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
        obtain ⟨ha, hfirst⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb, hsecond⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩,
            Prod.ext hfirst.symm hsecond.symm⟩
    rw [hf, Finset.offDiag_card, occurrenceFiber_card]
    simp [Config.interactionCount, Nat.mul_sub_left_distrib]
  · have hf :
        (occurrencePairs c).filter
            (fun p => (s, t) = occurrenceStatePair p) =
          occurrenceFiber c s ×ˢ occurrenceFiber c t := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
        obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hp
        have hfirst : p.1.1 = s :=
          (congrArg Prod.fst heq).symm
        have hsecond : p.2.1 = t :=
          (congrArg Prod.snd heq).symm
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨ha, hfirst⟩,
           Finset.mem_filter.mpr ⟨hb, hsecond⟩⟩
      · intro hp
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
        obtain ⟨ha, hfirst⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb, hsecond⟩ := Finset.mem_filter.mp hb
        have hne : p.1 ≠ p.2 := by
          intro heq
          apply hst
          exact hfirst.symm.trans ((congrArg Prod.fst heq).trans hsecond)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩,
            Prod.ext hfirst.symm hsecond.symm⟩
    rw [hf, Finset.card_product, occurrenceFiber_card, occurrenceFiber_card]
    simp [Config.interactionCount, hst]

private theorem uniform_finset_map_apply
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (hs : s.Nonempty) (f : α → β) (b : β) :
    ((PMF.uniformOfFinset s hs).map f) b =
      (((s.filter fun a => b = f a).card : ℝ≥0∞) /
        (s.card : ℝ≥0∞)) := by
  classical
  calc
    ((PMF.uniformOfFinset s hs).map f) b =
        ∑' a, if b = f a then PMF.uniformOfFinset s hs a else 0 := by
      rw [PMF.map_apply]
      apply tsum_congr
      intro a
      by_cases h : b = f a
      · simp only [if_pos h]
      · simp only [if_neg h]
    _ = ∑ a ∈ s, if b = f a then PMF.uniformOfFinset s hs a else 0 := by
      exact tsum_eq_sum fun a ha => by
        simp [PMF.uniformOfFinset_apply_of_notMem hs ha]
    _ = ∑ a ∈ s, if b = f a then (s.card : ℝ≥0∞)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [PMF.uniformOfFinset_apply_of_mem hs ha]
    _ = ∑ a ∈ s.filter (fun a => b = f a), (s.card : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_filter]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

noncomputable def occurrencePairLaw (c : Config Λ) (hc : 2 ≤ c.card) :
    PMF (OccurrencePair Λ) :=
  PMF.uniformOfFinset (occurrencePairs c) (occurrencePairs_nonempty c hc)

theorem occurrence_pair_state_law (c : Config Λ) (hc : 2 ≤ c.card) :
    (occurrencePairLaw c hc).map occurrenceStatePair = c.interactionPMF hc := by
  ext p
  rcases p with ⟨s, t⟩
  change ((PMF.uniformOfFinset (occurrencePairs c)
      (occurrencePairs_nonempty c hc)).map occurrenceStatePair) (s, t) =
    (c.interactionCount s t : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)
  rw [uniform_finset_map_apply, occurrence_pair_fiber_card, occurrencePairs_card]

theorem occurrence_pair_applicable (c : Config Λ) (p : OccurrencePair Λ)
    (hp : p ∈ occurrencePairs c) :
    Protocol.Applicable c p.1.1 p.2.1 := by
  classical
  obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
  have hnot : p.1 ∉ ({p.2} : Finset (OccurrenceLabel Λ)) := by
    simpa using hne
  let two : Finset (OccurrenceLabel Λ) := Finset.cons p.1 {p.2} hnot
  have htwo : two ⊆ c.toEnumFinset := by
    intro a h
    rcases Finset.mem_cons.mp h with h | h
    · simpa [h] using ha
    · have heq : a = p.2 := Finset.mem_singleton.mp h
      simpa [heq] using hb
  have hle := Multiset.map_fst_le_of_subset_toEnumFinset htwo
  change ({p.1.1, p.2.1} : Multiset Λ) ≤ c
  simpa only [two, Finset.cons_val, Finset.singleton_val,
    Multiset.map_cons, Multiset.map_singleton] using hle

def occurrenceResult (P : Protocol Λ) (c : Config Λ)
    (p : OccurrencePair Λ) : Config Λ :=
  c - {p.1.1, p.2.1} +
    {(P.δ p.1.1 p.2.1).1, (P.δ p.1.1 p.2.1).2}

theorem occurrenceResult_eq_scheduled (P : Protocol Λ) (c : Config Λ)
    (p : OccurrencePair Λ) (hp : p ∈ occurrencePairs c) :
    occurrenceResult P c p =
      Protocol.scheduledStep P c (occurrenceStatePair p) := by
  unfold occurrenceResult Protocol.scheduledStep Protocol.stepOrSelf
  dsimp [occurrenceStatePair]
  rw [if_pos (occurrence_pair_applicable c p hp)]

theorem labeled_scheduler_projects (P : Protocol Λ) (c : Config Λ)
    (hc : 2 ≤ c.card) :
    (occurrencePairLaw c hc).map (occurrenceResult P c) = P.stepDist c hc := by
  classical
  calc
    (occurrencePairLaw c hc).map (occurrenceResult P c)
        = (occurrencePairLaw c hc).map
            (fun p => Protocol.scheduledStep P c (occurrenceStatePair p)) := by
          ext c'
          simp only [PMF.map_apply]
          apply tsum_congr
          intro p
          by_cases hp : p ∈ occurrencePairs c
          · rw [occurrenceResult_eq_scheduled P c p hp]
          · have hz : occurrencePairLaw c hc p = 0 :=
              PMF.uniformOfFinset_apply_of_notMem
                (occurrencePairs_nonempty c hc) hp
            simp [hz]
    _ = ((occurrencePairLaw c hc).map occurrenceStatePair).map
          (Protocol.scheduledStep P c) := by
          simp only [PMF.map_comp, Function.comp_def]
    _ = P.stepDist c hc := by
          simp only [occurrence_pair_state_law, Protocol.stepDist]

noncomputable def occurrenceStepDist (P : Protocol Λ) (c : Config Λ) :
    PMF (Config Λ) :=
  if hc : 2 ≤ c.card then
    (occurrencePairLaw c hc).map (occurrenceResult P c)
  else PMF.pure c

theorem occurrenceStepDist_eq (P : Protocol Λ) (c : Config Λ) :
    occurrenceStepDist P c = P.stepDistOrSelf c := by
  by_cases hc : 2 ≤ c.card
  · simp only [occurrenceStepDist, Protocol.stepDistOrSelf, dif_pos hc]
    exact labeled_scheduler_projects P c hc
  · simp only [occurrenceStepDist, Protocol.stepDistOrSelf, dif_neg hc]

noncomputable def occurrenceKernel (P : Protocol Λ) :
    Kernel (Config Λ) (Config Λ) where
  toFun c := (occurrenceStepDist P c).toMeasure
  measurable' := Measurable.of_discrete

theorem occurrenceKernel_eq (P : Protocol Λ) :
    occurrenceKernel P = P.transitionKernel := by
  ext c s hs
  change (occurrenceStepDist P c).toMeasure s =
    (P.stepDistOrSelf c).toMeasure s
  rw [occurrenceStepDist_eq]

instance occurrenceKernel_isMarkov (P : Protocol Λ) :
    IsMarkovKernel (occurrenceKernel P) := by
  rw [occurrenceKernel_eq]
  infer_instance

/-- Occurrence labels are re-enumerated at each projected step.
This is not a persistent-agent path construction. -/
noncomputable def occurrenceKfamily (L K : ℕ) (t : ℕ) :
    Kernel (Π i : Finset.Iic t, ProtocolTraceLaw.St L K i)
      (ProtocolTraceLaw.St L K (t + 1)) :=
  Kernel.comap (occurrenceKernel (NonuniformMajority L K))
    (fun x => x ⟨t, Finset.mem_Iic.2 le_rfl⟩)
    (measurable_pi_apply _)

theorem occurrenceKfamily_eq (L K : ℕ) :
    occurrenceKfamily L K = ProtocolTraceLaw.kfamily (L := L) (K := K) := by
  funext t
  unfold occurrenceKfamily ProtocolTraceLaw.kfamily
  rw [occurrenceKernel_eq]

instance occurrenceKfamily_isMarkov (L K t : ℕ) :
    IsMarkovKernel (occurrenceKfamily L K t) := by
  rw [show occurrenceKfamily L K t =
      ProtocolTraceLaw.kfamily (L := L) (K := K) t from
    congrFun (occurrenceKfamily_eq L K) t]
  infer_instance

noncomputable def occurrencePrefixLaw {L K : ℕ}
    (entry : Config (AgentState L K)) (T : ℕ) :
    Measure (Π i : Finset.Iic T, ProtocolTraceLaw.St L K i) :=
  Kernel.partialTraj (occurrenceKfamily L K) 0 T (fun _ => entry)

theorem labeled_scheduler_projects_prefix {L K : ℕ}
    (entry : Config (AgentState L K)) (T : ℕ) :
    Measure.map (frestrictLe (π := ProtocolTraceLaw.St L K) T)
      (ProtocolTraceLaw.μ entry) = occurrencePrefixLaw entry T := by
  unfold occurrencePrefixLaw
  rw [occurrenceKfamily_eq]
  unfold ProtocolTraceLaw.μ ProtocolTraceLaw.traj0
  rw [Kernel.traj_map_frestrictLe_apply]

theorem labeled_scheduler_projects_cylinder {L K : ℕ}
    (entry : Config (AgentState L K)) (T : ℕ)
    (A : Set (Π i : Finset.Iic T, ProtocolTraceLaw.St L K i))
    (hA : MeasurableSet A) :
    ProtocolTraceLaw.μ entry
      {tr | frestrictLe (π := ProtocolTraceLaw.St L K) T tr ∈ A} =
        occurrencePrefixLaw entry T A := by
  have h := congrArg
    (fun ν : Measure (Π i : Finset.Iic T, ProtocolTraceLaw.St L K i) => ν A)
    (labeled_scheduler_projects_prefix entry T)
  dsimp only at h
  rw [Measure.map_apply (measurable_frestrictLe T) hA] at h
  exact h

end OccurrenceScheduler


/-! ## The exact one-draw Clock-tick law

The random variable here is on the scheduler's sampled ordered state pair.
It is deliberately not declared to be an observable of a configuration
transition: invisible Phase-2 Clock interactions prevent that declaration.
-/

section ClockTicks

variable {L K : ℕ}

def clockPairBit (p : AgentState L K × AgentState L K) : Bool :=
  decide (p.1.role = .clock ∧ p.2.role = .clock)

noncomputable def clockTickPMF
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) : PMF Bool :=
  (c.interactionPMF hc).map clockPairBit

theorem clock_pair_count (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter
        (fun a : AgentState L K => a.role = .clock),
      ∑ b ∈ Finset.univ.filter
        (fun b : AgentState L K => b.role = .clock),
        c.interactionCount a b) =
      ClockRealMixed.clockCount c * (ClockRealMixed.clockCount c - 1) := by
  classical
  calc
    _ = ∑ a ∈ Finset.univ.filter
          (fun a : AgentState L K => a.role = .clock),
          c.count a * (ClockRealMixed.clockCount c - 1) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact ClockRealMixed.sum_interactionCount_frontier_row c a
        (Finset.mem_filter.mp ha).2
    _ = (∑ a ∈ Finset.univ.filter
          (fun a : AgentState L K => a.role = .clock), c.count a) *
          (ClockRealMixed.clockCount c - 1) := by
      rw [Finset.sum_mul]
    _ = _ := by rw [ClockRealMixed.sum_count_clocks]

theorem clock_pair_probability (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter
        (fun a : AgentState L K => a.role = .clock),
      ∑ b ∈ Finset.univ.filter
        (fun b : AgentState L K => b.role = .clock),
        c.interactionProb a b) =
      ((ClockRealMixed.clockCount c *
        (ClockRealMixed.clockCount c - 1) : ℕ) : ℝ≥0∞) /
        (c.totalPairs : ℝ≥0∞) := by
  classical
  have hcount :
      (∑ a ∈ Finset.univ.filter
          (fun a : AgentState L K => a.role = .clock),
        ∑ b ∈ Finset.univ.filter
          (fun b : AgentState L K => b.role = .clock),
          (c.interactionCount a b : ℝ≥0∞)) =
        ((ClockRealMixed.clockCount c *
          (ClockRealMixed.clockCount c - 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast clock_pair_count c
  simp only [Config.interactionProb, div_eq_mul_inv]
  simp_rw [← Finset.sum_mul]
  rw [hcount]

theorem clock_tick_law
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    clockTickPMF c hc true =
      ((ClockRealMixed.clockCount c *
        (ClockRealMixed.clockCount c - 1) : ℕ) : ℝ≥0∞) /
        (c.totalPairs : ℝ≥0∞) := by
  classical
  unfold clockTickPMF
  calc
    ((c.interactionPMF hc).map clockPairBit) true =
        ∑ p : AgentState L K × AgentState L K,
          if true = clockPairBit p then c.interactionProb p.1 p.2 else 0 := by
      rw [PMF.map_apply, tsum_fintype]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : true = clockPairBit p
      · simpa only [if_pos h] using
          (show (c.interactionPMF hc) p =
            c.interactionProb p.1 p.2 from rfl)
      · simp only [if_neg h]
    _ = ∑ a ∈ Finset.univ.filter
          (fun a : AgentState L K => a.role = .clock),
        ∑ b ∈ Finset.univ.filter
          (fun b : AgentState L K => b.role = .clock),
          c.interactionProb a b := by
      rw [show (Finset.univ :
          Finset (AgentState L K × AgentState L K)) =
          Finset.univ ×ˢ Finset.univ from
            (Finset.univ_product_univ).symm]
      simp only [Finset.sum_product, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases ha : a.role = .clock
      · simp [clockPairBit, ha]
      · simp [clockPairBit, ha]
    _ = _ := clock_pair_probability c

theorem clock_tick_rate_le_one
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    ((ClockRealMixed.clockCount c *
        (ClockRealMixed.clockCount c - 1) : ℕ) : ℝ≥0∞) /
        (c.totalPairs : ℝ≥0∞) ≤ 1 := by
  rw [← clock_tick_law c hc]
  exact PMF.coe_le_one (clockTickPMF c hc) true

end ClockTicks

/-- A one-step extension retains the sampled state pair as well as its image. -/
noncomputable def clockJointStepPMF {L K : ℕ}
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    PMF ((AgentState L K × AgentState L K) × Config (AgentState L K)) :=
  (c.interactionPMF hc).map
    (fun p => (p, Protocol.scheduledStep (NonuniformMajority L K) c p))

theorem clock_joint_step_projects {L K : ℕ}
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    (clockJointStepPMF c hc).map Prod.snd =
      (NonuniformMajority L K).stepDistOrSelf c := by
  simp only [clockJointStepPMF, PMF.map_comp, Function.comp_def,
    Protocol.stepDistOrSelf, dif_pos hc, Protocol.stepDist]

theorem clock_joint_step_tick_law {L K : ℕ}
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    ((clockJointStepPMF c hc).map (fun p => clockPairBit p.1)) true =
      ((ClockRealMixed.clockCount c *
        (ClockRealMixed.clockCount c - 1) : ℕ) : ℝ≥0∞) /
        (c.totalPairs : ℝ≥0∞) := by
  unfold clockJointStepPMF
  rw [PMF.map_comp]
  change clockTickPMF c hc true = _
  exact clock_tick_law c hc

/-- The state marginal is the actual one-step marginal of ProtocolTraceLaw. -/
theorem clock_joint_step_trace_marginal {L K : ℕ}
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    Measure.map (fun tr : Phase3GoodClock.Trace L K => tr 1)
        (ProtocolTraceLaw.μ c) =
      ((clockJointStepPMF c hc).map Prod.snd).toMeasure := by
  rw [clock_joint_step_projects]
  have h := (ProtocolTraceLaw.traceLawAt c 1).endpoint_law
  simpa only [pow_one, Protocol.transitionKernel] using h

/-! ## Initialized Clock-pair front facts -/


variable {L K : ℕ}

/-- The exact selected active-pair event behind the ordinary P2 formula. -/
theorem active_pair_front_step
    (T : ℕ) (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hcap : T < K * (L + 1)) :
    ClockRealKernel.rBeyond (T + 1)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Config (AgentState L K)) =
      ClockRealKernel.rBeyond (T + 1) ({s, t} : Config (AgentState L K)) +
        (if (s.minute.val ≤ T ∧ T < t.minute.val) ∨
              (t.minute.val ≤ T ∧ T < s.minute.val) ∨
              (s.minute.val = T ∧ t.minute.val = T)
          then 1 else 0) := by
  classical
  change
    Multiset.countP (ClockRealKernel.clockBeyondP (T + 1))
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) =
      Multiset.countP (ClockRealKernel.clockBeyondP (T + 1))
        ({s, t} : Multiset (AgentState L K)) + _
  rw [ClockRealKernel.countP_pair, ClockRealKernel.countP_pair]
  by_cases hmin : s.minute = t.minute
  · have hval : s.minute.val = t.minute.val := congrArg Fin.val hmin
    by_cases hbelow : s.minute.val < K * (L + 1)
    · have hd := Transition_phase3_clock_minute_drip_decreases
        (L := L) (K := K) s t hs_phase ht_phase
        hs_clock ht_clock hmin hbelow
      have hsrole := hd.2.2.1
      have htrole := hd.2.2.2.1
      have hsminute := hd.2.2.2.2.1
      have htminute := hd.2.2.2.2.2.1
      simp only [ClockRealKernel.clockBeyondP, hs_clock, ht_clock,
        hsrole, htrole, true_and, hsminute, htminute]
      split_ifs <;> omega
    · have hc := ClockRealKernel.Transition_phase3_clock_cap
        (L := L) (K := K) s t hs_phase ht_phase
        hs_clock ht_clock hmin hbelow
      simp only [ClockRealKernel.clockBeyondP, hs_clock, ht_clock,
        hc.1, hc.2.1, true_and, hc.2.2.1, hc.2.2.2]
      split_ifs <;> omega
  · have hval : s.minute.val ≠ t.minute.val := by
      intro h
      exact hmin (Fin.ext h)
    have hs := Transition_phase3_clock_minute_sync_decreases
      (L := L) (K := K) s t hs_phase ht_phase
      hs_clock ht_clock hmin
    have hsrole := hs.2.2.1
    have htrole := hs.2.2.2.1
    have hsminute := hs.2.2.2.2.1
    have htminute := hs.2.2.2.2.2.1
    simp only [ClockRealKernel.clockBeyondP, hs_clock, ht_clock,
      hsrole, htrole, true_and, hsminute, htminute]
    rcases le_total s.minute t.minute with hle | hle
    · rw [max_eq_right hle]
      change s.minute.val ≤ t.minute.val at hle
      split_ifs <;> omega
    · rw [max_eq_left hle]
      change t.minute.val ≤ s.minute.val at hle
      split_ifs <;> omega

/-- The ambient population may contain non-Clocks; only the selected pair
is required to consist of initialized Phase-3 Clocks. -/
theorem active_clock_pair_step_interval
    (T : ℕ) (c : Config (AgentState L K)) (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    ClockRealKernel.rBeyond T c ≤
        ClockRealKernel.rBeyond T
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ∧
      ClockRealKernel.rBeyond T
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
        ClockRealKernel.rBeyond T c + 1 := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} +
            {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hin :
        Multiset.countP (fun a => ClockRealKernel.clockBeyondP T a)
            ({s, t} : Multiset (AgentState L K)) ≤
          Multiset.countP (fun a => ClockRealKernel.clockBeyondP T a) c :=
      Multiset.countP_le_of_le _ hsub
    have hlo := ClockRealKernel.rBeyond_pair_mono
      (L := L) (K := K) T s t hs_phase ht_phase hs_clock ht_clock
    have hhi := Phase3GoodClockRegime.rBeyond_pair_le_add_one
      (L := L) (K := K) T s t hs_phase ht_phase hs_clock ht_clock
    simp only [ClockRealKernel.rBeyond, hstep, Multiset.countP_add,
      Multiset.countP_sub hsub]
    constructor <;> omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    constructor <;> omega

theorem active_clock_pair_step_zero_or_one
    (T : ℕ) (c : Config (AgentState L K)) (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    ClockRealKernel.rBeyond T
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
        ClockRealKernel.rBeyond T c ∨
      ClockRealKernel.rBeyond T
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
        ClockRealKernel.rBeyond T c + 1 := by
  have h := active_clock_pair_step_interval
    T c s t hs_phase ht_phase hs_clock ht_clock
  omega

theorem clock_front_kernel_interval
    (T : ℕ) (c c' : Config (AgentState L K))
    (hc : ClockRealKernel.AllClockP3 c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ClockRealKernel.rBeyond T c ≤ ClockRealKernel.rBeyond T c' ∧
      ClockRealKernel.rBeyond T c' ≤ ClockRealKernel.rBeyond T c + 1 := by
  exact ⟨ClockRealKernel.rBeyond_ge_monotone
      T (ClockRealKernel.rBeyond T c) c c' hc le_rfl hc',
    Phase3GoodClockRegime.rBeyond_step_unit_increment T c c' hc hc'⟩

theorem clock_trace_step_event
    (c : Config (AgentState L K))
    (A : Set (Config (AgentState L K))) :
    ProtocolTraceLaw.μ c {tr | tr 1 ∈ A} =
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
  have hA : MeasurableSet A :=
    DiscreteMeasurableSpace.forall_measurableSet _
  calc
    ProtocolTraceLaw.μ c {tr | tr 1 ∈ A} =
        (Measure.map (fun tr : Phase3GoodClock.Trace L K => tr 1)
          (ProtocolTraceLaw.μ c)) A := by
      rw [Measure.map_apply (measurable_pi_apply 1) hA] <;> rfl
    _ = (((NonuniformMajority L K).transitionKernel ^ 1) c) A := by
      rw [(ProtocolTraceLaw.traceLawAt c 1).endpoint_law]
    _ = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
      rw [pow_one] <;> rfl

theorem clock_front_trace_bad_increment_zero
    (T : ℕ) (c : Config (AgentState L K))
    (hc : ClockRealKernel.AllClockP3 c) :
    ProtocolTraceLaw.μ c
      {tr | ¬ (ClockRealKernel.rBeyond T c ≤
          ClockRealKernel.rBeyond T (tr 1) ∧
        ClockRealKernel.rBeyond T (tr 1) ≤
          ClockRealKernel.rBeyond T c + 1)} = 0 := by
  classical
  change ProtocolTraceLaw.μ c
      {tr | tr 1 ∈
        {c' : Config (AgentState L K) |
          ¬ (ClockRealKernel.rBeyond T c ≤ ClockRealKernel.rBeyond T c' ∧
            ClockRealKernel.rBeyond T c' ≤
              ClockRealKernel.rBeyond T c + 1)}} = 0
  rw [clock_trace_step_event c
    {c' | ¬ (ClockRealKernel.rBeyond T c ≤ ClockRealKernel.rBeyond T c' ∧
      ClockRealKernel.rBeyond T c' ≤ ClockRealKernel.rBeyond T c + 1)}]
  rw [PMF.toMeasure_apply_eq_zero_iff
    (p := (NonuniformMajority L K).stepDistOrSelf c)
    (s := {c' | ¬ (ClockRealKernel.rBeyond T c ≤ ClockRealKernel.rBeyond T c' ∧
      ClockRealKernel.rBeyond T c' ≤ ClockRealKernel.rBeyond T c + 1)})
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (clock_front_kernel_interval T c c' hc hsupp)

/-- A same-state drip contribution, not the full gated P2 equality. -/
theorem clock_drip_trace_lower_bound
    (T : ℕ) (c : Config (AgentState L K)) (w : AgentState L K)
    (hw_phase : w.phase.val = 3) (hw_clock : w.role = .clock)
    (hw_min : w.minute.val = T) (hcap : T < K * (L + 1))
    (hc : 2 ≤ c.card) (hcount : 2 ≤ c.count w) :
    ENNReal.ofReal ((c.count w * (c.count w - 1) : ℝ) /
      (c.card * (c.card - 1) : ℝ)) ≤
      ProtocolTraceLaw.μ c
        {tr | ClockRealKernel.rBeyond (T + 1) c + 1 ≤
          ClockRealKernel.rBeyond (T + 1) (tr 1)} := by
  change ENNReal.ofReal ((c.count w * (c.count w - 1) : ℝ) /
      (c.card * (c.card - 1) : ℝ)) ≤
    ProtocolTraceLaw.μ c
      {tr | tr 1 ∈
        {c' : Config (AgentState L K) |
          ClockRealKernel.rBeyond (T + 1) c + 1 ≤
            ClockRealKernel.rBeyond (T + 1) c'}}
  rw [clock_trace_step_event c
    {c' | ClockRealKernel.rBeyond (T + 1) c + 1 ≤
      ClockRealKernel.rBeyond (T + 1) c'}]
  exact ClockRealKernel.clock_real_drip_advance_prob
    T c w hw_phase hw_clock hw_min hcap hc
    (ClockRealKernel.rBeyond (T + 1) c) rfl hcount

def inactiveClock : AgentState 0 256 where
  input := .A
  output := .T
  phase := ⟨2, by decide⟩
  role := .clock
  assigned := false
  bias := .zero
  smallBias := ⟨3, by decide⟩
  hour := ⟨0, by decide⟩
  minute := ⟨0, by decide⟩
  full := false
  opinions := ⟨2, by decide⟩
  counter := ⟨50, by decide⟩

def inactiveReserve : AgentState 0 256 :=
  { inactiveClock with role := .reserve }

def activeClock : AgentState 0 256 :=
  { inactiveClock with phase := ⟨3, by decide⟩ }

def staleInactiveClock : AgentState 0 256 :=
  { inactiveClock with minute := ⟨256, by decide⟩ }

theorem inactive_clock_pair_self_loop :
    Transition 0 256 inactiveClock inactiveClock =
      (inactiveClock, inactiveClock) := by
  decide +kernel

theorem inactive_reserve_pair_self_loop :
    Transition 0 256 inactiveReserve inactiveReserve =
      (inactiveReserve, inactiveReserve) := by
  decide +kernel

theorem inactive_cross_pair_self_loop :
    Transition 0 256 inactiveClock inactiveReserve =
        (inactiveClock, inactiveReserve) ∧
      Transition 0 256 inactiveReserve inactiveClock =
        (inactiveReserve, inactiveClock) := by
  decide +kernel

theorem active_inactive_clock_pair_drips :
    (Transition 0 256 activeClock inactiveClock).1.minute.val = 1 ∧
      (Transition 0 256 activeClock inactiveClock).2.minute.val = 0 ∧
      (Transition 0 256 activeClock inactiveClock).2.phase.val = 3 := by
  decide +kernel

theorem raw_front_drops_on_activation :
    ClockRealKernel.rBeyond 2
      ({(Transition 0 256 staleInactiveClock activeClock).1,
        (Transition 0 256 staleInactiveClock activeClock).2} :
          Config (AgentState 0 256)) = 0 ∧
    ClockRealKernel.rBeyond 2
      ({staleInactiveClock, activeClock} : Config (AgentState 0 256)) = 1 := by
  decide +kernel


/-! ## A sampled Clock tick is not determined by the state transition -/

def invisibleLabelState (i : Fin 4) : AgentState 0 256 :=
  if i.val < 2 then inactiveClock else inactiveReserve

def invisibleLabelStep (i j : Fin 4) : Fin 4 → AgentState 0 256 :=
  let out := Transition 0 256 (invisibleLabelState i) (invisibleLabelState j)
  Function.update (Function.update invisibleLabelState i out.1) j out.2

theorem invisible_label_step (i j : Fin 4) :
    invisibleLabelStep i j = invisibleLabelState := by
  funext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem invisible_ticks_differ :
    clockPairBit (invisibleLabelState 0, invisibleLabelState 1) = true ∧
    clockPairBit (invisibleLabelState 2, invisibleLabelState 3) = false := by
  decide +kernel

/-- Even the full labeled state before and after a step cannot reveal its
sampled Clock-tick bit. The example is a local obstruction, not a valid-input
large-population entry theorem. -/
theorem no_labeled_state_tick_reader :
    ¬ ∃ read :
        (Fin 4 → AgentState 0 256) →
        (Fin 4 → AgentState 0 256) → Bool,
      ∀ i j : Fin 4, i ≠ j →
        read invisibleLabelState (invisibleLabelStep i j) =
          clockPairBit (invisibleLabelState i, invisibleLabelState j) := by
  rintro ⟨read, hread⟩
  have hc := hread (0 : Fin 4) (1 : Fin 4) (by decide)
  have hr := hread (2 : Fin 4) (3 : Fin 4) (by decide)
  rw [invisible_label_step, invisible_ticks_differ.1] at hc
  rw [invisible_label_step, invisible_ticks_differ.2] at hr
  have hbad : true = false := hc.symm.trans hr
  cases hbad

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeModel
