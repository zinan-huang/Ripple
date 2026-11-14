/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closed numerical calibration for the joint Phase-1 stopped argument

This file sharpens the Phase-1 drift horizon to `18 n (L+1)` from the actual
role-split and small-gap scales.  It then calibrates the aggregate clock-depth
first-exit tail at the protocol reset `50(L+1)` and scale `s = 1/3`.

The final assembly uses one far-mass tail and one first-exit tail.  There is no
sum over time prefixes.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiWork
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1JointStopped

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The sharp eighteen-window horizon -/

/-- The exact scale assumptions give the stronger rational partner-floor
calibration `117 n ≤ 1000 P`, where `P = ⌈(mc-g)/4⌉`. -/
theorem phase1_partnerFloor_strong_linear
    {n g mc : ℕ}
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    117 * n ≤ 1000 * ((mc - g + 3) / 4) := by
  have hceil : mc - g ≤ 4 * ((mc - g + 3) / 4) := by omega
  omega

/-- Under the actual Phase-1 role-split and small-gap scales, the sharp far
drift horizon fits in `18 n (L+1)` interactions. -/
theorem phase1_driftHorizon_le_18_of_scales
    {n L g mc : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    Phase1FarPhiWork.horizon n g mc ≤ 18 * n * (L + 1) := by
  rw [Phase1FarPhiWork.horizon, DriftSurvival.driftHorizon, Nat.ceil_le]
  let P : ℕ := (mc - g + 3) / 4
  have hPlinear : 117 * n ≤ 1000 * P := by
    exact phase1_partnerFloor_strong_linear hmain hgap
  have hPpos : 0 < P := by
    dsimp [P]
    omega
  have hPRpos : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hnpos : 0 < n := by omega
  have hPhiNat : 2 * n ≤ 2 ^ (L + 1) := by
    calc
      2 * n ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 hnL
      _ = 2 ^ (L + 1) := by rw [pow_succ']
  have hSecondNat : 2 * n ^ 2 ≤ 2 ^ (2 * L + 1) := by
    calc
      2 * n ^ 2 ≤ 2 * (2 ^ L) ^ 2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hnL 2)
      _ = 2 ^ (2 * L + 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega
  have hlogPhi :
      Real.log ((2 * n : ℕ) : ℝ) ≤ (L + 1 : ℕ) * Real.log 2 := by
    calc
      Real.log ((2 * n : ℕ) : ℝ) ≤
          Real.log ((2 : ℝ) ^ (L + 1)) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hPhiNat
      _ = (L + 1 : ℕ) * Real.log 2 := Real.log_pow 2 (L + 1)
  have hlogSecond :
      Real.log ((2 : ℝ) * n ^ 2) ≤
        (2 * L + 1 : ℕ) * Real.log 2 := by
    calc
      Real.log ((2 : ℝ) * n ^ 2) ≤
          Real.log ((2 : ℝ) ^ (2 * L + 1)) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hSecondNat
      _ = (2 * L + 1 : ℕ) * Real.log 2 :=
        Real.log_pow 2 (2 * L + 1)
  have hlogSum :
      Real.log ((2 * n : ℕ) : ℝ) + Real.log ((2 : ℝ) * n ^ 2)
        ≤ (3 * (L : ℝ) + 2) * Real.log 2 := by
    calc
      Real.log ((2 * n : ℕ) : ℝ) + Real.log ((2 : ℝ) * n ^ 2)
          ≤ (((L + 1 : ℕ) : ℝ) * Real.log 2) +
              (((2 * L + 1 : ℕ) : ℝ) * Real.log 2) :=
            add_le_add hlogPhi hlogSecond
      _ = (3 * (L : ℝ) + 2) * Real.log 2 := by
        push_cast
        ring
  have hlogSum0 :
      0 ≤ Real.log ((2 * n : ℕ) : ℝ) +
        Real.log ((2 : ℝ) * n ^ 2) := by
    apply add_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * n by omega))
    · apply Real.log_nonneg
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hrate :
      (n : ℝ) * ((n : ℝ) - 1) /
          Phase1FarPhiWork.partnerB g mc ≤ (1000 / 117 : ℝ) * n := by
    rw [div_le_iff₀]
    · have hPlinearR : (117 : ℝ) * n ≤ 1000 * P := by
        exact_mod_cast hPlinear
      dsimp [Phase1FarPhiWork.partnerB, P]
      nlinarith
    · simpa [Phase1FarPhiWork.partnerB, P] using hPRpos
  have hlogConstant :
      (1000 / 117 : ℝ) * ((3 * (L : ℝ) + 2) * Real.log 2) ≤
        18 * ((L : ℝ) + 1) := by
    have hfactor : 0 ≤ (1000 / 117 : ℝ) * (3 * (L : ℝ) + 2) := by
      positivity
    have hmul :=
      mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hfactor
    norm_num at hmul ⊢
    nlinarith
  calc
    (n : ℝ) * ((n : ℝ) - 1) /
          Phase1FarPhiWork.partnerB g mc *
          (Real.log ((2 * n : ℕ) : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2))
        ≤ ((1000 / 117 : ℝ) * n) *
          (Real.log ((2 * n : ℕ) : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2)) :=
      mul_le_mul_of_nonneg_right hrate hlogSum0
    _ ≤ ((1000 / 117 : ℝ) * n) *
          ((3 * (L : ℝ) + 2) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hlogSum (by positivity)
    _ ≤ (n : ℝ) * (18 * ((L : ℝ) + 1)) := by
      nlinarith [hlogConstant]
    _ = (18 * n * (L + 1) : ℕ) := by
      push_cast
      ring

/-! ## The single first-exit clock tail -/

/-- A rational certificate for the exponential slack used below. -/
private theorem eight_mul_exp_twelve_le_four_thirds_pow_fifty :
    (8 : ℝ) * Real.exp 12 ≤ (4 / 3 : ℝ) ^ 50 := by
  have he : Real.exp 1 ≤ (11 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hp : Real.exp 1 ^ 12 ≤ (11 / 4 : ℝ) ^ 12 :=
    pow_le_pow_left₀ (by positivity) he 12
  have hexp : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [show (12 : ℝ) = (12 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
  rw [hexp]
  calc
    (8 : ℝ) * Real.exp 1 ^ 12 ≤
        8 * (11 / 4 : ℝ) ^ 12 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (4 / 3 : ℝ) ^ 50 := by norm_num

/-- Real arithmetic core of the Phase-1 clock calibration.  At the
Lean-friendly scale `s = log(4/3)`, the MGF rate is exactly
`1 + 2/(3n)`.  An eighteen-window horizon leaves half of the inverse-square
budget for this one first-exit event. -/
theorem phase1_clock_numerics_real
    (n L H : ℕ) (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hH : H ≤ 18 * n * (L + 1)) :
    (1 + 2 / (3 * (n : ℝ))) ^ H * (n : ℝ) /
        (4 / 3 : ℝ) ^ (50 * (L + 1))
      ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set x : ℝ := 2 / (3 * (n : ℝ)) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hpowExp : (1 + x) ^ H ≤ Real.exp ((H : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by rw [add_comm]; exact Real.add_one_le_exp x) H
  have hHx : (H : ℝ) * x ≤ 12 * (L + 1 : ℕ) := by
    have hHR : (H : ℝ) ≤ 18 * (n : ℝ) * (L + 1 : ℕ) := by
      exact_mod_cast hH
    rw [hx]
    calc
      (H : ℝ) * (2 / (3 * (n : ℝ)))
          ≤ (18 * (n : ℝ) * (L + 1 : ℕ)) *
              (2 / (3 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hHR (by positivity)
      _ = 12 * (L + 1 : ℕ) := by field_simp; ring
  have hrate : (1 + x) ^ H ≤ Real.exp (12 * (L + 1 : ℕ)) :=
    hpowExp.trans (Real.exp_le_exp.mpr hHx)
  have hdenGrowth :
      Real.exp (12 * (L + 1 : ℕ)) * (8 : ℝ) ^ (L + 1) ≤
        (4 / 3 : ℝ) ^ (50 * (L + 1)) := by
    have hp := pow_le_pow_left₀ (by positivity)
      eight_mul_exp_twelve_le_four_thirds_pow_fifty (L + 1)
    calc
      Real.exp (12 * (L + 1 : ℕ)) * (8 : ℝ) ^ (L + 1)
          = ((8 : ℝ) * Real.exp 12) ^ (L + 1) := by
            rw [mul_pow]
            rw [show (12 : ℝ) * (L + 1 : ℕ) =
                ((L + 1 : ℕ) : ℝ) * 12 by ring,
              Real.exp_nat_mul]
            ring
      _ ≤ ((4 / 3 : ℝ) ^ 50) ^ (L + 1) := hp
      _ = (4 / 3 : ℝ) ^ (50 * (L + 1)) := by
        rw [pow_mul]
  have hratio :
      (1 + x) ^ H * (n : ℝ) /
          (4 / 3 : ℝ) ^ (50 * (L + 1))
        ≤ (n : ℝ) / (8 : ℝ) ^ (L + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      (1 + x) ^ H * (n : ℝ) * (8 : ℝ) ^ (L + 1)
          ≤ Real.exp (12 * (L + 1 : ℕ)) * (n : ℝ) *
              (8 : ℝ) ^ (L + 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hrate (by positivity)) (by positivity)
      _ = (n : ℝ) *
            (Real.exp (12 * (L + 1 : ℕ)) * (8 : ℝ) ^ (L + 1)) := by
        ring
      _ ≤ (n : ℝ) * (4 / 3 : ℝ) ^ (50 * (L + 1)) :=
        mul_le_mul_of_nonneg_left hdenGrowth (by positivity)
      _ = (n : ℝ) * (4 / 3 : ℝ) ^ (50 * (L + 1)) := rfl
  have hnLR : (n : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hnL
  have hnCube : (n : ℝ) ^ 3 ≤ ((2 : ℝ) ^ L) ^ 3 :=
    pow_le_pow_left₀ hnpos.le hnLR 3
  have hcubeBudget :
      2 * (n : ℝ) ^ 3 ≤ (8 : ℝ) ^ (L + 1) := by
    calc
      2 * (n : ℝ) ^ 3 ≤ 2 * ((2 : ℝ) ^ L) ^ 3 :=
        mul_le_mul_of_nonneg_left hnCube (by norm_num)
      _ = 2 * (2 : ℝ) ^ (3 * L) := by
        congr 1
        rw [← pow_mul]
        congr 1
        omega
      _ = 2 * (8 : ℝ) ^ L := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      _ ≤ 8 * (8 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (8 : ℝ) ^ (L + 1) := by rw [pow_succ']
  calc
    (1 + 2 / (3 * (n : ℝ))) ^ H * (n : ℝ) /
          (4 / 3 : ℝ) ^ (50 * (L + 1))
        = (1 + x) ^ H * (n : ℝ) /
            (4 / 3 : ℝ) ^ (50 * (L + 1)) := by rw [hx]
    _ ≤ (n : ℝ) / (8 : ℝ) ^ (L + 1) := hratio
    _ ≤ 1 / (2 * (n : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- At `s = log(4/3)`, the abstract aggregate-depth rate is the concrete
`ofReal (1 + 2/(3n))` used by the real numerical lemma. -/
theorem phase1_counterDepthRate_log_four_thirds
    (n : ℕ) (hn : 1 ≤ n) :
    ClockCounterDepthCover.counterDepthRate n (Real.log (4 / 3 : ℝ)) =
      ENNReal.ofReal (1 + 2 / (3 * (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqpos : (0 : ℝ) < 4 / 3 := by norm_num
  have he0 : (0 : ℝ) ≤ Real.exp (Real.log (4 / 3 : ℝ)) - 1 := by
    rw [Real.exp_log hqpos]
    norm_num
  have hofac :
      ENNReal.ofReal
          (1 + 2 * (Real.exp (Real.log (4 / 3 : ℝ)) - 1) / (n : ℝ)) =
        1 + ENNReal.ofReal (Real.exp (Real.log (4 / 3 : ℝ)) - 1) *
          ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]
    congr 1
    rw [show 2 * (Real.exp (Real.log (4 / 3 : ℝ)) - 1) / (n : ℝ) =
        (Real.exp (Real.log (4 / 3 : ℝ)) - 1) * (2 / (n : ℝ)) by ring]
    rw [ENNReal.ofReal_mul he0]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
    norm_num
  unfold ClockCounterDepthCover.counterDepthRate
  rw [show (2 : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log (4 / 3 : ℝ)) - 1) /
          (n : ℝ≥0∞) =
        ENNReal.ofReal (Real.exp (Real.log (4 / 3 : ℝ)) - 1) *
          ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) by
        rw [mul_comm, mul_div_assoc]]
  rw [← hofac, Real.exp_log hqpos]
  congr 1
  field_simp
  ring

/-- The one Phase-1 first-exit clock event consumes at most the second half of
the inverse-square phase budget.  This is the actual protocol reset and does
not sum the endpoint estimate over prefixes. -/
theorem phase1_counterDepthTail_le_half
    (n L H : ℕ) (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hH : H ≤ 18 * n * (L + 1)) :
    ClockCounterDepthCover.counterDepthTail
        n H (50 * (L + 1)) (Real.log (4 / 3 : ℝ))
      ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
  have hqpos : (0 : ℝ) < 4 / 3 := by norm_num
  have hbase0 : (0 : ℝ) ≤ 1 + 2 / (3 * (n : ℝ)) := by positivity
  have hdenpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (50 * (L + 1)) := by positivity
  have hthreshold :
      ClockCounterDepthCover.counterDepthThreshold
          (50 * (L + 1)) (Real.log (4 / 3 : ℝ)) =
        ENNReal.ofReal ((4 / 3 : ℝ) ^ (50 * (L + 1))) := by
    unfold ClockCounterDepthCover.counterDepthThreshold
    rw [show Real.log (4 / 3 : ℝ) * ((50 * (L + 1) : ℕ) : ℝ) =
        ((50 * (L + 1) : ℕ) : ℝ) * Real.log (4 / 3 : ℝ) by ring,
      Real.exp_nat_mul, Real.exp_log hqpos]
  have htail :
      ClockCounterDepthCover.counterDepthTail
          n H (50 * (L + 1)) (Real.log (4 / 3 : ℝ)) =
        ENNReal.ofReal
          ((1 + 2 / (3 * (n : ℝ))) ^ H * (n : ℝ) /
            (4 / 3 : ℝ) ^ (50 * (L + 1))) := by
    unfold ClockCounterDepthCover.counterDepthTail
    rw [phase1_counterDepthRate_log_four_thirds n (by omega), hthreshold,
      ← ENNReal.ofReal_pow hbase0, ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_div_of_pos hdenpos]
  rw [htail, DriftSurvival.coe_driftBudgetNN]
  exact ENNReal.ofReal_le_ofReal
    (phase1_clock_numerics_real n L H hn hnL hH)

/-! ## Closed joint work component -/

/-- The genuine Phase-1 entry surface consumed by the joint stopped proof.
The reset is the literal `phaseInit 1` clock payload. -/
def Phase1JointPre (n g mc : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c ∧
    ∀ a ∈ c, a.role = Role.clock → a.counter.val = 50 * (L + 1)

/-- Complete Phase-1 convergence estimate: the sharp far drain and the single
first-exit clock event together consume at most `n⁻²`. -/
theorem phase1_joint_failure_le_inv_sq
    (n L g mc : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc)
    (c₀ : Config (AgentState L K))
    (hpre : Phase1JointPre (L := L) (K := K) n g mc c₀) :
    ((NonuniformMajority L K).transitionKernel ^
        Phase1FarPhiWork.horizon n g mc) c₀
      {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
      ≤ 1 / (n : ℝ≥0∞) ^ 2 := by
  have hH := phase1_driftHorizon_le_18_of_scales hn hnL hmain hgap
  have hP : 0 < (mc - g + 3) / 4 := by omega
  have hgood : Phase1ClockDepthStopped.Good
      (L := L) (K := K) n g mc c₀ := by
    refine ⟨hpre.1, ?_⟩
    intro a ha hclock
    rw [hpre.2 a ha hclock]
    omega
  have hmainCard :
      RoleSplitConcentration.mainCount (L := L) (K := K) c₀ ≤ c₀.card := by
    unfold RoleSplitConcentration.mainCount
    exact Multiset.countP_le_card _ _
  have hmc : mc ≤ n := by
    have hmcMain := hpre.1.2.2
    have hcard := hpre.1.1.1
    omega
  have hB0 : 0 < Phase1FarPhiWork.partnerB g mc :=
    Phase1FarPhiWork.partnerB_pos hP
  have hBle : Phase1FarPhiWork.partnerB g mc ≤
      (n : ℝ) * ((n : ℝ) - 1) :=
    Phase1FarPhiWork.partnerB_le_scheduler hn hmc
  let r : ℝ≥0∞ := 1 - Phase1FarPhiSharp.farBetaSharp n g mc
  have hdrain :
      r ^ Phase1FarPhiWork.horizon n g mc * ((2 * n : ℕ) : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
    dsimp [r, Phase1FarPhiWork.horizon]
    rw [Phase1FarPhiWork.farBetaSharp_eq_ofReal_partnerB]
    exact DriftSurvival.drift_pow_le_budget_sub hn (by omega) (by omega)
      hB0 hBle
  have hfar :
      r ^ Phase1FarPhiWork.horizon n g mc *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := by
    calc
      r ^ Phase1FarPhiWork.horizon n g mc *
          (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞)
          ≤ r ^ Phase1FarPhiWork.horizon n g mc *
              ((2 * n : ℕ) : ℝ≥0∞) := by
            gcongr
            exact_mod_cast Phase1FarPhiWork.farPhiN_le_two_mul_n c₀ hpre.1
      _ ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) := hdrain
  have hclock :
      ClockCounterDepthCover.counterDepthTail n
          (Phase1FarPhiWork.horizon n g mc) (50 * (L + 1))
          (Real.log (4 / 3 : ℝ))
        ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) :=
    phase1_counterDepthTail_le_half n L
      (Phase1FarPhiWork.horizon n g mc) hn hnL hH
  have hs : (0 : ℝ) ≤ Real.log (4 / 3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hjoint := Phase1JointStopped.real_phase1_joint_failure_le
    (L := L) (K := K)
    n g mc (Phase1FarPhiWork.horizon n g mc) (50 * (L + 1))
    hn (Real.log (4 / 3 : ℝ)) hs c₀ hgood hpre.2
  calc
    ((NonuniformMajority L K).transitionKernel ^
        Phase1FarPhiWork.horizon n g mc) c₀
      {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
        ≤ r ^ Phase1FarPhiWork.horizon n g mc *
            (Phase1FarPhi.farPhiN c₀ : ℝ≥0∞) +
          ClockCounterDepthCover.counterDepthTail n
            (Phase1FarPhiWork.horizon n g mc) (50 * (L + 1))
            (Real.log (4 / 3 : ℝ)) := hjoint
    _ ≤ (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) +
          (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) :=
      add_le_add hfar hclock
    _ = 1 / (n : ℝ≥0∞) ^ 2 := by
      rw [← two_mul]
      exact DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
        (D := 2) (n := n) (by omega) (by omega)

/-- The replacement Phase-1 work component.  Unlike the historical wrapper,
its Pre does not contain a start-dependent prefix-sum hypothesis. -/
noncomputable def phase1JointWork
    (n g mc : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase1JointPre (L := L) (K := K) n g mc
  Post := Phase1FarPhiWork.Post (L := L) (K := K) n g mc
  t := Phase1FarPhiWork.horizon n g mc
  ε := DriftSurvival.driftBudgetNN 2 n +
    DriftSurvival.driftBudgetNN 2 n
  convergence := by
    intro c₀ hpre
    calc
      ((NonuniformMajority L K).transitionKernel ^
          Phase1FarPhiWork.horizon n g mc) c₀
        {c | ¬ Phase1FarPhiWork.Post (L := L) (K := K) n g mc c}
          ≤ 1 / (n : ℝ≥0∞) ^ 2 :=
        phase1_joint_failure_le_inv_sq n L g mc hn hnL hmain hgap c₀ hpre
      _ = ((DriftSurvival.driftBudgetNN 2 n +
            DriftSurvival.driftBudgetNN 2 n : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_add, ← two_mul]
        exact (DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
          (D := 2) (n := n) (by omega) (by omega)).symm

@[simp] theorem phase1JointWork_Post
    (n g mc : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    (phase1JointWork (L := L) (K := K) n g mc hn hnL hmain hgap).Post =
      Phase1FarPhiWork.Post (L := L) (K := K) n g mc := rfl

/-- The new work endpoint feeds the existing reachable Phase-1-to-2 bridge. -/
theorem phase1JointWork_post_to_phase1Drained
    (n g mc : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc)
    (c : Config (AgentState L K))
    (hpost : (phase1JointWork (L := L) (K := K)
      n g mc hn hnL hmain hgap).Post c) :
    Phase1GapFloorEntryClosure.Phase1Drained (L := L) (K := K) n c :=
  Phase1FarPhiWork.post_to_phase1Drained n g mc c hpost

theorem phase1JointWork_t_le_18
    (n g mc : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    (phase1JointWork (L := L) (K := K) n g mc hn hnL hmain hgap).t ≤
      18 * n * (L + 1) :=
  phase1_driftHorizon_le_18_of_scales hn hnL hmain hgap

theorem phase1JointWork_epsilon_le_inv_sq
    (n g mc : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    ((phase1JointWork (L := L) (K := K) n g mc hn hnL hmain hgap).ε : ℝ≥0∞)
      ≤ 1 / (n : ℝ≥0∞) ^ 2 := by
  change ((DriftSurvival.driftBudgetNN 2 n +
      DriftSurvival.driftBudgetNN 2 n : ℝ≥0) : ℝ≥0∞) ≤ _
  rw [ENNReal.coe_add, ← two_mul]
  exact le_of_eq (DriftSurvival.natCast_mul_driftBudgetNN_eq_inv_sq
    (D := 2) (n := n) (by omega) (by omega))

#print axioms phase1_partnerFloor_strong_linear
#print axioms phase1_driftHorizon_le_18_of_scales
#print axioms phase1_clock_numerics_real
#print axioms phase1_counterDepthRate_log_four_thirds
#print axioms phase1_counterDepthTail_le_half
#print axioms phase1_joint_failure_le_inv_sq
#print axioms phase1JointWork
#print axioms phase1JointWork_Post
#print axioms phase1JointWork_post_to_phase1Drained
#print axioms phase1JointWork_t_le_18
#print axioms phase1JointWork_epsilon_le_inv_sq

end Ripple.PopulationProtocol.ExactMajority
