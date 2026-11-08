/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Explicit Phase-7 multiplicative-drift horizon

This file converts the analytic horizon for one exact-band Phase-7 stage into
an explicit `O(n (L+1))` interaction bound.  The eliminator floor
`n ≤ 4 E7` makes the ordered-pair prefactor at most `2n`; the two logarithmic
terms contribute at most `3(L+1) log 2`.  Thus one stage costs at most
`5 n (L+1)` interactions, and the naturally truncated family of at most three
stages costs at most `15 n (L+1)`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon
import Ripple.PopulationProtocol.ExactMajority.Probability.PaperRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandStages

namespace Ripple.PopulationProtocol.ExactMajority

/-- One exact-band Phase-7 drift stage fits in `5 n (L+1)` interactions when
the eliminator pool has the paper-scale floor `n ≤ 4 E7`. -/
theorem phase7_driftHorizon_le_5
    {n L E7 : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L) (hE7linear : n ≤ 4 * E7) :
    DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 ≤
      5 * n * (L + 1) := by
  rw [DriftSurvival.driftHorizon, Nat.ceil_le]
  have hE7pos : 0 < E7 := by omega
  have hBpos : (0 : ℝ) < ((2 * E7 : ℕ) : ℝ) := by
    positivity
  have hnpos : 0 < n := by omega
  have hlogN :
      Real.log (n : ℝ) ≤ (L : ℕ) * Real.log 2 := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ L) := by
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast hnL
      _ = (L : ℕ) * Real.log 2 := Real.log_pow 2 L
  have hSixNat : 6 * n ^ 2 ≤ 2 ^ (2 * L + 3) := by
    calc
      6 * n ^ 2 ≤ 8 * (2 ^ L) ^ 2 :=
        Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hnL 2)
      _ = 2 ^ (2 * L + 3) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
        congr 1
        omega
  have hlogSix :
      Real.log ((6 : ℝ) * n ^ 2) ≤ (2 * L + 3 : ℕ) * Real.log 2 := by
    calc
      Real.log ((6 : ℝ) * n ^ 2) ≤ Real.log ((2 : ℝ) ^ (2 * L + 3)) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hSixNat
      _ = (2 * L + 3 : ℕ) * Real.log 2 := Real.log_pow 2 (2 * L + 3)
  have hlogSum :
      Real.log (n : ℝ) + Real.log ((6 : ℝ) * n ^ 2) ≤
        (3 * (L : ℝ) + 3) * Real.log 2 := by
    calc
      Real.log (n : ℝ) + Real.log ((6 : ℝ) * n ^ 2) ≤
          ((L : ℕ) : ℝ) * Real.log 2 +
            ((2 * L + 3 : ℕ) : ℝ) * Real.log 2 :=
        add_le_add hlogN hlogSix
      _ = (3 * (L : ℝ) + 3) * Real.log 2 := by
        push_cast
        ring
  have hlogSum0 :
      0 ≤ Real.log (n : ℝ) + Real.log ((6 : ℝ) * n ^ 2) := by
    apply add_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    · apply Real.log_nonneg
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hrate :
      (n : ℝ) * ((n : ℝ) - 1) / ((2 * E7 : ℕ) : ℝ) ≤ 2 * n := by
    rw [div_le_iff₀ hBpos]
    have hE7linearR : (n : ℝ) ≤ 4 * E7 := by
      exact_mod_cast hE7linear
    norm_num at hE7linearR ⊢
    nlinarith
  have hlogConstant :
      2 * ((3 * (L : ℝ) + 3) * Real.log 2) ≤
        5 * ((L : ℝ) + 1) := by
    have hfactor : 0 ≤ 6 * ((L : ℝ) + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hfactor
    norm_num at hmul ⊢
    nlinarith
  calc
    (n : ℝ) * ((n : ℝ) - 1) / ((2 * E7 : ℕ) : ℝ) *
          (Real.log (n : ℝ) + Real.log ((6 : ℝ) * n ^ 2))
        ≤ (2 * n) *
          (Real.log (n : ℝ) + Real.log ((6 : ℝ) * n ^ 2)) :=
      mul_le_mul_of_nonneg_right hrate hlogSum0
    _ ≤ (2 * n) * ((3 * (L : ℝ) + 3) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hlogSum (by positivity)
    _ ≤ (n : ℝ) * (5 * ((L : ℝ) + 1)) := by
      nlinarith [hlogConstant]
    _ = (5 * n * (L + 1) : ℕ) := by
      push_cast
      ring

/-- Any family of at most three identical Phase-7 band stages has total
horizon at most `15 n (L+1)`. -/
theorem phase7_stageCount_driftHorizon_le_15
    {n L E7 stageCount : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L) (hE7linear : n ≤ 4 * E7)
    (hstageCount : stageCount ≤ 3) :
    stageCount * DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 ≤
      15 * n * (L + 1) := by
  calc
    stageCount * DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 ≤
        3 * DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 :=
      Nat.mul_le_mul_right _ hstageCount
    _ ≤ 3 * (5 * n * (L + 1)) :=
      Nat.mul_le_mul_left 3 (phase7_driftHorizon_le_5 hn hnL hE7linear)
    _ = 15 * n * (L + 1) := by ring

/-- The naturally truncated band family has at most the paper's three stages,
so its total drift horizon fits in `15 n (L+1)` interactions. -/
theorem phase7_allStages_driftHorizon_le_15
    {n L E7 : ℕ} (l : ℕ)
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L) (hE7linear : n ≤ 4 * E7) :
    Phase7BandStages.phase7StageCount L l *
        DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 ≤
      15 * n * (L + 1) :=
  phase7_stageCount_driftHorizon_le_15 hn hnL hE7linear
    (Phase7BandStages.phase7StageCount_le_three L l)

/-- Paper-regime specialization of the one-stage horizon bound. -/
theorem phase7_driftHorizon_le_5_of_regime
    {n L K E7 : ℕ}
    (hReg : PaperRegime.Regime n L K) (hE7linear : n ≤ 4 * E7) :
    DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 ≤
      5 * n * (L + 1) := by
  apply phase7_driftHorizon_le_5 hReg.two_le_n _ hE7linear
  rw [hReg.hLlog]
  exact Nat.le_pow_clog (by norm_num) n

/-- Paper-regime specialization of the naturally truncated three-stage total. -/
theorem phase7_allStages_driftHorizon_le_15_of_regime
    {n L K E7 : ℕ} (l : ℕ)
    (hReg : PaperRegime.Regime n L K) (hE7linear : n ≤ 4 * E7) :
    Phase7BandStages.phase7StageCount L l *
        DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 ≤
      15 * n * (L + 1) := by
  apply phase7_allStages_driftHorizon_le_15 l hReg.two_le_n _ hE7linear
  rw [hReg.hLlog]
  exact Nat.le_pow_clog (by norm_num) n

#print axioms phase7_driftHorizon_le_5
#print axioms phase7_stageCount_driftHorizon_le_15
#print axioms phase7_allStages_driftHorizon_le_15
#print axioms phase7_driftHorizon_le_5_of_regime
#print axioms phase7_allStages_driftHorizon_le_15_of_regime

end Ripple.PopulationProtocol.ExactMajority
