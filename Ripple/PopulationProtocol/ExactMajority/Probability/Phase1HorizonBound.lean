/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Explicit sharp Phase-1 drift horizon

The four-orientation drift rate uses the full partner floor
`P = (mc - g + 3) / 4`.  When `n ≤ 9P`, its calibrated half-budget horizon
fits in `19 n (L+1)` interactions.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiWork
import Ripple.PopulationProtocol.ExactMajority.Probability.PaperRegime

namespace Ripple.PopulationProtocol.ExactMajority

/-- The paper-scale role split and small-gap inequalities imply the nine-to-one
partner-floor calibration.  The `+3` in the floor is exactly ceiling division
by four. -/
theorem phase1_partnerFloor_linear
    {n g mc : ℕ}
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    n ≤ 9 * ((mc - g + 3) / 4) := by
  have hceil : mc - g ≤ 4 * ((mc - g + 3) / 4) := by omega
  have hratio : 4 * n ≤ 9 * (mc - g) := by omega
  omega

/-- The sharp `12n/25` natural Main floor extracted from `RoleSplitGood` at
slack at most `1/25`. -/
theorem twelve_mul_n_le_twentyfive_mul_mainCount_of_roleSplitGood
    {η : ℝ} (hη : η ≤ 1 / 25)
    {n : ℕ} {c : Config (AgentState L K)}
    (hgood : RoleSplitConcentration.RoleSplitGood
      (L := L) (K := K) η n c) :
    12 * n ≤ 25 * RoleSplitConcentration.mainCount
      (L := L) (K := K) c := by
  have hmain := hgood.2.1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hηnonneg : 0 ≤ 1 / 25 - η := by linarith
  have hreal :
      (12 : ℝ) * n ≤
        25 * RoleSplitConcentration.mainCount (L := L) (K := K) c := by
    nlinarith [mul_nonneg hηnonneg hn0]
  exact_mod_cast hreal

/-- The sharp Phase-1 far-mass horizon fits the clock-compatible display bound
under a nine-to-one linear partner-floor calibration. -/
theorem phase1_driftHorizon_le_19
    {n L g mc : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hPlinear : n ≤ 9 * ((mc - g + 3) / 4)) :
    Phase1FarPhiWork.horizon n g mc ≤ 19 * n * (L + 1) := by
  rw [Phase1FarPhiWork.horizon, DriftSurvival.driftHorizon, Nat.ceil_le]
  let P : ℕ := (mc - g + 3) / 4
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
          Phase1FarPhiWork.partnerB g mc ≤ 9 * n := by
    rw [div_le_iff₀]
    · have hPlinearR : (n : ℝ) ≤ 9 * P := by
        exact_mod_cast hPlinear
      dsimp [Phase1FarPhiWork.partnerB, P]
      nlinarith
    · simpa [Phase1FarPhiWork.partnerB, P] using hPRpos
  have hlogConstant :
      9 * ((3 * (L : ℝ) + 2) * Real.log 2) ≤
        19 * ((L : ℝ) + 1) := by
    have hfactor : 0 ≤ 9 * (3 * (L : ℝ) + 2) := by positivity
    have hmul :=
      mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hfactor
    norm_num at hmul ⊢
    nlinarith
  calc
    (n : ℝ) * ((n : ℝ) - 1) /
          Phase1FarPhiWork.partnerB g mc *
          (Real.log ((2 * n : ℕ) : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2))
        ≤ (9 * n) *
          (Real.log ((2 * n : ℕ) : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2)) :=
      mul_le_mul_of_nonneg_right hrate hlogSum0
    _ ≤ (9 * n) * ((3 * (L : ℝ) + 2) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hlogSum (by positivity)
    _ ≤ (n : ℝ) * (19 * ((L : ℝ) + 1)) := by
      nlinarith [hlogConstant]
    _ = (19 * n * (L + 1) : ℕ) := by
      push_cast
      ring

/-- Horizon wrapper using the natural-number forms of the role-split and
small-gap scales directly. -/
theorem phase1_driftHorizon_le_19_of_scales
    {n L g mc : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hmain : 12 * n ≤ 25 * mc)
    (hgap : 40 * g ≤ mc) :
    Phase1FarPhiWork.horizon n g mc ≤ 19 * n * (L + 1) :=
  phase1_driftHorizon_le_19 hn hnL
    (phase1_partnerFloor_linear hmain hgap)

/-- Role-split specialization with `mc` instantiated by the actual conserved
Main count and the small-gap branch supplied as `40g ≤ mc`. -/
theorem phase1_driftHorizon_le_19_of_roleSplitGood
    {η : ℝ} (hη : η ≤ 1 / 25)
    {n L g : ℕ} {c : Config (AgentState L K)}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L)
    (hgood : RoleSplitConcentration.RoleSplitGood
      (L := L) (K := K) η n c)
    (hgap : 40 * g ≤
      RoleSplitConcentration.mainCount (L := L) (K := K) c) :
    Phase1FarPhiWork.horizon n g
        (RoleSplitConcentration.mainCount (L := L) (K := K) c)
      ≤ 19 * n * (L + 1) :=
  phase1_driftHorizon_le_19_of_scales hn hnL
    (twelve_mul_n_le_twentyfive_mul_mainCount_of_roleSplitGood hη hgood)
    hgap

/-- Paper-regime specialization: `L = clog₂ n` supplies `n ≤ 2^L`. -/
theorem phase1_driftHorizon_le_19_of_regime
    {n L K g mc : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (hPlinear : n ≤ 9 * ((mc - g + 3) / 4)) :
    Phase1FarPhiWork.horizon n g mc ≤ 19 * n * (L + 1) := by
  apply phase1_driftHorizon_le_19 hReg.two_le_n _ hPlinear
  rw [hReg.hLlog]
  exact Nat.le_pow_clog (by norm_num) n

#print axioms phase1_driftHorizon_le_19
#print axioms phase1_partnerFloor_linear
#print axioms twelve_mul_n_le_twentyfive_mul_mainCount_of_roleSplitGood
#print axioms phase1_driftHorizon_le_19_of_scales
#print axioms phase1_driftHorizon_le_19_of_roleSplitGood
#print axioms phase1_driftHorizon_le_19_of_regime

end Ripple.PopulationProtocol.ExactMajority
