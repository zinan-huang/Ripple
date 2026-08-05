/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase1Assembly

/-!
# Discharging the phase-1 rate interface

`Phase1PhiRateHyp n` has two fields: `progress` (the per-rung Chernoff deadline,
proved unconditionally in `Tri.phase1RungPhi_pow_mul_le`) and `gap_lower` (the
concrete closure of that deadline for the corrected phase-1 rungs).  This file
discharges both fields and assembles the unconditional theorem.  For
`progress`, the empty-band case (`upper ≤ lower + 1`) has no live state, so
`phase1RungPhi = 0` and the bound is immediate (or, at `T = 0`, the potential
factor alone via `base_pow_ratio_le_ofReal_exp`).
-/

namespace Tri

open scoped ENNReal

set_option exponentiation.threshold 500

/-- The `progress` field of `Phase1PhiRateHyp`, proved unconditionally: on a live
band it is `phase1RungPhi_pow_mul_le`; on an empty band `phase1RungPhi = 0`. -/
theorem phase1_progress_field (n : ℕ)
    (lower bLo upper start T : ℕ) (E : ℝ)
    (h3 : 3 ≤ n) (hpop : lower + bLo + 2 = n) (hlower : 0 < lower)
    (hbias : bLo < lower) (hupper : upper ≤ n) (hstart : lower ≤ start)
    (hstartUp : start ≤ upper)
    (hdeadline : E ≤ phase1PhiGap n lower bLo upper * (T : ℝ) -
        ((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))) :
    phase1RungPhi n lower bLo upper ^ T *
          phase1RungBase lower bLo ^ start /
          phase1RungBase lower bLo ^ upper ≤
      ENNReal.ofReal (Real.exp (-E)) := by
  by_cases hband : lower + 1 < upper
  · exact phase1RungPhi_pow_mul_le n lower bLo upper start T h3 hpop hlower hbias
      hupper hstart hstartUp hband E hdeadline
  · -- Empty band: no live state, so `phase1RungMax = 0`, hence `phase1RungPhi = 0`.
    have hbase := phase1RungBase_spec hlower hbias
    have hbaseTop : phase1RungBase lower bLo ≠ ⊤ :=
      ne_top_of_lt (hbase.2.1.trans_le le_top)
    have hwm : ∀ a b : ℕ, phase1RungWeightedMass n lower bLo upper a b = 0 := by
      intro a b; unfold phase1RungWeightedMass
      rw [dif_neg (by rintro ⟨-, -, hlo, hhi⟩; omega)]
    have hmax0 : phase1RungMax n lower bLo upper = 0 := by
      unfold phase1RungMax
      apply le_antisymm _ bot_le
      apply Finset.sup_le; intro a _
      apply Finset.sup_le; intro b _
      exact (hwm a b).le
    have hphi0 : phase1RungPhi n lower bLo upper = 0 := by
      unfold phase1RungPhi; rw [hmax0, ENNReal.zero_div]
    rw [hphi0]
    rcases Nat.eq_zero_or_pos T with hT | hT
    · -- `T = 0`: the potential factor alone, bounded by the deadline.
      subst hT
      simp only [pow_zero, one_mul]
      rw [phase1RungBase]
      have hpq : lower + bLo ≤ 2 * lower := by omega
      have hp0 : 0 < lower + bLo := by omega
      refine (base_pow_ratio_le_ofReal_exp (lower + bLo) (2 * lower) start upper hp0 hpq
        hstartUp).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
      have hd : E ≤ -(((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * (lower : ℝ)) / ((lower : ℝ) + (bLo : ℝ)))) := by
        have h0 := hdeadline
        rw [Nat.cast_zero, mul_zero, zero_sub] at h0
        exact h0
      have hcast : (((2 * lower : ℕ) : ℝ)) / (((lower + bLo : ℕ) : ℝ)) =
          (2 * (lower : ℝ)) / ((lower : ℝ) + (bLo : ℝ)) := by push_cast; ring
      rw [hcast]
      linarith [hd]
    · -- `T ≥ 1`: `0 ^ T = 0 ≤ anything`.
      simp [zero_pow (show T ≠ 0 by omega)]

set_option maxHeartbeats 2000000 in
-- The two-piece midpoint estimate requires a large nonlinear arithmetic context.
/-- The concrete corrected-rung gap clears the phase-1 deadline rate. -/
theorem phase1_gap_lower_field (n γ j : ℕ) (hn : 2 ^ 420 ≤ n)
    (hγ : 1 ≤ γ) (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hmove : phase1CheckpointR n γ j < phase1CheckpointR n γ (j + 1)) :
    ((phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)) +
        ((phase1CorrUpper n γ j : ℝ) -
          (phase1CheckpointR n γ j : ℝ)) *
          Real.log ((2 * phase1LowerR n γ j : ℝ) /
            (phase1LowerR n γ j + phase1LowerMinorityR n γ j : ℝ))) /
      (24 * (n : ℝ)) ≤
      phase1PhiGap n (phase1LowerR n γ j)
        (phase1LowerMinorityR n γ j) (phase1CorrUpper n γ j) := by
  let gap := phase1GapR n γ j
  let k := phase1FellerK n γ j
  let r := phase1CorrUpperBuffer n γ j
  let current := phase1CheckpointR n γ j
  let next := phase1CheckpointR n γ (j + 1)
  let lower := phase1LowerR n γ j
  let bLo := phase1LowerMinorityR n γ j
  let upper := phase1CorrUpper n γ j
  let returnLo := phase1ReturnLoR n γ j
  let bReturn := phase1ReturnMinorityR n γ j
  let M := phase1PhiMid lower upper
  have D : Phase1CorrRungData n gap k r current next lower bLo upper
      returnLo bReturn := by
    simpa only [gap, k, r, current, next, lower, bLo, upper, returnLo, bReturn]
      using phase1_corr_rung_data n γ j hn hγ hsize hmove
  have hn512 : 512 ≤ n := by
    exact hn.trans' (le_trans (by norm_num : 512 ≤ 2 ^ 9)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 9 ≤ 420)))
  have hnR : (0 : ℝ) < n := by exact_mod_cast D.hnPos
  have hn512R : (512 : ℝ) ≤ n := by exact_mod_cast hn512
  have hkR : (0 : ℝ) < k := by exact_mod_cast D.hkPos
  have hlowerR : (0 : ℝ) < lower := by exact_mod_cast D.hlowerPos
  have hgapKR : (gap : ℝ) ≤ 5 * k := by exact_mod_cast D.hgapK
  have hpopR : (lower : ℝ) + bLo + 2 = n := by
    exact_mod_cast D.hpopLower
  have hdiffLoR : (bLo : ℝ) + 2 * k ≤ lower := by
    exact_mod_cast D.hlowerDiffLo
  have hdiffHiR : (10 : ℝ) * lower ≤ 10 * bLo + 21 * k := by
    exact_mod_cast D.hlowerDiffHi
  have hdenomR : (99 : ℝ) * n ≤
      100 * ((lower : ℝ) + bLo) := by
    exact_mod_cast D.hdenom
  have hstartR : (lower : ℝ) + k = current := by
    exact_mod_cast D.hstart
  have hupperDistR : (10 : ℝ) * upper ≤
      10 * current + 31 * k := by
    exact_mod_cast D.hupperDist
  have hlowerNR : (lower : ℝ) ≤ n := by exact_mod_cast D.hlowerN
  have hbiasR : (bLo : ℝ) ≤ lower := by exact_mod_cast D.hbias.le
  have hd0 : (0 : ℝ) ≤ (lower : ℝ) - bLo := by
    linarith
  have hd2k : (2 : ℝ) * k ≤ (lower : ℝ) - bLo := by linarith
  have hd21 : (lower : ℝ) - bLo ≤ 21 / 10 * k := by linarith
  have hcurrentUpper : current ≤ upper := D.hadvance.trans D.hnextUpper
  have hcurrentUpperR : (current : ℝ) ≤ upper := by
    exact_mod_cast hcurrentUpper
  have hdist0 : (0 : ℝ) ≤ (upper : ℝ) - current := by
    linarith
  have hdist : (upper : ℝ) - current ≤ 31 / 10 * k := by
    linarith
  have hsumPos : (0 : ℝ) < (lower : ℝ) + bLo := by positivity
  have hratioOne : (1 : ℝ) ≤
      (2 * lower : ℝ) / ((lower : ℝ) + bLo) := by
    rw [le_div_iff₀ hsumPos]
    linarith
  have hlogNonneg : 0 ≤
      Real.log ((2 * lower : ℝ) / ((lower : ℝ) + bLo)) :=
    Real.log_nonneg hratioOne
  have hlogUpper :
      Real.log ((2 * lower : ℝ) / ((lower : ℝ) + bLo)) ≤
        ((lower : ℝ) - bLo) / ((lower : ℝ) + bLo) := by
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (2 * lower : ℝ) /
        ((lower : ℝ) + bLo) by positivity)
    have heq : (2 * lower : ℝ) / ((lower : ℝ) + bLo) - 1 =
        ((lower : ℝ) - bLo) / ((lower : ℝ) + bLo) := by
      field_simp
      ring
    rwa [heq] at hlog
  have hdistDrift : ((upper : ℝ) - current) *
      ((lower : ℝ) - bLo) ≤
        (31 / 10 * k) * (21 / 10 * k) :=
    mul_le_mul hdist hd21 hd0 (by positivity)
  have hscaledDist : 100 * ((upper : ℝ) - current) *
      ((lower : ℝ) - bLo) ≤ 651 * k ^ 2 := by
    nlinarith
  have hscaledDistN := mul_le_mul_of_nonneg_left hscaledDist
    (show (0 : ℝ) ≤ 33 * n by positivity)
  have hscaledDenom := mul_le_mul_of_nonneg_right hdenomR
    (show (0 : ℝ) ≤ 217 * k ^ 2 by positivity)
  have hdistCross : 33 * n * ((upper : ℝ) - current) *
      ((lower : ℝ) - bLo) ≤
        217 * k ^ 2 * ((lower : ℝ) + bLo) := by
    nlinarith
  have hpotentialRatio : ((upper : ℝ) - current) *
      (((lower : ℝ) - bLo) / ((lower : ℝ) + bLo)) ≤
        (217 / 33 : ℝ) * k ^ 2 / n := by
    rw [show ((upper : ℝ) - current) *
        (((lower : ℝ) - bLo) / ((lower : ℝ) + bLo)) =
      (((upper : ℝ) - current) * ((lower : ℝ) - bLo)) /
        ((lower : ℝ) + bLo) by ring]
    rw [div_le_div_iff₀ hsumPos hnR]
    nlinarith
  have hpotential : ((upper : ℝ) - current) *
      Real.log ((2 * lower : ℝ) / ((lower : ℝ) + bLo)) ≤
        (217 / 33 : ℝ) * k ^ 2 / n :=
    (mul_le_mul_of_nonneg_left hlogUpper hdist0).trans hpotentialRatio
  have hgapSqUpper : (gap : ℝ) ^ 2 ≤ 25 * (k : ℝ) ^ 2 := by
    nlinarith
  have hgaussian : (gap : ℝ) ^ 2 / (48 * (n : ℝ)) ≤
      25 * (k : ℝ) ^ 2 / (48 * (n : ℝ)) := by
    exact div_le_div_of_nonneg_right hgapSqUpper (by positivity)
  have hnumUpper : (gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
      ((upper : ℝ) - current) *
        Real.log ((2 * lower : ℝ) / ((lower : ℝ) + bLo)) ≤
        (36 / 5 : ℝ) * k ^ 2 / n := by
    calc
      _ ≤ 25 * (k : ℝ) ^ 2 / (48 * (n : ℝ)) +
          (217 / 33 : ℝ) * k ^ 2 / n := add_le_add hgaussian hpotential
      _ ≤ (36 / 5 : ℝ) * k ^ 2 / n := by
        field_simp [hnR.ne']
        nlinarith [sq_nonneg (k : ℝ)]
  have hrateUpper : ((gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
      ((upper : ℝ) - current) *
        Real.log ((2 * lower : ℝ) / ((lower : ℝ) + bLo))) /
        (24 * (n : ℝ)) ≤
      (3 / 10 : ℝ) * k ^ 2 / n ^ 2 := by
    calc
      _ ≤ ((36 / 5 : ℝ) * k ^ 2 / n) / (24 * n) :=
        div_le_div_of_nonneg_right hnumUpper (by positivity)
      _ = (3 / 10 : ℝ) * k ^ 2 / n ^ 2 := by
        field_simp [hnR.ne']
        ring
  have hband : lower + 1 < upper := by
    have := D.hstart
    have := D.hkPos
    have := D.hadvance
    have := D.hnextUpper
    omega
  have hMge : lower + 1 ≤ M := by
    dsimp [M, phase1PhiMid]
    omega
  have hMle : M ≤ upper - 1 := by
    dsimp [M, phase1PhiMid]
    omega
  have hnLowerSucc : n ≤ 2 * (lower + 1) := by
    have := D.hpopLower
    have := D.hbias
    omega
  have hMhalf : n ≤ 2 * M := by omega
  have hMseven : 8 * M ≤ 7 * n + 8 := by
    calc
      8 * M ≤ 8 * (upper - 1) := Nat.mul_le_mul_left 8 hMle
      _ ≤ 8 * upper := Nat.mul_le_mul_left 8 (Nat.sub_le upper 1)
      _ ≤ 7 * n + 8 := D.hupperSeven
  have hTopHalf : n ≤ 2 * (upper - 1) := by omega
  have hTopSeven : 8 * (upper - 1) ≤ 7 * n + 8 :=
    (Nat.mul_le_mul_left 8 (Nat.sub_le upper 1)).trans D.hupperSeven
  have hXYLower : ∀ x : ℕ, n ≤ 2 * x → 8 * x ≤ 7 * n + 8 →
      (13 / 128 : ℝ) * (n : ℝ) ^ 2 ≤ phase1PhiXY n x := by
    intro x hhalf hseven
    have hhalfR : (n : ℝ) ≤ 2 * x := by exact_mod_cast hhalf
    have hsevenR : (8 : ℝ) * x ≤ 7 * n + 8 := by exact_mod_cast hseven
    have hproduct : 0 ≤
        (7 * (n : ℝ) + 8 - 8 * x) * (8 * (x : ℝ) - n) :=
      mul_nonneg (by linarith) (by linarith)
    have hnLarge : 96 * (n : ℝ) + 128 ≤ (n : ℝ) ^ 2 := by
      have hproductN : 0 ≤ ((n : ℝ) - 512) * n :=
        mul_nonneg (by linarith) hnR.le
      nlinarith
    unfold phase1PhiXY
    nlinarith
  have hXYM := hXYLower M hMhalf hMseven
  have hXYTop := hXYLower (upper - 1) hTopHalf hTopSeven
  let w : ℝ := ((lower : ℝ) + bLo) / (2 * lower)
  have hw0 : (0 : ℝ) ≤ w := by dsimp [w]; positivity
  have hDriftLow : phase1PhiDrift n lower bLo (lower + 1) =
      ((lower : ℝ) - bLo) / 2 := by
    unfold phase1PhiDrift
    rw [show ((lower : ℝ) + bLo) / (2 * lower) = w by rfl]
    push_cast
    dsimp [w]
    field_simp
    nlinarith
  have hDriftM : phase1PhiDrift n lower bLo M =
      ((lower : ℝ) - bLo) / 2 +
        ((M : ℝ) - ((lower : ℝ) + 1)) * (w + 1) := by
    rw [← hDriftLow]
    unfold phase1PhiDrift
    rw [show ((lower : ℝ) + bLo) / (2 * lower) = w by rfl]
    push_cast
    ring
  have hMgeR : (lower : ℝ) + 1 ≤ M := by exact_mod_cast hMge
  have hDriftLowK : (k : ℝ) ≤
      phase1PhiDrift n lower bLo (lower + 1) := by
    rw [hDriftLow]
    linarith
  have hDriftMK : (k : ℝ) ≤ phase1PhiDrift n lower bLo M := by
    rw [hDriftM]
    have hgrowth : 0 ≤
        ((M : ℝ) - ((lower : ℝ) + 1)) * (w + 1) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  let pieceLower : ℝ := (13 / 128 : ℝ) * (n : ℝ) ^ 2 * k
  have hXYM0 : (0 : ℝ) ≤ phase1PhiXY n M :=
    (show (0 : ℝ) ≤ 13 / 128 * (n : ℝ) ^ 2 by positivity).trans hXYM
  have hXYTop0 : (0 : ℝ) ≤ phase1PhiXY n (upper - 1) :=
    (show (0 : ℝ) ≤ 13 / 128 * (n : ℝ) ^ 2 by positivity).trans hXYTop
  have hp1Lower : pieceLower ≤ phase1PhiPiece1 n lower bLo upper := by
    change pieceLower ≤ phase1PhiXY n M *
      phase1PhiDrift n lower bLo (lower + 1)
    dsimp [pieceLower]
    exact mul_le_mul hXYM hDriftLowK (by positivity) hXYM0
  have hp2Lower : pieceLower ≤ phase1PhiPiece2 n lower bLo upper := by
    change pieceLower ≤ phase1PhiXY n (upper - 1) *
      phase1PhiDrift n lower bLo M
    dsimp [pieceLower]
    exact mul_le_mul hXYTop hDriftMK (by positivity) hXYTop0
  have hminLower : pieceLower ≤
      min (phase1PhiPiece1 n lower bLo upper)
        (phase1PhiPiece2 n lower bLo upper) := le_min hp1Lower hp2Lower
  let f : ℝ := ((lower : ℝ) - bLo) / (2 * lower)
  have hf0 : (0 : ℝ) ≤ f := by dsimp [f]; positivity
  have hfLower : (k : ℝ) / n ≤ f := by
    dsimp [f]
    rw [div_le_div_iff₀ hnR (by positivity : (0 : ℝ) < 2 * lower)]
    have hleft := mul_le_mul_of_nonneg_right hd2k
      (show (0 : ℝ) ≤ lower by positivity)
    have hright := mul_le_mul_of_nonneg_left hlowerNR hd0
    nlinarith
  have hgapNumerator : (13 / 128 : ℝ) * n * k ^ 2 ≤
      f * min (phase1PhiPiece1 n lower bLo upper)
        (phase1PhiPiece2 n lower bLo upper) := by
    have hmul := mul_le_mul hfLower hminLower (by positivity) hf0
    calc
      (13 / 128 : ℝ) * n * k ^ 2 = (k / n) * pieceLower := by
        dsimp [pieceLower]
        field_simp [hnR.ne']
      _ ≤ f * min (phase1PhiPiece1 n lower bLo upper)
          (phase1PhiPiece2 n lower bLo upper) := hmul
  have h6c : (6 : ℝ) * (Nat.choose n 3 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    have hnat := six_mul_choose_three_add_two (lower + bLo)
    rw [show lower + bLo + 2 = n from D.hpopLower] at hnat
    have hcast : (6 : ℝ) * (Nat.choose n 3 : ℝ) =
        (n : ℝ) * ((lower : ℝ) + bLo + 1) *
          ((lower : ℝ) + bLo) := by
      exact_mod_cast hnat
    rw [hcast]
    have hsum : (lower : ℝ) + bLo = n - 2 := by linarith
    rw [hsum]
    ring
  have hcPos : (0 : ℝ) < (Nat.choose n 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos D.h3
  have hfalling : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ≤
      (n : ℝ) ^ 3 := by
    have hprod : 0 ≤ (n : ℝ) * (3 * (n : ℝ) - 2) :=
      mul_nonneg hnR.le (by linarith)
    nlinarith
  have hchooseUpper : 2 * (Nat.choose n 3 : ℝ) ≤ (n : ℝ) ^ 3 / 3 := by
    nlinarith
  have hphiLower : (39 / 128 : ℝ) * k ^ 2 / n ^ 2 ≤
      phase1PhiGap n lower bLo upper := by
    unfold phase1PhiGap
    change (39 / 128 : ℝ) * k ^ 2 / n ^ 2 ≤
      f * min (phase1PhiPiece1 n lower bLo upper)
        (phase1PhiPiece2 n lower bLo upper) /
          (2 * (Nat.choose n 3 : ℝ))
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Nat.choose n 3)]
    calc
      (39 / 128 : ℝ) * k ^ 2 / n ^ 2 *
          (2 * (Nat.choose n 3 : ℝ)) ≤
          (39 / 128 : ℝ) * k ^ 2 / n ^ 2 * (n ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hchooseUpper (by positivity)
      _ = (13 / 128 : ℝ) * n * k ^ 2 := by
        field_simp [hnR.ne']
        ring
      _ ≤ f * min (phase1PhiPiece1 n lower bLo upper)
          (phase1PhiPiece2 n lower bLo upper) := hgapNumerator
  have hrateToGap : ((gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
      ((upper : ℝ) - current) *
        Real.log ((2 * lower : ℝ) / ((lower : ℝ) + bLo))) /
        (24 * (n : ℝ)) ≤ phase1PhiGap n lower bLo upper := by
    calc
      _ ≤ (3 / 10 : ℝ) * k ^ 2 / n ^ 2 := hrateUpper
      _ ≤ (39 / 128 : ℝ) * k ^ 2 / n ^ 2 := by
        have hkSq : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
        have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (3 / 10 : ℝ) ≤ 39 / 128)
            hkSq) hnSq
      _ ≤ phase1PhiGap n lower bLo upper := hphiLower
  simpa only [gap, current, lower, bLo, upper] using hrateToGap

/-- The fully unconditional phase-one interface closes the reconciled theorem. -/
theorem theorem1b : Theorem1b_statement :=
  theorem1b_of_phi fun n =>
    ⟨phase1_progress_field n, fun γ j => phase1_gap_lower_field n γ j⟩

end Tri

#print axioms Tri.phase1_progress_field
#print axioms Tri.phase1_gap_lower_field
#print axioms Tri.theorem1b
