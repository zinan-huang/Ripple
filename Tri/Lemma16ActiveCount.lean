/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16Exponent
import Tri.InfectionActiveConstants
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Lemma 16's all-active-interaction error

Before the first active-population checkpoint, every all-active raw
interaction has conditional probability at most `(a / n)³`.  This file
specializes the existing adapted counter bound at tilt `4/3`, converts the
strict paper threshold exactly, and proves the explicit error
`exp (-(cStar * rho) / 27)`.

The scalar estimate first obtains the slightly stronger denominator `20`.
No independence or binomial-law identification is used.
-/

namespace Tri

open scoped ENNReal

/-- The least integer counter value satisfying the paper's strict event. -/
theorem lemma16_strict_counter_threshold (m C : ℕ) :
    4 * m < 3 * C ↔ 4 * m / 3 + 1 ≤ C := by
  omega

/-- Convert Lemma 16's cross-multiplied mean hypothesis to the cubic ENNReal
budget consumed by the adapted counter theorem. -/
theorem lemma16_cube_mean_le
    (n a q rho cStar : ℕ)
    (h3 : 3 ≤ n)
    (hmean : q * a ^ 3 ≤ rho * n ^ 2) :
    (((cStar * q * n : ℕ) : ℝ≥0∞) *
        (((a : ℝ≥0∞) / (n : ℝ≥0∞)) ^ 3)) ≤
      ((cStar * rho : ℕ) : ℝ≥0∞) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hmeanE :
      (q : ℝ≥0∞) * (a : ℝ≥0∞) ^ 3 ≤
        (rho : ℝ≥0∞) * (n : ℝ≥0∞) ^ 2 := by
    exact_mod_cast hmean
  rw [show ((a : ℝ≥0∞) / (n : ℝ≥0∞)) ^ 3 =
      (a : ℝ≥0∞) ^ 3 / (n : ℝ≥0∞) ^ 3 by
    simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]]
  simp only [div_eq_mul_inv, ← mul_assoc]
  change
    (((cStar * q * n : ℕ) : ℝ≥0∞) * (a : ℝ≥0∞) ^ 3) /
        (n : ℝ≥0∞) ^ 3 ≤
      ((cStar * rho : ℕ) : ℝ≥0∞)
  apply (ENNReal.div_le_iff (pow_ne_zero _ hn0) (by finiteness)).2
  calc
    (((cStar * q * n : ℕ) : ℝ≥0∞) * (a : ℝ≥0∞) ^ 3)
        = (cStar : ℝ≥0∞) * (n : ℝ≥0∞) *
            ((q : ℝ≥0∞) * (a : ℝ≥0∞) ^ 3) := by
              push_cast
              ring
    _ ≤ (cStar : ℝ≥0∞) * (n : ℝ≥0∞) *
          ((rho : ℝ≥0∞) * (n : ℝ≥0∞) ^ 2) := by
            gcongr
    _ = ((cStar * rho : ℕ) : ℝ≥0∞) *
          (n : ℝ≥0∞) ^ 3 := by
            push_cast
            ring

/-- A rational lower bound on the fixed tilt's logarithm. -/
theorem log_four_thirds_ge_twenty_three_eightieth :
    (23 : ℝ) / 80 ≤ Real.log ((4 : ℝ) / 3) := by
  have h := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 7)
    (by norm_num)
    (by norm_num)
    2
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- Real scalar bound for the `4/3` MGF tilt and exact integer threshold. -/
theorem four_thirds_floor_tail_real
    (p : ℝ) (hp : 0 ≤ p)
    (T m : ℕ)
    (hmean : (T : ℝ) * p ≤ (m : ℝ)) :
    ((1 + p / 3) ^ T) /
        (((4 : ℝ) / 3) ^ (4 * m / 3 + 1)) ≤
      Real.exp (-((m : ℝ) / 20)) := by
  let M : ℕ := 4 * m / 3 + 1
  change
    ((1 + p / 3) ^ T) / (((4 : ℝ) / 3) ^ M) ≤
      Real.exp (-((m : ℝ) / 20))
  have hMnat : 4 * m < 3 * M := by
    dsimp [M]
    omega
  have hMR : (4 * (m : ℝ)) / 3 ≤ (M : ℝ) := by
    have hcast : 4 * (m : ℝ) < 3 * (M : ℝ) := by
      exact_mod_cast hMnat
    nlinarith
  have hlog43 :
      (23 : ℝ) / 80 ≤ Real.log ((4 : ℝ) / 3) :=
    log_four_thirds_ge_twenty_three_eightieth
  have hbasePos : 0 < 1 + p / 3 := by positivity
  have hlogBase :
      Real.log (1 + p / 3) ≤ p / 3 := by
    have h := Real.log_le_sub_one_of_pos hbasePos
    nlinarith
  have hnum :
      (T : ℝ) * Real.log (1 + p / 3) ≤
        (m : ℝ) / 3 := by
    calc
      (T : ℝ) * Real.log (1 + p / 3)
          ≤ (T : ℝ) * (p / 3) := by
            exact mul_le_mul_of_nonneg_left hlogBase (by positivity)
      _ ≤ (m : ℝ) / 3 := by
            nlinarith
  have hden :
      ((4 * (m : ℝ)) / 3) * ((23 : ℝ) / 80) ≤
        (M : ℝ) * Real.log ((4 : ℝ) / 3) := by
    exact mul_le_mul hMR hlog43 (by norm_num) (by positivity)
  apply Real.le_exp_of_log_le
  rw [Real.log_div
        (pow_ne_zero _ (ne_of_gt hbasePos))
        (pow_ne_zero _ (by norm_num : (4 : ℝ) / 3 ≠ 0)),
      Real.log_pow, Real.log_pow]
  nlinarith

/-- ENNReal transport of `four_thirds_floor_tail_real`. -/
theorem four_thirds_floor_tail_ennreal
    {p pCompl : ℝ≥0∞}
    (hsum : pCompl + p = 1)
    (T m : ℕ)
    (hmean : (T : ℝ≥0∞) * p ≤ (m : ℝ≥0∞)) :
    ((pCompl + p * ((4 : ℝ≥0∞) / 3)) ^ T) /
        (((4 : ℝ≥0∞) / 3) ^ (4 * m / 3 + 1)) ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) / 20))) := by
  have hp_le_one : p ≤ 1 := by
    calc
      p = 0 + p := by simp
      _ ≤ pCompl + p := add_le_add bot_le le_rfl
      _ = 1 := hsum
  have hpCompl_le_one : pCompl ≤ 1 := by
    calc
      pCompl = pCompl + 0 := by simp
      _ ≤ pCompl + p := add_le_add le_rfl bot_le
      _ = 1 := hsum
  have hpTop : p ≠ ⊤ :=
    ne_of_lt (hp_le_one.trans_lt ENNReal.one_lt_top)
  have hpComplTop : pCompl ≠ ⊤ :=
    ne_of_lt (hpCompl_le_one.trans_lt ENNReal.one_lt_top)
  let r : ℝ≥0∞ := (4 : ℝ≥0∞) / 3
  let M : ℕ := 4 * m / 3 + 1
  change
    ((pCompl + p * r) ^ T) / (r ^ M) ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) / 20)))
  have hr0 : r ≠ 0 := by
    norm_num [r]
  have hprTop : p * r ≠ ⊤ := by
    finiteness
  have hnumTop : (pCompl + p * r) ^ T ≠ ⊤ := by
    finiteness
  have hden0 : r ^ M ≠ 0 := pow_ne_zero _ hr0
  have hleftTop :
      ((pCompl + p * r) ^ T) / (r ^ M) ≠ ⊤ := by
    simp [ENNReal.div_eq_top, hden0, hnumTop]
  have hsumR : pCompl.toReal + p.toReal = 1 := by
    have h := congrArg ENNReal.toReal hsum
    simpa [ENNReal.toReal_add hpComplTop hpTop] using h
  have hmeanR :
      (T : ℝ) * p.toReal ≤ (m : ℝ) := by
    have h := ENNReal.toReal_mono
      (by finiteness : ((m : ℕ) : ℝ≥0∞) ≠ ⊤) hmean
    simpa using h
  have hbaseR :
      pCompl.toReal + p.toReal * ((4 : ℝ) / 3) =
        1 + p.toReal / 3 := by
    nlinarith [hsumR]
  have hreal := four_thirds_floor_tail_real
    p.toReal ENNReal.toReal_nonneg T m hmeanR
  rw [← ENNReal.toReal_le_toReal hleftTop (by simp)]
  rw [ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_pow]
  rw [ENNReal.toReal_add hpComplTop hprTop]
  simp only [ENNReal.toReal_mul]
  have hrReal : r.toReal = (4 : ℝ) / 3 := by
    norm_num [r]
  rw [hrReal]
  rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  rw [hbaseR]
  exact hreal

/-- The existing adapted all-active counter has the stronger explicit
`exp (-(cStar * rho) / 20)` tail at Lemma 16's strict threshold. -/
theorem infectionAllActiveCount_lemma16_tail_twentieth
    (n : ℕ) (h3 : 3 ≤ n)
    (a : ℕ) (ha : a ≤ n)
    (q rho cStar : ℕ)
    (hmean : q * a ^ 3 ≤ rho * n ^ 2)
    (s0 : InfectionState n) :
    (∑' z, if 4 * cStar * rho < 3 * z.2 then
        iter (infectionAllActiveCount n h3 a)
          (cStar * q * n) (s0, 0) z
      else 0) ≤
    ENNReal.ofReal
      (Real.exp (-(((cStar * rho : ℕ) : ℝ) / 20))) := by
  let m : ℕ := cStar * rho
  let T : ℕ := cStar * q * n
  let M : ℕ := 4 * m / 3 + 1
  let cube : ℝ≥0∞ := infectionAllActiveCube n a
  let cubeCompl : ℝ≥0∞ := infectionAllActiveCubeCompl n a
  have hpartition : cubeCompl + cube = 1 := by
    simpa [cube, cubeCompl, add_comm] using
      infectionAllActiveCube_add_compl n a h3 ha
  have hmu : (T : ℝ≥0∞) * cube ≤ (m : ℝ≥0∞) := by
    simpa [T, m, cube, infectionAllActiveCube] using
      lemma16_cube_mean_le n a q rho cStar h3 hmean
  have hraw :=
    infectionAllActiveCount_tail_cube_four_thirds
      n h3 a ha T M s0
  have hraw' :
      (∑' z, if M ≤ z.2 then
          iter (infectionAllActiveCount n h3 a) T (s0, 0) z
        else 0) ≤
      ((cubeCompl + cube * ((4 : ℝ≥0∞) / 3)) ^ T) /
        (((4 : ℝ≥0∞) / 3) ^ M) := by
    simpa [cube, cubeCompl] using hraw
  calc
    (∑' z, if 4 * cStar * rho < 3 * z.2 then
        iter (infectionAllActiveCount n h3 a)
          (cStar * q * n) (s0, 0) z
      else 0) =
      (∑' z, if M ≤ z.2 then
          iter (infectionAllActiveCount n h3 a) T (s0, 0) z
        else 0) := by
          apply tsum_congr
          intro z
          have hthreshold :
              4 * cStar * rho < 3 * z.2 ↔ M ≤ z.2 := by
            simpa [M, m, Nat.mul_assoc] using
              lemma16_strict_counter_threshold
                (cStar * rho) z.2
          simp [T, hthreshold]
    _ ≤ ((cubeCompl + cube * ((4 : ℝ≥0∞) / 3)) ^ T) /
          (((4 : ℝ≥0∞) / 3) ^ M) := hraw'
    _ ≤ ENNReal.ofReal
          (Real.exp (-((m : ℝ) / 20))) := by
            simpa [M] using
              four_thirds_floor_tail_ennreal
                hpartition T m hmu
    _ = ENNReal.ofReal
          (Real.exp
            (-(((cStar * rho : ℕ) : ℝ) / 20))) := by
            rfl

/-- Lemma 16's normalized all-active-interaction error term. -/
theorem infectionAllActiveCount_lemma16_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (a : ℕ) (ha : a ≤ n)
    (q rho cStar : ℕ)
    (hmean : q * a ^ 3 ≤ rho * n ^ 2)
    (s0 : InfectionState n) :
    (∑' z, if 4 * cStar * rho < 3 * z.2 then
        iter (infectionAllActiveCount n h3 a)
          (cStar * q * n) (s0, 0) z
      else 0) ≤
    lemma16ReactionError cStar rho := by
  calc
    _ ≤ ENNReal.ofReal
        (Real.exp
          (-(((cStar * rho : ℕ) : ℝ) / 20))) :=
      infectionAllActiveCount_lemma16_tail_twentieth
        n h3 a ha q rho cStar hmean s0
    _ ≤ lemma16ReactionError cStar rho := by
      unfold lemma16ReactionError
      apply ENNReal.ofReal_mono
      apply Real.exp_le_exp.mpr
      have hm : 0 ≤ (((cStar * rho : ℕ) : ℝ)) := by positivity
      nlinarith

end Tri

#print axioms Tri.lemma16_strict_counter_threshold
#print axioms Tri.lemma16_cube_mean_le
#print axioms Tri.log_four_thirds_ge_twenty_three_eightieth
#print axioms Tri.four_thirds_floor_tail_real
#print axioms Tri.four_thirds_floor_tail_ennreal
#print axioms Tri.infectionAllActiveCount_lemma16_tail_twentieth
#print axioms Tri.infectionAllActiveCount_lemma16_tail
