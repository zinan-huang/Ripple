/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar Hoeffding bounds

This file proves the real inequalities used to optimize the Chernoff bound in
`Tri.Progress`.  It contains no probabilistic arguments: the main input is the
concavity of the logarithm of the centered Bernoulli exponential moment.
-/

namespace Tri

/-- The logarithmic form of Hoeffding's lemma for a Bernoulli variable.

The proof studies `log (p' + p * exp (-x)) + p * x - x ^ 2 / 8`. Its second
derivative is nonpositive by the elementary inequality
`4 * p' * (p * exp (-x)) ≤ (p' + p * exp (-x)) ^ 2`, so its derivative at
zero shows that zero is a maximum. -/
theorem bernoulli_log_mgf_le {p p' t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hsum : p + p' = 1) (ht : 0 ≤ t) :
    Real.log (p' + p * Real.exp (-t)) ≤ -p * t + t ^ 2 / 8 := by
  have hp'₀ : 0 ≤ p' := by linarith
  have hsum' : p' + p = 1 := by linarith
  let B : ℝ → ℝ := fun x ↦ p' + p * Real.exp (-x)
  let f : ℝ → ℝ := fun x ↦ Real.log (B x) + p * x - x ^ 2 / 8
  let f' : ℝ → ℝ := fun x ↦ -p * Real.exp (-x) / B x + p - x / 4
  let f'' : ℝ → ℝ := fun x ↦ p * p' * Real.exp (-x) / (B x) ^ 2 - 1 / 4
  have hBpos (x : ℝ) : 0 < B x := by
    dsimp [B]
    by_cases hp : p = 0
    · have hp'eq : p' = 1 := by linarith
      simp [hp, hp'eq]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hp)
      positivity
  have hBderiv (x : ℝ) : HasDerivAt B (-p * Real.exp (-x)) x := by
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
      convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1
      ring
    simpa [B] using (hexp.const_mul p).const_add p'
  have hfderiv (x : ℝ) : HasDerivAt f (f' x) x := by
    have hlog := (hBderiv x).log (hBpos x).ne'
    have hlin := (hasDerivAt_id x).const_mul p
    have hsq := (hasDerivAt_pow 2 x).div_const 8
    convert (hlog.add hlin).sub hsq using 1
    simp [f', B]
    ring
  have hf'deriv (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have hnum : HasDerivAt (fun y : ℝ ↦ -p * Real.exp (-y))
        (p * Real.exp (-x)) x := by
      have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
        convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1
        ring
      convert hexp.const_mul (-p) using 1
      ring
    have hquot := hnum.div (hBderiv x) (hBpos x).ne'
    have hlin := (hasDerivAt_id x).div_const 4
    convert (hquot.add_const p).sub hlin using 1
    dsimp [f'', B]
    field_simp [(hBpos x).ne']
    ring
  have hf''nonpos (x : ℝ) : f'' x ≤ 0 := by
    have hamgm := four_mul_le_sq_add p' (p * Real.exp (-x))
    have hBsq : 0 < (B x) ^ 2 := sq_pos_of_pos (hBpos x)
    dsimp [f'', B]
    rw [sub_nonpos, div_le_iff₀ hBsq]
    nlinarith
  have hconcave : ConcaveOn ℝ Set.univ f := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.univ) (f' := f') (f'' := f'')
      convex_univ ?_ ?_ ?_ ?_
    · exact fun x _ ↦ (hfderiv x).continuousAt.continuousWithinAt
    · intro x _
      simpa using hfderiv x
    · intro x _
      simpa using hf'deriv x
    · intro x _
      exact hf''nonpos x
  have hfzero : f 0 = 0 := by simp [f, B, hsum']
  have hfderivzero : HasDerivAt f 0 0 := by
    convert hfderiv 0 using 1
    simp [f', B, hsum']
  have hft : f t ≤ 0 := by
    rcases ht.eq_or_lt with rfl | ht
    · exact hfzero.le
    · have hslope := hconcave.slope_le_of_hasDerivAt
          (Set.mem_univ 0) (Set.mem_univ t) ht hfderivzero
      rw [slope_def_field, hfzero, sub_zero, sub_zero, div_le_iff₀ ht] at hslope
      simpa using hslope
  dsimp [f, B] at hft
  linarith

/-- **Hoeffding's lemma for a Bernoulli variable.** If `p` and `p'` are
complementary probabilities and `t` is nonnegative, then the lower-tail
Bernoulli exponential moment is bounded by a Gaussian exponential moment. -/
theorem bernoulli_hoeffding {p p' t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hsum : p + p' = 1) (ht : 0 ≤ t) :
    p' + p * Real.exp (-t) ≤ Real.exp (-p * t + t ^ 2 / 8) := by
  have hp'₀ : 0 ≤ p' := by linarith
  have hbase : 0 < p' + p * Real.exp (-t) := by
    by_cases hp : p = 0
    · have : p' = 1 := by linarith
      simp [hp, this]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hp)
      positivity
  exact (Real.log_le_iff_le_exp hbase).mp (bernoulli_log_mgf_le hp₀ hp₁ hsum ht)

/-- **The optimized Bernoulli lower-tail exponent.** For `0 ≤ a < p`, substituting
`t = 4 * (p - a)` into Hoeffding's lemma and combining the exponential terms
gives the exponent `-2 * T * (p - a) ^ 2`. -/
theorem bernoulli_hoeffding_optimized {a p p' t : ℝ}
    (ha : 0 ≤ a) (hap : a < p) (hp₁ : p ≤ 1) (hsum : p + p' = 1)
    (ht : t = 4 * (p - a)) (T : ℕ) :
    (p' + p * Real.exp (-t)) ^ T * Real.exp (t * (a * (T : ℝ)))
      ≤ Real.exp (-2 * (T : ℝ) * (p - a) ^ 2) := by
  have hp₀ : 0 ≤ p := by linarith
  have ht₀ : 0 ≤ t := by rw [ht]; linarith
  have hhoeffding := bernoulli_hoeffding hp₀ hp₁ hsum ht₀
  have hp'₀ : 0 ≤ p' := by linarith
  have hbase : 0 ≤ p' + p * Real.exp (-t) :=
    add_nonneg hp'₀ (mul_nonneg hp₀ (Real.exp_nonneg _))
  have hpow := pow_le_pow_left₀ hbase hhoeffding T
  calc
    (p' + p * Real.exp (-t)) ^ T * Real.exp (t * (a * (T : ℝ)))
        ≤ Real.exp (-p * t + t ^ 2 / 8) ^ T * Real.exp (t * (a * (T : ℝ))) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp ((T : ℝ) * (-p * t + t ^ 2 / 8) + t * (a * (T : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ = Real.exp (-2 * (T : ℝ) * (p - a) ^ 2) := by
      congr 1
      rw [ht]
      ring

end Tri
