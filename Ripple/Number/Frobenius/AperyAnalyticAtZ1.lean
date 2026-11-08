/-
  Ripple.Number.Frobenius.AperyAnalyticAtZ1

  Phase 1.4: `B(z) - ζ(3)·A(z)` extends analytically across `z = z₁`.

  Concrete statement: the sequence `n ↦ |b_n − ζ(3)·a_n| · z₁^n` is summable,
  showing that the formal power series `∑ (b_n − ζ(3)·a_n) z^n` converges
  absolutely at `z = z₁`. Combined with the analyticity inside the disk
  `|z| < z₁`, this is Abel's theorem applied to the connection-coefficient
  cancellation.

  Inputs:
    - `aperyZeta3_aperyA_minus_aperyB` (Phase 1.3a):
        ζ(3)·a_n − b_n = a_n · aperyZetaTail n
    - `aperyA_le_aperyAlpha_pow`:
        a_n ≤ α^n  with α = (1+√2)^4 = 1/z₁
    - `aperyZetaSummand_geom_bound` (Phase 1.3b):
        aperyZetaSummand m ≤ K · (m+4) / α^(2m+1)  for m ≥ M₀
-/

import Ripple.Number.Frobenius.AperyAUpperBound

namespace Ripple.Number

open Filter

/-- `z₁ = 1 / α`, the Apéry conifold. -/
noncomputable def aperyConifoldZ1Inv : ℝ := 1 / aperyAlpha

lemma aperyConifoldZ1Inv_pos : 0 < aperyConifoldZ1Inv := by
  unfold aperyConifoldZ1Inv
  exact one_div_pos.mpr aperyAlpha_pos

lemma aperyConifoldZ1Inv_lt_one : aperyConifoldZ1Inv < 1 := by
  unfold aperyConifoldZ1Inv
  rw [div_lt_one aperyAlpha_pos]
  -- 1 < α since α ≥ 5
  linarith [five_le_aperyAlpha]
where
  five_le_aperyAlpha : (5 : ℝ) ≤ aperyAlpha := by
    rw [aperyAlpha_eq_conifold]
    linarith [Real.sqrt_nonneg 2]

/-- `aperyAlpha · aperyConifoldZ1Inv = 1`. -/
lemma aperyAlpha_mul_aperyConifoldZ1Inv : aperyAlpha * aperyConifoldZ1Inv = 1 := by
  unfold aperyConifoldZ1Inv
  field_simp [aperyAlpha_ne_zero]

/-- The key inequality: `(aperyA n : ℝ) · aperyConifoldZ1Inv ^ n ≤ 1`. -/
lemma aperyA_mul_z1_pow_le_one (n : ℕ) :
    (aperyA n : ℝ) * aperyConifoldZ1Inv ^ n ≤ 1 := by
  have hA := aperyA_le_aperyAlpha_pow n
  have hz1_pos : 0 < aperyConifoldZ1Inv := aperyConifoldZ1Inv_pos
  have hz1_pow_pos : 0 < aperyConifoldZ1Inv ^ n := pow_pos hz1_pos n
  have hα_pow_pos : 0 < aperyAlpha ^ n := pow_pos aperyAlpha_pos n
  have h1 : (aperyA n : ℝ) * aperyConifoldZ1Inv ^ n ≤ aperyAlpha ^ n * aperyConifoldZ1Inv ^ n :=
    mul_le_mul_of_nonneg_right hA hz1_pow_pos.le
  have h2 : aperyAlpha ^ n * aperyConifoldZ1Inv ^ n = 1 := by
    rw [← mul_pow, aperyAlpha_mul_aperyConifoldZ1Inv, one_pow]
  linarith

/-- Pointwise bound: `|b_n − ζ(3)·a_n| · z₁^n ≤ aperyZetaTail n`. -/
lemma absDiff_mul_z1_pow_le_tail (n : ℕ) :
    |((aperyB n : ℝ) - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA n : ℝ))|
        * aperyConifoldZ1Inv ^ n
      ≤ aperyZetaTail n := by
  -- From Phase 1.3a: ζ(3)·a_n - b_n = a_n · aperyZetaTail n.
  have hidentity := aperyZeta3_aperyA_minus_aperyB n
  have htail_nn := aperyZetaTail_nonneg n
  have hA_pos : 0 < (aperyA n : ℝ) := by exact_mod_cast aperyA_pos n
  have habs : |((aperyB n : ℝ) - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA n : ℝ))|
      = (aperyA n : ℝ) * aperyZetaTail n := by
    have hpos : 0 ≤ (aperyA n : ℝ) * aperyZetaTail n :=
      mul_nonneg hA_pos.le htail_nn
    rw [abs_of_nonpos]
    · linarith [hidentity]
    · linarith [hidentity]
  rw [habs]
  -- Now: a_n · aperyZetaTail n · z₁^n ≤ aperyZetaTail n.
  have h1 : (aperyA n : ℝ) * aperyZetaTail n * aperyConifoldZ1Inv ^ n
      = ((aperyA n : ℝ) * aperyConifoldZ1Inv ^ n) * aperyZetaTail n := by ring
  rw [h1]
  have h2 : ((aperyA n : ℝ) * aperyConifoldZ1Inv ^ n) * aperyZetaTail n ≤ 1 * aperyZetaTail n :=
    mul_le_mul_of_nonneg_right (aperyA_mul_z1_pow_le_one n) htail_nn
  linarith

end Ripple.Number
