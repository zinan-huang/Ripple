/-
  Ripple.Kurtz.StrongApprox.DyadicStep — one level of the dyadic Poisson–Brownian coupling

  A dyadic parent interval `J` of length `ℓ` carries the Poisson count `m = Y(J)` and the Brownian
  increment `wJ = W(J)`.  The midpoint refinement uses one standard normal `z`: the Brownian value
  at the midpoint is `W(a) + wJ/2 + (√ℓ/2) z` (Lévy construction) and the left-child count is
  `q = Q_m(z)` (binomial quantile coupling).  With the interval errors `D(I) = Y(I) − |I| − W(I)`,
  the quantile error `ε = q − m/2 − (√m/2) z` and the fresh term
  `g = ε + ((√m − √ℓ)/2) z`, the children satisfy `D(I_L) = g + D(J)/2`, `D(I_R) = −g + D(J)/2`.
  The cross term `|√m − √ℓ| |z| / 2` is bounded in two regimes (coarse: `|z| ≤ √ℓ/4`; fine: no
  condition) by linear functions of `|D(J)|`, `z²`, `z'²` and `√ℓ |z'|`, where `m − ℓ = D(J) + √ℓ z'`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Real

/-- The fresh term of a refinement: quantile error plus the `(√m − √ℓ) z / 2` correction. -/
noncomputable def freshTerm (m ℓ z q : ℝ) : ℝ :=
  (q - m / 2 - Real.sqrt m / 2 * z) + (Real.sqrt m - Real.sqrt ℓ) / 2 * z

/-- Lemma D, left child: `D(I_L) = g + D(J)/2`. -/
theorem dyadic_left_error (m ℓ wJ z q : ℝ) :
    q - ℓ / 2 - (wJ / 2 + Real.sqrt ℓ / 2 * z) = freshTerm m ℓ z q + (m - ℓ - wJ) / 2 := by
  unfold freshTerm; ring

/-- Lemma D, right child: `D(I_R) = −g + D(J)/2`. -/
theorem dyadic_right_error (m ℓ wJ z q : ℝ) :
    (m - q) - ℓ / 2 - (wJ - (wJ / 2 + Real.sqrt ℓ / 2 * z)) =
      -freshTerm m ℓ z q + (m - ℓ - wJ) / 2 := by
  unfold freshTerm; ring

/-- `|√m − √ℓ| (√m + √ℓ) = |m − ℓ|` for `m, ℓ ≥ 0`. -/
theorem abs_sqrt_sub_sqrt_mul_add {m ℓ : ℝ} (hm : 0 ≤ m) (hℓ : 0 ≤ ℓ) :
    |Real.sqrt m - Real.sqrt ℓ| * (Real.sqrt m + Real.sqrt ℓ) = |m - ℓ| := by
  have h : (Real.sqrt m - Real.sqrt ℓ) * (Real.sqrt m + Real.sqrt ℓ) = m - ℓ := by
    have h1 := Real.sq_sqrt hm
    have h2 := Real.sq_sqrt hℓ
    nlinarith [h1, h2]
  rw [← h, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt m + Real.sqrt ℓ)]

/-- `|√m − √ℓ| ≤ |m − ℓ| / √ℓ` for `m ≥ 0`, `ℓ > 0`. -/
theorem abs_sqrt_sub_sqrt_le_div {m ℓ : ℝ} (hm : 0 ≤ m) (hℓ : 0 < ℓ) :
    |Real.sqrt m - Real.sqrt ℓ| ≤ |m - ℓ| / Real.sqrt ℓ := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  rw [le_div_iff₀ hs, ← abs_sqrt_sub_sqrt_mul_add hm hℓ.le]
  have : 0 ≤ |Real.sqrt m - Real.sqrt ℓ| := abs_nonneg _
  nlinarith [Real.sqrt_nonneg m]

/-- `|√m − √ℓ|² ≤ |m − ℓ|` for `m, ℓ ≥ 0`. -/
theorem sq_abs_sqrt_sub_sqrt_le {m ℓ : ℝ} (hm : 0 ≤ m) (hℓ : 0 ≤ ℓ) :
    |Real.sqrt m - Real.sqrt ℓ| ^ 2 ≤ |m - ℓ| := by
  rw [← abs_sqrt_sub_sqrt_mul_add hm hℓ, sq]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc |Real.sqrt m - Real.sqrt ℓ| ≤ |Real.sqrt m| + |Real.sqrt ℓ| := abs_sub _ _
    _ = Real.sqrt m + Real.sqrt ℓ := by
        rw [abs_of_nonneg (Real.sqrt_nonneg m), abs_of_nonneg (Real.sqrt_nonneg ℓ)]

/-- AM–GM in the form used for the fine regime: `a b ≤ a²/4 + b²`. -/
theorem mul_le_sq_div_four_add_sq (a b : ℝ) : a * b ≤ a ^ 2 / 4 + b ^ 2 := by
  nlinarith [sq_nonneg (a / 2 - b)]

/-- Cross term, coarse regime (`|z| ≤ √ℓ / 4`):
`|√m − √ℓ| |z| / 2 ≤ |D|/8 + (z² + z'²)/4` where `m − ℓ = D + √ℓ z'`. -/
theorem cross_term_coarse {m ℓ D z z' : ℝ} (hm : 0 ≤ m) (hℓ : 0 < ℓ)
    (hD : m - ℓ = D + Real.sqrt ℓ * z') (hz : |z| ≤ Real.sqrt ℓ / 4) :
    |Real.sqrt m - Real.sqrt ℓ| * |z| / 2 ≤ |D| / 8 + (z ^ 2 + z' ^ 2) / 4 := by
  set s := Real.sqrt ℓ with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hℓ
  -- `|√m − √ℓ| s ≤ |D| + s |z'|`
  have h1 : |Real.sqrt m - s| * s ≤ |D| + s * |z'| := by
    have := abs_sqrt_sub_sqrt_mul_add hm hℓ.le
    rw [← hs_def] at this
    calc |Real.sqrt m - s| * s ≤ |Real.sqrt m - s| * (Real.sqrt m + s) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          linarith [Real.sqrt_nonneg m]
      _ = |m - ℓ| := this
      _ = |D + s * z'| := by rw [hD]
      _ ≤ |D| + |s * z'| := abs_add_le _ _
      _ = |D| + s * |z'| := by rw [abs_mul, abs_of_pos hs]
  have hz0 : 0 ≤ |z| := abs_nonneg _
  have hz'0 : 0 ≤ |z'| := abs_nonneg _
  have ha : 0 ≤ |Real.sqrt m - s| := abs_nonneg _
  have hD0 : 0 ≤ |D| := abs_nonneg _
  -- multiply the goal by `s > 0`
  refine le_of_mul_le_mul_left ?_ hs
  have hzz' : |z'| * |z| ≤ (z ^ 2 + z' ^ 2) / 2 := by
    nlinarith [sq_nonneg (|z| - |z'|), sq_abs z, sq_abs z']
  calc s * (|Real.sqrt m - s| * |z| / 2) = (|Real.sqrt m - s| * s) * |z| / 2 := by ring
    _ ≤ (|D| + s * |z'|) * |z| / 2 := by gcongr
    _ = |D| * |z| / 2 + s * (|z'| * |z|) / 2 := by ring
    _ ≤ |D| * (s / 4) / 2 + s * ((z ^ 2 + z' ^ 2) / 2) / 2 := by gcongr
    _ = s * (|D| / 8 + (z ^ 2 + z' ^ 2) / 4) := by ring

/-- Cross term, fine regime (no condition on `z`):
`|√m − √ℓ| |z| / 2 ≤ |D|/8 + z²/2 + √ℓ |z'| / 8` where `m − ℓ = D + √ℓ z'`. -/
theorem cross_term_fine {m ℓ D z z' : ℝ} (hm : 0 ≤ m) (hℓ : 0 ≤ ℓ)
    (hD : m - ℓ = D + Real.sqrt ℓ * z') :
    |Real.sqrt m - Real.sqrt ℓ| * |z| / 2 ≤ |D| / 8 + z ^ 2 / 2 + Real.sqrt ℓ * |z'| / 8 := by
  have hsq := sq_abs_sqrt_sub_sqrt_le hm hℓ
  have hx : |m - ℓ| ≤ |D| + Real.sqrt ℓ * |z'| := by
    rw [hD]
    calc |D + Real.sqrt ℓ * z'| ≤ |D| + |Real.sqrt ℓ * z'| := abs_add_le _ _
      _ = |D| + Real.sqrt ℓ * |z'| := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg ℓ)]
  have hamgm := mul_le_sq_div_four_add_sq |Real.sqrt m - Real.sqrt ℓ| |z|
  have hz2 : |z| ^ 2 = z ^ 2 := sq_abs z
  nlinarith [hsq, hx, hamgm, hz2]

end Ripple.Kurtz.StrongApprox
