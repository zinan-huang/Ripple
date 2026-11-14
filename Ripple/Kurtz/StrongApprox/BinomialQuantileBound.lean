/-
  Ripple.Kurtz.StrongApprox.BinomialQuantileBound — (BQ): the symmetric-binomial quantile coupling
  error is at most `1 + z²`, and the law of the coupling

  Mathematics: the quantile-coupling bound (Lemma T).

  With `binF m k = P(Bin(m,½) ≤ k)` and `q = natQuantile (binF m) (Φ z)`:
  * (L) `q ≤ m`, `g(q−1) < z` when `q ≥ 1`, `z ≤ g(q+1)` when `q + 1 ≤ m` (from (I) at `p = ½`);
  * the real-count root `gB m y = sgn(y − m/2) √(m G(y/m))`, `G(t) = 2D(t‖½)`, is continuous,
    and `|y − m/2 − (√m/2) gB(y)| ≤ gB(y)²` on `[0,m]` (calculus of
    `f(δ) = (1+δ)log(1+δ) + (1−δ)log(1−δ)`: `f ≥ δ²`, `f − δ² ≤ 2δ⁴/9` on `[0,½]`);
  * (BQ) `|q − m/2 − (√m/2) z| ≤ 1 + z²` for every `m` and every real `z`;
  * the coupled count `binCoupling m ∘ Z`, `Z ~ N(0,1)`, has cdf `P(Bin(m,½) ≤ k)`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.BinomialIntersection
import Ripple.Kurtz.StrongApprox.QuantileCoupling
import Ripple.Kurtz.StrongApprox.QuantileLaw
import Ripple.Kurtz.StrongApprox.PoissonQuantileBound

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### The symmetric rate `G(t) = 2 D(t ‖ ½)` -/

/-- `G(t) = 2 (t log t + (1−t) log(1−t)) + 2 log 2 = 2 D(t‖½)`. -/
noncomputable def symG (t : ℝ) : ℝ :=
  2 * (t * Real.log t + (1 - t) * Real.log (1 - t)) + 2 * Real.log 2

theorem log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [one_div, Real.log_inv]

theorem one_sub_half : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num

theorem two_mul_binRate_half (t : ℝ) : 2 * binRate t (1 / 2) = symG t := by
  unfold binRate symG
  rw [one_sub_half, log_half]
  ring

theorem symG_symm (t : ℝ) : symG (1 - t) = symG t := by
  unfold symG; rw [sub_sub_cancel]; ring

theorem continuous_symG : Continuous symG := by
  have h1 : Continuous fun t : ℝ => (1 - t) * Real.log (1 - t) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact ((Real.continuous_mul_log.add h1).const_mul 2).add continuous_const

theorem symG_half : symG (1 / 2) = 0 := by
  unfold symG
  rw [one_sub_half, log_half]; ring

theorem symG_zero : symG 0 = 2 * Real.log 2 := by simp [symG]

theorem symG_one : symG 1 = 2 * Real.log 2 := by simp [symG]

theorem symG_le_two_log_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : symG t ≤ 2 * Real.log 2 := by
  unfold symG
  have h1 := Real.mul_log_nonpos ht0 ht1
  have h2 := Real.mul_log_nonpos (by linarith : 0 ≤ 1 - t) (by linarith : 1 - t ≤ 1)
  linarith

/-- `G'(t) = 2 (log t − log(1−t))`. -/
noncomputable def symG' (t : ℝ) : ℝ := 2 * (Real.log t - Real.log (1 - t))

theorem symG'_half : symG' (1 / 2) = 0 := by
  unfold symG'; rw [one_sub_half]; ring

theorem hasDerivAt_symG {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : HasDerivAt symG (symG' t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log t + 1) t :=
    Real.hasDerivAt_mul_log ht0.ne'
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
  have h3 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      ((Real.log (1 - t) + 1) * (-1)) t :=
    (Real.hasDerivAt_mul_log (by linarith : (1 : ℝ) - t ≠ 0)).comp t h2
  have h := ((h1.add h3).const_mul 2).add_const (2 * Real.log 2)
  refine h.congr_deriv ?_
  unfold symG'; ring

theorem hasDerivAt_symG' {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt symG' (2 * (t⁻¹ + (1 - t)⁻¹)) t := by
  have h1 := Real.hasDerivAt_log ht0.ne'
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
  have h3 := h2.log (by linarith : (1 : ℝ) - t ≠ 0)
  have h := (h1.sub h3).const_mul 2
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_sq_lin (t : ℝ) :
    HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 2) (4 * (2 * t - 1)) t := by
  have := (((hasDerivAt_id t).const_mul 2).sub_const 1).pow 2
  convert this using 1
  simp only [id]
  norm_num
  try ring

theorem hasDerivAt_pow_four_lin (t : ℝ) :
    HasDerivAt (fun x : ℝ => 2 / 9 * (2 * x - 1) ^ 4) (16 / 9 * (2 * t - 1) ^ 3) t := by
  have := ((((hasDerivAt_id t).const_mul 2).sub_const 1).pow 4).const_mul (2 / 9 : ℝ)
  convert this using 1
  simp only [id]
  norm_num
  try ring

/-- `φ = G − (2t−1)²` has derivative `G' − 4(2t−1)`. -/
theorem hasDerivAt_phi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun x => symG x - (2 * x - 1) ^ 2) (symG' t - 4 * (2 * t - 1)) t :=
  (hasDerivAt_symG ht0 ht1).sub (hasDerivAt_sq_lin t)

theorem hasDerivAt_phi' {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun x => symG' x - 4 * (2 * x - 1)) (2 * (t⁻¹ + (1 - t)⁻¹) - 8) t := by
  have h2 : HasDerivAt (fun x : ℝ => 4 * (2 * x - 1)) (4 * 2) t := by
    have := (((hasDerivAt_id t).const_mul 2).sub_const 1).const_mul (4 : ℝ)
    convert this using 1
    norm_num
  have := (hasDerivAt_symG' ht0 ht1).sub h2
  refine this.congr_deriv ?_
  ring

/-- `1/t + 1/(1−t) ≥ 4` on `(0,1)`. -/
theorem four_le_inv_add_inv {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 4 ≤ t⁻¹ + (1 - t)⁻¹ := by
  have h1t : 0 < 1 - t := by linarith
  rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ ht0.ne' h1t.ne', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * t - 1)]

/-- `φ' ≥ 0` on `[½, 1)`. -/
theorem phi'_nonneg {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) : 0 ≤ symG' t - 4 * (2 * t - 1) := by
  have hmono : MonotoneOn (fun x => symG' x - 4 * (2 * x - 1)) (Ico (1 / 2) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
    · intro x hx
      exact (hasDerivAt_phi' (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (hasDerivAt_phi' (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hasDerivAt_phi' (by linarith [hx.1]) hx.2).deriv]
      linarith [four_le_inv_add_inv (by linarith [hx.1] : 0 < x) hx.2]
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨ht, ht1⟩ ht
  simp only [symG'_half] at this
  linarith

/-- `G(t) ≥ (2t−1)²` on `[½, 1]`. -/
theorem symG_ge_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) : (2 * t - 1) ^ 2 ≤ symG t := by
  have hmono : MonotoneOn (fun x => symG x - (2 * x - 1) ^ 2) (Icc (1 / 2) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (continuous_symG.sub (by fun_prop)).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_phi (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_phi (by linarith [hx.1]) hx.2).deriv]
      exact phi'_nonneg hx.1.le hx.2
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨ht, ht1⟩ ht
  simp only [symG_half] at this
  norm_num at this
  linarith

/-- `G(t) ≥ (2t−1)²` on `[0, 1]`. -/
theorem symG_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (2 * t - 1) ^ 2 ≤ symG t := by
  rcases le_or_gt (1 / 2) t with h | h
  · exact symG_ge_of_half_le h ht1
  · have := symG_ge_of_half_le (t := 1 - t) (by linarith) (by linarith)
    rw [symG_symm] at this
    nlinarith

theorem symG_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ symG t :=
  (sq_nonneg _).trans (symG_ge ht0 ht1)

/-- `ψ'' ≥ 0` on `[½, ¾]`: `(32/3)(2t−1)² + 8 ≥ 2/(t(1−t))`. -/
theorem psi''_nonneg {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 3 / 4) :
    0 ≤ 32 / 3 * (2 * t - 1) ^ 2 - (2 * (t⁻¹ + (1 - t)⁻¹) - 8) := by
  have ht0 : 0 < t := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hsum : t⁻¹ + (1 - t)⁻¹ = 1 / (t * (1 - t)) := by
    rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ ht0.ne' h1t.ne']
    congr 1; ring
  rw [hsum]
  have hu0 : 0 ≤ 2 * t - 1 := by linarith
  have hu1 : 2 * t - 1 ≤ 1 / 2 := by linarith
  have hprod : 0 ≤ (2 * t - 1) ^ 2 * (1 - 4 * (2 * t - 1) ^ 2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have key : 2 * (1 / (t * (1 - t))) ≤ 32 / 3 * (2 * t - 1) ^ 2 + 8 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem hasDerivAt_psi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun x => 2 / 9 * (2 * x - 1) ^ 4 - (symG x - (2 * x - 1) ^ 2))
      (16 / 9 * (2 * t - 1) ^ 3 - (symG' t - 4 * (2 * t - 1))) t :=
  (hasDerivAt_pow_four_lin t).sub (hasDerivAt_phi ht0 ht1)

theorem hasDerivAt_psi' {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun x => 16 / 9 * (2 * x - 1) ^ 3 - (symG' x - 4 * (2 * x - 1)))
      (32 / 3 * (2 * t - 1) ^ 2 - (2 * (t⁻¹ + (1 - t)⁻¹) - 8)) t := by
  have h1 : HasDerivAt (fun x : ℝ => 16 / 9 * (2 * x - 1) ^ 3) (32 / 3 * (2 * t - 1) ^ 2) t := by
    have := ((((hasDerivAt_id t).const_mul 2).sub_const 1).pow 3).const_mul (16 / 9 : ℝ)
    convert this using 1
    simp only [id]
    norm_num
    try ring
  exact h1.sub (hasDerivAt_phi' ht0 ht1)

/-- `ψ' ≥ 0` on `[½, ¾]`. -/
theorem psi'_nonneg {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 3 / 4) :
    0 ≤ 16 / 9 * (2 * t - 1) ^ 3 - (symG' t - 4 * (2 * t - 1)) := by
  have hmono : MonotoneOn (fun x => 16 / 9 * (2 * x - 1) ^ 3 - (symG' x - 4 * (2 * x - 1)))
      (Icc (1 / 2) (3 / 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_psi' (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_psi' (by linarith [hx.1])
        (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_psi' (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact psi''_nonneg hx.1.le hx.2.le
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨ht, ht1⟩ ht
  simp only [symG'_half] at this
  norm_num at this
  linarith

/-- `G(t) − (2t−1)² ≤ (2/9)(2t−1)⁴` on `[½, ¾]`. -/
theorem symG_sub_le {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 3 / 4) :
    symG t - (2 * t - 1) ^ 2 ≤ 2 / 9 * (2 * t - 1) ^ 4 := by
  have hmono : MonotoneOn (fun x => 2 / 9 * (2 * x - 1) ^ 4 - (symG x - (2 * x - 1) ^ 2))
      (Icc (1 / 2) (3 / 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact ((by fun_prop : Continuous fun x : ℝ => 2 / 9 * (2 * x - 1) ^ 4).sub
        (continuous_symG.sub (by fun_prop))).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_psi (by linarith [hx.1])
        (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_psi (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact psi'_nonneg hx.1.le hx.2.le
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨ht, ht1⟩ ht
  simp only [symG_half] at this
  norm_num at this
  linarith

/-! ### The real-count root `gB m y = sgn(y − m/2) √(m G(y/m))` -/

/-- `g_{m,½}(y)` for a real count `y`. -/
noncomputable def gB (m : ℕ) (y : ℝ) : ℝ := binSignedRootR m (1 / 2) y

theorem gB_nat (m k : ℕ) : gB m k = binSignedRoot m k (1 / 2) := rfl

theorem gB_eq (m : ℕ) (y : ℝ) :
    gB m y = if (m : ℝ) / 2 ≤ y then Real.sqrt (m * symG (y / m))
      else -Real.sqrt (m * symG (y / m)) := by
  unfold gB binSignedRootR
  have h1 : (m : ℝ) * (1 / 2) = m / 2 := by ring
  have h2 : 2 * (m : ℝ) * binRate (y / m) (1 / 2) = m * symG (y / m) := by
    rw [← two_mul_binRate_half]; ring
  rw [h1, h2]

theorem gB_eq_fun (m : ℕ) : gB m = fun y => if (m : ℝ) / 2 ≤ y then Real.sqrt (m * symG (y / m))
    else -Real.sqrt (m * symG (y / m)) := funext (gB_eq m)

theorem gB_half (m : ℕ) (hm : 0 < m) : gB m (m / 2) = 0 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [gB_eq, if_pos le_rfl]
  have : (m : ℝ) / 2 / m = 1 / 2 := by field_simp
  rw [this, symG_half, mul_zero, Real.sqrt_zero]

theorem abs_gB (m : ℕ) (y : ℝ) : |gB m y| = Real.sqrt (m * symG (y / m)) := by
  rw [gB_eq]
  split_ifs
  · exact abs_of_nonneg (Real.sqrt_nonneg _)
  · rw [abs_neg]; exact abs_of_nonneg (Real.sqrt_nonneg _)

theorem continuous_gB (m : ℕ) (hm : 0 < m) : Continuous (gB m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [continuous_iff_continuousAt]
  intro y
  have hsq : Continuous fun y : ℝ => Real.sqrt (m * symG (y / m)) :=
    Real.continuous_sqrt.comp ((continuous_symG.comp (continuous_id.div_const _)).const_mul _)
  rcases lt_trichotomy y ((m : ℝ) / 2) with hy | hy | hy
  · have hev : (fun y : ℝ => -Real.sqrt (m * symG (y / m))) =ᶠ[𝓝 y] gB m := by
      filter_upwards [Iio_mem_nhds hy] with x hx
      rw [gB_eq, if_neg (not_le.mpr hx)]
    exact hsq.neg.continuousAt.congr hev
  · rw [hy, ContinuousAt, gB_half m hm, tendsto_zero_iff_abs_tendsto_zero]
    have habs : abs ∘ gB m = fun x => Real.sqrt (m * symG (x / m)) := funext (abs_gB m)
    rw [habs]
    have h0 : Real.sqrt (m * symG ((m : ℝ) / 2 / m)) = 0 := by
      have : (m : ℝ) / 2 / m = 1 / 2 := by field_simp
      rw [this, symG_half, mul_zero, Real.sqrt_zero]
    rw [← h0]
    exact hsq.continuousAt
  · have hev : (fun y : ℝ => Real.sqrt (m * symG (y / m))) =ᶠ[𝓝 y] gB m := by
      filter_upwards [Ioi_mem_nhds hy] with x hx
      rw [gB_eq, if_pos (le_of_lt hx)]
    exact hsq.continuousAt.congr hev

theorem gB_zero (m : ℕ) (hm : 0 < m) : gB m 0 = -Real.sqrt (m * (2 * Real.log 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [gB_eq, if_neg (by linarith), zero_div, symG_zero]

theorem gB_top (m : ℕ) (hm : 0 < m) : gB m m = Real.sqrt (m * (2 * Real.log 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [gB_eq, if_pos (by linarith), div_self hmR.ne', symG_one]

/-- `gB m 0 ≤ gB m y` on `[0, m]`. -/
theorem gB_zero_le (m : ℕ) (hm : 0 < m) {y : ℝ} (hy0 : 0 ≤ y) (hym : y ≤ m) :
    gB m 0 ≤ gB m y := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht0 : 0 ≤ y / m := by positivity
  have ht1 : y / m ≤ 1 := by rw [div_le_one hmR]; exact hym
  rw [gB_zero m hm, gB_eq]
  split_ifs with h
  · linarith [Real.sqrt_nonneg (m * symG (y / m)), Real.sqrt_nonneg (m * (2 * Real.log 2))]
  · apply neg_le_neg
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (symG_le_two_log_two ht0 ht1) hmR.le

/-- `gB m y ≤ gB m m` on `[0, m]`. -/
theorem gB_le_top (m : ℕ) (hm : 0 < m) {y : ℝ} (hy0 : 0 ≤ y) (hym : y ≤ m) :
    gB m y ≤ gB m m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht0 : 0 ≤ y / m := by positivity
  have ht1 : y / m ≤ 1 := by rw [div_le_one hmR]; exact hym
  rw [gB_top m hm, gB_eq]
  split_ifs with h
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (symG_le_two_log_two ht0 ht1) hmR.le
  · linarith [Real.sqrt_nonneg (m * symG (y / m)), Real.sqrt_nonneg (m * (2 * Real.log 2))]

/-! ### The continuous bound `|y − m/2 − (√m/2) g(y)| ≤ g(y)²` -/

theorem abs_sub_le_gB_sq (m : ℕ) (hm : 0 < m) {y : ℝ} (hy0 : 0 ≤ y) (hym : y ≤ m) :
    |y - m / 2 - Real.sqrt m / 2 * gB m y| ≤ gB m y ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set t : ℝ := y / m with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hmR]; exact hym
  have hyt : y = m * t := by rw [ht_def]; field_simp
  have hG : 0 ≤ symG t := symG_nonneg ht0 ht1
  set r : ℝ := Real.sqrt (symG t) with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = symG t := Real.sq_sqrt hG
  have hsqrt : Real.sqrt (m * symG t) = Real.sqrt m * r := Real.sqrt_mul hmR.le _
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmR.le
  have hgB := gB_eq m y
  rw [← ht_def, hsqrt] at hgB
  rcases le_or_gt ((m : ℝ) / 2) y with hly | hyl
  · -- `t ≥ ½`, `g = √m r`
    have ht : 1 / 2 ≤ t := by rw [ht_def, le_div_iff₀ hmR]; linarith
    have hg : gB m y = Real.sqrt m * r := by rw [hgB, if_pos hly]
    set b : ℝ := 2 * t - 1 with hb_def
    have hb0 : 0 ≤ b := by linarith
    have hb1 : b ≤ 1 := by linarith
    have h1 : b ^ 2 ≤ r ^ 2 := by rw [hr2, hb_def]; exact symG_ge_of_half_le ht ht1
    have h2 : b ≤ 1 / 2 → r ^ 2 - b ^ 2 ≤ 2 * b ^ 3 / 3 := by
      intro hb
      rw [hr2, hb_def]
      have := symG_sub_le ht (by linarith : t ≤ 3 / 4)
      have hb3 : 0 ≤ (2 * t - 1) ^ 3 * (3 - (2 * t - 1)) :=
        mul_nonneg (pow_nonneg hb0 3) (by linarith)
      nlinarith
    obtain ⟨hc1, hc2⟩ := sqrt_sub_bounds hb0 hb1 hr0 h1 h2
    rw [hg]
    have hexpr : y - m / 2 - Real.sqrt m / 2 * (Real.sqrt m * r) = m / 2 * (b - r) := by
      rw [hyt, hb_def]; linear_combination (-(r / 2)) * hss
    have hg2 : (Real.sqrt m * r) ^ 2 = m * r ^ 2 := by rw [mul_pow, Real.sq_sqrt hmR.le]
    rw [hexpr, hg2, abs_of_nonpos (by nlinarith)]
    nlinarith
  · -- `t < ½`, `g = −√m r`
    have ht : t < 1 / 2 := by rw [ht_def, div_lt_iff₀ hmR]; linarith
    have hg : gB m y = -(Real.sqrt m * r) := by rw [hgB, if_neg (not_le.mpr hyl)]
    set b : ℝ := 1 - 2 * t with hb_def
    have hb0 : 0 ≤ b := by linarith
    have hb1 : b ≤ 1 := by linarith
    have hsym : symG t = symG (1 - t) := (symG_symm t).symm
    have h1 : b ^ 2 ≤ r ^ 2 := by
      rw [hr2, hb_def, hsym]
      have := symG_ge_of_half_le (t := 1 - t) (by linarith) (by linarith)
      nlinarith
    have h2 : b ≤ 1 / 2 → r ^ 2 - b ^ 2 ≤ 2 * b ^ 3 / 3 := by
      intro hb
      rw [hr2, hb_def, hsym]
      have := symG_sub_le (t := 1 - t) (by linarith) (by linarith)
      have hb3 : 0 ≤ (2 * (1 - t) - 1) ^ 3 * (3 - (2 * (1 - t) - 1)) :=
        mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)
      nlinarith
    obtain ⟨hc1, hc2⟩ := sqrt_sub_bounds hb0 hb1 hr0 h1 h2
    rw [hg]
    have hexpr : y - m / 2 - Real.sqrt m / 2 * (-(Real.sqrt m * r)) = m / 2 * (r - b) := by
      rw [hyt, hb_def]; linear_combination (r / 2) * hss
    have hg2 : (-(Real.sqrt m * r)) ^ 2 = m * r ^ 2 := by
      rw [neg_sq, mul_pow, Real.sq_sqrt hmR.le]
    rw [hexpr, hg2, abs_of_nonneg (by nlinarith)]
    nlinarith

/-! ### The Bin(m,½) cdf and the localization (L) -/

/-- The Bin(m,½) cdf on `ℕ`: `binF m k = P(Bin(m,½) ≤ k)`. -/
noncomputable def binF (m k : ℕ) : ℝ := binCdf m (k + 1) (1 / 2)

theorem binCdf_eq_one_of_le (m k : ℕ) (hk : m + 1 ≤ k) (p : ℝ) : binCdf m k p = 1 := by
  rw [← binCdf_total m p]
  unfold binCdf
  symm
  apply Finset.sum_subset
    (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hk))
  intro j hj hj'
  rw [Finset.mem_range] at hj hj'
  unfold binTermP
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem binCdf_le_one (m k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : binCdf m k p ≤ 1 := by
  rcases le_or_gt k (m + 1) with h | h
  · rw [← binCdf_total m p]; exact binCdf_mono m hp0 hp1 h
  · rw [binCdf_eq_one_of_le m k h.le p]

theorem binF_monotone (m : ℕ) : Monotone (binF m) := fun _ _ hjk =>
  binCdf_mono m (by norm_num) (by norm_num) (Nat.succ_le_succ hjk)

theorem binF_nonneg (m k : ℕ) : 0 ≤ binF m k := binCdf_nonneg _ _ (by norm_num) (by norm_num)

theorem binF_le_one (m k : ℕ) : binF m k ≤ 1 := binCdf_le_one _ _ (by norm_num) (by norm_num)

theorem binF_top (m : ℕ) : binF m m = 1 := binCdf_total m _

theorem exists_binF_ge (m : ℕ) (z : ℝ) : ∃ k, stdNormalCdf z ≤ binF m k :=
  ⟨m, by rw [binF_top]; exact stdNormalCdf_le_one _⟩

/-- **(L)** for the symmetric binomial: if `q = natQuantile (binF m) (Φ z)` then `q ≤ m`,
`g(q−1) < z` when `q ≥ 1`, and `z ≤ g(q+1)` when `q + 1 ≤ m`. -/
theorem binomial_quantile_localization (m : ℕ) {z : ℝ} {q : ℕ}
    (hq : natQuantile (binF m) (stdNormalCdf z) = q) :
    q ≤ m ∧ (1 ≤ q → binSignedRoot m (q - 1) (1 / 2) < z) ∧
      (q + 1 ≤ m → z ≤ binSignedRoot m (q + 1) (1 / 2)) := by
  have hqm : q ≤ m := hq ▸ natQuantile_le_of_eq_one (binF_top m) (stdNormalCdf_le_one z)
  have hchar := (natQuantile_eq_iff (binF_monotone m) (exists_binF_ge m z)
    (stdNormalCdf_pos z) q).mp hq
  obtain ⟨h1, h2⟩ := hchar
  simp only [tail_succ] at h1
  have hΦq : stdNormalCdf z ≤ binF m q := by linarith
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨hqm, ?_, ?_⟩
  · intro hq1
    obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    simp only [tail_succ] at h2
    have hlt : binF m j < stdNormalCdf z := by linarith
    have hI := (binomial_intersection m j (by omega) hp0 hp1).2
    have : stdNormalCdf (binSignedRoot m j (1 / 2)) < stdNormalCdf z :=
      lt_of_le_of_lt hI (by unfold binF at hlt; exact hlt)
    simpa using stdNormalCdf_strictMono.lt_iff_lt.mp this
  · intro hq1
    have hI := (binomial_intersection m (q + 1) hq1 hp0 hp1).1
    have : stdNormalCdf z ≤ stdNormalCdf (binSignedRoot m (q + 1) (1 / 2)) :=
      hΦq.trans (by unfold binF at hΦq; exact hI)
    exact stdNormalCdf_strictMono.le_iff_le.mp this

/-! ### (BQ) -/

theorem binomial_quantile_bound_of_root (m : ℕ) (hm : 0 < m) {z : ℝ} {q : ℕ} {y : ℝ}
    (hy0 : 0 ≤ y) (hym : y ≤ m) (hroot : gB m y = z) (hqy : |(q : ℝ) - y| ≤ 1) :
    |(q : ℝ) - m / 2 - Real.sqrt m / 2 * z| ≤ 1 + z ^ 2 := by
  have h := abs_sub_le_gB_sq m hm hy0 hym
  rw [hroot] at h
  calc |(q : ℝ) - m / 2 - Real.sqrt m / 2 * z|
      = |((q : ℝ) - y) + (y - m / 2 - Real.sqrt m / 2 * z)| := by ring_nf
    _ ≤ |(q : ℝ) - y| + |y - m / 2 - Real.sqrt m / 2 * z| := abs_add_le _ _
    _ ≤ 1 + z ^ 2 := by linarith

/-- `1/2 ≤ log 2`. -/
theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- **(BQ)**: for every `m` and every real `z`, the symmetric binomial quantile
`q = F_{Bin(m,½)}^{-1}(Φ z)` satisfies `|q − m/2 − (√m/2) z| ≤ 1 + z²`. -/
theorem binomial_quantile_bound (m : ℕ) {z : ℝ} {q : ℕ}
    (hq : natQuantile (binF m) (stdNormalCdf z) = q) :
    |(q : ℝ) - m / 2 - Real.sqrt m / 2 * z| ≤ 1 + z ^ 2 := by
  obtain ⟨hqm, hlow, hup⟩ := binomial_quantile_localization m hq
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hq0 : q = 0 := by omega
    subst hq0
    simp
    positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hmR.le
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hsm : Real.sqrt m ≤ Real.sqrt (m * (2 * Real.log 2)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [half_le_log_two]
  by_cases hz0 : z < gB m 0
  · -- below the range: `q = 0`
    have hq0 : q = 0 := by
      by_contra hne
      have h1 := hlow (Nat.one_le_iff_ne_zero.mpr hne)
      rw [← gB_nat] at h1
      have := gB_zero_le m hm (by positivity : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))
        (by exact_mod_cast (by omega : q - 1 ≤ m))
      linarith
    subst hq0
    rw [gB_zero m hm] at hz0
    have hzneg : Real.sqrt m ≤ -z := by linarith
    simp only [Nat.cast_zero]
    have hpos : 0 ≤ (0 : ℝ) - m / 2 - Real.sqrt m / 2 * z := by nlinarith
    rw [abs_of_nonneg hpos]
    nlinarith [sq_nonneg (Real.sqrt m + z)]
  · push Not at hz0
    by_cases hzm : gB m m < z
    · -- above the range: `q = m`
      have hqm' : q = m := by
        by_contra hne
        have h1 := hup (by omega)
        rw [← gB_nat] at h1
        have := gB_le_top m hm (by positivity : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ))
          (by exact_mod_cast (by omega : q + 1 ≤ m))
        linarith
      rw [hqm']
      rw [gB_top m hm] at hzm
      have hzpos : Real.sqrt m ≤ z := by linarith
      have hneg : (m : ℝ) - m / 2 - Real.sqrt m / 2 * z ≤ 0 := by nlinarith
      rw [abs_of_nonpos hneg]
      nlinarith [sq_nonneg (Real.sqrt m - z)]
    · push Not at hzm
      -- the root lies in `[y₀, y₁]`, `y₀ = max (q−1) 0`, `y₁ = min (q+1) m`
      set y₀ : ℝ := max ((q : ℝ) - 1) 0 with hy₀
      set y₁ : ℝ := min ((q : ℝ) + 1) m with hy₁
      have hy₀0 : 0 ≤ y₀ := le_max_right _ _
      have hy₀q : (q : ℝ) - 1 ≤ y₀ := le_max_left _ _
      have hy₁q : y₁ ≤ (q : ℝ) + 1 := min_le_left _ _
      have hy₁m : y₁ ≤ m := min_le_right _ _
      have hqmR : (q : ℝ) ≤ m := by exact_mod_cast hqm
      have hy₀le : y₀ ≤ y₁ := by
        apply max_le
        · apply le_min <;> linarith
        · apply le_min <;> positivity
      have hgy₀ : gB m y₀ ≤ z := by
        rcases Nat.eq_zero_or_pos q with rfl | hqpos
        · have : y₀ = 0 := by rw [hy₀]; simp
          rw [this]; exact hz0
        · have h1 := hlow hqpos
          rw [← gB_nat] at h1
          have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
            rw [Nat.cast_sub hqpos]; simp
          have : y₀ = (q : ℝ) - 1 := by
            rw [hy₀]; apply max_eq_left
            have : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
            linarith
          rw [this, ← hcast]
          exact h1.le
      have hgy₁ : z ≤ gB m y₁ := by
        rcases hqm.lt_or_eq with hqlt | hqeq
        · have h1 := hup hqlt
          rw [← gB_nat] at h1
          have : y₁ = (q : ℝ) + 1 := by
            rw [hy₁]; apply min_eq_left
            exact_mod_cast hqlt
          rw [this]
          exact_mod_cast h1
        · have : y₁ = m := by
            rw [hy₁]; apply min_eq_right
            rw [hqeq]; linarith
          rw [this]; exact hzm
      have hivt := intermediate_value_Icc hy₀le (continuous_gB m hm).continuousOn
      obtain ⟨y, hy, hroot⟩ := hivt ⟨hgy₀, hgy₁⟩
      refine binomial_quantile_bound_of_root m hm (hy₀0.trans hy.1) (hy.2.trans hy₁m) hroot ?_
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]

/-! ### The coupling map and its law -/

/-- The Bin(m,½) quantile coupling map `z ↦ F_{Bin(m,½)}^{-1}(Φ z)`. -/
noncomputable def binCoupling (m : ℕ) (z : ℝ) : ℕ := natQuantile (binF m) (stdNormalCdf z)

theorem binCoupling_monotone (m : ℕ) : Monotone (binCoupling m) := by
  intro z z' hzz'
  unfold binCoupling
  have h1 : stdNormalCdf z' ≤ binF m (natQuantile (binF m) (stdNormalCdf z')) :=
    le_apply_natQuantile (exists_binF_ge m z')
  exact natQuantile_le_of_le ((stdNormalCdf_monotone hzz').trans h1)

theorem measurable_binCoupling (m : ℕ) : Measurable (binCoupling m) :=
  (binCoupling_monotone m).measurable

theorem binCoupling_le (m : ℕ) (z : ℝ) : binCoupling m z ≤ m :=
  natQuantile_le_of_eq_one (binF_top m) (stdNormalCdf_le_one z)

/-- (BQ) for the coupling map. -/
theorem abs_binCoupling_sub_le (m : ℕ) (z : ℝ) :
    |(binCoupling m z : ℝ) - m / 2 - Real.sqrt m / 2 * z| ≤ 1 + z ^ 2 :=
  binomial_quantile_bound m rfl

/-- The coupled count has the Bin(m,½) cdf: `P{Q ≤ k} = P(Bin(m,½) ≤ k)`. -/
theorem measure_binCoupling_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    (m k : ℕ) :
    P {ω | binCoupling m (Z ω) ≤ k} = ENNReal.ofReal (binCdf m (k + 1) (1 / 2)) :=
  measure_natQuantile_stdNormalCdf_le P hZ hlaw (binF_monotone m) (binF_nonneg m) (binF_le_one m)
    ⟨m, binF_top m⟩ k

end Ripple.Kurtz.StrongApprox
