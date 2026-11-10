import Ripple.Number.Hypergeometric.GaussPeriods

/-!
# Two hypergeometric transformations near `0`

* `gauss2F1_quarter_unique`: an analytic solution `g` of the `(1/4, 3/4; 1)` equation
  `x(1 − x)g″ + (1 − 2x)g′ − (3/16)g = 0` on a disc `|x| < r ≤ 1` with `g(0) = 1` is
  `₂F₁(1/4, 3/4; 1; x)`. Proof: for the Wronskian `W = g·H′ − g′·H` with `H = ₂F₁(1/4,3/4;1;·)`,
  `(x(1 − x)W)′ = 0` and `W(0) = 0` by the equation at `0`; so `W = 0`, `g/H` is constant near `0`,
  and the identity theorem extends `g = H` to the disc.
* `gauss2F1_quadratic`: `₂F₁(1/8, 3/8; 1; 4x(1 − x)) = ₂F₁(1/4, 3/4; 1; x)` for `|x| < 1/5`.
* `gauss2F1_cubic_pow_four`: `₂F₁(1/12, 5/12; 1; 27x(1 − x)²/(1 + 3x)³)⁴ = (1 + 3x)·₂F₁(1/4, 3/4; 1; x)⁴`
  for `|x| < 1/50` (the fourth power of `(1 + 3x)^{-1/4} ₂F₁(1/12,5/12;1;u(x)) = ₂F₁(1/4,3/4;1;x)`).
-/

namespace Ripple.Number.Hypergeometric

open Complex Filter Topology Metric

noncomputable section

theorem gauss2F1_hasDerivAt (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z :=
  (gauss2F1_hasDerivAt_of_norm_lt_one a b z hz).differentiableAt.hasDerivAt

theorem gauss2F1_differentiableOn (a b : ℂ) :
    DifferentiableOn ℂ (gauss2F1 a b 1) (ball (0 : ℂ) 1) := fun z hz =>
  (gauss2F1_hasDerivAt a b (mem_ball_zero_iff.mp hz)).differentiableAt.differentiableWithinAt

theorem gauss2F1_hasDerivAt_deriv (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (deriv (gauss2F1 a b 1)) (deriv (deriv (gauss2F1 a b 1)) z) z :=
  ((((gauss2F1_differentiableOn a b).deriv isOpen_ball) z (mem_ball_zero_iff.mpr hz)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))).hasDerivAt

theorem gauss2F1_ode (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (deriv (gauss2F1 a b 1)) z +
        (1 - (a + b + 1) * z) * deriv (gauss2F1 a b 1) z - a * b * gauss2F1 a b 1 z = 0 := by
  have h := gauss2F1_operator_eq_zero_of_norm_lt_one a b z hz
  unfold gauss2F1Operator at h
  exact h

theorem gauss2F1_zero (a b : ℂ) : gauss2F1 a b 1 0 = 1 := by
  rw [gauss2F1_one_eq_tsum, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

/-- **Uniqueness at `0` for the `(1/4, 3/4; 1)` equation.** -/
theorem gauss2F1_quarter_unique {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {g g1 g2 : ℂ → ℂ}
    (hg : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt g (g1 x) x)
    (hg1 : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt g1 (g2 x) x)
    (hode : ∀ x ∈ ball (0 : ℂ) r,
      x * (1 - x) * g2 x + (1 - 2 * x) * g1 x - 3 / 16 * g x = 0)
    (h0 : g 0 = 1) :
    ∀ x ∈ ball (0 : ℂ) r, g x = gauss2F1 (1 / 4) (3 / 4) 1 x := by
  have hB1 : ∀ x ∈ ball (0 : ℂ) r, ‖x‖ < 1 := fun x hx =>
    lt_of_lt_of_le (mem_ball_zero_iff.mp hx) hr1
  have hH : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt (gauss2F1 (1 / 4) (3 / 4) 1)
      (deriv (gauss2F1 (1 / 4) (3 / 4) 1) x) x := fun x hx => gauss2F1_hasDerivAt _ _ (hB1 x hx)
  have hH1 : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt (deriv (gauss2F1 (1 / 4) (3 / 4) 1))
      (deriv (deriv (gauss2F1 (1 / 4) (3 / 4) 1)) x) x := fun x hx =>
    gauss2F1_hasDerivAt_deriv _ _ (hB1 x hx)
  have hHode : ∀ x ∈ ball (0 : ℂ) r,
      x * (1 - x) * deriv (deriv (gauss2F1 (1 / 4) (3 / 4) 1)) x +
        (1 - 2 * x) * deriv (gauss2F1 (1 / 4) (3 / 4) 1) x -
        3 / 16 * gauss2F1 (1 / 4) (3 / 4) 1 x = 0 := fun x hx => by
    have h := gauss2F1_ode (1 / 4 : ℂ) (3 / 4) (hB1 x hx)
    linear_combination h
  have h0B : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  -- `V = x(1 − x)W` is constant, hence `0`
  have hVd : ∀ x ∈ ball (0 : ℂ) r, HasDerivAt (fun y => y * (1 - y) *
      (g y * deriv (gauss2F1 (1 / 4) (3 / 4) 1) y - g1 y * gauss2F1 (1 / 4) (3 / 4) 1 y)) 0 x := by
    intro x hx
    have hp : HasDerivAt (fun y : ℂ => y * (1 - y)) (1 * (1 - x) + x * (0 - 1)) x :=
      (hasDerivAt_id' x).fun_mul ((hasDerivAt_const x (1 : ℂ)).fun_sub (hasDerivAt_id' x))
    have h := hp.fun_mul (((hg x hx).fun_mul (hH1 x hx)).fun_sub ((hg1 x hx).fun_mul (hH x hx)))
    refine h.congr_deriv ?_
    linear_combination g x * hHode x hx - gauss2F1 (1 / 4) (3 / 4) 1 x * hode x hx
  have hVc : ∀ x ∈ ball (0 : ℂ) r, x * (1 - x) *
      (g x * deriv (gauss2F1 (1 / 4) (3 / 4) 1) x - g1 x * gauss2F1 (1 / 4) (3 / 4) 1 x) =
      0 * (1 - 0) * (g 0 * deriv (gauss2F1 (1 / 4) (3 / 4) 1) 0 -
        g1 0 * gauss2F1 (1 / 4) (3 / 4) 1 0) := fun x hx =>
    IsOpen.is_const_of_deriv_eq_zero isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
      (fun x hx => (hVd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hVd x hx).deriv) hx h0B
  have hW : ∀ x ∈ ball (0 : ℂ) r,
      g x * deriv (gauss2F1 (1 / 4) (3 / 4) 1) x - g1 x * gauss2F1 (1 / 4) (3 / 4) 1 x = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      linear_combination g 0 * hHode 0 h0B - gauss2F1 (1 / 4) (3 / 4) 1 0 * hode 0 h0B
    · have h := hVc x hx
      simp only [zero_mul] at h
      have h1 : (1 : ℂ) - x ≠ 0 := by
        intro h1
        have : ‖x‖ = 1 := by rw [← sub_eq_zero.mp h1, norm_one]
        linarith [hB1 x hx]
      exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hx0 h1)
  -- `g / H` is constant near `0`
  have hH0 : gauss2F1 (1 / 4 : ℂ) (3 / 4) 1 0 = 1 := gauss2F1_zero _ _
  obtain ⟨ρ, hρ, hρH⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hH 0 h0B).continuousAt.eventually_ne (by rw [hH0]; exact one_ne_zero))
  set ρ' := min ρ r with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ hr
  have hsub : ball (0 : ℂ) ρ' ⊆ ball (0 : ℂ) r := ball_subset_ball (min_le_right _ _)
  have hsubρ : ball (0 : ℂ) ρ' ⊆ ball (0 : ℂ) ρ := ball_subset_ball (min_le_left _ _)
  have hRd : ∀ x ∈ ball (0 : ℂ) ρ',
      HasDerivAt (fun y => g y / gauss2F1 (1 / 4) (3 / 4) 1 y) 0 x := by
    intro x hx
    have hHx := hρH x (hsubρ hx)
    have h := (hg x (hsub hx)).fun_div (hH x (hsub hx)) hHx
    refine h.congr_deriv ?_
    rw [div_eq_zero_iff]
    left
    linear_combination -hW x (hsub hx)
  have hRc : ∀ x ∈ ball (0 : ℂ) ρ', g x / gauss2F1 (1 / 4) (3 / 4) 1 x =
      g 0 / gauss2F1 (1 / 4) (3 / 4) 1 0 := fun x hx =>
    IsOpen.is_const_of_deriv_eq_zero isOpen_ball (convex_ball (0 : ℂ) ρ').isPreconnected
      (fun x hx => (hRd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hRd x hx).deriv) hx (mem_ball_self hρ'pos)
  have hloc : ∀ x ∈ ball (0 : ℂ) ρ', g x = gauss2F1 (1 / 4) (3 / 4) 1 x := by
    intro x hx
    have h := hRc x hx
    simp only [h0, hH0, div_one] at h
    have hHx := hρH x (hsubρ hx)
    rw [div_eq_one_iff_eq hHx] at h
    exact h
  -- identity theorem on the disc
  have hgA : AnalyticOnNhd ℂ g (ball (0 : ℂ) r) :=
    DifferentiableOn.analyticOnNhd (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
      isOpen_ball
  have hHA : AnalyticOnNhd ℂ (gauss2F1 (1 / 4) (3 / 4) 1) (ball (0 : ℂ) r) :=
    DifferentiableOn.analyticOnNhd (fun x hx => (hH x hx).differentiableAt.differentiableWithinAt)
      isOpen_ball
  have hev : g =ᶠ[𝓝 0] gauss2F1 (1 / 4) (3 / 4) 1 :=
    Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hρ'pos) hloc
  exact hgA.eqOn_of_preconnected_of_eventuallyEq hHA (convex_ball (0 : ℂ) r).isPreconnected h0B hev

/-! ### The quadratic transformation -/

theorem norm_quadArg_lt_one {x : ℂ} (hx : ‖x‖ < 1 / 5) : ‖4 * x * (1 - x)‖ < 1 := by
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  have hn := norm_nonneg x
  calc ‖4 * x * (1 - x)‖ = 4 * ‖x‖ * ‖1 - x‖ := by rw [norm_mul, norm_mul, h4]
    _ ≤ 4 * ‖x‖ * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by rw [norm_one])) (by positivity)
    _ < 1 := by nlinarith

/-- **Quadratic transformation**: `₂F₁(1/8, 3/8; 1; 4x(1 − x)) = ₂F₁(1/4, 3/4; 1; x)`. -/
theorem gauss2F1_quadratic {x : ℂ} (hx : ‖x‖ < 1 / 5) :
    gauss2F1 (1 / 8) (3 / 8) 1 (4 * x * (1 - x)) = gauss2F1 (1 / 4) (3 / 4) 1 x := by
  have hyd : ∀ x : ℂ, HasDerivAt (fun y : ℂ => 4 * y * (1 - y)) (4 - 8 * x) x := fun x =>
    (((hasDerivAt_id' x).const_mul (4 : ℂ)).fun_mul
      ((hasDerivAt_const x (1 : ℂ)).fun_sub (hasDerivAt_id' x))).congr_deriv (by ring)
  have hlin : ∀ x : ℂ, HasDerivAt (fun y : ℂ => 4 - 8 * y) (-8) x := fun x =>
    ((hasDerivAt_const x (4 : ℂ)).fun_sub ((hasDerivAt_id' x).const_mul (8 : ℂ))).congr_deriv
      (by ring)
  have hy : ∀ x ∈ ball (0 : ℂ) (1 / 5), ‖4 * x * (1 - x)‖ < 1 := fun x hx =>
    norm_quadArg_lt_one (mem_ball_zero_iff.mp hx)
  refine gauss2F1_quarter_unique (r := 1 / 5) (by norm_num) (by norm_num)
    (g := fun x => gauss2F1 (1 / 8) (3 / 8) 1 (4 * x * (1 - x)))
    (g1 := fun x => deriv (gauss2F1 (1 / 8) (3 / 8) 1) (4 * x * (1 - x)) * (4 - 8 * x))
    (g2 := fun x => deriv (deriv (gauss2F1 (1 / 8) (3 / 8) 1)) (4 * x * (1 - x)) * (4 - 8 * x) *
      (4 - 8 * x) + deriv (gauss2F1 (1 / 8) (3 / 8) 1) (4 * x * (1 - x)) * (-8))
    ?_ ?_ ?_ ?_ x (mem_ball_zero_iff.mpr hx)
  · intro x hx
    exact (gauss2F1_hasDerivAt _ _ (hy x hx)).comp x (hyd x)
  · intro x hx
    exact ((gauss2F1_hasDerivAt_deriv _ _ (hy x hx)).comp x (hyd x)).fun_mul (hlin x)
  · intro x hx
    have h := gauss2F1_ode (1 / 8 : ℂ) (3 / 8) (hy x hx)
    beta_reduce
    linear_combination 4 * h
  · change gauss2F1 (1 / 8) (3 / 8) 1 (4 * 0 * (1 - 0)) = 1
    rw [show (4 : ℂ) * 0 * (1 - 0) = 0 by ring]
    exact gauss2F1_zero _ _

/-! ### The cubic transformation -/

/-- The cubic argument `u(x) = 27x(1 − x)²/(1 + 3x)³`. -/
def cubicArg (x : ℂ) : ℂ := 27 * x * (1 - x) ^ 2 / (1 + 3 * x) ^ 3

/-- `u′(x) = 27(x − 1)(9x − 1)/(1 + 3x)⁴`. -/
def cubicArg1 (x : ℂ) : ℂ := 27 * (x - 1) * (9 * x - 1) / (1 + 3 * x) ^ 4

/-- `u″(x) = −54(27x² − 54x + 11)/(1 + 3x)⁵`. -/
def cubicArg2 (x : ℂ) : ℂ := -54 * (27 * x ^ 2 - 54 * x + 11) / (1 + 3 * x) ^ 5

section Cubic

variable {x : ℂ}

theorem one_add_three_mul_ne_zero (hx : ‖x‖ < 1 / 50) : 1 + 3 * x ≠ 0 := by
  intro h
  have h1 : x = -1 / 3 := by linear_combination h / 3
  rw [h1] at hx
  norm_num at hx

theorem one_add_three_mul_mem_slitPlane (hx : ‖x‖ < 1 / 50) : 1 + 3 * x ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : |x.re| ≤ ‖x‖ := Complex.abs_re_le_norm _
  have h2 := abs_le.mp h1
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero]
  linarith [h2.1]

theorem norm_cubicArg_lt_one (hx : ‖x‖ < 1 / 50) : ‖cubicArg x‖ < 1 := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hm : ‖1 - x‖ ≤ 1 + ‖x‖ := (norm_sub_le _ _).trans (by rw [norm_one])
  have hn : 1 - 3 * ‖x‖ ≤ ‖1 + 3 * x‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(3 * x))
    rw [sub_neg_eq_add, norm_one, norm_neg, norm_mul] at h
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3] at h
    linarith
  have hn0 : 0 < 1 - 3 * ‖x‖ := by linarith
  have h27 : ‖(27 : ℂ)‖ = 27 := by simp
  rw [cubicArg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, h27,
    div_lt_one (pow_pos (hn0.trans_le hn) 3)]
  have h1 : 27 * ‖x‖ * ‖1 - x‖ ^ 2 ≤ 27 * (1 / 50) * (51 / 50) ^ 2 := by
    have hm2 : ‖1 - x‖ ^ 2 ≤ (51 / 50) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    have h27x : 27 * ‖x‖ ≤ 27 * (1 / 50) := by linarith
    calc 27 * ‖x‖ * ‖1 - x‖ ^ 2 ≤ 27 * (1 / 50) * ‖1 - x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h27x (sq_nonneg _)
      _ ≤ 27 * (1 / 50) * (51 / 50) ^ 2 := mul_le_mul_of_nonneg_left hm2 (by norm_num)
  have h2 : (47 / 50 : ℝ) ^ 3 ≤ ‖1 + 3 * x‖ ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 3
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le (by norm_num) h2)

theorem hasDerivAt_cubicArg (hx : ‖x‖ < 1 / 50) : HasDerivAt cubicArg (cubicArg1 x) x := by
  have hw := one_add_three_mul_ne_zero hx
  have hn : HasDerivAt (fun y : ℂ => 27 * y * (1 - y) ^ 2)
      (27 * 1 * (1 - x) ^ 2 + 27 * x * (2 * (1 - x) * (0 - 1))) x := by
    have h := ((hasDerivAt_id' x).const_mul (27 : ℂ)).fun_mul
      (((hasDerivAt_const x (1 : ℂ)).fun_sub (hasDerivAt_id' x)).fun_pow 2)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hd : HasDerivAt (fun y : ℂ => (1 + 3 * y) ^ 3) (3 * (1 + 3 * x) ^ 2 * 3) x := by
    have h := ((hasDerivAt_const x (1 : ℂ)).fun_add ((hasDerivAt_id' x).const_mul (3 : ℂ))).fun_pow
      3
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  refine (hn.fun_div hd (pow_ne_zero 3 hw)).congr_deriv ?_
  rw [cubicArg1]
  field_simp
  ring

theorem hasDerivAt_cubicArg1 (hx : ‖x‖ < 1 / 50) : HasDerivAt cubicArg1 (cubicArg2 x) x := by
  have hw := one_add_three_mul_ne_zero hx
  have hn : HasDerivAt (fun y : ℂ => 27 * (y - 1) * (9 * y - 1))
      (27 * (9 * x - 1) + 27 * (x - 1) * 9) x := by
    have h := (((hasDerivAt_id' x).fun_sub (hasDerivAt_const x (1 : ℂ))).const_mul
      (27 : ℂ)).fun_mul (((hasDerivAt_id' x).const_mul (9 : ℂ)).fun_sub (hasDerivAt_const x (1 : ℂ)))
    refine h.congr_deriv ?_
    ring
  have hd : HasDerivAt (fun y : ℂ => (1 + 3 * y) ^ 4) (4 * (1 + 3 * x) ^ 3 * 3) x := by
    have h := ((hasDerivAt_const x (1 : ℂ)).fun_add ((hasDerivAt_id' x).const_mul (3 : ℂ))).fun_pow
      4
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  refine (hn.fun_div hd (pow_ne_zero 4 hw)).congr_deriv ?_
  rw [cubicArg2]
  field_simp
  ring

/-- `p(x) = (1 + 3x)^{−1/4}` and its derivative `−(3/4) p/(1 + 3x)`. -/
theorem hasDerivAt_cubicPow (hx : ‖x‖ < 1 / 50) :
    HasDerivAt (fun y : ℂ => (1 + 3 * y) ^ (-1 / 4 : ℂ))
      (-3 / 4 * (1 + 3 * x) ^ (-1 / 4 : ℂ) / (1 + 3 * x)) x := by
  have hw := one_add_three_mul_ne_zero hx
  have hl : HasDerivAt (fun y : ℂ => 1 + 3 * y) 3 x :=
    ((hasDerivAt_const x (1 : ℂ)).fun_add ((hasDerivAt_id' x).const_mul (3 : ℂ))).congr_deriv
      (by ring)
  refine (hl.cpow_const (one_add_three_mul_mem_slitPlane hx)).congr_deriv ?_
  rw [Complex.cpow_sub _ _ hw, Complex.cpow_one]
  ring

theorem hasDerivAt_cubicPow1 (hx : ‖x‖ < 1 / 50) :
    HasDerivAt (fun y : ℂ => -3 / 4 * (1 + 3 * y) ^ (-1 / 4 : ℂ) / (1 + 3 * y))
      (45 / 16 * (1 + 3 * x) ^ (-1 / 4 : ℂ) / (1 + 3 * x) ^ 2) x := by
  have hw := one_add_three_mul_ne_zero hx
  have hl : HasDerivAt (fun y : ℂ => 1 + 3 * y) 3 x :=
    ((hasDerivAt_const x (1 : ℂ)).fun_add ((hasDerivAt_id' x).const_mul (3 : ℂ))).congr_deriv
      (by ring)
  refine (((hasDerivAt_cubicPow hx).const_mul (-3 / 4 : ℂ)).fun_div hl hw).congr_deriv ?_
  field_simp
  ring

end Cubic

/-- **Cubic transformation** (fourth-power form):
`₂F₁(1/12, 5/12; 1; 27x(1 − x)²/(1 + 3x)³)⁴ = (1 + 3x)·₂F₁(1/4, 3/4; 1; x)⁴` for `|x| < 1/50`. -/
theorem gauss2F1_cubic_pow_four {x : ℂ} (hx : ‖x‖ < 1 / 50) :
    gauss2F1 (1 / 12) (5 / 12) 1 (cubicArg x) ^ 4 =
      (1 + 3 * x) * gauss2F1 (1 / 4) (3 / 4) 1 x ^ 4 := by
  have hB : ∀ y ∈ ball (0 : ℂ) (1 / 50), ‖y‖ < 1 / 50 := fun y hy => mem_ball_zero_iff.mp hy
  have heq := gauss2F1_quarter_unique (r := 1 / 50) (by norm_num) (by norm_num)
    (g := fun y => (1 + 3 * y) ^ (-1 / 4 : ℂ) * gauss2F1 (1 / 12) (5 / 12) 1 (cubicArg y))
    (g1 := fun y => -3 / 4 * (1 + 3 * y) ^ (-1 / 4 : ℂ) / (1 + 3 * y) *
        gauss2F1 (1 / 12) (5 / 12) 1 (cubicArg y) +
      (1 + 3 * y) ^ (-1 / 4 : ℂ) * (deriv (gauss2F1 (1 / 12) (5 / 12) 1) (cubicArg y) *
        cubicArg1 y))
    (g2 := fun y => (45 / 16 * (1 + 3 * y) ^ (-1 / 4 : ℂ) / (1 + 3 * y) ^ 2 *
          gauss2F1 (1 / 12) (5 / 12) 1 (cubicArg y) +
        -3 / 4 * (1 + 3 * y) ^ (-1 / 4 : ℂ) / (1 + 3 * y) *
          (deriv (gauss2F1 (1 / 12) (5 / 12) 1) (cubicArg y) * cubicArg1 y)) +
      (-3 / 4 * (1 + 3 * y) ^ (-1 / 4 : ℂ) / (1 + 3 * y) *
          (deriv (gauss2F1 (1 / 12) (5 / 12) 1) (cubicArg y) * cubicArg1 y) +
        (1 + 3 * y) ^ (-1 / 4 : ℂ) *
          (deriv (deriv (gauss2F1 (1 / 12) (5 / 12) 1)) (cubicArg y) * cubicArg1 y * cubicArg1 y +
            deriv (gauss2F1 (1 / 12) (5 / 12) 1) (cubicArg y) * cubicArg2 y)))
    ?_ ?_ ?_ ?_ x (mem_ball_zero_iff.mpr hx)
  · -- conclude from `p·F₁(u) = H` and `p⁴ = (1 + 3x)⁻¹`
    have hw := one_add_three_mul_ne_zero hx
    beta_reduce at heq
    rw [← heq, mul_pow, ← Complex.cpow_nat_mul,
      show ((4 : ℕ) : ℂ) * (-1 / 4) = -1 by norm_num, Complex.cpow_neg_one, ← mul_assoc,
      mul_inv_cancel₀ hw, one_mul]
  · intro y hy
    have hu := norm_cubicArg_lt_one (hB y hy)
    exact (hasDerivAt_cubicPow (hB y hy)).fun_mul
      ((gauss2F1_hasDerivAt (1 / 12 : ℂ) (5 / 12) hu).comp y (hasDerivAt_cubicArg (hB y hy)))
  · intro y hy
    have hu := norm_cubicArg_lt_one (hB y hy)
    have hF := (gauss2F1_hasDerivAt (1 / 12 : ℂ) (5 / 12) hu).comp y
      (hasDerivAt_cubicArg (hB y hy))
    have hF1 := (gauss2F1_hasDerivAt_deriv (1 / 12 : ℂ) (5 / 12) hu).comp y
      (hasDerivAt_cubicArg (hB y hy))
    exact ((hasDerivAt_cubicPow1 (hB y hy)).fun_mul hF).fun_add
      ((hasDerivAt_cubicPow (hB y hy)).fun_mul (hF1.fun_mul (hasDerivAt_cubicArg1 (hB y hy))))
  · intro y hy
    have hy' := hB y hy
    have hw := one_add_three_mul_ne_zero hy'
    have hF := gauss2F1_ode (1 / 12 : ℂ) (5 / 12) (norm_cubicArg_lt_one hy')
    beta_reduce
    generalize gauss2F1 (1 / 12) (5 / 12) 1 (cubicArg y) = F0 at hF ⊢
    generalize deriv (gauss2F1 (1 / 12) (5 / 12) 1) (cubicArg y) = F1 at hF ⊢
    generalize deriv (deriv (gauss2F1 (1 / 12) (5 / 12) 1)) (cubicArg y) = F2 at hF ⊢
    generalize (1 + 3 * y) ^ (-1 / 4 : ℂ) = P
    simp only [cubicArg, cubicArg1, cubicArg2, div_eq_mul_inv, ← inv_pow] at hF ⊢
    generalize hv : (1 + 3 * y)⁻¹ = v at hF ⊢
    have hv0 : (1 + 3 * y) * v = 1 := by rw [← hv]; exact mul_inv_cancel₀ hw
    linear_combination (27 * P * (1 - y) * v ^ 2) * hF + (-3 * P * (5*F0*v*y - 5*F0*v - F0 -
      1296*F1*v^4*y^3 + 3744*F1*v^4*y^2 - 2448*F1*v^4*y + 432*F1*v^3*y^2 - 288*F1*v^3*y -
      144*F1*v^3 + 144*F1*v^2*y - 144*F1*v^2 + 34992*F2*v^7*y^6 - 81648*F2*v^7*y^5 +
      38880*F2*v^7*y^4 + 23328*F2*v^7*y^3 - 11664*F2*v^7*y^2 - 3888*F2*v^7*y +
      11664*F2*v^6*y^5 - 31104*F2*v^6*y^4 + 23328*F2*v^6*y^3 - 3888*F2*v^6*y +
      3888*F2*v^5*y^4 - 11664*F2*v^5*y^3 + 11664*F2*v^5*y^2 - 3888*F2*v^5*y) / 16) * hv0
  · change (1 + 3 * 0) ^ (-1 / 4 : ℂ) * gauss2F1 (1 / 12) (5 / 12) 1 (cubicArg 0) = 1
    have h0 : cubicArg 0 = 0 := by simp [cubicArg]
    rw [h0, gauss2F1_zero, show (1 : ℂ) + 3 * 0 = 1 by ring, Complex.one_cpow, one_mul]

end

end Ripple.Number.Hypergeometric
