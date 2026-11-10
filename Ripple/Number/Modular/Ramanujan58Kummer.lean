import Ripple.Number.Modular.Ramanujan58Chart
import Ripple.Number.Hypergeometric.Transform58
import Ripple.Number.Milla.Kummer

/-!
# L58-7: the level-2 Kummer identity near `τ₅₈` and the premise of Ramanujan's formula

With `Z = 2E₂(2z) − E₂(z)`, `e = E₄(z)` and `x = (e − Z²)/(3Z²)` (`xk`): `E₄ = Z²(1 + 3x)`,
`1/J = 27x(1 − x)²/(1 + 3x)³` and `x₂ = 256/(T + 104) = 4x(1 − x)` (from `e + 4E₄(2z) = 5Z²` and
`E₆ = Z(4Z² − 3e)`). Milla's `E₄ = ₂F₁(1/12, 5/12; 1; 1/J)⁴` on `Im z > 5/4`, the cubic and the
quadratic transformations of `Transform58` give `Z² = ₂F₁(1/8, 3/8; 1; x₂)⁴` (`Z_sq_eq_gauss`).
At `τ₅₈`, `Z > 0` (real `E₂` bounds) and `₂F₁(1/8, 3/8; 1; 99⁻⁴) ≥ 1` is real, so
`Z = ₂F₁(1/8, 3/8; 1; x₂)²` near `τ₅₈`; the chain rule and `ramanujan58_cm_relation` give the
premise `ramanujanCM58GaussDerivativeCombination = 9801/(2√2π)` (`ramanujanCM58_evaluation`).
-/

namespace Ripple.Number.Modular

open Complex Filter Topology ModularForm EisensteinSeries E2StarCM163 Metric
open UpperHalfPlane hiding I
open scoped Real
open Ripple.Number.Hypergeometric

noncomputable section

/-! ### Real `E₂` bounds -/

/-- The real coefficients of `E₂`. -/
def e2c (n : ℕ) : ℝ := if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℝ)

theorem coeff_E2QExpansion_eq_e2c (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n E2QExpansion = (e2c n : ℂ) := by
  rw [coeff_E2QExpansion, e2c]
  split_ifs <;> push_cast <;> ring

theorem e2c_succ_ge (n : ℕ) : -24 * 4 ^ (n + 1) ≤ e2c (n + 1) := by
  unfold e2c
  rw [if_neg (Nat.succ_ne_zero n)]
  have h1 : ArithmeticFunction.sigma 1 (n + 1) ≤ (n + 1) ^ 2 :=
    ArithmeticFunction.sigma_le_pow_succ 1 (n + 1)
  have h2 : (n + 1) ^ 2 ≤ 4 ^ (n + 1) := by
    have h3 : (n + 1) ^ 2 ≤ (2 ^ (n + 1)) ^ 2 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 2
    calc (n + 1) ^ 2 ≤ (2 ^ (n + 1)) ^ 2 := h3
      _ = 4 ^ (n + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4 : (ArithmeticFunction.sigma 1 (n + 1) : ℝ) ≤ 4 ^ (n + 1) := by
    exact_mod_cast h1.trans h2
  linarith

theorem e2c_succ_nonpos (n : ℕ) : e2c (n + 1) ≤ 0 := by
  unfold e2c
  rw [if_neg (Nat.succ_ne_zero n)]
  have : (0 : ℝ) ≤ ArithmeticFunction.sigma 1 (n + 1) := Nat.cast_nonneg _
  linarith

/-- Tail bounds for a real `E₂` series at `0 ≤ x ≤ 1/32`. -/
theorem e2_series_bounds {x s : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 32)
    (hs : HasSum (fun n => e2c n * x ^ n) s) : 1 - 192 * x ≤ s ∧ s ≤ 1 := by
  have htail := (hasSum_nat_add_iff' 1).mpr hs
  have he0 : e2c 0 = 1 := by simp [e2c]
  simp only [Finset.sum_range_one, pow_zero, mul_one, he0] at htail
  have hup := hasSum_le (fun n => mul_nonpos_of_nonpos_of_nonneg (e2c_succ_nonpos n)
    (pow_nonneg hx0 _)) htail hasSum_zero
  have hr : 4 * x < 1 := by linarith
  have hgeo := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left (-96 * x)
  have hlow := hasSum_le (fun n => by
      have := e2c_succ_ge n
      calc -96 * x * (4 * x) ^ n = -24 * 4 ^ (n + 1) * x ^ (n + 1) := by ring
        _ ≤ e2c (n + 1) * x ^ (n + 1) := mul_le_mul_of_nonneg_right this (pow_nonneg hx0 _))
    hgeo htail
  have hinv : (1 - 4 * x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hb : -96 * x * 2 ≤ -96 * x * (1 - 4 * x)⁻¹ := by
    have : 0 ≤ 96 * x := by linarith
    nlinarith
  constructor <;> linarith

/-- `E₂(τ)` is real with the tail bounds when the nome is a real `x ∈ [0, 1/32]`. -/
theorem E2_real_bounds (τ : ℍ) {x : ℝ} (hq : Function.Periodic.qParam 1 (τ : ℂ) = x)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 32) :
    ∃ a : ℝ, E2 τ = a ∧ 1 - 192 * x ≤ a ∧ a ≤ 1 := by
  have hC := E2QExpansion_hasSum τ
  simp only [coeff_E2QExpansion_eq_e2c, hq] at hC
  have hC' : HasSum (fun n => ((e2c n * x ^ n : ℝ) : ℂ)) (E2 τ) := by
    simpa using hC
  have hR : Summable (fun n => e2c n * x ^ n) := Complex.summable_ofReal.mp hC'.summable
  refine ⟨∑' n, e2c n * x ^ n, ?_, e2_series_bounds hx0 hx1 hR.hasSum⟩
  exact hC'.unique (Complex.hasSum_ofReal.mpr hR.hasSum)

/-- `E₄(τ₅₈)`, `E₄(2τ₅₈)`, `E₂(τ₅₈)`, `E₂(2τ₅₈)` are real and within `10⁻³` of `1`. -/
theorem tau58_values : ∃ e f a b : ℝ, vE t58 = e ∧ vF t58 = f ∧ vA t58 = a ∧ vB t58 = b ∧
    1 ≤ e ∧ e ≤ 1 + 1 / 1000 ∧ 1 ≤ f ∧ f ≤ 1 + 1 / 1000 ∧ 1 - 1 / 1000 ≤ a ∧ a ≤ 1 ∧
    1 - 1 / 1000 ≤ b ∧ b ≤ 1 := by
  have hq0 := q58_pos
  have hq1 := q58_le
  obtain ⟨e, he, he1, he2⟩ := E4_real_bounds ramanujanTau58 qParam_tau58 hq0.le (by linarith)
  obtain ⟨a, ha, ha1, ha2⟩ := E2_real_bounds ramanujanTau58 qParam_tau58 hq0.le (by linarith)
  have hq2 : Function.Periodic.qParam 1 ((scaleGL 2 • ramanujanTau58 : ℍ) : ℂ) =
      ((q58 ^ 2 : ℝ) : ℂ) := by
    rw [qParam_scaleGL, qParam_tau58]
    push_cast
    ring
  have hqa : q58 ^ 2 ≤ q58 * (1 / 15000000000) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left hq1 hq0.le
  have hqs : q58 ^ 2 ≤ 1 / 32 := by nlinarith
  obtain ⟨f, hf, hf1, hf2⟩ := E4_real_bounds _ hq2 (by positivity) hqs
  obtain ⟨b, hb, hb1, hb2⟩ := E2_real_bounds _ hq2 (by positivity) hqs
  have hqb : (q58 ^ 2) ^ 2 ≤ q58 ^ 2 := by
    have h1 : q58 ^ 2 ≤ 1 := by linarith
    calc (q58 ^ 2) ^ 2 = q58 ^ 2 * q58 ^ 2 := sq _
      _ ≤ q58 ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = q58 ^ 2 := mul_one _
  have hq2n : 0 ≤ q58 ^ 2 := by positivity
  refine ⟨e, f, a, b, by rw [vE_eq, ofComplex_t58, he], by rw [vF_eq t58_im_pos, ofComplex_t58, hf],
    by rw [vA_eq, ofComplex_t58, ha], by rw [vB_eq t58_im_pos, ofComplex_t58, hb],
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ### `₂F₁(1/8, 3/8; 1; x)` is real for real `x` -/

/-- The real coefficients of `₂F₁(1/8, 3/8; 1; ·)`. -/
def r58 : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 / 8 + n) * (3 / 8 + n) / ((n : ℝ) + 1) ^ 2 * r58 n

theorem r58_nonneg (n : ℕ) : 0 ≤ r58 n := by
  induction n with
  | zero => simp [r58]
  | succ n ih =>
      simp only [r58]
      positivity

theorem gauss2F1Coeff_eighth (n : ℕ) :
    gauss2F1Coeff (1 / 8) (3 / 8) 1 n = (r58 n : ℂ) := by
  induction n with
  | zero => simp [r58]
  | succ n ih =>
      have h := gauss2F1Coeff_succ_one (1 / 8 : ℂ) (3 / 8) n
      have hn : ((n : ℂ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Nat.succ_ne_zero n)
      rw [ih] at h
      have h2 : gauss2F1Coeff (1 / 8) (3 / 8) 1 (n + 1) =
          (1 / 8 + n) * (3 / 8 + n) * (r58 n : ℂ) / ((n : ℂ) + 1) ^ 2 := by
        rw [eq_div_iff hn]
        linear_combination h
      rw [h2]
      simp only [r58]
      push_cast
      ring

theorem gauss2F1_eighth_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ φ : ℝ, gauss2F1 (1 / 8) (3 / 8) 1 (x : ℂ) = φ ∧ 1 ≤ φ := by
  have habc : ∀ kn : ℕ, (kn : ℂ) ≠ -(1 / 8) ∧ (kn : ℂ) ≠ -(3 / 8) ∧ (kn : ℂ) ≠ -(1 : ℂ) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      (have h' := congrArg Complex.re h; norm_num at h'; linarith)
  have hxn : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx0]; exact hx1
  have hS := (gauss2F1_summable_of_norm_lt_one (1 / 8 : ℂ) (3 / 8) hxn habc).hasSum
  rw [← gauss2F1_one_eq_tsum] at hS
  simp only [gauss2F1Coeff_eighth] at hS
  have hS' : HasSum (fun n => ((r58 n * x ^ n : ℝ) : ℂ)) (gauss2F1 (1 / 8) (3 / 8) 1 (x : ℂ)) := by
    simpa using hS
  have hR : Summable (fun n => r58 n * x ^ n) := Complex.summable_ofReal.mp hS'.summable
  refine ⟨∑' n, r58 n * x ^ n, hS'.unique (Complex.hasSum_ofReal.mpr hR.hasSum), ?_⟩
  have h := sum_le_hasSum (Finset.range 1)
    (fun i _ => mul_nonneg (r58_nonneg i) (pow_nonneg hx0 i)) hR.hasSum
  simpa [r58] using h

/-! ### The level-2 Kummer identity in the chart -/

/-- `x = (E₄ − Z²)/(3Z²)`, so that `E₄ = Z²(1 + 3x)` and `x₂ = 4x(1 − x)`. -/
def xk (z : ℂ) : ℂ := (vE z - cZ58 z ^ 2) / (3 * cZ58 z ^ 2)

theorem chart_level2 {z : ℂ} (hz : 0 < z.im) :
    vE z + 4 * vF z = 5 * cZ58 z ^ 2 ∧
      2 * vE6a z = 3 * cZ58 z * (4 * vF z - vE z) - 7 * cZ58 z ^ 3 := by
  have hZ := level2Z_apply (ofComplex z)
  rw [← vB_eq hz, ← vA_eq] at hZ
  have hJ1 := level2_E4_sum (ofComplex z)
  rw [← vF_eq hz, ← vE_eq, hZ] at hJ1
  have hJ2 := level2_E6 (ofComplex z)
  rw [← vF_eq hz, ← vE_eq, ← vE6a_eq, hZ] at hJ2
  exact ⟨hJ1, hJ2⟩

theorem chart_E6 {z : ℂ} (hz : 0 < z.im) :
    vE6a z = cZ58 z * (4 * cZ58 z ^ 2 - 3 * vE z) := by
  obtain ⟨hJ1, hJ2⟩ := chart_level2 hz
  linear_combination hJ2 / 2 + (3 * cZ58 z / 2) * hJ1

theorem cx258_eq {z : ℂ} (hz : 0 < z.im) (hQ : vQ0 z ≠ 0) (hZ : cZ58 z ≠ 0) :
    cx258 z = 4 * xk z * (1 - xk z) := by
  obtain ⟨hJ1, -⟩ := chart_level2 hz
  have hf : vF z = (5 * cZ58 z ^ 2 - vE z) / 4 := by linear_combination hJ1 / 4
  have hPQ : vP0 z + 104 * vQ0 z = 3600 * cZ58 z ^ 4 := by
    simp only [vP0, vQ0, l58P0, l58Q0]
    rw [hf]
    ring
  have hQv : vQ0 z = 25 * (vE z - cZ58 z ^ 2) * (4 * cZ58 z ^ 2 - vE z) / 4 := by
    simp only [vQ0, l58Q0]
    rw [hf]
    ring
  rw [cx258, cT58, div_add' _ _ _ hQ, div_div_eq_mul_div, hPQ, hQv, xk]
  field_simp
  ring

theorem one_add_three_xk {z : ℂ} (hZ : cZ58 z ≠ 0) : 1 + 3 * xk z = vE z / cZ58 z ^ 2 := by
  rw [xk]
  field_simp
  ring

/-- **`Z² = ₂F₁(1/8, 3/8; 1; x₂)⁴`** at every point of `Im z > 5/4` where `Z, E₄, Q ≠ 0` and
`|x| < 1/50`. -/
theorem Z_sq_eq_gauss {z : ℂ} (hz : 5 / 4 < z.im) (hZ : cZ58 z ≠ 0) (he : vE z ≠ 0)
    (hQ : vQ0 z ≠ 0) (hx : ‖xk z‖ < 1 / 50) :
    cZ58 z ^ 2 = gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 4 := by
  have hz0 : 0 < z.im := by linarith
  have hR : ofComplex z ∈ Milla.Region := by
    change (5 : ℝ) / 4 < (ofComplex z).im
    rw [← UpperHalfPlane.coe_im, coe_ofComplex58 hz0]
    exact hz
  have hM := Milla.E₄_eq_hyp2F1_pow_four hR
  have h1x := one_add_three_xk hZ
  have hJ : (Milla.J (ofComplex z))⁻¹ = cubicArg (xk z) := by
    rw [Milla.J, inv_div]
    change (vE z ^ 3 - vE6a z ^ 2) / vE z ^ 3 = _
    rw [chart_E6 hz0]
    have h2 : 1 - xk z = (4 * cZ58 z ^ 2 - vE z) / (3 * cZ58 z ^ 2) := by
      rw [xk]
      field_simp
      ring
    rw [cubicArg, h1x, h2, xk]
    field_simp
    ring
  rw [hJ] at hM
  have hC := gauss2F1_cubic_pow_four hx
  have hQd := gauss2F1_quadratic (lt_trans hx (by norm_num))
  have hE : vE z = (1 + 3 * xk z) * cZ58 z ^ 2 := by
    rw [h1x, div_mul_cancel₀ _ (pow_ne_zero 2 hZ)]
  have h1 : (1 + 3 * xk z) * cZ58 z ^ 2 =
      (1 + 3 * xk z) * gauss2F1 (1 / 4) (3 / 4) 1 (xk z) ^ 4 := by
    rw [← hE, ← hC]
    exact hM
  have h3x : 1 + 3 * xk z ≠ 0 := by
    rw [h1x]
    exact div_ne_zero he (pow_ne_zero 2 hZ)
  rw [mul_left_cancel₀ h3x h1, ← hQd, cx258_eq hz0 hQ hZ]

/-! ### At `τ₅₈` -/

theorem cx258_t58 : cx258 t58 = 1 / 99 ^ 4 := by
  rw [cx258, cT58_t58]
  norm_num

theorem t58_im_gt : 5 / 4 < t58.im := by
  have h : t58.im = Real.sqrt 58 / 2 := ramanujanTau58_im
  rw [h]
  have : (5 / 2 : ℝ) < Real.sqrt 58 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

theorem continuousAt_xk {z : ℂ} (hz : 0 < z.im) (hZ : cZ58 z ≠ 0) : ContinuousAt xk z := by
  have hE := (hasDerivAt_vE hz).continuousAt
  have hZc := (hasDerivAt_cZ58 hz).continuousAt
  exact (hE.sub (hZc.pow 2)).div (continuousAt_const.mul (hZc.pow 2))
    (mul_ne_zero three_ne_zero (pow_ne_zero 2 hZ))

/-- **The premise of Ramanujan's 1914 formula**:
`1103 F(99⁻⁴)² + 26390·99⁻⁴·2F(99⁻⁴)F′(99⁻⁴) = 9801/(2√2π)` for `F = ₂F₁(1/8, 3/8; 1; ·)`. -/
theorem ramanujanCM58_evaluation :
    Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
  obtain ⟨e, f, a, b, he, hf, ha, hb, he1, he2, hf1, hf2, ha1, ha2, hb1, hb2⟩ := tau58_values
  have hw := t58_im_pos
  have hQ := vQ0_t58_ne_zero
  have hT104 : cT58 t58 + 104 ≠ 0 := by
    rw [cT58_t58]
    norm_num
  -- `Z(τ₅₈) = 2b − a > 0`
  have hZt : cZ58 t58 = ((2 * b - a : ℝ) : ℂ) := by
    simp only [cZ58]
    rw [ha, hb]
    push_cast
    ring
  have hZr1 : 998 / 1000 ≤ 2 * b - a := by linarith
  have hZr2 : 2 * b - a ≤ 1001 / 1000 := by linarith
  have hZ0 : cZ58 t58 ≠ 0 := by
    rw [hZt]
    exact_mod_cast (show (0 : ℝ) < 2 * b - a by linarith).ne'
  have he0 : vE t58 ≠ 0 := by
    rw [he]
    exact_mod_cast (show (0 : ℝ) < e by linarith).ne'
  -- `|x(τ₅₈)| < 1/50`
  have hxt : ‖xk t58‖ < 1 / 50 := by
    have hxr : xk t58 = (((e - (2 * b - a) ^ 2) / (3 * (2 * b - a) ^ 2) : ℝ) : ℂ) := by
      rw [xk, he, hZt]
      push_cast
      ring
    have hsq1 : (998 / 1000 : ℝ) ^ 2 ≤ (2 * b - a) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hZr1 2
    have hsq2 : (2 * b - a) ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hZr2 2
    have hpos : (0 : ℝ) < 3 * (2 * b - a) ^ 2 := by nlinarith
    rw [hxr, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor
    · rw [lt_div_iff₀ hpos]
      nlinarith
    · rw [div_lt_iff₀ hpos]
      nlinarith
  -- `Z² = F(x₂)⁴` near `τ₅₈`
  have hev : ∀ᶠ z in 𝓝 t58, 5 / 4 < z.im ∧ cZ58 z ≠ 0 ∧ vE z ≠ 0 ∧ vQ0 z ≠ 0 ∧
      ‖xk z‖ < 1 / 50 := by
    have h1 : ∀ᶠ z in 𝓝 t58, 5 / 4 < z.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds t58_im_gt
    have h2 := (hasDerivAt_cZ58 hw).continuousAt.eventually_ne hZ0
    have h3 := (hasDerivAt_vE hw).continuousAt.eventually_ne he0
    have h4 := (hasDerivAt_vQ0 hw).continuousAt.eventually_ne hQ
    have h5 := (continuousAt_xk hw hZ0).norm.eventually_lt continuousAt_const hxt
    filter_upwards [h1, h2, h3, h4, h5] with z k1 k2 k3 k4 k5
    exact ⟨k1, k2, k3, k4, k5⟩
  have hsq : ∀ᶠ z in 𝓝 t58, cZ58 z ^ 2 = gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 4 :=
    hev.mono fun z h => Z_sq_eq_gauss h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  -- the sign: `F(99⁻⁴)` is real and `≥ 1`
  obtain ⟨φ, hφ, hφ1⟩ := gauss2F1_eighth_real (x := 1 / 99 ^ 4) (by positivity) (by norm_num)
  have hφ' : gauss2F1 (1 / 8) (3 / 8) 1 (1 / 99 ^ 4) = (φ : ℂ) := by
    rw [← hφ]
    norm_num
  have hx0n : ‖(1 / 99 ^ 4 : ℂ)‖ < 1 := by norm_num
  have hFd : HasDerivAt (gauss2F1 (1 / 8) (3 / 8) 1)
      (deriv (gauss2F1 (1 / 8) (3 / 8) 1) (cx258 t58)) (cx258 t58) := by
    rw [cx258_t58]
    exact gauss2F1_hasDerivAt _ _ hx0n
  have hxd := hasDerivAt_cx258 hw hQ hT104
  have hFx := hFd.comp t58 hxd
  have hG : ContinuousAt (fun z => cZ58 z + gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 2) t58 :=
    (hasDerivAt_cZ58 hw).continuousAt.add (hFx.continuousAt.pow 2)
  have hGt : cZ58 t58 + gauss2F1 (1 / 8) (3 / 8) 1 (cx258 t58) ^ 2 ≠ 0 := by
    rw [hZt, cx258_t58, hφ']
    exact_mod_cast (show (0 : ℝ) < 2 * b - a + φ ^ 2 by nlinarith).ne'
  have hZF : cZ58 =ᶠ[𝓝 t58] fun z => gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 2 := by
    filter_upwards [hsq, hG.eventually_ne hGt] with z k1 k2
    have hm : (cZ58 z - gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 2) *
        (cZ58 z + gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 2) = 0 := by
      linear_combination k1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right k2)
  -- values and derivatives at `τ₅₈`
  have hZv : cZ58 t58 = gauss2F1 (1 / 8) (3 / 8) 1 (1 / 99 ^ 4) ^ 2 := by
    have h := hZF.eq_of_nhds
    beta_reduce at h
    rw [h, cx258_t58]
  have hZd : deriv cZ58 t58 = 2 * gauss2F1 (1 / 8) (3 / 8) 1 (1 / 99 ^ 4) *
      deriv (gauss2F1 (1 / 8) (3 / 8) 1) (1 / 99 ^ 4) * deriv cx258 t58 := by
    have hd2 : HasDerivAt (fun z => gauss2F1 (1 / 8) (3 / 8) 1 (cx258 z) ^ 2) _ t58 :=
      hFx.fun_pow 2
    rw [hZF.deriv_eq, hd2.deriv, hxd.deriv]
    simp only [Function.comp_apply, cx258_t58, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hxd0 : deriv cx258 t58 ≠ 0 := by
    rw [hxd.deriv]
    exact div_ne_zero (mul_ne_zero (by norm_num) cT58D_t58_ne_zero) (pow_ne_zero 2 hT104)
  have key : Hypergeometric.ramanujanCM58GaussDerivativeCombination =
      1103 * cZ58 t58 + 26390 * (1 / 99 ^ 4) * deriv cZ58 t58 / deriv cx258 t58 := by
    rw [Hypergeometric.ramanujanCM58GaussDerivativeCombination, hZv, hZd, mul_div_assoc,
      mul_div_cancel_right₀ _ hxd0]
  rw [key, ramanujan58_cm_relation]

end

end Ripple.Number.Modular
