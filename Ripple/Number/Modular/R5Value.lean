import Ripple.Number.Modular.R5Root
import Ripple.Number.Modular.Level58Fixed
import Ripple.Number.Modular.SingularModuli

/-!
# R5: `T(τ₅₈) = T₀`

At `τ₅₈ = i√58/2` (`ramanujanTau58`) the nome `q = e^{−π√58}` is real and below
`1/(1.5·10¹⁰)`. Crude tail bounds for `E₄` give `E₄(τ₅₈) = e`, `E₄(2τ₅₈) = f` real with
`e ∈ [1 + 240q, 1 + 240q + 122880q²]`, `f ∈ [1, 1 + 240q² + 122880q⁴]`, hence
`Q = (e − f)(16f − e) ∈ (0, 3601q]`, `P ≥ 3599` and `T = P/Q ≥ 1.1·10¹⁰`. The fixing map
`μ(τ) = −29/(2τ)` fixes `τ₅₈`, so `T(τ₅₈)` is a real root of `Ψ₂₉(X, X)` above `1.1·10¹⁰`, which is
`T₀ = 256·99⁴ − 104` (`psi29_diag_eq_T0`). Equivalently `x₂(τ₅₈) = 256/(T + 104) = 1/99⁴`.
-/

namespace Ripple.Number.Modular

open Finset UpperHalfPlane

/-- The real coefficients of `E₄`. -/
noncomputable def e4c (n : ℕ) : ℝ :=
  if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℝ)

theorem coeff_E4QExpansion_eq_e4c (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n E4QExpansion = (e4c n : ℂ) := by
  rw [coeff_E4QExpansion, e4c]
  split_ifs <;> push_cast <;> ring

theorem e4c_nonneg (n : ℕ) : 0 ≤ e4c n := by
  unfold e4c
  split_ifs <;> positivity

theorem e4c_le (n : ℕ) : e4c n ≤ 240 * 16 ^ n := by
  unfold e4c
  split_ifs with h
  · subst h
    norm_num
  · have h1 : ArithmeticFunction.sigma 3 n ≤ n ^ 4 := ArithmeticFunction.sigma_le_pow_succ 3 n
    have h2 : n ^ 4 ≤ 16 ^ n := by
      have h3 : n ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
      calc n ^ 4 ≤ (2 ^ n) ^ 4 := h3
        _ = 16 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h4 : (ArithmeticFunction.sigma 3 n : ℝ) ≤ 16 ^ n := by exact_mod_cast h1.trans h2
    linarith

theorem e4c_one : e4c 1 = 240 := by
  simp [e4c, ArithmeticFunction.sigma_apply]

/-- Tail bounds for a real `E₄` series at `0 ≤ x ≤ 1/32`. -/
theorem e4_series_bounds {x s : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 32)
    (hs : HasSum (fun n => e4c n * x ^ n) s) :
    1 + 240 * x ≤ s ∧ s ≤ 1 + 240 * x + 122880 * x ^ 2 := by
  have htail := (hasSum_nat_add_iff' 2).mpr hs
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one] at htail
  have he0 : e4c 0 = 1 := by simp [e4c]
  rw [he0, e4c_one] at htail
  have hnn : 0 ≤ s - (1 * 1 + 240 * x) :=
    htail.nonneg fun n => mul_nonneg (e4c_nonneg _) (pow_nonneg hx0 _)
  have hr : 16 * x < 1 := by linarith
  have hgeo := ((hasSum_geometric_of_lt_one (by positivity) hr).mul_left (240 * (16 * x) ^ 2))
  have hle := hasSum_le (fun n => by
      have := e4c_le (n + 2)
      calc e4c (n + 2) * x ^ (n + 2) ≤ 240 * 16 ^ (n + 2) * x ^ (n + 2) :=
            mul_le_mul_of_nonneg_right this (pow_nonneg hx0 _)
        _ = 240 * (16 * x) ^ 2 * (16 * x) ^ n := by ring) htail hgeo
  have hinv : (1 - 16 * x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hb : 240 * (16 * x) ^ 2 * (1 - 16 * x)⁻¹ ≤ 240 * (16 * x) ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  constructor <;> nlinarith

/-- `E₄(τ)` is real with the tail bounds when the nome is a real `x ∈ [0, 1/32]`. -/
theorem E4_real_bounds (τ : ℍ) {x : ℝ} (hq : Function.Periodic.qParam 1 (τ : ℂ) = x)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 32) :
    ∃ e : ℝ, E4 τ = e ∧ 1 + 240 * x ≤ e ∧ e ≤ 1 + 240 * x + 122880 * x ^ 2 := by
  have hC := E4QExpansion_hasSum τ
  simp only [coeff_E4QExpansion_eq_e4c, hq] at hC
  have hC' : HasSum (fun n => ((e4c n * x ^ n : ℝ) : ℂ)) (E4 τ) := by
    simpa using hC
  have hR : Summable (fun n => e4c n * x ^ n) := Complex.summable_ofReal.mp hC'.summable
  refine ⟨∑' n, e4c n * x ^ n, ?_, e4_series_bounds hx0 hx1 hR.hasSum⟩
  exact hC'.unique (Complex.hasSum_ofReal.mpr hR.hasSum)

/-- The nome at `τ₅₈`. -/
noncomputable def q58 : ℝ := Real.exp (-Real.pi * Real.sqrt 58)

theorem qParam_tau58 : Function.Periodic.qParam 1 (ramanujanTau58 : ℂ) = q58 := by
  rw [Function.Periodic.qParam, q58, ← ramanujanTau58_q]
  congr 1
  push_cast
  ring

theorem q58_pos : 0 < q58 := Real.exp_pos _

theorem q58_le : q58 ≤ 1 / 15000000000 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hs : (7.6 : ℝ) < Real.sqrt 58 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hx : (23.8 : ℝ) ≤ Real.pi * Real.sqrt 58 := by nlinarith
  have he1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h23 : (2.7 : ℝ) ^ 23 < Real.exp 23 := by
    rw [show (23 : ℝ) = (23 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  have h08 : (1.8 : ℝ) ≤ Real.exp 0.8 := by
    have := Real.add_one_le_exp (0.8 : ℝ)
    linarith
  have hE : (15000000000 : ℝ) ≤ Real.exp (Real.pi * Real.sqrt 58) := by
    have h1 : Real.exp 23.8 = Real.exp 23 * Real.exp 0.8 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : Real.exp 23.8 ≤ Real.exp (Real.pi * Real.sqrt 58) := Real.exp_le_exp.mpr hx
    have h3 : (15000000000 : ℝ) ≤ (2.7 : ℝ) ^ 23 * 1.8 := by norm_num
    have h4 : (2.7 : ℝ) ^ 23 * 1.8 ≤ Real.exp 23 * Real.exp 0.8 :=
      mul_le_mul h23.le h08 (by norm_num) (Real.exp_pos _).le
    linarith
  rw [q58, neg_mul, Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hE

theorem mu58_tau58 : mu58 ramanujanTau58 = ramanujanTau58 := by
  apply UpperHalfPlane.ext
  rw [coe_mu58]
  have h0 : (ramanujanTau58 : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have hq := ramanujanTau58_reduced_form_quadratic
  field_simp
  linear_combination -hq

/-- The real values `e = E₄(τ₅₈)`, `f = E₄(2τ₅₈)` and the bound `P(e,f) ≥ 1.1·10¹⁰ Q(e,f) > 0`. -/
theorem tau58_PQ :
    ∃ e f : ℝ, E4 ramanujanTau58 = e ∧ E4 (scaleGL 2 • ramanujanTau58) = f ∧
      0 < -e ^ 2 + 17 * e * f - 16 * f ^ 2 ∧
      11000000000 * (-e ^ 2 + 17 * e * f - 16 * f ^ 2) ≤
        248 * e ^ 2 - 616 * e * f + 3968 * f ^ 2 := by
  have hq0 := q58_pos
  have hq1 := q58_le
  obtain ⟨e, he, he1, he2⟩ := E4_real_bounds ramanujanTau58 qParam_tau58 hq0.le (by linarith)
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
  have hqb : (q58 ^ 2) ^ 2 ≤ q58 ^ 2 := by
    have h1 : q58 ^ 2 ≤ 1 := by linarith
    calc (q58 ^ 2) ^ 2 = q58 ^ 2 * q58 ^ 2 := sq _
      _ ≤ q58 ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = q58 ^ 2 := mul_one _
  have hq2n : 0 ≤ q58 ^ 2 := by positivity
  have hQ : -e ^ 2 + 17 * e * f - 16 * f ^ 2 = (e - f) * (16 * f - e) := by ring
  have hef : 0 < e - f := by linarith
  have hfe : 0 < 16 * f - e := by linarith
  refine ⟨e, f, he, hf, by rw [hQ]; exact mul_pos hef hfe, ?_⟩
  have hefu : e - f ≤ 240 * q58 + 122880 * q58 ^ 2 := by linarith
  have hfeu : 16 * f - e ≤ 15 := by linarith
  have hQle : -e ^ 2 + 17 * e * f - 16 * f ^ 2 ≤ 15 * (240 * q58 + 122880 * q58 ^ 2) := by
    rw [hQ]
    calc (e - f) * (16 * f - e) ≤ (240 * q58 + 122880 * q58 ^ 2) * 15 :=
          mul_le_mul hefu hfeu hfe.le (by positivity)
      _ = 15 * (240 * q58 + 122880 * q58 ^ 2) := by ring
  have hP : 3599 ≤ 248 * e ^ 2 - 616 * e * f + 3968 * f ^ 2 := by
    have h1 : 248 * e ^ 2 - 616 * e * f + 3968 * f ^ 2 =
        248 * (e - f) ^ 2 + f * (3720 * f - 120 * e) := by ring
    have h2 : 3599 ≤ 3720 * f - 120 * e := by linarith
    have h3 : 3720 * f - 120 * e ≤ f * (3720 * f - 120 * e) := by
      nlinarith [mul_nonneg (show 0 ≤ f - 1 by linarith) (show 0 ≤ 3720 * f - 120 * e by linarith)]
    nlinarith [sq_nonneg (e - f)]
  linarith

/-- **R5.** `T(τ₅₈) = T₀ = 256·99⁴ − 104`. -/
theorem hauptT58_tau58 : hauptT58 ramanujanTau58 = 256 * 99 ^ 4 - 104 := by
  obtain ⟨e, f, he, hf, hQpos, hPQ⟩ := tau58_PQ
  have hQC : level2Q (E4 ramanujanTau58) (E4 (scaleGL 2 • ramanujanTau58)) =
      ((-e ^ 2 + 17 * e * f - 16 * f ^ 2 : ℝ) : ℂ) := by
    rw [he, hf]
    simp only [level2Q, quadForm]
    push_cast
    ring
  have hPC : level2P (E4 ramanujanTau58) (E4 (scaleGL 2 • ramanujanTau58)) =
      ((248 * e ^ 2 - 616 * e * f + 3968 * f ^ 2 : ℝ) : ℂ) := by
    rw [he, hf]
    simp only [level2P, quadForm]
    push_cast
    ring
  set r : ℝ := (248 * e ^ 2 - 616 * e * f + 3968 * f ^ 2) / (-e ^ 2 + 17 * e * f - 16 * f ^ 2)
    with hr
  have hT : hauptT58 ramanujanTau58 = (r : ℂ) := by
    rw [hauptT58, hPC, hQC, hr]
    push_cast
    rfl
  have hQ : level2Q (E4 ramanujanTau58) (E4 (scaleGL 2 • ramanujanTau58)) ≠ 0 := by
    rw [hQC]
    exact_mod_cast hQpos.ne'
  have h := psi29_mu58_equation ramanujanTau58 hQ (by rw [mu58_tau58]; exact hQ)
  rw [mu58_tau58, hT] at h
  have hr1 : (11000000000 : ℝ) ≤ r := by
    rw [hr, le_div_iff₀ hQpos]
    exact hPQ
  rw [hT, psi29_diag_eq_T0 hr1 h]
  push_cast
  ring

/-- **R5**, Ramanujan's singular value: `x₂(τ₅₈) = 256/(T(τ₅₈) + 104) = 1/99⁴`. -/
theorem x2_tau58 : 256 / (hauptT58 ramanujanTau58 + 104) = 1 / 99 ^ 4 := by
  rw [hauptT58_tau58]
  norm_num

end Ripple.Number.Modular
