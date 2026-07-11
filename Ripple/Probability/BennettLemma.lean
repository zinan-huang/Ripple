/-
  Ripple.Probability.BennettLemma — Bennett/Bernstein One-Step MGF Bound

  The core analytical inequality for Freedman's martingale concentration:
    exp(t*d) ≤ 1 + t*d + ψ(t,c)·d²   for |d| ≤ c
  where ψ(t,c) = t²/(2(1 - t*c/3)).
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Ripple.Probability

open Real Set

/-! ## Bennett's φ function -/

noncomputable def bennett_phi (y : ℝ) : ℝ :=
  if y = 0 then 1 / 2 else (exp y - 1 - y) / y ^ 2

theorem bennett_phi_nonneg (y : ℝ) : 0 ≤ bennett_phi y := by
  unfold bennett_phi
  split_ifs with h
  · positivity
  · apply div_nonneg
    · linarith [add_one_le_exp y]
    · positivity

private lemma bennett_aux_deriv1_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x - 1) * exp x + 1 := by
  have hmono : MonotoneOn (fun x : ℝ => (x - 1) * exp x + 1) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro z hz
      have hzpos : 0 < z := by simpa [interior_Ici] using hz
      have hderiv :
          deriv (fun x : ℝ => (x - 1) * exp x + 1) z = z * exp z := by
        simp [Real.deriv_exp]
        ring_nf
      rw [hderiv]
      exact mul_nonneg hzpos.le (le_of_lt (exp_pos z))
  have h := hmono (by simp) hx hx
  simpa using h

private lemma bennett_aux_deriv2_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x - 2) * exp x + x + 2 := by
  have hmono : MonotoneOn (fun x : ℝ => (x - 2) * exp x + x + 2) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro z hz
      have hz0 : 0 ≤ z := by
        have : 0 < z := by simpa [interior_Ici] using hz
        exact this.le
      have hderiv :
          deriv (fun x : ℝ => (x - 2) * exp x + x + 2) z =
            (z - 1) * exp z + 1 := by
        rw [deriv_fun_add]
        · rw [deriv_fun_add]
          · rw [deriv_fun_mul]
            · simp [Real.deriv_exp]
              ring
            · fun_prop
            · fun_prop
          · fun_prop
          · fun_prop
        · fun_prop
        · fun_prop
      rw [hderiv]
      exact bennett_aux_deriv1_nonneg hz0
  have h := hmono (by simp) hx hx
  simpa using h

private lemma bennett_q_mono :
    MonotoneOn (fun x : ℝ => (exp x - 1 - x) / x ^ 2) (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ)) ?_ ?_ ?_
  · refine ContinuousOn.div₀ ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero 2 (ne_of_gt hx)
  · refine DifferentiableOn.fun_div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      have hx0 : 0 < x := by simpa [interior_Ioi] using hx
      exact pow_ne_zero 2 (ne_of_gt hx0)
  · intro z hz
    have hzpos : 0 < z := by simpa [interior_Ioi] using hz
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hderiv :
        deriv (fun x : ℝ => (exp x - 1 - x) / x ^ 2) z =
          ((z - 2) * exp z + z + 2) / z ^ 3 := by
      have hsq_deriv : deriv (fun x : ℝ => x ^ 2) z = 2 * z := by
        rw [deriv_pow_field]
        ring
      rw [deriv_fun_div]
      · simp [Real.deriv_exp, hsq_deriv]
        field_simp [hz0]
        ring
      · fun_prop
      · fun_prop
      · exact pow_ne_zero 2 hz0
    rw [hderiv]
    exact div_nonneg (bennett_aux_deriv2_nonneg hzpos.le) (by positivity)

private lemma bennett_phi_half_le {y : ℝ} (hy : 0 ≤ y) :
    (1 : ℝ) / 2 ≤ bennett_phi y := by
  unfold bennett_phi
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [if_neg hy0]
    have hquad := Real.quadratic_le_exp_of_nonneg hy
    have hnum : y ^ 2 / 2 ≤ exp y - 1 - y := by linarith
    have hdiv := div_le_div_of_nonneg_right hnum (sq_nonneg y)
    field_simp [hy0] at hdiv ⊢
    nlinarith

private lemma exp_neg_quadratic_remainder {z : ℝ} (hz : 0 ≤ z) :
    exp (-z) - 1 + z ≤ z ^ 2 / 2 := by
  have hmono : MonotoneOn (fun x : ℝ => 1 - x + x ^ 2 / 2 - exp (-x)) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      have hderiv :
          deriv (fun x : ℝ => 1 - x + x ^ 2 / 2 - exp (-x)) x =
            -1 + x + exp (-x) := by
        have hexp_deriv : deriv (fun y : ℝ => exp (-y)) x = - exp (-x) := by
          rw [_root_.deriv_exp (show DifferentiableAt ℝ (fun y : ℝ => -y) x by fun_prop)]
          simp
        have hsq_deriv : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
          rw [deriv_pow_field]
          ring
        rw [deriv_fun_sub]
        · rw [deriv_fun_add]
          · rw [deriv_fun_sub]
            · simp [hexp_deriv, hsq_deriv]
            · fun_prop
            · fun_prop
          · fun_prop
          · fun_prop
        · fun_prop
        · fun_prop
      rw [hderiv]
      linarith [Real.one_sub_le_exp_neg x]
  have h := hmono (by simp) hz hz
  simp at h
  linarith

private lemma bennett_phi_pos_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    bennett_phi u ≤ bennett_phi v := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  unfold bennett_phi
  rw [if_neg hu.ne', if_neg hv.ne']
  exact bennett_q_mono hu hv huv

private lemma exp_le_one_add_self_add_phi_mul_sq_of_abs_le {z a : ℝ}
    (hzabs : |z| ≤ a) (ha : 0 ≤ a) :
    exp z ≤ 1 + z + bennett_phi a * z ^ 2 := by
  by_cases hz0 : z = 0
  · simp [hz0]
  by_cases hz_nonneg : 0 ≤ z
  · have hzpos : 0 < z := lt_of_le_of_ne hz_nonneg (Ne.symm hz0)
    have hza : z ≤ a := by
      rwa [abs_of_nonneg hz_nonneg] at hzabs
    have hphi := bennett_phi_pos_mono hzpos hza
    have hphi' : (exp z - 1 - z) / z ^ 2 ≤ bennett_phi a := by
      simpa [bennett_phi, hzpos.ne'] using hphi
    have hmul := mul_le_mul_of_nonneg_right hphi' (sq_nonneg z)
    have hrem : exp z - 1 - z ≤ bennett_phi a * z ^ 2 := by
      calc
        exp z - 1 - z = ((exp z - 1 - z) / z ^ 2) * z ^ 2 := by
          field_simp [hz0]
        _ ≤ bennett_phi a * z ^ 2 := hmul
    linarith
  · have hneg := exp_neg_quadratic_remainder (z := -z) (by linarith)
    have hrem : exp z - 1 - z ≤ z ^ 2 / 2 := by
      simpa using hneg
    have hhalf := bennett_phi_half_le ha
    have hmul := mul_le_mul_of_nonneg_right hhalf (sq_nonneg z)
    nlinarith

private lemma bennett_den_ne {x : ℝ} (hx3 : x ≠ 3) :
    2 * (1 - x / 3) ≠ 0 := by
  intro h
  field_simp at h
  have : x = 3 := by nlinarith
  exact hx3 this

private lemma bennett_major_deriv (x : ℝ) (hx3 : x ≠ 3) :
    deriv (fun x : ℝ => 1 + x + x ^ 2 / (2 * (1 - x / 3))) x =
      1 + x / (1 - x / 3) + x ^ 2 / (6 * (1 - x / 3) ^ 2) := by
  have hq : deriv (fun x : ℝ => x ^ 2 / (2 * (1 - x / 3))) x =
      x / (1 - x / 3) + x ^ 2 / (6 * (1 - x / 3) ^ 2) := by
    have hden : 2 * (1 - x / 3) ≠ 0 := bennett_den_ne hx3
    have hsq_deriv : deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
      rw [deriv_pow_field]
      ring
    rw [deriv_fun_div]
    · simp [hsq_deriv]
      field_simp [hx3]
      ring
    · fun_prop
    · fun_prop
    · exact hden
  rw [deriv_fun_add]
  · rw [deriv_fun_add]
    · simp [hq]
      ring
    · fun_prop
    · fun_prop
  · fun_prop
  · refine DifferentiableAt.fun_div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · exact bennett_den_ne hx3

private lemma bennett_major_exp_deriv (x : ℝ) (hx3 : x ≠ 3) :
    deriv (fun x : ℝ => (1 + x + x ^ 2 / (2 * (1 - x / 3))) * exp (-x)) x =
      exp (-x) * (x ^ 3 / (18 * (1 - x / 3) ^ 2)) := by
  have h_exp_deriv : deriv (fun y : ℝ => exp (-y)) x = - exp (-x) := by
    rw [_root_.deriv_exp (show DifferentiableAt ℝ (fun y : ℝ => -y) x by fun_prop)]
    simp
  have h3x : 3 - x ≠ 0 := by
    intro h
    have : x = 3 := by linarith
    exact hx3 this
  have hquad : 9 - x * 6 + x ^ 2 ≠ 0 := by
    intro h
    have hs : (x - 3) ^ 2 = 0 := by nlinarith
    have hlin : x - 3 = 0 := sq_eq_zero_iff.mp hs
    have : x = 3 := by linarith
    exact hx3 this
  rw [deriv_fun_mul]
  · rw [bennett_major_deriv x hx3, h_exp_deriv]
    field_simp [hx3, h3x, hquad]
    ring
  · refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) ?_
    · fun_prop
    · fun_prop
    · refine DifferentiableAt.fun_div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · exact bennett_den_ne hx3
  · fun_prop

private lemma bennett_major_exp_differentiableAt (x : ℝ) (hx3 : x ≠ 3) :
    DifferentiableAt ℝ
      (fun x : ℝ => (1 + x + x ^ 2 / (2 * (1 - x / 3))) * exp (-x)) x := by
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.add (DifferentiableAt.add ?_ ?_) ?_
    · fun_prop
    · fun_prop
    · refine DifferentiableAt.fun_div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · exact bennett_den_ne hx3
  · fun_prop

private lemma exp_le_bennett_major {y : ℝ} (hy : 0 ≤ y) (hy3 : y < 3) :
    exp y ≤ 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
  let M : ℝ → ℝ := fun x =>
    (1 + x + x ^ 2 / (2 * (1 - x / 3))) * exp (-x)
  have hmono : MonotoneOn M (Icc 0 y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) y) ?_ ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
        · fun_prop
        · fun_prop
        · refine ContinuousOn.div₀ ?_ ?_ ?_
          · fun_prop
          · fun_prop
          · intro x hx
            exact bennett_den_ne (by linarith [hx.2, hy3])
      · fun_prop
    · intro x hx
      have hxI : x ∈ Icc (0 : ℝ) y := interior_subset hx
      exact (bennett_major_exp_differentiableAt x
        (by linarith [hxI.2, hy3])).differentiableWithinAt
    · intro x hx
      have hxI : x ∈ Icc (0 : ℝ) y := interior_subset hx
      have hx0 : 0 ≤ x := hxI.1
      have hx3 : x ≠ 3 := by linarith [hxI.2, hy3]
      have hdenpos : 0 < 1 - x / 3 := by nlinarith [hxI.2, hy3]
      rw [bennett_major_exp_deriv x hx3]
      refine mul_nonneg (le_of_lt (exp_pos _)) ?_
      exact div_nonneg (by positivity) (by positivity)
  have h01 : M 0 ≤ M y := hmono (by simp [hy]) (by simp [hy]) hy
  change (1 + 0 + 0 ^ 2 / (2 * (1 - 0 / 3))) * exp (-0) ≤
      (1 + y + y ^ 2 / (2 * (1 - y / 3))) * exp (-y) at h01
  simp at h01
  have hmul := mul_le_mul_of_nonneg_right h01 (le_of_lt (exp_pos y))
  calc
    exp y = 1 * exp y := by ring
    _ ≤ ((1 + y + y ^ 2 / (2 * (1 - y / 3))) * exp (-y)) * exp y := hmul
    _ = 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
      rw [mul_assoc, ← exp_add]
      simp

/-! ## Step A: exponential bound with φ -/

theorem bennett_exp_bound {x c t : ℝ} (hx : |x| ≤ c) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    exp (t * x) ≤ 1 + t * x + t ^ 2 * bennett_phi (t * c) * x ^ 2 := by
  have htc : 0 ≤ t * c := mul_nonneg ht hc
  have h_abs_tx : |t * x| ≤ t * c := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hx ht
  have h := exp_le_one_add_self_add_phi_mul_sq_of_abs_le h_abs_tx htc
  calc
    exp (t * x) ≤ 1 + t * x + bennett_phi (t * c) * (t * x) ^ 2 := h
    _ = 1 + t * x + t ^ 2 * bennett_phi (t * c) * x ^ 2 := by ring

/-! ## Step B: φ(y) ≤ 1/(2(1 - y/3)) -/

theorem bennett_phi_le_bernstein {y : ℝ} (hy : 0 ≤ y) (hy3 : y < 3) :
    bennett_phi y ≤ 1 / (2 * (1 - y / 3)) := by
  unfold bennett_phi
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [if_neg hy0]
    have hmajor := exp_le_bennett_major hy hy3
    have hnum : exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)) := by linarith
    calc
      (exp y - 1 - y) / y ^ 2 ≤
          (y ^ 2 / (2 * (1 - y / 3))) / y ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg y)
      _ = 1 / (2 * (1 - y / 3)) := by
        field_simp [hy0]

/-! ## Combined Bernstein one-step bound -/

noncomputable def bernstein_psi (t c : ℝ) : ℝ :=
  if t * c < 3 ∧ 0 ≤ t then t ^ 2 / (2 * (1 - t * c / 3)) else 0

theorem bernstein_one_step {d c t : ℝ} (hd : |d| ≤ c) (hc : 0 ≤ c)
    (ht : 0 ≤ t) (htc : t * c < 3) :
    exp (t * d) ≤ 1 + t * d + bernstein_psi t c * d ^ 2 := by
  have key := bennett_exp_bound hd hc ht
  suffices h : t ^ 2 * bennett_phi (t * c) ≤ bernstein_psi t c by
    linarith [sq_nonneg d, bennett_phi_nonneg (t * c),
      mul_le_mul_of_nonneg_right h (sq_nonneg d)]
  unfold bernstein_psi
  rw [if_pos ⟨htc, ht⟩]
  by_cases ht0 : t = 0
  · simp [ht0, bennett_phi]
  · have htc_nn : 0 ≤ t * c := mul_nonneg ht hc
    have h_phi := bennett_phi_le_bernstein htc_nn htc
    calc t ^ 2 * bennett_phi (t * c)
        ≤ t ^ 2 * (1 / (2 * (1 - t * c / 3))) :=
          mul_le_mul_of_nonneg_left h_phi (sq_nonneg t)
      _ = t ^ 2 / (2 * (1 - t * c / 3)) := by ring

/-! ## Utility lemmas -/

theorem exp_neg_mul_one_add_le_one {x : ℝ} (hx : 0 ≤ x) :
    exp (-x) * (1 + x) ≤ 1 := by
  have h1 : 1 + x ≤ exp x := by linarith [add_one_le_exp x]
  have hexp_pos : 0 < exp (-x) := exp_pos _
  calc exp (-x) * (1 + x)
      ≤ exp (-x) * exp x :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hexp_pos)
    _ = 1 := by rw [← exp_add]; simp

theorem bernstein_optimal {u v c : ℝ} (hu : 0 < u) (hv : 0 < v) (hc : 0 ≤ c) :
    let t := u / (v + c * u / 3)
    bernstein_psi t c * v - t * u = -(u ^ 2) / (2 * (v + c * u / 3)) := by
  simp only
  have hvcup : 0 < v + c * u / 3 := by positivity
  have htc_lt : u / (v + c * u / 3) * c < 3 := by
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ hvcup]
    nlinarith
  have ht_nn : 0 ≤ u / (v + c * u / 3) := div_nonneg hu.le hvcup.le
  unfold bernstein_psi
  rw [if_pos ⟨htc_lt, ht_nn⟩]
  field_simp
  ring

end Ripple.Probability
