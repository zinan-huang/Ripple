/-
  Ripple.Kurtz.StrongApprox.GaussianMoments — second and fourth moments of `N(0,1)`

  Route: `iteratedDeriv_mgf_zero` with `mgf id (gaussianReal 0 1) = fun t => exp (t²/2)`, whose
  iterated derivatives are `p_n(t) exp(t²/2)` with `p₂ = 1 + t²`, `p₄ = 3 + 6t² + t⁴`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory

/-- `E(t) = exp(t²/2)`. -/
noncomputable def gaussMgf (t : ℝ) : ℝ := Real.exp (t ^ 2 / 2)

theorem hasDerivAt_gaussMgf (t : ℝ) : HasDerivAt gaussMgf (t * gaussMgf t) t := by
  have h := (((hasDerivAt_id t).pow 2).div_const 2).exp
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, gaussMgf]
  ring

/-- Derivative of `p · E` where `p` is differentiable. -/
theorem hasDerivAt_mul_gaussMgf {p : ℝ → ℝ} {p' t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun s => p s * gaussMgf s) ((p' + t * p t) * gaussMgf t) t := by
  have h := hp.mul (hasDerivAt_gaussMgf t)
  refine h.congr_deriv ?_
  ring

theorem mgf_id_gaussianReal_zero_one : mgf id (gaussianReal 0 1) = gaussMgf := by
  rw [mgf_id_gaussianReal]
  funext t
  simp [gaussMgf]

theorem iteratedDeriv_one_gaussMgf : iteratedDeriv 1 gaussMgf = fun t => t * gaussMgf t := by
  rw [iteratedDeriv_one]
  funext t
  exact (hasDerivAt_gaussMgf t).deriv

theorem iteratedDeriv_two_gaussMgf :
    iteratedDeriv 2 gaussMgf = fun t => (1 + t ^ 2) * gaussMgf t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one_gaussMgf]
  funext t
  have h := hasDerivAt_mul_gaussMgf (p := fun s => s) (hasDerivAt_id t)
  rw [h.deriv]
  ring

theorem iteratedDeriv_three_gaussMgf :
    iteratedDeriv 3 gaussMgf = fun t => (3 * t + t ^ 3) * gaussMgf t := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_gaussMgf]
  funext t
  have hp : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
    have := ((hasDerivAt_id t).pow 2).const_add 1
    refine this.congr_deriv ?_
    simp
  have h := hasDerivAt_mul_gaussMgf hp
  rw [h.deriv]
  ring

theorem iteratedDeriv_four_gaussMgf :
    iteratedDeriv 4 gaussMgf = fun t => (3 + 6 * t ^ 2 + t ^ 4) * gaussMgf t := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_gaussMgf]
  funext t
  have hp : HasDerivAt (fun s : ℝ => 3 * s + s ^ 3) (3 + 3 * t ^ 2) t := by
    have := ((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)
    refine this.congr_deriv ?_
    simp
  have h := hasDerivAt_mul_gaussMgf hp
  rw [h.deriv]
  ring

theorem zero_mem_interior_integrableExpSet :
    (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
  rw [integrableExpSet_id_gaussianReal]
  simp

/-- `E Z² = 1` for `Z ~ N(0,1)`. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := iteratedDeriv_mgf_zero zero_mem_interior_integrableExpSet 2
  rw [mgf_id_gaussianReal_zero_one, iteratedDeriv_two_gaussMgf] at h
  simp only [gaussMgf] at h
  have : (∫ x, (id ^ 2) x ∂(gaussianReal 0 1)) = ∫ x, x ^ 2 ∂(gaussianReal 0 1) := by
    congr 1
  rw [← this, ← h]
  simp

/-- `E Z⁴ = 3` for `Z ~ N(0,1)`. -/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := iteratedDeriv_mgf_zero zero_mem_interior_integrableExpSet 4
  rw [mgf_id_gaussianReal_zero_one, iteratedDeriv_four_gaussMgf] at h
  simp only [gaussMgf] at h
  have : (∫ x, (id ^ 4) x ∂(gaussianReal 0 1)) = ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
    congr 1
  rw [← this, ← h]
  simp

/-- `E (1 + 2Z²)² = 17`. -/
theorem integral_one_add_two_sq_sq_gaussianReal :
    ∫ x, (1 + 2 * x ^ 2) ^ 2 ∂(gaussianReal 0 1) = 17 := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
    simpa using integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 2
  have h4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
    simpa using integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 4
  have hfun : (fun x : ℝ => (1 + 2 * x ^ 2) ^ 2) = fun x => (1 + 4 * x ^ 2) + 4 * x ^ 4 := by
    funext x; ring
  have hA : Integrable (fun x : ℝ => 1 + 4 * x ^ 2) (gaussianReal 0 1) :=
    (integrable_const 1).add (h2.const_mul 4)
  have hB : Integrable (fun x : ℝ => 4 * x ^ 4) (gaussianReal 0 1) := h4.const_mul 4
  have e1 : ∫ x, (1 + 4 * x ^ 2 + 4 * x ^ 4) ∂(gaussianReal 0 1) =
      (∫ x, (1 + 4 * x ^ 2) ∂(gaussianReal 0 1)) + ∫ x, 4 * x ^ 4 ∂(gaussianReal 0 1) :=
    integral_add hA hB
  have e2 : ∫ x, (1 + 4 * x ^ 2) ∂(gaussianReal 0 1) =
      (∫ _, (1 : ℝ) ∂(gaussianReal 0 1)) + ∫ x, 4 * x ^ 2 ∂(gaussianReal 0 1) :=
    integral_add (integrable_const 1) (h2.const_mul 4)
  rw [hfun, e1, e2, integral_const_mul, integral_const_mul, integral_const,
    integral_sq_gaussianReal, integral_pow_four_gaussianReal]
  simp [measureReal_univ_eq_one]
  norm_num

end Ripple.Kurtz.StrongApprox
