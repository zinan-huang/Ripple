import Ripple.Kurtz.StrongApprox.PaperSectionFourHypotheses
import Ripple.Kurtz.StrongApprox.SectionFourAssembly

/-!
# Returning the approximation to the paper's Euclidean norm

Multiplying the random error coefficient by `d + 1` converts the internal
sup-norm estimate to the Euclidean estimate, including dimension zero.
Dividing the exponential parameter by the same constant preserves every
exponential integrand exactly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Ripple.Kurtz.StrongApprox
open PaperSectionFourHypotheses SectionFourAssembly

/-- A deliberately non-sharp positive dimension factor handles all dimensions. -/
theorem paperNorm_le_dimension_mul_norm {d : ℕ} (x : Fin d → ℝ) :
    paperNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hc : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith
  have hh := (paperNorm_sq_le x).trans
    (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖))
  have hp := paperNorm_nonneg x
  have hn := norm_nonneg x
  by_contra h
  rw [not_le] at h
  have hq : 0 ≤ ((d : ℝ) + 1) * ‖x‖ := by positivity
  have h2 : (((d : ℝ) + 1) * ‖x‖) ^ 2 < paperNorm x ^ 2 := pow_lt_pow_left₀ h hq two_ne_zero
  rw [mul_pow] at h2
  linarith

/-- Rescaling a coefficient and inversely rescaling the exponent preserves
both integrability and the uniform exponential-moment bound. -/
theorem uniformExpMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {R : ℕ → Ω → ℝ} {eta C c : ℝ}
    (hR : UniformExpMoment R eta C P) (hc : 0 < c) :
    UniformExpMoment (fun N ω => c * R N ω) (eta / c) C P where
  eta_pos := div_pos hR.eta_pos hc
  measurable N hN := measurable_const.mul (hR.measurable N hN)
  nonneg N hN ω := mul_nonneg hc.le (hR.nonneg N hN ω)
  integrable N hN := by
    have heq : (fun ω => Real.exp (eta / c * (c * R N ω))) =
        (fun ω => Real.exp (eta * R N ω)) := by
      funext ω
      congr 1
      field_simp [hc.ne']
    rw [heq]
    exact hR.integrable N hN
  integral_le N hN := by
    have heq : (fun ω => Real.exp (eta / c * (c * R N ω))) =
        (fun ω => Real.exp (eta * R N ω)) := by
      funext ω
      congr 1
      field_simp [hc.ne']
    rw [heq]
    exact hR.integral_le N hN

/-- Pointwise conversion of the scaled approximation error. -/
theorem paperNorm_error_le {d N : ℕ} {x : Fin d → ℝ} {gamma : ℝ}
    (hb : ‖x‖ ≤ gamma * Real.log (N : ℝ) / Real.sqrt N) :
    paperNorm x ≤ (((d : ℝ) + 1) * gamma) * Real.log (N : ℝ) / Real.sqrt N := by
  calc
    paperNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := paperNorm_le_dimension_mul_norm x
    _ ≤ ((d : ℝ) + 1) * (gamma * Real.log (N : ℝ) / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Ripple.Kurtz.StrongApprox
