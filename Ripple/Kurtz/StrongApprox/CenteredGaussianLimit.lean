import Ripple.Kurtz.StrongApprox.WienerIntegralGaussian
import Mathlib.Probability.Moments.Covariance

/-!
# Dominated limits of centered Gaussian random variables

A common square-integrable bound supplies convergence of the variances.
The Gaussian limit theorem then identifies the law, including degenerate limits.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Kurtz.StrongApprox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The second moment of a centered real Gaussian equals its variance parameter. -/
theorem integral_sq_of_centeredGaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, (X ω) ^ 2 ∂P = (v : ℝ) := by
  have hm : ∫ ω, X ω ∂P = 0 := by
    rw [hX.integral_eq, integral_id_gaussianReal]
  have h := covariance_eq_sub hX.hasGaussianLaw.memLp_two hX.hasGaussianLaw.memLp_two
  rw [covariance_self hX.aemeasurable, hX.variance_eq,
    variance_id_gaussianReal, hm] at h
  simpa only [zero_mul, sub_zero, Pi.mul_apply, pow_two] using h.symm

/-- A centered Gaussian law survives a dominated almost-sure limit. The variance
is derived as the second moment of the limit, rather than supplied as a premise. -/
theorem centeredGaussian_law_of_dominated_ae_tendsto
    {X : ℕ → Ω → ℝ} {Y D : Ω → ℝ} {v : ℕ → ℝ≥0}
    (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, HasLaw (X n) (gaussianReal 0 (v n)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hD : Integrable (fun ω => (D ω) ^ 2) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ D ω) :
    HasLaw Y (gaussianReal 0 (∫ ω, (Y ω) ^ 2 ∂P).toNNReal) P := by
  have hsecond : Tendsto (fun n => ∫ ω, (X n ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (Y ω) ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => (D ω) ^ 2)
    · intro n
      exact ((hX n).pow_const 2).aestronglyMeasurable
    · exact hD
    · intro n
      filter_upwards [hbound n] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hDpos : 0 ≤ D ω := (abs_nonneg _).trans hω
      have hsq := mul_nonneg (sub_nonneg.mpr hω)
        (add_nonneg hDpos (abs_nonneg (X n ω)))
      nlinarith [sq_abs (X n ω)]
    · filter_upwards [hlim] with ω hω
      exact hω.pow 2
  have hv : Tendsto (fun n => (v n : ℝ)) atTop
      (𝓝 ((∫ ω, (Y ω) ^ 2 ∂P).toNNReal : ℝ)) := by
    simpa only [integral_sq_of_centeredGaussian (hlaw _),
      Real.coe_toNNReal _ (integral_nonneg fun ω => sq_nonneg (Y ω))] using hsecond
  exact centeredGaussian_law_of_ae_tendsto hX (fun n => (hlaw n).map_eq) hlim hv

end Ripple.Kurtz.StrongApprox
