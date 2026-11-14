import Ripple.Stochastic.WienerIntegralL2

/-!
# Bilinear isometry for deterministic Wiener integrals

Polarization upgrades the existing norm isometry to the cross second moment
needed for covariance kernels with two different observation times.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

namespace Ripple.Stochastic.MathFin.WienerIntegralL2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} [IsPreBrownian B μ] [IsProbabilityMeasure μ]

/-- The installed deterministic integral, bundled with its established norm isometry. -/
def wienerIntegralIsometry (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearMap := (wienerIntegralLp (μ := μ) B T).toLinearMap
  norm_map' φ := by
    simpa only [ContinuousLinearMap.coe_coe] using
      wienerIntegralLp_norm (μ := μ) (B := B) T φ

/-- Inner products are preserved for arbitrary deterministic square-integrable inputs. -/
theorem inner_wienerIntegralLp (T : ℝ≥0)
    (φ ψ : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ⟪wienerIntegralLp (μ := μ) B T φ, wienerIntegralLp (μ := μ) B T ψ⟫_ℝ =
      ⟪φ, ψ⟫_ℝ :=
  (wienerIntegralIsometry (μ := μ) (B := B) T).inner_map_map φ ψ

/-- The cross second moment is the integral of the product of the two kernels. -/
theorem integral_mul_wienerIntegralLp (T : ℝ≥0)
    (φ ψ : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    (∫ ω, (wienerIntegralLp (μ := μ) B T φ : Ω → ℝ) ω *
      (wienerIntegralLp (μ := μ) B T ψ : Ω → ℝ) ω ∂μ) =
      ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), φ s * ψ s := by
  have h := inner_wienerIntegralLp (μ := μ) (B := B) T φ ψ
  rw [L2.inner_def, L2.inner_def] at h
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using h

end Ripple.Stochastic.MathFin.WienerIntegralL2
