import Ripple.Number.Modular.SingularModuli
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# Analytic globalization bridge for theta identities

This file isolates the analytic continuation step needed by the modular-CM
evaluation layer.  Once the Jacobi quartic defect is proved to have an
accumulation of zeros in the upper half-plane, the isolated-zeros theorem
globalizes it to the whole upper half-plane.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Complex Filter
open scoped Topology
open scoped UpperHalfPlane

lemma upperHalfPlaneSet_isPreconnected :
    IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
  Convex.isPreconnected (convex_halfSpace_im_gt 0)

lemma jacobiQuarticDefect_differentiableOn_upperHalfPlane :
    DifferentiableOn ℂ jacobiQuarticDefect UpperHalfPlane.upperHalfPlaneSet := by
  intro τ hτ
  exact (differentiableAt_jacobiQuarticDefect hτ).differentiableWithinAt

lemma jacobiQuarticDefect_analyticOnNhd_upperHalfPlane :
    AnalyticOnNhd ℂ jacobiQuarticDefect UpperHalfPlane.upperHalfPlaneSet := by
  exact jacobiQuarticDefect_differentiableOn_upperHalfPlane.analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet

/-- If the Jacobi quartic defect has a zero sequence accumulating at one
upper-half-plane point, it vanishes throughout the upper half-plane. -/
lemma jacobiQuarticDefect_eqOn_zero_of_frequently_zero
    {τ₀ : ℂ} (hτ₀ : τ₀ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hfreq : ∃ᶠ τ in 𝓝[≠] τ₀, jacobiQuarticDefect τ = 0) :
    Set.EqOn jacobiQuarticDefect 0 UpperHalfPlane.upperHalfPlaneSet := by
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    jacobiQuarticDefect_analyticOnNhd_upperHalfPlane
    upperHalfPlaneSet_isPreconnected hτ₀ hfreq

lemma jacobiQuarticDefect_eq_zero_of_frequently_zero
    {τ τ₀ : ℂ} (hτ : τ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hτ₀ : τ₀ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hfreq : ∃ᶠ w in 𝓝[≠] τ₀, jacobiQuarticDefect w = 0) :
    jacobiQuarticDefect τ = 0 :=
  jacobiQuarticDefect_eqOn_zero_of_frequently_zero hτ₀ hfreq hτ

lemma thetaLambda_neg_inv_of_frequently_jacobiQuartic_zero (τ : ℍ)
    (hθ : jacobiTheta (τ : ℂ) ≠ 0)
    {τ₀ : ℂ} (hτ₀ : τ₀ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hfreq : ∃ᶠ w in 𝓝[≠] τ₀, jacobiQuarticDefect w = 0) :
    thetaLambda (-1 / (τ : ℂ)) = 1 - thetaLambda (τ : ℂ) := by
  refine thetaLambda_neg_inv_of_jacobiQuarticDefect_zero τ hθ ?_
  exact jacobiQuarticDefect_eq_zero_of_frequently_zero
    (show (τ : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet from τ.2) hτ₀ hfreq

lemma one_sub_thetaLambda_of_frequently_jacobiQuartic_zero {τ τ₀ : ℂ}
    (hτ : τ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hθ : jacobiTheta τ ≠ 0)
    (hτ₀ : τ₀ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hfreq : ∃ᶠ w in 𝓝[≠] τ₀, jacobiQuarticDefect w = 0) :
    1 - thetaLambda τ = thetaFourConst τ ^ 4 / jacobiTheta τ ^ 4 := by
  refine one_sub_thetaLambda_of_jacobiQuarticDefect_zero τ hθ ?_
  exact jacobiQuarticDefect_eq_zero_of_frequently_zero hτ hτ₀ hfreq

lemma kleinJFromLambda_thetaLambda_of_frequently_jacobiQuartic_zero {τ τ₀ : ℂ}
    (hτ : τ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hθ : jacobiTheta τ ≠ 0)
    (hθ₂ : thetaTwoConst τ ≠ 0)
    (hθ₄ : thetaFourConst τ ≠ 0)
    (hτ₀ : τ₀ ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hfreq : ∃ᶠ w in 𝓝[≠] τ₀, jacobiQuarticDefect w = 0) :
    kleinJFromLambda (thetaLambda τ) =
      256 * (jacobiTheta τ ^ 8 - thetaTwoConst τ ^ 4 * thetaFourConst τ ^ 4) ^ 3 /
        (thetaTwoConst τ ^ 8 * thetaFourConst τ ^ 8 * jacobiTheta τ ^ 8) := by
  refine kleinJFromLambda_thetaLambda_of_jacobiQuarticDefect_zero τ hθ hθ₂ hθ₄ ?_
  exact jacobiQuarticDefect_eq_zero_of_frequently_zero hτ hτ₀ hfreq

end Modular
end Number
end Ripple
