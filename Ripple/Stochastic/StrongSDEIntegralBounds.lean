import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# From the terminal Itô isometry and Doob to Picard noise bounds

This file uses only Mathlib. H is the predictable L² integrand space
(with the Hilbert sum norm for finitely many channels), V is terminal L², and S
is continuous adapted path L² with its supremum norm. For the exact terminal
isometry, state vectors use `EuclideanSpace ℝ (Fin d)`, not the default Pi norm
on `Fin d → ℝ`. All three are genuine
normed spaces, not raw representatives with a discrete metric.

The Itô integral construction is to produce I, J, hTerminalIsometry, and hDoobMaximal.
The last premise is the strong maximal inequality for continuous integral versions; it is NOT
the weak nonnegative-supermartingale tail estimate. Linearity of J follows from
linearity at each time and indistinguishability of continuous versions.
The strong-solution construction is to produce coefficientMap and hCoefficientEnergy
using the channel Lipschitz constants and time integration. These are explicit
hypotheses here.
-/

namespace Ripple.Stochastic.StrongSDE

variable {H V S : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Named L² maximal estimate for the continuous integral, conditional on Doob
and the terminal isometry for the SAME integrand. -/
theorem continuousIto_maximal_sq
    (I : H →L[ℝ] V) (J : H →L[ℝ] S)
    (hTerminalIsometry : ∀ U, ‖I U‖ = ‖U‖)
    (hDoobMaximal : ∀ U, ‖J U‖ ^ 2 ≤ 4 * ‖I U‖ ^ 2)
    (U : H) : ‖J U‖ ^ 2 ≤ 4 * ‖U‖ ^ 2 := by
  simpa only [hTerminalIsometry U] using hDoobMaximal U

/-- The maximal estimate applied to coefficient differences produces precisely
the stochastic premise consumed by `picardStep_difference_sq_le`. In the
application the coefficient map already includes the scale N^(-1/2). -/
theorem doobNoiseDifferenceBound
    (I : H →L[ℝ] V) (J : H →L[ℝ] S)
    (hTerminalIsometry : ∀ U, ‖I U‖ = ‖U‖)
    (hDoobMaximal : ∀ U, ‖J U‖ ^ 2 ≤ 4 * ‖I U‖ ^ 2)
    (coefficientMap : S → H) (h LSsq : ℝ)
    (hCoefficientEnergy : ∀ X Y,
      ‖coefficientMap X - coefficientMap Y‖ ^ 2 ≤ h * LSsq * ‖X - Y‖ ^ 2)
    (X Y : S) :
    ‖J (coefficientMap X) - J (coefficientMap Y)‖ ^ 2 ≤
      4 * h * LSsq * ‖X - Y‖ ^ 2 := by
  rw [← map_sub]
  have hm := continuousIto_maximal_sq I J hTerminalIsometry hDoobMaximal
    (coefficientMap X - coefficientMap Y)
  have he := hCoefficientEnergy X Y
  nlinarith

/-- Bounded coefficients supply the matching map-value estimate. -/
theorem doobNoiseValueBound
    (I : H →L[ℝ] V) (J : H →L[ℝ] S)
    (hTerminalIsometry : ∀ U, ‖I U‖ = ‖U‖)
    (hDoobMaximal : ∀ U, ‖J U‖ ^ 2 ≤ 4 * ‖I U‖ ^ 2)
    (coefficientMap : S → H) (h BSsq : ℝ)
    (hCoefficientEnergy : ∀ X, ‖coefficientMap X‖ ^ 2 ≤ h * BSsq)
    (X : S) : ‖J (coefficientMap X)‖ ^ 2 ≤ 4 * h * BSsq := by
  have hm := continuousIto_maximal_sq I J hTerminalIsometry hDoobMaximal
    (coefficientMap X)
  have he := hCoefficientEnergy X
  nlinarith

end Ripple.Stochastic.StrongSDE
