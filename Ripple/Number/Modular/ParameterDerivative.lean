import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative bridge for modular hypergeometric evaluations

This file records a small calculus identity used to pass from a derivative
with respect to the hypergeometric argument `x` to a derivative with respect
to a modular parameter `τ`.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

lemma hypergeom_linear_combination_via_parameter_derivative
    {F X : ℂ → ℂ} {τ x F' X' A B : ℂ}
    (hx : X τ = x) (hF : HasDerivAt F F' x) (hX : HasDerivAt X X' τ) (hX' : X' ≠ 0) :
    A * F x + B * x * F' =
      A * F (X τ) + B * x * (deriv (fun t => F (X t)) τ / X') := by
  have hcomp : HasDerivAt (fun t => F (X t)) (F' * X') τ := by
    simpa [Function.comp_def] using HasDerivAt.comp_of_eq (x := τ) hF hX hx.symm
  have hderiv : deriv (fun t => F (X t)) τ = F' * X' := hcomp.deriv
  rw [hx, hderiv]
  field_simp [hX']

end Modular
end Number
end Ripple
