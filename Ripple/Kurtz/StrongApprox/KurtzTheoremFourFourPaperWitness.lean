import Ripple.Kurtz.StrongApprox.KurtzTheoremFourFour
import Ripple.Kurtz.StrongApprox.KurtzTheoremFourFourWitness

/-!
# The printed hypotheses of Kurtz's Theorem 4.4 for a concrete model

The model is the one of `KurtzTheoremFourFourWitness`: state `Fin 1 → ℝ`, two channels with
directions `+1`, `-1` and rates `f₊ x = 2 + sin x`, `f₋ x = 2`, population rates `f_N = f`
and `Γ = 0`. Both directions have Euclidean norm `1`, the rates are at least `1`, and the
square roots are therefore `1`-Lipschitz, so the summed square-root bound holds with `M = 1`.
The drift is `F x = sin x`; its coordinate partials are `cos x` and `-sin x`, both bounded
by `1`.

`kurtz_theorem_four_four_paper_witness` is `kurtz_theorem_four_four` applied to this record.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
open PaperSectionFourHypotheses

theorem paperNorm_witnessDir_sq (l : Fin 2) : paperNorm (witnessDir l) ^ 2 = 1 := by
  rw [paperNorm_sq, Fin.sum_univ_one]
  fin_cases l
  · show (1 : ℝ) ^ 2 = 1
    norm_num
  · show (-1 : ℝ) ^ 2 = 1
    norm_num

theorem witnessRate_sq_sub_le (l : Fin 2) (x y : Fin 1 → ℝ) :
    (Real.sqrt (witnessRate l x) - Real.sqrt (witnessRate l y)) ^ 2 ≤
      (witnessRate l x - witnessRate l y) ^ 2 := by
  have hs := abs_sqrt_sub_sqrt_le_of_one_le (one_le_witnessRate l x) (one_le_witnessRate l y)
  rw [← sq_abs, ← sq_abs (witnessRate l x - witnessRate l y)]
  exact pow_le_pow_left₀ (abs_nonneg _) hs 2

/-- The summed square-root bound with `M = 1`. -/
theorem witness_sqrt_sum (x y : Fin 1 → ℝ) :
    ∑ l, paperNorm (witnessDir l) ^ 2 *
        (Real.sqrt (witnessRate l x) - Real.sqrt (witnessRate l y)) ^ 2 ≤
      1 * paperNorm (x - y) ^ 2 := by
  have hxy : paperNorm (x - y) ^ 2 = (x 0 - y 0) ^ 2 := by
    rw [paperNorm_sq, Fin.sum_univ_one, Pi.sub_apply]
  have e0 : witnessRate 0 x - witnessRate 0 y = Real.sin (x 0) - Real.sin (y 0) := by
    show 2 + Real.sin (x 0) - (2 + Real.sin (y 0)) = Real.sin (x 0) - Real.sin (y 0)
    ring
  have e1 : witnessRate 1 x = witnessRate 1 y := rfl
  have h0 : (witnessRate 0 x - witnessRate 0 y) ^ 2 ≤ (x 0 - y 0) ^ 2 := by
    rw [e0, ← sq_abs, ← sq_abs (x 0 - y 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_sub_sin_le _ _) 2
  rw [Fin.sum_univ_two, paperNorm_witnessDir_sq, paperNorm_witnessDir_sq, one_mul, one_mul,
    one_mul, hxy, e1, sub_self, zero_pow two_ne_zero, add_zero]
  exact (witnessRate_sq_sub_le 0 x y).trans h0

/-- The coordinate partials of the drift `x ↦ sin (x 0)`: first `cos`, second `-sin`. -/
def witnessPartials : BoundedCoordinatePartials (tcDrift witnessRate witnessDir) 1 1 where
  first x _ _ := Real.cos (x 0)
  second x _ _ _ := -Real.sin (x 0)
  first_nonneg := zero_le_one
  second_nonneg := zero_le_one
  has_first x i j := by
    obtain rfl : j = 0 := Subsingleton.elim j 0
    have hF : (fun t => tcDrift witnessRate witnessDir (Function.update x 0 t) i) =
        Real.sin := by
      funext t
      rw [witness_tcDrift, Function.update_self]
      show Real.sin t * 1 = Real.sin t
      rw [mul_one]
    rw [hF]
    exact Real.hasDerivAt_sin (x 0)
  has_second x i j k := by
    obtain rfl : k = 0 := Subsingleton.elim k 0
    show HasDerivAt (fun t => Real.cos (Function.update x 0 t 0)) (-Real.sin (x 0)) (x 0)
    have hG : (fun t => Real.cos (Function.update x 0 t 0)) = Real.cos := by
      funext t
      rw [Function.update_self]
    rw [hG]
    exact Real.hasDerivAt_cos (x 0)
  first_bound x _ _ := Real.abs_cos_le_one (x 0)
  second_bound x _ _ _ := by
    rw [abs_neg]
    exact Real.abs_sin_le_one (x 0)

/-- The printed hypotheses of Theorem 4.4 for the two-channel model, with `f_N = f`,
`Γ = 0`, `M = 1` and partial bounds `1`. -/
def witnessPaperData :
    SectionFourPaperData witnessDir witnessRate (fun _ => witnessRate) witnessEps 0 1 1 1 where
  eps_nonneg := witnessEps_nonneg
  gamma_nonneg := le_rfl
  sqrt_nonneg := zero_le_one
  rate_nonneg _ _ := witnessRate_nonneg
  rate_bound _ _ := witnessRate_le
  rate_error N _ l x := by
    show |witnessRate l x - witnessRate l x| ≤ 0 * witnessEps l / (N : ℝ)
    rw [sub_self, abs_zero, zero_mul, zero_div]
  sqrt_sum := witness_sqrt_sum
  partials := witnessPartials

/-- Kurtz's Theorem 4.4, from the printed hypotheses, for the two-channel model with rates
`2 + sin x` and `2`: the record `SectionFourPaperData` is inhabited by a model with a
state-dependent rate. -/
theorem kurtz_theorem_four_four_paper_witness (x0 : Fin 1 → ℝ) :
    witnessPaperData.Conclusion x0 :=
  kurtz_theorem_four_four _ x0

end Ripple.Kurtz.StrongApprox
