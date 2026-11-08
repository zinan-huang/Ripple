import Ripple.Number.Modular.CMEvaluationIsRoot
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary nonvanishing inputs at the CM points

These lemmas close the local denominator side of the theta/lambda CM bridge.
They use Mathlib's explicit exponential tail bound for `jacobiTheta`.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Complex Real
open scoped UpperHalfPlane

private lemma exp_neg_pi_lt_one_third :
    Real.exp (-Real.pi) < (1 / 3 : ℝ) := by
  have h3 : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at h ⊢
    exact h
  have h2pi : (2 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  have h : (3 : ℝ) < Real.exp Real.pi :=
    h3.trans (Real.exp_lt_exp.mpr h2pi)
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos _
  simpa [Real.exp_neg, one_div] using
    ((inv_lt_inv₀ hpos (by norm_num : (0 : ℝ) < 3)).2 h)

private lemma theta_tail_bound_lt_one_of_one_le_im {τ : ℂ}
    (him : 1 ≤ τ.im) :
    2 / (1 - Real.exp (-Real.pi * τ.im)) *
        Real.exp (-Real.pi * τ.im) < 1 := by
  let r := Real.exp (-Real.pi * τ.im)
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_le : r ≤ Real.exp (-Real.pi) := by
    dsimp [r]
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, him]
  have hr_lt_third : r < (1 / 3 : ℝ) :=
    hr_le.trans_lt exp_neg_pi_lt_one_third
  have hden_pos : 0 < 1 - r := by nlinarith
  have hmul : 3 * r < 1 := by nlinarith
  calc
    2 / (1 - r) * r = (2 * r) / (1 - r) := by ring
    _ < 1 := by
      rw [div_lt_one hden_pos]
      nlinarith

lemma jacobiTheta_ne_zero_of_one_le_im {τ : ℂ}
    (hτ : 0 < τ.im) (him : 1 ≤ τ.im) :
    jacobiTheta τ ≠ 0 := by
  intro hzero
  have hbound := norm_jacobiTheta_sub_one_le hτ
  have hlt := theta_tail_bound_lt_one_of_one_le_im him
  have hnorm : ‖jacobiTheta τ - 1‖ = 1 := by
    rw [hzero]
    norm_num
  rw [hnorm] at hbound
  linarith

lemma ramanujanTau58_one_le_im :
    1 ≤ (ramanujanTau58 : ℂ).im := by
  rw [ramanujanTau58_im]
  have hs : (2 : ℝ) ≤ Real.sqrt 58 :=
    Real.le_sqrt_of_sq_le (by norm_num : (2 : ℝ) ^ 2 ≤ 58)
  nlinarith

lemma heegnerTau163_one_le_im :
    1 ≤ (heegnerTau163 : ℂ).im := by
  rw [heegnerTau163_im]
  have hs : (2 : ℝ) ≤ Real.sqrt 163 :=
    Real.le_sqrt_of_sq_le (by norm_num : (2 : ℝ) ^ 2 ≤ 163)
  nlinarith

lemma jacobiTheta_ramanujanTau58_ne_zero :
    jacobiTheta (ramanujanTau58 : ℂ) ≠ 0 :=
  jacobiTheta_ne_zero_of_one_le_im ramanujanTau58.2 ramanujanTau58_one_le_im

lemma jacobiTheta_heegnerTau163_ne_zero :
    jacobiTheta (heegnerTau163 : ℂ) ≠ 0 :=
  jacobiTheta_ne_zero_of_one_le_im heegnerTau163.2 heegnerTau163_one_le_im

lemma differentiableAt_thetaLambda_ramanujanTau58 :
    DifferentiableAt ℂ thetaLambda (ramanujanTau58 : ℂ) :=
  differentiableAt_thetaLambda ramanujanTau58.2 jacobiTheta_ramanujanTau58_ne_zero

lemma differentiableAt_thetaLambda_heegnerTau163 :
    DifferentiableAt ℂ thetaLambda (heegnerTau163 : ℂ) :=
  differentiableAt_thetaLambda heegnerTau163.2 jacobiTheta_heegnerTau163_ne_zero

end Modular
end Number
end Ripple
