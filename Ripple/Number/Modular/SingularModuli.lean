import Ripple.Number.Modular.Lambda
import Ripple.Number.Modular.ParameterDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Singular-modulus normalizations for the Ramanujan--Chudnovsky formulas

This file contains only definitions and algebraic normalization lemmas.  The
analytic CM evaluations are not asserted here.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Complex
open scoped UpperHalfPlane

/-- Ramanujan's level-58 CM point `τ = √(-58) / 2` in the upper half-plane.

This is the reduced binary-quadratic-form representative `(2, 0, 29)` of
discriminant `-232`.  The hypergeometric pullback in Ramanujan's formula is
`λ(τ)^2 = 1 / 99^4`; using `τ = √(-58)` instead gives the wrong
normalization by a full modular-parameter square. -/
noncomputable def ramanujanTau58 : ℍ :=
  ⟨Real.sqrt 58 * Complex.I / 2, by
    rw [Complex.div_im]
    simp⟩

lemma ramanujanTau58_re :
    (ramanujanTau58 : ℂ).re = 0 := by
  norm_num [ramanujanTau58]

lemma ramanujanTau58_im :
    (ramanujanTau58 : ℂ).im = Real.sqrt 58 / 2 := by
  norm_num [ramanujanTau58]

lemma ramanujanTau58_quadratic :
    4 * (ramanujanTau58 : ℂ)^2 + 58 = 0 := by
  have hs : ((Real.sqrt 58 : ℝ) : ℂ)^2 = 58 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 58)
  rw [ramanujanTau58]
  ring_nf
  rw [hs]
  norm_num

lemma ramanujanTau58_reduced_form_quadratic :
    2 * (ramanujanTau58 : ℂ)^2 + 29 = 0 := by
  have h := ramanujanTau58_quadratic
  linear_combination h / 2

lemma ramanujanTau58_q :
    Complex.exp (2 * Real.pi * Complex.I * (ramanujanTau58 : ℂ)) =
      Real.exp (-Real.pi * Real.sqrt 58) := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (ramanujanTau58 : ℂ) =
      ((-Real.pi * Real.sqrt 58 : ℝ) : ℂ) by
    apply Complex.ext
    · simp [ramanujanTau58, Complex.mul_re, Complex.mul_im]
      ring
    · simp [ramanujanTau58, Complex.mul_re, Complex.mul_im]]
  simp [Complex.ofReal_exp]

lemma ramanujanTau58_q_double :
    Complex.exp (4 * Real.pi * Complex.I * (ramanujanTau58 : ℂ)) =
      Real.exp (-(2 * Real.pi * Real.sqrt 58)) := by
  rw [show 4 * (Real.pi : ℂ) * Complex.I * (ramanujanTau58 : ℂ) =
      ((-(2 * Real.pi * Real.sqrt 58) : ℝ) : ℂ) by
    apply Complex.ext
    · simp [ramanujanTau58, Complex.mul_re, Complex.mul_im]
      ring
    · simp [ramanujanTau58, Complex.mul_re, Complex.mul_im]]
  simp [Complex.ofReal_exp]

lemma ramanujanTau58_q_half :
    Complex.exp (Real.pi * Complex.I * (ramanujanTau58 : ℂ)) =
      Real.exp (-(Real.pi * Real.sqrt 58 / 2)) := by
  rw [show (Real.pi : ℂ) * Complex.I * (ramanujanTau58 : ℂ) =
      ((-(Real.pi * Real.sqrt 58 / 2) : ℝ) : ℂ) by
    apply Complex.ext
    · simp [ramanujanTau58, Complex.mul_re, Complex.mul_im]
      ring
    · simp [ramanujanTau58, Complex.mul_re, Complex.mul_im]]
  simp [Complex.ofReal_exp]

lemma modularLambdaEta_ramanujanTau58_product_form :
    modularLambdaEta (ramanujanTau58 : ℂ) =
      16 * (Real.exp (-(Real.pi * Real.sqrt 58 / 2)) : ℂ) *
        ((∏' n : ℕ, (1 - ModularForm.eta_q n ((ramanujanTau58 : ℂ) / 2))) ^ 8 *
          (∏' n : ℕ, (1 - ModularForm.eta_q n (2 * (ramanujanTau58 : ℂ)))) ^ 16 /
            (∏' n : ℕ, (1 - ModularForm.eta_q n (ramanujanTau58 : ℂ))) ^ 24) := by
  rw [modularLambdaEta_eq_q_prefactor_products, ramanujanTau58_q_half]

lemma modularLambdaEta_ramanujanTau58_qPochhammer_form :
    modularLambdaEta (ramanujanTau58 : ℂ) =
      16 * (Real.exp (-(Real.pi * Real.sqrt 58 / 2)) : ℂ) *
        (qPochhammerInf (Real.exp (-(Real.pi * Real.sqrt 58 / 2)) : ℂ) ^ 8 *
          qPochhammerInf (Real.exp (-(2 * Real.pi * Real.sqrt 58)) : ℂ) ^ 16 /
            qPochhammerInf (Real.exp (-Real.pi * Real.sqrt 58) : ℂ) ^ 24) := by
  rw [modularLambdaEta_eq_qPochhammerInf]
  rw [ramanujanTau58_q_half, ramanujanTau58_q_double, ramanujanTau58_q]

/-- The small modular parameter in Ramanujan's `1/π` formula. -/
noncomputable def ramanujanLambda58Target : ℂ :=
  1 / (99 : ℂ)^2

lemma ramanujanLambda58Target_sq :
    ramanujanLambda58Target ^ 2 = 1 / (99 : ℂ)^4 := by
  unfold ramanujanLambda58Target
  rw [div_pow]
  norm_num

lemma ramanujanLambda58Target_ne_zero :
    ramanujanLambda58Target ≠ 0 := by
  unfold ramanujanLambda58Target
  norm_num

lemma ramanujanLambda58Target_sq_ne_zero :
    ramanujanLambda58Target ^ 2 ≠ 0 :=
  pow_ne_zero 2 ramanujanLambda58Target_ne_zero

lemma ramanujanLambda58Target_one_sub_ne_zero :
    1 - ramanujanLambda58Target ≠ 0 := by
  unfold ramanujanLambda58Target
  norm_num

/-- The standard theta-two constant
`θ₂(τ) = exp(π i τ / 4) * jacobiTheta₂(τ / 2, τ)`.

Mathlib's two-variable `jacobiTheta₂` is the unshifted
`∑ exp(2πinz + πin²τ)`.  The prefactor below converts the diagonal value
`z = τ / 2` into the classical shifted theta constant
`∑ exp(πi(n+1/2)²τ)`. -/
noncomputable def thetaTwoConst (τ : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ

lemma thetaTwoConst_eq (τ : ℂ) :
    thetaTwoConst τ =
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ := rfl

/-- Shifted-series form of the classical theta-two constant. -/
lemma thetaTwoConst_eq_tsum_shifted (τ : ℂ) :
    thetaTwoConst τ =
      ∑' n : ℤ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ) := by
  unfold thetaTwoConst jacobiTheta₂ jacobiTheta₂_term
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← Complex.exp_add]
  congr 1
  ring

lemma thetaTwoConst_shifted_pair (n : ℕ) (τ : ℂ) :
    Complex.exp (Real.pi * Complex.I * (((-(n + 1 : ℕ) : ℤ) : ℂ) + 1 / 2)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ) := by
  have hshift :
      (((-(n + 1 : ℕ) : ℤ) : ℂ) + 1 / 2) = -((n : ℂ) + 1 / 2) := by
    norm_num
    ring
  congr 1
  rw [hshift]
  ring

lemma thetaTwoConst_shifted_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ =>
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ)) := by
  have hbase : Summable (fun n : ℤ => jacobiTheta₂_term n (τ / 2) τ) :=
    (summable_jacobiTheta₂_term_iff (τ / 2) τ).2 hτ
  have hterm : (fun n : ℤ =>
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ)) =
        fun n : ℤ => Complex.exp (Real.pi * Complex.I * τ / 4) *
          jacobiTheta₂_term n (τ / 2) τ := by
    funext n
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hterm]
  exact hbase.mul_left _

lemma thetaTwoConst_hasSum_nat_mul_two {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ =>
      2 * Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ))
      (thetaTwoConst τ) := by
  let f : ℤ → ℂ := fun n =>
    Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ)
  have hf : HasSum f (thetaTwoConst τ) := by
    rw [thetaTwoConst_eq_tsum_shifted]
    exact (thetaTwoConst_shifted_summable hτ).hasSum
  refine hf.nat_add_neg_add_one.congr_fun ?_
  intro n
  dsimp [f]
  change
    2 * Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ) +
        Complex.exp (Real.pi * Complex.I * (((-((n : ℤ) + 1) : ℤ) : ℂ) + 1 / 2)^2 * τ)
  have hpair :
      Complex.exp (Real.pi * Complex.I * (((-((n : ℤ) + 1) : ℤ) : ℂ) + 1 / 2)^2 * τ) =
        Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1 / 2)^2 * τ) := by
    have hshift :
        (((-((n : ℤ) + 1) : ℤ) : ℂ) + 1 / 2) = -((n : ℂ) + 1 / 2) := by
      norm_num
      ring
    congr 1
    rw [hshift]
    ring
  rw [hpair]
  ring

lemma thetaTwoConst_hasSum_q_series {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ =>
      2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
        Complex.exp (Real.pi * Complex.I * τ) ^ (n * (n + 1)))
      (thetaTwoConst τ) := by
  refine (thetaTwoConst_hasSum_nat_mul_two hτ).congr_fun ?_
  intro n
  rw [← Complex.exp_nat_mul]
  rw [show 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
      Complex.exp ((n * (n + 1) : ℕ) * (Real.pi * Complex.I * τ)) =
    2 * (Complex.exp (Real.pi * Complex.I * τ / 4) *
      Complex.exp ((n * (n + 1) : ℕ) * (Real.pi * Complex.I * τ))) by ring]
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring_nf

/-- The classical theta-four constant `θ₄(τ) = ∑ (-1)^n q^{n^2}`,
represented as the two-variable theta function at `z = 1/2`. -/
noncomputable def thetaFourConst (τ : ℂ) : ℂ :=
  jacobiTheta₂ (1 / 2) τ

lemma thetaFourConst_eq (τ : ℂ) :
    thetaFourConst τ = jacobiTheta₂ (1 / 2) τ := rfl

/-- Series form of theta-four: `θ₄(τ) = ∑ exp(πinτ) q^{n^2}`. -/
lemma thetaFourConst_eq_tsum (τ : ℂ) :
    thetaFourConst τ =
      ∑' n : ℤ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + n ^ 2 * τ)) := by
  unfold thetaFourConst jacobiTheta₂ jacobiTheta₂_term
  apply tsum_congr
  intro n
  congr 1
  ring

lemma thetaFourConst_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ =>
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + n ^ 2 * τ))) := by
  have hbase : Summable (fun n : ℤ => jacobiTheta₂_term n (1 / 2) τ) :=
    (summable_jacobiTheta₂_term_iff (1 / 2 : ℂ) τ).2 hτ
  have hterm : (fun n : ℤ =>
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + n ^ 2 * τ))) =
        fun n : ℤ => jacobiTheta₂_term n (1 / 2) τ := by
    funext n
    unfold jacobiTheta₂_term
    congr 1
    ring
  rw [hterm]
  exact hbase

lemma thetaFourConst_pair (n : ℕ) (τ : ℂ) :
    Complex.exp (Real.pi * Complex.I * ((-(n : ℤ) : ℂ) + (-(n : ℤ) : ℂ)^2 * τ)) =
      Complex.exp (Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ)) := by
  rw [show Real.pi * Complex.I * ((-(n : ℤ) : ℂ) + (-(n : ℤ) : ℂ)^2 * τ) =
      Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ) -
        (n : ℂ) * (2 * Real.pi * Complex.I) by
    norm_num
    ring]
  rw [Complex.exp_sub, Complex.exp_nat_mul_two_pi_mul_I]
  simp

lemma thetaFourConst_hasSum_nat_mul_two {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ =>
      2 * Complex.exp (Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ)))
      (thetaFourConst τ + 1) := by
  let f : ℤ → ℂ := fun n =>
    Complex.exp (Real.pi * Complex.I * ((n : ℂ) + n ^ 2 * τ))
  have hf : HasSum f (thetaFourConst τ) := by
    rw [thetaFourConst_eq_tsum]
    exact (thetaFourConst_summable hτ).hasSum
  convert hf.nat_add_neg.congr_fun ?_ using 1
  · simp [f]
  · intro n
    dsimp [f]
    have hpair :
        Complex.exp (Real.pi * Complex.I * (((-(Int.ofNat n) : ℤ) : ℂ) +
            ((-(Int.ofNat n) : ℤ) : ℂ)^2 * τ)) =
          Complex.exp (Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ)) := by
      rw [show Real.pi * Complex.I * (((-(Int.ofNat n) : ℤ) : ℂ) +
            ((-(Int.ofNat n) : ℤ) : ℂ)^2 * τ) =
          Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ) -
            (n : ℂ) * (2 * Real.pi * Complex.I) by
        norm_num
        ring]
      rw [Complex.exp_sub, Complex.exp_nat_mul_two_pi_mul_I]
      simp
    have hpair' :
        Complex.exp (Real.pi * Complex.I * (((-((n : ℤ)) : ℤ) : ℂ) +
            ((-((n : ℤ)) : ℤ) : ℂ)^2 * τ)) =
          Complex.exp (Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ)) := by
      simpa using hpair
    rw [hpair']
    have hnat :
        Complex.exp (Real.pi * Complex.I * (((n : ℤ) : ℂ) + ((n : ℤ) : ℂ)^2 * τ)) =
          Complex.exp (Real.pi * Complex.I * ((n : ℂ) + (n : ℂ)^2 * τ)) := by
      norm_num
    rw [hnat]
    ring

lemma thetaFourConst_hasSum_q_series {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ =>
      2 * (-1 : ℂ) ^ n * Complex.exp (Real.pi * Complex.I * τ) ^ (n ^ 2))
      (thetaFourConst τ + 1) := by
  refine (thetaFourConst_hasSum_nat_mul_two hτ).congr_fun ?_
  intro n
  rw [← Complex.exp_nat_mul]
  rw [show 2 * (-1 : ℂ) ^ n *
      Complex.exp ((n ^ 2 : ℕ) * (Real.pi * Complex.I * τ)) =
    2 * ((-1 : ℂ) ^ n *
      Complex.exp ((n ^ 2 : ℕ) * (Real.pi * Complex.I * τ))) by ring]
  rw [← show Complex.exp ((n : ℂ) * (Real.pi * Complex.I)) = (-1 : ℂ) ^ n by
    rw [show (n : ℂ) * (Real.pi * Complex.I) = n * (Real.pi * Complex.I) by norm_num]
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]]
  rw [← Complex.exp_add]
  congr 1
  apply congrArg Complex.exp
  norm_num
  ring

lemma jacobiTheta_hasSum_q_series {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ =>
      2 * Complex.exp (Real.pi * Complex.I * τ) ^ ((n + 1) ^ 2))
      (jacobiTheta τ - 1) := by
  have h := hasSum_nat_jacobiTheta hτ
  convert h.mul_left (2 : ℂ) using 1
  · ext n
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num
    ring_nf
  · ring

lemma thetaFourConst_two_add (τ : ℂ) :
    thetaFourConst (τ + 2) = thetaFourConst τ := by
  unfold thetaFourConst
  rw [jacobiTheta₂_add_right]

/-- The theta-four constant is theta-three shifted by one in the modular
parameter. -/
lemma thetaFourConst_eq_jacobiTheta_add_one (τ : ℂ) :
    thetaFourConst τ = jacobiTheta (τ + 1) := by
  rw [thetaFourConst_eq_tsum, jacobiTheta]
  apply tsum_congr
  intro n
  have hEven : Even (n - n ^ 2) := by
    have h := Int.even_mul_pred_self n
    convert h.neg using 1
    ring
  rcases hEven with ⟨k, hk⟩
  rw [show Real.pi * Complex.I * ((n : ℂ) + n ^ 2 * τ) =
      Real.pi * Complex.I * (((n ^ 2 : ℤ) : ℂ) * (τ + 1)) +
        Real.pi * Complex.I * (((n - n ^ 2 : ℤ) : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_add]
  rw [hk]
  push_cast
  rw [show Real.pi * Complex.I * ((k : ℂ) + k) =
      (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  rw [mul_one]
  congr 1
  ring

lemma jacobiTheta_add_one (τ : ℂ) :
    jacobiTheta (τ + 1) = thetaFourConst τ :=
  (thetaFourConst_eq_jacobiTheta_add_one τ).symm

lemma thetaFourConst_add_one (τ : ℂ) :
    thetaFourConst (τ + 1) = jacobiTheta τ := by
  rw [thetaFourConst_eq_jacobiTheta_add_one]
  rw [show τ + 1 + 1 = 2 + τ by ring]
  exact jacobiTheta_two_add τ

private lemma jacobiTheta₂_diag_add_one (τ : ℂ) :
    jacobiTheta₂ ((τ + 1) / 2) (τ + 1) = jacobiTheta₂ (τ / 2) τ := by
  unfold jacobiTheta₂ jacobiTheta₂_term
  apply tsum_congr
  intro n
  have hEven : Even (n + n ^ 2) := by
    have h := Int.even_mul_succ_self n
    convert h using 1
    ring
  rcases hEven with ⟨k, hk⟩
  rw [show 2 * Real.pi * Complex.I * ↑n * ((τ + 1) / 2) +
        Real.pi * Complex.I * ↑n ^ 2 * (τ + 1) =
      (2 * Real.pi * Complex.I * ↑n * (τ / 2) +
        Real.pi * Complex.I * ↑n ^ 2 * τ) +
        Real.pi * Complex.I * (((n + n ^ 2 : ℤ) : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_add]
  rw [hk]
  push_cast
  rw [show Real.pi * Complex.I * ((k : ℂ) + k) =
      (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  rw [mul_one]

lemma thetaTwoConst_add_one (τ : ℂ) :
    thetaTwoConst (τ + 1) =
      Complex.exp (Real.pi * Complex.I / 4) * thetaTwoConst τ := by
  unfold thetaTwoConst
  rw [jacobiTheta₂_diag_add_one]
  rw [show Real.pi * Complex.I * (τ + 1) / 4 =
      Real.pi * Complex.I / 4 + Real.pi * Complex.I * τ / 4 by ring]
  rw [Complex.exp_add]
  ring

lemma cpow_half_pow_eight (z : ℂ) :
    (z ^ (1 / 2 : ℂ)) ^ 8 = z ^ 4 := by
  have h2 : (z ^ (2⁻¹ : ℂ)) ^ 2 = z :=
    Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)
  calc
    (z ^ (1 / 2 : ℂ)) ^ 8 = ((z ^ (2⁻¹ : ℂ)) ^ 2) ^ 4 := by
      norm_num
      ring
    _ = z ^ 4 := by rw [h2]

lemma differentiableAt_thetaFourConst {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaFourConst τ := by
  unfold thetaFourConst
  exact differentiableAt_jacobiTheta₂_snd (1 / 2) hτ

lemma thetaTwoConst_neg_inv (τ : ℂ) (hτ : τ ≠ 0) :
    thetaTwoConst (-1 / τ) =
      (-Complex.I * τ) ^ (1 / 2 : ℂ) * thetaFourConst τ := by
  unfold thetaTwoConst thetaFourConst
  rw [show (-1 / τ) / 2 = -((1 / 2 : ℂ) / τ) by ring]
  rw [jacobiTheta₂_neg_left]
  have hA : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ
  have hE :
      Complex.exp (-Real.pi * Complex.I * (1 / 2 : ℂ)^2 / τ) ≠ 0 :=
    Complex.exp_ne_zero _
  have hfe := jacobiTheta₂_functional_equation (1 / 2 : ℂ) τ
  have hsolve :
      jacobiTheta₂ ((1 / 2 : ℂ) / τ) (-1 / τ) =
        (-Complex.I * τ) ^ (1 / 2 : ℂ) *
          Complex.exp (Real.pi * Complex.I * (1 / 2 : ℂ)^2 / τ) *
            jacobiTheta₂ (1 / 2) τ := by
    rw [hfe]
    field_simp [hA, hE]
    set A : ℂ := Complex.I * ↑Real.pi / (2 ^ 2 * τ)
    change jacobiTheta₂ (1 / (2 * τ)) (-(1 / τ)) =
      jacobiTheta₂ (1 / (2 * τ)) (-(1 / τ)) * Complex.exp A * Complex.exp (-A)
    have hAexp : Complex.exp A * Complex.exp (-A) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc
      jacobiTheta₂ (1 / (2 * τ)) (-(1 / τ))
          = jacobiTheta₂ (1 / (2 * τ)) (-(1 / τ)) * 1 := by ring
      _ = jacobiTheta₂ (1 / (2 * τ)) (-(1 / τ)) *
            (Complex.exp A * Complex.exp (-A)) := by rw [hAexp]
      _ = jacobiTheta₂ (1 / (2 * τ)) (-(1 / τ)) * Complex.exp A * Complex.exp (-A) := by ring
  rw [hsolve]
  rw [show Real.pi * Complex.I * (-1 / τ) / 4 =
      -(Real.pi * Complex.I * (1 / 2 : ℂ)^2 / τ) by ring]
  rw [Complex.exp_neg]
  field_simp [Complex.exp_ne_zero (Real.pi * Complex.I * (1 / 2 : ℂ)^2 / τ)]

lemma thetaFourConst_neg_inv (τ : ℂ) (hτ : τ ≠ 0) :
    thetaFourConst (-1 / τ) =
      (-Complex.I * τ) ^ (1 / 2 : ℂ) * thetaTwoConst τ := by
  let A : ℂ := (-Complex.I * τ) ^ (1 / 2 : ℂ)
  let E : ℂ := Complex.exp (-Real.pi * Complex.I * (τ / 2)^2 / τ)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact (cpow_ne_zero_iff_of_exponent_ne_zero
      (by norm_num : (1 / 2 : ℂ) ≠ 0)).2
        (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ)
  have hE : E ≠ 0 := by
    dsimp [E]
    exact Complex.exp_ne_zero _
  have hE_eval : E = Complex.exp (-(Real.pi * Complex.I * τ / 4)) := by
    dsimp [E]
    congr 1
    field_simp [hτ]
    ring
  have hFE := jacobiTheta₂_functional_equation (τ / 2) τ
  have hFE' :
      jacobiTheta₂ (τ / 2) τ =
        (1 / A) * E * jacobiTheta₂ (1 / 2) (-1 / τ) := by
    simpa [A, E, hτ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hFE
  have hsolve :
      jacobiTheta₂ (1 / 2) (-1 / τ) =
        A * Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
    calc
      jacobiTheta₂ (1 / 2) (-1 / τ)
          = A * E⁻¹ * jacobiTheta₂ (τ / 2) τ := by
              rw [hFE']
              field_simp [hA, hE]
      _ = A * Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
              rw [hE_eval]
              rw [show (Complex.exp (-(Real.pi * Complex.I * τ / 4)))⁻¹ =
                  Complex.exp (Real.pi * Complex.I * τ / 4) by
                rw [← Complex.exp_neg]
                simp]
  unfold thetaFourConst thetaTwoConst
  rw [hsolve]
  ring

lemma thetaTwoConst_neg_inv_pow_eight (τ : ℂ) (hτ : τ ≠ 0) :
    thetaTwoConst (-1 / τ) ^ 8 = τ ^ 4 * thetaFourConst τ ^ 8 := by
  rw [thetaTwoConst_neg_inv τ hτ]
  rw [mul_pow, cpow_half_pow_eight]
  ring_nf
  norm_num [Complex.I_mul_I]

lemma thetaFourConst_neg_inv_pow_eight (τ : ℂ) (hτ : τ ≠ 0) :
    thetaFourConst (-1 / τ) ^ 8 = τ ^ 4 * thetaTwoConst τ ^ 8 := by
  rw [thetaFourConst_neg_inv τ hτ]
  rw [mul_pow, cpow_half_pow_eight]
  ring_nf
  norm_num [Complex.I_mul_I]

lemma jacobiTheta_neg_inv_pow_eight (τ : ℍ) :
    jacobiTheta (-1 / (τ : ℂ)) ^ 8 =
      (τ : ℂ) ^ 4 * jacobiTheta (τ : ℂ) ^ 8 := by
  rw [show -1 / (τ : ℂ) = -(τ : ℂ)⁻¹ by ring]
  rw [← show ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ by
    rw [UpperHalfPlane.modular_S_smul]
    simp]
  rw [jacobiTheta_S_smul τ]
  rw [mul_pow, cpow_half_pow_eight]
  ring_nf
  norm_num [Complex.I_mul_I]

noncomputable def thetaE4Sum (τ : ℂ) : ℂ :=
  thetaTwoConst τ ^ 8 + jacobiTheta τ ^ 8 + thetaFourConst τ ^ 8

lemma thetaE4Sum_add_one (τ : ℂ) :
    thetaE4Sum (τ + 1) = thetaE4Sum τ := by
  unfold thetaE4Sum
  rw [thetaTwoConst_add_one, jacobiTheta_add_one, thetaFourConst_add_one]
  rw [mul_pow]
  have hroot : Complex.exp (Real.pi * Complex.I / 4) ^ 8 = 1 := by
    rw [← Complex.exp_nat_mul]
    rw [show (8 : ℕ) * (Real.pi * Complex.I / 4) =
        2 * Real.pi * Complex.I by
      norm_num
      ring]
    rw [Complex.exp_two_pi_mul_I]
  rw [hroot]
  ring

lemma thetaE4Sum_neg_inv (τ : ℍ) :
    thetaE4Sum (-1 / (τ : ℂ)) =
      (τ : ℂ)^4 * thetaE4Sum (τ : ℂ) := by
  unfold thetaE4Sum
  rw [thetaTwoConst_neg_inv_pow_eight (τ : ℂ) (UpperHalfPlane.ne_zero τ)]
  rw [thetaFourConst_neg_inv_pow_eight (τ : ℂ) (UpperHalfPlane.ne_zero τ)]
  rw [jacobiTheta_neg_inv_pow_eight τ]
  ring

/-- The theta-constant presentation of the classical Legendre modular lambda parameter. -/
noncomputable def thetaLambda (τ : ℂ) : ℂ :=
  thetaTwoConst τ ^ 4 / jacobiTheta τ ^ 4

lemma thetaLambda_eq (τ : ℂ) :
    thetaLambda τ = thetaTwoConst τ ^ 4 / jacobiTheta τ ^ 4 := rfl

lemma thetaTwoConst_pow_four (τ : ℂ) :
    thetaTwoConst τ ^ 4 =
      Complex.exp (Real.pi * Complex.I * τ) * jacobiTheta₂ (τ / 2) τ ^ 4 := by
  unfold thetaTwoConst
  rw [mul_pow]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma thetaLambda_eq_exp_mul_raw (τ : ℂ) :
    thetaLambda τ =
      Complex.exp (Real.pi * Complex.I * τ) *
        (jacobiTheta₂ (τ / 2) τ ^ 4 / jacobiTheta τ ^ 4) := by
  rw [thetaLambda_eq, thetaTwoConst_pow_four]
  ring

lemma thetaTwoConst_two_add (τ : ℂ) :
    thetaTwoConst (τ + 2) = Complex.I * thetaTwoConst τ := by
  unfold thetaTwoConst
  rw [show (τ + 2) / 2 = τ / 2 + 1 by ring]
  rw [jacobiTheta₂_add_right (τ / 2 + 1) τ]
  rw [jacobiTheta₂_add_left (τ / 2) τ]
  rw [show Real.pi * Complex.I * (τ + 2) / 4 =
      Real.pi * Complex.I * τ / 4 + Real.pi / 2 * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  ring

lemma thetaLambda_two_add (τ : ℂ) :
    thetaLambda (τ + 2) = thetaLambda τ := by
  unfold thetaLambda
  rw [thetaTwoConst_two_add]
  rw [show τ + 2 = 2 + τ by ring, jacobiTheta_two_add]
  rw [mul_pow]
  rw [show Complex.I ^ 4 = 1 by norm_num [Complex.ext]]
  ring_nf

lemma thetaLambda_add_two_mul_nat (τ : ℂ) :
    ∀ n : ℕ, thetaLambda (τ + 2 * (n : ℂ)) = thetaLambda τ
  | 0 => by simp
  | n + 1 => by
      rw [show τ + 2 * ((n + 1 : ℕ) : ℂ) = (τ + 2 * (n : ℂ)) + 2 by
        norm_num
        ring]
      rw [thetaLambda_two_add, thetaLambda_add_two_mul_nat τ n]

/-- The Jacobi quartic defect.  The classical identity is exactly
`jacobiQuarticDefect τ = 0`. -/
noncomputable def jacobiQuarticDefect (τ : ℂ) : ℂ :=
  jacobiTheta τ ^ 4 - thetaTwoConst τ ^ 4 - thetaFourConst τ ^ 4

lemma jacobiQuarticDefect_eq_zero_iff (τ : ℂ) :
    jacobiQuarticDefect τ = 0 ↔
      jacobiTheta τ ^ 4 = thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4 := by
  unfold jacobiQuarticDefect
  constructor <;> intro h <;> linear_combination h

lemma jacobiQuarticDefect_two_add (τ : ℂ) :
    jacobiQuarticDefect (τ + 2) = jacobiQuarticDefect τ := by
  unfold jacobiQuarticDefect
  rw [show τ + 2 = 2 + τ by ring, jacobiTheta_two_add]
  rw [show 2 + τ = τ + 2 by ring]
  rw [thetaTwoConst_two_add, thetaFourConst_two_add]
  rw [mul_pow]
  rw [show Complex.I ^ 4 = 1 by norm_num [Complex.ext]]
  ring

lemma jacobiQuarticDefect_neg_inv (τ : ℍ) :
    jacobiQuarticDefect (-1 / (τ : ℂ)) =
      ((-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 *
        jacobiQuarticDefect (τ : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hS : jacobiTheta (-(τ : ℂ)⁻¹) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta (τ : ℂ) := by
    have hraw := jacobiTheta_S_smul τ
    rw [UpperHalfPlane.modular_S_smul] at hraw
    simpa [one_div] using hraw
  unfold jacobiQuarticDefect
  rw [show -1 / (τ : ℂ) = -((τ : ℂ)⁻¹) by ring]
  rw [hS]
  rw [show -((τ : ℂ)⁻¹) = -1 / (τ : ℂ) by ring]
  rw [thetaTwoConst_neg_inv (τ : ℂ) hτ]
  rw [thetaFourConst_neg_inv (τ : ℂ) hτ]
  ring

lemma jacobiQuarticDefect_add_two_mul_nat (τ : ℂ) :
    ∀ n : ℕ, jacobiQuarticDefect (τ + 2 * (n : ℂ)) = jacobiQuarticDefect τ
  | 0 => by simp
  | n + 1 => by
      rw [show τ + 2 * ((n + 1 : ℕ) : ℂ) = (τ + 2 * (n : ℂ)) + 2 by
        norm_num
        ring]
      rw [jacobiQuarticDefect_two_add, jacobiQuarticDefect_add_two_mul_nat τ n]

lemma thetaLambda_neg_inv_of_jacobi_quartic (τ : ℍ)
    (hθ : jacobiTheta (τ : ℂ) ≠ 0)
    (hJac : jacobiTheta (τ : ℂ) ^ 4 =
      thetaTwoConst (τ : ℂ) ^ 4 + thetaFourConst (τ : ℂ) ^ 4) :
    thetaLambda (-1 / (τ : ℂ)) = 1 - thetaLambda (τ : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hA : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ
  have hS : jacobiTheta (-(τ : ℂ)⁻¹) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta (τ : ℂ) := by
    have hraw := jacobiTheta_S_smul τ
    rw [UpperHalfPlane.modular_S_smul] at hraw
    simpa [one_div] using hraw
  unfold thetaLambda
  rw [thetaTwoConst_neg_inv (τ : ℂ) hτ]
  rw [show -1 / (τ : ℂ) = -((τ : ℂ)⁻¹) by ring]
  rw [hS]
  field_simp [hθ, hA]
  rw [hJac]
  ring

lemma thetaLambda_neg_inv_of_jacobiQuarticDefect_zero (τ : ℍ)
    (hθ : jacobiTheta (τ : ℂ) ≠ 0)
    (hDef : jacobiQuarticDefect (τ : ℂ) = 0) :
    thetaLambda (-1 / (τ : ℂ)) = 1 - thetaLambda (τ : ℂ) :=
  thetaLambda_neg_inv_of_jacobi_quartic τ hθ
    ((jacobiQuarticDefect_eq_zero_iff (τ : ℂ)).1 hDef)

lemma one_sub_thetaLambda_of_jacobi_quartic (τ : ℂ)
    (hθ : jacobiTheta τ ≠ 0)
    (hJac : jacobiTheta τ ^ 4 = thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4) :
    1 - thetaLambda τ = thetaFourConst τ ^ 4 / jacobiTheta τ ^ 4 := by
  unfold thetaLambda
  field_simp [pow_ne_zero 4 hθ]
  linear_combination hJac

lemma one_sub_thetaLambda_of_jacobiQuarticDefect_zero (τ : ℂ)
    (hθ : jacobiTheta τ ≠ 0)
    (hDef : jacobiQuarticDefect τ = 0) :
    1 - thetaLambda τ = thetaFourConst τ ^ 4 / jacobiTheta τ ^ 4 :=
  one_sub_thetaLambda_of_jacobi_quartic τ hθ
    ((jacobiQuarticDefect_eq_zero_iff τ).1 hDef)

lemma kleinJFromLambda_thetaLambda_of_jacobi_quartic (τ : ℂ)
    (hθ : jacobiTheta τ ≠ 0)
    (hθ₂ : thetaTwoConst τ ≠ 0)
    (hθ₄ : thetaFourConst τ ≠ 0)
    (hJac : jacobiTheta τ ^ 4 = thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4) :
    kleinJFromLambda (thetaLambda τ) =
      256 * (jacobiTheta τ ^ 8 - thetaTwoConst τ ^ 4 * thetaFourConst τ ^ 4) ^ 3 /
        (thetaTwoConst τ ^ 8 * thetaFourConst τ ^ 8 * jacobiTheta τ ^ 8) := by
  have hθ4pow : jacobiTheta τ ^ 4 ≠ 0 := pow_ne_zero 4 hθ
  have hθ8pow : jacobiTheta τ ^ 8 ≠ 0 := pow_ne_zero 8 hθ
  have hθ2pow : thetaTwoConst τ ^ 4 ≠ 0 := pow_ne_zero 4 hθ₂
  have hθ4cpow : thetaFourConst τ ^ 4 ≠ 0 := pow_ne_zero 4 hθ₄
  have hLam : thetaLambda τ = thetaTwoConst τ ^ 4 / jacobiTheta τ ^ 4 := rfl
  have hOneLam : 1 - thetaLambda τ = thetaFourConst τ ^ 4 / jacobiTheta τ ^ 4 :=
    one_sub_thetaLambda_of_jacobi_quartic τ hθ hJac
  have hOneQuot :
      1 - thetaTwoConst τ ^ 4 / jacobiTheta τ ^ 4 =
        thetaFourConst τ ^ 4 / jacobiTheta τ ^ 4 := by
    simpa [hLam] using hOneLam
  unfold kleinJFromLambda
  rw [hLam, hOneQuot]
  field_simp [hθ4pow, hθ8pow, hθ2pow, hθ4cpow]
  rw [show jacobiTheta τ ^ 4 = thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4 from hJac]
  rw [show jacobiTheta τ ^ 8 = (thetaTwoConst τ ^ 4 + thetaFourConst τ ^ 4)^2 by
    rw [← hJac]
    ring]
  ring

lemma kleinJFromLambda_thetaLambda_of_jacobiQuarticDefect_zero (τ : ℂ)
    (hθ : jacobiTheta τ ≠ 0)
    (hθ₂ : thetaTwoConst τ ≠ 0)
    (hθ₄ : thetaFourConst τ ≠ 0)
    (hDef : jacobiQuarticDefect τ = 0) :
    kleinJFromLambda (thetaLambda τ) =
      256 * (jacobiTheta τ ^ 8 - thetaTwoConst τ ^ 4 * thetaFourConst τ ^ 4) ^ 3 /
        (thetaTwoConst τ ^ 8 * thetaFourConst τ ^ 8 * jacobiTheta τ ^ 8) :=
  kleinJFromLambda_thetaLambda_of_jacobi_quartic τ hθ hθ₂ hθ₄
    ((jacobiQuarticDefect_eq_zero_iff τ).1 hDef)

lemma differentiableAt_jacobiTheta₂_diag_half {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ (w / 2) w) τ := by
  have hpair : DifferentiableAt ℂ (fun w : ℂ => (w / 2, w)) τ := by
    fun_prop
  have htheta :
      DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (τ / 2, τ) := by
    exact (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
  exact DifferentiableAt.comp (f := fun w : ℂ => (w / 2, w))
    (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) τ htheta hpair

lemma differentiableAt_thetaTwoConst {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaTwoConst τ := by
  unfold thetaTwoConst
  exact (by fun_prop : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (Real.pi * Complex.I * w / 4)) τ).mul
    (differentiableAt_jacobiTheta₂_diag_half hτ)

lemma differentiableAt_thetaLambda {τ : ℂ} (hτ : 0 < τ.im)
    (hθ : jacobiTheta τ ≠ 0) :
    DifferentiableAt ℂ thetaLambda τ := by
  unfold thetaLambda
  exact ((differentiableAt_thetaTwoConst hτ).pow 4).div
    ((differentiableAt_jacobiTheta hτ).pow 4) (pow_ne_zero 4 hθ)

lemma differentiableAt_jacobiQuarticDefect {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ jacobiQuarticDefect τ := by
  unfold jacobiQuarticDefect
  exact (((differentiableAt_jacobiTheta hτ).pow 4).sub
    ((differentiableAt_thetaTwoConst hτ).pow 4)).sub
      ((differentiableAt_thetaFourConst hτ).pow 4)

lemma continuousAt_jacobiQuarticDefect {τ : ℂ} (hτ : 0 < τ.im) :
    ContinuousAt jacobiQuarticDefect τ :=
  (differentiableAt_jacobiQuarticDefect hτ).continuousAt

lemma differentiableAt_kleinJFromLambda {lam : ℂ} (h0 : lam ≠ 0)
    (h1 : 1 - lam ≠ 0) :
    DifferentiableAt ℂ kleinJFromLambda lam := by
  unfold kleinJFromLambda
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 h1)

lemma differentiableAt_kleinJFromLambda_ramanujanTarget :
    DifferentiableAt ℂ kleinJFromLambda ramanujanLambda58Target :=
  differentiableAt_kleinJFromLambda ramanujanLambda58Target_ne_zero
    ramanujanLambda58Target_one_sub_ne_zero

/-- Ramanujan's level-58 singular-modulus statement, isolated as a proposition
for downstream proof by theta/eta transformations. -/
def RamanujanLambda58Statement : Prop :=
  thetaLambda (ramanujanTau58 : ℂ) = ramanujanLambda58Target

lemma RamanujanLambda58Statement.sq (h : RamanujanLambda58Statement) :
    thetaLambda (ramanujanTau58 : ℂ) ^ 2 = 1 / (99 : ℂ)^4 := by
  rw [h, ramanujanLambda58Target_sq]

lemma kleinJFromLambda_ramanujanLambda58Target :
    kleinJFromLambda ramanujanLambda58Target =
      (3544454449806874081077604 : ℂ) / 144149438750625 := by
  norm_num [kleinJFromLambda, ramanujanLambda58Target]

lemma deriv_kleinJFromLambda_ramanujanLambda58Target :
    deriv kleinJFromLambda ramanujanLambda58Target =
      -(8684356187587639410587785699 : ℂ) / 18016841390625 := by
  rw [deriv_kleinJFromLambda ramanujanLambda58Target_ne_zero
    ramanujanLambda58Target_one_sub_ne_zero]
  norm_num [ramanujanLambda58Target]

lemma heegnerTau163_q :
    Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)) =
      -Real.exp (-Real.pi * Real.sqrt 163) := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (heegnerTau163 : ℂ) =
      (Real.pi * Complex.I) + ((-Real.pi * Real.sqrt 163 : ℝ) : ℂ) by
    apply Complex.ext <;> simp [heegnerTau163, Complex.mul_re, Complex.mul_im] <;> ring]
  rw [Complex.exp_add]
  rw [show Complex.exp (Real.pi * Complex.I) = -1 by simp]
  simp [Complex.ofReal_exp]

lemma heegnerTau163_q_double :
    Complex.exp (4 * Real.pi * Complex.I * (heegnerTau163 : ℂ)) =
      Real.exp (-(2 * Real.pi * Real.sqrt 163)) := by
  rw [show 4 * (Real.pi : ℂ) * Complex.I * (heegnerTau163 : ℂ) =
      2 * Real.pi * Complex.I + ((-(2 * Real.pi * Real.sqrt 163) : ℝ) : ℂ) by
    apply Complex.ext <;> simp [heegnerTau163, Complex.mul_re, Complex.mul_im] <;> ring]
  rw [Complex.exp_add]
  rw [Complex.exp_two_pi_mul_I]
  simp [Complex.ofReal_exp]

lemma heegnerTau163_q_half :
    Complex.exp (Real.pi * Complex.I * (heegnerTau163 : ℂ)) =
      Complex.I * Real.exp (-(Real.pi * Real.sqrt 163 / 2)) := by
  rw [show (Real.pi : ℂ) * Complex.I * (heegnerTau163 : ℂ) =
      Real.pi * Complex.I / 2 + ((-(Real.pi * Real.sqrt 163 / 2) : ℝ) : ℂ) by
    apply Complex.ext <;> simp [heegnerTau163, Complex.mul_re, Complex.mul_im] <;> ring]
  rw [Complex.exp_add]
  rw [show Complex.exp ((Real.pi : ℂ) * Complex.I / 2) =
      Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) by
    congr 1
    ring]
  rw [Complex.exp_pi_div_two_mul_I]
  simp [Complex.ofReal_exp]

lemma modularLambdaEta_heegnerTau163_product_form :
    modularLambdaEta (heegnerTau163 : ℂ) =
      16 * (Complex.I * (Real.exp (-(Real.pi * Real.sqrt 163 / 2)) : ℂ)) *
        ((∏' n : ℕ, (1 - ModularForm.eta_q n ((heegnerTau163 : ℂ) / 2))) ^ 8 *
          (∏' n : ℕ, (1 - ModularForm.eta_q n (2 * (heegnerTau163 : ℂ)))) ^ 16 /
            (∏' n : ℕ, (1 - ModularForm.eta_q n (heegnerTau163 : ℂ))) ^ 24) := by
  rw [modularLambdaEta_eq_q_prefactor_products, heegnerTau163_q_half]

lemma modularLambdaEta_heegnerTau163_qPochhammer_form :
    modularLambdaEta (heegnerTau163 : ℂ) =
      16 * (Complex.I * (Real.exp (-(Real.pi * Real.sqrt 163 / 2)) : ℂ)) *
        (qPochhammerInf (Complex.I * (Real.exp (-(Real.pi * Real.sqrt 163 / 2)) : ℂ)) ^ 8 *
          qPochhammerInf (Real.exp (-(2 * Real.pi * Real.sqrt 163)) : ℂ) ^ 16 /
            qPochhammerInf (-(Real.exp (-Real.pi * Real.sqrt 163) : ℂ)) ^ 24) := by
  rw [modularLambdaEta_eq_qPochhammerInf]
  rw [heegnerTau163_q_half, heegnerTau163_q_double, heegnerTau163_q]

lemma heegnerTau163_quadratic :
    (heegnerTau163 : ℂ)^2 - (heegnerTau163 : ℂ) + 41 = 0 := by
  have hs : ((Real.sqrt 163 : ℝ) : ℂ)^2 = 163 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 163)
  rw [heegnerTau163]
  ring_nf
  rw [hs]
  norm_num

/-- Chudnovsky's `₃F₂` argument recovered from the `j`-value. -/
lemma chudnovsky_argument_from_j_target :
    (1728 : ℂ) / heegnerJ163Target = -1728 / (640320 : ℂ)^3 := by
  unfold heegnerJ163Target
  norm_num

lemma heegnerJ163Target_ne_zero :
    heegnerJ163Target ≠ 0 := by
  unfold heegnerJ163Target
  norm_num

end Modular
end Number
end Ripple
