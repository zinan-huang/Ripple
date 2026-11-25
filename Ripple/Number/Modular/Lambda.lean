import Ripple.Number.Modular.KleinJ
import Ripple.Number.Modular.QPochhammer
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

/-!
# Modular lambda objects

This file introduces the eta-quotient presentation of the classical modular
lambda function.  The transformation laws and CM evaluations are deliberately
kept as downstream proof targets; this file contains only definitions and
algebraic normalization lemmas.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Complex
open scoped UpperHalfPlane

/-- Eta-quotient expression for the classical modular lambda function. -/
noncomputable def modularLambdaEta (τ : ℂ) : ℂ :=
  16 * ModularForm.eta (τ / 2) ^ 8 * ModularForm.eta (2 * τ) ^ 16 /
    ModularForm.eta τ ^ 24

/-- The eta-quotient lambda value at the discriminant `-163` Heegner point. -/
noncomputable def lambdaEta163 : ℂ :=
  modularLambdaEta (heegnerTau163 : ℂ)

lemma modularLambdaEta_eq (τ : ℂ) :
    modularLambdaEta τ =
      16 * ModularForm.eta (τ / 2) ^ 8 * ModularForm.eta (2 * τ) ^ 16 /
        ModularForm.eta τ ^ 24 := rfl

lemma modularLambdaEta_eq_q_tprod (τ : ℂ) :
    modularLambdaEta τ =
      16 *
        (Function.Periodic.qParam 24 (τ / 2) *
            ∏' n : ℕ, (1 - ModularForm.eta_q n (τ / 2))) ^ 8 *
        (Function.Periodic.qParam 24 (2 * τ) *
            ∏' n : ℕ, (1 - ModularForm.eta_q n (2 * τ))) ^ 16 /
        (Function.Periodic.qParam 24 τ *
            ∏' n : ℕ, (1 - ModularForm.eta_q n τ)) ^ 24 := by
  unfold modularLambdaEta ModularForm.eta
  rfl

lemma modularLambdaEta_q_prefactor (τ : ℂ) :
    Function.Periodic.qParam 24 (τ / 2) ^ 8 *
        Function.Periodic.qParam 24 (2 * τ) ^ 16 /
      Function.Periodic.qParam 24 τ ^ 24 =
        Complex.exp (Real.pi * Complex.I * τ) := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  field_simp
  norm_num

lemma modularLambdaEta_eq_q_prefactor_products (τ : ℂ) :
    modularLambdaEta τ =
      16 * Complex.exp (Real.pi * Complex.I * τ) *
        ((∏' n : ℕ, (1 - ModularForm.eta_q n (τ / 2))) ^ 8 *
          (∏' n : ℕ, (1 - ModularForm.eta_q n (2 * τ))) ^ 16 /
            (∏' n : ℕ, (1 - ModularForm.eta_q n τ)) ^ 24) := by
  rw [modularLambdaEta_eq_q_tprod]
  rw [mul_pow, mul_pow, mul_pow]
  rw [show
      16 *
          (Function.Periodic.qParam 24 (τ / 2) ^ 8 *
            (∏' n : ℕ, (1 - ModularForm.eta_q n (τ / 2))) ^ 8) *
          (Function.Periodic.qParam 24 (2 * τ) ^ 16 *
            (∏' n : ℕ, (1 - ModularForm.eta_q n (2 * τ))) ^ 16) /
          (Function.Periodic.qParam 24 τ ^ 24 *
            (∏' n : ℕ, (1 - ModularForm.eta_q n τ)) ^ 24)
        =
      16 *
        (Function.Periodic.qParam 24 (τ / 2) ^ 8 *
          Function.Periodic.qParam 24 (2 * τ) ^ 16 /
            Function.Periodic.qParam 24 τ ^ 24) *
        ((∏' n : ℕ, (1 - ModularForm.eta_q n (τ / 2))) ^ 8 *
          (∏' n : ℕ, (1 - ModularForm.eta_q n (2 * τ))) ^ 16 /
            (∏' n : ℕ, (1 - ModularForm.eta_q n τ)) ^ 24) by
    have hq : Function.Periodic.qParam 24 τ ^ 24 ≠ 0 :=
      pow_ne_zero 24 (Function.Periodic.qParam_ne_zero τ)
    field_simp [hq]
    ]
  rw [modularLambdaEta_q_prefactor]

lemma modularLambdaEta_eq_qPochhammerInf (τ : ℂ) :
    modularLambdaEta τ =
      16 * Complex.exp (Real.pi * Complex.I * τ) *
        (qPochhammerInf (Complex.exp (Real.pi * Complex.I * τ)) ^ 8 *
          qPochhammerInf (Complex.exp (4 * Real.pi * Complex.I * τ)) ^ 16 /
            qPochhammerInf (Complex.exp (2 * Real.pi * Complex.I * τ)) ^ 24) := by
  rw [modularLambdaEta_eq_q_prefactor_products]
  rw [show (∏' n : ℕ, (1 - ModularForm.eta_q n (τ / 2))) =
      qPochhammerInf (Complex.exp (Real.pi * Complex.I * τ)) by
    rw [← qPochhammerInf_eq_eta_tprod (τ / 2)]
    congr 1
    congr 1
    ring]
  rw [show (∏' n : ℕ, (1 - ModularForm.eta_q n (2 * τ))) =
      qPochhammerInf (Complex.exp (4 * Real.pi * Complex.I * τ)) by
    rw [← qPochhammerInf_eq_eta_tprod (2 * τ)]
    congr 1
    congr 1
    ring]
  rw [show (∏' n : ℕ, (1 - ModularForm.eta_q n τ)) =
      qPochhammerInf (Complex.exp (2 * Real.pi * Complex.I * τ)) by
    rw [← qPochhammerInf_eq_eta_tprod τ]]

lemma lambdaEta163_eq :
    lambdaEta163 = modularLambdaEta (heegnerTau163 : ℂ) := rfl

lemma eta_heegnerTau163_ne_zero :
    ModularForm.eta (heegnerTau163 : ℂ) ≠ 0 :=
  ModularForm.eta_ne_zero heegnerTau163.2

lemma eta_heegnerTau163_div_two_ne_zero :
    ModularForm.eta ((heegnerTau163 : ℂ) / 2) ≠ 0 := by
  apply ModularForm.eta_ne_zero
  change 0 < (((heegnerTau163 : ℂ) / 2).im)
  rw [Complex.div_im]
  norm_num
  positivity

lemma eta_two_mul_heegnerTau163_ne_zero :
    ModularForm.eta (2 * (heegnerTau163 : ℂ)) ≠ 0 := by
  apply ModularForm.eta_ne_zero
  change 0 < ((2 * (heegnerTau163 : ℂ)).im)
  rw [Complex.mul_im]
  norm_num
  positivity

lemma lambdaEta163_den_ne_zero :
    ModularForm.eta (heegnerTau163 : ℂ) ^ 24 ≠ 0 :=
  pow_ne_zero 24 eta_heegnerTau163_ne_zero

lemma lambdaEta163_ne_zero : lambdaEta163 ≠ 0 := by
  unfold lambdaEta163 modularLambdaEta
  have hnum : 16 * ModularForm.eta ((heegnerTau163 : ℂ) / 2) ^ 8 *
      ModularForm.eta (2 * (heegnerTau163 : ℂ)) ^ 16 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 8 eta_heegnerTau163_div_two_ne_zero))
      (pow_ne_zero 16 eta_two_mul_heegnerTau163_ne_zero)
  exact div_ne_zero hnum lambdaEta163_den_ne_zero

/-- The rational function connecting the Legendre lambda parameter with Klein's `j`. -/
noncomputable def kleinJFromLambda (lam : ℂ) : ℂ :=
  256 * (1 - lam + lam ^ 2) ^ 3 / (lam ^ 2 * (1 - lam) ^ 2)

lemma kleinJFromLambda_eq (lam : ℂ) :
    kleinJFromLambda lam =
      256 * (1 - lam + lam ^ 2) ^ 3 / (lam ^ 2 * (1 - lam) ^ 2) := rfl

lemma hasDerivAt_kleinJFromLambda {lam : ℂ} (h0 : lam ≠ 0) (h1 : 1 - lam ≠ 0) :
    HasDerivAt kleinJFromLambda
      (256 * (1 - lam + lam ^ 2) ^ 2 * (2 * lam - 1) * (2 + lam - lam ^ 2) /
        (lam ^ 3 * (1 - lam) ^ 3)) lam := by
  unfold kleinJFromLambda
  have hden : lam ^ 2 * (1 - lam) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 h1)
  have hnum : HasDerivAt (fun x : ℂ => 256 * (1 - x + x ^ 2) ^ 3)
      (256 * (3 * (1 - lam + lam ^ 2)^2 * (-1 + 2 * lam))) lam := by
    convert! (by fun_prop :
      DifferentiableAt ℂ (fun x : ℂ => 256 * (1 - x + x ^ 2) ^ 3) lam).hasDerivAt using 1
    have hinner : deriv (fun x : ℂ => 1 - x + x ^ 2) lam = -1 + 2 * lam := by
      rw [deriv_fun_add]
      · rw [deriv_const_sub, deriv_fun_pow]
        · simp [deriv_id'']
        · fun_prop
      · fun_prop
      · fun_prop
    rw [deriv_const_mul, deriv_fun_pow]
    · rw [hinner]
      ring
    · fun_prop
    · fun_prop
  have hden' : HasDerivAt (fun x : ℂ => x ^ 2 * (1 - x) ^ 2)
      (2 * lam * (1 - lam)^2 + lam^2 * (2 * (1 - lam) * (-1))) lam := by
    convert! (by fun_prop :
      DifferentiableAt ℂ (fun x : ℂ => x ^ 2 * (1 - x) ^ 2) lam).hasDerivAt using 1
    have hone : deriv (fun x : ℂ => 1 - x) lam = -1 := by
      rw [deriv_const_sub]
      simp [deriv_id'']
    rw [deriv_fun_mul]
    · rw [deriv_fun_pow, deriv_fun_pow]
      · rw [hone]
        simp [deriv_id'']
      · fun_prop
      · fun_prop
    · fun_prop
    · fun_prop
  convert! hnum.div hden' hden using 1
  field_simp [h0, h1]; ring

lemma deriv_kleinJFromLambda {lam : ℂ} (h0 : lam ≠ 0) (h1 : 1 - lam ≠ 0) :
    deriv kleinJFromLambda lam =
      256 * (1 - lam + lam ^ 2) ^ 2 * (2 * lam - 1) * (2 + lam - lam ^ 2) /
        (lam ^ 3 * (1 - lam) ^ 3) :=
  (hasDerivAt_kleinJFromLambda h0 h1).deriv

lemma kleinJFromLambda_one_sub (lam : ℂ) :
    kleinJFromLambda (1 - lam) = kleinJFromLambda lam := by
  unfold kleinJFromLambda
  ring_nf

lemma kleinJFromLambda_inv {lam : ℂ} (h : lam ≠ 0) :
    kleinJFromLambda lam⁻¹ = kleinJFromLambda lam := by
  unfold kleinJFromLambda
  field_simp [h]
  ring

lemma kleinJFromLambda_one_div {lam : ℂ} (h : lam ≠ 0) :
    kleinJFromLambda (1 / lam) = kleinJFromLambda lam := by
  simpa [one_div] using kleinJFromLambda_inv h

lemma kleinJFromLambda_one_div_one_sub {lam : ℂ} (h : 1 - lam ≠ 0) :
    kleinJFromLambda (1 / (1 - lam)) = kleinJFromLambda lam := by
  rw [kleinJFromLambda_one_div h, kleinJFromLambda_one_sub]

/-- The concrete CM evaluation statement needed for the Chudnovsky formula. -/
def KleinJCM163Statement : Prop :=
  kleinJ heegnerTau163 = heegnerJ163Target

/-- The corresponding lambda-evaluation statement. -/
def LambdaCM163Statement : Prop :=
  kleinJFromLambda lambdaEta163 = heegnerJ163Target

lemma LambdaCM163Statement.eq_target (h : LambdaCM163Statement) :
    kleinJFromLambda lambdaEta163 = heegnerJ163Target := h

lemma KleinJCM163Statement.eq_target (h : KleinJCM163Statement) :
    kleinJ heegnerTau163 = heegnerJ163Target := h

end Modular
end Number
end Ripple
