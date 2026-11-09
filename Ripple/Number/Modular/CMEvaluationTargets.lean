import Ripple.Number.Modular.SingularModuli
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Algebraic endpoints for the Ramanujan--Chudnovsky CM evaluations

This file contains the exact algebraic target equations that the analytic
CM-evaluation layer must prove for `thetaLambda ramanujanTau58` and
`kleinJ heegnerTau163`.  There are no analytic assertions here: every lemma is
an elementary calculation from the already-defined target constants.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Polynomial

/-- The degree-58 Ramanujan lambda target is `λ = 1 / 99^2`.  This linear
polynomial records the algebraic endpoint of the level-58 modular equation
after the correct CM branch has been selected. -/
noncomputable def ramanujanLambda58TargetPolynomial : ℂ[X] :=
  C ((99 : ℂ)^2) * X - 1

lemma ramanujanLambda58TargetPolynomial_eval :
    ramanujanLambda58TargetPolynomial.eval ramanujanLambda58Target = 0 := by
  norm_num [ramanujanLambda58TargetPolynomial, ramanujanLambda58Target]

lemma ramanujanLambda58TargetPolynomial_isRoot_iff {z : ℂ} :
    ramanujanLambda58TargetPolynomial.IsRoot z ↔ z = ramanujanLambda58Target := by
  unfold Polynomial.IsRoot ramanujanLambda58TargetPolynomial ramanujanLambda58Target
  constructor
  · intro h
    simp at h
    field_simp [show ((99 : ℂ)^2) ≠ 0 by norm_num] at h ⊢
    linear_combination h
  · intro h
    rw [h]
    norm_num

/-- The hypergeometric pullback is `x = λ^2 = 1 / 99^4`. -/
noncomputable def ramanujanPullback58TargetPolynomial : ℂ[X] :=
  C ((99 : ℂ)^4) * X - 1

lemma ramanujanPullback58TargetPolynomial_eval :
    ramanujanPullback58TargetPolynomial.eval (ramanujanLambda58Target ^ 2) = 0 := by
  norm_num [ramanujanPullback58TargetPolynomial, ramanujanLambda58Target]

lemma ramanujanPullback58TargetPolynomial_eval_ramanujanX :
    ramanujanPullback58TargetPolynomial.eval (1 / (99 : ℂ)^4) = 0 := by
  norm_num [ramanujanPullback58TargetPolynomial]

lemma ramanujanPullback58TargetPolynomial_isRoot_iff {z : ℂ} :
    ramanujanPullback58TargetPolynomial.IsRoot z ↔ z = 1 / (99 : ℂ)^4 := by
  unfold Polynomial.IsRoot ramanujanPullback58TargetPolynomial
  constructor
  · intro h
    simp at h
    field_simp [show ((99 : ℂ)^4) ≠ 0 by norm_num] at h ⊢
    linear_combination h
  · intro h
    rw [h]
    norm_num

/-- The rational number `256(1 - λ + λ^2)^3/(λ^2(1-λ)^2)` at `λ = 1/99²`. Since `1/99²` is not the
Legendre lambda value of `i√58/2`, this number is **not** `j(i√58/2)`. -/
noncomputable def ramanujanJ58Target : ℂ :=
  kleinJFromLambda ramanujanLambda58Target

lemma ramanujanJ58Target_eq :
    ramanujanJ58Target =
      (3544454449806874081077604 : ℂ) / 144149438750625 := by
  rw [ramanujanJ58Target, kleinJFromLambda_ramanujanLambda58Target]

/-- The linear rational class-polynomial endpoint for the branch selected by
`λ = 1 / 99^2`.  The full analytic proof still has to identify the CM value
with this branch. -/
noncomputable def ramanujanJ58TargetPolynomial : ℂ[X] :=
  C (144149438750625 : ℂ) * X - C (3544454449806874081077604 : ℂ)

lemma ramanujanJ58TargetPolynomial_eval :
    ramanujanJ58TargetPolynomial.eval ramanujanJ58Target = 0 := by
  rw [ramanujanJ58Target_eq]
  norm_num [ramanujanJ58TargetPolynomial]

lemma ramanujanJ58TargetPolynomial_isRoot_iff {z : ℂ} :
    ramanujanJ58TargetPolynomial.IsRoot z ↔ z = ramanujanJ58Target := by
  unfold Polynomial.IsRoot ramanujanJ58TargetPolynomial
  rw [ramanujanJ58Target_eq]
  constructor
  · intro h
    simp at h
    field_simp [show (144149438750625 : ℂ) ≠ 0 by norm_num] at h ⊢
    linear_combination h
  · intro h
    rw [h]
    norm_num

lemma kleinJFromLambda_ramanujanTarget_isRoot :
    ramanujanJ58TargetPolynomial.IsRoot (kleinJFromLambda ramanujanLambda58Target) := by
  simpa [Polynomial.IsRoot, ramanujanJ58Target] using ramanujanJ58TargetPolynomial_eval

/-- The class-number-one polynomial for the discriminant `-163` Heegner
`j`-value in this normalization. -/
noncomputable def heegnerJ163ClassPolynomial : ℂ[X] :=
  X - C (-((640320 : ℂ)^3))

lemma heegnerJ163ClassPolynomial_eval :
    heegnerJ163ClassPolynomial.eval heegnerJ163Target = 0 := by
  norm_num [heegnerJ163ClassPolynomial, heegnerJ163Target]

lemma heegnerJ163Target_isRoot_classPolynomial :
    heegnerJ163ClassPolynomial.IsRoot heegnerJ163Target := by
  simpa [Polynomial.IsRoot] using heegnerJ163ClassPolynomial_eval

lemma heegnerJ163ClassPolynomial_isRoot_iff {z : ℂ} :
    heegnerJ163ClassPolynomial.IsRoot z ↔ z = heegnerJ163Target := by
  unfold Polynomial.IsRoot heegnerJ163ClassPolynomial heegnerJ163Target
  constructor
  · intro h
    simp at h
    linear_combination h
  · intro h
    rw [h]
    norm_num

lemma heegnerJ163ClassPolynomial_monic :
    heegnerJ163ClassPolynomial.Monic := by
  exact monic_X_sub_C (-((640320 : ℂ)^3))

lemma heegnerJ163ClassPolynomial_natDegree :
    heegnerJ163ClassPolynomial.natDegree = 1 := by
  norm_num [heegnerJ163ClassPolynomial]

lemma heegnerJ163ClassPolynomial_ne_zero :
    heegnerJ163ClassPolynomial ≠ 0 := by
  intro h
  have hdeg := congrArg Polynomial.natDegree h
  rw [heegnerJ163ClassPolynomial_natDegree] at hdeg
  simp at hdeg

end Modular
end Number
end Ripple
