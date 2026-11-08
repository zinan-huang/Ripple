import Ripple.Number.Modular.ThetaQuartic
import Ripple.Number.Modular.CMEvaluationIsRoot
import Ripple.Number.Modular.ModularPoly41
import Ripple.Number.Modular.ModularPoly41Data
import Ripple.Number.Modular.ModularPolynomialSturmCertificate
import Ripple.Number.Modular.Phi41FrickeSturm
import Ripple.Number.Modular.Gamma0_41_SturmBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# CM evaluation at discriminant `-163`

This file is the discriminant `-163` endpoint for the Chudnovsky CM
calculation.  The route is the theta-lambda route from the round-16 handoff:

1. specialize the theta quartic identity at
   `τ₁₆₃ = (1 + i sqrt 163) / 2`;
2. compute `thetaLambda τ₁₆₃` by its tiny-q expansion;
3. push the resulting lambda value through
   `kleinJFromLambda`;
4. identify this with the level-one Klein invariant.

 No CM fact is pushed to the caller as a hypothesis.  The remaining modular
equation input is isolated as a concrete theorem gap at the CM point.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Polynomial
open CongruenceSubgroup
open scoped UpperHalfPlane BigOperators MatrixGroups Manifold ModularForm

/-- The theta-constant expression obtained from the Legendre lambda
presentation of the Klein invariant. -/
noncomputable def kleinJThetaExpression (τ : ℂ) : ℂ :=
  256 * (jacobiTheta τ ^ 8 - thetaTwoConst τ ^ 4 * thetaFourConst τ ^ 4) ^ 3 /
    (thetaTwoConst τ ^ 8 * thetaFourConst τ ^ 8 * jacobiTheta τ ^ 8)

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

private lemma exp_neg_pi_mul_im_lt_one_third {τ : ℂ}
    (him : 1 ≤ τ.im) :
    Real.exp (-Real.pi * τ.im) < (1 / 3 : ℝ) := by
  have hle : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, him]
  exact hle.trans_lt exp_neg_pi_lt_one_third

private lemma norm_exp_pi_I_mul (τ : ℂ) :
    ‖Complex.exp (Real.pi * Complex.I * τ)‖ =
      Real.exp (-Real.pi * τ.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

private lemma heegnerTau163_one_le_im_local :
    1 ≤ (heegnerTau163 : ℂ).im := by
  rw [heegnerTau163_im]
  have hs : (2 : ℝ) ≤ Real.sqrt 163 :=
    Real.le_sqrt_of_sq_le (by norm_num : (2 : ℝ) ^ 2 ≤ 163)
  linarith

/-- The level-41 Heegner translate `τ₁₆₃ / 41 = (1 + i sqrt 163) / 82`. -/
noncomputable def heegnerTau163_div41 : ℍ :=
  ⟨((1 : ℂ) + Real.sqrt 163 * Complex.I) / 82, by
    rw [Complex.div_im]
    simp⟩

theorem qParam_heegnerTau163_div41_pow_41 :
    Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ 41 =
      Function.Periodic.qParam 1 (heegnerTau163 : ℂ) := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  simp [heegnerTau163_div41, heegnerTau163]
  ring

theorem qPullback41_hasSum_eval_at_heegnerTau163_div41
    {f : PowerSeries ℂ} {value : ℂ}
    (hsum : HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n f *
        Function.Periodic.qParam 1 (heegnerTau163 : ℂ) ^ n) value) :
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (qPullback41 f) *
        Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n) value := by
  apply qPullback41_hasSum_eval
  simpa [qParam_heegnerTau163_div41_pow_41] using hsum

/-- The determinant-41 matrix carrying `τ₁₆₃` to `τ₁₆₃ / 41`.  This is the
cyclic-isogeny witness behind the level-41 modular equation. -/
def heegnerTau163_level41Matrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 41]

theorem heegnerTau163_level41Matrix_det :
    heegnerTau163_level41Matrix.det = 41 := by
  simp [heegnerTau163_level41Matrix, Matrix.det_fin_two]

/-- Fractional-linear action of an integer `2 × 2` matrix on complex points.
For determinant different from `1` this is not an `SL₂(ℤ)` action, but it is
the transform appearing in modular polynomial relations. -/
noncomputable def detMatrixTransform (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) /
    ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ))

/-- A concrete determinant-`N` fractional-linear witness connecting two
complex points. -/
structure DetMatrixTransformWitness (N : ℤ) (τ τ' : ℂ) where
  matrix : Matrix (Fin 2) (Fin 2) ℤ
  det_eq : matrix.det = N
  map_eq : detMatrixTransform matrix τ = τ'

/-- Fractional-linear action of the determinant-41 witness on complex points.
This is kept separate from the `SL₂(ℤ)` action because the witness has
determinant `41`, not `1`. -/
noncomputable def heegnerTau163_level41Transform (τ : ℂ) : ℂ :=
  detMatrixTransform heegnerTau163_level41Matrix τ

theorem heegnerTau163_level41Transform_eq_div41 :
    heegnerTau163_level41Transform (heegnerTau163 : ℂ) =
      (heegnerTau163_div41 : ℂ) := by
  simp [heegnerTau163_level41Transform, detMatrixTransform, heegnerTau163_level41Matrix,
    heegnerTau163_div41, heegnerTau163]
  ring

def heegnerTau163_level41_transform_witness :
    DetMatrixTransformWitness 41 (heegnerTau163 : ℂ) (heegnerTau163_div41 : ℂ) := by
  refine ⟨heegnerTau163_level41Matrix, heegnerTau163_level41Matrix_det, ?_⟩
  exact heegnerTau163_level41Transform_eq_div41

private lemma complex_int_eq_of_norm_sub_lt_one {z : ℂ} {m : ℤ}
    (hz : ∃ n : ℤ, z = (n : ℂ)) (hclose : ‖z - (m : ℂ)‖ < 1) :
    z = (m : ℂ) := by
  rcases hz with ⟨n, rfl⟩
  by_contra hne
  have hnm : n ≠ m := by
    intro h
    exact hne (by rw [h])
  have hsub : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hone : (1 : ℝ) ≤ ‖((n - m : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hsub
  have hlt : ‖((n - m : ℤ) : ℂ)‖ < 1 := by
    simpa using hclose
  linarith

private lemma complex_rat_eq_int_of_integral {z : ℂ}
    (hrat : ∃ q : ℚ, z = (q : ℂ)) (hint : IsIntegral ℤ z) :
    ∃ n : ℤ, z = (n : ℂ) := by
  rcases hrat with ⟨q, rfl⟩
  have hqint : IsIntegral ℤ q := by
    have hmap : IsIntegral ℤ ((algebraMap ℚ ℂ) q) := by
      simpa using hint
    exact (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom ℤ ℚ ℂ)
      (algebraMap ℚ ℂ).injective).mp hmap
  rcases IsIntegrallyClosed.algebraMap_eq_of_integral
      (R := ℤ) (K := ℚ) hqint with ⟨n, hn⟩
  use n
  rw [← hn]
  norm_num

/-- Integral binary quadratic forms, represented by coefficients
`a x² + b xy + c y²`.  This local structure is only used for the elementary
class-number-one enumeration at discriminant `-163`. -/
structure IntegralBinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq

/-- The standard reduced positive-definite condition for negative
discriminants, together with the discriminant equation. -/
def IsReducedPositiveFormOfDiscriminant (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) : Prop :=
  0 < Q.a ∧ |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c ∧
    ((|Q.b| = Q.a ∨ Q.a = Q.c) → 0 ≤ Q.b) ∧
      Q.b ^ 2 - 4 * Q.a * Q.c = D

instance (D : ℤ) :
    DecidablePred (IsReducedPositiveFormOfDiscriminant D) := by
  intro Q
  unfold IsReducedPositiveFormOfDiscriminant
  infer_instance

/-- Reduced positive binary quadratic forms of discriminant `-163`, after the
standard reduced-form bounds have narrowed the check to the odd values
`b ∈ {-7,-5,-3,-1,1,3,5,7}` with the corresponding `a = 1` candidates.
The non-reduced candidates reduce to `x² + xy + 41y²`; the reduced boundary
rule keeps only the positive `b = 1` representative. -/
def cm163LeadingOneReducedForms : Finset IntegralBinaryQuadraticForm :=
  ([⟨1, -7, 53⟩, ⟨1, -5, 47⟩, ⟨1, -3, 43⟩, ⟨1, -1, 41⟩,
      ⟨1, 1, 41⟩, ⟨1, 3, 43⟩, ⟨1, 5, 47⟩, ⟨1, 7, 53⟩] :
      List IntegralBinaryQuadraticForm).toFinset.filter
    (IsReducedPositiveFormOfDiscriminant (-163))

/-- Among the leading-coefficient-one candidates of
`cm163LeadingOneReducedForms`, the only reduced form of discriminant `-163` is
`x² + xy + 41y²`; the boundary convention `|b| = a → b ≥ 0` removes the
equivalent `x² - xy + 41y²` representative.  This checks the `a = 1` list only;
the enumeration over all reduced forms is
`eq_of_isReducedPositiveFormOfDiscriminant_neg163`. -/
theorem cm163LeadingOneReducedForms_eq_singleton :
    cm163LeadingOneReducedForms = {⟨1, 1, 41⟩} := by
  decide

/-- The `a = 1` candidate list `cm163LeadingOneReducedForms` has exactly one
reduced member.  By itself this is not class number one; see
`eq_of_isReducedPositiveFormOfDiscriminant_neg163` and
`mem_cm163LeadingOneReducedForms_iff`. -/
theorem card_cm163LeadingOneReducedForms_eq_one :
    cm163LeadingOneReducedForms.card = 1 := by
  rw [cm163LeadingOneReducedForms_eq_singleton]
  simp

/-- Class number one for discriminant `-163`, as an enumeration of reduced forms:
every reduced positive-definite integral binary quadratic form of discriminant
`-163` (convention `|b| ≤ a ≤ c`, with `0 ≤ b` when `|b| = a` or `a = c`) is
`x² + xy + 41y²`.

All reduced forms are examined, not only the `a = 1` candidates listed in
`cm163LeadingOneReducedForms`.  The proof applies
`reduced_discriminant_neg163_unique` (convention `0 ≤ b ≤ a ≤ c`, bound `a ≤ 7`
and case split) to `(a, |b|, c)`; it gives `a = 1` and `|b| = 1`, so `|b| = a`
and the boundary rule forces `b = 1`. -/
theorem eq_of_isReducedPositiveFormOfDiscriminant_neg163
    (Q : IntegralBinaryQuadraticForm)
    (hQ : IsReducedPositiveFormOfDiscriminant (-163) Q) : Q = ⟨1, 1, 41⟩ := by
  obtain ⟨a, b, c⟩ := Q
  obtain ⟨ha, hba, hac, hbd, hdisc⟩ := hQ
  dsimp only at ha hba hac hbd hdisc
  have hdisc' : |b| * |b| - 4 * a * c = -163 := by
    rw [abs_mul_abs_self]
    linear_combination hdisc
  obtain ⟨rfl, hb1, rfl⟩ :=
    reduced_discriminant_neg163_unique ha (abs_nonneg b) hba hac hdisc'
  have hb : 0 ≤ b := hbd (Or.inl hb1)
  rw [abs_of_nonneg hb] at hb1
  subst hb1
  rfl

/-- The `a = 1` candidate list `cm163LeadingOneReducedForms` contains every
reduced form of discriminant `-163`, by
`eq_of_isReducedPositiveFormOfDiscriminant_neg163`. -/
theorem mem_cm163LeadingOneReducedForms_iff (Q : IntegralBinaryQuadraticForm) :
    Q ∈ cm163LeadingOneReducedForms ↔
      IsReducedPositiveFormOfDiscriminant (-163) Q := by
  unfold cm163LeadingOneReducedForms
  rw [Finset.mem_filter]
  refine ⟨And.right, fun hQ => ⟨?_, hQ⟩⟩
  rw [eq_of_isReducedPositiveFormOfDiscriminant_neg163 Q hQ]
  simp

private lemma norm_pow_sub_pow_le (x y : ℂ) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤
      ‖x - y‖ * ∑ i ∈ Finset.range n, ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) := by
  have hgeom := geom_sum₂_mul x y n
  calc
    ‖x ^ n - y ^ n‖ =
        ‖(∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y)‖ := by
          rw [hgeom]
    _ = ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ * ‖x - y‖ := by
          rw [norm_mul]
    _ ≤ (∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖) * ‖x - y‖ := by
          exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range n, ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i)) * ‖x - y‖ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_mul, norm_pow, norm_pow]
    _ = ‖x - y‖ * ∑ i ∈ Finset.range n, ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) := by
          ring

private lemma norm_pow_four_sub_pow_four_le_of_norm_lt_two {x y : ℂ}
    (hx : ‖x‖ < (2 : ℝ)) (hy : ‖y‖ < (2 : ℝ)) :
    ‖x ^ 4 - y ^ 4‖ ≤ 32 * ‖x - y‖ := by
  have hbase := norm_pow_sub_pow_le x y 4
  have hsum :
      (∑ i ∈ Finset.range 4, ‖x‖ ^ i * ‖y‖ ^ (4 - 1 - i)) ≤
        (32 : ℝ) := by
    calc
      (∑ i ∈ Finset.range 4, ‖x‖ ^ i * ‖y‖ ^ (4 - 1 - i))
          ≤ ∑ i ∈ Finset.range 4, (2 : ℝ) ^ 3 := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi4 : i < 4 := Finset.mem_range.mp hi
            have hxi : ‖x‖ ^ i ≤ (2 : ℝ) ^ i :=
              pow_le_pow_left₀ (norm_nonneg _) hx.le i
            have hyi : ‖y‖ ^ (4 - 1 - i) ≤ (2 : ℝ) ^ (4 - 1 - i) :=
              pow_le_pow_left₀ (norm_nonneg _) hy.le _
            calc
              ‖x‖ ^ i * ‖y‖ ^ (4 - 1 - i)
                  ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ (4 - 1 - i) := by
                    exact mul_le_mul hxi hyi (by positivity) (by positivity)
              _ = (2 : ℝ) ^ 3 := by
                    rw [← pow_add]
                    congr
                    omega
      _ = (32 : ℝ) := by norm_num
  calc
    ‖x ^ 4 - y ^ 4‖
        ≤ ‖x - y‖ *
            ∑ i ∈ Finset.range 4, ‖x‖ ^ i * ‖y‖ ^ (4 - 1 - i) := hbase
    _ ≤ ‖x - y‖ * 32 := by
          exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 32 * ‖x - y‖ := by ring

private lemma norm_pow_eight_sub_pow_eight_le_of_norm_lt_two {x y : ℂ}
    (hx : ‖x‖ < (2 : ℝ)) (hy : ‖y‖ < (2 : ℝ)) :
    ‖x ^ 8 - y ^ 8‖ ≤ 1024 * ‖x - y‖ := by
  have hbase := norm_pow_sub_pow_le x y 8
  have hsum :
      (∑ i ∈ Finset.range 8, ‖x‖ ^ i * ‖y‖ ^ (8 - 1 - i)) ≤
        (1024 : ℝ) := by
    calc
      (∑ i ∈ Finset.range 8, ‖x‖ ^ i * ‖y‖ ^ (8 - 1 - i))
          ≤ ∑ i ∈ Finset.range 8, (2 : ℝ) ^ 7 := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi8 : i < 8 := Finset.mem_range.mp hi
            have hxi : ‖x‖ ^ i ≤ (2 : ℝ) ^ i :=
              pow_le_pow_left₀ (norm_nonneg _) hx.le i
            have hyi : ‖y‖ ^ (8 - 1 - i) ≤ (2 : ℝ) ^ (8 - 1 - i) :=
              pow_le_pow_left₀ (norm_nonneg _) hy.le _
            calc
              ‖x‖ ^ i * ‖y‖ ^ (8 - 1 - i)
                  ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ (8 - 1 - i) := by
                    exact mul_le_mul hxi hyi (by positivity) (by positivity)
              _ = (2 : ℝ) ^ 7 := by
                    rw [← pow_add]
                    congr
                    omega
      _ = (1024 : ℝ) := by norm_num
  calc
    ‖x ^ 8 - y ^ 8‖
        ≤ ‖x - y‖ *
            ∑ i ∈ Finset.range 8, ‖x‖ ^ i * ‖y‖ ^ (8 - 1 - i) := hbase
    _ ≤ ‖x - y‖ * 1024 := by
          exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 1024 * ‖x - y‖ := by ring

private lemma norm_cube_sub_cube_le_of_norm_le {x y : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖x ^ 3 - y ^ 3‖ ≤ 3 * R ^ 2 * ‖x - y‖ := by
  have hbase := norm_pow_sub_pow_le x y 3
  have hsum :
      (∑ i ∈ Finset.range 3, ‖x‖ ^ i * ‖y‖ ^ (3 - 1 - i)) ≤
        3 * R ^ 2 := by
    calc
      (∑ i ∈ Finset.range 3, ‖x‖ ^ i * ‖y‖ ^ (3 - 1 - i))
          ≤ ∑ _i ∈ Finset.range 3, R ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi3 : i < 3 := Finset.mem_range.mp hi
            have hxi : ‖x‖ ^ i ≤ R ^ i :=
              pow_le_pow_left₀ (norm_nonneg _) hx i
            have hyi : ‖y‖ ^ (3 - 1 - i) ≤ R ^ (3 - 1 - i) :=
              pow_le_pow_left₀ (norm_nonneg _) hy _
            calc
              ‖x‖ ^ i * ‖y‖ ^ (3 - 1 - i)
                  ≤ R ^ i * R ^ (3 - 1 - i) := by
                    exact mul_le_mul hxi hyi (by positivity) (pow_nonneg hR _)
              _ = R ^ 2 := by
                    rw [← pow_add]
                    congr
                    omega
      _ = 3 * R ^ 2 := by norm_num
  calc
    ‖x ^ 3 - y ^ 3‖
        ≤ ‖x - y‖ *
            ∑ i ∈ Finset.range 3, ‖x‖ ^ i * ‖y‖ ^ (3 - 1 - i) := hbase
    _ ≤ ‖x - y‖ * (3 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 3 * R ^ 2 * ‖x - y‖ := by ring

/-- At the Heegner point the nome is negative real and has absolute value
`exp (-π sqrt 163)`.  The equality itself is already proved in
`SingularModuli`; this named lemma keeps the CM-evaluation file self-contained
at the level where the q-expansion calculation starts. -/
lemma heegnerTau163_nome_eq :
    Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)) =
      -Real.exp (-Real.pi * Real.sqrt 163) :=
  heegnerTau163_q

/-- The principal part of the `j` q-expansion at `τ₁₆₃`. -/
lemma heegnerTau163_q_inv :
    (Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ =
      -(Real.exp (Real.pi * Real.sqrt 163) : ℂ) := by
  rw [heegnerTau163_q]
  rw [show (-(Real.exp (-Real.pi * Real.sqrt 163) : ℂ))⁻¹ =
      -((Real.exp (-Real.pi * Real.sqrt 163) : ℂ)⁻¹) by ring]
  rw [← Complex.ofReal_inv]
  · congr 1
    rw [show -Real.pi * Real.sqrt 163 = -(Real.pi * Real.sqrt 163) by ring]
    rw [Real.exp_neg]
    rw [inv_inv]

/-- The exact real expression left after comparing the principal part
`1/q + 744` with the CM target. -/
lemma heegnerTau163_principal_part_sub_target :
    (Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ +
        744 - heegnerJ163Target =
      (((640320 : ℝ) ^ 3 + 744 -
        Real.exp (Real.pi * Real.sqrt 163)) : ℂ) := by
  rw [heegnerTau163_q_inv]
  unfold heegnerJ163Target
  norm_num
  ring

/-- Exact norm of the usual nome at `τ₁₆₃`. -/
lemma norm_heegnerTau163_q :
    ‖Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ =
      Real.exp (-Real.pi * Real.sqrt 163) := by
  rw [Complex.norm_exp]
  congr 1
  simp [heegnerTau163, Complex.mul_re, Complex.mul_im]
  ring

/-- Norm of the half-nome at `τ₁₆₃`. -/
lemma norm_heegnerTau163_q_half :
    ‖Complex.exp (Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ =
      Real.exp (-(Real.pi * Real.sqrt 163 / 2)) := by
  rw [norm_exp_pi_I_mul, heegnerTau163_im]
  ring_nf

/-- The half-nome is already small enough for geometric theta tails. -/
lemma norm_heegnerTau163_q_half_lt_one_third :
    ‖Complex.exp (Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ < (1 / 3 : ℝ) := by
  rw [norm_exp_pi_I_mul]
  exact exp_neg_pi_mul_im_lt_one_third heegnerTau163_one_le_im_local

/-- A stronger explicit smallness bound for the half-nome at `τ₁₆₃`. -/
lemma norm_heegnerTau163_q_half_lt_two_pow_neg_18 :
    ‖Complex.exp (Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ <
      (1 / 2 : ℝ) ^ 18 := by
  rw [norm_heegnerTau163_q_half]
  have hsqrt : (12 : ℝ) < Real.sqrt 163 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    norm_num
  have hprod : (18 : ℝ) < Real.pi * Real.sqrt 163 / 2 := by
    nlinarith [Real.pi_gt_three, hsqrt, Real.sqrt_nonneg 163]
  have hexp : Real.exp (-(Real.pi * Real.sqrt 163 / 2)) < Real.exp (-18 : ℝ) := by
    rw [Real.exp_lt_exp]
    linarith
  have hpow :
      Real.exp (-18 : ℝ) = Real.exp (-1 : ℝ) ^ 18 := by
    rw [show (-18 : ℝ) = (18 : ℕ) * (-1 : ℝ) by norm_num]
    rw [Real.exp_nat_mul]
  rw [hpow] at hexp
  exact hexp.trans
    (pow_lt_pow_left₀ Real.exp_neg_one_lt_half (Real.exp_pos (-1)).le (by norm_num))

lemma heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18 :
    let τ : ℂ := heegnerTau163
    Real.exp (-Real.pi * τ.im) < (1 / 2 : ℝ) ^ 18 := by
  let τ : ℂ := heegnerTau163
  have h := norm_heegnerTau163_q_half_lt_two_pow_neg_18
  rw [norm_heegnerTau163_q_half] at h
  have him : τ.im = Real.sqrt 163 / 2 := by
    dsimp [τ]
    exact heegnerTau163_im
  change Real.exp (-Real.pi * τ.im) < (1 / 2 : ℝ) ^ 18
  rw [him]
  simpa [show -Real.pi * (Real.sqrt 163 / 2) =
      -(Real.pi * Real.sqrt 163 / 2) by ring] using h

lemma norm_heegnerTau163_half_nome_lt_two_pow_neg_18 :
    let τ : ℂ := heegnerTau163
    ‖Complex.exp (Real.pi * Complex.I * τ)‖ < (1 / 2 : ℝ) ^ 18 := by
  simpa using norm_heegnerTau163_q_half_lt_two_pow_neg_18

lemma norm_heegnerTau163_half_nome_gt_two_pow_neg_30 :
    let τ : ℂ := heegnerTau163
    (1 / 2 : ℝ) ^ 30 < ‖Complex.exp (Real.pi * Complex.I * τ)‖ := by
  change (1 / 2 : ℝ) ^ 30 < ‖Complex.exp (Real.pi * Complex.I * (heegnerTau163 : ℂ))‖
  rw [norm_heegnerTau163_q_half]
  have hsqrt : Real.sqrt 163 < (12.7672 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 163) (by norm_num : (0 : ℝ) ≤ 12.7672)]
    norm_num
  have hpi : Real.pi < (3.1416 : ℝ) := by linarith [Real.pi_lt_d20]
  have hprod : Real.pi * Real.sqrt 163 / 2 < (20.055 : ℝ) := by
    nlinarith [Real.pi_pos, Real.sqrt_nonneg 163]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h30log2 : (20.055 : ℝ) < 30 * Real.log 2 := by linarith
  have hchain : Real.pi * Real.sqrt 163 / 2 < 30 * Real.log 2 := by linarith
  have hexp_mono : Real.exp (Real.pi * Real.sqrt 163 / 2) <
      Real.exp (30 * Real.log 2) := Real.exp_lt_exp.mpr hchain
  have hexp_log : Real.exp (30 * Real.log 2) = (2 : ℝ) ^ 30 := by
    rw [show (30 : ℝ) * Real.log 2 = (30 : ℕ) * Real.log 2 by norm_num]
    rw [Real.exp_nat_mul]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlt : Real.exp (Real.pi * Real.sqrt 163 / 2) < (2 : ℝ) ^ 30 := by
    linarith [hexp_mono, hexp_log.symm ▸ hexp_mono]
  have hpos : 0 < Real.exp (Real.pi * Real.sqrt 163 / 2) := Real.exp_pos _
  rw [show -(Real.pi * Real.sqrt 163 / 2) = -(Real.pi * Real.sqrt 163 / 2) from rfl]
  rw [Real.exp_neg]
  rw [show (1 / 2 : ℝ) ^ 30 = ((2 : ℝ) ^ 30)⁻¹ by norm_num]
  exact (inv_lt_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 30) hpos).2 hlt

lemma heegnerTau163_half_nome_ne_zero :
    let τ : ℂ := heegnerTau163
    Complex.exp (Real.pi * Complex.I * τ) ≠ 0 := by
  intro τ
  exact Complex.exp_ne_zero _

lemma norm_heegnerTau163_half_nome_sq_lt_two_pow_neg_36 :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖Q‖ ^ 2 < (1 / 2 : ℝ) ^ 36 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, Q] using norm_heegnerTau163_half_nome_lt_two_pow_neg_18
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  calc
    ‖Q‖ ^ 2 < ((1 / 2 : ℝ) ^ 18) ^ 2 :=
      pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
    _ = (1 / 2 : ℝ) ^ 36 := by
      rw [← pow_mul]

/-- A convenient bound for the usual nome at `τ₁₆₃`. -/
lemma norm_heegnerTau163_q_lt_one_ninth :
    ‖Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ < (1 / 9 : ℝ) := by
  rw [show 2 * Real.pi * Complex.I * (heegnerTau163 : ℂ) =
      (2 : ℕ) * (Real.pi * Complex.I * (heegnerTau163 : ℂ)) by norm_num; ring,
    Complex.exp_nat_mul, norm_pow]
  have h := norm_heegnerTau163_q_half_lt_one_third
  have hnonneg : 0 ≤ ‖Complex.exp (Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ :=
    norm_nonneg _
  nlinarith

/-- A stronger explicit smallness bound for the usual nome at `τ₁₆₃`. -/
lemma norm_heegnerTau163_q_lt_two_pow_neg_36 :
    ‖Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ))‖ <
      (1 / 2 : ℝ) ^ 36 := by
  rw [norm_heegnerTau163_q]
  have hsqrt : (12 : ℝ) < Real.sqrt 163 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
    norm_num
  have hprod : (36 : ℝ) < Real.pi * Real.sqrt 163 := by
    nlinarith [Real.pi_gt_three, hsqrt, Real.sqrt_nonneg 163]
  have hexp : Real.exp (-Real.pi * Real.sqrt 163) < Real.exp (-36 : ℝ) := by
    rw [Real.exp_lt_exp]
    linarith
  have hpow :
      Real.exp (-36 : ℝ) = Real.exp (-1 : ℝ) ^ 36 := by
    rw [show (-36 : ℝ) = (36 : ℕ) * (-1 : ℝ) by norm_num]
    rw [Real.exp_nat_mul]
  rw [hpow] at hexp
  exact hexp.trans
    (pow_lt_pow_left₀ Real.exp_neg_one_lt_half (Real.exp_pos (-1)).le (by norm_num))

private lemma div_one_sub_lt_two_pow_succ {r : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hr : r < (1 / 2 : ℝ) ^ n) :
    r / (1 - r) < (1 / 2 : ℝ) ^ (n - 1) := by
  have hpow_pos : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hpow_le_half : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega : n ≠ 0)
  have hr_lt_half : r < (1 / 2 : ℝ) := lt_of_lt_of_le hr hpow_le_half
  have hpow_lt_one : (1 / 2 : ℝ) ^ n < 1 := by
    linarith
  have hr_lt_one : r < 1 := hr.trans hpow_lt_one
  have hden : 0 < 1 - r := by linarith
  have htarget_pos : 0 < (1 / 2 : ℝ) ^ (n - 1) :=
    pow_pos (by norm_num) _
  rw [div_lt_iff₀ hden]
  have hpow_step :
      (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ n =>
        simp [pow_succ']
  calc
    r < (1 / 2 : ℝ) ^ n := hr
    _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n - 1) := hpow_step
    _ < (1 / 2 : ℝ) ^ (n - 1) * (1 - r) := by
      nlinarith [htarget_pos, hr_lt_half]

private lemma two_mul_div_one_sub_lt_two_pow_pred {r : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hr : r < (1 / 2 : ℝ) ^ n) :
    2 * r / (1 - r) < (1 / 2 : ℝ) ^ (n - 2) := by
  have hpow_pos : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hpow_le_half : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega : n ≠ 0)
  have hr_lt_half : r < (1 / 2 : ℝ) := lt_of_lt_of_le hr hpow_le_half
  have hpow_lt_one : (1 / 2 : ℝ) ^ n < 1 := by
    linarith
  have hr_lt_one : r < 1 := hr.trans hpow_lt_one
  have hden : 0 < 1 - r := by linarith
  have htarget_pos : 0 < (1 / 2 : ℝ) ^ (n - 2) :=
    pow_pos (by norm_num) _
  rw [div_lt_iff₀ hden]
  have hpow_step :
      2 * (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n - 2) := by
    cases n with
    | zero => omega
    | succ n =>
        cases n with
        | zero => omega
        | succ n =>
            simp [pow_succ']
  calc
    2 * r < 2 * (1 / 2 : ℝ) ^ n := by linarith
    _ = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n - 2) := hpow_step
    _ < (1 / 2 : ℝ) ^ (n - 2) * (1 - r) := by
      nlinarith [htarget_pos, hr_lt_half]

private lemma hasSum_geometric_offset {r : ℝ} (k : ℕ)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    HasSum (fun n : ℕ => r ^ (n + k)) (r ^ k / (1 - r)) := by
  have hgeom := hasSum_geometric_of_lt_one hr_nonneg hr_lt_one
  have hmul := hgeom.mul_left (r ^ k)
  convert hmul using 1
  · ext n
    rw [pow_add]
    ring

private lemma pow_six_div_one_sub_lt_two_pow_neg_100 {r : ℝ}
    (hr_pos : 0 < r) (hr : r < (1 / 2 : ℝ) ^ 18) :
    r ^ 6 / (1 - r) < (1 / 2 : ℝ) ^ 100 := by
  have hpow_le_half : (1 / 2 : ℝ) ^ 18 ≤ (1 / 2 : ℝ) :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by norm_num : (18 : ℕ) ≠ 0)
  have hr_lt_half : r < (1 / 2 : ℝ) := lt_of_lt_of_le hr hpow_le_half
  have hden : 0 < 1 - r := by linarith
  rw [div_lt_iff₀ hden]
  have hr6 : r ^ 6 < ((1 / 2 : ℝ) ^ 18) ^ 6 :=
    pow_lt_pow_left₀ hr hr_pos.le (by norm_num)
  have hpow_eq : ((1 / 2 : ℝ) ^ 18) ^ 6 = (1 / 2 : ℝ) ^ 108 := by
    rw [← pow_mul]
  have hsmall : (1 / 2 : ℝ) ^ 108 < (1 / 2 : ℝ) ^ 100 * (1 / 2 : ℝ) := by
    norm_num
  linarith

private lemma two_mul_pow_nine_div_one_sub_lt_two_pow_neg_150 {r : ℝ}
    (hr_pos : 0 < r) (hr : r < (1 / 2 : ℝ) ^ 18) :
    2 * r ^ 9 / (1 - r) < (1 / 2 : ℝ) ^ 150 := by
  have hpow_le_half : (1 / 2 : ℝ) ^ 18 ≤ (1 / 2 : ℝ) :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by norm_num : (18 : ℕ) ≠ 0)
  have hr_lt_half : r < (1 / 2 : ℝ) := lt_of_lt_of_le hr hpow_le_half
  have hden : 0 < 1 - r := by linarith
  rw [div_lt_iff₀ hden]
  have hr9 : r ^ 9 < ((1 / 2 : ℝ) ^ 18) ^ 9 :=
    pow_lt_pow_left₀ hr hr_pos.le (by norm_num)
  have hpow_eq : ((1 / 2 : ℝ) ^ 18) ^ 9 = (1 / 2 : ℝ) ^ 162 := by
    rw [← pow_mul]
  have hsmall : 2 * (1 / 2 : ℝ) ^ 162 < (1 / 2 : ℝ) ^ 150 * (1 / 2 : ℝ) := by
    norm_num
  linarith

/-- The normalized `θ₂` series differs from its leading term by a geometric
tail.  This is the quantitative core of the `θ₂(τ₁₆₃) ≠ 0` proof. -/
lemma thetaTwoConst_heegnerTau163_normalized_sub_one_norm_le :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    let r : ℝ := Real.exp (-Real.pi * τ.im)
    ‖thetaTwoConst τ / ((2 : ℂ) * E) - 1‖ ≤ r / (1 - r) := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simpa using heegnerTau163.2
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hE : (2 : ℂ) * E ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have hQnorm : ‖Q‖ = r := by
    dsimp [Q, r]
    exact norm_exp_pi_I_mul τ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have hr_lt_one : r < 1 := by linarith
  have hseries :
      HasSum (fun n : ℕ => Q ^ (n * (n + 1)))
        (thetaTwoConst τ / ((2 : ℂ) * E)) := by
    have hraw := thetaTwoConst_hasSum_q_series hτ
    have hdiv := hraw.div_const ((2 : ℂ) * E)
    convert hdiv using 1
    · ext n
      dsimp [Q, E]
      field_simp [hE]
  have htail :
      HasSum (fun n : ℕ => Q ^ ((n + 1) * ((n + 1) + 1)))
        (thetaTwoConst τ / ((2 : ℂ) * E) - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hseries
  have htail_norm_summable :
      Summable (fun n : ℕ => ‖Q ^ ((n + 1) * ((n + 1) + 1))‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => r ^ (n + 1))
      (g := fun n : ℕ => ‖Q ^ ((n + 1) * ((n + 1) + 1))‖)
      (fun n => norm_nonneg _) ?_ ?_
    · intro n
      dsimp
      rw [norm_pow, hQnorm]
      exact pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
        (by nlinarith : n + 1 ≤ (n + 1) * ((n + 1) + 1))
    · have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
        simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (ne_of_gt hr_pos)]
        exact hasSum_geometric_of_lt_one hr_pos.le hr_lt_one
      exact hgeom.summable
  have hnorm_le :
      ‖∑' n : ℕ, Q ^ ((n + 1) * ((n + 1) + 1))‖ ≤
        ∑' n : ℕ, ‖Q ^ ((n + 1) * ((n + 1) + 1))‖ :=
    norm_tsum_le_tsum_norm htail_norm_summable
  rw [htail.tsum_eq] at hnorm_le
  refine hnorm_le.trans ?_
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (ne_of_gt hr_pos)]
    exact hasSum_geometric_of_lt_one hr_pos.le hr_lt_one
  exact (htail_norm_summable.tsum_mono hgeom.summable (fun n => by
    dsimp
    rw [norm_pow, hQnorm]
    exact pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
      (by nlinarith : n + 1 ≤ (n + 1) * ((n + 1) + 1)))).trans_eq hgeom.tsum_eq

lemma thetaTwoConst_heegnerTau163_normalized_sub_two_terms_norm_le :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    let r : ℝ := Real.exp (-Real.pi * τ.im)
    ‖thetaTwoConst τ / ((2 : ℂ) * E) - (1 + Q ^ 2)‖ ≤ r ^ 6 / (1 - r) := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simpa using heegnerTau163.2
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hE : (2 : ℂ) * E ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have hQnorm : ‖Q‖ = r := by
    dsimp [Q, r]
    exact norm_exp_pi_I_mul τ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have hr_lt_one : r < 1 := by linarith
  have hseries :
      HasSum (fun n : ℕ => Q ^ (n * (n + 1)))
        (thetaTwoConst τ / ((2 : ℂ) * E)) := by
    have hraw := thetaTwoConst_hasSum_q_series hτ
    have hdiv := hraw.div_const ((2 : ℂ) * E)
    convert hdiv using 1
    · ext n
      dsimp [Q, E]
      field_simp [hE]
  have htail :
      HasSum (fun n : ℕ => Q ^ ((n + 2) * ((n + 2) + 1)))
        (thetaTwoConst τ / ((2 : ℂ) * E) - (1 + Q ^ 2)) := by
    have h := (hasSum_nat_add_iff' 2).mpr hseries
    convert h using 1
    norm_num [Finset.sum_range_succ]
  have htail_norm_summable :
      Summable (fun n : ℕ => ‖Q ^ ((n + 2) * ((n + 2) + 1))‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => r ^ (n + 6))
      (g := fun n : ℕ => ‖Q ^ ((n + 2) * ((n + 2) + 1))‖)
      (fun n => norm_nonneg _) ?_ ?_
    · intro n
      dsimp
      rw [norm_pow, hQnorm]
      exact pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
        (by nlinarith : n + 6 ≤ (n + 2) * ((n + 2) + 1))
    · exact (hasSum_geometric_offset 6 hr_pos.le hr_lt_one).summable
  have hnorm_le :
      ‖∑' n : ℕ, Q ^ ((n + 2) * ((n + 2) + 1))‖ ≤
        ∑' n : ℕ, ‖Q ^ ((n + 2) * ((n + 2) + 1))‖ :=
    norm_tsum_le_tsum_norm htail_norm_summable
  rw [htail.tsum_eq] at hnorm_le
  refine hnorm_le.trans ?_
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 6)) (r ^ 6 / (1 - r)) :=
    hasSum_geometric_offset 6 hr_pos.le hr_lt_one
  exact (htail_norm_summable.tsum_mono hgeom.summable (fun n => by
    dsimp
    rw [norm_pow, hQnorm]
    exact pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
      (by nlinarith : n + 6 ≤ (n + 2) * ((n + 2) + 1)))).trans_eq hgeom.tsum_eq

/-- The theta-three constant at `τ₁₆₃` is within a tiny geometric tail of `1`. -/
lemma jacobiTheta_heegnerTau163_sub_one_norm_le :
    let τ : ℂ := heegnerTau163
    let r : ℝ := Real.exp (-Real.pi * τ.im)
    ‖jacobiTheta τ - 1‖ ≤ 2 * r / (1 - r) := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simpa using heegnerTau163.2
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hQnorm : ‖Q‖ = r := by
    dsimp [Q, r]
    exact norm_exp_pi_I_mul τ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have hr_lt_one : r < 1 := by linarith
  have hseries :
      HasSum (fun n : ℕ => 2 * Q ^ ((n + 1) ^ 2))
        (jacobiTheta τ - 1) := by
    simpa [Q] using jacobiTheta_hasSum_q_series hτ
  have htail_norm_summable :
      Summable (fun n : ℕ => ‖(2 : ℂ) * Q ^ ((n + 1) ^ 2)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => 2 * r ^ (n + 1))
      (g := fun n : ℕ => ‖(2 : ℂ) * Q ^ ((n + 1) ^ 2)‖)
      (fun n => norm_nonneg _) ?_ ?_
    · intro n
      change ‖(2 : ℂ) * Q ^ ((n + 1) ^ 2)‖ ≤ 2 * r ^ (n + 1)
      rw [norm_mul, norm_pow, hQnorm]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
          (by nlinarith : n + 1 ≤ (n + 1) ^ 2))
        (by norm_num)
    · have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
        simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (ne_of_gt hr_pos)]
        exact hasSum_geometric_of_lt_one hr_pos.le hr_lt_one
      exact (hgeom.mul_left (2 : ℝ)).summable
  have hnorm_le :
      ‖∑' n : ℕ, (2 : ℂ) * Q ^ ((n + 1) ^ 2)‖ ≤
        ∑' n : ℕ, ‖(2 : ℂ) * Q ^ ((n + 1) ^ 2)‖ :=
    norm_tsum_le_tsum_norm htail_norm_summable
  rw [hseries.tsum_eq] at hnorm_le
  refine hnorm_le.trans ?_
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (ne_of_gt hr_pos)]
    exact hasSum_geometric_of_lt_one hr_pos.le hr_lt_one
  have hgeom2 : HasSum (fun n : ℕ => 2 * r ^ (n + 1)) (2 * (r / (1 - r))) :=
    hgeom.mul_left (2 : ℝ)
  have hmono :
      (∑' n : ℕ, ‖(2 : ℂ) * Q ^ ((n + 1) ^ 2)‖) ≤
        ∑' n : ℕ, 2 * r ^ (n + 1) :=
    htail_norm_summable.tsum_mono hgeom2.summable (fun n => by
      rw [norm_mul, norm_pow, hQnorm]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
          (by nlinarith : n + 1 ≤ (n + 1) ^ 2))
        (by norm_num))
  exact hmono.trans_eq (by
    rw [hgeom2.tsum_eq]
    ring)

lemma jacobiTheta_heegnerTau163_sub_three_terms_norm_le :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    let r : ℝ := Real.exp (-Real.pi * τ.im)
    ‖jacobiTheta τ - (1 + 2 * Q + 2 * Q ^ 4)‖ ≤ 2 * r ^ 9 / (1 - r) := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simpa using heegnerTau163.2
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hQnorm : ‖Q‖ = r := by
    dsimp [Q, r]
    exact norm_exp_pi_I_mul τ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have hr_lt_one : r < 1 := by linarith
  have hseries :
      HasSum (fun n : ℕ => 2 * Q ^ ((n + 1) ^ 2))
        (jacobiTheta τ - 1) := by
    simpa [Q] using jacobiTheta_hasSum_q_series hτ
  have htail :
      HasSum (fun n : ℕ => 2 * Q ^ ((n + 3) ^ 2))
        (jacobiTheta τ - (1 + 2 * Q + 2 * Q ^ 4)) := by
    have h := (hasSum_nat_add_iff' 2).mpr hseries
    convert h using 1
    norm_num [Finset.sum_range_succ]
    ring
  have htail_norm_summable :
      Summable (fun n : ℕ => ‖(2 : ℂ) * Q ^ ((n + 3) ^ 2)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => 2 * r ^ (n + 9))
      (g := fun n : ℕ => ‖(2 : ℂ) * Q ^ ((n + 3) ^ 2)‖)
      (fun n => norm_nonneg _) ?_ ?_
    · intro n
      change ‖(2 : ℂ) * Q ^ ((n + 3) ^ 2)‖ ≤ 2 * r ^ (n + 9)
      rw [norm_mul, norm_pow, hQnorm]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
          (by nlinarith : n + 9 ≤ (n + 3) ^ 2))
        (by norm_num)
    · exact ((hasSum_geometric_offset 9 hr_pos.le hr_lt_one).mul_left (2 : ℝ)).summable
  have hnorm_le :
      ‖∑' n : ℕ, (2 : ℂ) * Q ^ ((n + 3) ^ 2)‖ ≤
        ∑' n : ℕ, ‖(2 : ℂ) * Q ^ ((n + 3) ^ 2)‖ :=
    norm_tsum_le_tsum_norm htail_norm_summable
  rw [htail.tsum_eq] at hnorm_le
  refine hnorm_le.trans ?_
  have hgeom : HasSum (fun n : ℕ => 2 * r ^ (n + 9)) (2 * (r ^ 9 / (1 - r))) :=
    (hasSum_geometric_offset 9 hr_pos.le hr_lt_one).mul_left (2 : ℝ)
  have hmono :
      (∑' n : ℕ, ‖(2 : ℂ) * Q ^ ((n + 3) ^ 2)‖) ≤
        ∑' n : ℕ, 2 * r ^ (n + 9) :=
    htail_norm_summable.tsum_mono hgeom.summable (fun n => by
      rw [norm_mul, norm_pow, hQnorm]
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [htwo]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
          (by nlinarith : n + 9 ≤ (n + 3) ^ 2))
        (by norm_num))
  exact hmono.trans_eq (by
    rw [hgeom.tsum_eq]
    ring)

/-- The theta-four constant at `τ₁₆₃` is also within a tiny geometric tail
of `1`. -/
lemma thetaFourConst_heegnerTau163_sub_one_norm_le :
    let τ : ℂ := heegnerTau163
    let r : ℝ := Real.exp (-Real.pi * τ.im)
    ‖thetaFourConst τ - 1‖ ≤ 2 * r / (1 - r) := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simpa using heegnerTau163.2
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hQnorm : ‖Q‖ = r := by
    dsimp [Q, r]
    exact norm_exp_pi_I_mul τ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have hr_lt_one : r < 1 := by linarith
  have hseries :
      HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * Q ^ (n ^ 2))
        (thetaFourConst τ + 1) := by
    simpa [Q] using thetaFourConst_hasSum_q_series hτ
  have htail :
      HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2))
        (thetaFourConst τ - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hseries
    convert h using 1
    norm_num [Finset.sum_range_succ]
    ring
  have htail_norm_summable :
      Summable (fun n : ℕ =>
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => 2 * r ^ (n + 1))
      (g := fun n : ℕ =>
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖)
      (fun n => norm_nonneg _) ?_ ?_
    · intro n
      calc
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖ =
            2 * r ^ ((n + 1) ^ 2) := by
          rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
            norm_pow, hQnorm]
          norm_num
        _ ≤ 2 * r ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
              (by nlinarith : n + 1 ≤ (n + 1) ^ 2))
            (by norm_num)
    · have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
        simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (ne_of_gt hr_pos)]
        exact hasSum_geometric_of_lt_one hr_pos.le hr_lt_one
      exact (hgeom.mul_left (2 : ℝ)).summable
  have hnorm_le :
      ‖∑' n : ℕ,
        (2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖ ≤
        ∑' n : ℕ,
          ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖ :=
    norm_tsum_le_tsum_norm htail_norm_summable
  rw [htail.tsum_eq] at hnorm_le
  refine hnorm_le.trans ?_
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (ne_of_gt hr_pos)]
    exact hasSum_geometric_of_lt_one hr_pos.le hr_lt_one
  have hgeom2 : HasSum (fun n : ℕ => 2 * r ^ (n + 1)) (2 * (r / (1 - r))) :=
    hgeom.mul_left (2 : ℝ)
  have hmono :
      (∑' n : ℕ,
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖) ≤
        ∑' n : ℕ, 2 * r ^ (n + 1) :=
    htail_norm_summable.tsum_mono hgeom2.summable (fun n => by
      calc
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 1) * Q ^ ((n + 1) ^ 2)‖ =
            2 * r ^ ((n + 1) ^ 2) := by
          rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
            norm_pow, hQnorm]
          norm_num
        _ ≤ 2 * r ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
              (by nlinarith : n + 1 ≤ (n + 1) ^ 2))
            (by norm_num))
  exact hmono.trans_eq (by
    rw [hgeom2.tsum_eq]
    ring)

lemma thetaFourConst_heegnerTau163_sub_three_terms_norm_le :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    let r : ℝ := Real.exp (-Real.pi * τ.im)
    ‖thetaFourConst τ - (1 - 2 * Q + 2 * Q ^ 4)‖ ≤ 2 * r ^ 9 / (1 - r) := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simpa using heegnerTau163.2
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hQnorm : ‖Q‖ = r := by
    dsimp [Q, r]
    exact norm_exp_pi_I_mul τ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have hr_lt_one : r < 1 := by linarith
  have hseries :
      HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * Q ^ (n ^ 2))
        (thetaFourConst τ + 1) := by
    simpa [Q] using thetaFourConst_hasSum_q_series hτ
  have htail :
      HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2))
        (thetaFourConst τ - (1 - 2 * Q + 2 * Q ^ 4)) := by
    have h := (hasSum_nat_add_iff' 3).mpr hseries
    convert h using 1
    · norm_num [Finset.sum_range_succ]
      ring
  have htail_norm_summable :
      Summable (fun n : ℕ =>
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => 2 * r ^ (n + 9))
      (g := fun n : ℕ =>
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖)
      (fun n => norm_nonneg _) ?_ ?_
    · intro n
      calc
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖ =
            2 * r ^ ((n + 3) ^ 2) := by
          rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
            norm_pow, hQnorm]
          norm_num
        _ ≤ 2 * r ^ (n + 9) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
              (by nlinarith : n + 9 ≤ (n + 3) ^ 2))
            (by norm_num)
    · exact ((hasSum_geometric_offset 9 hr_pos.le hr_lt_one).mul_left (2 : ℝ)).summable
  have hnorm_le :
      ‖∑' n : ℕ,
        (2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖ ≤
        ∑' n : ℕ,
          ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖ :=
    norm_tsum_le_tsum_norm htail_norm_summable
  rw [htail.tsum_eq] at hnorm_le
  refine hnorm_le.trans ?_
  have hgeom : HasSum (fun n : ℕ => 2 * r ^ (n + 9)) (2 * (r ^ 9 / (1 - r))) :=
    (hasSum_geometric_offset 9 hr_pos.le hr_lt_one).mul_left (2 : ℝ)
  have hmono :
      (∑' n : ℕ,
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖) ≤
        ∑' n : ℕ, 2 * r ^ (n + 9) :=
    htail_norm_summable.tsum_mono hgeom.summable (fun n => by
      calc
        ‖(2 : ℂ) * (-1 : ℂ) ^ (n + 3) * Q ^ ((n + 3) ^ 2)‖ =
            2 * r ^ ((n + 3) ^ 2) := by
          rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
            norm_pow, hQnorm]
          norm_num
        _ ≤ 2 * r ^ (n + 9) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr_pos.le hr_lt_one.le
              (by nlinarith : n + 9 ≤ (n + 3) ^ 2))
            (by norm_num))
  exact hmono.trans_eq (by
    rw [hgeom.tsum_eq]
    ring)

lemma thetaTwoConst_heegnerTau163_normalized_sub_two_terms_norm_lt_two_pow_neg_100 :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖thetaTwoConst τ / ((2 : ℂ) * E) - (1 + Q ^ 2)‖ < (1 / 2 : ℝ) ^ 100 := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail :
      ‖thetaTwoConst τ / ((2 : ℂ) * E) - (1 + Q ^ 2)‖ ≤ r ^ 6 / (1 - r) := by
    simpa [τ, E, Q, r] using
      thetaTwoConst_heegnerTau163_normalized_sub_two_terms_norm_le
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, r] using heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18
  exact htail.trans_lt (pow_six_div_one_sub_lt_two_pow_neg_100 hr_pos hr)

lemma jacobiTheta_heegnerTau163_sub_three_terms_norm_lt_two_pow_neg_150 :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖jacobiTheta τ - (1 + 2 * Q + 2 * Q ^ 4)‖ < (1 / 2 : ℝ) ^ 150 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail :
      ‖jacobiTheta τ - (1 + 2 * Q + 2 * Q ^ 4)‖ ≤ 2 * r ^ 9 / (1 - r) := by
    simpa [τ, Q, r] using jacobiTheta_heegnerTau163_sub_three_terms_norm_le
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, r] using heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18
  exact htail.trans_lt (two_mul_pow_nine_div_one_sub_lt_two_pow_neg_150 hr_pos hr)

lemma thetaFourConst_heegnerTau163_sub_three_terms_norm_lt_two_pow_neg_150 :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖thetaFourConst τ - (1 - 2 * Q + 2 * Q ^ 4)‖ < (1 / 2 : ℝ) ^ 150 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail :
      ‖thetaFourConst τ - (1 - 2 * Q + 2 * Q ^ 4)‖ ≤ 2 * r ^ 9 / (1 - r) := by
    simpa [τ, Q, r] using thetaFourConst_heegnerTau163_sub_three_terms_norm_le
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.exp_pos _
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, r] using heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18
  exact htail.trans_lt (two_mul_pow_nine_div_one_sub_lt_two_pow_neg_150 hr_pos hr)

lemma thetaTwoConst_heegnerTau163_two_term_error :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ ε : ℂ,
      ‖ε‖ < (1 / 2 : ℝ) ^ 100 ∧
      thetaTwoConst τ / ((2 : ℂ) * E) = 1 + Q ^ 2 + ε := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine ⟨thetaTwoConst τ / ((2 : ℂ) * E) - (1 + Q ^ 2), ?_, ?_⟩
  · simpa [τ, E, Q] using
      thetaTwoConst_heegnerTau163_normalized_sub_two_terms_norm_lt_two_pow_neg_100
  · ring

lemma thetaTwoConst_heegnerTau163_two_term_error_rel :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ ε : ℂ,
      ‖ε‖ ≤ ‖Q‖ ^ 6 / (1 - ‖Q‖) ∧
      thetaTwoConst τ / ((2 : ℂ) * E) = 1 + Q ^ 2 + ε := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine ⟨thetaTwoConst τ / ((2 : ℂ) * E) - (1 + Q ^ 2), ?_, ?_⟩
  · have h := thetaTwoConst_heegnerTau163_normalized_sub_two_terms_norm_le
    have hQnorm : ‖Q‖ = Real.exp (-Real.pi * τ.im) := by
      dsimp [Q]
      exact norm_exp_pi_I_mul τ
    simpa [τ, E, Q, hQnorm] using h
  · ring

lemma jacobiTheta_heegnerTau163_three_term_error :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ ε : ℂ,
      ‖ε‖ < (1 / 2 : ℝ) ^ 150 ∧
      jacobiTheta τ = 1 + 2 * Q + 2 * Q ^ 4 + ε := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine ⟨jacobiTheta τ - (1 + 2 * Q + 2 * Q ^ 4), ?_, ?_⟩
  · simpa [τ, Q] using jacobiTheta_heegnerTau163_sub_three_terms_norm_lt_two_pow_neg_150
  · ring

lemma jacobiTheta_heegnerTau163_three_term_error_rel :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ ε : ℂ,
      ‖ε‖ ≤ 2 * ‖Q‖ ^ 9 / (1 - ‖Q‖) ∧
      jacobiTheta τ = 1 + 2 * Q + 2 * Q ^ 4 + ε := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine ⟨jacobiTheta τ - (1 + 2 * Q + 2 * Q ^ 4), ?_, ?_⟩
  · have h := jacobiTheta_heegnerTau163_sub_three_terms_norm_le
    have hQnorm : ‖Q‖ = Real.exp (-Real.pi * τ.im) := by
      dsimp [Q]
      exact norm_exp_pi_I_mul τ
    simpa [τ, Q, hQnorm] using h
  · ring

lemma thetaFourConst_heegnerTau163_three_term_error :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ ε : ℂ,
      ‖ε‖ < (1 / 2 : ℝ) ^ 150 ∧
      thetaFourConst τ = 1 - 2 * Q + 2 * Q ^ 4 + ε := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine ⟨thetaFourConst τ - (1 - 2 * Q + 2 * Q ^ 4), ?_, ?_⟩
  · simpa [τ, Q] using thetaFourConst_heegnerTau163_sub_three_terms_norm_lt_two_pow_neg_150
  · ring

lemma thetaFourConst_heegnerTau163_three_term_error_rel :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ ε : ℂ,
      ‖ε‖ ≤ 2 * ‖Q‖ ^ 9 / (1 - ‖Q‖) ∧
      thetaFourConst τ = 1 - 2 * Q + 2 * Q ^ 4 + ε := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine ⟨thetaFourConst τ - (1 - 2 * Q + 2 * Q ^ 4), ?_, ?_⟩
  · have h := thetaFourConst_heegnerTau163_sub_three_terms_norm_le
    have hQnorm : ‖Q‖ = Real.exp (-Real.pi * τ.im) := by
      dsimp [Q]
      exact norm_exp_pi_I_mul τ
    simpa [τ, Q, hQnorm] using h
  · ring

private lemma half_lt_norm_of_norm_sub_one_lt_half {z : ℂ}
    (h : ‖z - 1‖ < (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) < ‖z‖ := by
  have hone : ‖(1 : ℂ)‖ ≤ ‖z‖ + ‖z - 1‖ := by
    calc
      ‖(1 : ℂ)‖ = ‖z + (1 - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖1 - z‖ := norm_add_le _ _
      _ = ‖z‖ + ‖z - 1‖ := by
        rw [show 1 - z = -(z - 1) by ring, norm_neg]
  norm_num at hone
  linarith

lemma thetaTwoConst_heegnerTau163_normalized_norm_gt_half :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    (1 / 2 : ℝ) < ‖thetaTwoConst τ / ((2 : ℂ) * E)‖ := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  refine half_lt_norm_of_norm_sub_one_lt_half ?_
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail :
      ‖thetaTwoConst τ / ((2 : ℂ) * E) - 1‖ ≤ r / (1 - r) := by
    simpa [τ, E, r] using thetaTwoConst_heegnerTau163_normalized_sub_one_norm_le
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, r] using heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18
  have hsmall : r / (1 - r) < (1 / 2 : ℝ) :=
    (div_one_sub_lt_two_pow_succ (by norm_num : 1 ≤ (18 : ℕ)) hr).trans
      (by norm_num)
  exact htail.trans_lt hsmall

lemma jacobiTheta_heegnerTau163_norm_gt_half :
    (1 / 2 : ℝ) < ‖jacobiTheta (heegnerTau163 : ℂ)‖ := by
  refine half_lt_norm_of_norm_sub_one_lt_half ?_
  let τ : ℂ := heegnerTau163
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail : ‖jacobiTheta τ - 1‖ ≤ 2 * r / (1 - r) := by
    simpa [τ, r] using jacobiTheta_heegnerTau163_sub_one_norm_le
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, r] using heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18
  have hsmall : 2 * r / (1 - r) < (1 / 2 : ℝ) :=
    (two_mul_div_one_sub_lt_two_pow_pred (by norm_num : 2 ≤ (18 : ℕ)) hr).trans
      (by norm_num)
  exact htail.trans_lt hsmall

lemma thetaFourConst_heegnerTau163_norm_gt_half :
    (1 / 2 : ℝ) < ‖thetaFourConst (heegnerTau163 : ℂ)‖ := by
  refine half_lt_norm_of_norm_sub_one_lt_half ?_
  let τ : ℂ := heegnerTau163
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail : ‖thetaFourConst τ - 1‖ ≤ 2 * r / (1 - r) := by
    simpa [τ, r] using thetaFourConst_heegnerTau163_sub_one_norm_le
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, r] using heegnerTau163_exp_neg_pi_im_lt_two_pow_neg_18
  have hsmall : 2 * r / (1 - r) < (1 / 2 : ℝ) :=
    (two_mul_div_one_sub_lt_two_pow_pred (by norm_num : 2 ≤ (18 : ℕ)) hr).trans
      (by norm_num)
  exact htail.trans_lt hsmall

lemma kleinJThetaExpression_heegnerTau163_eq_normalized :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    let A : ℂ := thetaTwoConst τ / ((2 : ℂ) * E)
    let B : ℂ := jacobiTheta τ
    let C : ℂ := thetaFourConst τ
    kleinJThetaExpression τ =
      (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
        (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  let A : ℂ := thetaTwoConst τ / ((2 : ℂ) * E)
  let B : ℂ := jacobiTheta τ
  let C : ℂ := thetaFourConst τ
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have hA : thetaTwoConst τ = ((2 : ℂ) * E) * A := by
    dsimp [A]
    field_simp [hE]
  have hE4 : E ^ 4 = Q := by
    dsimp [E, Q]
    rw [← Complex.exp_nat_mul (Real.pi * Complex.I * τ / 4) 4]
    congr 1
    norm_num
    ring
  have hE8 : E ^ 8 = Q ^ 2 := by
    rw [show E ^ 8 = (E ^ 4) ^ 2 by ring, hE4]
  change
    256 * (B ^ 8 - thetaTwoConst τ ^ 4 * C ^ 4) ^ 3 /
        (thetaTwoConst τ ^ 8 * C ^ 8 * B ^ 8) =
      (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
        (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8)
  rw [hA]
  rw [show (((2 : ℂ) * E) * A) ^ 4 = 16 * Q * A ^ 4 by
    rw [mul_pow, mul_pow, hE4]
    norm_num]
  rw [show (((2 : ℂ) * E) * A) ^ 8 = 256 * Q ^ 2 * A ^ 8 by
    rw [mul_pow, mul_pow, hE8]
    norm_num]
  ring_nf

lemma kleinJThetaExpression_heegnerTau163_error_model :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ εA εB εC : ℂ,
      ‖εA‖ < (1 / 2 : ℝ) ^ 100 ∧
      ‖εB‖ < (1 / 2 : ℝ) ^ 150 ∧
      ‖εC‖ < (1 / 2 : ℝ) ^ 150 ∧
      kleinJThetaExpression τ =
        let A : ℂ := 1 + Q ^ 2 + εA
        let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
        let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
        (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
          (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  rcases (by
    simpa [τ, E, Q] using thetaTwoConst_heegnerTau163_two_term_error) with
    ⟨εA, hεA, hA⟩
  rcases (by
    simpa [τ, Q] using jacobiTheta_heegnerTau163_three_term_error) with
    ⟨εB, hεB, hB⟩
  rcases (by
    simpa [τ, Q] using thetaFourConst_heegnerTau163_three_term_error) with
    ⟨εC, hεC, hC⟩
  refine ⟨εA, εB, εC, ?_, ?_, ?_, ?_⟩
  · simpa using hεA
  · simpa using hεB
  · simpa using hεC
  have hnorm := kleinJThetaExpression_heegnerTau163_eq_normalized
  dsimp [τ, E, Q] at hnorm
  rw [hnorm, hA, hB, hC]

lemma kleinJThetaExpression_heegnerTau163_error_model_rel :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ∃ εA εB εC : ℂ,
      ‖εA‖ ≤ ‖Q‖ ^ 6 / (1 - ‖Q‖) ∧
      ‖εB‖ ≤ 2 * ‖Q‖ ^ 9 / (1 - ‖Q‖) ∧
      ‖εC‖ ≤ 2 * ‖Q‖ ^ 9 / (1 - ‖Q‖) ∧
      kleinJThetaExpression τ =
        let A : ℂ := 1 + Q ^ 2 + εA
        let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
        let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
        (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
          (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  rcases (by
    simpa [τ, E, Q] using thetaTwoConst_heegnerTau163_two_term_error_rel) with
    ⟨εA, hεA, hA⟩
  rcases (by
    simpa [τ, Q] using jacobiTheta_heegnerTau163_three_term_error_rel) with
    ⟨εB, hεB, hB⟩
  rcases (by
    simpa [τ, Q] using thetaFourConst_heegnerTau163_three_term_error_rel) with
    ⟨εC, hεC, hC⟩
  refine ⟨εA, εB, εC, hεA, hεB, hεC, ?_⟩
  have hnorm := kleinJThetaExpression_heegnerTau163_eq_normalized
  dsimp [τ, E, Q] at hnorm
  rw [hnorm, hA, hB, hC]

lemma heegnerTau163_truncatedA_sub_one_norm_lt_two_pow_neg_36 :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖(1 + Q ^ 2) - 1‖ < (1 / 2 : ℝ) ^ 36 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, Q] using norm_heegnerTau163_half_nome_lt_two_pow_neg_18
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  calc
    ‖(1 + Q ^ 2) - 1‖ = ‖Q‖ ^ 2 := by
      rw [show (1 + Q ^ 2) - 1 = Q ^ 2 by ring, norm_pow]
    _ < ((1 / 2 : ℝ) ^ 18) ^ 2 :=
      pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
    _ = (1 / 2 : ℝ) ^ 36 := by
      rw [← pow_mul]

lemma heegnerTau163_truncatedB_sub_one_norm_lt_two_pow_neg_16 :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖(1 + 2 * Q + 2 * Q ^ 4) - 1‖ < (1 / 2 : ℝ) ^ 16 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, Q] using norm_heegnerTau163_half_nome_lt_two_pow_neg_18
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQ4 : ‖Q‖ ^ 4 < ((1 / 2 : ℝ) ^ 18) ^ 4 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
  calc
    ‖(1 + 2 * Q + 2 * Q ^ 4) - 1‖ = ‖2 * Q + 2 * Q ^ 4‖ := by
      congr 1
      ring
    _ ≤ ‖2 * Q‖ + ‖2 * Q ^ 4‖ := norm_add_le _ _
    _ = 2 * ‖Q‖ + 2 * ‖Q‖ ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow]
      norm_num
    _ < (1 / 2 : ℝ) ^ 16 := by
      have hsmall :
          2 * ((1 / 2 : ℝ) ^ 18) + 2 * ((1 / 2 : ℝ) ^ 18) ^ 4 <
            (1 / 2 : ℝ) ^ 16 := by norm_num
      linarith

lemma heegnerTau163_truncatedC_sub_one_norm_lt_two_pow_neg_16 :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖(1 - 2 * Q + 2 * Q ^ 4) - 1‖ < (1 / 2 : ℝ) ^ 16 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, Q] using norm_heegnerTau163_half_nome_lt_two_pow_neg_18
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQ4 : ‖Q‖ ^ 4 < ((1 / 2 : ℝ) ^ 18) ^ 4 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
  calc
    ‖(1 - 2 * Q + 2 * Q ^ 4) - 1‖ = ‖-(2 * Q) + 2 * Q ^ 4‖ := by
      congr 1
      ring
    _ ≤ ‖-(2 * Q)‖ + ‖2 * Q ^ 4‖ := norm_add_le _ _
    _ = 2 * ‖Q‖ + 2 * ‖Q‖ ^ 4 := by
      rw [norm_neg, norm_mul, norm_mul, norm_pow]
      norm_num
    _ < (1 / 2 : ℝ) ^ 16 := by
      have hsmall :
          2 * ((1 / 2 : ℝ) ^ 18) + 2 * ((1 / 2 : ℝ) ^ 18) ^ 4 <
            (1 / 2 : ℝ) ^ 16 := by norm_num
      linarith

lemma heegnerTau163_truncatedA_norm_gt_half :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    (1 / 2 : ℝ) < ‖1 + Q ^ 2‖ := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine half_lt_norm_of_norm_sub_one_lt_half ?_
  have h := heegnerTau163_truncatedA_sub_one_norm_lt_two_pow_neg_36
  have hsmall : (1 / 2 : ℝ) ^ 36 < (1 / 2 : ℝ) := by norm_num
  have h' : ‖(1 + Q ^ 2) - 1‖ < (1 / 2 : ℝ) ^ 36 := by
    simpa [τ, Q] using h
  exact h'.trans hsmall

lemma heegnerTau163_truncatedB_norm_gt_half :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    (1 / 2 : ℝ) < ‖1 + 2 * Q + 2 * Q ^ 4‖ := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine half_lt_norm_of_norm_sub_one_lt_half ?_
  have h := heegnerTau163_truncatedB_sub_one_norm_lt_two_pow_neg_16
  have hsmall : (1 / 2 : ℝ) ^ 16 < (1 / 2 : ℝ) := by norm_num
  have h' : ‖(1 + 2 * Q + 2 * Q ^ 4) - 1‖ < (1 / 2 : ℝ) ^ 16 := by
    simpa [τ, Q] using h
  exact h'.trans hsmall

lemma heegnerTau163_truncatedC_norm_gt_half :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    (1 / 2 : ℝ) < ‖1 - 2 * Q + 2 * Q ^ 4‖ := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  refine half_lt_norm_of_norm_sub_one_lt_half ?_
  have h := heegnerTau163_truncatedC_sub_one_norm_lt_two_pow_neg_16
  have hsmall : (1 / 2 : ℝ) ^ 16 < (1 / 2 : ℝ) := by norm_num
  have h' : ‖(1 - 2 * Q + 2 * Q ^ 4) - 1‖ < (1 / 2 : ℝ) ^ 16 := by
    simpa [τ, Q] using h
  exact h'.trans hsmall

lemma heegnerTau163_usual_nome_eq_half_nome_sq :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    Complex.exp (2 * Real.pi * Complex.I * τ) = Q ^ 2 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  dsimp [Q]
  rw [← Complex.exp_nat_mul (Real.pi * Complex.I * τ) 2]
  congr 1
  norm_num
  ring

lemma heegnerTau163_principal_part_eq_half_nome :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    (Complex.exp (2 * Real.pi * Complex.I * τ))⁻¹ + 744 =
      Q⁻¹ ^ 2 + 744 := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have hq := heegnerTau163_usual_nome_eq_half_nome_sq
  dsimp [τ, Q] at hq ⊢
  rw [hq]
  ring

lemma thetaTwoConst_heegnerTau163_normalized_sub_one_norm_lt_two_pow_neg_17 :
    let τ : ℂ := heegnerTau163
    let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
    ‖thetaTwoConst τ / ((2 : ℂ) * E) - 1‖ < (1 / 2 : ℝ) ^ 17 := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail :
      ‖thetaTwoConst τ / ((2 : ℂ) * E) - 1‖ ≤ r / (1 - r) := by
    simpa [τ, E, r] using thetaTwoConst_heegnerTau163_normalized_sub_one_norm_le
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    have h := norm_heegnerTau163_q_half_lt_two_pow_neg_18
    rw [norm_heegnerTau163_q_half] at h
    have him : τ.im = Real.sqrt 163 / 2 := by
      dsimp [τ]
      exact heegnerTau163_im
    dsimp [r]
    rw [him]
    simpa [show -Real.pi * (Real.sqrt 163 / 2) =
        -(Real.pi * Real.sqrt 163 / 2) by ring] using h
  exact htail.trans_lt (div_one_sub_lt_two_pow_succ (by norm_num) hr)

lemma jacobiTheta_heegnerTau163_sub_one_norm_lt_two_pow_neg_16 :
    ‖jacobiTheta (heegnerTau163 : ℂ) - 1‖ < (1 / 2 : ℝ) ^ 16 := by
  let τ : ℂ := heegnerTau163
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail : ‖jacobiTheta τ - 1‖ ≤ 2 * r / (1 - r) := by
    simpa [τ, r] using jacobiTheta_heegnerTau163_sub_one_norm_le
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    have h := norm_heegnerTau163_q_half_lt_two_pow_neg_18
    rw [norm_heegnerTau163_q_half] at h
    have him : τ.im = Real.sqrt 163 / 2 := by
      dsimp [τ]
      exact heegnerTau163_im
    dsimp [r]
    rw [him]
    simpa [show -Real.pi * (Real.sqrt 163 / 2) =
        -(Real.pi * Real.sqrt 163 / 2) by ring] using h
  exact htail.trans_lt (two_mul_div_one_sub_lt_two_pow_pred (by norm_num) hr)

lemma thetaFourConst_heegnerTau163_sub_one_norm_lt_two_pow_neg_16 :
    ‖thetaFourConst (heegnerTau163 : ℂ) - 1‖ < (1 / 2 : ℝ) ^ 16 := by
  let τ : ℂ := heegnerTau163
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have htail : ‖thetaFourConst τ - 1‖ ≤ 2 * r / (1 - r) := by
    simpa [τ, r] using thetaFourConst_heegnerTau163_sub_one_norm_le
  have hr : r < (1 / 2 : ℝ) ^ 18 := by
    have h := norm_heegnerTau163_q_half_lt_two_pow_neg_18
    rw [norm_heegnerTau163_q_half] at h
    have him : τ.im = Real.sqrt 163 / 2 := by
      dsimp [τ]
      exact heegnerTau163_im
    dsimp [r]
    rw [him]
    simpa [show -Real.pi * (Real.sqrt 163 / 2) =
        -(Real.pi * Real.sqrt 163 / 2) by ring] using h
  exact htail.trans_lt (two_mul_div_one_sub_lt_two_pow_pred (by norm_num) hr)

private lemma two_mul_r_div_one_sub_r_lt_one {r : ℝ}
    (hr : r < (1 / 3 : ℝ)) :
    2 * r / (1 - r) < 1 := by
  have hden : 0 < 1 - r := by linarith
  rw [div_lt_one hden]
  linarith

/-- Nonvanishing of `θ₃` at `τ₁₆₃`, proved directly from the q-expansion
tail bound. -/
lemma jacobiTheta_heegnerTau163_ne_zero_qExpansion :
    jacobiTheta (heegnerTau163 : ℂ) ≠ 0 := by
  let τ : ℂ := heegnerTau163
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have htail : ‖jacobiTheta τ - 1‖ ≤ 2 * r / (1 - r) := by
    simpa [τ, r] using jacobiTheta_heegnerTau163_sub_one_norm_le
  have hsmall : 2 * r / (1 - r) < 1 :=
    two_mul_r_div_one_sub_r_lt_one hr_lt_third
  intro hzero
  have hdist : ‖jacobiTheta τ - 1‖ = 1 := by
    rw [hzero]
    norm_num
  rw [hdist] at htail
  linarith

/-- Nonvanishing of `θ₄` at `τ₁₆₃`, proved directly from the q-expansion
tail bound. -/
lemma thetaFourConst_heegnerTau163_ne_zero_qExpansion :
    thetaFourConst (heegnerTau163 : ℂ) ≠ 0 := by
  let τ : ℂ := heegnerTau163
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have htail : ‖thetaFourConst τ - 1‖ ≤ 2 * r / (1 - r) := by
    simpa [τ, r] using thetaFourConst_heegnerTau163_sub_one_norm_le
  have hsmall : 2 * r / (1 - r) < 1 :=
    two_mul_r_div_one_sub_r_lt_one hr_lt_third
  intro hzero
  have hdist : ‖thetaFourConst τ - 1‖ = 1 := by
    rw [hzero]
    norm_num
  rw [hdist] at htail
  linarith

/-- The Jacobi quartic identity specialized at `τ₁₆₃`. -/
lemma heegnerTau163_jacobiQuarticDefect_eq_zero :
    jacobiQuarticDefect (heegnerTau163 : ℂ) = 0 :=
  jacobiQuarticDefect_eq_zero (heegnerTau163 : ℂ) heegnerTau163.2

/-- Nonvanishing of `θ₂` at `τ₁₆₃`.

This follows by isolating the first shifted q-series term and bounding the
remaining tail by `|q| = exp (-π sqrt 163)`. -/
theorem thetaTwoConst_heegnerTau163_ne_zero :
    thetaTwoConst (heegnerTau163 : ℂ) ≠ 0 := by
  let τ : ℂ := heegnerTau163
  let E : ℂ := Complex.exp (Real.pi * Complex.I * τ / 4)
  let r : ℝ := Real.exp (-Real.pi * τ.im)
  have him : 1 ≤ τ.im := by
    dsimp [τ]
    simpa using heegnerTau163_one_le_im_local
  have hE : (2 : ℂ) * E ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have hr_lt_third : r < (1 / 3 : ℝ) := by
    dsimp [r]
    exact exp_neg_pi_mul_im_lt_one_third him
  have htail_bound :
      ‖thetaTwoConst τ / ((2 : ℂ) * E) - 1‖ ≤ r / (1 - r) := by
    simpa [τ, E, r] using thetaTwoConst_heegnerTau163_normalized_sub_one_norm_le
  intro hzero
  have hdist : ‖thetaTwoConst τ / ((2 : ℂ) * E) - 1‖ = 1 := by
    rw [hzero]
    simp
  have hsmall : r / (1 - r) < 1 := by
    have hden : 0 < 1 - r := by linarith
    rw [div_lt_one hden]
    linarith
  rw [hdist] at htail_bound
  linarith

/-- Nonvanishing of `θ₄` at `τ₁₆₃`.

This follows from the q-series `θ₄ = 1 + O(q)` and the same tiny-q tail
bound. -/
theorem thetaFourConst_heegnerTau163_ne_zero :
    thetaFourConst (heegnerTau163 : ℂ) ≠ 0 := by
  exact thetaFourConst_heegnerTau163_ne_zero_qExpansion

/-- The theta-lambda value at `τ₁₆₃` is nonzero. -/
lemma thetaLambda_heegnerTau163_ne_zero :
    thetaLambda (heegnerTau163 : ℂ) ≠ 0 := by
  unfold thetaLambda
  exact div_ne_zero
    (pow_ne_zero 4 thetaTwoConst_heegnerTau163_ne_zero)
    (pow_ne_zero 4 jacobiTheta_heegnerTau163_ne_zero_qExpansion)

/-- The complementary theta-lambda value at `τ₁₆₃` is nonzero. -/
lemma one_sub_thetaLambda_heegnerTau163_ne_zero :
    1 - thetaLambda (heegnerTau163 : ℂ) ≠ 0 := by
  have hone :
      1 - thetaLambda (heegnerTau163 : ℂ) =
        thetaFourConst (heegnerTau163 : ℂ) ^ 4 /
          jacobiTheta (heegnerTau163 : ℂ) ^ 4 :=
    one_sub_thetaLambda_of_jacobiQuarticDefect_zero
      (heegnerTau163 : ℂ)
      jacobiTheta_heegnerTau163_ne_zero_qExpansion
      heegnerTau163_jacobiQuarticDefect_eq_zero
  rw [hone]
  exact div_ne_zero
    (pow_ne_zero 4 thetaFourConst_heegnerTau163_ne_zero)
    (pow_ne_zero 4 jacobiTheta_heegnerTau163_ne_zero_qExpansion)

/-- Denominator nonvanishing for the Legendre `j`-map at the CM lambda
value. -/
lemma kleinJFromLambda_thetaLambda_heegnerTau163_den_ne_zero :
    thetaLambda (heegnerTau163 : ℂ) ^ 2 *
        (1 - thetaLambda (heegnerTau163 : ℂ)) ^ 2 ≠ 0 := by
  exact mul_ne_zero
    (pow_ne_zero 2 thetaLambda_heegnerTau163_ne_zero)
    (pow_ne_zero 2 one_sub_thetaLambda_heegnerTau163_ne_zero)

/-- The Legendre-lambda rational expression reduces to the theta-constant
expression at `τ₁₆₃`.  This part is purely algebraic once the Jacobi quartic
identity and denominator nonvanishing are known. -/
lemma kleinJFromLambda_thetaLambda_heegnerTau163_eq_thetaExpression :
    kleinJFromLambda (thetaLambda (heegnerTau163 : ℂ)) =
      kleinJThetaExpression (heegnerTau163 : ℂ) := by
  simpa [kleinJThetaExpression] using
    kleinJFromLambda_thetaLambda_of_jacobiQuarticDefect_zero
      (heegnerTau163 : ℂ)
      jacobiTheta_heegnerTau163_ne_zero_qExpansion
      thetaTwoConst_heegnerTau163_ne_zero
      thetaFourConst_heegnerTau163_ne_zero
      heegnerTau163_jacobiQuarticDefect_eq_zero


private lemma normalizedKleinJ_error_model_factor_norms_gt_half
    {Q εA εB εC : ℂ}
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    (1 / 2 : ℝ) < ‖A‖ ∧ (1 / 2 : ℝ) < ‖B‖ ∧ (1 / 2 : ℝ) < ‖C‖ := by
  let A : ℂ := 1 + Q ^ 2 + εA
  let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
  let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQ2 : ‖Q‖ ^ 2 < ((1 / 2 : ℝ) ^ 18) ^ 2 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
  have hQ4 : ‖Q‖ ^ 4 < ((1 / 2 : ℝ) ^ 18) ^ 4 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
  have hAclose : ‖A - 1‖ < (1 / 2 : ℝ) := by
    calc
      ‖A - 1‖ = ‖Q ^ 2 + εA‖ := by
        dsimp [A]
        congr 1
        ring
      _ ≤ ‖Q ^ 2‖ + ‖εA‖ := norm_add_le _ _
      _ = ‖Q‖ ^ 2 + ‖εA‖ := by rw [norm_pow]
      _ < (1 / 2 : ℝ) := by
        have hsmall : ((1 / 2 : ℝ) ^ 18) ^ 2 + (1 / 2 : ℝ) ^ 100 <
            (1 / 2 : ℝ) := by norm_num
        linarith
  have hBclose : ‖B - 1‖ < (1 / 2 : ℝ) := by
    calc
      ‖B - 1‖ = ‖(2 : ℂ) * Q + 2 * Q ^ 4 + εB‖ := by
        dsimp [B]
        congr 1
        ring
      _ ≤ ‖(2 : ℂ) * Q + 2 * Q ^ 4‖ + ‖εB‖ := norm_add_le _ _
      _ ≤ (‖(2 : ℂ) * Q‖ + ‖2 * Q ^ 4‖) + ‖εB‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (2 * ‖Q‖ + 2 * ‖Q‖ ^ 4) + ‖εB‖ := by
        rw [norm_mul, norm_mul, norm_pow]
        norm_num
      _ < (1 / 2 : ℝ) := by
        have hsmall :
            (2 * ((1 / 2 : ℝ) ^ 18) + 2 * ((1 / 2 : ℝ) ^ 18) ^ 4) +
                (1 / 2 : ℝ) ^ 150 <
              (1 / 2 : ℝ) := by norm_num
        linarith
  have hCclose : ‖C - 1‖ < (1 / 2 : ℝ) := by
    calc
      ‖C - 1‖ = ‖-(2 * Q) + 2 * Q ^ 4 + εC‖ := by
        dsimp [C]
        congr 1
        ring
      _ ≤ ‖-(2 * Q) + 2 * Q ^ 4‖ + ‖εC‖ := norm_add_le _ _
      _ ≤ (‖-(2 * Q)‖ + ‖2 * Q ^ 4‖) + ‖εC‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (2 * ‖Q‖ + 2 * ‖Q‖ ^ 4) + ‖εC‖ := by
        rw [norm_neg, norm_mul, norm_mul, norm_pow]
        norm_num
      _ < (1 / 2 : ℝ) := by
        have hsmall :
            (2 * ((1 / 2 : ℝ) ^ 18) + 2 * ((1 / 2 : ℝ) ^ 18) ^ 4) +
                (1 / 2 : ℝ) ^ 150 <
              (1 / 2 : ℝ) := by norm_num
        linarith
  exact ⟨half_lt_norm_of_norm_sub_one_lt_half hAclose,
    half_lt_norm_of_norm_sub_one_lt_half hBclose,
    half_lt_norm_of_norm_sub_one_lt_half hCclose⟩

private lemma normalizedKleinJ_error_model_factor_norms_lt_two
    {Q εA εB εC : ℂ}
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    ‖A‖ < (2 : ℝ) ∧ ‖B‖ < (2 : ℝ) ∧ ‖C‖ < (2 : ℝ) := by
  let A : ℂ := 1 + Q ^ 2 + εA
  let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
  let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQ2 : ‖Q‖ ^ 2 < ((1 / 2 : ℝ) ^ 18) ^ 2 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
  have hQ4 : ‖Q‖ ^ 4 < ((1 / 2 : ℝ) ^ 18) ^ 4 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (by norm_num)
  have hAclose : ‖A - 1‖ < (1 / 2 : ℝ) := by
    calc
      ‖A - 1‖ = ‖Q ^ 2 + εA‖ := by
        dsimp [A]
        congr 1
        ring
      _ ≤ ‖Q ^ 2‖ + ‖εA‖ := norm_add_le _ _
      _ = ‖Q‖ ^ 2 + ‖εA‖ := by rw [norm_pow]
      _ < (1 / 2 : ℝ) := by
        have hsmall : ((1 / 2 : ℝ) ^ 18) ^ 2 + (1 / 2 : ℝ) ^ 100 <
            (1 / 2 : ℝ) := by norm_num
        linarith
  have hBclose : ‖B - 1‖ < (1 / 2 : ℝ) := by
    calc
      ‖B - 1‖ = ‖(2 : ℂ) * Q + 2 * Q ^ 4 + εB‖ := by
        dsimp [B]
        congr 1
        ring
      _ ≤ ‖(2 : ℂ) * Q + 2 * Q ^ 4‖ + ‖εB‖ := norm_add_le _ _
      _ ≤ (‖(2 : ℂ) * Q‖ + ‖2 * Q ^ 4‖) + ‖εB‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (2 * ‖Q‖ + 2 * ‖Q‖ ^ 4) + ‖εB‖ := by
        rw [norm_mul, norm_mul, norm_pow]
        norm_num
      _ < (1 / 2 : ℝ) := by
        have hsmall :
            (2 * ((1 / 2 : ℝ) ^ 18) + 2 * ((1 / 2 : ℝ) ^ 18) ^ 4) +
                (1 / 2 : ℝ) ^ 150 <
              (1 / 2 : ℝ) := by norm_num
        linarith
  have hCclose : ‖C - 1‖ < (1 / 2 : ℝ) := by
    calc
      ‖C - 1‖ = ‖-(2 * Q) + 2 * Q ^ 4 + εC‖ := by
        dsimp [C]
        congr 1
        ring
      _ ≤ ‖-(2 * Q) + 2 * Q ^ 4‖ + ‖εC‖ := norm_add_le _ _
      _ ≤ (‖-(2 * Q)‖ + ‖2 * Q ^ 4‖) + ‖εC‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (2 * ‖Q‖ + 2 * ‖Q‖ ^ 4) + ‖εC‖ := by
        rw [norm_neg, norm_mul, norm_mul, norm_pow]
        norm_num
      _ < (1 / 2 : ℝ) := by
        have hsmall :
            (2 * ((1 / 2 : ℝ) ^ 18) + 2 * ((1 / 2 : ℝ) ^ 18) ^ 4) +
                (1 / 2 : ℝ) ^ 150 <
              (1 / 2 : ℝ) := by norm_num
        linarith
  have hA : ‖A‖ ≤ ‖A - 1‖ + ‖(1 : ℂ)‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_add_le (A - 1) (1 : ℂ)
  have hB : ‖B‖ ≤ ‖B - 1‖ + ‖(1 : ℂ)‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_add_le (B - 1) (1 : ℂ)
  have hC : ‖C‖ ≤ ‖C - 1‖ + ‖(1 : ℂ)‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_add_le (C - 1) (1 : ℂ)
  have hA2 : ‖A‖ < (2 : ℝ) := by
    norm_num at hA
    linarith
  have hB2 : ‖B‖ < (2 : ℝ) := by
    norm_num at hB
    linarith
  have hC2 : ‖C‖ < (2 : ℝ) := by
    norm_num at hC
    linarith
  exact ⟨hA2, hB2, hC2⟩

private lemma normalizedKleinJ_error_model_den_norm_lower
    {Q εA εB εC : ℂ}
    (hQ0 : Q ≠ 0)
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    (1 / 2 : ℝ) ^ 24 * ‖Q‖ ^ 2 <
      ‖Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8‖ := by
  let A : ℂ := 1 + Q ^ 2 + εA
  let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
  let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
  have hfac := normalizedKleinJ_error_model_factor_norms_gt_half
    (Q := Q) (εA := εA) (εB := εB) (εC := εC) hQ hεA hεB hεC
  dsimp [A, B, C] at hfac
  rcases hfac with ⟨hA, hB, hC⟩
  have hQpos : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
  have hA8 : (1 / 2 : ℝ) ^ 8 < ‖A‖ ^ 8 :=
    pow_lt_pow_left₀ hA (by norm_num) (by norm_num)
  have hB8 : (1 / 2 : ℝ) ^ 8 < ‖B‖ ^ 8 :=
    pow_lt_pow_left₀ hB (by norm_num) (by norm_num)
  have hC8 : (1 / 2 : ℝ) ^ 8 < ‖C‖ ^ 8 :=
    pow_lt_pow_left₀ hC (by norm_num) (by norm_num)
  change (1 / 2 : ℝ) ^ 24 * ‖Q‖ ^ 2 <
      ‖Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8‖
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
  have hQ2pos : 0 < ‖Q‖ ^ 2 := pow_pos hQpos _
  have hhalf24 : (1 / 2 : ℝ) ^ 24 =
      (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 := by
    norm_num [pow_add]
  rw [hhalf24]
  have hA8pos : 0 < ‖A‖ ^ 8 := lt_trans (by norm_num) hA8
  have hC8pos : 0 < ‖C‖ ^ 8 := lt_trans (by norm_num) hC8
  have hAC : (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 < ‖A‖ ^ 8 * ‖C‖ ^ 8 :=
    mul_lt_mul hA8 hC8.le (by norm_num : (0 : ℝ) < (1 / 2) ^ 8) hA8pos.le
  have hAC_rhs_pos : 0 < ‖A‖ ^ 8 * ‖C‖ ^ 8 := mul_pos hA8pos hC8pos
  have hACB :
      (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 <
        ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8 :=
    mul_lt_mul hAC hB8.le (by norm_num : (0 : ℝ) < (1 / 2) ^ 8) hAC_rhs_pos.le
  calc
    (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 * ‖Q‖ ^ 2
        = ‖Q‖ ^ 2 * ((1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 8) := by
          ring
    _ < ‖Q‖ ^ 2 * (‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8) :=
          mul_lt_mul_of_pos_left hACB hQ2pos
    _ = ‖Q‖ ^ 2 * ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8 := by
          ring

private noncomputable def truncatedNResidual (Q : ℂ) : ℂ :=
  16 * (16 * Q ^ 28 + 128 * Q ^ 25 + 64 * Q ^ 24 + 448 * Q ^ 22 +
    432 * Q ^ 21 + 112 * Q ^ 20 + 832 * Q ^ 19 + 1408 * Q ^ 18 +
    544 * Q ^ 17 + 1488 * Q ^ 16 + 1952 * Q ^ 15 + 2160 * Q ^ 14 +
    840 * Q ^ 13 + 3014 * Q ^ 12 + 1344 * Q ^ 11 + 2512 * Q ^ 10 +
    656 * Q ^ 9 + 2700 * Q ^ 8 + 360 * Q ^ 7 + 1644 * Q ^ 6 +
    107 * Q ^ 5 + 1063 * Q ^ 4 + 4 * Q ^ 3 + 420 * Q ^ 2 + 135)

private noncomputable def truncatedMResidual (Q : ℂ) : ℂ :=
  65536 * Q ^ 76 + 524288 * Q ^ 74 + 2359296 * Q ^ 72 +
    7340032 * Q ^ 70 + 17039360 * Q ^ 68 + 30408704 * Q ^ 66 +
    41287680 * Q ^ 64 + 39976960 * Q ^ 62 + 20365312 * Q ^ 60 -
    11403264 * Q ^ 58 - 36470784 * Q ^ 56 - 36864000 * Q ^ 54 -
    12083200 * Q ^ 52 + 17203200 * Q ^ 50 + 27074560 * Q ^ 48 +
    13082624 * Q ^ 46 - 7715328 * Q ^ 44 - 14995456 * Q ^ 42 -
    6356992 * Q ^ 40 + 4618240 * Q ^ 38 + 6813184 * Q ^ 36 +
    1275904 * Q ^ 34 - 2877952 * Q ^ 32 - 2003456 * Q ^ 30 +
    426944 * Q ^ 28 + 1229312 * Q ^ 26 + 128128 * Q ^ 24 -
    473984 * Q ^ 22 - 119712 * Q ^ 20 + 98688 * Q ^ 18 +
    113248 * Q ^ 16 - 49952 * Q ^ 14 - 50559 * Q ^ 12 +
    41864 * Q ^ 10 - 4004 * Q ^ 8 - 8200 * Q ^ 6 +
    5030 * Q ^ 4 - 1480 * Q ^ 2 + 252

private lemma truncatedN_expansion (Q : ℂ) :
    let A : ℂ := 1 + Q ^ 2
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4
    B ^ 8 - 16 * Q * A ^ 4 * C ^ 4 =
      1 + 240 * Q ^ 2 + Q ^ 4 * truncatedNResidual Q := by
  intro A B C
  dsimp [A, B, C, truncatedNResidual]
  ring_nf

private lemma truncatedM_expansion (Q : ℂ) :
    let A : ℂ := 1 + Q ^ 2
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4
    A ^ 8 * C ^ 8 * B ^ 8 =
      1 - 24 * Q ^ 2 + Q ^ 4 * truncatedMResidual Q := by
  intro A B C
  dsimp [A, B, C, truncatedMResidual]
  ring_nf

private noncomputable def idealNumeratorResidual (Q : ℂ) : ℂ :=
  16777216 * Q ^ 92 + 402653184 * Q ^ 89 + 201326592 * Q ^ 88 +
    4630511616 * Q ^ 86 + 4580179968 * Q ^ 85 +
    1157627904 * Q ^ 84 + 33755758592 * Q ^ 83 +
    50331648000 * Q ^ 82 + 24662507520 * Q ^ 81 +
    180103413760 * Q ^ 80 + 351214239744 * Q ^ 79 +
    258051932160 * Q ^ 78 + 784292904960 * Q ^ 77 +
    1759877464064 * Q ^ 76 + 1724362260480 * Q ^ 75 +
    3054096613376 * Q ^ 74 + 6838510682112 * Q ^ 73 +
    8238747353088 * Q ^ 72 + 11075051323392 * Q ^ 71 +
    21878751100928 * Q ^ 70 + 30090722279424 * Q ^ 69 +
    36642304557056 * Q ^ 68 + 60509273456640 * Q ^ 67 +
    88116186578944 * Q ^ 66 + 106257146970112 * Q ^ 65 +
    149387322458112 * Q ^ 64 + 214828358565888 * Q ^ 63 +
    263684606656512 * Q ^ 62 + 332088358207488 * Q ^ 61 +
    450159454994432 * Q ^ 60 + 556404783972352 * Q ^ 59 +
    661051590967296 * Q ^ 58 + 826119168196608 * Q ^ 57 +
    1010411447549952 * Q ^ 56 + 1155102629953536 * Q ^ 55 +
    1355550085447680 * Q ^ 54 + 1577505084538880 * Q ^ 53 +
    1787512718516224 * Q ^ 52 + 1945222604390400 * Q ^ 51 +
    2206115533455360 * Q ^ 50 + 2349769215442944 * Q ^ 49 +
    2557035903180800 * Q ^ 48 + 2608519212957696 * Q ^ 47 +
    2851833629962240 * Q ^ 46 + 2763115470323712 * Q ^ 45 +
    2962499666442752 * Q ^ 44 + 2744750326677504 * Q ^ 43 +
    2957181865873408 * Q ^ 42 + 2553152275218432 * Q ^ 41 +
    2769686427516928 * Q ^ 40 + 2239540375191552 * Q ^ 39 +
    2470644799051776 * Q ^ 38 + 1823573589172224 * Q ^ 37 +
    2080021583751680 * Q ^ 36 + 1392823426973696 * Q ^ 35 +
    1655100219791360 * Q ^ 34 + 981867087101952 * Q ^ 33 +
    1242435933526528 * Q ^ 32 + 642322053464064 * Q ^ 31 +
    875338012986368 * Q ^ 30 + 384601797992448 * Q ^ 29 +
    578213477849920 * Q ^ 28 + 210577819926528 * Q ^ 27 +
    355246496934400 * Q ^ 26 + 104028323813376 * Q ^ 25 +
    202383261610880 * Q ^ 24 + 46005670203392 * Q ^ 23 +
    105835815069824 * Q ^ 22 + 17912723815680 * Q ^ 21 +
    50483701082272 * Q ^ 20 + 6029458246656 * Q ^ 19 +
    21676329574272 * Q ^ 18 + 1707762191872 * Q ^ 17 +
    8282786350496 * Q ^ 16 + 390549825024 * Q ^ 15 +
    2762261815352 * Q ^ 14 + 67984194432 * Q ^ 13 +
    787066739295 * Q ^ 12 + 8000830464 * Q ^ 11 +
    185111498776 * Q ^ 10 + 527993088 * Q ^ 9 +
    34318577444 * Q ^ 8 + 14371200 * Q ^ 7 +
    4628375512 * Q ^ 6 + 97296 * Q ^ 5 +
    398068714 * Q ^ 4 + 192 * Q ^ 3 +
    16768552 * Q ^ 2 + 196884

private def idealNumeratorResidualTailTerms : List (ℕ × ℕ) :=
  [(16777216, 90), (402653184, 87), (201326592, 86),
    (4630511616, 84), (4580179968, 83), (1157627904, 82),
    (33755758592, 81), (50331648000, 80), (24662507520, 79),
    (180103413760, 78), (351214239744, 77), (258051932160, 76),
    (784292904960, 75), (1759877464064, 74), (1724362260480, 73),
    (3054096613376, 72), (6838510682112, 71), (8238747353088, 70),
    (11075051323392, 69), (21878751100928, 68), (30090722279424, 67),
    (36642304557056, 66), (60509273456640, 65), (88116186578944, 64),
    (106257146970112, 63), (149387322458112, 62), (214828358565888, 61),
    (263684606656512, 60), (332088358207488, 59), (450159454994432, 58),
    (556404783972352, 57), (661051590967296, 56), (826119168196608, 55),
    (1010411447549952, 54), (1155102629953536, 53), (1355550085447680, 52),
    (1577505084538880, 51), (1787512718516224, 50), (1945222604390400, 49),
    (2206115533455360, 48), (2349769215442944, 47), (2557035903180800, 46),
    (2608519212957696, 45), (2851833629962240, 44), (2763115470323712, 43),
    (2962499666442752, 42), (2744750326677504, 41), (2957181865873408, 40),
    (2553152275218432, 39), (2769686427516928, 38), (2239540375191552, 37),
    (2470644799051776, 36), (1823573589172224, 35), (2080021583751680, 34),
    (1392823426973696, 33), (1655100219791360, 32), (981867087101952, 31),
    (1242435933526528, 30), (642322053464064, 29), (875338012986368, 28),
    (384601797992448, 27), (578213477849920, 26), (210577819926528, 25),
    (355246496934400, 24), (104028323813376, 23), (202383261610880, 22),
    (46005670203392, 21), (105835815069824, 20), (17912723815680, 19),
    (50483701082272, 18), (6029458246656, 17), (21676329574272, 16),
    (1707762191872, 15), (8282786350496, 14), (390549825024, 13),
    (2762261815352, 12), (67984194432, 11), (787066739295, 10),
    (8000830464, 9), (185111498776, 8), (527993088, 7),
    (34318577444, 6), (14371200, 5), (4628375512, 4), (97296, 3),
    (398068714, 2), (192, 1), (16768552, 0)]

private noncomputable def idealNumeratorResidualTail (Q : ℂ) : ℂ :=
  (idealNumeratorResidualTailTerms.map (fun t => (t.1 : ℂ) * Q ^ t.2)).sum

private lemma norm_tail_term_list_le_coeff_sum
    (terms : List (ℕ × ℕ)) (Q : ℂ) (hQ1 : ‖Q‖ ≤ 1) :
    ‖(terms.map (fun t => (t.1 : ℂ) * Q ^ t.2)).sum‖ ≤
      (terms.map (fun t => (t.1 : ℝ))).sum := by
  induction terms with
  | nil =>
      simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        ‖(t.1 : ℂ) * Q ^ t.2 +
            (ts.map (fun t => (t.1 : ℂ) * Q ^ t.2)).sum‖
            ≤ ‖(t.1 : ℂ) * Q ^ t.2‖ +
                ‖(ts.map (fun t => (t.1 : ℂ) * Q ^ t.2)).sum‖ := norm_add_le _ _
        _ ≤ (t.1 : ℝ) + (ts.map (fun t => (t.1 : ℝ))).sum := by
          exact add_le_add
            (by
              calc
                ‖(t.1 : ℂ) * Q ^ t.2‖ = (t.1 : ℝ) * ‖Q‖ ^ t.2 := by
                  rw [norm_mul, norm_pow, Complex.norm_natCast]
                _ ≤ (t.1 : ℝ) * 1 := by
                  exact mul_le_mul_of_nonneg_left
                    (pow_le_one₀ (norm_nonneg Q) hQ1)
                    (by exact_mod_cast Nat.zero_le t.1)
                _ = (t.1 : ℝ) := by ring)
            ih

private lemma idealNumeratorResidual_eq_const_add_tail (Q : ℂ) :
    idealNumeratorResidual Q =
      196884 + Q ^ 2 * idealNumeratorResidualTail Q := by
  dsimp [idealNumeratorResidual, idealNumeratorResidualTail,
    idealNumeratorResidualTailTerms]
  ring_nf

private lemma idealNumeratorResidualTail_norm_le (Q : ℂ) (hQ1 : ‖Q‖ ≤ 1) :
    ‖idealNumeratorResidualTail Q‖ ≤ (60000000000000000 : ℝ) := by
  calc
    ‖idealNumeratorResidualTail Q‖
        ≤ (idealNumeratorResidualTailTerms.map (fun t => (t.1 : ℝ))).sum := by
          simpa [idealNumeratorResidualTail] using
            norm_tail_term_list_le_coeff_sum idealNumeratorResidualTailTerms Q hQ1
    _ ≤ (60000000000000000 : ℝ) := by
          norm_num [idealNumeratorResidualTailTerms]

private lemma idealNumeratorResidual_norm_le (Q : ℂ)
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18) :
    ‖idealNumeratorResidual Q‖ ≤ (2000000 : ℝ) := by
  have hQ1 : ‖Q‖ ≤ 1 :=
    hQ.le.trans (by norm_num : ((1 / 2 : ℝ) ^ 18) ≤ 1)
  have hQ2 :
      ‖Q‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ 18) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg Q) hQ.le 2
  have htail := idealNumeratorResidualTail_norm_le Q hQ1
  rw [idealNumeratorResidual_eq_const_add_tail]
  calc
    ‖(196884 : ℂ) + Q ^ 2 * idealNumeratorResidualTail Q‖
        ≤ ‖(196884 : ℂ)‖ + ‖Q ^ 2 * idealNumeratorResidualTail Q‖ := norm_add_le _ _
    _ = (196884 : ℝ) + ‖Q‖ ^ 2 * ‖idealNumeratorResidualTail Q‖ := by
          rw [norm_mul, norm_pow]
          norm_num
    _ ≤ (196884 : ℝ) + ((1 / 2 : ℝ) ^ 18) ^ 2 *
          (60000000000000000 : ℝ) := by
          exact add_le_add le_rfl (mul_le_mul hQ2 htail (norm_nonneg _)
            (by positivity))
    _ ≤ (2000000 : ℝ) := by
          norm_num


/-- The cube of `B₀⁸ − 16QA₀⁴C₀⁴` minus `(1+744Q²)A₀⁸C₀⁸B₀⁸` at ε = 0,
expressed as Q⁴ times a bounded complex number.

Using `truncatedN_expansion`: `X₀ = 1 + 240Q² + Q⁴·N(Q)`,
and `truncatedM_expansion`: `A₀⁸C₀⁸B₀⁸ = 1 − 24Q² + Q⁴·M(Q)`,
one expands `X₀³ − (1+744Q²)(1−24Q²+Q⁴M)` and verifies the constant
and Q² terms cancel (mod Q⁵ the residual is 196884·Q⁴). -/
private lemma ideal_numerator_eq_Q4_factor (Q : ℂ)
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18) :
    let A₀ : ℂ := 1 + Q ^ 2
    let B₀ : ℂ := 1 + 2 * Q + 2 * Q ^ 4
    let C₀ : ℂ := 1 - 2 * Q + 2 * Q ^ 4
    ∃ P : ℂ,
      (B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4) ^ 3 -
          (1 + 744 * Q ^ 2) * (A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8) =
        Q ^ 4 * P ∧
      ‖P‖ ≤ (2000000 : ℝ) := by
  intro A₀ B₀ C₀
  refine ⟨idealNumeratorResidual Q, ?_, idealNumeratorResidual_norm_le Q hQ⟩
  dsimp [A₀, B₀, C₀, idealNumeratorResidual]
  ring_nf

private lemma normalizedKleinJ_N_perturb_bound
    {Q εA εB εC : ℂ}
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    let A₀ : ℂ := 1 + Q ^ 2
    let B₀ : ℂ := 1 + 2 * Q + 2 * Q ^ 4
    let C₀ : ℂ := 1 - 2 * Q + 2 * Q ^ 4
    ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) -
        (B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4)‖
      ≤ 1024 * ‖εB‖ + 8192 * ‖Q‖ * (‖εA‖ + ‖εC‖) := by
  intro A B C A₀ B₀ C₀
  have hfac := normalizedKleinJ_error_model_factor_norms_lt_two hQ hεA hεB hεC
  change ‖A‖ < (2 : ℝ) ∧ ‖B‖ < (2 : ℝ) ∧ ‖C‖ < (2 : ℝ) at hfac
  obtain ⟨hA2, hB2, hC2⟩ := hfac
  have hzeroA : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 100 := by norm_num
  have hzeroB : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 150 := by norm_num
  have hzeroC : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 150 := by norm_num
  have hfac0 := normalizedKleinJ_error_model_factor_norms_lt_two
    (Q := Q) (εA := 0) (εB := 0) (εC := 0) hQ hzeroA hzeroB hzeroC
  have hfac0' : ‖A₀‖ < (2 : ℝ) ∧ ‖B₀‖ < (2 : ℝ) ∧ ‖C₀‖ < (2 : ℝ) := by
    simpa [A₀, B₀, C₀] using hfac0
  obtain ⟨hA02, hB02, hC02⟩ := hfac0'
  have hBdiff : ‖B ^ 8 - B₀ ^ 8‖ ≤ 1024 * ‖εB‖ := by
    have h := norm_pow_eight_sub_pow_eight_le_of_norm_lt_two hB2 hB02
    have hsub : B - B₀ = εB := by
      dsimp [B, B₀]
      ring
    simpa [hsub] using h
  have hAdiff4 : ‖A ^ 4 - A₀ ^ 4‖ ≤ 32 * ‖εA‖ := by
    have h := norm_pow_four_sub_pow_four_le_of_norm_lt_two hA2 hA02
    have hsub : A - A₀ = εA := by
      dsimp [A, A₀]
      ring
    simpa [hsub] using h
  have hCdiff4 : ‖C ^ 4 - C₀ ^ 4‖ ≤ 32 * ‖εC‖ := by
    have h := norm_pow_four_sub_pow_four_le_of_norm_lt_two hC2 hC02
    have hsub : C - C₀ = εC := by
      dsimp [C, C₀]
      ring
    simpa [hsub] using h
  have hC4 : ‖C ^ 4‖ ≤ (16 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hC2.le 4).trans (by norm_num)
  have hA04 : ‖A₀ ^ 4‖ ≤ (16 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hA02.le 4).trans (by norm_num)
  have hprod :
      ‖A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4‖
        ≤ 512 * (‖εA‖ + ‖εC‖) := by
    have hsplit :
        A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4 =
          (A ^ 4 - A₀ ^ 4) * C ^ 4 + A₀ ^ 4 * (C ^ 4 - C₀ ^ 4) := by
      ring
    calc
      ‖A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4‖
          = ‖(A ^ 4 - A₀ ^ 4) * C ^ 4 + A₀ ^ 4 * (C ^ 4 - C₀ ^ 4)‖ := by
            rw [hsplit]
      _ ≤ ‖(A ^ 4 - A₀ ^ 4) * C ^ 4‖ +
            ‖A₀ ^ 4 * (C ^ 4 - C₀ ^ 4)‖ := norm_add_le _ _
      _ = ‖A ^ 4 - A₀ ^ 4‖ * ‖C ^ 4‖ +
            ‖A₀ ^ 4‖ * ‖C ^ 4 - C₀ ^ 4‖ := by rw [norm_mul, norm_mul]
      _ ≤ (32 * ‖εA‖) * 16 + 16 * (32 * ‖εC‖) := by
            exact add_le_add
              (mul_le_mul hAdiff4 hC4 (norm_nonneg _) (by positivity))
              (mul_le_mul hA04 hCdiff4 (norm_nonneg _) (by positivity))
      _ = 512 * (‖εA‖ + ‖εC‖) := by ring
  have hmain :
      ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) -
          (B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4)‖
        ≤ 1024 * ‖εB‖ + 16 * ‖Q‖ * (512 * (‖εA‖ + ‖εC‖)) := by
    calc
      ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) -
          (B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4)‖
          = ‖(B ^ 8 - B₀ ^ 8) -
              16 * Q * (A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4)‖ := by
              congr 1
              ring
      _ ≤ ‖B ^ 8 - B₀ ^ 8‖ +
            16 * ‖Q‖ * ‖A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4‖ := by
              have h := norm_add_le (B ^ 8 - B₀ ^ 8)
                (-(16 * Q * (A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4)))
              rw [norm_neg, norm_mul, norm_mul] at h
              norm_num at h
              simpa [sub_eq_add_neg] using h
      _ ≤ 1024 * ‖εB‖ + 16 * ‖Q‖ * (512 * (‖εA‖ + ‖εC‖)) := by
              have hsecond :
                  16 * ‖Q‖ * ‖A ^ 4 * C ^ 4 - A₀ ^ 4 * C₀ ^ 4‖
                    ≤ 16 * ‖Q‖ * (512 * (‖εA‖ + ‖εC‖)) := by
                exact mul_le_mul_of_nonneg_left hprod (by positivity)
              exact add_le_add hBdiff hsecond
  convert hmain using 1
  ring

private lemma normalizedKleinJ_N_norm_le_512
    {Q εA εB εC : ℂ}
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    ‖B ^ 8 - 16 * Q * A ^ 4 * C ^ 4‖ ≤ (512 : ℝ) := by
  intro A B C
  have hfac := normalizedKleinJ_error_model_factor_norms_lt_two hQ hεA hεB hεC
  change ‖A‖ < (2 : ℝ) ∧ ‖B‖ < (2 : ℝ) ∧ ‖C‖ < (2 : ℝ) at hfac
  obtain ⟨hA2, hB2, hC2⟩ := hfac
  have hB8 : ‖B ^ 8‖ ≤ (256 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hB2.le 8).trans (by norm_num)
  have hA4 : ‖A ^ 4‖ ≤ (16 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hA2.le 4).trans (by norm_num)
  have hC4 : ‖C ^ 4‖ ≤ (16 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hC2.le 4).trans (by norm_num)
  calc
    ‖B ^ 8 - 16 * Q * A ^ 4 * C ^ 4‖
        ≤ ‖B ^ 8‖ + 16 * ‖Q‖ * ‖A ^ 4‖ * ‖C ^ 4‖ := by
          have h := norm_add_le (B ^ 8) (-(16 * Q * A ^ 4 * C ^ 4))
          rw [norm_neg, norm_mul, norm_mul, norm_mul] at h
          norm_num at h
          simpa [sub_eq_add_neg] using h
    _ ≤ 256 + 16 * ((1 / 2 : ℝ) ^ 18) * 16 * 16 := by
          exact add_le_add hB8
            (mul_le_mul (mul_le_mul (mul_le_mul (by norm_num : (16 : ℝ) ≤ 16) hQ.le
              (norm_nonneg _) (by norm_num)) hA4 (by positivity) (by positivity))
              hC4 (norm_nonneg _) (by positivity))
    _ ≤ (512 : ℝ) := by norm_num

private lemma normalizedKleinJ_M_perturb_bound
    {Q εA εB εC : ℂ}
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    let A₀ : ℂ := 1 + Q ^ 2
    let B₀ : ℂ := 1 + 2 * Q + 2 * Q ^ 4
    let C₀ : ℂ := 1 - 2 * Q + 2 * Q ^ 4
    ‖A ^ 8 * C ^ 8 * B ^ 8 - A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8‖
      ≤ 67108864 * (‖εA‖ + ‖εB‖ + ‖εC‖) := by
  intro A B C A₀ B₀ C₀
  have hfac := normalizedKleinJ_error_model_factor_norms_lt_two hQ hεA hεB hεC
  change ‖A‖ < (2 : ℝ) ∧ ‖B‖ < (2 : ℝ) ∧ ‖C‖ < (2 : ℝ) at hfac
  obtain ⟨hA2, hB2, hC2⟩ := hfac
  have hzeroA : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 100 := by norm_num
  have hzeroB : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 150 := by norm_num
  have hzeroC : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 150 := by norm_num
  have hfac0 := normalizedKleinJ_error_model_factor_norms_lt_two
    (Q := Q) (εA := 0) (εB := 0) (εC := 0) hQ hzeroA hzeroB hzeroC
  have hfac0' : ‖A₀‖ < (2 : ℝ) ∧ ‖B₀‖ < (2 : ℝ) ∧ ‖C₀‖ < (2 : ℝ) := by
    simpa [A₀, B₀, C₀] using hfac0
  obtain ⟨hA02, hB02, hC02⟩ := hfac0'
  have hAdiff8 : ‖A ^ 8 - A₀ ^ 8‖ ≤ 1024 * ‖εA‖ := by
    have h := norm_pow_eight_sub_pow_eight_le_of_norm_lt_two hA2 hA02
    have hsub : A - A₀ = εA := by
      dsimp [A, A₀]
      ring
    simpa [hsub] using h
  have hBdiff8 : ‖B ^ 8 - B₀ ^ 8‖ ≤ 1024 * ‖εB‖ := by
    have h := norm_pow_eight_sub_pow_eight_le_of_norm_lt_two hB2 hB02
    have hsub : B - B₀ = εB := by
      dsimp [B, B₀]
      ring
    simpa [hsub] using h
  have hCdiff8 : ‖C ^ 8 - C₀ ^ 8‖ ≤ 1024 * ‖εC‖ := by
    have h := norm_pow_eight_sub_pow_eight_le_of_norm_lt_two hC2 hC02
    have hsub : C - C₀ = εC := by
      dsimp [C, C₀]
      ring
    simpa [hsub] using h
  have hA08 : ‖A₀ ^ 8‖ ≤ (256 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hA02.le 8).trans (by norm_num)
  have hC8 : ‖C ^ 8‖ ≤ (256 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hC2.le 8).trans (by norm_num)
  have hC08 : ‖C₀ ^ 8‖ ≤ (256 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hC02.le 8).trans (by norm_num)
  have hB8 : ‖B ^ 8‖ ≤ (256 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hB2.le 8).trans (by norm_num)
  have hB08 : ‖B₀ ^ 8‖ ≤ (256 : ℝ) := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hB02.le 8).trans (by norm_num)
  have hsplit :
      A ^ 8 * C ^ 8 * B ^ 8 - A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8 =
        (A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8 +
          A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8 +
            A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8) := by
    have haux (X Y Z X₀ Y₀ Z₀ : ℂ) :
        X * Y * Z - X₀ * Y₀ * Z₀ =
          (X - X₀) * Y * Z + X₀ * (Y - Y₀) * Z + X₀ * Y₀ * (Z - Z₀) := by
      ring
    exact haux (A ^ 8) (C ^ 8) (B ^ 8) (A₀ ^ 8) (C₀ ^ 8) (B₀ ^ 8)
  calc
    ‖A ^ 8 * C ^ 8 * B ^ 8 - A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8‖
        = ‖(A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8 +
          A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8 +
            A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8)‖ := by rw [hsplit]
    _ ≤ ‖(A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8‖ +
          ‖A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8‖ +
            ‖A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8)‖ := by
          calc
            ‖(A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8 +
              A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8 +
                A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8)‖
              ≤ ‖(A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8 +
                  A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8‖ +
                    ‖A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8)‖ := norm_add_le _ _
            _ ≤ (‖(A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8‖ +
                  ‖A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8‖) +
                    ‖A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8)‖ := by
                  gcongr
                  exact norm_add_le _ _
            _ = ‖(A ^ 8 - A₀ ^ 8) * C ^ 8 * B ^ 8‖ +
                  ‖A₀ ^ 8 * (C ^ 8 - C₀ ^ 8) * B ^ 8‖ +
                    ‖A₀ ^ 8 * C₀ ^ 8 * (B ^ 8 - B₀ ^ 8)‖ := by ring
    _ ≤ (1024 * ‖εA‖) * 256 * 256 +
          256 * (1024 * ‖εC‖) * 256 +
            256 * 256 * (1024 * ‖εB‖) := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
          exact add_le_add
            (add_le_add
              (mul_le_mul (mul_le_mul hAdiff8 hC8 (norm_nonneg _) (by positivity))
                hB8 (norm_nonneg _) (by positivity))
              (mul_le_mul (mul_le_mul hA08 hCdiff8 (norm_nonneg _) (by positivity))
                hB8 (norm_nonneg _) (by positivity)))
            (mul_le_mul (mul_le_mul hA08 hC08 (by positivity) (by positivity))
              hBdiff8 (norm_nonneg _) (by positivity))
    _ ≤ 67108864 * (‖εA‖ + ‖εB‖ + ‖εC‖) := by
          linarith [norm_nonneg εA, norm_nonneg εB, norm_nonneg εC]

private lemma normalizedKleinJ_error_factor_norm_le_two {Q : ℂ}
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18) :
    ‖(1 : ℂ) + 744 * Q ^ 2‖ ≤ (2 : ℝ) := by
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQ2 : ‖Q‖ ^ 2 < ((1 / 2 : ℝ) ^ 18) ^ 2 :=
    pow_lt_pow_left₀ hQ hQ_nonneg (show (2 : ℕ) ≠ 0 by norm_num)
  calc
    ‖(1 : ℂ) + 744 * Q ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖744 * Q ^ 2‖ := norm_add_le _ _
    _ = 1 + 744 * ‖Q‖ ^ 2 := by
          rw [norm_mul, norm_pow]
          norm_num
    _ ≤ 2 := by
          have hsmall : 744 * ((1 / 2 : ℝ) ^ 18) ^ 2 < 1 := by norm_num
          linarith

/-- The ε-perturbation effect on the full numerator expression is negligible.

When A = A₀+εA, B = B₀+εB, C = C₀+εC with |εA| < 2⁻¹⁰⁰ and
|εB|, |εC| < 2⁻¹⁵⁰, the Lipschitz-type change in the degree-24 polynomial
expression is bounded by (1/1024)·‖Q‖², negligible vs the ideal term. -/
private lemma epsilon_perturbation_numerator_bound
    {Q εA εB εC : ℂ}
    (hQlb : (1 / 2 : ℝ) ^ 30 < ‖Q‖)
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A₀ : ℂ := 1 + Q ^ 2
    let B₀ : ℂ := 1 + 2 * Q + 2 * Q ^ 4
    let C₀ : ℂ := 1 - 2 * Q + 2 * Q ^ 4
    let A : ℂ := A₀ + εA
    let B : ℂ := B₀ + εB
    let C : ℂ := C₀ + εC
    ‖((B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8) -
      ((B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8)‖ <
      (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := by
  intro A₀ B₀ C₀ A B C
  set N : ℂ := B ^ 8 - 16 * Q * A ^ 4 * C ^ 4
  set N₀ : ℂ := B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4
  set M : ℂ := A ^ 8 * C ^ 8 * B ^ 8
  set M₀ : ℂ := A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8
  set K : ℂ := 1 + 744 * Q ^ 2
  have hNdiff :
      ‖N - N₀‖ ≤ 1024 * ‖εB‖ + 8192 * ‖Q‖ * (‖εA‖ + ‖εC‖) := by
    simpa [N, N₀, A, B, C, A₀, B₀, C₀] using
      normalizedKleinJ_N_perturb_bound hQ hεA hεB hεC
  have hMdiff :
      ‖M - M₀‖ ≤ 67108864 * (‖εA‖ + ‖εB‖ + ‖εC‖) := by
    simpa [M, M₀, A, B, C, A₀, B₀, C₀] using
      normalizedKleinJ_M_perturb_bound hQ hεA hεB hεC
  have hNle : ‖N‖ ≤ (512 : ℝ) := by
    simpa [N, A, B, C] using normalizedKleinJ_N_norm_le_512 hQ hεA hεB hεC
  have hzeroA : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 100 := by norm_num
  have hzeroB : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 150 := by norm_num
  have hzeroC : ‖(0 : ℂ)‖ < (1 / 2 : ℝ) ^ 150 := by norm_num
  have hN0le : ‖N₀‖ ≤ (512 : ℝ) := by
    simpa [N₀, A₀, B₀, C₀] using
      normalizedKleinJ_N_norm_le_512 (Q := Q) (εA := 0) (εB := 0) (εC := 0)
        hQ hzeroA hzeroB hzeroC
  have hcube :
      ‖N ^ 3 - N₀ ^ 3‖ ≤ 3 * (512 : ℝ) ^ 2 * ‖N - N₀‖ :=
    norm_cube_sub_cube_le_of_norm_le (by norm_num) hNle hN0le
  have hK : ‖K‖ ≤ (2 : ℝ) := by
    simpa [K] using normalizedKleinJ_error_factor_norm_le_two hQ
  have hsumAC : ‖εA‖ + ‖εC‖ < (1 / 2 : ℝ) ^ 99 := by
    have hsmall : (1 / 2 : ℝ) ^ 100 + (1 / 2 : ℝ) ^ 150 < (1 / 2 : ℝ) ^ 99 := by
      norm_num
    linarith
  have hQsumAC : ‖Q‖ * (‖εA‖ + ‖εC‖) <
      (1 / 2 : ℝ) ^ 117 := by
    have hmul := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hQ hsumAC.le
      (norm_nonneg Q) (by positivity : (0 : ℝ) < (1 / 2) ^ 99)
    convert hmul using 1
    norm_num [pow_add]
  have hNdiff_small : ‖N - N₀‖ < (1 / 2 : ℝ) ^ 100 := by
    calc
      ‖N - N₀‖ ≤ 1024 * ‖εB‖ + 8192 * ‖Q‖ * (‖εA‖ + ‖εC‖) := hNdiff
      _ < 1024 * (1 / 2 : ℝ) ^ 150 + 8192 * (1 / 2 : ℝ) ^ 117 := by
            linarith
      _ < (1 / 2 : ℝ) ^ 100 := by norm_num
  have hcube_small : ‖N ^ 3 - N₀ ^ 3‖ < (1 / 2 : ℝ) ^ 80 := by
    calc
      ‖N ^ 3 - N₀ ^ 3‖ ≤ 3 * (512 : ℝ) ^ 2 * ‖N - N₀‖ := hcube
      _ < 3 * (512 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 100 := by
            linarith
      _ < (1 / 2 : ℝ) ^ 80 := by norm_num
  have hsumABC : ‖εA‖ + ‖εB‖ + ‖εC‖ < (1 / 2 : ℝ) ^ 99 := by
    have hsmall :
        (1 / 2 : ℝ) ^ 100 + (1 / 2 : ℝ) ^ 150 + (1 / 2 : ℝ) ^ 150 <
          (1 / 2 : ℝ) ^ 99 := by norm_num
    linarith
  have hMdiff_small : ‖M - M₀‖ < (1 / 2 : ℝ) ^ 73 := by
    calc
      ‖M - M₀‖ ≤ 67108864 * (‖εA‖ + ‖εB‖ + ‖εC‖) := hMdiff
      _ < 67108864 * (1 / 2 : ℝ) ^ 99 := by linarith
      _ = (1 / 2 : ℝ) ^ 73 := by norm_num
  have hKM_small : ‖K * (M - M₀)‖ < (1 / 2 : ℝ) ^ 72 := by
    calc
      ‖K * (M - M₀)‖ = ‖K‖ * ‖M - M₀‖ := by rw [norm_mul]
      _ ≤ 2 * ‖M - M₀‖ := by
            exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ < 2 * (1 / 2 : ℝ) ^ 73 := by
            exact mul_lt_mul_of_pos_left hMdiff_small (by norm_num)
      _ = (1 / 2 : ℝ) ^ 72 := by norm_num
  have hleft_small :
      ‖(N ^ 3 - K * M) - (N₀ ^ 3 - K * M₀)‖ < (1 / 2 : ℝ) ^ 71 := by
    have hsplit : (N ^ 3 - K * M) - (N₀ ^ 3 - K * M₀) =
        (N ^ 3 - N₀ ^ 3) - K * (M - M₀) := by
      have haux (X Y K M M₀ : ℂ) :
          (X - K * M) - (Y - K * M₀) = (X - Y) - K * (M - M₀) := by
        ring
      exact haux (N ^ 3) (N₀ ^ 3) K M M₀
    calc
      ‖(N ^ 3 - K * M) - (N₀ ^ 3 - K * M₀)‖
          = ‖(N ^ 3 - N₀ ^ 3) - K * (M - M₀)‖ := by rw [hsplit]
      _ ≤ ‖N ^ 3 - N₀ ^ 3‖ + ‖K * (M - M₀)‖ := by
            simpa [sub_eq_add_neg] using norm_add_le (N ^ 3 - N₀ ^ 3) (-(K * (M - M₀)))
      _ < (1 / 2 : ℝ) ^ 80 + (1 / 2 : ℝ) ^ 72 := add_lt_add hcube_small hKM_small
      _ < (1 / 2 : ℝ) ^ 71 := by norm_num
  have hQ2lb : (1 / 2 : ℝ) ^ 60 < ‖Q‖ ^ 2 := by
    have h := pow_lt_pow_left₀ hQlb (by positivity : (0 : ℝ) ≤ (1 / 2) ^ 30)
      (show (2 : ℕ) ≠ 0 by norm_num)
    convert h using 1
    norm_num [pow_mul]
  have hrhs : (1 / 2 : ℝ) ^ 71 < (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := by
    calc
      (1 / 2 : ℝ) ^ 71 < (1 / 1024 : ℝ) * (1 / 2 : ℝ) ^ 60 := by norm_num
      _ < (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := by
            exact mul_lt_mul_of_pos_left hQ2lb (by norm_num)
  calc
    ‖((B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8) -
      ((B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8)‖
        = ‖(N ^ 3 - K * M) - (N₀ ^ 3 - K * M₀)‖ := by
          congr 1
          simp [N, N₀, M, M₀, K, mul_assoc]
    _ < (1 / 2 : ℝ) ^ 71 := hleft_small
    _ < (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := hrhs

/-- Numerator bound for the principal-part estimate.

Combines the ideal (ε=0) bound from `ideal_numerator_eq_Q4_factor` with the
perturbation bound from `epsilon_perturbation_numerator_bound` via triangle
inequality, then shows the sum is less than `(1/4)·‖Q‖²·‖A‖⁸·‖C‖⁸·‖B‖⁸`
using `‖Q‖² < 2⁻³⁶` and `‖A‖⁸·‖C‖⁸·‖B‖⁸ > (7/8)²⁴`. -/
private lemma normalizedKleinJ_error_numerator_bound
    {Q εA εB εC : ℂ}
    (hQ0 : Q ≠ 0)
    (hQlb : (1 / 2 : ℝ) ^ 30 < ‖Q‖)
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8‖ <
      (1 / 4 : ℝ) * (‖Q‖ ^ 2 * ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8) := by
  intro A B C
  set A₀ : ℂ := 1 + Q ^ 2
  set B₀ : ℂ := 1 + 2 * Q + 2 * Q ^ 4
  set C₀ : ℂ := 1 - 2 * Q + 2 * Q ^ 4
  have hA_eq : A = A₀ + εA := by dsimp [A, A₀]
  have hB_eq : B = B₀ + εB := by dsimp [B, B₀]
  have hC_eq : C = C₀ + εC := by dsimp [C, C₀]
  set numFull := (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
      (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8
  set numIdeal := (B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4) ^ 3 -
      (1 + 744 * Q ^ 2) * A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8
  have htri : ‖numFull‖ ≤ ‖numIdeal‖ + ‖numFull - numIdeal‖ := by
    calc
      ‖numFull‖ = ‖numIdeal + (numFull - numIdeal)‖ := by ring_nf
      _ ≤ ‖numIdeal‖ + ‖numFull - numIdeal‖ := norm_add_le _ _
  obtain ⟨P, hP_eq, hP_bound⟩ := ideal_numerator_eq_Q4_factor Q hQ
  have hideal_norm : ‖numIdeal‖ ≤ (2000000 : ℝ) * ‖Q‖ ^ 4 := by
    have hni : numIdeal = Q ^ 4 * P := by
      simpa [numIdeal, A₀, B₀, C₀, mul_assoc] using hP_eq
    rw [hni, norm_mul, norm_pow]
    calc
      ‖Q‖ ^ 4 * ‖P‖ ≤ ‖Q‖ ^ 4 * 2000000 :=
        mul_le_mul_of_nonneg_left hP_bound (by positivity)
      _ = 2000000 * ‖Q‖ ^ 4 := by ring
  have hperturb := epsilon_perturbation_numerator_bound hQlb hQ hεA hεB hεC (Q := Q)
  have hperturb' : ‖numFull - numIdeal‖ < (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := by
    have hconv : numFull - numIdeal =
        ((B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
          (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8) -
        ((B₀ ^ 8 - 16 * Q * A₀ ^ 4 * C₀ ^ 4) ^ 3 -
          (1 + 744 * Q ^ 2) * A₀ ^ 8 * C₀ ^ 8 * B₀ ^ 8) := by
      dsimp [numFull, numIdeal]
    rw [hconv]
    simpa [hA_eq, hB_eq, hC_eq] using hperturb
  have hnum_total :
      ‖numFull‖ < (2000000 : ℝ) * ‖Q‖ ^ 4 +
        (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := by
    calc
      ‖numFull‖ ≤ ‖numIdeal‖ + ‖numFull - numIdeal‖ := htri
      _ < (2000000 : ℝ) * ‖Q‖ ^ 4 +
            (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := by linarith [hideal_norm, hperturb']
  have hQ_nonneg : 0 ≤ ‖Q‖ := norm_nonneg _
  have hQpos : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
  have hQ2pos : 0 < ‖Q‖ ^ 2 := pow_pos hQpos _
  have hQ2_bound : ‖Q‖ ^ 2 < (1 / 2 : ℝ) ^ 36 := by
    have := pow_lt_pow_left₀ hQ hQ_nonneg (show (2 : ℕ) ≠ 0 by norm_num)
    convert this using 1
    norm_num [pow_mul]
  have hBclose : ‖B - 1‖ < (1 / 8 : ℝ) := by
    calc
      ‖B - 1‖ = ‖(2 : ℂ) * Q + 2 * Q ^ 4 + εB‖ := by
        dsimp [B]
        congr 1
        ring
      _ ≤ ‖(2 : ℂ) * Q + 2 * Q ^ 4‖ + ‖εB‖ := norm_add_le _ _
      _ ≤ (‖(2 : ℂ) * Q‖ + ‖2 * Q ^ 4‖) + ‖εB‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (2 * ‖Q‖ + 2 * ‖Q‖ ^ 4) + ‖εB‖ := by
        rw [norm_mul, norm_mul, norm_pow]
        norm_num
      _ < (1 / 8 : ℝ) := by
        nlinarith [hQ, hεB,
          show (2 * ((1/2:ℝ)^18) + 2*((1/2:ℝ)^18)^4) +
            (1/2:ℝ)^150 < 1/8 from by norm_num]
  have hCclose : ‖C - 1‖ < (1 / 8 : ℝ) := by
    calc
      ‖C - 1‖ = ‖-(2 * Q) + 2 * Q ^ 4 + εC‖ := by
        dsimp [C]
        congr 1
        ring
      _ ≤ ‖-(2 * Q) + 2 * Q ^ 4‖ + ‖εC‖ := norm_add_le _ _
      _ ≤ (‖-(2 * Q)‖ + ‖2 * Q ^ 4‖) + ‖εC‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (2 * ‖Q‖ + 2 * ‖Q‖ ^ 4) + ‖εC‖ := by
        rw [norm_neg, norm_mul, norm_mul, norm_pow]
        norm_num
      _ < (1 / 8 : ℝ) := by
        nlinarith [hQ, hεC,
          show (2 * ((1/2:ℝ)^18) + 2*((1/2:ℝ)^18)^4) +
            (1/2:ℝ)^150 < 1/8 from by norm_num]
  have hAclose : ‖A - 1‖ < (1 / 8 : ℝ) := by
    calc
      ‖A - 1‖ = ‖Q ^ 2 + εA‖ := by
        dsimp [A]
        congr 1
        ring
      _ ≤ ‖Q ^ 2‖ + ‖εA‖ := norm_add_le _ _
      _ = ‖Q‖ ^ 2 + ‖εA‖ := by rw [norm_pow]
      _ < (1 / 8 : ℝ) := by
        linarith [hQ, hεA,
          show ((1/2:ℝ)^18)^2 + (1/2:ℝ)^100 < 1/8 from by norm_num]
  have hA78 : (7 / 8 : ℝ) < ‖A‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖A‖ + ‖A - 1‖ := by
      calc
        ‖(1 : ℂ)‖ = ‖A + (1 - A)‖ := by ring_nf
        _ ≤ ‖A‖ + ‖1 - A‖ := norm_add_le _ _
        _ = ‖A‖ + ‖A - 1‖ := by rw [show 1 - A = -(A - 1) by ring, norm_neg]
    norm_num at h1
    linarith
  have hB78 : (7 / 8 : ℝ) < ‖B‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖B‖ + ‖B - 1‖ := by
      calc
        ‖(1 : ℂ)‖ = ‖B + (1 - B)‖ := by ring_nf
        _ ≤ ‖B‖ + ‖1 - B‖ := norm_add_le _ _
        _ = ‖B‖ + ‖B - 1‖ := by rw [show 1 - B = -(B - 1) by ring, norm_neg]
    norm_num at h1
    linarith
  have hC78 : (7 / 8 : ℝ) < ‖C‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖C‖ + ‖C - 1‖ := by
      calc
        ‖(1 : ℂ)‖ = ‖C + (1 - C)‖ := by ring_nf
        _ ≤ ‖C‖ + ‖1 - C‖ := norm_add_le _ _
        _ = ‖C‖ + ‖C - 1‖ := by rw [show 1 - C = -(C - 1) by ring, norm_neg]
    norm_num at h1
    linarith
  have hA8_tight : (7 / 8 : ℝ) ^ 8 < ‖A‖ ^ 8 :=
    pow_lt_pow_left₀ hA78 (by norm_num) (by norm_num)
  have hB8_tight : (7 / 8 : ℝ) ^ 8 < ‖B‖ ^ 8 :=
    pow_lt_pow_left₀ hB78 (by norm_num) (by norm_num)
  have hC8_tight : (7 / 8 : ℝ) ^ 8 < ‖C‖ ^ 8 :=
    pow_lt_pow_left₀ hC78 (by norm_num) (by norm_num)
  have hACB_tight : (7 / 8 : ℝ) ^ 24 < ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8 := by
    have hsplit : (7 / 8 : ℝ) ^ 24 =
        (7 / 8 : ℝ) ^ 8 * (7 / 8 : ℝ) ^ 8 * (7 / 8 : ℝ) ^ 8 := by
      norm_num [pow_add]
    rw [hsplit]
    exact mul_lt_mul
      (mul_lt_mul hA8_tight hC8_tight.le (by positivity)
        (lt_trans (by positivity) hA8_tight).le)
      hB8_tight.le (by positivity)
      (mul_pos (lt_trans (by positivity) hA8_tight)
        (lt_trans (by positivity) hC8_tight)).le
  have hscaled :
      (2000000 : ℝ) * ‖Q‖ ^ 2 + (1 / 1024 : ℝ) <
        (1 / 4 : ℝ) * (7 / 8 : ℝ) ^ 24 := by
    calc
      (2000000 : ℝ) * ‖Q‖ ^ 2 + (1 / 1024 : ℝ)
          < 2000000 * (1 / 2 : ℝ) ^ 36 + (1 / 1024 : ℝ) := by
            gcongr
      _ < (1 / 4 : ℝ) * (7 / 8 : ℝ) ^ 24 := by norm_num
  calc
    ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8‖
        = ‖numFull‖ := by dsimp [numFull]
    _ < (2000000 : ℝ) * ‖Q‖ ^ 4 + (1 / 1024 : ℝ) * ‖Q‖ ^ 2 := hnum_total
    _ = ‖Q‖ ^ 2 * ((2000000 : ℝ) * ‖Q‖ ^ 2 + (1 / 1024 : ℝ)) := by ring
    _ < ‖Q‖ ^ 2 * ((1 / 4 : ℝ) * (7 / 8 : ℝ) ^ 24) :=
          mul_lt_mul_of_pos_left hscaled hQ2pos
    _ < ‖Q‖ ^ 2 * ((1 / 4 : ℝ) * (‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8)) := by
          apply mul_lt_mul_of_pos_left _ hQ2pos
          apply mul_lt_mul_of_pos_left hACB_tight
          norm_num
    _ = (1 / 4 : ℝ) * (‖Q‖ ^ 2 * ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8) := by ring


/-- The remaining finite rational-function estimate behind the half-nome
principal part.

This is independent of theta functions and CM: it is a concrete inequality
for four complex variables under explicit smallness assumptions.
The lower bound on `‖Q‖` is needed because the ε-perturbation divided by Q²
can blow up for Q very close to zero. -/
theorem normalizedKleinJ_error_model_principal_bound
    {Q εA εB εC : ℂ}
    (hQ0 : Q ≠ 0)
    (hQlb : (1 / 2 : ℝ) ^ 30 < ‖Q‖)
    (hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18)
    (hεA : ‖εA‖ < (1 / 2 : ℝ) ^ 100)
    (hεB : ‖εB‖ < (1 / 2 : ℝ) ^ 150)
    (hεC : ‖εC‖ < (1 / 2 : ℝ) ^ 150) :
    let A : ℂ := 1 + Q ^ 2 + εA
    let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
    let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
    ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
          (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) -
        (Q⁻¹ ^ 2 + 744)‖ < (1 / 2 : ℝ) := by
  intro A B C
  -- Establish that A, B, C have norm > 1/2
  have hfac := normalizedKleinJ_error_model_factor_norms_gt_half hQ hεA hεB hεC
  change (1 / 2 : ℝ) < ‖A‖ ∧ (1 / 2 : ℝ) < ‖B‖ ∧ (1 / 2 : ℝ) < ‖C‖ at hfac
  obtain ⟨hAnorm, hBnorm, hCnorm⟩ := hfac
  -- The denominator is nonzero
  have hA_ne : A ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num : (0:ℝ) < 1/2) hAnorm)
  have hB_ne : B ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num : (0:ℝ) < 1/2) hBnorm)
  have hC_ne : C ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num : (0:ℝ) < 1/2) hCnorm)
  have hQ2_ne : Q ^ 2 ≠ 0 := pow_ne_zero _ hQ0
  have hden_ne : Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hQ2_ne (pow_ne_zero _ hA_ne))
      (pow_ne_zero _ hC_ne)) (pow_ne_zero _ hB_ne)
  -- Rewrite the difference as a single fraction
  have hkey : (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
        (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) - (Q⁻¹ ^ 2 + 744) =
      ((B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
        (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8) /
      (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) := by
    have h := hden_ne
    field_simp
  rw [hkey]
  rw [norm_div]
  -- Use the denominator lower bound
  have hden_lower := normalizedKleinJ_error_model_den_norm_lower hQ0 hQ hεA hεB hεC
  change (1 / 2 : ℝ) ^ 24 * ‖Q‖ ^ 2 < ‖Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8‖ at hden_lower
  have hden_pos : 0 < ‖Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8‖ :=
    lt_trans (by positivity) hden_lower
  rw [div_lt_iff₀ hden_pos]
  -- Use the numerator bound
  have hnum := normalizedKleinJ_error_numerator_bound hQ0 hQlb hQ hεA hεB hεC
  change ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
      (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8‖ <
    (1 / 4 : ℝ) * (‖Q‖ ^ 2 * ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8) at hnum
  -- Now we need: ‖numerator‖ < (1/2) * ‖denominator‖
  -- We have: ‖numerator‖ < (1/4) * (‖Q‖² * ‖A‖⁸ * ‖C‖⁸ * ‖B‖⁸)
  -- And: ‖denominator‖ = ‖Q²A⁸C⁸B⁸‖ = ‖Q‖² * ‖A‖⁸ * ‖C‖⁸ * ‖B‖⁸
  have hden_eq : ‖Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8‖ =
      ‖Q‖ ^ 2 * ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8 := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
  calc ‖(B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 -
          (1 + 744 * Q ^ 2) * A ^ 8 * C ^ 8 * B ^ 8‖
      < (1 / 4 : ℝ) * (‖Q‖ ^ 2 * ‖A‖ ^ 8 * ‖C‖ ^ 8 * ‖B‖ ^ 8) := hnum
    _ ≤ (1 / 2 : ℝ) * ‖Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8‖ := by
        rw [hden_eq]
        linarith [mul_pos (show (0:ℝ) < ‖Q‖ ^ 2 from pow_pos (norm_pos_iff.mpr hQ0) _)
          (mul_pos (pow_pos (lt_trans (by norm_num : (0:ℝ) < 1/2) hAnorm) 8)
            (mul_pos (pow_pos (lt_trans (by norm_num : (0:ℝ) < 1/2) hCnorm) 8)
              (pow_pos (lt_trans (by norm_num : (0:ℝ) < 1/2) hBnorm) 8)))]

/-- Finite, explicit error estimate for the normalized half-nome model.

At this point all analytic theta-series tails have already been bounded
above.  What remains is a deterministic rational-function stability estimate
with
`|Q| < 2⁻¹⁸`, `|εA| < 2⁻¹⁰⁰`, and
`|εB|, |εC| < 2⁻¹⁵⁰`, using
`kleinJThetaExpression_heegnerTau163_error_model`. -/
theorem kleinJThetaExpression_heegnerTau163_half_nome_principal_bound :
    let τ : ℂ := heegnerTau163
    let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
    ‖kleinJThetaExpression τ - (Q⁻¹ ^ 2 + 744)‖ < (1 / 2 : ℝ) := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  have herr :
      ∃ εA εB εC : ℂ,
        ‖εA‖ < (1 / 2 : ℝ) ^ 100 ∧
        ‖εB‖ < (1 / 2 : ℝ) ^ 150 ∧
        ‖εC‖ < (1 / 2 : ℝ) ^ 150 ∧
        kleinJThetaExpression τ =
          let A : ℂ := 1 + Q ^ 2 + εA
          let B : ℂ := 1 + 2 * Q + 2 * Q ^ 4 + εB
          let C : ℂ := 1 - 2 * Q + 2 * Q ^ 4 + εC
          (B ^ 8 - 16 * Q * A ^ 4 * C ^ 4) ^ 3 /
            (Q ^ 2 * A ^ 8 * C ^ 8 * B ^ 8) := by
    simpa [τ, Q] using kleinJThetaExpression_heegnerTau163_error_model
  rcases herr with ⟨εA, εB, εC, hεA, hεB, hεC, hmodel⟩
  change ‖kleinJThetaExpression τ - (Q⁻¹ ^ 2 + 744)‖ < (1 / 2 : ℝ)
  rw [hmodel]
  have hQ0 : Q ≠ 0 := Complex.exp_ne_zero _
  have hQlb : (1 / 2 : ℝ) ^ 30 < ‖Q‖ := by
    simpa [τ, Q] using norm_heegnerTau163_half_nome_gt_two_pow_neg_30
  have hQ : ‖Q‖ < (1 / 2 : ℝ) ^ 18 := by
    simpa [τ, Q] using norm_heegnerTau163_half_nome_lt_two_pow_neg_18
  exact normalizedKleinJ_error_model_principal_bound
    hQ0 hQlb hQ hεA hεB hεC

/-- The theta-expression q-expansion through constant term:
`J_θ(τ₁₆₃) = q⁻¹ + 744 + O(q)`.

This is the remaining analytic series-manipulation part of the numerical
branch.  The already-proved theta tail bounds above give the small parameter
`|q| < 2⁻³⁶`; the missing work is the finite algebraic expansion of the
rational theta expression and the geometric bound for the remainder. -/
theorem kleinJThetaExpression_heegnerTau163_principal_bound :
    ‖kleinJThetaExpression (heegnerTau163 : ℂ) -
        ((Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ + 744)‖ <
      (1 / 2 : ℝ) := by
  let τ : ℂ := heegnerTau163
  let Q : ℂ := Complex.exp (Real.pi * Complex.I * τ)
  rw [show ((Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ + 744) =
      Q⁻¹ ^ 2 + 744 by
    simpa [τ, Q] using heegnerTau163_principal_part_eq_half_nome]
  simpa [τ, Q] using kleinJThetaExpression_heegnerTau163_half_nome_principal_bound

private lemma sqrt163_gt_d20 :
    (12.76714533480370466170 : ℝ) < Real.sqrt 163 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 12.76714533480370466170)]
  norm_num

private lemma sqrt163_lt_d20 :
    Real.sqrt 163 < (12.76714533480370466172 : ℝ) := by
  rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 163)
    (by norm_num : (0 : ℝ) ≤ (12.76714533480370466172 : ℝ))]
  norm_num

private lemma pi_mul_sqrt163_gt_d20 :
    (40.109169991132519755 : ℝ) < Real.pi * Real.sqrt 163 := by
  have hpi := Real.pi_gt_d20
  have hs := sqrt163_gt_d20
  have hprod :
      (3.14159265358979323846 : ℝ) * (12.76714533480370466170 : ℝ) <
        Real.pi * Real.sqrt 163 := by
    exact mul_lt_mul hpi hs.le (by norm_num) Real.pi_pos.le
  norm_num at hprod ⊢
  linarith

private lemma pi_mul_sqrt163_lt_d20 :
    Real.pi * Real.sqrt 163 < (40.109169991132519756 : ℝ) := by
  have hpi := Real.pi_lt_d20
  have hs := sqrt163_lt_d20
  have hprod :
      Real.pi * Real.sqrt 163 <
        (3.14159265358979323847 : ℝ) * (12.76714533480370466172 : ℝ) := by
    exact mul_lt_mul hpi hs.le
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 163)) (by norm_num)
  norm_num at hprod ⊢
  linarith

private lemma exp_frac_lower_chudnovsky :
    (1.1153519341656537 : ℝ) <
      Real.exp (0.109169991132519755 : ℝ) := by
  have h := Real.exp_bound (x := (0.109169991132519755 : ℝ)) (n := 20)
    (by norm_num : |(0.109169991132519755 : ℝ)| ≤ 1) (by norm_num : 0 < 20)
  have hle := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ] at hle ⊢
  linarith

private lemma exp_frac_upper_chudnovsky :
    Real.exp (0.109169991132519756 : ℝ) <
      (1.115351934165653702 : ℝ) := by
  have h := Real.exp_bound (x := (0.109169991132519756 : ℝ)) (n := 20)
    (by norm_num : |(0.109169991132519756 : ℝ)| ≤ 1) (by norm_num : 0 < 20)
  have hle := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ] at hle ⊢
  linarith

private lemma exp_one_lower_chudnovsky :
    (2.71828182845904523534 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_near_20
  have hle := (abs_sub_le_iff.mp h).2
  norm_num at hle ⊢
  linarith

private lemma exp_one_upper_chudnovsky :
    Real.exp 1 < (2.71828182845904523537 : ℝ) := by
  have h := Real.exp_one_near_20
  have hle := (abs_sub_le_iff.mp h).1
  norm_num at hle ⊢
  linarith

/-- The real near-integer estimate behind the Chudnovsky miracle:
`exp(π sqrt 163)` is within `1/2` of `640320³ + 744`.

This is now isolated as a pure real-analytic numerical certificate.  A full
proof should use the high-precision `π` bounds, rational square-root bounds
for `sqrt 163`, and a certified exponential Taylor interval. -/
theorem exp_pi_sqrt163_near_chudnovsky_interval :
    |(640320 : ℝ) ^ 3 + 744 -
        Real.exp (Real.pi * Real.sqrt 163)| < (1 / 2 : ℝ) := by
  have hxl := pi_mul_sqrt163_gt_d20
  have hxu := pi_mul_sqrt163_lt_d20
  have he1l := exp_one_lower_chudnovsky
  have he1u := exp_one_upper_chudnovsky
  have hfl := exp_frac_lower_chudnovsky
  have hfu := exp_frac_upper_chudnovsky
  have hLowerProd :
      (640320 : ℝ) ^ 3 + 744 - (1 / 2 : ℝ) <
        (2.71828182845904523534 : ℝ) ^ 40 *
          (1.1153519341656537 : ℝ) := by
    norm_num
  have hUpperProd :
      (2.71828182845904523537 : ℝ) ^ 40 *
          (1.115351934165653702 : ℝ) <
        (640320 : ℝ) ^ 3 + 744 + (1 / 2 : ℝ) := by
    norm_num
  have hExpLowerFactor :
      (2.71828182845904523534 : ℝ) ^ 40 *
          (1.1153519341656537 : ℝ) <
        (Real.exp 1) ^ 40 * Real.exp (0.109169991132519755 : ℝ) := by
    exact mul_lt_mul
      (pow_lt_pow_left₀ he1l (by norm_num) (by norm_num : 40 ≠ 0))
      hfl.le (by norm_num) (by positivity)
  have hExpUpperFactor :
      (Real.exp 1) ^ 40 * Real.exp (0.109169991132519756 : ℝ) <
        (2.71828182845904523537 : ℝ) ^ 40 *
          (1.115351934165653702 : ℝ) := by
    exact mul_lt_mul
      (pow_lt_pow_left₀ he1u (Real.exp_pos 1).le (by norm_num : 40 ≠ 0))
      hfu.le (Real.exp_pos _) (by positivity)
  have hExpLowerExact :
      (Real.exp 1) ^ 40 * Real.exp (0.109169991132519755 : ℝ) =
        Real.exp (40.109169991132519755 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have hExpUpperExact :
      (Real.exp 1) ^ 40 * Real.exp (0.109169991132519756 : ℝ) =
        Real.exp (40.109169991132519756 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have hLower :
      (640320 : ℝ) ^ 3 + 744 - (1 / 2 : ℝ) <
        Real.exp (Real.pi * Real.sqrt 163) := by
    calc
      (640320 : ℝ) ^ 3 + 744 - (1 / 2 : ℝ) <
          (2.71828182845904523534 : ℝ) ^ 40 *
            (1.1153519341656537 : ℝ) := hLowerProd
      _ < (Real.exp 1) ^ 40 *
            Real.exp (0.109169991132519755 : ℝ) := hExpLowerFactor
      _ = Real.exp (40.109169991132519755 : ℝ) := hExpLowerExact
      _ < Real.exp (Real.pi * Real.sqrt 163) := Real.exp_lt_exp.mpr hxl
  have hUpper :
      Real.exp (Real.pi * Real.sqrt 163) <
        (640320 : ℝ) ^ 3 + 744 + (1 / 2 : ℝ) := by
    calc
      Real.exp (Real.pi * Real.sqrt 163) <
          Real.exp (40.109169991132519756 : ℝ) := Real.exp_lt_exp.mpr hxu
      _ = (Real.exp 1) ^ 40 *
            Real.exp (0.109169991132519756 : ℝ) := hExpUpperExact.symm
      _ < (2.71828182845904523537 : ℝ) ^ 40 *
            (1.115351934165653702 : ℝ) := hExpUpperFactor
      _ < (640320 : ℝ) ^ 3 + 744 + (1 / 2 : ℝ) := hUpperProd
  rw [abs_sub_lt_iff]
  constructor <;> linarith

lemma sqrt163_gt_d6 :
    (12.767145 : ℝ) < Real.sqrt 163 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 12.767145)]
  norm_num

lemma sqrt163_lt_d6 :
    Real.sqrt 163 < (12.767146 : ℝ) := by
  rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 163)
    (by norm_num : (0 : ℝ) ≤ (12.767146 : ℝ))]
  norm_num

lemma pi_mul_sqrt163_gt_d6 :
    (40.10916 : ℝ) < Real.pi * Real.sqrt 163 := by
  have hpi := Real.pi_gt_d20
  have hs := sqrt163_gt_d6
  nlinarith [Real.pi_pos, Real.sqrt_nonneg 163]

lemma pi_mul_sqrt163_lt_d6 :
    Real.pi * Real.sqrt 163 < (40.10918 : ℝ) := by
  have hpi := Real.pi_lt_d20
  have hs := sqrt163_lt_d6
  nlinarith [Real.pi_pos, Real.sqrt_nonneg 163]

lemma exp_pi_sqrt163_between_d6 :
    Real.exp (40.10916 : ℝ) <
        Real.exp (Real.pi * Real.sqrt 163) ∧
      Real.exp (Real.pi * Real.sqrt 163) <
        Real.exp (40.10918 : ℝ) := by
  exact ⟨Real.exp_lt_exp.mpr pi_mul_sqrt163_gt_d6,
    Real.exp_lt_exp.mpr pi_mul_sqrt163_lt_d6⟩

theorem exp_pi_sqrt163_near_chudnovsky_integer :
    ‖(((640320 : ℝ) ^ 3 + 744 -
        Real.exp (Real.pi * Real.sqrt 163)) : ℂ)‖ < (1 / 2 : ℝ) := by
  norm_num
  rw [show ((Real.pi : ℂ) * (Real.sqrt 163 : ℂ)) =
      ((Real.pi * Real.sqrt 163 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_exp]
  norm_cast
  have h := exp_pi_sqrt163_near_chudnovsky_interval
  norm_num at h ⊢
  exact h

/-- The principal part `q⁻¹ + 744` is already within `1/2` of the target. -/
lemma heegnerTau163_principal_part_sub_target_norm_lt_half :
    ‖((Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ + 744) -
        heegnerJ163Target‖ < (1 / 2 : ℝ) := by
  rw [show ((Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ + 744) -
        heegnerJ163Target =
      (Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ +
        744 - heegnerJ163Target by ring]
  rw [heegnerTau163_principal_part_sub_target]
  exact exp_pi_sqrt163_near_chudnovsky_integer

/-- Numerical q-expansion bound placing the theta expression within distance
`< 1` of the target integer. -/
theorem norm_kleinJThetaExpression_heegnerTau163_sub_target_lt_one :
    ‖kleinJThetaExpression (heegnerTau163 : ℂ) - heegnerJ163Target‖ < 1 := by
  let p : ℂ :=
    (Complex.exp (2 * Real.pi * Complex.I * (heegnerTau163 : ℂ)))⁻¹ + 744
  have hsplit :
      kleinJThetaExpression (heegnerTau163 : ℂ) - heegnerJ163Target =
        (kleinJThetaExpression (heegnerTau163 : ℂ) - p) +
          (p - heegnerJ163Target) := by
    dsimp [p]
    ring
  calc
    ‖kleinJThetaExpression (heegnerTau163 : ℂ) - heegnerJ163Target‖
        = ‖(kleinJThetaExpression (heegnerTau163 : ℂ) - p) +
            (p - heegnerJ163Target)‖ := by rw [hsplit]
    _ ≤ ‖kleinJThetaExpression (heegnerTau163 : ℂ) - p‖ +
          ‖p - heegnerJ163Target‖ := norm_add_le _ _
    _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
          exact add_lt_add
            (by
              dsimp [p]
              exact kleinJThetaExpression_heegnerTau163_principal_bound)
            (by
              dsimp [p]
              exact heegnerTau163_principal_part_sub_target_norm_lt_half)
    _ = 1 := by norm_num

-- `delta_slash_action_level_one` is now public in `ModularPolynomialQExpansion.lean`.

/-- `mapGL ℝ` on `SL(2, ℤ)` is definitionally `toGL ∘ map (Int.castRingHom ℝ)`; this
bridges the two spellings so that `𝒮ℒ`-flavoured slash-invariance lemmas rewrite
against the `SL(2, ℤ)`-flavoured goals produced by `ModularForm.SL_slash_apply`. -/
private lemma mapGL_eq_toGL_map (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ) γ =
      Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ) :=
  rfl

/-- The `SL(2, ℤ)` action on `ℍ` is `MulAction.compHom` along `mapGL ℝ`, so the two
spellings of the orbit point agree definitionally. -/
private lemma sl_smul_eq_mapGL_smul (γ : SL(2, ℤ)) (z : ℍ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ) γ • z = γ • z :=
  rfl

private lemma cuspForm_cube_div_delta_slash_action (f : CuspForm 𝒮ℒ 4) (γ : SL(2, ℤ)) :
    (fun z : ℍ => f z ^ 3 / ModularForm.discriminant z) ∣[(0 : ℤ)] γ =
      fun z : ℍ => f z ^ 3 / ModularForm.discriminant z := by
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) f ⟨γ, rfl⟩ z
  rw [sl_smul_eq_mapGL_smul, mapGL_eq_toGL_map] at hf
  have hd := congrFun (delta_slash_action_level_one γ) z
  rw [ModularForm.SL_slash_apply] at hd
  rw [ModularForm.SL_slash_apply, hf]
  have hdne :
      UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
          z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero _ _
  have hdelg : ModularForm.discriminant (γ • z) ≠ 0 := ModularForm.discriminant_ne_zero (γ • z)
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  field_simp [hdne, hdelg, hdel] at hd
  ring_nf at hd
  rw [hd]
  field_simp [hdne, hdel]
  · norm_num

-- `mdiff_delta` is now public in `ModularPolynomialQExpansion.lean`.

private lemma mdiff_cuspForm_cube_div_delta (f : CuspForm 𝒮ℒ 4) :
    MDiff (fun z : ℍ => f z ^ 3 / ModularForm.discriminant z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hf : MDiff (f : ℍ → ℂ) := ModularFormClass.holo f
  have hf' := (UpperHalfPlane.mdifferentiable_iff.mp hf) z hz
  have hd :
      DifferentiableWithinAt ℂ
        (fun x : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex x)) {z | 0 < z.im} z :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdiff_delta) z hz
  have hdn : ModularForm.discriminant (UpperHalfPlane.ofComplex z) ≠ 0 :=
    ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
  exact (hf'.pow 3).div hd hdn

private lemma norm_qParam_eq (z : ℍ) :
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp only [Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]

private lemma norm_tprod_one_sub_sub_one_le {f : ℕ → ℂ}
    (hmult : Multipliable (fun n => 1 + (-f n)))
    (hsum : Summable (fun n => ‖f n‖)) :
    ‖∏' n, (1 - f n) - 1‖ ≤ Real.exp (∑' n, ‖f n‖) - 1 := by
  have heq : (fun n => (1 : ℂ) - f n) = (fun n => 1 + (-f n)) := funext (fun n => by ring)
  rw [heq]
  apply le_of_tendsto' ((continuous_norm.tendsto _).comp
    (hmult.tendsto_prod_tprod_nat.sub tendsto_const_nhds))
  intro N
  calc ‖∏ n ∈ Finset.range N, (1 + (-f n)) - 1‖
      ≤ Real.exp (∑ n ∈ Finset.range N, ‖-f n‖) - 1 :=
        Finset.norm_prod_one_add_sub_one_le _ _
    _ ≤ Real.exp (∑' n, ‖f n‖) - 1 := by
        apply sub_le_sub_right
        apply Real.exp_le_exp_of_le
        simp_rw [norm_neg]
        exact hsum.sum_le_tsum _ (fun _ _ => norm_nonneg _)

private lemma eta_product_norm_eventually_ge :
    ∀ᶠ z : ℍ in UpperHalfPlane.atImInfty,
      (1 / 2 : ℝ) ≤ ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ := by
  refine (UpperHalfPlane.atImInfty_mem _).mpr ⟨1, fun z hz => ?_⟩
  change (1 / 2 : ℝ) ≤ ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖
  have hrq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 := by
    rw [norm_qParam_eq]; exact Real.exp_lt_one_iff.mpr (by nlinarith [z.2, Real.pi_pos])
  have hmult : Multipliable fun n => 1 - ModularForm.eta_q n (z : ℂ) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2
  have hsumm : Summable (fun n => ‖ModularForm.eta_q n (z : ℂ)‖) := by
    simpa [norm_neg] using ModularForm.summable_eta_q z
  have hsum_bound : ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ ≤ 1 / 4 := by
    have : ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ =
        ‖Function.Periodic.qParam 1 (z : ℂ)‖ / (1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖) := by
      simp only [ModularForm.eta_q, norm_pow]
      rw [show (fun n : ℕ => ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ (n + 1)) =
          (fun n => ‖Function.Periodic.qParam 1 (z : ℂ)‖ *
            ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ n)
        from funext (fun n => by ring),
        tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) hrq, div_eq_mul_inv]
    rw [this]
    have hq_le : ‖Function.Periodic.qParam 1 (z : ℂ)‖ ≤ 1 / 5 := by
      rw [norm_qParam_eq]
      calc Real.exp (-2 * Real.pi * z.im)
          ≤ Real.exp (-6) := by
            apply Real.exp_le_exp_of_le
            have := Real.pi_gt_three; nlinarith
        _ ≤ 1 / 5 := by
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
            have h5 : (1 / 5 : ℝ)⁻¹ = 5 := by norm_num
            rw [h5]
            calc (5 : ℝ) ≤ 2 ^ 6 := by norm_num
              _ ≤ Real.exp 1 ^ 6 := by
                  apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
                  linarith [Real.add_one_le_exp (1 : ℝ)]
              _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h1mr : (0 : ℝ) < 1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖ := by linarith
    calc ‖Function.Periodic.qParam 1 (z : ℂ)‖ /
        (1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖)
        ≤ (1 / 5) / (4 / 5) := by
          rw [div_le_div_iff₀ h1mr (by norm_num : (0:ℝ) < 4 / 5)]
          linarith [norm_nonneg (Function.Periodic.qParam 1 (z : ℂ))]
      _ = 1 / 4 := by norm_num
  have hprod_close : ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ)) - 1‖ ≤ 1 / 2 := by
    calc ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ)) - 1‖
        ≤ Real.exp (∑' n, ‖ModularForm.eta_q n (z : ℂ)‖) - 1 :=
          norm_tprod_one_sub_sub_one_le hmult hsumm
      _ ≤ 2 * ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ := by
          set S := ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ with hS_def
          have hS_nn : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
          have hS_le1 : |S| ≤ 1 := by rw [abs_of_nonneg hS_nn]; linarith [hsum_bound]
          have hab := Real.abs_exp_sub_one_le hS_le1
          rw [abs_of_nonneg (by linarith [Real.add_one_le_exp S]),
            abs_of_nonneg hS_nn] at hab
          linarith
      _ ≤ 2 * (1 / 4) := by linarith [hsum_bound]
      _ = 1 / 2 := by norm_num
  have h_tri := abs_norm_sub_norm_le (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) 1
  rw [norm_one] at h_tri
  have h_abs_le : |‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ - 1| ≤ 1 / 2 :=
    h_tri.trans hprod_close
  linarith [(abs_le.mp h_abs_le).1]

private lemma norm_delta_eq (z : ℍ) :
    ‖ModularForm.discriminant z‖ = ‖Function.Periodic.qParam 1 (z : ℂ)‖ *
      ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ ^ 24 := by
  have hmult : Multipliable fun n => 1 - ModularForm.eta_q n (z : ℂ) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2
  rw [ModularForm.discriminant_eq_q_prod, norm_mul, hmult.tprod_pow 24, norm_pow]

-- `delta_norm_lower_bound` is now public in `ModularPolynomialQExpansion.lean`;
-- the duplicate definition has been removed to avoid namespace collision.

private lemma isZeroAtImInfty_cuspFormCubeDivDelta (f : CuspForm 𝒮ℒ 4) :
    UpperHalfPlane.IsZeroAtImInfty (fun z : ℍ => f z ^ 3 / ModularForm.discriminant z) := by
  apply UpperHalfPlane.IsZeroAtImInfty.of_exp_decay
  have hf_decay : ⇑f =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / 1) :=
    CuspFormClass.exp_decay_atImInfty f one_pos
      one_mem_strictPeriods_SL
  simp only [div_one] at hf_decay
  refine ⟨4 * Real.pi, by positivity, ?_⟩
  -- f³ =O exp(-6πτ.im)
  have hf3 : (fun z : ℍ => f z ^ 3) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (-6 * Real.pi * τ.im) := by
    have h := hf_decay.pow 3
    refine h.congr_right fun z => ?_
    rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
  -- Δ⁻¹ =O exp(2πτ.im)
  have hdelta_inv : (fun z : ℍ => (ModularForm.discriminant z)⁻¹) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (2 * Real.pi * τ.im) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(2 : ℝ) ^ 24, ?_⟩
    filter_upwards [delta_norm_lower_bound] with z hz
    rw [norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hpos : 0 < (1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im) := by positivity
    calc ‖ModularForm.discriminant z‖⁻¹
        ≤ ((1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im))⁻¹ :=
          inv_anti₀ hpos hz
      _ = (2 : ℝ) ^ 24 * (Real.exp (-2 * Real.pi * z.im))⁻¹ := by
          have : ((1 / 2 : ℝ) ^ 24)⁻¹ = (2 : ℝ) ^ 24 := by
            rw [one_div, inv_pow, inv_inv]
          rw [mul_inv_rev, mul_comm, this]
      _ = (2 : ℝ) ^ 24 * Real.exp (2 * Real.pi * z.im) := by
          congr 1; rw [← Real.exp_neg]; congr 1; ring
  -- f³/Δ = f³ · Δ⁻¹ =O exp(-6πτ.im) · exp(2πτ.im) = exp(-4πτ.im)
  exact ((hf3.mul hdelta_inv).congr_left (fun z => by simp [div_eq_mul_inv])).congr_right
    fun z => by rw [← Real.exp_add]; congr 1; ring

private lemma bddAtCusp_cuspFormCubeDivDelta (f : CuspForm 𝒮ℒ 4)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (fun z : ℍ => f z ^ 3 / ModularForm.discriminant z) 0 := by
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc]
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc
  exact ⟨γ, hγ.symm, by
    rw [cuspForm_cube_div_delta_slash_action f γ]
    exact (isZeroAtImInfty_cuspFormCubeDivDelta f).isBoundedAtImInfty⟩

private noncomputable def cuspFormCubeDivDeltaMF (f : CuspForm 𝒮ℒ 4) :
    ModularForm 𝒮ℒ 0 where
  toSlashInvariantForm :=
    { toFun := fun z => f z ^ 3 / ModularForm.discriminant z
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        exact cuspForm_cube_div_delta_slash_action f g }
  holo' := mdiff_cuspForm_cube_div_delta f
  bdd_at_cusps' hc := bddAtCusp_cuspFormCubeDivDelta f hc

private lemma cuspFormCubeDivDelta_const (f : CuspForm 𝒮ℒ 4) :
    ∃ c : ℂ, ∀ z : ℍ, f z ^ 3 / ModularForm.discriminant z = c := by
  have ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const (cuspFormCubeDivDeltaMF f)
  exact ⟨c, fun z => congr_fun hc z⟩

private lemma cuspFormCubeDivDelta_eq_zero (f : CuspForm 𝒮ℒ 4) :
    ∀ z : ℍ, f z ^ 3 / ModularForm.discriminant z = 0 := by
  obtain ⟨c, hc⟩ := cuspFormCubeDivDelta_const f
  suffices c = 0 by intro z; rw [hc z, this]
  have hzero := isZeroAtImInfty_cuspFormCubeDivDelta f
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  have htend : Filter.Tendsto (fun _ : ℍ => c) UpperHalfPlane.atImInfty (nhds 0) :=
    hzero.congr (fun z => hc z)
  rwa [tendsto_const_nhds_iff] at htend

private theorem dim_S4_level_one_zero (f : CuspForm 𝒮ℒ 4) : ⇑f = 0 := by
  ext z
  have h := cuspFormCubeDivDelta_eq_zero f z
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rwa [pow_eq_zero_iff (by norm_num : 3 ≠ 0)] at h
  · exact absurd h hdel

private lemma cuspForm_square_div_delta_slash_action (f : CuspForm 𝒮ℒ 6) (γ : SL(2, ℤ)) :
    (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) ∣[(0 : ℤ)] γ =
      fun z : ℍ => f z ^ 2 / ModularForm.discriminant z := by
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) f ⟨γ, rfl⟩ z
  rw [sl_smul_eq_mapGL_smul, mapGL_eq_toGL_map] at hf
  have hd := congrFun (delta_slash_action_level_one γ) z
  rw [ModularForm.SL_slash_apply] at hd
  rw [ModularForm.SL_slash_apply, hf]
  have hdne :
      UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
          z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero _ _
  have hdelg : ModularForm.discriminant (γ • z) ≠ 0 := ModularForm.discriminant_ne_zero (γ • z)
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  field_simp [hdne, hdelg, hdel] at hd
  ring_nf at hd
  rw [hd]
  field_simp [hdne, hdel]
  · norm_num

private lemma mdiff_cuspForm_square_div_delta (f : CuspForm 𝒮ℒ 6) :
    MDiff (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hf : MDiff (f : ℍ → ℂ) := ModularFormClass.holo f
  have hf' := (UpperHalfPlane.mdifferentiable_iff.mp hf) z hz
  have hd :
      DifferentiableWithinAt ℂ
        (fun x : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex x)) {z | 0 < z.im} z :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdiff_delta) z hz
  have hdn : ModularForm.discriminant (UpperHalfPlane.ofComplex z) ≠ 0 :=
    ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
  exact (hf'.pow 2).div hd hdn

private lemma isZeroAtImInfty_cuspFormSquareDivDelta (f : CuspForm 𝒮ℒ 6) :
    UpperHalfPlane.IsZeroAtImInfty (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) := by
  apply UpperHalfPlane.IsZeroAtImInfty.of_exp_decay
  have hf_decay : ⇑f =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / 1) :=
    CuspFormClass.exp_decay_atImInfty f one_pos
      one_mem_strictPeriods_SL
  simp only [div_one] at hf_decay
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  have hf2 : (fun z : ℍ => f z ^ 2) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (-4 * Real.pi * τ.im) := by
    have h := hf_decay.pow 2
    refine h.congr_right fun z => ?_
    rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
  have hdelta_inv : (fun z : ℍ => (ModularForm.discriminant z)⁻¹) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (2 * Real.pi * τ.im) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(2 : ℝ) ^ 24, ?_⟩
    filter_upwards [delta_norm_lower_bound] with z hz
    rw [norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hpos : 0 < (1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im) := by positivity
    calc ‖ModularForm.discriminant z‖⁻¹
        ≤ ((1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im))⁻¹ :=
          inv_anti₀ hpos hz
      _ = (2 : ℝ) ^ 24 * (Real.exp (-2 * Real.pi * z.im))⁻¹ := by
          have : ((1 / 2 : ℝ) ^ 24)⁻¹ = (2 : ℝ) ^ 24 := by
            rw [one_div, inv_pow, inv_inv]
          rw [mul_inv_rev, mul_comm, this]
      _ = (2 : ℝ) ^ 24 * Real.exp (2 * Real.pi * z.im) := by
          congr 1; rw [← Real.exp_neg]; congr 1; ring
  exact ((hf2.mul hdelta_inv).congr_left (fun z => by simp [div_eq_mul_inv])).congr_right
    fun z => by rw [← Real.exp_add]; congr 1; ring

private lemma bddAtCusp_cuspFormSquareDivDelta (f : CuspForm 𝒮ℒ 6)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) 0 := by
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc]
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc
  exact ⟨γ, hγ.symm, by
    rw [cuspForm_square_div_delta_slash_action f γ]
    exact (isZeroAtImInfty_cuspFormSquareDivDelta f).isBoundedAtImInfty⟩

private noncomputable def cuspFormSquareDivDeltaMF (f : CuspForm 𝒮ℒ 6) :
    ModularForm 𝒮ℒ 0 where
  toSlashInvariantForm :=
    { toFun := fun z => f z ^ 2 / ModularForm.discriminant z
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        exact cuspForm_square_div_delta_slash_action f g }
  holo' := mdiff_cuspForm_square_div_delta f
  bdd_at_cusps' hc := bddAtCusp_cuspFormSquareDivDelta f hc

private lemma cuspFormSquareDivDelta_const (f : CuspForm 𝒮ℒ 6) :
    ∃ c : ℂ, ∀ z : ℍ, f z ^ 2 / ModularForm.discriminant z = c := by
  have ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const (cuspFormSquareDivDeltaMF f)
  exact ⟨c, fun z => congr_fun hc z⟩

private lemma cuspFormSquareDivDelta_eq_zero (f : CuspForm 𝒮ℒ 6) :
    ∀ z : ℍ, f z ^ 2 / ModularForm.discriminant z = 0 := by
  obtain ⟨c, hc⟩ := cuspFormSquareDivDelta_const f
  suffices c = 0 by intro z; rw [hc z, this]
  have hzero := isZeroAtImInfty_cuspFormSquareDivDelta f
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  have htend : Filter.Tendsto (fun _ : ℍ => c) UpperHalfPlane.atImInfty (nhds 0) :=
    hzero.congr (fun z => hc z)
  rwa [tendsto_const_nhds_iff] at htend

private theorem dim_S6_level_one_zero (f : CuspForm 𝒮ℒ 6) : ⇑f = 0 := by
  ext z
  have h := cuspFormSquareDivDelta_eq_zero f z
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rwa [pow_eq_zero_iff (by norm_num : 2 ≠ 0)] at h
  · exact absurd h hdel

/-- Slash invariance of `thetaE4Sum` under any element of `SL₂(ℤ)`, proved by
induction on the closure `⟨S, T⟩ = SL₂(ℤ)`. -/
private lemma thetaE4Sum_slash_action_SL (γ : SL(2, ℤ)) :
    (fun τ : ℍ => thetaE4Sum (τ : ℂ)) ∣[(4 : ℤ)] γ =
      fun τ : ℍ => thetaE4Sum (τ : ℂ) := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction with
  | one => simp [SlashAction.slash_one]
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · -- S case: thetaE4Sum(-1/τ) = τ⁴ · thetaE4Sum(τ) cancels denom(S,τ)⁻⁴ = τ⁻⁴
        ext τ
        have hne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
        simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S]
        have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
          rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]; field_simp
        rw [hS, thetaE4Sum_neg_inv τ, mul_comm ((τ : ℂ) ^ 4), mul_assoc,
          ← zpow_natCast (τ : ℂ) 4, ← zpow_add₀ hne]
        norm_num
      · -- T case: thetaE4Sum(τ+1) = thetaE4Sum(τ) and denom(T,τ) = 1
        ext τ
        simp only [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul,
          UpperHalfPlane.coe_vadd, Complex.ofReal_one]
        rw [show (1 : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 from add_comm _ _,
          thetaE4Sum_add_one]
        suffices h : UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) (τ : ℂ) = 1 by
          rw [h]; simp
        simp [UpperHalfPlane.denom, ModularGroup.T, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.of_apply]
  | mul g h _ _ ig ih =>
      rw [SlashAction.slash_mul, ig, ih]
  | inv g _ ig =>
      have h1 : (fun τ : ℍ => thetaE4Sum (τ : ℂ)) ∣[(4 : ℤ)] (g * g⁻¹) =
          (fun τ : ℍ => thetaE4Sum (τ : ℂ)) ∣[(4 : ℤ)] g⁻¹ := by
        rw [SlashAction.slash_mul, ig]
      rw [mul_inv_cancel, SlashAction.slash_one] at h1
      exact h1.symm

private lemma exp_neg_pi_le_third : Real.exp (-Real.pi) ≤ 1 / 3 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h_inv : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    calc (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by positivity) h2
      _ = 1 / 2 := by norm_num
  calc Real.exp (-Real.pi)
      ≤ Real.exp (-3 : ℝ) := Real.exp_le_exp_of_le (by linarith [Real.pi_gt_three])
    _ = Real.exp (-1 : ℝ) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le h_inv 3
    _ = 1 / 8 := by norm_num
    _ ≤ 1 / 3 := by norm_num

private lemma norm_jacobiTheta_sub_one_le_one {z : ℂ} (him : 0 < z.im) (hz1 : 1 ≤ z.im) :
    ‖jacobiTheta z - 1‖ ≤ 1 := by
  have h := norm_jacobiTheta_sub_one_le him
  have hr : Real.exp (-Real.pi * z.im) ≤ 1 / 3 :=
    (Real.exp_le_exp_of_le (by nlinarith [Real.pi_pos] : -Real.pi * z.im ≤ -Real.pi)).trans
      exp_neg_pi_le_third
  have hr_pos : (0 : ℝ) < 1 - Real.exp (-Real.pi * z.im) := by
    have : Real.exp (-Real.pi * z.im) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith [hr]
  calc ‖jacobiTheta z - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) := h
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div]
        exact div_le_one_of_le₀ (by linarith) hr_pos.le

private lemma thetaE4Sum_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => thetaE4Sum (τ : ℂ) / 2) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨768, 1, fun z hz => ?_⟩
  have him : 0 < (z : ℂ).im := z.im_pos
  have him4 : 0 < ((z : ℂ) + 1).im := by
    simp only [Complex.add_im, Complex.one_im, add_zero]; exact him
  have hθ₃ : ‖jacobiTheta (z : ℂ)‖ ≤ 2 := by
    have h1 := norm_jacobiTheta_sub_one_le_one him hz
    calc ‖jacobiTheta (z : ℂ)‖
        = ‖(jacobiTheta (z : ℂ) - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖jacobiTheta (z : ℂ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by linarith [norm_one (α := ℂ)]
      _ = 2 := by norm_num
  have hθ₄ : ‖thetaFourConst (z : ℂ)‖ ≤ 2 := by
    rw [thetaFourConst_eq_jacobiTheta_add_one]
    have hz1' : 1 ≤ ((z : ℂ) + 1).im := by
      simp only [Complex.add_im, Complex.one_im, add_zero]; exact hz
    have h1 := norm_jacobiTheta_sub_one_le_one him4 hz1'
    calc ‖jacobiTheta ((z : ℂ) + 1)‖
        = ‖(jacobiTheta ((z : ℂ) + 1) - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖jacobiTheta ((z : ℂ) + 1) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by linarith [norm_one (α := ℂ)]
      _ = 2 := by norm_num
  have hθ₂₄ : ‖thetaTwoConst (z : ℂ) ^ 4‖ ≤ 32 := by
    have hq := jacobi_theta_quartic_identity him
    have hsub : thetaTwoConst (z : ℂ) ^ 4 =
        jacobiTheta (z : ℂ) ^ 4 - thetaFourConst (z : ℂ) ^ 4 := by linear_combination -hq
    rw [hsub]
    calc ‖jacobiTheta (z : ℂ) ^ 4 - thetaFourConst (z : ℂ) ^ 4‖
        ≤ ‖jacobiTheta (z : ℂ) ^ 4‖ + ‖thetaFourConst (z : ℂ) ^ 4‖ := norm_sub_le _ _
      _ = ‖jacobiTheta (z : ℂ)‖ ^ 4 + ‖thetaFourConst (z : ℂ)‖ ^ 4 := by
          simp only [norm_pow]
      _ ≤ 2 ^ 4 + 2 ^ 4 := by gcongr
      _ = 32 := by norm_num
  have hθ₂₈ : ‖thetaTwoConst (z : ℂ) ^ 8‖ ≤ 1024 := by
    rw [show (8 : ℕ) = 4 * 2 from by norm_num, pow_mul, norm_pow]
    calc ‖thetaTwoConst (z : ℂ) ^ 4‖ ^ 2 ≤ 32 ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hθ₂₄ 2
      _ = 1024 := by norm_num
  have hθ₃₈ : ‖jacobiTheta (z : ℂ) ^ 8‖ ≤ 2 ^ 8 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hθ₃ 8
  have hθ₄₈ : ‖thetaFourConst (z : ℂ) ^ 8‖ ≤ 2 ^ 8 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hθ₄ 8
  have hsum : ‖thetaE4Sum (z : ℂ)‖ ≤ 1024 + 2 ^ 8 + 2 ^ 8 := by
    change ‖thetaTwoConst (z : ℂ) ^ 8 + jacobiTheta (z : ℂ) ^ 8 +
        thetaFourConst (z : ℂ) ^ 8‖ ≤ _
    calc ‖thetaTwoConst (z : ℂ) ^ 8 + jacobiTheta (z : ℂ) ^ 8 +
            thetaFourConst (z : ℂ) ^ 8‖
        ≤ ‖thetaTwoConst (z : ℂ) ^ 8 + jacobiTheta (z : ℂ) ^ 8‖ +
            ‖thetaFourConst (z : ℂ) ^ 8‖ := norm_add_le _ _
      _ ≤ (‖thetaTwoConst (z : ℂ) ^ 8‖ + ‖jacobiTheta (z : ℂ) ^ 8‖) +
            ‖thetaFourConst (z : ℂ) ^ 8‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (1024 + 2 ^ 8) + 2 ^ 8 := by linarith
  calc ‖thetaE4Sum (z : ℂ) / 2‖
      = ‖thetaE4Sum (z : ℂ)‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
    _ ≤ (1024 + 2 ^ 8 + 2 ^ 8) / 2 := by linarith
    _ = 768 := by norm_num

/-- `(1/2) · thetaE4Sum` as a level-1 weight-4 modular form. -/
private noncomputable def halfThetaE4SumMF : ModularForm 𝒮ℒ 4 where
  toSlashInvariantForm :=
    { toFun := fun τ => thetaE4Sum (τ : ℂ) / 2
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        have hsl := thetaE4Sum_slash_action_SL g
        change (fun τ : ℍ => thetaE4Sum (τ : ℂ) / 2) ∣[(4 : ℤ)] g =
            fun τ : ℍ => thetaE4Sum (τ : ℂ) / 2
        ext τ
        simp only [ModularForm.SL_slash_apply]
        rw [div_mul_eq_mul_div]
        have hτ := congr_fun hsl τ
        simp only [ModularForm.SL_slash_apply] at hτ
        rw [hτ] }
  holo' := by
    intro ⟨z, hz⟩
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    have hd : DifferentiableAt ℂ (fun w => thetaE4Sum w / 2) z :=
      ((((differentiableAt_thetaTwoConst hz).pow 8).add
        ((differentiableAt_jacobiTheta hz).pow 8)).add
        ((differentiableAt_thetaFourConst hz).pow 8)).div_const _
    exact hd.congr_of_eventuallyEq <| by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      rfl
  bdd_at_cusps' := fun {c} hc => by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv := thetaE4Sum_slash_action_SL γ
    have : (fun τ : ℍ => thetaE4Sum (τ : ℂ) / 2) ∣[(4 : ℤ)] γ =
        fun τ : ℍ => thetaE4Sum (τ : ℂ) / 2 := by
      ext τ
      rw [ModularForm.SL_slash_apply, div_mul_eq_mul_div]
      have hτ := congr_fun hinv τ
      rw [ModularForm.SL_slash_apply] at hτ
      rw [hτ]
    rw [this]
    exact thetaE4Sum_isBoundedAtImInfty

private lemma tendsto_rexp_neg_mul_im {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun z : ℍ => Real.exp (-c * z.im)) UpperHalfPlane.atImInfty (nhds 0) := by
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((Filter.tendsto_comap (f := UpperHalfPlane.im) :
        Filter.Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty Filter.atTop).const_mul_atTop
      hc)).congr ?_
  intro z
  simp only [Function.comp_apply, neg_mul]

private lemma tendsto_jacobiTheta_one :
    Filter.Tendsto (fun z : ℍ => jacobiTheta (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := by
  have h0 : Filter.Tendsto (fun z : ℍ => jacobiTheta (z : ℂ) - 1)
      UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
    refine (isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto
      UpperHalfPlane.tendsto_coe_atImInfty).trans_tendsto ?_
    simpa [Function.comp_def, UpperHalfPlane.coe_im] using
      tendsto_rexp_neg_mul_im Real.pi_pos
  have hconst : Filter.Tendsto (fun _ : ℍ => (1 : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := tendsto_const_nhds
  have := h0.add hconst
  simp only [sub_add_cancel, zero_add] at this
  exact this

private lemma tendsto_thetaFourConst_one :
    Filter.Tendsto (fun z : ℍ => thetaFourConst (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := by
  have hrewrite : ∀ z : ℍ, thetaFourConst (z : ℂ) = jacobiTheta ((z : ℂ) + 1) :=
    fun z => thetaFourConst_eq_jacobiTheta_add_one _
  simp_rw [hrewrite]
  have h0 : Filter.Tendsto (fun z : ℍ => jacobiTheta ((z : ℂ) + 1) - 1)
      UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
    have hφ : Filter.Tendsto (fun z : ℍ => (z : ℂ) + 1)
        UpperHalfPlane.atImInfty (Filter.comap Complex.im Filter.atTop) := by
      rw [Filter.tendsto_comap_iff]
      show Filter.Tendsto (Complex.im ∘ fun z : ℍ => (z : ℂ) + 1) _ Filter.atTop
      have : (Complex.im ∘ fun z : ℍ => (z : ℂ) + 1) = UpperHalfPlane.im := by
        ext z; simp [Complex.add_im, UpperHalfPlane.coe_im]
      rw [this]
      exact Filter.tendsto_comap
    refine (isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto hφ).trans_tendsto ?_
    simpa [Function.comp_def, Complex.add_im, UpperHalfPlane.coe_im] using
      tendsto_rexp_neg_mul_im Real.pi_pos
  have hconst : Filter.Tendsto (fun _ : ℍ => (1 : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := tendsto_const_nhds
  have := h0.add hconst
  simp only [sub_add_cancel, zero_add] at this
  exact this

private lemma tendsto_E4_one :
    Filter.Tendsto (fun z : ℍ => E4 z) UpperHalfPlane.atImInfty (nhds 1) := by
  have h0 : Filter.Tendsto (fun z : ℍ => E4 z - 1)
      UpperHalfPlane.atImInfty (nhds (0 : ℂ)) := by
    have hval : UpperHalfPlane.valueAtInfty (E4 : ℍ → ℂ) = 1 := by
      rw [← ModularFormClass.qExpansion_coeff_zero E4 one_pos
        one_mem_strictPeriods_SL]
      exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4)
        (by norm_num : Even 4)
    have hdec := UpperHalfPlane.exp_decay_sub_atImInfty one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex E4 one_mem_strictPeriods_SL)
      (ModularFormClass.holo E4)
      (ModularFormClass.bdd_at_infty E4)
    rw [hval] at hdec
    have ht : Filter.Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / 1))
        UpperHalfPlane.atImInfty (nhds 0) := by
      simpa [div_one, mul_assoc] using
        tendsto_rexp_neg_mul_im (by positivity : 0 < 2 * Real.pi)
    exact hdec.trans_tendsto ht
  have hconst : Filter.Tendsto (fun _ : ℍ => (1 : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := tendsto_const_nhds
  have := h0.add hconst
  simp only [sub_add_cancel, zero_add] at this
  exact this

private lemma E4_sub_halfThetaE4Sum_isZeroAtImInfty :
    UpperHalfPlane.IsZeroAtImInfty
      (fun z : ℍ => E4 z - thetaE4Sum (z : ℂ) / 2) := by
  change Filter.Tendsto (fun z : ℍ => E4 z - thetaE4Sum (z : ℂ) / 2)
    UpperHalfPlane.atImInfty (nhds 0)
  have h3 := tendsto_jacobiTheta_one
  have h4 := tendsto_thetaFourConst_one
  have h2_4 : Filter.Tendsto (fun z : ℍ => thetaTwoConst (z : ℂ) ^ 4)
      UpperHalfPlane.atImInfty (nhds 0) := by
    have hq : (fun z : ℍ => thetaTwoConst (z : ℂ) ^ 4) =
        fun z : ℍ => jacobiTheta (z : ℂ) ^ 4 - thetaFourConst (z : ℂ) ^ 4 := by
      ext z; linear_combination -(jacobi_theta_quartic_identity z.2)
    rw [hq]
    have := (h3.pow 4).sub (h4.pow 4)
    simp only [one_pow, sub_self] at this
    exact this
  have h2_8 : Filter.Tendsto (fun z : ℍ => thetaTwoConst (z : ℂ) ^ 8)
      UpperHalfPlane.atImInfty (nhds 0) := by
    have : (fun z : ℍ => thetaTwoConst (z : ℂ) ^ 8) =
        fun (z : ℍ) => (thetaTwoConst (z : ℂ) ^ 4) ^ 2 := by ext z; ring
    rw [this]
    have := h2_4.pow 2
    simp only [zero_pow, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true] at this
    exact this
  have htheta : Filter.Tendsto (fun z : ℍ => thetaE4Sum (z : ℂ) / 2)
      UpperHalfPlane.atImInfty (nhds 1) := by
    change Filter.Tendsto (fun z : ℍ => (thetaTwoConst (z : ℂ) ^ 8 +
        jacobiTheta (z : ℂ) ^ 8 + thetaFourConst (z : ℂ) ^ 8) / 2) _ (nhds 1)
    have htend := ((h2_8.add (h3.pow 8)).add (h4.pow 8)).div_const (2 : ℂ)
    simp only [one_pow, zero_add] at htend
    convert htend using 1
    norm_num
  have := tendsto_E4_one.sub htheta
  simp only [sub_self] at this
  exact this

/-- The difference `E₄ - thetaE4Sum/2` as a cusp form (the cusp vanishing
condition uses `E₄(∞) = 1` and `thetaE4Sum(∞) = 2`). -/
private noncomputable def E4SubHalfThetaCF : CuspForm 𝒮ℒ 4 :=
  { toSlashInvariantForm := (E4 - halfThetaE4SumMF).toSlashInvariantForm
    holo' := (E4 - halfThetaE4SumMF).holo'
    zero_at_cusps' := fun {c} hc => by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isZeroAt_iff_forall_SL2Z
        (f := (E4 - halfThetaE4SumMF).toFun) (k := (4 : ℤ)) hc]
      intro γ _
      have hcoe : (E4 - halfThetaE4SumMF).toFun = ⇑(E4 - halfThetaE4SumMF) := rfl
      suffices h : (E4 - halfThetaE4SumMF).toFun ∣[(4 : ℤ)] γ =
          (fun z : ℍ => E4 z - thetaE4Sum (z : ℂ) / 2) by
        rw [h]
        exact E4_sub_halfThetaE4Sum_isZeroAtImInfty
      rw [hcoe]
      ext τ
      rw [ModularForm.SL_slash_apply]
      have hinv := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ)
        (E4 - halfThetaE4SumMF) ⟨γ, rfl⟩ τ
      rw [sl_smul_eq_mapGL_smul, mapGL_eq_toGL_map] at hinv
      rw [hinv, zpow_neg]
      have hmul : ∀ (d : ℂ) (_ : d ≠ 0) (x : ℂ), d * x * d⁻¹ = x := fun d hd x => by
        rw [mul_comm d x, mul_assoc, mul_inv_cancel₀ hd, mul_one]
      exact hmul _ (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero γ τ)) _
  }

private theorem two_mul_E4_eq_thetaE4Sum (τ : ℍ) :
    2 * E4 τ = thetaE4Sum (τ : ℂ) := by
  have hzero := dim_S4_level_one_zero E4SubHalfThetaCF
  have hτ : E4 τ - thetaE4Sum (τ : ℂ) / 2 = 0 := by
    simpa [E4SubHalfThetaCF, halfThetaE4SumMF] using congr_fun hzero τ
  have := sub_eq_zero.mp hτ
  linear_combination 2 * this

/-- The reduced theta-constant formula for `E₄`, derived from the sum formula
`2E₄ = θ₂⁸ + θ₃⁸ + θ₄⁸` and Jacobi's quartic identity. -/
private theorem classical_E4_reduced_theta_identity (τ : ℍ) :
    E4 τ =
      thetaTwoConst (τ : ℂ) ^ 8 +
        thetaTwoConst (τ : ℂ) ^ 4 * thetaFourConst (τ : ℂ) ^ 4 +
          thetaFourConst (τ : ℂ) ^ 8 := by
  have h2E := two_mul_E4_eq_thetaE4Sum τ
  unfold thetaE4Sum at h2E
  have hquartic := jacobi_theta_quartic_identity τ.2
  have hθ38 : jacobiTheta (τ : ℂ) ^ 8 =
      (thetaTwoConst (τ : ℂ) ^ 4 + thetaFourConst (τ : ℂ) ^ 4) ^ 2 := by
    rw [← hquartic]; ring
  rw [hθ38] at h2E
  linear_combination h2E / 2

/-- The standard theta-constant formula for `E₄`, specialized at `τ₁₆₃`. -/
theorem two_mul_E4_heegnerTau163_eq_theta_sum :
    2 * E4 heegnerTau163 =
      thetaTwoConst (heegnerTau163 : ℂ) ^ 8 +
        jacobiTheta (heegnerTau163 : ℂ) ^ 8 +
          thetaFourConst (heegnerTau163 : ℂ) ^ 8 := by
  exact two_mul_E4_eq_thetaE4Sum heegnerTau163

/-- Algebraic form of the `E₄` theta formula using Jacobi's quartic identity. -/
lemma E4_heegnerTau163_eq_thetaExpression :
    E4 heegnerTau163 =
      jacobiTheta (heegnerTau163 : ℂ) ^ 8 -
        thetaTwoConst (heegnerTau163 : ℂ) ^ 4 *
          thetaFourConst (heegnerTau163 : ℂ) ^ 4 := by
  have hE := two_mul_E4_heegnerTau163_eq_theta_sum
  have hquartic :
      jacobiTheta (heegnerTau163 : ℂ) ^ 4 =
        thetaTwoConst (heegnerTau163 : ℂ) ^ 4 +
          thetaFourConst (heegnerTau163 : ℂ) ^ 4 :=
    (jacobiQuarticDefect_eq_zero_iff (heegnerTau163 : ℂ)).mp
      heegnerTau163_jacobiQuarticDefect_eq_zero
  have htheta8 :
      jacobiTheta (heegnerTau163 : ℂ) ^ 8 =
        (thetaTwoConst (heegnerTau163 : ℂ) ^ 4 +
          thetaFourConst (heegnerTau163 : ℂ) ^ 4) ^ 2 := by
    rw [← hquartic]
    ring
  calc
    E4 heegnerTau163 =
        (thetaTwoConst (heegnerTau163 : ℂ) ^ 8 +
          jacobiTheta (heegnerTau163 : ℂ) ^ 8 +
            thetaFourConst (heegnerTau163 : ℂ) ^ 8) / 2 := by
          linear_combination hE / 2
    _ = jacobiTheta (heegnerTau163 : ℂ) ^ 8 -
        thetaTwoConst (heegnerTau163 : ℂ) ^ 4 *
          thetaFourConst (heegnerTau163 : ℂ) ^ 4 := by
          rw [htheta8]
          ring

private noncomputable def etaProductQ (τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * τ)

private noncomputable def etaPochhammer (τ : ℂ) : ℂ :=
  qPochhammerInf (etaProductQ τ)

private noncomputable def etaEvenPlusProduct (τ : ℂ) : ℂ :=
  ∏' n : ℕ, (1 + etaProductQ τ ^ (n + 1))

private noncomputable def etaOddMinusProduct (τ : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - etaProductQ τ ^ (2 * n + 1))

private lemma eta_eq_exp_mul_qPochhammerInf (τ : ℂ) :
    ModularForm.eta τ =
      Complex.exp (2 * Real.pi * Complex.I * τ / 24) * etaPochhammer τ := by
  unfold ModularForm.eta etaPochhammer etaProductQ
  rw [show Function.Periodic.qParam 24 τ =
      Complex.exp (2 * Real.pi * Complex.I * τ / 24) by
        simp [Function.Periodic.qParam]]
  rw [← qPochhammerInf_eq_eta_tprod τ]

private lemma norm_etaProductQ_lt_one (τ : ℍ) :
    ‖etaProductQ (τ : ℂ)‖ < 1 :=
  UpperHalfPlane.norm_exp_two_pi_I_lt_one τ

private lemma summable_norm_etaProductQ_pow (τ : ℍ) :
    Summable fun n : ℕ => ‖etaProductQ (τ : ℂ) ^ (n + 1)‖ := by
  simp only [norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) (norm_etaProductQ_lt_one τ)).mul_left _
    |>.congr (fun n => by ring)

private lemma multipliable_one_sub_etaProductQ_pow (τ : ℍ) :
    Multipliable fun n : ℕ => 1 - etaProductQ (τ : ℂ) ^ (n + 1) := by
  have h : Multipliable fun n : ℕ => (1 : ℂ) + (-(etaProductQ (τ : ℂ) ^ (n + 1))) :=
    multipliable_one_add_of_summable ((summable_norm_etaProductQ_pow τ).congr
      (fun n => by simp [norm_neg]))
  exact h.congr (fun n => by ring)

private lemma multipliable_one_add_etaProductQ_pow (τ : ℍ) :
    Multipliable fun n : ℕ => 1 + etaProductQ (τ : ℂ) ^ (n + 1) :=
  multipliable_one_add_of_summable (summable_norm_etaProductQ_pow τ)

private lemma summable_norm_etaProductQ_odd_pow (τ : ℍ) :
    Summable fun n : ℕ => ‖etaProductQ (τ : ℂ) ^ (2 * n + 1)‖ := by
  have hq := norm_etaProductQ_lt_one τ
  have hq2 : ‖etaProductQ (τ : ℂ)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hg := (summable_geometric_of_lt_one (by positivity) hq2).mul_left
    (‖etaProductQ (τ : ℂ)‖)
  apply hg.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_pow]
  rw [show 2 * n + 1 = 1 + 2 * n from by omega, pow_add, pow_one, pow_mul]

private lemma multipliable_one_sub_etaProductQ_odd_pow (τ : ℍ) :
    Multipliable fun n : ℕ => 1 - etaProductQ (τ : ℂ) ^ (2 * n + 1) := by
  have h : Multipliable fun n : ℕ => (1 : ℂ) + (-(etaProductQ (τ : ℂ) ^ (2 * n + 1))) :=
    multipliable_one_add_of_summable ((summable_norm_etaProductQ_odd_pow τ).congr
      (fun n => by simp [norm_neg]))
  exact h.congr (fun n => by ring)

private lemma summable_norm_etaProductQ_even_pow (τ : ℍ) :
    Summable fun n : ℕ => ‖etaProductQ (τ : ℂ) ^ (2 * n + 1 + 1)‖ := by
  have hq := norm_etaProductQ_lt_one τ
  have hq2 : ‖etaProductQ (τ : ℂ)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hg := (summable_geometric_of_lt_one (by positivity) hq2).mul_left
    (‖etaProductQ (τ : ℂ)‖ ^ 2)
  apply hg.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_pow]
  rw [show 2 * n + 1 + 1 = 2 + 2 * n from by omega, pow_add, pow_mul]

private lemma multipliable_one_sub_etaProductQ_even_pow (τ : ℍ) :
    Multipliable fun n : ℕ => 1 - etaProductQ (τ : ℂ) ^ (2 * n + 1 + 1) := by
  have h : Multipliable fun n : ℕ => (1 : ℂ) + (-(etaProductQ (τ : ℂ) ^ (2 * n + 1 + 1))) :=
    multipliable_one_add_of_summable ((summable_norm_etaProductQ_even_pow τ).congr
      (fun n => by simp [norm_neg]))
  exact h.congr (fun n => by ring)

private lemma etaPochhammer_ne_zero (τ : ℍ) :
    etaPochhammer (τ : ℂ) ≠ 0 := by
  unfold etaPochhammer qPochhammerInf
  have heq : (fun n : ℕ => 1 - etaProductQ (τ : ℂ) ^ (n + 1)) =
      (fun n : ℕ => 1 + (-(etaProductQ (τ : ℂ) ^ (n + 1)))) := by
    ext n; ring
  rw [heq]
  apply tprod_one_add_ne_zero_of_summable
  · intro n heq'
    have h1 : ‖etaProductQ (τ : ℂ) ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (norm_etaProductQ_lt_one τ)
        (by omega : n + 1 ≠ 0)
    have h2 : etaProductQ (τ : ℂ) ^ (n + 1) = 1 := by linear_combination -heq'
    have h3 : ‖etaProductQ (τ : ℂ) ^ (n + 1)‖ = 1 := by rw [h2, norm_one]
    linarith
  · exact (summable_norm_etaProductQ_pow τ).congr (fun n => by simp [norm_neg])

/-- The eighth-power theta product `(θ₂ · θ₃ · θ₄)⁸ = θ₂⁸ · θ₃⁸ · θ₄⁸`. -/
private noncomputable def thetaProductEight (τ : ℂ) : ℂ :=
  thetaTwoConst τ ^ 8 * jacobiTheta τ ^ 8 * thetaFourConst τ ^ 8

private lemma thetaProductEight_add_one (τ : ℂ) :
    thetaProductEight (τ + 1) = thetaProductEight τ := by
  unfold thetaProductEight
  rw [thetaTwoConst_add_one, jacobiTheta_add_one, thetaFourConst_add_one]
  rw [mul_pow]
  have hroot : Complex.exp (Real.pi * Complex.I / 4) ^ 8 = 1 := by
    rw [← Complex.exp_nat_mul]
    rw [show (8 : ℕ) * (Real.pi * Complex.I / 4) = 2 * Real.pi * Complex.I by norm_num; ring]
    rw [Complex.exp_two_pi_mul_I]
  rw [hroot]
  ring

private lemma thetaProductEight_neg_inv (τ : ℍ) :
    thetaProductEight (-1 / (τ : ℂ)) =
      (τ : ℂ) ^ 12 * thetaProductEight (τ : ℂ) := by
  unfold thetaProductEight
  rw [thetaTwoConst_neg_inv_pow_eight (τ : ℂ) (UpperHalfPlane.ne_zero τ)]
  rw [thetaFourConst_neg_inv_pow_eight (τ : ℂ) (UpperHalfPlane.ne_zero τ)]
  rw [jacobiTheta_neg_inv_pow_eight τ]
  ring

private lemma thetaProductEight_slash_action_SL (γ : SL(2, ℤ)) :
    (fun τ : ℍ => thetaProductEight (τ : ℂ)) ∣[(12 : ℤ)] γ =
      fun τ : ℍ => thetaProductEight (τ : ℂ) := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction with
  | one => simp [SlashAction.slash_one]
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · ext τ
        have hne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
        simp only [ModularForm.SL_slash_apply, ModularGroup.denom_S]
        have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
          rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]; field_simp
        rw [hS, thetaProductEight_neg_inv τ, mul_comm ((τ : ℂ) ^ 12), mul_assoc,
          ← zpow_natCast (τ : ℂ) 12, ← zpow_add₀ hne]
        norm_num
      · ext τ
        simp only [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul,
          UpperHalfPlane.coe_vadd, Complex.ofReal_one]
        rw [show (1 : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 from add_comm _ _,
          thetaProductEight_add_one]
        suffices h : UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) (τ : ℂ) = 1 by
          rw [h]; simp
        simp [UpperHalfPlane.denom, ModularGroup.T, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.of_apply]
  | mul g h _ _ ig ih =>
      rw [SlashAction.slash_mul, ig, ih]
  | inv g _ ig =>
      have h1 : (fun τ : ℍ => thetaProductEight (τ : ℂ)) ∣[(12 : ℤ)] (g * g⁻¹) =
          (fun τ : ℍ => thetaProductEight (τ : ℂ)) ∣[(12 : ℤ)] g⁻¹ := by
        rw [SlashAction.slash_mul, ig]
      rw [mul_inv_cancel, SlashAction.slash_one] at h1
      exact h1.symm

private lemma mdiff_thetaProductEight :
    MDiff (fun z : ℍ => thetaProductEight (z : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  change DifferentiableWithinAt ℂ
    (fun x : ℂ => thetaProductEight (UpperHalfPlane.ofComplex x : ℂ)) {z | 0 < z.im} z
  simp only [thetaProductEight]
  have h1 := differentiableAt_thetaTwoConst hz
  have h2 := differentiableAt_jacobiTheta hz
  have h3 := differentiableAt_thetaFourConst hz
  exact (((h1.pow 8).mul (h2.pow 8)).mul (h3.pow 8)).differentiableWithinAt.congr
    (fun x hx => by simp [UpperHalfPlane.ofComplex_apply_of_im_pos hx])
    (by simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz])

private lemma thetaProductEight_div_delta_slash_action (γ : SL(2, ℤ)) :
    (fun z : ℍ => thetaProductEight (z : ℂ) / ModularForm.discriminant z) ∣[(0 : ℤ)] γ =
      fun z : ℍ => thetaProductEight (z : ℂ) / ModularForm.discriminant z := by
  ext z
  have htp := congrFun (thetaProductEight_slash_action_SL γ) z
  have hd := congrFun (delta_slash_action_level_one γ) z
  rw [ModularForm.SL_slash_apply] at htp hd
  rw [ModularForm.SL_slash_apply]
  have hdne : UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero _ _
  have hdelg : ModularForm.discriminant (γ • z) ≠ 0 := ModularForm.discriminant_ne_zero (γ • z)
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  field_simp [hdne, hdelg, hdel] at hd htp ⊢
  rw [hd, htp]
  simp only [neg_zero, zpow_zero, mul_one]
  ring

/-- `θ₂⁸ = q · jacobiTheta₂(τ/2, τ)⁸` where `q = 𝕢 1 τ = exp(2πiτ)`. -/
private lemma thetaTwoConst_pow_8_eq_q_mul (τ : ℂ) :
    thetaTwoConst τ ^ 8 =
      Function.Periodic.qParam 1 τ * jacobiTheta₂ (τ / 2) τ ^ 8 := by
  rw [thetaTwoConst_eq, mul_pow]
  congr 1
  rw [Function.Periodic.qParam]
  simp only [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `jacobiTheta₂(τ/2, τ) → 2` as `Im(τ) → ∞`. -/
private lemma tendsto_jacobiTheta2_half :
    Filter.Tendsto (fun z : ℍ => jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 2) := by
  suffices h0 : Filter.Tendsto
      (fun z : ℍ => jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) - 2)
      UpperHalfPlane.atImInfty (nhds (0 : ℂ)) by
    have := h0.add (tendsto_const_nhds (x := (2 : ℂ)))
    simp only [sub_add_cancel, zero_add] at this; exact this
  have hpair : ∀ (τ : ℂ) (n : ℕ),
      jacobiTheta₂_term (↑n) (τ / 2) τ = jacobiTheta₂_term (-(↑n + 1)) (τ / 2) τ := by
    intro τ n; simp only [jacobiTheta₂_term]; congr 1; push_cast; ring
  have hterm0 : ∀ τ : ℂ, jacobiTheta₂_term (0 : ℤ) (τ / 2) τ = 1 := fun τ => by
    simp [jacobiTheta₂_term]
  have htail : ∀ z : ℍ, HasSum
      (fun n : ℕ => 2 * jacobiTheta₂_term (↑(n + 1) : ℤ) ((z : ℂ) / 2) (z : ℂ))
      (jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) - 2) := by
    intro z
    have hs := (hasSum_jacobiTheta₂_term ((z : ℂ) / 2) z.2).nat_add_neg_add_one
    simp_rw [show ∀ n : ℕ, jacobiTheta₂_term (↑n) ((z : ℂ) / 2) (z : ℂ) +
        jacobiTheta₂_term (-(↑n + 1)) ((z : ℂ) / 2) (z : ℂ) =
        2 * jacobiTheta₂_term (↑n : ℤ) ((z : ℂ) / 2) (z : ℂ) from fun n => by
      rw [← hpair]; ring] at hs
    have h1 := (hasSum_nat_add_iff' 1).mpr hs
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, hterm0, mul_one] at h1
    exact h1
  apply squeeze_zero_norm (a := fun z : ℍ =>
    2 * (Real.exp (-(2 * Real.pi) * z.im) / (1 - Real.exp (-(2 * Real.pi) * z.im))))
  · intro z
    have hrq : Real.exp (-(2 * Real.pi) * z.im) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [z.im_pos, Real.pi_pos])
    have hterm_le : ∀ n : ℕ,
        ‖2 * jacobiTheta₂_term (↑(n + 1) : ℤ) ((z : ℂ) / 2) (z : ℂ)‖ ≤
        2 * Real.exp (-(2 * Real.pi) * z.im) ^ (n + 1) := by
      intro n
      rw [norm_mul, Complex.norm_ofNat, norm_jacobiTheta₂_term]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      simp only [Complex.div_ofNat_im, UpperHalfPlane.coe_im, Int.cast_natCast]
      push_cast
      have hpi := Real.pi_pos
      have hy := z.im_pos
      have hn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
      have h_np : (0 : ℝ) ≤ ↑n + 1 := by linarith
      linarith [mul_nonneg (mul_nonneg (mul_nonneg hpi.le h_np) hy.le) hn]
    have hgeo : HasSum (fun n : ℕ => 2 * Real.exp (-(2 * Real.pi) * z.im) ^ (n + 1))
        (2 * (Real.exp (-(2 * Real.pi) * z.im) / (1 - Real.exp (-(2 * Real.pi) * z.im)))) := by
      suffices h : HasSum (fun n : ℕ => Real.exp (-(2 * Real.pi) * z.im) ^ (n + 1))
          (Real.exp (-(2 * Real.pi) * z.im) / (1 - Real.exp (-(2 * Real.pi) * z.im))) from
        h.mul_left 2
      have h0 := hasSum_geometric_of_lt_one (Real.exp_pos _).le hrq
      have h1 := (hasSum_nat_add_iff' 1).mpr h0
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero] at h1
      have hne : (1 : ℝ) - Real.exp (-(2 * Real.pi) * z.im) ≠ 0 := by
        intro h; linarith [hrq]
      rwa [show (1 - Real.exp (-(2 * Real.pi) * z.im))⁻¹ - 1 =
        Real.exp (-(2 * Real.pi) * z.im) / (1 - Real.exp (-(2 * Real.pi) * z.im)) from by
        rw [inv_eq_one_div, div_sub_one hne]; ring_nf] at h1
    exact (htail z).norm_le_of_bounded hgeo hterm_le
  · change Filter.Tendsto
        ((fun r => 2 * (r / (1 - r))) ∘ (fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im)))
        UpperHalfPlane.atImInfty (nhds 0)
    apply Filter.Tendsto.comp _ (tendsto_rexp_neg_mul_im (by positivity : 0 < 2 * Real.pi))
    have hcont : Filter.Tendsto (fun r : ℝ => 2 * (r / (1 - r))) (nhds 0)
        (nhds (2 * ((0 : ℝ) / (1 - 0)))) :=
      continuousAt_const.mul
        (continuousAt_id.div (continuousAt_const.sub continuousAt_id)
          (by norm_num : (1 : ℝ) - 0 ≠ 0))
    simp only [zero_div, mul_zero] at hcont
    exact hcont

/-- The eta product `∏(1 - q^(n+1))` tends to 1 at infinity. -/
private lemma tendsto_eta_tprod_one :
    Filter.Tendsto (fun z : ℍ => ∏' n, (1 - ModularForm.eta_q n (z : ℂ)))
      UpperHalfPlane.atImInfty (nhds 1) := by
  suffices h0 : Filter.Tendsto
      (fun z : ℍ => ∏' n, (1 - ModularForm.eta_q n (z : ℂ)) - 1)
      UpperHalfPlane.atImInfty (nhds (0 : ℂ)) by
    have := h0.add (tendsto_const_nhds (x := (1 : ℂ)))
    simp only [sub_add_cancel, zero_add] at this; exact this
  apply squeeze_zero_norm
  · intro z
    exact norm_tprod_one_sub_sub_one_le
      (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2)
      (by simpa [norm_neg] using ModularForm.summable_eta_q z)
  · -- exp(∑'‖eta_q n z‖) - 1 → 0 since ∑'‖eta_q‖ = r/(1-r) → 0 for r = exp(-2πy)
    have h_sum_eq : ∀ z : ℍ, ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ =
        ‖Function.Periodic.qParam 1 (z : ℂ)‖ /
          (1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖) := by
      intro z
      simp only [ModularForm.eta_q, norm_pow]
      rw [show (fun n : ℕ => ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ (n + 1)) =
          (fun n => ‖Function.Periodic.qParam 1 (z : ℂ)‖ *
            ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ n)
        from funext (fun n => by ring),
        tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) (by
          rw [norm_qParam_eq]
          exact Real.exp_lt_one_iff.mpr (by nlinarith [z.im_pos, Real.pi_pos])),
        div_eq_mul_inv]
    simp_rw [h_sum_eq, norm_qParam_eq]
    have key : ∀ z : ℍ, -2 * Real.pi * z.im = -(2 * Real.pi) * z.im := fun _ => by ring
    simp_rw [key]
    change Filter.Tendsto
      ((fun r => Real.exp (r / (1 - r)) - 1) ∘ (fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im)))
      UpperHalfPlane.atImInfty (nhds 0)
    apply Filter.Tendsto.comp _ (tendsto_rexp_neg_mul_im (by positivity : 0 < 2 * Real.pi))
    have hcont : Filter.Tendsto (fun r : ℝ => Real.exp (r / (1 - r)) - 1) (nhds 0)
        (nhds (Real.exp ((0 : ℝ) / (1 - 0)) - 1)) :=
      ContinuousAt.sub
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_id.div (continuousAt_const.sub continuousAt_id)
            (by norm_num : (1 : ℝ) - 0 ≠ 0)))
        continuousAt_const
    simp only [zero_div, Real.exp_zero, sub_self] at hcont
    exact hcont

lemma tendsto_delta_zero :
    Filter.Tendsto (fun z : ℍ => ModularForm.discriminant z)
      UpperHalfPlane.atImInfty (nhds 0) := by
  have hq : Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hprod : Filter.Tendsto
      (fun z : ℍ => (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 24)
      UpperHalfPlane.atImInfty (nhds (1 ^ 24)) :=
    tendsto_eta_tprod_one.pow 24
  have hmul := hq.mul hprod
  simpa only [zero_mul, one_pow] using hmul.congr' (Filter.Eventually.of_forall fun z => by
    rw [ModularForm.discriminant_eq_q_prod z,
      (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow 24])

lemma delta_isZeroAtImInfty :
    UpperHalfPlane.IsZeroAtImInfty (fun z : ℍ => ModularForm.discriminant z) :=
  tendsto_delta_zero

lemma isBoundedAtImInfty_delta :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => ModularForm.discriminant z) :=
  delta_isZeroAtImInfty.isBoundedAtImInfty

lemma bddAtCusp_delta
    {c : OnePoint ℝ} (hc : IsCusp c Γ(1)) :
    c.IsBoundedAt (fun z : ℍ => ModularForm.discriminant z) 12 := by
  have hc' : IsCusp c 𝒮ℒ := by
    convert hc using 1
    change 𝒮ℒ = (Gamma 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)
    rw [Gamma_one_top]
    exact (MonoidHom.range_eq_map
      (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ))
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _hγ
  rw [delta_slash_action_level_one γ]
  exact isBoundedAtImInfty_delta

theorem deltaQExpansion_hasSum (τ : ℍ) :
    HasSum (fun d : ℕ =>
      PowerSeries.coeff (R := ℂ) d deltaQExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ d)
      (ModularForm.discriminant τ) := by
  unfold deltaQExpansion
  simpa [smul_eq_mul, deltaLevelOneMF] using
    (ModularFormClass.hasSum_qExpansion (f := deltaLevelOneMF)
      (h := 1) one_pos one_mem_strictPeriods_SL τ)

theorem deltaQExpansion_summable_norm (τ : ℍ) :
    Summable fun d : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) d deltaQExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ d‖ := by
  unfold deltaQExpansion
  simpa [deltaLevelOneMF] using
    qExpansion_summable_norm_of_norm_lt_one (f := deltaLevelOneMF)
      one_pos one_mem_strictPeriods_SL
      (by simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ)

theorem deltaQExpansion_evalCertificate (τ : ℍ) :
    PowerSeriesEvalCertificate deltaQExpansion
      (Function.Periodic.qParam 1 (τ : ℂ)) (ModularForm.discriminant τ) := by
  exact ⟨deltaQExpansion_hasSum τ, deltaQExpansion_summable_norm τ⟩

theorem E4CubedQExpansionAtTau_evalCertificate :
    PowerSeriesEvalCertificate E4CubedQExpansionAtTau
      (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ))
      (E4 heegnerTau163 ^ 3) := by
  have hbase := PowerSeriesEvalCertificate.pow (E4QExpansion_evalCertificate heegnerTau163) 3
  have hbaseQ : PowerSeriesEvalCertificate (E4QExpansion ^ 3)
      (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ 41)
      (E4 heegnerTau163 ^ 3) := by
    simpa [qParam_heegnerTau163_div41_pow_41] using hbase
  simpa [E4CubedQExpansionAtTau] using PowerSeriesEvalCertificate.qPullback41 hbaseQ

theorem deltaQExpansionAtTau_evalCertificate :
    PowerSeriesEvalCertificate deltaQExpansionAtTau
      (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ))
      (ModularForm.discriminant heegnerTau163) := by
  have hbase := deltaQExpansion_evalCertificate heegnerTau163
  have hbaseQ : PowerSeriesEvalCertificate deltaQExpansion
      (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ 41)
      (ModularForm.discriminant heegnerTau163) := by
    simpa [qParam_heegnerTau163_div41_pow_41] using hbase
  simpa [deltaQExpansionAtTau] using PowerSeriesEvalCertificate.qPullback41 hbaseQ

theorem E4CubedQExpansionAtTauDiv41_evalCertificate :
    PowerSeriesEvalCertificate E4CubedQExpansionAtTauDiv41
      (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ))
      (E4 heegnerTau163_div41 ^ 3) := by
  simpa [E4CubedQExpansionAtTauDiv41] using
    PowerSeriesEvalCertificate.pow (E4QExpansion_evalCertificate heegnerTau163_div41) 3

theorem deltaQExpansionAtTauDiv41_evalCertificate :
    PowerSeriesEvalCertificate deltaQExpansionAtTauDiv41
      (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ))
      (ModularForm.discriminant heegnerTau163_div41) := by
  simpa [deltaQExpansionAtTauDiv41] using
    deltaQExpansion_evalCertificate heegnerTau163_div41

theorem deltaQExpansion_eq_deltaEulerSeries_of_dominated
    (hbound :
      ∀ τ : ℍ, ∃ bound : ℕ → ℝ,
        Summable bound ∧
          ∀ᶠ N : ℕ in Filter.atTop, ∀ d : ℕ,
            ‖PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) *
              Function.Periodic.qParam 1 (τ : ℂ) ^ d‖ ≤ bound d) :
    deltaQExpansion = deltaEulerSeries := by
  refine deltaQExpansion_eq_deltaEulerSeries_of_delta_hasSum ?_
  intro τ
  rcases hbound τ with ⟨bound, hbound_sum, hbound_eventually⟩
  exact delta_hasSum_deltaEulerCoeff_of_dominated τ hbound_sum hbound_eventually

theorem deltaQExpansion_eq_deltaEulerSeries_of_absCoeffEval_bound
    (hbound :
      ∀ τ : ℍ, ∃ s C : ℝ,
        0 < s ∧ s < 1 ∧ ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < s ∧
          ∀ᶠ N : ℕ in Filter.atTop,
            Polynomial.absCoeffEval (deltaEulerPolyTrunc N) s ≤ C) :
    deltaQExpansion = deltaEulerSeries := by
  refine deltaQExpansion_eq_deltaEulerSeries_of_delta_hasSum ?_
  intro τ
  rcases hbound τ with ⟨s, C, hs_pos, hs_lt_one, hqs, hC⟩
  exact delta_hasSum_deltaEulerCoeff_of_absCoeffEval_bound τ hs_pos hs_lt_one hqs hC

theorem complex_sturm_bound_valence_formula_phi41Level41Cleared :
    phi41Level41ComplexSturmPrinciple := by
  exact complex_sturm_bound_valence_formula_phi41Level41Cleared_of_modularForm_qExpansion_and_sturm
    phi41Level41ClearedAsModularForm
    (phi41Level41ClearedAsModularForm_qExpansion deltaQExpansion_eq_deltaEulerSeries)
    (levelGamma0_41_sturm_weight_1008 phi41Level41ClearedAsModularForm)

/-- Integer-coefficient version of the level-41 Sturm principle.  This is now
only a coercion bridge from the complex modular-form statement above. -/
theorem sturm_bound_valence_formula_phi41Level41Cleared :
    phi41Level41SturmPrinciple := by
  exact phi41Level41SturmPrinciple_of_complex
    complex_sturm_bound_valence_formula_phi41Level41Cleared

theorem phi41Level41SturmPrinciple_proof :
    phi41Level41SturmPrinciple := by
  exact sturm_bound_valence_formula_phi41Level41Cleared

theorem phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm_certificate
    (hcert : phi41Level41SturmCoefficientCertificate) :
    ∀ n : ℕ,
      PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0 :=
  phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm
    phi41Level41SturmPrinciple_proof hcert

theorem phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm_range_certificate
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    ∀ n : ℕ,
      PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0 :=
  phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm_certificate
    (phi41Level41SturmCoefficientCertificate_of_range hcert)

theorem phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm_certificate
    (hcert : phi41Level41SturmCoefficientCertificate) :
    phi41Level41ClearedEulerQExpansion = 0 := by
  exact phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm
    phi41Level41SturmPrinciple_proof hcert

theorem phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm_range_certificate
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    phi41Level41ClearedEulerQExpansion = 0 := by
  exact phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm_certificate
    (phi41Level41SturmCoefficientCertificate_of_range hcert)

theorem phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm_certificate
    (hdelta : deltaQExpansion = deltaEulerSeries)
    (hcert : phi41Level41SturmCoefficientCertificate) :
    phi41Level41ClearedQExpansion = 0 := by
  exact phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm hdelta
    phi41Level41SturmPrinciple_proof hcert

theorem phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm_range_certificate
    (hdelta : deltaQExpansion = deltaEulerSeries)
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    phi41Level41ClearedQExpansion = 0 := by
  exact phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm_certificate hdelta
    (phi41Level41SturmCoefficientCertificate_of_range hcert)

/-- The ratio `θ₂⁸θ₃⁸θ₄⁸/Δ` tends to `256` at infinity. -/
private lemma tendsto_thetaProductEight_div_delta :
    Filter.Tendsto (fun z : ℍ => thetaProductEight (z : ℂ) / ModularForm.discriminant z)
      UpperHalfPlane.atImInfty (nhds 256) := by
  have hq_ne : ∀ z : ℍ, Function.Periodic.qParam 1 (z : ℂ) ≠ 0 :=
    fun z => Complex.exp_ne_zero _
  have hprod_ne : ∀ z : ℍ, ∏' n, (1 - ModularForm.eta_q n (z : ℂ)) ≠ 0 :=
    fun z => ModularForm.eta_tprod_ne_zero z.2
  have hrewrite : ∀ z : ℍ, thetaProductEight (z : ℂ) / ModularForm.discriminant z =
      jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) ^ 8 * jacobiTheta (z : ℂ) ^ 8 *
        thetaFourConst (z : ℂ) ^ 8 /
          (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 24 := by
    intro z
    have hdelta_ne := ModularForm.discriminant_ne_zero z
    have hp := pow_ne_zero 24 (hprod_ne z)
    rw [div_eq_div_iff hdelta_ne hp]
    unfold thetaProductEight
    rw [thetaTwoConst_pow_8_eq_q_mul, ModularForm.discriminant_eq_q_prod z,
        ← (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow 24]
    ring
  simp_rw [hrewrite]
  have h_jt2 := tendsto_jacobiTheta2_half.pow 8
  have h_j3 := tendsto_jacobiTheta_one.pow 8
  have h_j4 := tendsto_thetaFourConst_one.pow 8
  have h_prod := tendsto_eta_tprod_one.pow 24
  simp only [one_pow] at h_j3 h_j4 h_prod
  have h_num := (h_jt2.mul h_j3).mul h_j4
  simp only [mul_one] at h_num
  convert h_num.div h_prod (by norm_num) using 1; norm_num

/-- The eighth-power theta product divided by Δ tends to 256 at infinity. -/
private lemma thetaProductEight_div_delta_isZeroAtImInfty :
    UpperHalfPlane.IsZeroAtImInfty
      (fun z : ℍ => thetaProductEight (z : ℂ) / ModularForm.discriminant z -
        256) := by
  have h := tendsto_thetaProductEight_div_delta.sub
    (tendsto_const_nhds (x := (256 : ℂ)))
  simp only [sub_self] at h
  exact h

private lemma isBoundedAtImInfty_thetaProductEight_div_delta :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun z : ℍ => thetaProductEight (z : ℂ) / ModularForm.discriminant z) := by
  suffices h : UpperHalfPlane.IsBoundedAtImInfty
      (fun z : ℍ => (thetaProductEight (z : ℂ) / ModularForm.discriminant z - 256) + (256 : ℂ)) by
    rwa [show (fun z : ℍ => (thetaProductEight (z : ℂ) / ModularForm.discriminant z - 256) +
      (256 : ℂ)) = fun z : ℍ => thetaProductEight (z : ℂ) / ModularForm.discriminant z from
        by ext z; ring] at h
  exact thetaProductEight_div_delta_isZeroAtImInfty.isBoundedAtImInfty.add
    (.of_bound 256 (Filter.Eventually.of_forall fun _ => by
      simp only [Pi.one_apply, norm_one, mul_one]; norm_num))

private lemma thetaProductEight_div_delta_eq_256 (τ : ℍ) :
    thetaProductEight (τ : ℂ) / ModularForm.discriminant τ = 256 := by
  let F : ModularForm 𝒮ℒ 0 :=
    { toSlashInvariantForm :=
        { toFun := fun z => thetaProductEight (z : ℂ) / ModularForm.discriminant z
          slash_action_eq' := fun γ hγ => by
            obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
            exact thetaProductEight_div_delta_slash_action g }
      holo' := by
        rw [UpperHalfPlane.mdifferentiable_iff]
        intro z hz
        have htp := (UpperHalfPlane.mdifferentiable_iff.mp mdiff_thetaProductEight) z hz
        have hd := (UpperHalfPlane.mdifferentiable_iff.mp mdiff_delta) z hz
        have hdn : ModularForm.discriminant (UpperHalfPlane.ofComplex z) ≠ 0 :=
          ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
        exact htp.div hd hdn
      bdd_at_cusps' := fun {c} hc => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [thetaProductEight_div_delta_slash_action γ]
        exact isBoundedAtImInfty_thetaProductEight_div_delta }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  have heq : ∀ z : ℍ, thetaProductEight (z : ℂ) / ModularForm.discriminant z = c := by
    intro z; exact congr_fun hc z
  rw [heq τ]
  have hzero := thetaProductEight_div_delta_isZeroAtImInfty
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  have htend : Filter.Tendsto (fun _ : ℍ => c - (256 : ℂ)) UpperHalfPlane.atImInfty (nhds 0) :=
    hzero.congr fun z => by rw [heq z]
  rwa [tendsto_const_nhds_iff, sub_eq_zero] at htend

/-- The eighth-power identity: `(θ₂θ₃θ₄)⁸ = 256Δ = (2η³)⁸`. -/
private theorem thetaProductEight_eq_256_delta (τ : ℍ) :
    thetaProductEight (τ : ℂ) = 256 * ModularForm.discriminant τ := by
  have h := thetaProductEight_div_delta_eq_256 τ
  have hdel : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rwa [div_eq_iff hdel] at h

/-- The classical Jacobi identity `θ₂ · θ₃ · θ₄ = 2η³`.

Proved by the dimension argument: `(θ₂θ₃θ₄)⁸ = 256η²⁴` as weight-12
modular forms (using the S and T transformation laws and `dim S₁₂ = 1`),
then taking the 8th root via a continuity argument on ℍ. -/
private theorem jacobi_triple_product_theta_eta_normalization (τ : ℍ) :
    thetaTwoConst (τ : ℂ) * jacobiTheta (τ : ℂ) * thetaFourConst (τ : ℂ) =
      2 * ModularForm.eta (τ : ℂ) ^ 3 := by
  have heta_ne : ∀ z : ℍ, ModularForm.eta (z : ℂ) ≠ 0 := fun z => ModularForm.eta_ne_zero z.2
  have hprod_ne : ∀ z : ℍ, ∏' n, (1 - ModularForm.eta_q n (z : ℂ)) ≠ 0 :=
    fun z => ModularForm.eta_tprod_ne_zero z.2
  have h2eta3_ne : ∀ z : ℍ, (2 : ℂ) * ModularForm.eta (z : ℂ) ^ 3 ≠ 0 :=
    fun z => mul_ne_zero two_ne_zero (pow_ne_zero 3 (heta_ne z))
  suffices hratio : thetaTwoConst (τ : ℂ) * jacobiTheta (τ : ℂ) * thetaFourConst (τ : ℂ) /
      (2 * ModularForm.eta (τ : ℂ) ^ 3) = 1 by
    rwa [div_eq_one_iff_eq (h2eta3_ne τ)] at hratio
  -- Rewrite ratio by canceling the common q-factor exp(πiτ/4)
  have hq_cancel : ∀ z : ℍ,
      thetaTwoConst (z : ℂ) * jacobiTheta (z : ℂ) * thetaFourConst (z : ℂ) /
        (2 * ModularForm.eta (z : ℂ) ^ 3) =
      jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) * jacobiTheta (z : ℂ) * thetaFourConst (z : ℂ) /
        (2 * (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3) := by
    intro z
    have h2p3 : (2 : ℂ) * (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3 ≠ 0 :=
      mul_ne_zero two_ne_zero (pow_ne_zero 3 (hprod_ne z))
    rw [div_eq_div_iff (h2eta3_ne z) h2p3, thetaTwoConst_eq,
      show ModularForm.eta (z : ℂ) = Function.Periodic.qParam 24 (z : ℂ) *
        ∏' n, (1 - ModularForm.eta_q n (z : ℂ)) from rfl, mul_pow,
      show (Function.Periodic.qParam (24 : ℝ) (z : ℂ)) ^ 3 =
        Complex.exp (↑Real.pi * Complex.I * (z : ℂ) / 4) from by
        rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]
    ring
  rw [hq_cancel]
  -- The simplified ratio satisfies r^8 = 1
  -- (abbreviation for readability)
  let r : ℍ → ℂ := fun z => jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) * jacobiTheta (z : ℂ) *
    thetaFourConst (z : ℂ) / (2 * (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3)
  change r τ = 1
  have hpow8 : ∀ z : ℍ, r z ^ 8 = 1 := by
    intro z
    change (jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) * jacobiTheta (z : ℂ) * thetaFourConst (z : ℂ) /
        (2 * (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3)) ^ 8 = 1
    rw [← hq_cancel z, div_pow]
    have hnum : (thetaTwoConst (z : ℂ) * jacobiTheta (z : ℂ) * thetaFourConst (z : ℂ)) ^ 8 =
        thetaProductEight (z : ℂ) := by unfold thetaProductEight; ring
    rw [hnum, thetaProductEight_eq_256_delta z]
    simp only [ModularForm.discriminant]
    have h_den : (2 * ModularForm.eta (z : ℂ) ^ 3) ^ 8 =
        256 * ModularForm.eta (z : ℂ) ^ 24 := by ring
    rw [h_den]
    exact div_self (mul_ne_zero (by norm_num) (pow_ne_zero 24 (heta_ne z)))
  -- r is continuous on ℍ
  have hr_cont : Continuous r := by
    change Continuous fun z : ℍ => jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) * jacobiTheta (z : ℂ) *
      thetaFourConst (z : ℂ) / (2 * (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3)
    apply Continuous.div
    · exact ((continuous_iff_continuousAt.mpr fun z =>
          (differentiableAt_jacobiTheta₂_diag_half z.im_pos).continuousAt.comp
            UpperHalfPlane.continuous_coe.continuousAt).mul
        (continuous_iff_continuousAt.mpr fun z =>
          (differentiableAt_jacobiTheta z.im_pos).continuousAt.comp
            UpperHalfPlane.continuous_coe.continuousAt)).mul
        (continuous_iff_continuousAt.mpr fun z =>
          (differentiableAt_thetaFourConst z.im_pos).continuousAt.comp
            UpperHalfPlane.continuous_coe.continuousAt)
    · exact continuous_const.mul ((continuous_iff_continuousAt.mpr fun z =>
          (ModularForm.differentiableAt_eta_tprod z.2).continuousAt.comp
            UpperHalfPlane.continuous_coe.continuousAt).pow 3)
    · exact fun z => mul_ne_zero two_ne_zero (pow_ne_zero 3 (hprod_ne z))
  -- {z : ℂ | z ^ 8 = 1} is finite hence discrete
  have h_disc : IsDiscrete {z : ℂ | z ^ 8 = 1} := by
    apply Set.Finite.isDiscrete
    have : {z : ℂ | z ^ 8 = 1} =
        {z : ℂ | Polynomial.IsRoot
          ((Polynomial.X : Polynomial ℂ) ^ 8 - Polynomial.C 1) z} := by
      ext z; simp [Polynomial.IsRoot, sub_eq_zero]
    rw [this]
    exact Polynomial.finite_setOf_isRoot (by
      intro h; have := congr_arg (Polynomial.eval (0 : ℂ)) h; simp at this)
  -- By connectedness of ℍ, r is constant
  have hr_const : ∀ z₁ z₂ : ℍ, r z₁ = r z₂ := by
    intro z₁ z₂
    exact isPreconnected_univ.constant_of_mapsTo h_disc hr_cont.continuousOn
      (fun z _ => hpow8 z) trivial trivial
  -- r tends to 1 at the cusp
  have hr_lim : Filter.Tendsto r UpperHalfPlane.atImInfty (nhds 1) := by
    change Filter.Tendsto (fun z : ℍ => jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) *
        jacobiTheta (z : ℂ) * thetaFourConst (z : ℂ) /
        (2 * (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3))
        UpperHalfPlane.atImInfty (nhds 1)
    have h_num : Filter.Tendsto (fun z : ℍ => jacobiTheta₂ ((z : ℂ) / 2) (z : ℂ) *
        jacobiTheta (z : ℂ) * thetaFourConst (z : ℂ))
        UpperHalfPlane.atImInfty (nhds (2 * 1 * 1)) :=
      (tendsto_jacobiTheta2_half.mul tendsto_jacobiTheta_one).mul tendsto_thetaFourConst_one
    have h_den : Filter.Tendsto (fun z : ℍ => (2 : ℂ) *
        (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 3)
        UpperHalfPlane.atImInfty (nhds (2 * 1 ^ 3)) :=
      tendsto_const_nhds.mul (tendsto_eta_tprod_one.pow 3)
    have := h_num.div h_den (by norm_num : (2 : ℂ) * 1 ^ 3 ≠ 0)
    simp only [mul_one, one_pow, div_self (two_ne_zero' ℂ)] at this
    exact this
  -- Since r is constant and r → 1, r = 1
  have h_const_lim : Filter.Tendsto (fun _ : ℍ => r τ) UpperHalfPlane.atImInfty (nhds (r τ)) :=
    tendsto_const_nhds
  have h_eq : r = fun _ => r τ := funext (fun z => hr_const z τ)
  rw [h_eq] at hr_lim
  exact tendsto_nhds_unique h_const_lim hr_lim

/-- Jacobi triple-product corollary in the repository normalizations,
specialized at `τ₁₆₃`. -/
theorem thetaTwo_mul_thetaThree_mul_thetaFour_heegnerTau163 :
    thetaTwoConst (heegnerTau163 : ℂ) *
        jacobiTheta (heegnerTau163 : ℂ) *
          thetaFourConst (heegnerTau163 : ℂ) =
      2 * ModularForm.eta (heegnerTau163 : ℂ) ^ 3 := by
  exact jacobi_triple_product_theta_eta_normalization heegnerTau163

/-- The theta-constant product formula for the discriminant modular form,
specialized at `τ₁₆₃`. -/
theorem delta_heegnerTau163_eq_thetaExpression :
    ModularForm.discriminant heegnerTau163 =
      thetaTwoConst (heegnerTau163 : ℂ) ^ 8 *
        thetaFourConst (heegnerTau163 : ℂ) ^ 8 *
          jacobiTheta (heegnerTau163 : ℂ) ^ 8 / 256 := by
  unfold ModularForm.discriminant
  have hprod := thetaTwo_mul_thetaThree_mul_thetaFour_heegnerTau163
  rw [show thetaTwoConst (heegnerTau163 : ℂ) ^ 8 *
        thetaFourConst (heegnerTau163 : ℂ) ^ 8 *
          jacobiTheta (heegnerTau163 : ℂ) ^ 8 =
      (thetaTwoConst (heegnerTau163 : ℂ) *
        jacobiTheta (heegnerTau163 : ℂ) *
          thetaFourConst (heegnerTau163 : ℂ)) ^ 8 by ring]
  rw [hprod]
  ring

/-- Algebraic consequence of the theta formulas for `E₄` and `Δ`. -/
theorem kleinJ_heegnerTau163_eq_thetaExpression :
    kleinJ heegnerTau163 =
      kleinJThetaExpression (heegnerTau163 : ℂ) := by
  unfold kleinJ kleinJThetaExpression
  rw [E4_heegnerTau163_eq_thetaExpression,
    delta_heegnerTau163_eq_thetaExpression]
  have hθ : jacobiTheta (heegnerTau163 : ℂ) ^ 8 ≠ 0 :=
    pow_ne_zero 8 jacobiTheta_heegnerTau163_ne_zero_qExpansion
  have hθ₂ : thetaTwoConst (heegnerTau163 : ℂ) ^ 8 ≠ 0 :=
    pow_ne_zero 8 thetaTwoConst_heegnerTau163_ne_zero
  have hθ₄ : thetaFourConst (heegnerTau163 : ℂ) ^ 8 ≠ 0 :=
    pow_ne_zero 8 thetaFourConst_heegnerTau163_ne_zero
  field_simp [hθ, hθ₂, hθ₄]

/-- The classical identity `j(τ) = J(λ(τ))` specialized at `τ₁₆₃`, with
`λ = thetaLambda`.

The algebraic rational function `J` is `kleinJFromLambda`.  Proving this from
the definitions means comparing the Eisenstein/delta definition of `kleinJ`
with the theta-constant expression supplied by `thetaLambda`, using the
quartic identity specialized above. -/
theorem kleinJ_heegnerTau163_eq_kleinJFromLambda_thetaLambda :
    kleinJ heegnerTau163 =
      kleinJFromLambda (thetaLambda (heegnerTau163 : ℂ)) := by
  rw [kleinJ_heegnerTau163_eq_thetaExpression,
    kleinJFromLambda_thetaLambda_heegnerTau163_eq_thetaExpression]

private lemma modular_TS_heegnerTau163_div41 :
    (ModularGroup.T * ModularGroup.S) • heegnerTau163_div41 = heegnerTau163 := by
  ext
  rw [mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
    UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  rw [show (-(heegnerTau163_div41 : ℂ))⁻¹ =
      -82 / ((1 : ℂ) + Real.sqrt 163 * Complex.I) by
    simp [heegnerTau163_div41]
    field_simp]
  have hnorm :
      Complex.normSq ((1 : ℂ) + Real.sqrt 163 * Complex.I) = 164 := by
    simp [Complex.normSq]
    norm_num
  apply Complex.ext
  · rw [Complex.add_re, Complex.ofReal_re, Complex.div_re]
    norm_num [hnorm, heegnerTau163]
  · rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_im]
    norm_num [hnorm, heegnerTau163]
    ring

theorem kleinJ_heegnerTau163_div41_eq :
    kleinJ heegnerTau163_div41 = kleinJ heegnerTau163 := by
  have hJ :
      kleinJ ((ModularGroup.T * ModularGroup.S) • heegnerTau163_div41) =
        kleinJ heegnerTau163_div41 := by
    rw [mul_smul, kleinJ_T_invariant, kleinJ_S_invariant]
  rw [modular_TS_heegnerTau163_div41] at hJ
  exact hJ.symm

theorem phi41SparseTerms_cleared_kleinJ (τ τ' : ℍ) :
    evalSparseBivarClearedC phi41SparseTerms 42 42
        (E4 τ ^ 3) (ModularForm.discriminant τ)
        (E4 τ' ^ 3) (ModularForm.discriminant τ') =
      ModularForm.discriminant τ ^ 42 * ModularForm.discriminant τ' ^ 42 *
        evalSparseBivarC phi41SparseTerms (kleinJ τ) (kleinJ τ') := by
  rw [kleinJ_eq_E4_cubed_div_delta τ, kleinJ_eq_E4_cubed_div_delta τ']
  exact phi41SparseTerms_cleared_eq_den_mul_eval
    (E4 τ ^ 3) (ModularForm.discriminant τ)
    (E4 τ' ^ 3) (ModularForm.discriminant τ')
    (ModularForm.discriminant_ne_zero τ) (ModularForm.discriminant_ne_zero τ')

theorem level41_input_of_bivariate_modular_polynomial
    (Phi41 : ℂ → ℂ → ℂ)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        Phi41 (kleinJ τ) (kleinJ τ') = 0)
    (hdiag : ∀ z : ℂ, Phi41 z z = evalPhi41DiagIsolatedC z) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  have hw := heegnerTau163_level41_transform_witness
  have hΦ := hmod heegnerTau163 heegnerTau163_div41 hw
  rw [kleinJ_heegnerTau163_div41_eq] at hΦ
  rw [kleinJ_heegnerTau163_div41_eq]
  rw [← hdiag (kleinJ heegnerTau163)]
  exact hΦ

theorem level41_input_of_sparse_bivariate_modular_polynomial
    (terms : List SparseBivarTerm)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC terms (kleinJ τ) (kleinJ τ') = 0)
    (hdiag : ∀ z : ℂ, evalSparseBivarDiagC terms z = evalPhi41DiagIsolatedC z) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  refine level41_input_of_bivariate_modular_polynomial
    (fun x y => evalSparseBivarC terms x y) hmod ?_
  intro z
  change evalSparseBivarC terms z z = evalPhi41DiagIsolatedC z
  rw [evalSparseBivarC_diag, hdiag]

theorem level41_input_of_sparse_bivariate_modular_polynomial_with_diag_certificate
    (terms : List SparseBivarTerm)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC terms (kleinJ τ) (kleinJ τ') = 0)
    (hpoly : sparseBivarDiagPolynomialC terms = phi41DiagIsolatedPolynomialC) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_sparse_bivariate_modular_polynomial terms hmod
    (sparseBivarDiag_eq_evalPhi41DiagIsolatedC_of_polynomial_eq terms hpoly)

theorem level41_input_of_phi41SparseTerms
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC phi41SparseTerms (kleinJ τ) (kleinJ τ') = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_sparse_bivariate_modular_polynomial phi41SparseTerms
    hmod phi41SparseTerms_diag_eq_evalPhi41DiagIsolatedC

theorem level41_input_of_phi41SparseTerms_at_cm163
    (hmod : evalSparseBivarC phi41SparseTerms (kleinJ heegnerTau163)
      (kleinJ heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  rw [kleinJ_heegnerTau163_div41_eq] at hmod
  rw [evalSparseBivarC_diag] at hmod
  rw [kleinJ_heegnerTau163_div41_eq]
  rw [← phi41SparseTerms_diag_eq_evalPhi41DiagIsolatedC (kleinJ heegnerTau163)]
  exact hmod

theorem level41_input_of_phi41SparseTerms_cleared_at_cm163
    (hcleared :
      evalSparseBivarClearedC phi41SparseTerms 42 42
        (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
        (E4 heegnerTau163_div41 ^ 3) (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  have hzero := hcleared
  rw [phi41SparseTerms_cleared_kleinJ heegnerTau163 heegnerTau163_div41] at hzero
  have hden :
      ModularForm.discriminant heegnerTau163 ^ 42 *
          ModularForm.discriminant heegnerTau163_div41 ^ 42 ≠ 0 := by
    exact mul_ne_zero
      (pow_ne_zero 42 (ModularForm.discriminant_ne_zero heegnerTau163))
      (pow_ne_zero 42 (ModularForm.discriminant_ne_zero heegnerTau163_div41))
  have hmod :
      evalSparseBivarC phi41SparseTerms (kleinJ heegnerTau163)
        (kleinJ heegnerTau163_div41) = 0 := by
    rcases mul_eq_zero.mp hzero with hden_zero | hΦ
    · exact (hden hden_zero).elim
    · exact hΦ
  exact level41_input_of_phi41SparseTerms_at_cm163 hmod

theorem level41_input_of_phi41Level41ClearedQExpansion_certificate
    (hdeltaCoeff :
      ∀ d : ℕ, PowerSeries.coeff (R := ℂ) d deltaQExpansion = deltaEulerCoeff d)
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  have hseries :
      phi41Level41ClearedQExpansion = 0 :=
    phi41Level41ClearedQExpansion_eq_zero_of_delta_coeff_and_coeffZ
      hdeltaCoeff hcoeff
  exact level41_input_of_phi41SparseTerms_cleared_at_cm163 (hvalue hseries)

theorem level41_input_of_phi41Level41ClearedQExpansion_certificate_of_delta_hasSum
    (hdeltaSum :
      ∀ τ : ℍ,
        HasSum (fun d : ℕ =>
          deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
          (ModularForm.discriminant τ))
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  have hdelta : deltaQExpansion = deltaEulerSeries :=
    deltaQExpansion_eq_deltaEulerSeries_of_delta_hasSum hdeltaSum
  have hseries :
      phi41Level41ClearedQExpansion = 0 :=
    phi41Level41ClearedQExpansion_eq_zero_of_delta_euler_and_coeffZ
      hdelta hcoeff
  exact level41_input_of_phi41SparseTerms_cleared_at_cm163 (hvalue hseries)

theorem level41_input_of_phi41Level41ClearedQExpansion_certificate_of_euler
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  have hseries :
      phi41Level41ClearedQExpansion = 0 :=
    phi41Level41ClearedQExpansion_eq_zero_of_delta_euler_and_coeffZ
      deltaQExpansion_eq_deltaEulerSeries hcoeff
  exact level41_input_of_phi41SparseTerms_cleared_at_cm163 (hvalue hseries)

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41SparseTerms_cleared_at_cm163
    (hvalue (phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm
      deltaQExpansion_eq_deltaEulerSeries hsturm hcert))

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate_proof
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate
    phi41Level41SturmPrinciple_proof hcert hvalue

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_certificate
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate
    hsturm (phi41Level41SturmCoefficientCertificate_of_range hcert) hvalue

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_certificate_proof
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_certificate
    phi41Level41SturmPrinciple_proof hcert hvalue


theorem phi41Level41ClearedQExpansion_value_zero_of_hasSum
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    phi41Level41ClearedQExpansion = 0 →
      evalSparseBivarClearedC phi41SparseTerms 42 42
        (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
        (E4 heegnerTau163_div41 ^ 3)
        (ModularForm.discriminant heegnerTau163_div41) = 0 := by
  intro hzero
  exact powerSeries_coeff_hasSum_value_eq_zero_of_eq_zero hseries hzero

/-- Monomial-level analytic evaluation certificate for the CM-163
level-41 cleared q-expansion. -/
def phi41Level41SparseTermEvaluationCertificate : Prop :=
  ∀ t : SparseBivarTerm, t ∈ phi41SparseTerms →
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n
          ((t.coeff : PowerSeries ℂ) *
            E4CubedQExpansionAtTau ^ t.xPow *
            deltaQExpansionAtTau ^ (42 - t.xPow) *
            E4CubedQExpansionAtTauDiv41 ^ t.yPow *
            deltaQExpansionAtTauDiv41 ^ (42 - t.yPow)) *
        Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
      ((t.coeff : ℂ) * (E4 heegnerTau163 ^ 3) ^ t.xPow *
        ModularForm.discriminant heegnerTau163 ^ (42 - t.xPow) *
        (E4 heegnerTau163_div41 ^ 3) ^ t.yPow *
        ModularForm.discriminant heegnerTau163_div41 ^ (42 - t.yPow))

theorem phi41Level41SparseTermEvaluationCertificate_of_factor_certificates :
    phi41Level41SparseTermEvaluationCertificate := by
  intro t _ht
  let q : ℂ := Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ)
  have hc : PowerSeriesEvalCertificate (t.coeff : PowerSeries ℂ) q (t.coeff : ℂ) := by
    simpa using PowerSeriesEvalCertificate.const (t.coeff : ℂ) q
  have hx :=
    PowerSeriesEvalCertificate.pow E4CubedQExpansionAtTau_evalCertificate t.xPow
  have hdx :=
    PowerSeriesEvalCertificate.pow deltaQExpansionAtTau_evalCertificate (42 - t.xPow)
  have hy :=
    PowerSeriesEvalCertificate.pow E4CubedQExpansionAtTauDiv41_evalCertificate t.yPow
  have hdy :=
    PowerSeriesEvalCertificate.pow deltaQExpansionAtTauDiv41_evalCertificate (42 - t.yPow)
  have hterm :=
    PowerSeriesEvalCertificate.mul
      (PowerSeriesEvalCertificate.mul
        (PowerSeriesEvalCertificate.mul
          (PowerSeriesEvalCertificate.mul hc hx) hdx) hy) hdy
  simpa [q, mul_assoc] using hterm.hasSum

/-- Specialized finite-sparse reduction for evaluating the level-41 cleared
q-expansion at the CM-163 point.  After this theorem, the analytic work is
only to prove the individual monomial products have the advertised sums. -/
theorem phi41Level41ClearedQExpansion_hasSum_of_sparse_term_hasSum
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
        Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
      (evalSparseBivarClearedC phi41SparseTerms 42 42
        (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
        (E4 heegnerTau163_div41 ^ 3)
        (ModularForm.discriminant heegnerTau163_div41)) := by
  exact evalSparseBivarCleared_hasSum_of_term_hasSum
    phi41SparseTerms 42 42
    E4CubedQExpansionAtTau deltaQExpansionAtTau
    E4CubedQExpansionAtTauDiv41 deltaQExpansionAtTauDiv41
    (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
    (E4 heegnerTau163_div41 ^ 3)
    (ModularForm.discriminant heegnerTau163_div41)
    (Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ))
    hterms

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate
    hsturm hcert (phi41Level41ClearedQExpansion_value_zero_of_hasSum hseries)

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_eval_proof
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_eval
    phi41Level41SturmPrinciple_proof hcert hseries

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_certificate
    hsturm hcert (phi41Level41ClearedQExpansion_value_zero_of_hasSum hseries)

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_eval_proof
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_eval
    phi41Level41SturmPrinciple_proof hcert hseries

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_eval
    hsturm hcert
    (phi41Level41ClearedQExpansion_hasSum_of_sparse_term_hasSum hterms)

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval_proof
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval
    phi41Level41SturmPrinciple_proof hcert hterms

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_sparse_term_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_eval
    hsturm hcert
    (phi41Level41ClearedQExpansion_hasSum_of_sparse_term_hasSum hterms)

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_sparse_term_eval_proof
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_sparse_term_eval
    phi41Level41SturmPrinciple_proof hcert hterms

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_factor_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval
    hsturm hcert phi41Level41SparseTermEvaluationCertificate_of_factor_certificates

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_factor_eval_proof
    (hcert : phi41Level41SturmCoefficientCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_factor_eval
    phi41Level41SturmPrinciple_proof hcert

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_factor_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_sparse_term_eval
    hsturm hcert phi41Level41SparseTermEvaluationCertificate_of_factor_certificates

theorem level41_input_of_phi41Level41ClearedQExpansion_sturm_range_factor_eval_proof
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_range_factor_eval
    phi41Level41SturmPrinciple_proof hcert

theorem level41_input_cm163 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  exact level41_input_of_phi41Level41ClearedQExpansion_sturm_factor_eval_proof
    phi41Level41SturmCoefficientCertificate_proof

theorem eval_phi41SparseTerms_at_cm163_eq_diag :
    evalSparseBivarC phi41SparseTerms (kleinJ heegnerTau163)
        (kleinJ heegnerTau163_div41) =
      evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) := by
  rw [kleinJ_heegnerTau163_div41_eq]
  rw [evalSparseBivarC_diag, phi41SparseTerms_diag_eq_evalPhi41DiagIsolatedC]

theorem phi41SparseTerms_at_cm163_vanish_iff_diag :
    evalSparseBivarC phi41SparseTerms (kleinJ heegnerTau163)
        (kleinJ heegnerTau163_div41) = 0 ↔
      evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 := by
  rw [eval_phi41SparseTerms_at_cm163_eq_diag]

theorem kleinJ_heegnerTau163_eq_j163Val_of_phi41_diag
    (hmod : evalPhi41DiagIsolatedC (kleinJ heegnerTau163) = 0) :
    kleinJ heegnerTau163 = (j163Val : ℂ) := by
  have htarget : heegnerJ163Target = (j163Val : ℂ) := by
    norm_num [heegnerJ163Target, j163Val]
  have hclose :
      ‖kleinJ heegnerTau163 - (j163Val : ℂ)‖ < 1 := by
    rw [kleinJ_heegnerTau163_eq_thetaExpression]
    simpa [htarget] using
      norm_kleinJThetaExpression_heegnerTau163_sub_target_lt_one
  exact eq_j163Val_of_evalPhi41DiagIsolatedC_eq_zero_of_norm_sub_lt_one hmod hclose

theorem kleinJ_heegnerTau163_integral_integer_of_phi41_diag
    (hmod : evalPhi41DiagIsolatedC (kleinJ heegnerTau163) = 0) :
    ∃ n : ℤ, kleinJ heegnerTau163 = (n : ℂ) := by
  exact ⟨j163Val, kleinJ_heegnerTau163_eq_j163Val_of_phi41_diag hmod⟩

theorem modular_poly_41_vanishes_on_diagonal_cm163_of_kleinJ_eq_j163Val
    (hJ : kleinJ heegnerTau163 = (j163Val : ℂ)) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163) = 0 := by
  rw [hJ]
  exact evalPhi41DiagIsolatedC_j163Val

/-- The level-41 modular polynomial vanishes on the CM diagonal.  This is the
remaining modular-equation input: `τ₁₆₃` and `τ₁₆₃ / 41` are related by a
degree-41 cyclic isogeny, while the latter is `SL₂(ℤ)`-equivalent to
`τ₁₆₃`; after the diagonal specialization and root isolation, this is exactly
the centered polynomial equation used below. -/
theorem modular_poly_41_vanishes_on_diagonal_cm163_of_vanishes_at_div41
    (hlevel41 : evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0) :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163) = 0 := by
  simpa [kleinJ_heegnerTau163_div41_eq] using hlevel41

theorem modular_poly_41_vanishes_on_diagonal_cm163 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163) = 0 := by
  exact modular_poly_41_vanishes_on_diagonal_cm163_of_vanishes_at_div41 level41_input_cm163

/-- CM integrality via modular polynomial root isolation.

**Proof outline (bypasses CM theory):**
1. `Φ₄₁(j(τ₁₆₃), j(τ₁₆₃)) = 0` (modular equation; `τ₁₆₃` has CM norm 41).
2. `Φ₄₁(X,X) = (X + 640320³)² · g(X)` where `g(-640320³) ≠ 0` (ModularPoly41.lean).
3. Proximity `‖j(τ₁₆₃) - (-640320³)‖ < 1` (proved above).
4. Taylor domination: `g(z) ≠ 0` for `|z + 640320³| ≤ 1`.
5. Root isolation: `j(τ₁₆₃) = -640320³ ∈ ℤ`.

**Proved components:**
- Factorization identity (phi41Diag_eq_sq_mul_cofactor in ModularPoly41.lean): ✓ by `ring`.
- Root verification: `evalPhi41Diag (-640320³) = 0`: ✓ by kernel `decide` (`phi41Diag_root`).
- Cofactor nonvanishing: `evalPhi41DiagCofactor (-640320³) ≠ 0`: ✓ by kernel `decide`
  (`phi41DiagCofactor_ne_zero`).
-/
theorem kleinJ_heegnerTau163_integral_integer_of_phi41_diag_div41 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 →
    ∃ n : ℤ, kleinJ heegnerTau163 = (n : ℂ) := by
  intro hlevel41
  exact kleinJ_heegnerTau163_integral_integer_of_phi41_diag
    (modular_poly_41_vanishes_on_diagonal_cm163_of_vanishes_at_div41 hlevel41)

theorem kleinJ_heegnerTau163_eq_j163Val_of_phi41_diag_div41 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 →
    kleinJ heegnerTau163 = (j163Val : ℂ) := by
  intro hlevel41
  have htarget : heegnerJ163Target = (j163Val : ℂ) := by
    norm_num [heegnerJ163Target, j163Val]
  have hclose :
      ‖kleinJ heegnerTau163 - (j163Val : ℂ)‖ < 1 := by
    rw [kleinJ_heegnerTau163_eq_thetaExpression]
    simpa [htarget] using
      norm_kleinJThetaExpression_heegnerTau163_sub_target_lt_one
  exact complex_int_eq_of_norm_sub_lt_one
    (kleinJ_heegnerTau163_integral_integer_of_phi41_diag_div41 hlevel41)
    hclose

theorem kleinJ_heegnerTau163_integral_integer :
    ∃ n : ℤ, kleinJ heegnerTau163 = (n : ℂ) := by
  exact kleinJ_heegnerTau163_integral_integer_of_phi41_diag_div41 level41_input_cm163

theorem kleinJ_heegnerTau163_eq_j163Val :
    kleinJ heegnerTau163 = (j163Val : ℂ) := by
  exact kleinJ_heegnerTau163_eq_j163Val_of_phi41_diag_div41 level41_input_cm163

theorem evalPhi41DiagIsolatedC_kleinJThetaExpression_heegnerTau163_eq_zero_of_div41 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 →
    evalPhi41DiagIsolatedC (kleinJThetaExpression (heegnerTau163 : ℂ)) = 0 := by
  intro hlevel41
  rw [← kleinJ_heegnerTau163_eq_thetaExpression]
  exact modular_poly_41_vanishes_on_diagonal_cm163_of_vanishes_at_div41 hlevel41

private theorem cm_integrality_theta_expression_163
    (hlevel41 : evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0) :
    ∃ n : ℤ, kleinJThetaExpression (heegnerTau163 : ℂ) = (n : ℂ) := by
  refine ⟨j163Val, ?_⟩
  set z : ℂ := kleinJThetaExpression (heegnerTau163 : ℂ)
  have htarget : heegnerJ163Target = (j163Val : ℂ) := by
    norm_num [heegnerJ163Target, j163Val]
  have hclose : ‖z - (j163Val : ℂ)‖ < 1 := by
    simpa [z, htarget] using
      norm_kleinJThetaExpression_heegnerTau163_sub_target_lt_one
  have hmod : evalPhi41DiagIsolatedC z = 0 := by
    simpa [z] using evalPhi41DiagIsolatedC_kleinJThetaExpression_heegnerTau163_eq_zero_of_div41 hlevel41
  exact eq_j163Val_of_evalPhi41DiagIsolatedC_eq_zero_of_norm_sub_lt_one hmod hclose

/-- Exact target value, obtained by combining CM integrality
with the explicit q-expansion bound (proximity < 1). -/
theorem kleinJThetaExpression_heegnerTau163_eq_target_of_phi41_diag_div41
    (hlevel41 : evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0) :
    kleinJThetaExpression (heegnerTau163 : ℂ) = heegnerJ163Target := by
  let m : ℤ := -((640320 : ℤ) ^ 3)
  have htarget : heegnerJ163Target = (m : ℂ) := by
    dsimp [m]
    norm_num [heegnerJ163Target]
  have hclose :
      ‖kleinJThetaExpression (heegnerTau163 : ℂ) - (m : ℂ)‖ < 1 := by
    simpa [← htarget] using
      norm_kleinJThetaExpression_heegnerTau163_sub_target_lt_one
  rw [htarget]
  exact complex_int_eq_of_norm_sub_lt_one
    (cm_integrality_theta_expression_163 hlevel41)
    hclose

theorem kleinJThetaExpression_heegnerTau163_eq_target :
    kleinJThetaExpression (heegnerTau163 : ℂ) = heegnerJ163Target := by
  exact kleinJThetaExpression_heegnerTau163_eq_target_of_phi41_diag_div41 level41_input_cm163

/-- The theta-lambda q-expansion computation, pushed through the Legendre
`j`-map.  All algebraic reduction from `thetaLambda` to the theta expression
is already proved above; the only analytic input is
`kleinJThetaExpression_heegnerTau163_eq_target_of_phi41_diag_div41`. -/
theorem kleinJFromLambda_thetaLambda_heegnerTau163_eq_target_of_phi41_diag_div41
    (hlevel41 : evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0) :
    kleinJFromLambda (thetaLambda (heegnerTau163 : ℂ)) =
      heegnerJ163Target := by
  rw [kleinJFromLambda_thetaLambda_heegnerTau163_eq_thetaExpression,
    kleinJThetaExpression_heegnerTau163_eq_target_of_phi41_diag_div41 hlevel41]

theorem kleinJFromLambda_thetaLambda_heegnerTau163_eq_target :
    kleinJFromLambda (thetaLambda (heegnerTau163 : ℂ)) =
      heegnerJ163Target := by
  exact kleinJFromLambda_thetaLambda_heegnerTau163_eq_target_of_phi41_diag_div41 level41_input_cm163

/-- The target equality, repackaged as the class-polynomial root needed by
`CMEvaluationBridge`. -/
lemma kleinJFromLambda_thetaLambda_heegnerTau163_isRoot_of_phi41_diag_div41 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 →
    heegnerJ163ClassPolynomial.IsRoot
      (kleinJFromLambda (thetaLambda (heegnerTau163 : ℂ))) := by
  intro hlevel41
  rw [kleinJFromLambda_thetaLambda_heegnerTau163_eq_target_of_phi41_diag_div41 hlevel41]
  exact heegnerJ163Target_isRoot_classPolynomial

/-- The class-polynomial root statement for the actual Klein invariant,
obtained from the theta-lambda computation and the `j = J(λ)` bridge. -/
lemma kleinJ_heegnerTau163_isRoot_classPolynomial_of_phi41_diag_div41 :
    evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0 →
    heegnerJ163ClassPolynomial.IsRoot (kleinJ heegnerTau163) := by
  intro hlevel41
  rw [kleinJ_heegnerTau163_eq_kleinJFromLambda_thetaLambda]
  exact kleinJFromLambda_thetaLambda_heegnerTau163_isRoot_of_phi41_diag_div41 hlevel41

/-- The concrete CM evaluation:
`j((1 + i sqrt 163)/2) = -640320^3`. -/
theorem kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41_diag_div41
    (hlevel41 : evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0) :
    kleinJ heegnerTau163 = heegnerJ163Target :=
  heegnerJ163ClassPolynomial_isRoot_iff.mp
    (kleinJ_heegnerTau163_isRoot_classPolynomial_of_phi41_diag_div41 hlevel41)

theorem kleinJ_heegnerTau163_eq_heegnerJ163Target :
    kleinJ heegnerTau163 = heegnerJ163Target := by
  exact kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41_diag_div41 level41_input_cm163

/-- Named endpoint required downstream by the Chudnovsky development. -/
theorem KleinJCM163Statement_proof_of_phi41_diag_div41
    (hlevel41 : evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0) :
    KleinJCM163Statement :=
  KleinJCM163Statement.of_isRoot
    (kleinJ_heegnerTau163_isRoot_classPolynomial_of_phi41_diag_div41 hlevel41)

theorem KleinJCM163Statement_proof :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41 level41_input_cm163

theorem kleinJ_heegnerTau163_eq_heegnerJ163Target_of_sparse_bivariate_modular_polynomial
    (terms : List SparseBivarTerm)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC terms (kleinJ τ) (kleinJ τ') = 0)
    (hdiag : ∀ z : ℂ, evalSparseBivarDiagC terms z = evalPhi41DiagIsolatedC z) :
    kleinJ heegnerTau163 = heegnerJ163Target := by
  exact kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41_diag_div41
    (level41_input_of_sparse_bivariate_modular_polynomial terms hmod hdiag)

theorem kleinJ_heegnerTau163_eq_heegnerJ163Target_of_diag_certificate
    (terms : List SparseBivarTerm)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC terms (kleinJ τ) (kleinJ τ') = 0)
    (hpoly : sparseBivarDiagPolynomialC terms = phi41DiagIsolatedPolynomialC) :
    kleinJ heegnerTau163 = heegnerJ163Target := by
  exact kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41_diag_div41
    (level41_input_of_sparse_bivariate_modular_polynomial_with_diag_certificate
      terms hmod hpoly)

theorem kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41SparseTerms
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC phi41SparseTerms (kleinJ τ) (kleinJ τ') = 0) :
    kleinJ heegnerTau163 = heegnerJ163Target := by
  exact kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41_diag_div41
    (level41_input_of_phi41SparseTerms hmod)

theorem kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41SparseTerms_at_cm163
    (hmod : evalSparseBivarC phi41SparseTerms (kleinJ heegnerTau163)
      (kleinJ heegnerTau163_div41) = 0) :
    kleinJ heegnerTau163 = heegnerJ163Target := by
  exact kleinJ_heegnerTau163_eq_heegnerJ163Target_of_phi41_diag_div41
    (level41_input_of_phi41SparseTerms_at_cm163 hmod)

theorem KleinJCM163Statement_proof_of_sparse_bivariate_modular_polynomial
    (terms : List SparseBivarTerm)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC terms (kleinJ τ) (kleinJ τ') = 0)
    (hdiag : ∀ z : ℂ, evalSparseBivarDiagC terms z = evalPhi41DiagIsolatedC z) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_sparse_bivariate_modular_polynomial terms hmod hdiag)

theorem KleinJCM163Statement_proof_of_sparse_bivariate_modular_polynomial_with_diag_certificate
    (terms : List SparseBivarTerm)
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC terms (kleinJ τ) (kleinJ τ') = 0)
    (hpoly : sparseBivarDiagPolynomialC terms = phi41DiagIsolatedPolynomialC) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_sparse_bivariate_modular_polynomial_with_diag_certificate
      terms hmod hpoly)

theorem KleinJCM163Statement_proof_of_phi41SparseTerms
    (hmod : ∀ τ τ' : ℍ,
      DetMatrixTransformWitness 41 (τ : ℂ) (τ' : ℂ) →
        evalSparseBivarC phi41SparseTerms (kleinJ τ) (kleinJ τ') = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41SparseTerms hmod)

theorem KleinJCM163Statement_proof_of_phi41SparseTerms_at_cm163
    (hmod : evalSparseBivarC phi41SparseTerms (kleinJ heegnerTau163)
      (kleinJ heegnerTau163_div41) = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41SparseTerms_at_cm163 hmod)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_certificate
    (hdeltaCoeff :
      ∀ d : ℕ, PowerSeries.coeff (R := ℂ) d deltaQExpansion = deltaEulerCoeff d)
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_certificate
      hdeltaCoeff hcoeff hvalue)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_certificate_of_delta_hasSum
    (hdeltaSum :
      ∀ τ : ℍ,
        HasSum (fun d : ℕ =>
          deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
          (ModularForm.discriminant τ))
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_certificate_of_delta_hasSum
      hdeltaSum hcoeff hvalue)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_certificate_of_euler
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_certificate_of_euler
      hcoeff hvalue)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_certificate
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate
      hsturm hcert hvalue)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_range_certificate
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hvalue :
      phi41Level41ClearedQExpansion = 0 →
        evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41) = 0) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_range_certificate
      hsturm hcert hvalue)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_eval
      hsturm hcert hseries)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_range_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (heegnerTau163_div41 : ℂ) ^ n)
        (evalSparseBivarClearedC phi41SparseTerms 42 42
          (E4 heegnerTau163 ^ 3) (ModularForm.discriminant heegnerTau163)
          (E4 heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant heegnerTau163_div41))) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_range_eval
      hsturm hcert hseries)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate)
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval
      hsturm hcert hterms)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_range_sparse_term_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate)
    (hterms : phi41Level41SparseTermEvaluationCertificate) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_range_sparse_term_eval
      hsturm hcert hterms)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_factor_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_factor_eval hsturm hcert)

theorem KleinJCM163Statement_proof_of_phi41Level41ClearedQExpansion_sturm_range_factor_eval
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    KleinJCM163Statement := by
  exact KleinJCM163Statement_proof_of_phi41_diag_div41
    (level41_input_of_phi41Level41ClearedQExpansion_sturm_range_factor_eval hsturm hcert)

end Modular
end Number
end Ripple
