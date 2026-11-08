/-
  Ripple.Number.Frobenius.AperyAGFSharpFromFrobenius

  Phase 4: route the sharp `A''` denominator lower bound through the
  conifold Frobenius/connection-coefficient infrastructure instead of a
  coefficient-ratio lower bound.
-/

import Ripple.Number.Frobenius.AperyConifoldRatioSeries
import Ripple.Number.Frobenius.AperyInstance
import Ripple.Number.Frobenius.AperyACoefficientSharpLower
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

namespace Ripple.Number

open Filter
open Ripple.Number.Frobenius

/-- Left-hand conifold corridor in the shifted coordinate `t = z - z₁`. -/
def aperyConifoldLeftTInterval (δ : ℝ) : Set ℝ :=
  Set.Ioo (-δ) 0

/-- Closed Frobenius/Birkhoff inputs already available from the ratio family
and residual infrastructure. -/
lemma aperyFrobeniusRatioFamilyCoefficientControl_and_birkhoffSharpAsymptotics :
    AperyFrobeniusRatioFamilyCoefficientControl ∧
      AperyFrobeniusBirkhoffSharpAsymptotics := by
  let hcoef := aperyFrobeniusRatioFamilyCoefficientControl_proof
  exact ⟨hcoef, aperyFrobeniusBirkhoffSharpAsymptotics_proof hcoef⟩

/-- The ordinary Apéry `A` generating function has a nonzero `ρ = 1/2`
connection component at the conifold, with the sign that makes its second
derivative positive on the left corridor. -/
def AperyAOrdinarySeriesHasNonzeroHalfConnection : Prop :=
  ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧ a_half < 0 ∧
    Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)

/-- The local F5 copy of the Apéry `A` generating function is definitionally
the same coefficient series as the canonical Frobenius-side `aperyGFAReal`. -/
lemma aperyGFAReal_eq_canonical (z : ℝ) :
    aperyF5GFAReal z = Ripple.Number.Frobenius.aperyGFAReal z := by
  unfold aperyF5GFAReal Ripple.Number.Frobenius.aperyGFAReal aperyF5A Number.aperyA
  rfl

/-- Real-coefficient canonical Apéry `r(z) = 1 - 112z + 7z²`. -/
noncomputable def aperyRconifold : Polynomial ℝ :=
  Polynomial.monomial 0 1 + Polynomial.monomial 1 (-112 : ℝ) +
    Polynomial.monomial 2 7

/-- Real-coefficient canonical Apéry `s(z) = -5 + z`. -/
noncomputable def aperySconifold : Polynomial ℝ :=
  Polynomial.monomial 0 (-5 : ℝ) + Polynomial.monomial 1 1

/-- The full canonical Apéry differential operator in ordinary-derivative
form:

`S(z)·y + R(z)·y' + Q(z)·y'' + P(z)·y''' = 0`.

This is deliberately separated from the older reduced conifold operator
`aperyPsSeq 0 0 Q P`.  The reduced operator has the same indicial equation
at `z₁`, but it is not the differential equation satisfied by the ordinary
Apéry generating function `aperyGFAReal`; the lower-order `R,S` terms are
needed for ODE uniqueness and connection coefficients. -/
noncomputable def aperyCanonicalPsSeq : ℕ → Polynomial ℝ :=
  aperyPsSeq aperySconifold aperyRconifold
    Number.aperyQconifold Number.aperyPconifold

@[simp] lemma aperyCanonicalPsSeq_zero :
    aperyCanonicalPsSeq 0 = aperySconifold := rfl

@[simp] lemma aperyCanonicalPsSeq_one :
    aperyCanonicalPsSeq 1 = aperyRconifold := rfl

@[simp] lemma aperyCanonicalPsSeq_two :
    aperyCanonicalPsSeq 2 = Number.aperyQconifold := rfl

@[simp] lemma aperyCanonicalPsSeq_three :
    aperyCanonicalPsSeq 3 = Number.aperyPconifold := rfl

@[simp] lemma aperyCanonicalPsSeq_four_add (n : ℕ) :
    aperyCanonicalPsSeq (n + 4) = 0 := rfl

private lemma taylorShift_eval_at (p : Polynomial ℝ) (z₁ t : ℝ) :
    (taylorShift p z₁).eval t = p.eval (z₁ - t) := by
  unfold taylorShift
  rw [Polynomial.eval_comp]
  simp

lemma aperyCanonicalPsSeq_leading_eval_z1 :
    (aperyCanonicalPsSeq 3).eval Number.aperyConifoldZ1Poly = 0 := by
  simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_eval_z1

lemma aperyCanonical_simpleZero_half :
    simpleZeroIndicialPoly (aperyCanonicalPsSeq 2) (aperyCanonicalPsSeq 3)
      Number.aperyConifoldZ1Poly 2 (1 / 2 : ℝ) = 0 := by
  simpa [aperyCanonicalPsSeq] using
    (show simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
      Number.aperyConifoldZ1Poly 2 (1 / 2 : ℝ) = 0 by
      rw [← Ripple.Number.Frobenius.aperyPatternIndicialPoly_eq_simpleZero]
      exact (Ripple.Number.Frobenius.aperyPatternIndicialPoly_apery_eq_zero_iff _).mpr
        (Or.inr (Or.inl rfl)))

lemma aperyCanonical_no_integer_shift_half :
    ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (aperyCanonicalPsSeq 2) (aperyCanonicalPsSeq 3)
        Number.aperyConifoldZ1Poly 2 ((1 / 2 : ℝ) + m) ≠ 0 := by
  intro m hm
  simpa [aperyCanonicalPsSeq] using
    (Ripple.Number.Frobenius.apery_no_integer_shift_half m hm)

lemma aperyCanonical_simpleZero_one :
    simpleZeroIndicialPoly (aperyCanonicalPsSeq 2) (aperyCanonicalPsSeq 3)
      Number.aperyConifoldZ1Poly 2 (1 : ℝ) = 0 := by
  simpa [aperyCanonicalPsSeq] using
    (show simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
      Number.aperyConifoldZ1Poly 2 (1 : ℝ) = 0 by
      rw [← Ripple.Number.Frobenius.aperyPatternIndicialPoly_eq_simpleZero]
      exact (Ripple.Number.Frobenius.aperyPatternIndicialPoly_apery_eq_zero_iff _).mpr
        (Or.inr (Or.inr rfl)))

lemma aperyCanonical_no_integer_shift_one :
    ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (aperyCanonicalPsSeq 2) (aperyCanonicalPsSeq 3)
        Number.aperyConifoldZ1Poly 2 ((1 : ℝ) + m) ≠ 0 := by
  intro m hm
  simpa [aperyCanonicalPsSeq] using
    (Ripple.Number.Frobenius.apery_no_integer_shift_one m hm)

lemma aperyCanonical_simpleZero_zero :
    simpleZeroIndicialPoly (aperyCanonicalPsSeq 2) (aperyCanonicalPsSeq 3)
      Number.aperyConifoldZ1Poly 2 (0 : ℝ) = 0 := by
  simpa [aperyCanonicalPsSeq] using
    (show simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
      Number.aperyConifoldZ1Poly 2 (0 : ℝ) = 0 by
      rw [← Ripple.Number.Frobenius.aperyPatternIndicialPoly_eq_simpleZero]
      exact (Ripple.Number.Frobenius.aperyPatternIndicialPoly_apery_eq_zero_iff _).mpr
        (Or.inl rfl))

lemma aperyCanonical_no_integer_shift_zero_from_two :
    ∀ m : ℕ, 2 ≤ m →
      simpleZeroIndicialPoly (aperyCanonicalPsSeq 2) (aperyCanonicalPsSeq 3)
        Number.aperyConifoldZ1Poly 2 ((m : ℝ)) ≠ 0 := by
  intro m hm hzero
  have hroot :
      (m : ℝ) = 0 ∨ (m : ℝ) = (1 / 2 : ℝ) ∨ (m : ℝ) = 1 := by
    apply (Ripple.Number.Frobenius.aperyPatternIndicialPoly_apery_eq_zero_iff
      (m : ℝ)).mp
    rw [Ripple.Number.Frobenius.aperyPatternIndicialPoly_eq_simpleZero]
    simpa [aperyCanonicalPsSeq] using hzero
  rcases hroot with h | h | h
  · have hm_pos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
    linarith
  · have hm_ge : (1 : ℝ) ≤ m := by
      exact_mod_cast (by omega : 1 ≤ m)
    linarith
  · have hm_ge : (2 : ℝ) ≤ m := by
      exact_mod_cast hm
    linarith

open PowerSeries in
private lemma aperyCanonical_zero_resonant_obstruction_coeff_two :
    PowerSeries.coeff (R := ℝ) 2
      (substLHSGen aperyCanonicalPsSeq 3 Number.aperyConifoldZ1Poly 0
        (1 : PowerSeries ℝ)) = 0 := by
  rw [coeff_substLHSGen_one_explicit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [fallingFactorial]

open PowerSeries in
private lemma aperyCanonical_zero_frobeniusCoeff_one (c₀ : ℝ) :
    frobeniusCoeff aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 0 c₀ 1 = 0 := by
  rw [frobeniusCoeff, frobeniusBuilder]
  simp only [Nat.cast_one, zero_add]
  have hden : ((-1 : ℝ) ^ 2 *
        simpleZeroIndicialPoly (aperyCanonicalPsSeq 2)
          (aperyCanonicalPsSeq (2 + 1))
          Number.aperyConifoldZ1Poly 2 1) = 0 := by
    rw [show aperyCanonicalPsSeq (2 + 1) = aperyCanonicalPsSeq 3 by rfl]
    rw [aperyCanonical_simpleZero_one]
    ring
  rw [hden, div_zero]

open PowerSeries in
private lemma aperyCanonical_zero_substLHS_coeff_two (c₀ : ℝ) :
    PowerSeries.coeff (R := ℝ) 2
      (substLHSGen aperyCanonicalPsSeq 3 Number.aperyConifoldZ1Poly 0
        (frobeniusSolution aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀)) = 0 := by
  rw [coeff_succ_substLHSGen_linearity aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 0 1 _
    aperyCanonicalPsSeq_leading_eval_z1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [coeff_frobeniusSolution, frobeniusCoeff_zero]
  have hc1 : PowerSeries.coeff (R := ℝ) 1
      (frobeniusSolution aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀) = 0 := by
    rw [coeff_frobeniusSolution]
    exact aperyCanonical_zero_frobeniusCoeff_one c₀
  rw [hc1, zero_mul, add_zero]
  rw [show PowerSeries.coeff (R := ℝ) 2
      (substLHSGen aperyCanonicalPsSeq 3 Number.aperyConifoldZ1Poly 0
        ((PowerSeries.X : PowerSeries ℝ) ^ 0)) = 0 by
    simpa using aperyCanonical_zero_resonant_obstruction_coeff_two]
  ring

open PowerSeries in
/-- The canonical `ρ = 0` branch is resonant with `ρ = 1`, so the generic
non-resonance theorem does not apply.  In the Apéry canonical operator the
single resonant obstruction at level `1` vanishes, and the builder chooses
the normalized regular branch with coefficient `c₁ = 0`; all later levels
are non-resonant. -/
lemma aperyCanonical_frobeniusSolution_is_solution_zero_regular (c₀ : ℝ) :
    PowerSeries.coeff (R := ℝ) 0
        (frobeniusSolution aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly (0 : ℝ) c₀) = c₀ ∧
      ∀ k, PowerSeries.coeff (R := ℝ) k
        (substLHSGen aperyCanonicalPsSeq 3 Number.aperyConifoldZ1Poly
          (0 : ℝ)
          (frobeniusSolution aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (0 : ℝ) c₀)) = 0 := by
  refine ⟨by simp, ?_⟩
  intro k
  match k with
  | 0 =>
      exact coeff_zero_substLHSGen_frobeniusSolution aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀ aperyCanonicalPsSeq_leading_eval_z1
  | 1 =>
      exact coeff_one_substLHSGen_frobeniusSolution aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀ aperyCanonicalPsSeq_leading_eval_z1
        aperyCanonical_simpleZero_zero
  | m + 2 =>
      cases m with
      | zero =>
          exact aperyCanonical_zero_substLHS_coeff_two c₀
      | succ m =>
          have hnr :
              simpleZeroIndicialPoly (aperyCanonicalPsSeq 2)
                (aperyCanonicalPsSeq 3) Number.aperyConifoldZ1Poly 2
                ((0 : ℝ) + (((m + 1) + 1 : ℕ) : ℝ)) ≠ 0 := by
            rw [zero_add]
            exact aperyCanonical_no_integer_shift_zero_from_two
              ((m + 1) + 1) (by omega)
          exact coeff_frobeniusSolution_annihilates_succ
            aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 0 c₀
            (m + 1) aperyCanonicalPsSeq_leading_eval_z1 hnr

open PowerSeries in
lemma aperyCanonical_frobeniusSolution_is_solution_half (c₀ : ℝ) :
    PowerSeries.coeff (R := ℝ) 0
        (frobeniusSolution aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly (1 / 2 : ℝ) c₀) = c₀ ∧
      ∀ k, PowerSeries.coeff (R := ℝ) k
        (substLHSGen aperyCanonicalPsSeq 3 Number.aperyConifoldZ1Poly
          (1 / 2 : ℝ)
          (frobeniusSolution aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2 : ℝ) c₀)) = 0 := by
  exact frobeniusSolution_is_solution aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly (1 / 2 : ℝ) c₀
    aperyCanonicalPsSeq_leading_eval_z1
    aperyCanonical_simpleZero_half
    aperyCanonical_no_integer_shift_half

open PowerSeries in
lemma aperyCanonical_frobeniusSolution_is_solution_one (c₀ : ℝ) :
    PowerSeries.coeff (R := ℝ) 0
        (frobeniusSolution aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly (1 : ℝ) c₀) = c₀ ∧
      ∀ k, PowerSeries.coeff (R := ℝ) k
        (substLHSGen aperyCanonicalPsSeq 3 Number.aperyConifoldZ1Poly
          (1 : ℝ)
          (frobeniusSolution aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 : ℝ) c₀)) = 0 := by
  exact frobeniusSolution_is_solution aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly (1 : ℝ) c₀
    aperyCanonicalPsSeq_leading_eval_z1
    aperyCanonical_simpleZero_one
    aperyCanonical_no_integer_shift_one

private lemma aperySconifold_natDegree_le : aperySconifold.natDegree ≤ 1 := by
  unfold aperySconifold
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  exact max_le
    ((Polynomial.natDegree_monomial_le (-5 : ℝ)).trans (by norm_num))
    (Polynomial.natDegree_monomial_le (m := 1) (1 : ℝ))

private lemma aperyRconifold_natDegree_le : aperyRconifold.natDegree ≤ 2 := by
  unfold aperyRconifold
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ (Polynomial.natDegree_monomial_le (m := 2) (7 : ℝ))
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  exact max_le
    ((Polynomial.natDegree_monomial_le (1 : ℝ)).trans (by norm_num))
    ((Polynomial.natDegree_monomial_le (m := 1) (-112 : ℝ)).trans (by norm_num))

private lemma aperySconifold_taylorShift_coeff_abs_le_1000 (ℓ : ℕ) :
    |Polynomial.coeff (taylorShift aperySconifold
      Number.aperyConifoldZ1Poly) ℓ| ≤ (1000 : ℝ) := by
  by_cases hℓ : 2 ≤ ℓ
  · rw [taylorShift_coeff_eq_zero_of_natDegree_lt
      aperySconifold Number.aperyConifoldZ1Poly ℓ
      (lt_of_le_of_lt aperySconifold_natDegree_le (by omega)), abs_zero]
    norm_num
  push_neg at hℓ
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  interval_cases ℓ
  · rw [taylorShift_coeff_zero]
    unfold aperySconifold Number.aperyConifoldZ1Poly
    simp [Polynomial.eval_add, Polynomial.eval_monomial]
    rw [abs_le]
    constructor <;> nlinarith [hsq, hsqrt_nonneg]
  · rw [taylorShift_coeff_one]
    unfold aperySconifold
    simp [Polynomial.derivative_add, Polynomial.derivative_monomial,
      Polynomial.eval_add, Polynomial.eval_monomial]

private lemma aperyRconifold_taylorShift_coeff_abs_le_1000 (ℓ : ℕ) :
    |Polynomial.coeff (taylorShift aperyRconifold
      Number.aperyConifoldZ1Poly) ℓ| ≤ (1000 : ℝ) := by
  by_cases hℓ : 3 ≤ ℓ
  · rw [taylorShift_coeff_eq_zero_of_natDegree_lt
      aperyRconifold Number.aperyConifoldZ1Poly ℓ
      (lt_of_le_of_lt aperyRconifold_natDegree_le (by omega)), abs_zero]
    norm_num
  push_neg at hℓ
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  interval_cases ℓ
  · rw [taylorShift_coeff_zero]
    unfold aperyRconifold Number.aperyConifoldZ1Poly
    simp [Polynomial.eval_add, Polynomial.eval_monomial]
    rw [abs_le]
    constructor <;> nlinarith [hsq, hsqrt_nonneg]
  · rw [taylorShift_coeff_one]
    unfold aperyRconifold Number.aperyConifoldZ1Poly
    simp [Polynomial.derivative_add, Polynomial.derivative_monomial,
      Polynomial.eval_add, Polynomial.eval_monomial]
    rw [abs_le]
    constructor <;> nlinarith [hsq, hsqrt_nonneg]
  · rw [taylorShift_coeff_two]
    unfold aperyRconifold
    simp [Polynomial.derivative_add, Polynomial.derivative_monomial,
      Polynomial.eval_add, Polynomial.eval_monomial]
    norm_num

private lemma aperyCanonical_common_B_bound :
    ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (aperyCanonicalPsSeq j')
        Number.aperyConifoldZ1Poly) ℓ| ≤ (1000 : ℝ) := by
  intro j' hj' ℓ
  have hj'_lt : j' < 4 := by simpa using hj'
  interval_cases j'
  · simpa [aperyCanonicalPsSeq] using
      aperySconifold_taylorShift_coeff_abs_le_1000 ℓ
  · simpa [aperyCanonicalPsSeq] using
      aperyRconifold_taylorShift_coeff_abs_le_1000 ℓ
  · exact (Ripple.Number.Frobenius.aperyQconifold_taylorShift_coeff_abs_le ℓ).trans
      (by norm_num)
  · exact (Ripple.Number.Frobenius.aperyPconifold_taylorShift_coeff_abs_le ℓ).trans
      (by norm_num)

private lemma aperyCanonical_local_radius_exists :
    ∃ s : ℝ, 0 < s ∧
      s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
        |Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative Number.aperyPconifold)|) < 1 := by
  let K : ℝ := 1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
    |Polynomial.eval Number.aperyConifoldZ1Poly
      (Polynomial.derivative Number.aperyPconifold)|
  have hden_pos : 0 <
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)| :=
    Number.aperyPconifold_deriv_eval_z1_abs_pos
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  dsimp [K]
  field_simp [hK_pos.ne']
  linarith

private noncomputable def yAperyCanonicalHalf (c₀ : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (-t) * frobeniusValue aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly (1 / 2) c₀ t

private noncomputable def yAperyCanonicalZero (c₀ : ℝ) (t : ℝ) : ℝ :=
  frobeniusValue aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 0 c₀ t

private noncomputable def yAperyCanonicalOne (c₀ : ℝ) (t : ℝ) : ℝ :=
  t * frobeniusValue aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 1 c₀ t

private noncomputable def aperyCanonicalBranchTriple
    (a₀ a_half a₁ t : ℝ) : ℝ :=
  yAperyCanonicalZero a₀ t + yAperyCanonicalHalf a_half t +
    yAperyCanonicalOne a₁ t

/-!
`substLHSGen` uses the Frobenius variable `τ = z₁ - z`; see
`taylorShift`, where `taylorShift p z₁` is `p(z₁ - τ)`.  On the left
corridor our external coordinate is still `t = z - z₁ < 0`, so the
correct canonical Frobenius branches must evaluate the coefficient
series at `τ = -t`.  The older `aperyCanonicalBranchTriple` above keeps
the historical `t`-direct convention only for already-proved local
estimates; the ODE/connection route below uses the `Left` variants. -/

private noncomputable def yAperyCanonicalLeftHalf (c₀ : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (-t) * frobeniusValue aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly (1 / 2) c₀ (-t)

private noncomputable def yAperyCanonicalLeftZero (c₀ : ℝ) (t : ℝ) : ℝ :=
  frobeniusValue aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 0 c₀ (-t)

private noncomputable def yAperyCanonicalLeftOne (c₀ : ℝ) (t : ℝ) : ℝ :=
  (-t) * frobeniusValue aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 1 c₀ (-t)

private noncomputable def aperyCanonicalLeftBranchTriple
    (a₀ a_half a₁ t : ℝ) : ℝ :=
  yAperyCanonicalLeftZero a₀ t + yAperyCanonicalLeftHalf a_half t +
    yAperyCanonicalLeftOne a₁ t

private def IsCanonicalAperyConnectionCoeffsOn
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I,
    f (Number.aperyConifoldZ1Poly + t) =
      aperyCanonicalBranchTriple a₀ a_half a₁ t

private def IsCanonicalLeftAperyConnectionCoeffsOn
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I,
    f (Number.aperyConifoldZ1Poly + t) =
      aperyCanonicalLeftBranchTriple a₀ a_half a₁ t

/-- Canonical full-operator version of the half-connection statement.  Unlike
`AperyAOrdinarySeriesHasNonzeroHalfConnection`, this is stated with the
true Apéry operator `S,R,Q,P`, not the older reduced conifold operator. -/
def AperyAOrdinarySeriesHasCanonicalNonzeroHalfConnection : Prop :=
  ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧ a_half < 0 ∧
    IsCanonicalAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)

/-- Coordinate-correct canonical connection statement.  Here the external
left-corridor coordinate is `t = z - z₁ < 0`, but the Frobenius series is
evaluated at `τ = z₁ - z = -t`, matching the definition of `taylorShift`
and `substLHSGen`. -/
def AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection : Prop :=
  ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧ a_half < 0 ∧
    IsCanonicalLeftAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)

private lemma aperyCanonicalHalf_small :
    ∀ m : ℕ, 9 ≤ m →
      (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
  intro m hm
  have := Number.aperyConifold_small_H m (by omega)
  push_cast at this ⊢
  exact this

private lemma aperyCanonicalHalf_large :
    ∀ m : ℕ, 9 ≤ m →
      3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
  intro m hm
  have := Number.aperyConifold_large_H m (by omega)
  push_cast at this ⊢
  exact this

private lemma aperyCanonicalHalf_threshold :
    ∀ m : ℕ, 9 ≤ m →
      2 * |(aperyCanonicalPsSeq 2).eval Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
            Number.aperyConifoldZ1Poly| *
          (((m + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
  intro m hm
  change
      2 * |Number.aperyQconifold.eval Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative Number.aperyPconifold).eval
            Number.aperyConifoldZ1Poly| *
          (((m + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ))
  have := Number.aperyConifold_threshold_H m (by omega)
  push_cast at this ⊢
  exact this

private noncomputable def aperyConifoldZ2Poly : ℝ :=
  17 + 12 * Real.sqrt 2

private lemma aperyConifoldZ1_add_z2 :
    Number.aperyConifoldZ1Poly + aperyConifoldZ2Poly = 34 := by
  unfold Number.aperyConifoldZ1Poly aperyConifoldZ2Poly
  ring

private lemma aperyConifoldZ1_mul_z2 :
    Number.aperyConifoldZ1Poly * aperyConifoldZ2Poly = 1 := by
  unfold Number.aperyConifoldZ1Poly aperyConifoldZ2Poly
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  linarith

private lemma aperyConifoldZ1_lt_z2 :
    Number.aperyConifoldZ1Poly < aperyConifoldZ2Poly := by
  unfold Number.aperyConifoldZ1Poly aperyConifoldZ2Poly
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  linarith

private lemma aperyPconifold_eval_factor (z : ℝ) :
    Polynomial.eval z Number.aperyPconifold =
      z ^ 2 * (z - Number.aperyConifoldZ1Poly) *
        (z - aperyConifoldZ2Poly) := by
  unfold Number.aperyPconifold Number.aperyConifoldZ1Poly aperyConifoldZ2Poly
  simp [Polynomial.eval_add, Polynomial.eval_monomial]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ring_nf
  rw [h2]
  ring

lemma aperyPconifold_eval_pos_of_pos_lt_z1 {z : ℝ}
    (hz_pos : 0 < z) (hz_lt : z < Number.aperyConifoldZ1Poly) :
    0 < Polynomial.eval z Number.aperyPconifold := by
  rw [aperyPconifold_eval_factor]
  have hz_sq : 0 < z ^ 2 := sq_pos_of_ne_zero (ne_of_gt hz_pos)
  have hz_z1 : z - Number.aperyConifoldZ1Poly < 0 := by linarith
  have hz_z2 : z - aperyConifoldZ2Poly < 0 := by
    have hz1z2 := aperyConifoldZ1_lt_z2
    linarith
  have hprod : 0 < (z - Number.aperyConifoldZ1Poly) * (z - aperyConifoldZ2Poly) :=
    mul_pos_of_neg_of_neg hz_z1 hz_z2
  convert mul_pos hz_sq hprod using 1
  ring

lemma aperyPconifold_eval_ne_zero_of_pos_lt_z1 {z : ℝ}
    (hz_pos : 0 < z) (hz_lt : z < Number.aperyConifoldZ1Poly) :
    Polynomial.eval z Number.aperyPconifold ≠ 0 :=
  ne_of_gt (aperyPconifold_eval_pos_of_pos_lt_z1 hz_pos hz_lt)

lemma aperyPconifold_eval_ne_zero_on_left_corridor
    {δ t : ℝ} (hδ_le : δ ≤ Number.aperyConifoldZ1Poly)
    (ht : t ∈ aperyConifoldLeftTInterval δ) :
    Polynomial.eval (Number.aperyConifoldZ1Poly + t)
        Number.aperyPconifold ≠ 0 := by
  rcases ht with ⟨ht_left, ht_right⟩
  refine aperyPconifold_eval_ne_zero_of_pos_lt_z1 ?_ ?_
  · linarith
  · linarith

private noncomputable abbrev aperyGFASeries :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (Number.aperyA n : ℝ))

private noncomputable abbrev aperyGFADerivSeries :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => ((n : ℝ) + 1) * (Number.aperyA (n + 1) : ℝ))

private noncomputable abbrev aperyGFASecondDerivSeries :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
        (Number.aperyA (n + 2) : ℝ))

private noncomputable abbrev aperyGFAThirdDerivSeries :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ =>
      (((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1)) *
        (Number.aperyA (n + 3) : ℝ))

private noncomputable abbrev evalAtOneCLM :
    (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.evalL ℝ ℝ ℝ 1

private lemma aperyGFAReal_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall Ripple.Number.Frobenius.aperyGFAReal
      aperyGFASeries 0 (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
  change HasFPowerSeriesOnBall Ripple.Number.Frobenius.aperyGFAReal
    (FormalMultilinearSeries.ofScalars ℝ
      Ripple.Number.Frobenius.aperyGFAReal_regularDisk.coeffs)
    Ripple.Number.Frobenius.aperyGFAReal_regularDisk.center
    (ENNReal.ofReal Ripple.Number.Frobenius.aperyGFAReal_regularDisk.radius)
  exact {
    r_le := by
      exact Ripple.Number.Frobenius.aperyGFAReal_regularDisk.le_radius_ofScalars
        Ripple.Number.Frobenius.aperyGFAReal_regularDisk_summable_sub_radius
    r_pos := by
      exact ENNReal.ofReal_pos.mpr
        Ripple.Number.Frobenius.aperyGFAReal_regularDisk.radius_pos
    hasSum := by
      intro y hy
      exact Ripple.Number.Frobenius.aperyGFAReal_regularDisk.hasSum_ofScalars hy }

private lemma aperyGFAReal_deriv_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (deriv Ripple.Number.Frobenius.aperyGFAReal)
      aperyGFADerivSeries 0
      (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
  have h0 : HasFPowerSeriesOnBall (deriv Ripple.Number.Frobenius.aperyGFAReal)
      (evalAtOneCLM.compFormalMultilinearSeries
        aperyGFASeries.derivSeries) 0
      (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    refine
      (evalAtOneCLM.comp_hasFPowerSeriesOnBall
        aperyGFAReal_hasFPowerSeriesOnBall.fderiv).congr
        (g := deriv Ripple.Number.Frobenius.aperyGFAReal) ?_
    intro z _hz
    simp [evalAtOneCLM]
  convert h0 using 2
  ext n
  simp [aperyGFASeries, aperyGFADerivSeries, evalAtOneCLM,
    FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars]

private lemma aperyGFAReal_second_deriv_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal))
      aperyGFASecondDerivSeries 0
      (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
  have h0 : HasFPowerSeriesOnBall
      (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal))
      (evalAtOneCLM.compFormalMultilinearSeries
        aperyGFADerivSeries.derivSeries) 0
      (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    refine
      (evalAtOneCLM.comp_hasFPowerSeriesOnBall
        aperyGFAReal_deriv_hasFPowerSeriesOnBall.fderiv).congr
        (g := deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)) ?_
    intro z _hz
    simp [evalAtOneCLM]
  convert h0 using 2
  ext n
  simp [aperyGFADerivSeries, aperyGFASecondDerivSeries, evalAtOneCLM,
    FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars]
  ring

private lemma aperyGFAReal_third_deriv_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall
      (deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)))
      aperyGFAThirdDerivSeries 0
      (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
  have h0 : HasFPowerSeriesOnBall
      (deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)))
      (evalAtOneCLM.compFormalMultilinearSeries
        aperyGFASecondDerivSeries.derivSeries) 0
      (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    refine
      (evalAtOneCLM.comp_hasFPowerSeriesOnBall
        aperyGFAReal_second_deriv_hasFPowerSeriesOnBall.fderiv).congr
        (g := deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal))) ?_
    intro z _hz
    simp [evalAtOneCLM]
  convert h0 using 2
  ext n
  simp [aperyGFASecondDerivSeries, aperyGFAThirdDerivSeries, evalAtOneCLM,
    FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars]
  ring

private lemma ennreal_coe_nnnorm_real_eq_ofReal_abs (z : ℝ) :
    (↑‖z‖₊ : ENNReal) = ENNReal.ofReal |z| := by
  rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg z)]
  congr

private lemma aperyGFAReal_hasDerivAt
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    HasDerivAt Ripple.Number.Frobenius.aperyGFAReal
      (deriv Ripple.Number.Frobenius.aperyGFAReal z) z := by
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  have hy :
      (↑‖z‖₊ : ENNReal) <
        ENNReal.ofReal Number.aperyConifoldZ1Poly := by
    rw [ennreal_coe_nnnorm_real_eq_ofReal_abs]
    rw [ENNReal.ofReal_lt_ofReal_iff hz1_pos]
    exact hz
  have hfd :=
    HasFPowerSeriesOnBall.hasFDerivAt
      aperyGFAReal_hasFPowerSeriesOnBall (y := z) hy
  have hd := hfd.hasDerivAt
  have hd' :
      HasDerivAt Ripple.Number.Frobenius.aperyGFAReal
        (((continuousMultilinearCurryFin1 ℝ ℝ ℝ)
          (aperyGFASeries.changeOrigin z 1)) 1) z := by
    simpa [zero_add] using hd
  convert hd' using 1
  exact hd'.deriv

private lemma aperyGFAReal_deriv_hasDerivAt
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    HasDerivAt (deriv Ripple.Number.Frobenius.aperyGFAReal)
      (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) z) z := by
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  have hy :
      (↑‖z‖₊ : ENNReal) <
        ENNReal.ofReal Number.aperyConifoldZ1Poly := by
    rw [ennreal_coe_nnnorm_real_eq_ofReal_abs]
    rw [ENNReal.ofReal_lt_ofReal_iff hz1_pos]
    exact hz
  have hfd :=
    HasFPowerSeriesOnBall.hasFDerivAt
      aperyGFAReal_deriv_hasFPowerSeriesOnBall (y := z) hy
  have hd := hfd.hasDerivAt
  have hd' :
      HasDerivAt (deriv Ripple.Number.Frobenius.aperyGFAReal)
        (((continuousMultilinearCurryFin1 ℝ ℝ ℝ)
          (aperyGFADerivSeries.changeOrigin z 1)) 1) z := by
    simpa [zero_add] using hd
  convert hd' using 1
  exact hd'.deriv

private lemma aperyGFAReal_second_deriv_hasDerivAt
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    HasDerivAt (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal))
      (deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)) z) z := by
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  have hy :
      (↑‖z‖₊ : ENNReal) <
        ENNReal.ofReal Number.aperyConifoldZ1Poly := by
    rw [ennreal_coe_nnnorm_real_eq_ofReal_abs]
    rw [ENNReal.ofReal_lt_ofReal_iff hz1_pos]
    exact hz
  have hfd :=
    HasFPowerSeriesOnBall.hasFDerivAt
      aperyGFAReal_second_deriv_hasFPowerSeriesOnBall (y := z) hy
  have hd := hfd.hasDerivAt
  have hd' :
      HasDerivAt (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal))
        (((continuousMultilinearCurryFin1 ℝ ℝ ℝ)
          (aperyGFASecondDerivSeries.changeOrigin z 1)) 1) z := by
    simpa [zero_add] using hd
  convert hd' using 1
  exact hd'.deriv

private lemma aperyGFAReal_eq_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Ripple.Number.Frobenius.aperyGFAReal z =
      ∑' n : ℕ, (Number.aperyA n : ℝ) * z ^ n := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_hasFPowerSeriesOnBall.sum (y := z) hy
  rw [zero_add] at hsum
  rw [hsum]
  change
    FormalMultilinearSeries.ofScalarsSum (E := ℝ)
      (fun n : ℕ => (Number.aperyA n : ℝ)) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp [smul_eq_mul]

private lemma aperyGFAReal_deriv_eq_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    deriv Ripple.Number.Frobenius.aperyGFAReal z =
      ∑' n : ℕ,
        (((n : ℝ) + 1) * (Number.aperyA (n + 1) : ℝ)) * z ^ n := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_deriv_hasFPowerSeriesOnBall.sum (y := z) hy
  rw [zero_add] at hsum
  rw [hsum]
  change
    FormalMultilinearSeries.ofScalarsSum (E := ℝ)
      (fun n : ℕ =>
        (((n : ℝ) + 1) * (Number.aperyA (n + 1) : ℝ))) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp [smul_eq_mul]

private lemma aperyGFAReal_summable_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Summable (fun n : ℕ => (Number.aperyA n : ℝ) * z ^ n) := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_hasFPowerSeriesOnBall.hasSum hy
  exact hsum.summable.congr (fun n => by
    simp [aperyGFASeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
    ring)

private lemma aperyGFAReal_deriv_summable_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 1) * (Number.aperyA (n + 1) : ℝ)) * z ^ n) := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_deriv_hasFPowerSeriesOnBall.hasSum hy
  exact hsum.summable.congr (fun n => by
    simp [aperyGFADerivSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
    ring)

private lemma aperyGFAReal_second_deriv_eq_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) z =
      ∑' n : ℕ,
        (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
          (Number.aperyA (n + 2) : ℝ) * z ^ n := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_second_deriv_hasFPowerSeriesOnBall.sum (y := z) hy
  rw [zero_add] at hsum
  rw [hsum]
  change
    FormalMultilinearSeries.ofScalarsSum (E := ℝ)
      (fun n : ℕ =>
        (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
          (Number.aperyA (n + 2) : ℝ)) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp [smul_eq_mul]

private lemma aperyGFAReal_second_deriv_summable_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
        (Number.aperyA (n + 2) : ℝ) * z ^ n) := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_second_deriv_hasFPowerSeriesOnBall.hasSum hy
  exact hsum.summable.congr (fun n => by
    simp [aperyGFASecondDerivSeries, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_assoc]
    ring)

private lemma aperyGFAReal_third_deriv_eq_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)) z =
      ∑' n : ℕ,
        (((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1)) *
          (Number.aperyA (n + 3) : ℝ) * z ^ n := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_third_deriv_hasFPowerSeriesOnBall.sum (y := z) hy
  rw [zero_add] at hsum
  rw [hsum]
  change
    FormalMultilinearSeries.ofScalarsSum (E := ℝ)
      (fun n : ℕ =>
        (((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1)) *
          (Number.aperyA (n + 3) : ℝ)) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp [smul_eq_mul]

private lemma aperyGFAReal_third_deriv_summable_series
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1)) *
        (Number.aperyA (n + 3) : ℝ) * z ^ n) := by
  have hy :
      z ∈ Metric.eball (0 : ℝ)
        (ENNReal.ofReal Number.aperyConifoldZ1Poly) := by
    rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hz
  have hsum := aperyGFAReal_third_deriv_hasFPowerSeriesOnBall.hasSum hy
  exact hsum.summable.congr (fun n => by
    simp [aperyGFAThirdDerivSeries, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_assoc]
    ring)

private lemma tsum_mul_pow_shift (f : ℕ → ℝ) (z : ℝ) (k : ℕ)
    (hf : Summable (fun n : ℕ => f n * z ^ n)) :
    z ^ k * (∑' n : ℕ, f n * z ^ n) =
      ∑' n : ℕ, (if k ≤ n then f (n - k) else 0) * z ^ n := by
  let g : ℕ → ℝ := fun n => (if k ≤ n then f (n - k) else 0) * z ^ n
  have htail_eq : ∀ n : ℕ, g (n + k) = z ^ k * (f n * z ^ n) := by
    intro n
    simp [g]
    rw [pow_add]
    ring
  have htail_summable : Summable (fun n : ℕ => g (n + k)) := by
    refine (Summable.mul_left (z ^ k) hf).congr ?_
    intro n
    rw [htail_eq]
  have hg : Summable g := (summable_nat_add_iff k).mp htail_summable
  have hfirst : ∑ i ∈ Finset.range k, g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    simp [g, not_le_of_gt hik]
  have hsum := Summable.sum_add_tsum_nat_add k hg
  have htail_tsum :
      (∑' n : ℕ, g (n + k)) =
        z ^ k * (∑' n : ℕ, f n * z ^ n) := by
    rw [tsum_congr htail_eq, Summable.tsum_mul_left (z ^ k) hf]
  calc
    z ^ k * (∑' n : ℕ, f n * z ^ n) = ∑' n : ℕ, g (n + k) :=
      htail_tsum.symm
    _ = ∑' n : ℕ, g n := by linarith
    _ = ∑' n : ℕ, (if k ≤ n then f (n - k) else 0) * z ^ n := rfl

private lemma summable_mul_pow_shift (f : ℕ → ℝ) (z : ℝ) (k : ℕ)
    (hf : Summable (fun n : ℕ => f n * z ^ n)) :
    Summable (fun n : ℕ => (if k ≤ n then f (n - k) else 0) * z ^ n) := by
  let g : ℕ → ℝ := fun n => (if k ≤ n then f (n - k) else 0) * z ^ n
  have htail_eq : ∀ n : ℕ, g (n + k) = z ^ k * (f n * z ^ n) := by
    intro n
    simp [g]
    rw [pow_add]
    ring
  have htail_summable : Summable (fun n : ℕ => g (n + k)) := by
    refine (Summable.mul_left (z ^ k) hf).congr ?_
    intro n
    rw [htail_eq]
  exact (summable_nat_add_iff k).mp htail_summable

private lemma tsum_shifted_linear_three (f : ℕ → ℝ) (z a b c : ℝ) (k l m : ℕ)
    (hf : Summable (fun n : ℕ => f n * z ^ n)) :
    a * (z ^ k * (∑' n : ℕ, f n * z ^ n)) +
        b * (z ^ l * (∑' n : ℕ, f n * z ^ n)) +
        c * (z ^ m * (∑' n : ℕ, f n * z ^ n)) =
      ∑' n : ℕ,
        (a * (if k ≤ n then f (n - k) else 0) +
            b * (if l ≤ n then f (n - l) else 0) +
            c * (if m ≤ n then f (n - m) else 0)) * z ^ n := by
  set A : ℕ → ℝ := fun n => (if k ≤ n then f (n - k) else 0) * z ^ n with hA
  set B : ℕ → ℝ := fun n => (if l ≤ n then f (n - l) else 0) * z ^ n with hB
  set C : ℕ → ℝ := fun n => (if m ≤ n then f (n - m) else 0) * z ^ n with hC
  have hAs : Summable A := by
    simpa [hA] using summable_mul_pow_shift f z k hf
  have hBs : Summable B := by
    simpa [hB] using summable_mul_pow_shift f z l hf
  have hCs : Summable C := by
    simpa [hC] using summable_mul_pow_shift f z m hf
  have hAeq : z ^ k * (∑' n : ℕ, f n * z ^ n) = ∑' n : ℕ, A n := by
    simpa [hA] using tsum_mul_pow_shift f z k hf
  have hBeq : z ^ l * (∑' n : ℕ, f n * z ^ n) = ∑' n : ℕ, B n := by
    simpa [hB] using tsum_mul_pow_shift f z l hf
  have hCeq : z ^ m * (∑' n : ℕ, f n * z ^ n) = ∑' n : ℕ, C n := by
    simpa [hC] using tsum_mul_pow_shift f z m hf
  calc
    a * (z ^ k * (∑' n : ℕ, f n * z ^ n)) +
        b * (z ^ l * (∑' n : ℕ, f n * z ^ n)) +
        c * (z ^ m * (∑' n : ℕ, f n * z ^ n))
        = a * (∑' n : ℕ, A n) + b * (∑' n : ℕ, B n) +
            c * (∑' n : ℕ, C n) := by rw [hAeq, hBeq, hCeq]
    _ = (∑' n : ℕ, a * A n) + (∑' n : ℕ, b * B n) +
          (∑' n : ℕ, c * C n) := by
        rw [Summable.tsum_mul_left a hAs, Summable.tsum_mul_left b hBs,
          Summable.tsum_mul_left c hCs]
    _ = ∑' n : ℕ, (a * A n + b * B n + c * C n) := by
        rw [← Summable.tsum_add (Summable.mul_left a hAs) (Summable.mul_left b hBs),
          ← Summable.tsum_add
            ((Summable.mul_left a hAs).add (Summable.mul_left b hBs))
            (Summable.mul_left c hCs)]
    _ = ∑' n : ℕ,
        (a * (if k ≤ n then f (n - k) else 0) +
            b * (if l ≤ n then f (n - l) else 0) +
            c * (if m ≤ n then f (n - m) else 0)) * z ^ n := by
        apply tsum_congr
        intro n
        simp [hA, hB, hC]
        split_ifs <;> ring

private lemma summable_shifted_linear_three (f : ℕ → ℝ) (z a b c : ℝ) (k l m : ℕ)
    (hf : Summable (fun n : ℕ => f n * z ^ n)) :
    Summable (fun n : ℕ =>
      (a * (if k ≤ n then f (n - k) else 0) +
          b * (if l ≤ n then f (n - l) else 0) +
          c * (if m ≤ n then f (n - m) else 0)) * z ^ n) := by
  have hA : Summable (fun n : ℕ =>
      a * ((if k ≤ n then f (n - k) else 0) * z ^ n)) :=
    Summable.mul_left a (summable_mul_pow_shift f z k hf)
  have hB : Summable (fun n : ℕ =>
      b * ((if l ≤ n then f (n - l) else 0) * z ^ n)) :=
    Summable.mul_left b (summable_mul_pow_shift f z l hf)
  have hC : Summable (fun n : ℕ =>
      c * ((if m ≤ n then f (n - m) else 0) * z ^ n)) :=
    Summable.mul_left c (summable_mul_pow_shift f z m hf)
  refine (hA.add hB).add hC |>.congr ?_
  intro n
  split_ifs <;> ring

private lemma aperyA_ode_coefficient_real (n : ℕ) :
    ((n + 1 : ℝ) ^ 3) * (Number.aperyA (n + 1) : ℝ)
      - (2 * n + 1 : ℝ) * (17 * n ^ 2 + 17 * n + 5) *
          (Number.aperyA n : ℝ)
      + (n : ℝ) ^ 3 * (Number.aperyA (n - 1) : ℝ) = 0 := by
  have h := Number.aperyA_ode_coefficient n
  have hR := congrArg ((↑·) : ℚ → ℝ) h
  push_cast at hR
  exact hR

private noncomputable def aperyGFARealODECoeffShifted (n : ℕ) : ℝ :=
    ((if 2 ≤ n then
        (((n - 2 : ℕ) : ℝ) + 3) * (((n - 2 : ℕ) : ℝ) + 2) *
          (((n - 2 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 2 + 3) : ℝ) else 0)
      - 34 * (if 3 ≤ n then
        (((n - 3 : ℕ) : ℝ) + 3) * (((n - 3 : ℕ) : ℝ) + 2) *
          (((n - 3 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 3 + 3) : ℝ) else 0)
      + (if 4 ≤ n then
        (((n - 4 : ℕ) : ℝ) + 3) * (((n - 4 : ℕ) : ℝ) + 2) *
          (((n - 4 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 4 + 3) : ℝ) else 0))
    + (3 * (if 1 ≤ n then
        (((n - 1 : ℕ) : ℝ) + 2) * (((n - 1 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 1 + 2) : ℝ) else 0)
      - 153 * (if 2 ≤ n then
        (((n - 2 : ℕ) : ℝ) + 2) * (((n - 2 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 2 + 2) : ℝ) else 0)
      + 6 * (if 3 ≤ n then
        (((n - 3 : ℕ) : ℝ) + 2) * (((n - 3 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 3 + 2) : ℝ) else 0))
    + ((if 0 ≤ n then
        (((n - 0 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 0 + 1) : ℝ) else 0)
      - 112 * (if 1 ≤ n then
        (((n - 1 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 1 + 1) : ℝ) else 0)
      + 7 * (if 2 ≤ n then
        (((n - 2 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 2 + 1) : ℝ) else 0))
    + (-5 * (Number.aperyA n : ℝ) +
        (if 1 ≤ n then (Number.aperyA (n - 1) : ℝ) else 0))

private lemma aperyGFA_real_ode_shifted_coeff_zero (n : ℕ) :
    ((if 2 ≤ n then
        (((n - 2 : ℕ) : ℝ) + 3) * (((n - 2 : ℕ) : ℝ) + 2) *
          (((n - 2 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 2 + 3) : ℝ) else 0)
      - 34 * (if 3 ≤ n then
        (((n - 3 : ℕ) : ℝ) + 3) * (((n - 3 : ℕ) : ℝ) + 2) *
          (((n - 3 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 3 + 3) : ℝ) else 0)
      + (if 4 ≤ n then
        (((n - 4 : ℕ) : ℝ) + 3) * (((n - 4 : ℕ) : ℝ) + 2) *
          (((n - 4 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 4 + 3) : ℝ) else 0))
    + (3 * (if 1 ≤ n then
        (((n - 1 : ℕ) : ℝ) + 2) * (((n - 1 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 1 + 2) : ℝ) else 0)
      - 153 * (if 2 ≤ n then
        (((n - 2 : ℕ) : ℝ) + 2) * (((n - 2 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 2 + 2) : ℝ) else 0)
      + 6 * (if 3 ≤ n then
        (((n - 3 : ℕ) : ℝ) + 2) * (((n - 3 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 3 + 2) : ℝ) else 0))
    + ((if 0 ≤ n then
        (((n - 0 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 0 + 1) : ℝ) else 0)
      - 112 * (if 1 ≤ n then
        (((n - 1 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 1 + 1) : ℝ) else 0)
      + 7 * (if 2 ≤ n then
        (((n - 2 : ℕ) : ℝ) + 1) *
          (Number.aperyA (n - 2 + 1) : ℝ) else 0))
    + (-5 * (Number.aperyA n : ℝ) +
        (if 1 ≤ n then (Number.aperyA (n - 1) : ℝ) else 0)) = 0 := by
  by_cases hn : 4 ≤ n
  · have hrec := aperyA_ode_coefficient_real n
    have h23 : n - 2 + 3 = n + 1 := by omega
    have h33 : n - 3 + 3 = n := by omega
    have h43 : n - 4 + 3 = n - 1 := by omega
    have h12 : n - 1 + 2 = n + 1 := by omega
    have h22 : n - 2 + 2 = n := by omega
    have h32 : n - 3 + 2 = n - 1 := by omega
    have h11 : n - 1 + 1 = n := by omega
    have h21 : n - 2 + 1 = n - 1 := by omega
    simp [hn, (by omega : 3 ≤ n), (by omega : 2 ≤ n), (by omega : 1 ≤ n),
      h23, h33, h43, h12, h22, h32, h11, h21]
    linear_combination hrec
  · interval_cases n <;>
      simp [Number.aperyA_zero, Number.aperyA_one, Number.aperyA_two,
        Number.aperyA_three, Number.aperyA_four] <;>
      norm_num

private lemma aperyGFARealODECoeffShifted_zero (n : ℕ) :
    aperyGFARealODECoeffShifted n = 0 := by
  unfold aperyGFARealODECoeffShifted
  exact aperyGFA_real_ode_shifted_coeff_zero n

private lemma aperyGFAReal_satisfies_apery_ode_explicit
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    (z ^ 2 - 34 * z ^ 3 + z ^ 4) *
        deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)) z
      + (3 * z - 153 * z ^ 2 + 6 * z ^ 3) *
        deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) z
      + (1 - 112 * z + 7 * z ^ 2) *
        deriv Ripple.Number.Frobenius.aperyGFAReal z
      + (-5 + z) * Ripple.Number.Frobenius.aperyGFAReal z = 0 := by
  let f0 : ℕ → ℝ := fun n => (Number.aperyA n : ℝ)
  let f1 : ℕ → ℝ := fun n =>
    ((n : ℝ) + 1) * (Number.aperyA (n + 1) : ℝ)
  let f2 : ℕ → ℝ := fun n =>
    (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
      (Number.aperyA (n + 2) : ℝ)
  let f3 : ℕ → ℝ := fun n =>
    (((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1)) *
      (Number.aperyA (n + 3) : ℝ)
  have hs0 : Summable (fun n : ℕ => f0 n * z ^ n) := by
    simpa [f0] using aperyGFAReal_summable_series hz
  have hs1 : Summable (fun n : ℕ => f1 n * z ^ n) := by
    simpa [f1] using aperyGFAReal_deriv_summable_series hz
  have hs2 : Summable (fun n : ℕ => f2 n * z ^ n) := by
    simpa [f2] using aperyGFAReal_second_deriv_summable_series hz
  have hs3 : Summable (fun n : ℕ => f3 n * z ^ n) := by
    simpa [f3] using aperyGFAReal_third_deriv_summable_series hz
  rw [aperyGFAReal_third_deriv_eq_series (z := z) hz,
    aperyGFAReal_second_deriv_eq_series (z := z) hz,
    aperyGFAReal_deriv_eq_series (z := z) hz,
    aperyGFAReal_eq_series (z := z) hz]
  change
    (z ^ 2 - 34 * z ^ 3 + z ^ 4) * (∑' n : ℕ, f3 n * z ^ n)
      + (3 * z - 153 * z ^ 2 + 6 * z ^ 3) * (∑' n : ℕ, f2 n * z ^ n)
      + (1 - 112 * z + 7 * z ^ 2) * (∑' n : ℕ, f1 n * z ^ n)
      + (-5 + z) * (∑' n : ℕ, f0 n * z ^ n) = 0
  have hP :
      (z ^ 2 - 34 * z ^ 3 + z ^ 4) * (∑' n : ℕ, f3 n * z ^ n) =
        ∑' n : ℕ,
          (1 * (if 2 ≤ n then f3 (n - 2) else 0) +
              (-34) * (if 3 ≤ n then f3 (n - 3) else 0) +
              1 * (if 4 ≤ n then f3 (n - 4) else 0)) * z ^ n := by
    calc
      (z ^ 2 - 34 * z ^ 3 + z ^ 4) * (∑' n : ℕ, f3 n * z ^ n)
          = 1 * (z ^ 2 * (∑' n : ℕ, f3 n * z ^ n)) +
              (-34) * (z ^ 3 * (∑' n : ℕ, f3 n * z ^ n)) +
              1 * (z ^ 4 * (∑' n : ℕ, f3 n * z ^ n)) := by ring
      _ = _ := tsum_shifted_linear_three f3 z 1 (-34) 1 2 3 4 hs3
  have hQ :
      (3 * z - 153 * z ^ 2 + 6 * z ^ 3) * (∑' n : ℕ, f2 n * z ^ n) =
        ∑' n : ℕ,
          (3 * (if 1 ≤ n then f2 (n - 1) else 0) +
              (-153) * (if 2 ≤ n then f2 (n - 2) else 0) +
              6 * (if 3 ≤ n then f2 (n - 3) else 0)) * z ^ n := by
    calc
      (3 * z - 153 * z ^ 2 + 6 * z ^ 3) * (∑' n : ℕ, f2 n * z ^ n)
          = 3 * (z ^ 1 * (∑' n : ℕ, f2 n * z ^ n)) +
              (-153) * (z ^ 2 * (∑' n : ℕ, f2 n * z ^ n)) +
              6 * (z ^ 3 * (∑' n : ℕ, f2 n * z ^ n)) := by ring
      _ = _ := tsum_shifted_linear_three f2 z 3 (-153) 6 1 2 3 hs2
  have hR :
      (1 - 112 * z + 7 * z ^ 2) * (∑' n : ℕ, f1 n * z ^ n) =
        ∑' n : ℕ,
          (1 * (if 0 ≤ n then f1 (n - 0) else 0) +
              (-112) * (if 1 ≤ n then f1 (n - 1) else 0) +
              7 * (if 2 ≤ n then f1 (n - 2) else 0)) * z ^ n := by
    calc
      (1 - 112 * z + 7 * z ^ 2) * (∑' n : ℕ, f1 n * z ^ n)
          = 1 * (z ^ 0 * (∑' n : ℕ, f1 n * z ^ n)) +
              (-112) * (z ^ 1 * (∑' n : ℕ, f1 n * z ^ n)) +
              7 * (z ^ 2 * (∑' n : ℕ, f1 n * z ^ n)) := by ring
      _ = _ := tsum_shifted_linear_three f1 z 1 (-112) 7 0 1 2 hs1
  have hS :
      (-5 + z) * (∑' n : ℕ, f0 n * z ^ n) =
        ∑' n : ℕ,
          ((-5) * (if 0 ≤ n then f0 (n - 0) else 0) +
              1 * (if 1 ≤ n then f0 (n - 1) else 0) +
              0 * (if 0 ≤ n then f0 (n - 0) else 0)) * z ^ n := by
    calc
      (-5 + z) * (∑' n : ℕ, f0 n * z ^ n)
          = (-5) * (z ^ 0 * (∑' n : ℕ, f0 n * z ^ n)) +
              1 * (z ^ 1 * (∑' n : ℕ, f0 n * z ^ n)) +
              0 * (z ^ 0 * (∑' n : ℕ, f0 n * z ^ n)) := by ring
      _ = _ := tsum_shifted_linear_three f0 z (-5) 1 0 0 1 0 hs0
  rw [hP, hQ, hR, hS]
  have hsP := summable_shifted_linear_three f3 z 1 (-34) 1 2 3 4 hs3
  have hsQ := summable_shifted_linear_three f2 z 3 (-153) 6 1 2 3 hs2
  have hsR := summable_shifted_linear_three f1 z 1 (-112) 7 0 1 2 hs1
  have hsS := summable_shifted_linear_three f0 z (-5) 1 0 0 1 0 hs0
  rw [← Summable.tsum_add hsP hsQ,
    ← Summable.tsum_add (hsP.add hsQ) hsR,
    ← Summable.tsum_add ((hsP.add hsQ).add hsR) hsS]
  rw [tsum_congr (fun n => by
    have hterm :
        ((1 * (if 2 ≤ n then f3 (n - 2) else 0) +
              (-34) * (if 3 ≤ n then f3 (n - 3) else 0) +
              1 * (if 4 ≤ n then f3 (n - 4) else 0)) * z ^ n +
            (3 * (if 1 ≤ n then f2 (n - 1) else 0) +
              (-153) * (if 2 ≤ n then f2 (n - 2) else 0) +
              6 * (if 3 ≤ n then f2 (n - 3) else 0)) * z ^ n +
            (1 * (if 0 ≤ n then f1 (n - 0) else 0) +
              (-112) * (if 1 ≤ n then f1 (n - 1) else 0) +
              7 * (if 2 ≤ n then f1 (n - 2) else 0)) * z ^ n +
            ((-5) * (if 0 ≤ n then f0 (n - 0) else 0) +
              1 * (if 1 ≤ n then f0 (n - 1) else 0) +
              0 * (if 0 ≤ n then f0 (n - 0) else 0)) * z ^ n) =
          aperyGFARealODECoeffShifted n * z ^ n := by
      simp [aperyGFARealODECoeffShifted, f0, f1, f2, f3]
      split_ifs <;> ring
    rw [hterm, aperyGFARealODECoeffShifted_zero n, zero_mul]), tsum_zero]

lemma aperyGFAReal_satisfies_apery_ode_polynomial
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Polynomial.eval z Number.aperyPconifold *
        deriv (deriv (deriv Ripple.Number.Frobenius.aperyGFAReal)) z
      + Polynomial.eval z Number.aperyQconifold *
        deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) z
      + Polynomial.eval z aperyRconifold *
        deriv Ripple.Number.Frobenius.aperyGFAReal z
      + Polynomial.eval z aperySconifold *
        Ripple.Number.Frobenius.aperyGFAReal z = 0 := by
  have h := aperyGFAReal_satisfies_apery_ode_explicit (z := z) hz
  unfold Number.aperyPconifold Number.aperyQconifold aperyRconifold aperySconifold
  simp [Polynomial.eval_add, Polynomial.eval_monomial] at h ⊢
  ring_nf at h ⊢
  exact h

lemma aperyF5GFAReal_satisfies_apery_ode_polynomial
    {z : ℝ} (hz : |z| < Number.aperyConifoldZ1Poly) :
    Polynomial.eval z Number.aperyPconifold *
        deriv (deriv (deriv aperyF5GFAReal)) z
      + Polynomial.eval z Number.aperyQconifold *
        deriv (deriv aperyF5GFAReal) z
      + Polynomial.eval z aperyRconifold *
        deriv aperyF5GFAReal z
      + Polynomial.eval z aperySconifold *
        aperyF5GFAReal z = 0 := by
  have hfun : aperyF5GFAReal = Number.Frobenius.aperyGFAReal := by
    funext z
    exact aperyGFAReal_eq_canonical z
  rw [hfun]
  exact aperyGFAReal_satisfies_apery_ode_polynomial (z := z) hz

lemma aperyGFAReal_satisfies_apery_ode_on_left_corridor
    {δ t : ℝ} (hδ_le : δ ≤ Number.aperyConifoldZ1Poly)
    (ht : t ∈ aperyConifoldLeftTInterval δ) :
    Polynomial.eval (Number.aperyConifoldZ1Poly + t) Number.aperyPconifold *
        deriv (deriv (deriv aperyF5GFAReal))
          (Number.aperyConifoldZ1Poly + t)
      + Polynomial.eval (Number.aperyConifoldZ1Poly + t) Number.aperyQconifold *
        deriv (deriv aperyF5GFAReal)
          (Number.aperyConifoldZ1Poly + t)
      + Polynomial.eval (Number.aperyConifoldZ1Poly + t) aperyRconifold *
        deriv aperyF5GFAReal (Number.aperyConifoldZ1Poly + t)
      + Polynomial.eval (Number.aperyConifoldZ1Poly + t) aperySconifold *
        aperyF5GFAReal (Number.aperyConifoldZ1Poly + t) = 0 := by
  rcases ht with ⟨ht_left, ht_right⟩
  have hz_pos : 0 < Number.aperyConifoldZ1Poly + t := by linarith
  have hz_lt : Number.aperyConifoldZ1Poly + t < Number.aperyConifoldZ1Poly := by
    linarith
  have hz_abs :
      |Number.aperyConifoldZ1Poly + t| < Number.aperyConifoldZ1Poly := by
    rw [abs_of_pos hz_pos]
    exact hz_lt
  exact aperyGFAReal_satisfies_apery_ode_polynomial (z := _) hz_abs

abbrev AperyODEState : Type := ℝ × ℝ × ℝ

noncomputable def aperyODEStateField (z : ℝ) (Y : AperyODEState) :
    AperyODEState :=
  (Y.2.1,
    Y.2.2,
    - (Polynomial.eval z Number.aperyQconifold * Y.2.2 +
        Polynomial.eval z aperyRconifold * Y.2.1 +
        Polynomial.eval z aperySconifold * Y.1) /
      Polynomial.eval z Number.aperyPconifold)

/-- For fixed `z`, the canonical Apéry state vector field is a continuous
linear map in the state variables.  This is the Lipschitz input needed by the
ODE uniqueness theorem. -/
noncomputable def aperyODEStateCLM (z : ℝ) :
    AperyODEState →L[ℝ] AperyODEState :=
  ContinuousLinearMap.mk
    { toFun := fun Y : AperyODEState => aperyODEStateField z Y
      map_add' := by
        intro Y W
        ext <;> simp [aperyODEStateField]
        ring
      map_smul' := by
        intro c Y
        ext <;> simp [aperyODEStateField]
        ring }
    (by
      unfold aperyODEStateField
      fun_prop)

lemma aperyODEStateCLM_apply (z : ℝ) (Y : AperyODEState) :
    aperyODEStateCLM z Y = aperyODEStateField z Y := rfl

lemma aperyODEStateField_lipschitzWith (z : ℝ) :
    LipschitzWith ‖aperyODEStateCLM z‖₊ (aperyODEStateField z) := by
  simpa [aperyODEStateCLM_apply] using (aperyODEStateCLM z).lipschitz

lemma aperyODEStateField_lipschitzOnWith (z : ℝ) (s : Set AperyODEState) :
    LipschitzOnWith ‖aperyODEStateCLM z‖₊ (aperyODEStateField z) s :=
  (aperyODEStateField_lipschitzWith z).lipschitzOnWith

lemma aperyODEStateField_lipschitzOnWith_of_clm_norm_le
    {z K : ℝ} (hK : 0 ≤ K)
    (hbound : ‖aperyODEStateCLM z‖ ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (aperyODEStateField z)
      (Set.univ : Set AperyODEState) := by
  refine
    (aperyODEStateField_lipschitzOnWith z
      (Set.univ : Set AperyODEState)).weaken ?_
  rw [← NNReal.coe_le_coe]
  simp [Real.coe_toNNReal K hK]
  exact hbound

lemma aperyODEStateField_lipschitzOnWith_of_uniform_clm_norm_le
    {a b K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z ∈ Set.Ioo a b, ‖aperyODEStateCLM z‖ ≤ K) :
    ∀ z ∈ Set.Ioo a b,
      LipschitzOnWith (Real.toNNReal K) (aperyODEStateField z)
        (Set.univ : Set AperyODEState) := by
  intro z hz
  exact aperyODEStateField_lipschitzOnWith_of_clm_norm_le hK
    (hbound z hz)

private lemma aperyODEStateCLM_norm_le_of_coeff_bounds
    {z Cq Cr Cs K : ℝ}
    (hK0 : 0 ≤ K) (hK1 : 1 ≤ K)
    (hQ :
      ‖Polynomial.eval z Number.aperyQconifold /
          Polynomial.eval z Number.aperyPconifold‖ ≤ Cq)
    (hR :
      ‖Polynomial.eval z aperyRconifold /
          Polynomial.eval z Number.aperyPconifold‖ ≤ Cr)
    (hS :
      ‖Polynomial.eval z aperySconifold /
          Polynomial.eval z Number.aperyPconifold‖ ≤ Cs)
    (hCsum : Cq + Cr + Cs ≤ K) :
    ‖aperyODEStateCLM z‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 ?_
  intro Y
  have hY0 : ‖Y.1‖ ≤ ‖Y‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hY1 : ‖Y.2.1‖ ≤ ‖Y‖ := by
    rw [Prod.norm_def]
    exact le_trans (by
      rw [Prod.norm_def]
      exact le_max_left _ _) (le_max_right _ _)
  have hY2 : ‖Y.2.2‖ ≤ ‖Y‖ := by
    rw [Prod.norm_def]
    exact le_trans (by
      rw [Prod.norm_def]
      exact le_max_right _ _) (le_max_right _ _)
  have hYnn : 0 ≤ ‖Y‖ := norm_nonneg _
  have hKY : ‖Y‖ ≤ K * ‖Y‖ := by
    nlinarith
  have hCq : 0 ≤ Cq := le_trans (norm_nonneg _) hQ
  have hCr : 0 ≤ Cr := le_trans (norm_nonneg _) hR
  have hCs : 0 ≤ Cs := le_trans (norm_nonneg _) hS
  let q : ℝ :=
    Polynomial.eval z Number.aperyQconifold /
      Polynomial.eval z Number.aperyPconifold
  let r : ℝ :=
    Polynomial.eval z aperyRconifold /
      Polynomial.eval z Number.aperyPconifold
  let s : ℝ :=
    Polynomial.eval z aperySconifold /
      Polynomial.eval z Number.aperyPconifold
  have hqY : ‖q * Y.2.2‖ ≤ Cq * ‖Y‖ := by
    calc
      ‖q * Y.2.2‖ = ‖q‖ * ‖Y.2.2‖ := norm_mul _ _
      _ ≤ Cq * ‖Y‖ := mul_le_mul (by simpa [q] using hQ) hY2
        (norm_nonneg _) hCq
  have hrY : ‖r * Y.2.1‖ ≤ Cr * ‖Y‖ := by
    calc
      ‖r * Y.2.1‖ = ‖r‖ * ‖Y.2.1‖ := norm_mul _ _
      _ ≤ Cr * ‖Y‖ := mul_le_mul (by simpa [r] using hR) hY1
        (norm_nonneg _) hCr
  have hsY : ‖s * Y.1‖ ≤ Cs * ‖Y‖ := by
    calc
      ‖s * Y.1‖ = ‖s‖ * ‖Y.1‖ := norm_mul _ _
      _ ≤ Cs * ‖Y‖ := mul_le_mul (by simpa [s] using hS) hY0
        (norm_nonneg _) hCs
  have hthird_expr :
      (aperyODEStateCLM z Y).2.2 =
        - (q * Y.2.2 + r * Y.2.1 + s * Y.1) := by
    rw [aperyODEStateCLM_apply]
    unfold aperyODEStateField
    dsimp [q, r, s]
    ring
  have hthird :
      ‖(aperyODEStateCLM z Y).2.2‖ ≤ K * ‖Y‖ := by
    rw [hthird_expr, norm_neg]
    have htri :
        ‖q * Y.2.2 + r * Y.2.1 + s * Y.1‖ ≤
          ‖q * Y.2.2‖ + ‖r * Y.2.1‖ + ‖s * Y.1‖ := by
      have hAB :
          ‖q * Y.2.2 + r * Y.2.1‖ ≤
            ‖q * Y.2.2‖ + ‖r * Y.2.1‖ :=
        norm_add_le (q * Y.2.2) (r * Y.2.1)
      calc
        ‖q * Y.2.2 + r * Y.2.1 + s * Y.1‖
            ≤ ‖q * Y.2.2 + r * Y.2.1‖ + ‖s * Y.1‖ :=
              norm_add_le (q * Y.2.2 + r * Y.2.1) (s * Y.1)
        _ ≤ (‖q * Y.2.2‖ + ‖r * Y.2.1‖) + ‖s * Y.1‖ := by
              linarith
        _ = ‖q * Y.2.2‖ + ‖r * Y.2.1‖ + ‖s * Y.1‖ := by
              ring
    calc
      ‖q * Y.2.2 + r * Y.2.1 + s * Y.1‖
          ≤ ‖q * Y.2.2‖ + ‖r * Y.2.1‖ + ‖s * Y.1‖ := htri
      _ ≤ (Cq + Cr + Cs) * ‖Y‖ := by linarith
      _ ≤ K * ‖Y‖ := mul_le_mul_of_nonneg_right hCsum hYnn
  have hfirst : ‖(aperyODEStateCLM z Y).1‖ ≤ K * ‖Y‖ := by
    rw [aperyODEStateCLM_apply]
    unfold aperyODEStateField
    exact le_trans hY1 hKY
  have hsecond : ‖(aperyODEStateCLM z Y).2.1‖ ≤ K * ‖Y‖ := by
    rw [aperyODEStateCLM_apply]
    unfold aperyODEStateField
    exact le_trans hY2 hKY
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le hfirst (max_le hsecond hthird)

lemma aperyODEStateField_lipschitzOnWith_on_compact_subcorridor
    {a b : ℝ} (ha_pos : 0 < a) (_hab : a < b)
    (hb_lt : b < Number.aperyConifoldZ1Poly) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Set.Ioo a b,
      LipschitzOnWith (Real.toNNReal K) (aperyODEStateField z)
        (Set.univ : Set AperyODEState) := by
  have hQcont :
      ContinuousOn
        (fun z : ℝ =>
          ‖Polynomial.eval z Number.aperyQconifold /
            Polynomial.eval z Number.aperyPconifold‖)
        (Set.Icc a b) := by
    refine ContinuousOn.norm ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact Number.aperyQconifold.continuous.continuousOn
    · exact Number.aperyPconifold.continuous.continuousOn
    · intro z hz
      exact aperyPconifold_eval_ne_zero_of_pos_lt_z1
        (lt_of_lt_of_le ha_pos hz.1) (lt_of_le_of_lt hz.2 hb_lt)
  have hRcont :
      ContinuousOn
        (fun z : ℝ =>
          ‖Polynomial.eval z aperyRconifold /
            Polynomial.eval z Number.aperyPconifold‖)
        (Set.Icc a b) := by
    refine ContinuousOn.norm ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact aperyRconifold.continuous.continuousOn
    · exact Number.aperyPconifold.continuous.continuousOn
    · intro z hz
      exact aperyPconifold_eval_ne_zero_of_pos_lt_z1
        (lt_of_lt_of_le ha_pos hz.1) (lt_of_le_of_lt hz.2 hb_lt)
  have hScont :
      ContinuousOn
        (fun z : ℝ =>
          ‖Polynomial.eval z aperySconifold /
            Polynomial.eval z Number.aperyPconifold‖)
        (Set.Icc a b) := by
    refine ContinuousOn.norm ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact aperySconifold.continuous.continuousOn
    · exact Number.aperyPconifold.continuous.continuousOn
    · intro z hz
      exact aperyPconifold_eval_ne_zero_of_pos_lt_z1
        (lt_of_lt_of_le ha_pos hz.1) (lt_of_le_of_lt hz.2 hb_lt)
  obtain ⟨Cq, hCq⟩ := isCompact_Icc.exists_bound_of_continuousOn hQcont
  obtain ⟨Cr, hCr⟩ := isCompact_Icc.exists_bound_of_continuousOn hRcont
  obtain ⟨Cs, hCs⟩ := isCompact_Icc.exists_bound_of_continuousOn hScont
  let K : ℝ := max 1 (Cq + Cr + Cs)
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact le_trans zero_le_one (le_max_left _ _)
  · intro z hz
    have hzIcc : z ∈ Set.Icc a b := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    have hQz :
        ‖Polynomial.eval z Number.aperyQconifold /
            Polynomial.eval z Number.aperyPconifold‖ ≤ Cq := by
      have h := hCq z hzIcc
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
    have hRz :
        ‖Polynomial.eval z aperyRconifold /
            Polynomial.eval z Number.aperyPconifold‖ ≤ Cr := by
      have h := hCr z hzIcc
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
    have hSz :
        ‖Polynomial.eval z aperySconifold /
            Polynomial.eval z Number.aperyPconifold‖ ≤ Cs := by
      have h := hCs z hzIcc
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
    have hK0 : 0 ≤ K := by
      dsimp [K]
      exact le_trans zero_le_one (le_max_left _ _)
    have hK1 : 1 ≤ K := by
      dsimp [K]
      exact le_max_left _ _
    have hCsum : Cq + Cr + Cs ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    exact aperyODEStateField_lipschitzOnWith_of_clm_norm_le hK0
      (aperyODEStateCLM_norm_le_of_coeff_bounds hK0 hK1 hQz hRz hSz hCsum)

lemma aperyODEStateField_lipschitzOnWith_on_left_compact_subcorridor
    {δ : ℝ} (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly) :
    ∀ a b : ℝ,
      Number.aperyConifoldZ1Poly - δ < a → a < b →
        b < Number.aperyConifoldZ1Poly →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Set.Ioo a b,
          LipschitzOnWith (Real.toNNReal K) (aperyODEStateField z)
            (Set.univ : Set AperyODEState) := by
  intro a b ha_left hab hb_right
  have ha_pos : 0 < a := by
    have hleft_pos : 0 < Number.aperyConifoldZ1Poly - δ := by linarith
    exact lt_trans hleft_pos ha_left
  exact aperyODEStateField_lipschitzOnWith_on_compact_subcorridor
    ha_pos hab hb_right

private lemma apery_scalar_ode_third_eq_state_field
    {z y0 y1 y2 y3 : ℝ}
    (hP : Polynomial.eval z Number.aperyPconifold ≠ 0)
    (hode :
      Polynomial.eval z Number.aperyPconifold * y3
        + Polynomial.eval z Number.aperyQconifold * y2
        + Polynomial.eval z aperyRconifold * y1
        + Polynomial.eval z aperySconifold * y0 = 0) :
    y3 =
      (aperyODEStateField z (y0, y1, y2)).2.2 := by
  unfold aperyODEStateField
  field_simp [hP]
  linear_combination hode

lemma hasDerivAt_aperyODEState_of_scalar_ode
    {y y' y'' : ℝ → ℝ} {z y''' : ℝ}
    (hy : HasDerivAt y (y' z) z)
    (hy' : HasDerivAt y' (y'' z) z)
    (hy'' : HasDerivAt y'' y''' z)
    (hP : Polynomial.eval z Number.aperyPconifold ≠ 0)
    (hode :
      Polynomial.eval z Number.aperyPconifold * y'''
        + Polynomial.eval z Number.aperyQconifold * y'' z
        + Polynomial.eval z aperyRconifold * y' z
        + Polynomial.eval z aperySconifold * y z = 0) :
    HasDerivAt (fun x : ℝ => (y x, y' x, y'' x))
      (aperyODEStateField z (y z, y' z, y'' z)) z := by
  have hthird :=
    apery_scalar_ode_third_eq_state_field
      (z := z) (y0 := y z) (y1 := y' z) (y2 := y'' z) (y3 := y''')
      hP hode
  convert hy.prodMk (hy'.prodMk hy'') using 1
  ext <;> simp [aperyODEStateField, hthird]

lemma aperyGFAReal_state_hasDerivAt_on_left_corridor
    {z : ℝ} (hz_pos : 0 < z)
    (hz_lt : z < Number.aperyConifoldZ1Poly) :
    HasDerivAt
      (fun x : ℝ =>
        (Ripple.Number.Frobenius.aperyGFAReal x,
          deriv Ripple.Number.Frobenius.aperyGFAReal x,
          deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) x))
      (aperyODEStateField z
        (Ripple.Number.Frobenius.aperyGFAReal z,
          deriv Ripple.Number.Frobenius.aperyGFAReal z,
          deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) z)) z := by
  have hz_abs : |z| < Number.aperyConifoldZ1Poly := by
    rw [abs_of_pos hz_pos]
    exact hz_lt
  exact hasDerivAt_aperyODEState_of_scalar_ode
    (aperyGFAReal_hasDerivAt hz_abs)
    (aperyGFAReal_deriv_hasDerivAt hz_abs)
    (aperyGFAReal_second_deriv_hasDerivAt hz_abs)
    (aperyPconifold_eval_ne_zero_of_pos_lt_z1 hz_pos hz_lt)
    (aperyGFAReal_satisfies_apery_ode_polynomial hz_abs)

lemma aperyF5GFAReal_state_hasDerivAt_on_left_corridor
    {z : ℝ} (hz_pos : 0 < z)
    (hz_lt : z < Number.aperyConifoldZ1Poly) :
    HasDerivAt
      (fun x : ℝ =>
        (aperyF5GFAReal x,
          deriv aperyF5GFAReal x,
          deriv (deriv aperyF5GFAReal) x))
      (aperyODEStateField z
        (aperyF5GFAReal z,
          deriv aperyF5GFAReal z,
          deriv (deriv aperyF5GFAReal) z)) z := by
  simpa [aperyF5GFAReal, aperyF5A, Number.aperyA,
    Number.Frobenius.aperyGFAReal] using
      aperyGFAReal_state_hasDerivAt_on_left_corridor
        (z := z) hz_pos hz_lt

/-- Uniqueness for the canonical Apéry equation in first-order state form.

The theorem is deliberately stated with an explicit uniform Lipschitz
hypothesis on the open interval.  Later bridge lemmas only need to provide
that bound on a compact sub-corridor; the state vector field itself is already
known to be Lipschitz for each fixed point by `aperyODEStateField_lipschitzOnWith`.
-/
lemma aperyODEState_unique_on_Ioo
    {a b t₀ K : ℝ} {f g : ℝ → AperyODEState}
    (_hK : 0 ≤ K)
    (hLip : ∀ t ∈ Set.Ioo a b,
      LipschitzOnWith (Real.toNNReal K) (aperyODEStateField t)
        (Set.univ : Set AperyODEState))
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hf : ∀ t ∈ Set.Ioo a b,
      HasDerivAt f (aperyODEStateField t (f t)) t)
    (hg : ∀ t ∈ Set.Ioo a b,
      HasDerivAt g (aperyODEStateField t (g t)) t)
    (hinit : f t₀ = g t₀) :
    Set.EqOn f g (Set.Ioo a b) := by
  refine ODE_solution_unique_of_mem_Ioo hLip ht₀ ?_ ?_ hinit
  · intro t ht
    exact ⟨hf t ht, Set.mem_univ _⟩
  · intro t ht
    exact ⟨hg t ht, Set.mem_univ _⟩

/-- Scalar version of canonical Apéry uniqueness: two scalar functions whose
value/first/second derivative states solve the same third-order Apéry ODE and
agree at one interior point agree throughout the interval.

This is the main ODE-continuation bridge used to propagate a local Frobenius
matching identity across the left corridor. -/
lemma apery_scalar_ode_unique_on_Ioo
    {a b t₀ K : ℝ}
    {y y' y'' u u' u'' : ℝ → ℝ}
    (_hK : 0 ≤ K)
    (hLip : ∀ t ∈ Set.Ioo a b,
      LipschitzOnWith (Real.toNNReal K) (aperyODEStateField t)
        (Set.univ : Set AperyODEState))
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hP : ∀ t ∈ Set.Ioo a b,
      Polynomial.eval t Number.aperyPconifold ≠ 0)
    (hy : ∀ t ∈ Set.Ioo a b, HasDerivAt y (y' t) t)
    (hy' : ∀ t ∈ Set.Ioo a b, HasDerivAt y' (y'' t) t)
    (hy'' : ∀ t ∈ Set.Ioo a b, ∃ y''' : ℝ, HasDerivAt y'' y''' t ∧
      Polynomial.eval t Number.aperyPconifold * y'''
        + Polynomial.eval t Number.aperyQconifold * y'' t
        + Polynomial.eval t aperyRconifold * y' t
        + Polynomial.eval t aperySconifold * y t = 0)
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Set.Ioo a b, HasDerivAt u' (u'' t) t)
    (hu'' : ∀ t ∈ Set.Ioo a b, ∃ u''' : ℝ, HasDerivAt u'' u''' t ∧
      Polynomial.eval t Number.aperyPconifold * u'''
        + Polynomial.eval t Number.aperyQconifold * u'' t
        + Polynomial.eval t aperyRconifold * u' t
        + Polynomial.eval t aperySconifold * u t = 0)
    (hinit :
      (y t₀, y' t₀, y'' t₀) = (u t₀, u' t₀, u'' t₀)) :
    Set.EqOn y u (Set.Ioo a b) := by
  have hstate := aperyODEState_unique_on_Ioo
    (a := a) (b := b) (t₀ := t₀) (K := K)
    (f := fun t => (y t, y' t, y'' t))
    (g := fun t => (u t, u' t, u'' t))
    _hK hLip ht₀ ?_ ?_ hinit
  · intro t ht
    have h := hstate ht
    exact congrArg Prod.fst h
  · intro t ht
    rcases hy'' t ht with ⟨y''', hy3, hode⟩
    exact hasDerivAt_aperyODEState_of_scalar_ode
      (hy t ht) (hy' t ht) hy3 (hP t ht) hode
  · intro t ht
    rcases hu'' t ht with ⟨u''', hu3, hode⟩
    exact hasDerivAt_aperyODEState_of_scalar_ode
      (hu t ht) (hu' t ht) hu3 (hP t ht) hode

lemma apery_left_connection_of_branch_state_match
    {a₀ a_half a₁ δ z₀ K : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hK : 0 ≤ K)
    (hbound : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly,
      ‖aperyODEStateCLM z‖ ≤ K)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly,
      HasDerivAt
        (fun x : ℝ =>
          (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly),
            deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly)) x,
            deriv (deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly))) x))
        (aperyODEStateField z
          (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (z - Number.aperyConifoldZ1Poly),
            deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly)) z,
            deriv (deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly))) z)) z)
    (hinit :
      (aperyF5GFAReal z₀,
        deriv aperyF5GFAReal z₀,
        deriv (deriv aperyF5GFAReal) z₀) =
      (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (z₀ - Number.aperyConifoldZ1Poly),
        deriv (fun y : ℝ =>
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (y - Number.aperyConifoldZ1Poly)) z₀,
        deriv (deriv (fun y : ℝ =>
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (y - Number.aperyConifoldZ1Poly))) z₀)) :
    Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let I : Set ℝ :=
    Set.Ioo (Number.aperyConifoldZ1Poly - δ)
      Number.aperyConifoldZ1Poly
  let Fstate : ℝ → AperyODEState := fun z =>
    (aperyF5GFAReal z,
      deriv aperyF5GFAReal z,
      deriv (deriv aperyF5GFAReal) z)
  let Bstate : ℝ → AperyODEState := fun z =>
    (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly),
      deriv (fun y : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (y - Number.aperyConifoldZ1Poly)) z,
      deriv (deriv (fun y : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (y - Number.aperyConifoldZ1Poly))) z)
  have hLip : ∀ z ∈ I,
      LipschitzOnWith (Real.toNNReal K) (aperyODEStateField z)
        (Set.univ : Set AperyODEState) := by
    exact aperyODEStateField_lipschitzOnWith_of_uniform_clm_norm_le
      (a := Number.aperyConifoldZ1Poly - δ)
      (b := Number.aperyConifoldZ1Poly) hK hbound
  have hF : ∀ z ∈ I, HasDerivAt Fstate
      (aperyODEStateField z (Fstate z)) z := by
    intro z hz
    have hz_pos : 0 < z := by
      have hz1_minus_pos : 0 < Number.aperyConifoldZ1Poly - δ := by
        linarith
      exact lt_trans hz1_minus_pos hz.1
    exact aperyGFAReal_state_hasDerivAt_on_left_corridor
      (z := z) hz_pos hz.2
  have hB : ∀ z ∈ I, HasDerivAt Bstate
      (aperyODEStateField z (Bstate z)) z := by
    intro z hz
    exact hbranch z hz
  have hstate_eq : Set.EqOn Fstate Bstate I := by
    exact aperyODEState_unique_on_Ioo
      (a := Number.aperyConifoldZ1Poly - δ)
      (b := Number.aperyConifoldZ1Poly)
      (t₀ := z₀) (K := K)
      (f := Fstate) (g := Bstate) hK hLip hz₀ hF hB hinit
  intro t ht
  have hz_mem : Number.aperyConifoldZ1Poly + t ∈ I := by
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := hstate_eq hz_mem
  have hval := congrArg Prod.fst h
  have hshift :
      Number.aperyConifoldZ1Poly + t - Number.aperyConifoldZ1Poly = t := by
    ring
  simpa [Fstate, Bstate, aperyConifoldLeftTInterval, hshift] using hval

lemma apery_left_connection_of_branch_state_match_local
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hLipCompact :
      ∀ a b : ℝ,
        Number.aperyConifoldZ1Poly - δ < a → a < b →
          b < Number.aperyConifoldZ1Poly →
          ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Set.Ioo a b,
            LipschitzOnWith (Real.toNNReal K) (aperyODEStateField z)
              (Set.univ : Set AperyODEState))
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly,
      HasDerivAt
        (fun x : ℝ =>
          (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly),
            deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly)) x,
            deriv (deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly))) x))
        (aperyODEStateField z
          (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (z - Number.aperyConifoldZ1Poly),
            deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly)) z,
            deriv (deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly))) z)) z)
    (hinit :
      (aperyF5GFAReal z₀,
        deriv aperyF5GFAReal z₀,
        deriv (deriv aperyF5GFAReal) z₀) =
      (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (z₀ - Number.aperyConifoldZ1Poly),
        deriv (fun y : ℝ =>
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (y - Number.aperyConifoldZ1Poly)) z₀,
        deriv (deriv (fun y : ℝ =>
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (y - Number.aperyConifoldZ1Poly))) z₀)) :
    Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let left : ℝ := Number.aperyConifoldZ1Poly - δ
  let right : ℝ := Number.aperyConifoldZ1Poly
  let Fstate : ℝ → AperyODEState := fun z =>
    (aperyF5GFAReal z,
      deriv aperyF5GFAReal z,
      deriv (deriv aperyF5GFAReal) z)
  let Bstate : ℝ → AperyODEState := fun z =>
    (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly),
      deriv (fun y : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (y - Number.aperyConifoldZ1Poly)) z,
      deriv (deriv (fun y : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (y - Number.aperyConifoldZ1Poly))) z)
  have hleft_pos : 0 < left := by
    dsimp [left]
    linarith
  intro t ht
  let z : ℝ := Number.aperyConifoldZ1Poly + t
  have hz : z ∈ Set.Ioo left right := by
    dsimp [z, left, right, aperyConifoldLeftTInterval] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let lo : ℝ := min z₀ z
  let hi : ℝ := max z₀ z
  let a : ℝ := (left + lo) / 2
  let b : ℝ := (hi + right) / 2
  have hleft_lo : left < lo := by
    dsimp [lo]
    exact lt_min hz₀.1 hz.1
  have hhi_right : hi < right := by
    dsimp [hi]
    exact max_lt hz₀.2 hz.2
  have ha_left : left < a := by
    dsimp [a]
    linarith
  have hb_right : b < right := by
    dsimp [b]
    linarith
  have hlo_hi : lo ≤ hi := by
    dsimp [lo, hi]
    exact min_le_max
  have ha_lt_b : a < b := by
    dsimp [a, b]
    linarith
  obtain ⟨K, hK, hLip⟩ := hLipCompact a b ha_left ha_lt_b hb_right
  have hz₀_ab : z₀ ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z₀ := min_le_left _ _
      linarith
    · dsimp [b, hi]
      have hz0_le_max : z₀ ≤ max z₀ z := le_max_left _ _
      linarith
  have hz_ab : z ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z := min_le_right _ _
      linarith
    · dsimp [b, hi]
      have hz_le_max : z ≤ max z₀ z := le_max_right _ _
      linarith
  have hab_subset : Set.Ioo a b ⊆ Set.Ioo left right := by
    intro y hy
    exact ⟨lt_trans ha_left hy.1, lt_trans hy.2 hb_right⟩
  have hF : ∀ y ∈ Set.Ioo a b, HasDerivAt Fstate
      (aperyODEStateField y (Fstate y)) y := by
    intro y hy
    have hy_corr := hab_subset hy
    have hy_pos : 0 < y := lt_trans hleft_pos hy_corr.1
    exact aperyGFAReal_state_hasDerivAt_on_left_corridor
      (z := y) hy_pos hy_corr.2
  have hB : ∀ y ∈ Set.Ioo a b, HasDerivAt Bstate
      (aperyODEStateField y (Bstate y)) y := by
    intro y hy
    exact hbranch y (hab_subset hy)
  have hstate_eq : Set.EqOn Fstate Bstate (Set.Ioo a b) := by
    exact aperyODEState_unique_on_Ioo
      (a := a) (b := b) (t₀ := z₀) (K := K)
      (f := Fstate) (g := Bstate) hK hLip hz₀_ab hF hB hinit
  have h := hstate_eq hz_ab
  have hval := congrArg Prod.fst h
  have hshift : z - Number.aperyConifoldZ1Poly = t := by
    dsimp [z]
    ring
  simpa [Fstate, Bstate, z, hshift] using hval

lemma apery_left_connection_of_branch_state_match_local_auto
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly,
      HasDerivAt
        (fun x : ℝ =>
          (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly),
            deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly)) x,
            deriv (deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly))) x))
        (aperyODEStateField z
          (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (z - Number.aperyConifoldZ1Poly),
            deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly)) z,
            deriv (deriv (fun y : ℝ =>
              Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
                (y - Number.aperyConifoldZ1Poly))) z)) z)
    (hinit :
      (aperyF5GFAReal z₀,
        deriv aperyF5GFAReal z₀,
        deriv (deriv aperyF5GFAReal) z₀) =
      (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (z₀ - Number.aperyConifoldZ1Poly),
        deriv (fun y : ℝ =>
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (y - Number.aperyConifoldZ1Poly)) z₀,
        deriv (deriv (fun y : ℝ =>
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (y - Number.aperyConifoldZ1Poly))) z₀)) :
    Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  exact apery_left_connection_of_branch_state_match_local
    hδ_pos hδ_lt_z1 hz₀
    (aperyODEStateField_lipschitzOnWith_on_left_compact_subcorridor hδ_lt_z1)
    hbranch hinit

/-- State vector of the legacy reduced branch triple in the canonical `z`
coordinate.

`Ripple.Number.Frobenius.aperyBranchTriple` is built from `aperyPsSeq 0 0 Q P`.
It has the correct conifold indicial equation, but it is not the full
canonical `S,R,Q,P` Frobenius basis for `aperyGFAReal`.  Therefore the
canonical ODE-uniqueness bridge below must take an explicit `hbranch`
hypothesis; that hypothesis is the missing bridge, not something supplied
by the reduced branch package. -/
noncomputable def aperyBranchState (a₀ a_half a₁ z : ℝ) :
    AperyODEState :=
  (Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
      (z - Number.aperyConifoldZ1Poly),
    deriv (fun y : ℝ =>
      Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (y - Number.aperyConifoldZ1Poly)) z,
    deriv (deriv (fun y : ℝ =>
      Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (y - Number.aperyConifoldZ1Poly))) z)

lemma aperyBranchState_hasDerivAt_of_scalar_ode
    {a₀ a_half a₁ z y''' : ℝ}
    (hy : HasDerivAt
      (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))
      (deriv (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) z) z)
    (hy' : HasDerivAt
      (deriv (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)))
      (deriv (deriv (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))) z) z)
    (hy'' : HasDerivAt
      (deriv (deriv (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)))) y''' z)
    (hP : Polynomial.eval z Number.aperyPconifold ≠ 0)
    (hode :
      Polynomial.eval z Number.aperyPconifold * y'''
        + Polynomial.eval z Number.aperyQconifold *
          deriv (deriv (fun x : ℝ =>
            Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly))) z
        + Polynomial.eval z aperyRconifold *
          deriv (fun x : ℝ =>
            Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly)) z
        + Polynomial.eval z aperySconifold *
          Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
            (z - Number.aperyConifoldZ1Poly) = 0) :
    HasDerivAt
      (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
      (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z := by
  simpa [aperyBranchState] using
    hasDerivAt_aperyODEState_of_scalar_ode
      (y := fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))
      (y' := deriv (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)))
      (y'' := deriv (deriv (fun x : ℝ =>
        Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))))
      hy hy' hy'' hP hode

lemma apery_left_connection_exists_of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyBranchState a₀ a_half a₁ z₀ = Y) :
    ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧
      Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
        aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let Fstate : AperyODEState :=
    (aperyF5GFAReal z₀,
      deriv aperyF5GFAReal z₀,
      deriv (deriv aperyF5GFAReal) z₀)
  rcases hsurj Fstate with ⟨a₀, a_half, a₁, hmatch⟩
  refine ⟨a₀, a_half, a₁, δ, hδ_pos, ?_⟩
  refine apery_left_connection_of_branch_state_match_local_auto
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ) (z₀ := z₀)
    hδ_pos hδ_lt_z1 hz₀ ?_ ?_
  · intro z hz
    simpa [aperyBranchState] using hbranch a₀ a_half a₁ z hz
  · simpa [Fstate, aperyBranchState] using hmatch.symm

lemma aperyBranchState_eq_zero_propagates_on_left_corridor
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly,
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z)
    (hinit : aperyBranchState a₀ a_half a₁ z₀ = 0) :
    ∀ t ∈ aperyConifoldLeftTInterval δ,
      Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁ t = 0 := by
  let left : ℝ := Number.aperyConifoldZ1Poly - δ
  let right : ℝ := Number.aperyConifoldZ1Poly
  let Zstate : ℝ → AperyODEState := fun _ => 0
  intro t ht
  let z : ℝ := Number.aperyConifoldZ1Poly + t
  have hz : z ∈ Set.Ioo left right := by
    dsimp [z, left, right, aperyConifoldLeftTInterval] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let lo : ℝ := min z₀ z
  let hi : ℝ := max z₀ z
  let a : ℝ := (left + lo) / 2
  let b : ℝ := (hi + right) / 2
  have hleft_lo : left < lo := by
    dsimp [lo]
    exact lt_min hz₀.1 hz.1
  have hhi_right : hi < right := by
    dsimp [hi]
    exact max_lt hz₀.2 hz.2
  have ha_left : left < a := by
    dsimp [a]
    linarith
  have hb_right : b < right := by
    dsimp [b]
    linarith
  have ha_lt_b : a < b := by
    dsimp [a, b]
    have hlo_hi : lo ≤ hi := by
      dsimp [lo, hi]
      exact min_le_max
    linarith
  obtain ⟨K, hK, hLip⟩ :=
    aperyODEStateField_lipschitzOnWith_on_left_compact_subcorridor
      hδ_lt_z1 a b ha_left ha_lt_b hb_right
  have hz₀_ab : z₀ ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z₀ := min_le_left _ _
      linarith
    · dsimp [b, hi]
      have hz0_le_max : z₀ ≤ max z₀ z := le_max_left _ _
      linarith
  have hz_ab : z ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z := min_le_right _ _
      linarith
    · dsimp [b, hi]
      have hz_le_max : z ≤ max z₀ z := le_max_right _ _
      linarith
  have hab_subset : Set.Ioo a b ⊆ Set.Ioo left right := by
    intro y hy
    exact ⟨lt_trans ha_left hy.1, lt_trans hy.2 hb_right⟩
  have hZ : ∀ y ∈ Set.Ioo a b,
      HasDerivAt Zstate (aperyODEStateField y (Zstate y)) y := by
    intro y hy
    have hfield : aperyODEStateField y (Zstate y) = 0 := by
      simp [Zstate, aperyODEStateField]
    rw [hfield]
    exact hasDerivAt_const y (0 : AperyODEState)
  have hstate_eq : Set.EqOn
      (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
      Zstate (Set.Ioo a b) := by
    exact aperyODEState_unique_on_Ioo
      (a := a) (b := b) (t₀ := z₀) (K := K)
      (f := fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
      (g := Zstate) hK hLip hz₀_ab
      (fun y hy => hbranch y (hab_subset hy)) hZ
      (by simpa [Zstate] using hinit)
  have h := hstate_eq hz_ab
  have hval := congrArg Prod.fst h
  have hshift : z - Number.aperyConifoldZ1Poly = t := by
    dsimp [z]
    ring
  simpa [aperyBranchState, Zstate, hshift] using hval

lemma aperyBranchTriple_zero_on_left_corridor_forces_seeds_zero
    {a₀ a_half a₁ δ : ℝ} (hδ_pos : 0 < δ)
    (hzero : ∀ t ∈ aperyConifoldLeftTInterval δ,
      Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁ t = 0) :
    a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0 := by
  refine Ripple.Number.Frobenius.frobenius_three_branch_linear_independence
    hδ_pos one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    Ripple.Number.Frobenius.aperyZero_tendsto_one
    Ripple.Number.Frobenius.aperyHalf_div_sqrt_tendsto_one
    Ripple.Number.Frobenius.aperyOne_div_eps_tendsto_neg_one
    Ripple.Number.Frobenius.aperyHalf_tendsto_zero
    Ripple.Number.Frobenius.aperyOne_tendsto_zero
    Ripple.Number.Frobenius.aperyOne_div_sqrt_tendsto_zero
    ?_
  intro ε hε
  have ht : -ε ∈ aperyConifoldLeftTInterval δ := by
    dsimp [aperyConifoldLeftTInterval]
    exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have h := hzero (-ε) ht
  have hpk :
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
        Number.aperyConifoldZ1Poly = 0 :=
    Number.aperyPconifold_eval_z1
  have hz0 :
      Ripple.Number.Frobenius.yAperyZero a₀ (-ε) =
        a₀ * Ripple.Number.Frobenius.yAperyZero 1 (-ε) := by
    rw [← Ripple.Number.Frobenius.yAperyZero_smul_c₀ a₀ 1 (-ε)]
    ring_nf
  have hzh :
      Ripple.Number.Frobenius.yAperyHalf a_half (-ε) =
        a_half * Ripple.Number.Frobenius.yAperyHalf 1 (-ε) := by
    rw [← Ripple.Number.Frobenius.yAperyHalf_smul_c₀ a_half 1 (-ε)]
    ring_nf
  have hz1 :
      Ripple.Number.Frobenius.yApery a₁ (-ε) =
        a₁ * Ripple.Number.Frobenius.yApery 1 (-ε) := by
    rw [← Ripple.Number.Frobenius.yApery_smul_c₀ a₁ 1 (-ε)]
    ring_nf
  unfold Ripple.Number.Frobenius.aperyBranchTriple at h
  rw [hz0, hzh, hz1] at h
  exact h

lemma aperyBranchState_eq_zero_forces_seeds_zero
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly,
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z)
    (hinit : aperyBranchState a₀ a_half a₁ z₀ = 0) :
    a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0 := by
  exact aperyBranchTriple_zero_on_left_corridor_forces_seeds_zero hδ_pos
    (aperyBranchState_eq_zero_propagates_on_left_corridor
      hδ_pos hδ_lt_z1 hz₀ hbranch hinit)

/-- The fixed-point branch-state map, written as the linear combination of
the three pure Frobenius state columns. -/
noncomputable def aperyBranchStateLinearMap (z : ℝ) :
    AperyODEState →ₗ[ℝ] AperyODEState where
  toFun A :=
    (A.1 * (aperyBranchState 1 0 0 z).1 +
        A.2.1 * (aperyBranchState 0 1 0 z).1 +
        A.2.2 * (aperyBranchState 0 0 1 z).1,
      A.1 * (aperyBranchState 1 0 0 z).2.1 +
          A.2.1 * (aperyBranchState 0 1 0 z).2.1 +
          A.2.2 * (aperyBranchState 0 0 1 z).2.1,
        A.1 * (aperyBranchState 1 0 0 z).2.2 +
          A.2.1 * (aperyBranchState 0 1 0 z).2.2 +
          A.2.2 * (aperyBranchState 0 0 1 z).2.2)
  map_add' A B := by
    ext <;> simp <;> ring
  map_smul' c A := by
    ext <;> simp <;> ring

@[simp] lemma aperyBranchStateLinearMap_apply (z a₀ a_half a₁ : ℝ) :
    aperyBranchStateLinearMap z (a₀, a_half, a₁) =
      (a₀ * (aperyBranchState 1 0 0 z).1 +
          a_half * (aperyBranchState 0 1 0 z).1 +
          a₁ * (aperyBranchState 0 0 1 z).1,
        a₀ * (aperyBranchState 1 0 0 z).2.1 +
            a_half * (aperyBranchState 0 1 0 z).2.1 +
            a₁ * (aperyBranchState 0 0 1 z).2.1,
          a₀ * (aperyBranchState 1 0 0 z).2.2 +
            a_half * (aperyBranchState 0 1 0 z).2.2 +
            a₁ * (aperyBranchState 0 0 1 z).2.2) := rfl

private lemma aperyBranchTriple_linear_combination (a₀ a_half a₁ t : ℝ) :
    Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁ t =
      a₀ * Ripple.Number.Frobenius.aperyBranchTriple 1 0 0 t +
        a_half * Ripple.Number.Frobenius.aperyBranchTriple 0 1 0 t +
          a₁ * Ripple.Number.Frobenius.aperyBranchTriple 0 0 1 t := by
  rw [Ripple.Number.Frobenius.aperyBranchTriple_split]
  rw [Ripple.Number.Frobenius.aperyBranchTriple_only_zero_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_half_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_one_branch]
  unfold Ripple.Number.Frobenius.aperyBranchTriple
  have hz0 :
      Ripple.Number.Frobenius.yAperyZero a₀ t =
        a₀ * Ripple.Number.Frobenius.yAperyZero 1 t := by
    rw [← Ripple.Number.Frobenius.yAperyZero_smul_c₀ a₀ 1 t]
    ring
  have hzh :
      Ripple.Number.Frobenius.yAperyHalf a_half t =
        a_half * Ripple.Number.Frobenius.yAperyHalf 1 t := by
    rw [← Ripple.Number.Frobenius.yAperyHalf_smul_c₀ a_half 1 t]
    ring
  have hz1 :
      Ripple.Number.Frobenius.yApery a₁ t =
        a₁ * Ripple.Number.Frobenius.yApery 1 t := by
    rw [← Ripple.Number.Frobenius.yApery_smul_c₀ a₁ 1 t]
    ring
  have h0_zero : Ripple.Number.Frobenius.yAperyZero 0 t = 0 := by
    have := Ripple.Number.Frobenius.yAperyZero_smul_c₀ 0 1 t
    simpa using this
  have hh_zero : Ripple.Number.Frobenius.yAperyHalf 0 t = 0 := by
    have := Ripple.Number.Frobenius.yAperyHalf_smul_c₀ 0 1 t
    simpa using this
  have h1_zero : Ripple.Number.Frobenius.yApery 0 t = 0 := by
    have := Ripple.Number.Frobenius.yApery_smul_c₀ 0 1 t
    simpa using this
  rw [hz0, hzh, hz1, h0_zero, hh_zero, h1_zero]
  ring

private lemma aperyBranchStateLinearMap_eq_state
    {δ z : ℝ}
    (hz : z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ x,
      x ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun y : ℝ => aperyBranchState a₀ a_half a₁ y)
          (aperyODEStateField x (aperyBranchState a₀ a_half a₁ x)) x)
    (a₀ a_half a₁ : ℝ) :
    aperyBranchStateLinearMap z (a₀, a_half, a₁) =
      aperyBranchState a₀ a_half a₁ z := by
  let f : ℝ → ℝ := fun y =>
    Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
      (y - Number.aperyConifoldZ1Poly)
  let f0 : ℝ → ℝ := fun y =>
    Ripple.Number.Frobenius.aperyBranchTriple 1 0 0
      (y - Number.aperyConifoldZ1Poly)
  let fh : ℝ → ℝ := fun y =>
    Ripple.Number.Frobenius.aperyBranchTriple 0 1 0
      (y - Number.aperyConifoldZ1Poly)
  let f1 : ℝ → ℝ := fun y =>
    Ripple.Number.Frobenius.aperyBranchTriple 0 0 1
      (y - Number.aperyConifoldZ1Poly)
  have hf_eq : f = fun y => a₀ * f0 y + a_half * fh y + a₁ * f1 y := by
    funext y
    exact aperyBranchTriple_linear_combination a₀ a_half a₁
      (y - Number.aperyConifoldZ1Poly)
  have h0_state := hbranch 1 0 0 z hz
  have hh_state := hbranch 0 1 0 z hz
  have h1_state := hbranch 0 0 1 z hz
  have h0_diff : DifferentiableAt ℝ f0 z := by
    have h := h0_state.differentiableAt.fst
    simpa [aperyBranchState, f0] using h
  have hh_diff : DifferentiableAt ℝ fh z := by
    have h := hh_state.differentiableAt.fst
    simpa [aperyBranchState, fh] using h
  have h1_diff : DifferentiableAt ℝ f1 z := by
    have h := h1_state.differentiableAt.fst
    simpa [aperyBranchState, f1] using h
  have h0_d_diff : DifferentiableAt ℝ (deriv f0) z := by
    have h := h0_state.differentiableAt.snd.fst
    simpa [aperyBranchState, f0] using h
  have hh_d_diff : DifferentiableAt ℝ (deriv fh) z := by
    have h := hh_state.differentiableAt.snd.fst
    simpa [aperyBranchState, fh] using h
  have h1_d_diff : DifferentiableAt ℝ (deriv f1) z := by
    have h := h1_state.differentiableAt.snd.fst
    simpa [aperyBranchState, f1] using h
  have hderiv :
      deriv f z =
        a₀ * deriv f0 z + a_half * deriv fh z + a₁ * deriv f1 z := by
    let g : ℝ → ℝ := fun y => a₀ * f0 y + a_half * fh y + a₁ * f1 y
    have hg : HasDerivAt g
        (a₀ * deriv f0 z + a_half * deriv fh z + a₁ * deriv f1 z) z := by
      have h0c : HasDerivAt (fun y => a₀ * f0 y) (a₀ * deriv f0 z) z :=
        h0_diff.hasDerivAt.const_mul a₀
      have hhc : HasDerivAt (fun y => a_half * fh y) (a_half * deriv fh z) z :=
        hh_diff.hasDerivAt.const_mul a_half
      have h1c : HasDerivAt (fun y => a₁ * f1 y) (a₁ * deriv f1 z) z :=
        h1_diff.hasDerivAt.const_mul a₁
      simpa [g, add_assoc] using (h0c.add hhc).add h1c
    have hf_has : HasDerivAt f
        (a₀ * deriv f0 z + a_half * deriv fh z + a₁ * deriv f1 z) z := by
      simpa [hf_eq] using hg
    exact hf_has.deriv
  have hderiv2 :
      deriv (deriv f) z =
        a₀ * deriv (deriv f0) z +
          a_half * deriv (deriv fh) z +
            a₁ * deriv (deriv f1) z := by
    let g : ℝ → ℝ := fun y => a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y
    have hg : HasDerivAt g
        (a₀ * deriv (deriv f0) z +
          a_half * deriv (deriv fh) z +
            a₁ * deriv (deriv f1) z) z := by
      have h0c : HasDerivAt (fun y => a₀ * deriv f0 y)
          (a₀ * deriv (deriv f0) z) z :=
        h0_d_diff.hasDerivAt.const_mul a₀
      have hhc : HasDerivAt (fun y => a_half * deriv fh y)
          (a_half * deriv (deriv fh) z) z :=
        hh_d_diff.hasDerivAt.const_mul a_half
      have h1c : HasDerivAt (fun y => a₁ * deriv f1 y)
          (a₁ * deriv (deriv f1) z) z :=
        h1_d_diff.hasDerivAt.const_mul a₁
      simpa [g, add_assoc] using (h0c.add hhc).add h1c
    have hnear : ∀ᶠ y in nhds z,
        y ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly := by
      exact (isOpen_Ioo.mem_nhds hz)
    have hev : g =ᶠ[nhds z] deriv f := by
      filter_upwards [hnear] with y hy
      have hy0_state := hbranch 1 0 0 y hy
      have hyh_state := hbranch 0 1 0 y hy
      have hy1_state := hbranch 0 0 1 y hy
      have hy0 : DifferentiableAt ℝ f0 y := by
        have h := hy0_state.differentiableAt.fst
        simpa [aperyBranchState, f0] using h
      have hyh : DifferentiableAt ℝ fh y := by
        have h := hyh_state.differentiableAt.fst
        simpa [aperyBranchState, fh] using h
      have hy1 : DifferentiableAt ℝ f1 y := by
        have h := hy1_state.differentiableAt.fst
        simpa [aperyBranchState, f1] using h
      have hgy : deriv f y =
          a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y := by
        let gy : ℝ → ℝ := fun x => a₀ * f0 x + a_half * fh x + a₁ * f1 x
        have hgy_der : HasDerivAt gy
            (a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y) y := by
          have h0c : HasDerivAt (fun x => a₀ * f0 x) (a₀ * deriv f0 y) y :=
            hy0.hasDerivAt.const_mul a₀
          have hhc : HasDerivAt (fun x => a_half * fh x) (a_half * deriv fh y) y :=
            hyh.hasDerivAt.const_mul a_half
          have h1c : HasDerivAt (fun x => a₁ * f1 x) (a₁ * deriv f1 y) y :=
            hy1.hasDerivAt.const_mul a₁
          simpa [gy, add_assoc] using (h0c.add hhc).add h1c
        have hf_has : HasDerivAt f
            (a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y) y := by
          simpa [hf_eq] using hgy_der
        exact hf_has.deriv
      simp [g, hgy]
    have hdf : HasDerivAt (deriv f)
        (a₀ * deriv (deriv f0) z +
          a_half * deriv (deriv fh) z +
            a₁ * deriv (deriv f1) z) z :=
      hg.congr_of_eventuallyEq hev.symm
    exact hdf.deriv
  ext
  · simp [aperyBranchStateLinearMap, aperyBranchState,
      Ripple.Number.Frobenius.aperyBranchTriple_only_zero_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_half_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_one_branch]
    have h0_zero :
        Ripple.Number.Frobenius.yAperyZero 0 (z - Number.aperyConifoldZ1Poly) = 0 := by
      have := Ripple.Number.Frobenius.yAperyZero_smul_c₀ 0 1
        (z - Number.aperyConifoldZ1Poly)
      simpa using this
    have hh_zero :
        Ripple.Number.Frobenius.yAperyHalf 0 (z - Number.aperyConifoldZ1Poly) = 0 := by
      have := Ripple.Number.Frobenius.yAperyHalf_smul_c₀ 0 1
        (z - Number.aperyConifoldZ1Poly)
      simpa using this
    have h1_zero :
        Ripple.Number.Frobenius.yApery 0 (z - Number.aperyConifoldZ1Poly) = 0 := by
      have := Ripple.Number.Frobenius.yApery_smul_c₀ 0 1
        (z - Number.aperyConifoldZ1Poly)
      simpa using this
    have hz0 :
        Ripple.Number.Frobenius.yAperyZero a₀ (z - Number.aperyConifoldZ1Poly) =
          a₀ * Ripple.Number.Frobenius.yAperyZero 1 (z - Number.aperyConifoldZ1Poly) := by
      rw [← Ripple.Number.Frobenius.yAperyZero_smul_c₀ a₀ 1
        (z - Number.aperyConifoldZ1Poly)]
      ring
    have hzh :
        Ripple.Number.Frobenius.yAperyHalf a_half (z - Number.aperyConifoldZ1Poly) =
          a_half * Ripple.Number.Frobenius.yAperyHalf 1 (z - Number.aperyConifoldZ1Poly) := by
      rw [← Ripple.Number.Frobenius.yAperyHalf_smul_c₀ a_half 1
        (z - Number.aperyConifoldZ1Poly)]
      ring
    have hz1 :
        Ripple.Number.Frobenius.yApery a₁ (z - Number.aperyConifoldZ1Poly) =
          a₁ * Ripple.Number.Frobenius.yApery 1 (z - Number.aperyConifoldZ1Poly) := by
      rw [← Ripple.Number.Frobenius.yApery_smul_c₀ a₁ 1
        (z - Number.aperyConifoldZ1Poly)]
      ring
    unfold Ripple.Number.Frobenius.aperyBranchTriple
    rw [hz0, hzh, hz1]
  · simpa [aperyBranchStateLinearMap, aperyBranchState, f, f0, fh, f1,
      Ripple.Number.Frobenius.aperyBranchTriple_only_zero_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_half_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_one_branch] using hderiv.symm
  · simpa [aperyBranchStateLinearMap, aperyBranchState, f, f0, fh, f1,
      Ripple.Number.Frobenius.aperyBranchTriple_only_zero_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_half_branch,
      Ripple.Number.Frobenius.aperyBranchTriple_only_one_branch] using hderiv2.symm

lemma aperyBranchState_surjective_of_branch_ode
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z) :
    ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyBranchState a₀ a_half a₁ z₀ = Y := by
  let L : AperyODEState →ₗ[ℝ] AperyODEState := aperyBranchStateLinearMap z₀
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro A hA
    rcases A with ⟨a₀, a_half, a₁⟩
    have hstate : aperyBranchState a₀ a_half a₁ z₀ = 0 := by
      have hrel := aperyBranchStateLinearMap_eq_state
        (δ := δ) (z := z₀) hz₀ hbranch a₀ a_half a₁
      simpa [L, hrel] using hA
    obtain ⟨ha₀, ha_half, ha₁⟩ :=
      aperyBranchState_eq_zero_forces_seeds_zero
        hδ_pos hδ_lt_z1 hz₀
        (fun z hz => hbranch a₀ a_half a₁ z hz) hstate
    ext <;> simp [ha₀, ha_half, ha₁]
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective L :=
    LinearMap.injective_iff_surjective.mp hinj
  intro Y
  rcases hsurj Y with ⟨A, hA⟩
  rcases A with ⟨a₀, a_half, a₁⟩
  refine ⟨a₀, a_half, a₁, ?_⟩
  have hrel := aperyBranchStateLinearMap_eq_state
    (δ := δ) (z := z₀) hz₀ hbranch a₀ a_half a₁
  simpa [L, hrel] using hA

/-- State vector of the full canonical branch triple in the canonical `z`
coordinate.  This is the branch state tied to the ordinary Apéry operator
`S,R,Q,P`. -/
noncomputable def aperyCanonicalBranchState (a₀ a_half a₁ z : ℝ) :
    AperyODEState :=
  (aperyCanonicalBranchTriple a₀ a_half a₁
      (z - Number.aperyConifoldZ1Poly),
    deriv (fun y : ℝ =>
      aperyCanonicalBranchTriple a₀ a_half a₁
        (y - Number.aperyConifoldZ1Poly)) z,
    deriv (deriv (fun y : ℝ =>
      aperyCanonicalBranchTriple a₀ a_half a₁
        (y - Number.aperyConifoldZ1Poly))) z)

/-- State vector of the full canonical branch triple with the coordinate-correct
left Frobenius variable `τ = z₁ - z`. -/
noncomputable def aperyCanonicalLeftBranchState (a₀ a_half a₁ z : ℝ) :
    AperyODEState :=
  (aperyCanonicalLeftBranchTriple a₀ a_half a₁
      (z - Number.aperyConifoldZ1Poly),
    deriv (fun y : ℝ =>
      aperyCanonicalLeftBranchTriple a₀ a_half a₁
        (y - Number.aperyConifoldZ1Poly)) z,
    deriv (deriv (fun y : ℝ =>
      aperyCanonicalLeftBranchTriple a₀ a_half a₁
        (y - Number.aperyConifoldZ1Poly))) z)

lemma apery_left_connection_of_canonical_branch_state_match_local_auto
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly,
      HasDerivAt
        (fun x : ℝ => aperyCanonicalBranchState a₀ a_half a₁ x)
        (aperyODEStateField z
          (aperyCanonicalBranchState a₀ a_half a₁ z)) z)
    (hinit :
      (aperyF5GFAReal z₀,
        deriv aperyF5GFAReal z₀,
        deriv (deriv aperyF5GFAReal) z₀) =
      aperyCanonicalBranchState a₀ a_half a₁ z₀) :
    IsCanonicalAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let left : ℝ := Number.aperyConifoldZ1Poly - δ
  let right : ℝ := Number.aperyConifoldZ1Poly
  let Fstate : ℝ → AperyODEState := fun z =>
    (aperyF5GFAReal z,
      deriv aperyF5GFAReal z,
      deriv (deriv aperyF5GFAReal) z)
  let Bstate : ℝ → AperyODEState := fun z =>
    aperyCanonicalBranchState a₀ a_half a₁ z
  have hleft_pos : 0 < left := by
    dsimp [left]
    linarith
  intro t ht
  let z : ℝ := Number.aperyConifoldZ1Poly + t
  have hz : z ∈ Set.Ioo left right := by
    dsimp [z, left, right, aperyConifoldLeftTInterval] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let lo : ℝ := min z₀ z
  let hi : ℝ := max z₀ z
  let a : ℝ := (left + lo) / 2
  let b : ℝ := (hi + right) / 2
  have hleft_lo : left < lo := by
    dsimp [lo]
    exact lt_min hz₀.1 hz.1
  have hhi_right : hi < right := by
    dsimp [hi]
    exact max_lt hz₀.2 hz.2
  have ha_left : left < a := by
    dsimp [a]
    linarith
  have hb_right : b < right := by
    dsimp [b]
    linarith
  have ha_lt_b : a < b := by
    dsimp [a, b]
    have hlo_hi : lo ≤ hi := by
      dsimp [lo, hi]
      exact min_le_max
    linarith
  obtain ⟨K, hK, hLip⟩ :=
    aperyODEStateField_lipschitzOnWith_on_left_compact_subcorridor
      hδ_lt_z1 a b ha_left ha_lt_b hb_right
  have hz₀_ab : z₀ ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z₀ := min_le_left _ _
      linarith
    · dsimp [b, hi]
      have hz0_le_max : z₀ ≤ max z₀ z := le_max_left _ _
      linarith
  have hz_ab : z ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z := min_le_right _ _
      linarith
    · dsimp [b, hi]
      have hz_le_max : z ≤ max z₀ z := le_max_right _ _
      linarith
  have hab_subset : Set.Ioo a b ⊆ Set.Ioo left right := by
    intro y hy
    exact ⟨lt_trans ha_left hy.1, lt_trans hy.2 hb_right⟩
  have hF : ∀ y ∈ Set.Ioo a b, HasDerivAt Fstate
      (aperyODEStateField y (Fstate y)) y := by
    intro y hy
    have hy_corr := hab_subset hy
    have hy_pos : 0 < y := lt_trans hleft_pos hy_corr.1
    exact aperyGFAReal_state_hasDerivAt_on_left_corridor
      (z := y) hy_pos hy_corr.2
  have hB : ∀ y ∈ Set.Ioo a b, HasDerivAt Bstate
      (aperyODEStateField y (Bstate y)) y := by
    intro y hy
    exact hbranch y (hab_subset hy)
  have hstate_eq : Set.EqOn Fstate Bstate (Set.Ioo a b) := by
    exact aperyODEState_unique_on_Ioo
      (a := a) (b := b) (t₀ := z₀) (K := K)
      (f := Fstate) (g := Bstate) hK hLip hz₀_ab hF hB
      (by simpa [Fstate, Bstate] using hinit)
  have h := hstate_eq hz_ab
  have hval := congrArg Prod.fst h
  have hshift : z - Number.aperyConifoldZ1Poly = t := by
    dsimp [z]
    ring
  simpa [Fstate, Bstate, aperyCanonicalBranchState, z, hshift] using hval

lemma apery_left_connection_of_canonical_left_branch_state_match_local_auto
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly,
      HasDerivAt
        (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
        (aperyODEStateField z
          (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z)
    (hinit :
      (aperyF5GFAReal z₀,
        deriv aperyF5GFAReal z₀,
        deriv (deriv aperyF5GFAReal) z₀) =
      aperyCanonicalLeftBranchState a₀ a_half a₁ z₀) :
    IsCanonicalLeftAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let left : ℝ := Number.aperyConifoldZ1Poly - δ
  let right : ℝ := Number.aperyConifoldZ1Poly
  let Fstate : ℝ → AperyODEState := fun z =>
    (aperyF5GFAReal z,
      deriv aperyF5GFAReal z,
      deriv (deriv aperyF5GFAReal) z)
  let Bstate : ℝ → AperyODEState := fun z =>
    aperyCanonicalLeftBranchState a₀ a_half a₁ z
  have hleft_pos : 0 < left := by
    dsimp [left]
    linarith
  intro t ht
  let z : ℝ := Number.aperyConifoldZ1Poly + t
  have hz : z ∈ Set.Ioo left right := by
    dsimp [z, left, right, aperyConifoldLeftTInterval] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let lo : ℝ := min z₀ z
  let hi : ℝ := max z₀ z
  let a : ℝ := (left + lo) / 2
  let b : ℝ := (hi + right) / 2
  have hleft_lo : left < lo := by
    dsimp [lo]
    exact lt_min hz₀.1 hz.1
  have hhi_right : hi < right := by
    dsimp [hi]
    exact max_lt hz₀.2 hz.2
  have ha_left : left < a := by
    dsimp [a]
    linarith
  have hb_right : b < right := by
    dsimp [b]
    linarith
  have ha_lt_b : a < b := by
    dsimp [a, b]
    have hlo_hi : lo ≤ hi := by
      dsimp [lo, hi]
      exact min_le_max
    linarith
  obtain ⟨K, hK, hLip⟩ :=
    aperyODEStateField_lipschitzOnWith_on_left_compact_subcorridor
      hδ_lt_z1 a b ha_left ha_lt_b hb_right
  have hz₀_ab : z₀ ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z₀ := min_le_left _ _
      linarith
    · dsimp [b, hi]
      have hz0_le_max : z₀ ≤ max z₀ z := le_max_left _ _
      linarith
  have hz_ab : z ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z := min_le_right _ _
      linarith
    · dsimp [b, hi]
      have hz_le_max : z ≤ max z₀ z := le_max_right _ _
      linarith
  have hab_subset : Set.Ioo a b ⊆ Set.Ioo left right := by
    intro y hy
    exact ⟨lt_trans ha_left hy.1, lt_trans hy.2 hb_right⟩
  have hF : ∀ y ∈ Set.Ioo a b, HasDerivAt Fstate
      (aperyODEStateField y (Fstate y)) y := by
    intro y hy
    have hy_corr := hab_subset hy
    have hy_pos : 0 < y := lt_trans hleft_pos hy_corr.1
    exact aperyGFAReal_state_hasDerivAt_on_left_corridor
      (z := y) hy_pos hy_corr.2
  have hB : ∀ y ∈ Set.Ioo a b, HasDerivAt Bstate
      (aperyODEStateField y (Bstate y)) y := by
    intro y hy
    exact hbranch y (hab_subset hy)
  have hstate_eq : Set.EqOn Fstate Bstate (Set.Ioo a b) := by
    exact aperyODEState_unique_on_Ioo
      (a := a) (b := b) (t₀ := z₀) (K := K)
      (f := Fstate) (g := Bstate) hK hLip hz₀_ab hF hB
      (by simpa [Fstate, Bstate] using hinit)
  have h := hstate_eq hz_ab
  have hval := congrArg Prod.fst h
  have hshift : z - Number.aperyConifoldZ1Poly = t := by
    dsimp [z]
    ring
  simpa [Fstate, Bstate, aperyCanonicalLeftBranchState, z, hshift] using hval

lemma apery_left_canonical_connection_exists_of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyCanonicalBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyCanonicalBranchState a₀ a_half a₁ z₀ = Y) :
    ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧
      IsCanonicalAperyConnectionCoeffsOn a₀ a_half a₁
        aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let Fstate : AperyODEState :=
    (aperyF5GFAReal z₀,
      deriv aperyF5GFAReal z₀,
      deriv (deriv aperyF5GFAReal) z₀)
  rcases hsurj Fstate with ⟨a₀, a_half, a₁, hmatch⟩
  refine ⟨a₀, a_half, a₁, δ, hδ_pos, ?_⟩
  exact apery_left_connection_of_canonical_branch_state_match_local_auto
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ) (z₀ := z₀)
    hδ_pos hδ_lt_z1 hz₀
    (fun z hz => hbranch a₀ a_half a₁ z hz)
    (by simpa [Fstate] using hmatch.symm)

lemma apery_left_canonical_left_connection_exists_of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = Y) :
    ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧
      IsCanonicalLeftAperyConnectionCoeffsOn a₀ a_half a₁
        aperyF5GFAReal (aperyConifoldLeftTInterval δ) := by
  let Fstate : AperyODEState :=
    (aperyF5GFAReal z₀,
      deriv aperyF5GFAReal z₀,
      deriv (deriv aperyF5GFAReal) z₀)
  rcases hsurj Fstate with ⟨a₀, a_half, a₁, hmatch⟩
  refine ⟨a₀, a_half, a₁, δ, hδ_pos, ?_⟩
  exact apery_left_connection_of_canonical_left_branch_state_match_local_auto
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ) (z₀ := z₀)
    hδ_pos hδ_lt_z1 hz₀
    (fun z hz => hbranch a₀ a_half a₁ z hz)
    (by simpa [Fstate] using hmatch.symm)

lemma aperyCanonicalLeftBranchState_eq_zero_propagates_on_left_corridor
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly,
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z)
    (hinit : aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = 0) :
    ∀ t ∈ aperyConifoldLeftTInterval δ,
      aperyCanonicalLeftBranchTriple a₀ a_half a₁ t = 0 := by
  let left : ℝ := Number.aperyConifoldZ1Poly - δ
  let right : ℝ := Number.aperyConifoldZ1Poly
  let Zstate : ℝ → AperyODEState := fun _ => 0
  intro t ht
  let z : ℝ := Number.aperyConifoldZ1Poly + t
  have hz : z ∈ Set.Ioo left right := by
    dsimp [z, left, right, aperyConifoldLeftTInterval] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let lo : ℝ := min z₀ z
  let hi : ℝ := max z₀ z
  let a : ℝ := (left + lo) / 2
  let b : ℝ := (hi + right) / 2
  have hleft_lo : left < lo := by
    dsimp [lo]
    exact lt_min hz₀.1 hz.1
  have hhi_right : hi < right := by
    dsimp [hi]
    exact max_lt hz₀.2 hz.2
  have ha_left : left < a := by
    dsimp [a]
    linarith
  have hb_right : b < right := by
    dsimp [b]
    linarith
  have ha_lt_b : a < b := by
    dsimp [a, b]
    have hlo_hi : lo ≤ hi := by
      dsimp [lo, hi]
      exact min_le_max
    linarith
  obtain ⟨K, hK, hLip⟩ :=
    aperyODEStateField_lipschitzOnWith_on_left_compact_subcorridor
      hδ_lt_z1 a b ha_left ha_lt_b hb_right
  have hz₀_ab : z₀ ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z₀ := min_le_left _ _
      linarith
    · dsimp [b, hi]
      have hz0_le_max : z₀ ≤ max z₀ z := le_max_left _ _
      linarith
  have hz_ab : z ∈ Set.Ioo a b := by
    constructor
    · dsimp [a, lo]
      have hmin_le : min z₀ z ≤ z := min_le_right _ _
      linarith
    · dsimp [b, hi]
      have hz_le_max : z ≤ max z₀ z := le_max_right _ _
      linarith
  have hab_subset : Set.Ioo a b ⊆ Set.Ioo left right := by
    intro y hy
    exact ⟨lt_trans ha_left hy.1, lt_trans hy.2 hb_right⟩
  have hZ : ∀ y ∈ Set.Ioo a b,
      HasDerivAt Zstate (aperyODEStateField y (Zstate y)) y := by
    intro y _hy
    have hfield : aperyODEStateField y (Zstate y) = 0 := by
      simp [Zstate, aperyODEStateField]
    rw [hfield]
    exact hasDerivAt_const y (0 : AperyODEState)
  have hstate_eq : Set.EqOn
      (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
      Zstate (Set.Ioo a b) := by
    exact aperyODEState_unique_on_Ioo
      (a := a) (b := b) (t₀ := z₀) (K := K)
      (f := fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
      (g := Zstate) hK hLip hz₀_ab
      (fun y hy => hbranch y (hab_subset hy)) hZ
      (by simpa [Zstate] using hinit)
  have h := hstate_eq hz_ab
  have hval := congrArg Prod.fst h
  have hshift : z - Number.aperyConifoldZ1Poly = t := by
    dsimp [z]
    ring
  simpa [aperyCanonicalLeftBranchState, Zstate, hshift] using hval

private lemma aperyGFASecondReal_eq_canonical_second_deriv
    {z : ℝ} (hz : |z| < aperyConifoldZ1) :
    aperyGFASecondReal z =
      deriv (deriv Ripple.Number.Frobenius.aperyGFAReal) z := by
  rw [aperyGFAReal_second_deriv_eq_series (z := z) (by simpa using hz)]
  unfold aperyGFASecondReal aperyF5A Number.aperyA
  rfl

/-- Transport a canonical `aperyGFAReal` connection witness to the local F5
copy.  This isolates the remaining missing ODE/connection content: producing
the canonical left-corridor witness with `a_half < 0`. -/
lemma AperyAOrdinarySeriesHasNonzeroHalfConnection.of_canonical
    {a₀ a_half a₁ δ : ℝ} (hδ : 0 < δ) (hhalf : a_half < 0)
    (hconn : Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      Ripple.Number.Frobenius.aperyGFAReal (aperyConifoldLeftTInterval δ)) :
    AperyAOrdinarySeriesHasNonzeroHalfConnection := by
  refine ⟨a₀, a_half, a₁, δ, hδ, hhalf, ?_⟩
  refine hconn.congr ?_
  intro t _ht
  exact (aperyGFAReal_eq_canonical (Number.aperyConifoldZ1Poly + t)).symm

private lemma aperyGFAReal_eventuallyEq_branchTriple_of_left_connection
    {a₀ a_half a₁ δ x : ℝ} (_hδ : 0 < δ)
    (hx_left : Number.aperyConifoldZ1Poly - δ < x)
    (hx_right : x < Number.aperyConifoldZ1Poly)
    (hconn : Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    Ripple.Number.Frobenius.aperyGFAReal =ᶠ[nhds x]
      (fun z : ℝ => Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)) := by
  have hopen : IsOpen (Set.Ioo
      (Number.aperyConifoldZ1Poly - δ) Number.aperyConifoldZ1Poly) :=
    isOpen_Ioo
  have hmem : x ∈ Set.Ioo
      (Number.aperyConifoldZ1Poly - δ) Number.aperyConifoldZ1Poly :=
    ⟨hx_left, hx_right⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  rw [← aperyGFAReal_eq_canonical z]
  have ht : z - Number.aperyConifoldZ1Poly ∈ aperyConifoldLeftTInterval δ := by
    unfold aperyConifoldLeftTInterval
    rw [Set.mem_Ioo] at hz ⊢
    constructor <;> linarith
  have h := hconn (z - Number.aperyConifoldZ1Poly) ht
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

private lemma aperyGFASecondReal_eq_branchTriple_second_deriv_of_left_connection
    {a₀ a_half a₁ δ ε : ℝ} (hδ : 0 < δ)
    (hε_pos : 0 < ε) (hεδ : ε < δ)
    (hεz : ε < Number.aperyConifoldZ1Poly)
    (hconn : Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    aperyGFASecondReal (aperyConifoldZ1 - ε) =
      deriv (deriv
        (fun z : ℝ => Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
          (z - Number.aperyConifoldZ1Poly)))
        (aperyConifoldZ1 - ε) := by
  have hx_left :
      Number.aperyConifoldZ1Poly - δ <
        Number.aperyConifoldZ1Poly - ε := by linarith
  have hx_right :
      Number.aperyConifoldZ1Poly - ε <
        Number.aperyConifoldZ1Poly := by linarith
  have hx_abs : |aperyConifoldZ1 - ε| < aperyConifoldZ1 := by
    have hz_pos : 0 < aperyConifoldZ1 := by
      change 0 < Number.aperyConifoldZ1Poly
      exact Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hx_pos : 0 < aperyConifoldZ1 - ε := sub_pos.mpr hεz
    rw [abs_of_pos hx_pos]
    linarith
  rw [aperyGFASecondReal_eq_canonical_second_deriv (z := aperyConifoldZ1 - ε) hx_abs]
  have hev := aperyGFAReal_eventuallyEq_branchTriple_of_left_connection
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
    (x := aperyConifoldZ1 - ε) hδ
    (by
      change Number.aperyConifoldZ1Poly - δ <
        Number.aperyConifoldZ1Poly - ε
      exact hx_left)
    (by
      change Number.aperyConifoldZ1Poly - ε <
        Number.aperyConifoldZ1Poly
      exact hx_right) hconn
  exact hev.deriv.deriv_eq

private lemma aperyGFAReal_eventuallyEq_canonicalBranchTriple_of_left_connection
    {a₀ a_half a₁ δ x : ℝ} (_hδ : 0 < δ)
    (hx_left : Number.aperyConifoldZ1Poly - δ < x)
    (hx_right : x < Number.aperyConifoldZ1Poly)
    (hconn : IsCanonicalAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    Ripple.Number.Frobenius.aperyGFAReal =ᶠ[nhds x]
      (fun z : ℝ => aperyCanonicalBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)) := by
  have hopen : IsOpen (Set.Ioo
      (Number.aperyConifoldZ1Poly - δ) Number.aperyConifoldZ1Poly) :=
    isOpen_Ioo
  have hmem : x ∈ Set.Ioo
      (Number.aperyConifoldZ1Poly - δ) Number.aperyConifoldZ1Poly :=
    ⟨hx_left, hx_right⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  rw [← aperyGFAReal_eq_canonical z]
  have ht : z - Number.aperyConifoldZ1Poly ∈ aperyConifoldLeftTInterval δ := by
    unfold aperyConifoldLeftTInterval
    rw [Set.mem_Ioo] at hz ⊢
    constructor <;> linarith
  have h := hconn (z - Number.aperyConifoldZ1Poly) ht
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

private lemma aperyGFASecondReal_eq_canonicalBranchTriple_second_deriv_of_left_connection
    {a₀ a_half a₁ δ ε : ℝ} (hδ : 0 < δ)
    (hε_pos : 0 < ε) (hεδ : ε < δ)
    (hεz : ε < Number.aperyConifoldZ1Poly)
    (hconn : IsCanonicalAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    aperyGFASecondReal (aperyConifoldZ1 - ε) =
      deriv (deriv
        (fun z : ℝ => aperyCanonicalBranchTriple a₀ a_half a₁
          (z - Number.aperyConifoldZ1Poly)))
        (aperyConifoldZ1 - ε) := by
  have hx_left :
      Number.aperyConifoldZ1Poly - δ <
        Number.aperyConifoldZ1Poly - ε := by linarith
  have hx_right :
      Number.aperyConifoldZ1Poly - ε <
        Number.aperyConifoldZ1Poly := by linarith
  have hx_abs : |aperyConifoldZ1 - ε| < aperyConifoldZ1 := by
    have hz_pos : 0 < aperyConifoldZ1 := by
      change 0 < Number.aperyConifoldZ1Poly
      exact Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hx_pos : 0 < aperyConifoldZ1 - ε := sub_pos.mpr hεz
    rw [abs_of_pos hx_pos]
    linarith
  rw [aperyGFASecondReal_eq_canonical_second_deriv (z := aperyConifoldZ1 - ε) hx_abs]
  have hev := aperyGFAReal_eventuallyEq_canonicalBranchTriple_of_left_connection
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
    (x := aperyConifoldZ1 - ε) hδ
    (by
      change Number.aperyConifoldZ1Poly - δ <
        Number.aperyConifoldZ1Poly - ε
      exact hx_left)
    (by
      change Number.aperyConifoldZ1Poly - ε <
        Number.aperyConifoldZ1Poly
      exact hx_right) hconn
  exact hev.deriv.deriv_eq

private lemma aperyGFAReal_eventuallyEq_canonicalLeftBranchTriple_of_left_connection
    {a₀ a_half a₁ δ x : ℝ} (_hδ : 0 < δ)
    (hx_left : Number.aperyConifoldZ1Poly - δ < x)
    (hx_right : x < Number.aperyConifoldZ1Poly)
    (hconn : IsCanonicalLeftAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    Ripple.Number.Frobenius.aperyGFAReal =ᶠ[nhds x]
      (fun z : ℝ => aperyCanonicalLeftBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)) := by
  have hopen : IsOpen (Set.Ioo
      (Number.aperyConifoldZ1Poly - δ) Number.aperyConifoldZ1Poly) :=
    isOpen_Ioo
  have hmem : x ∈ Set.Ioo
      (Number.aperyConifoldZ1Poly - δ) Number.aperyConifoldZ1Poly :=
    ⟨hx_left, hx_right⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  rw [← aperyGFAReal_eq_canonical z]
  have ht : z - Number.aperyConifoldZ1Poly ∈ aperyConifoldLeftTInterval δ := by
    unfold aperyConifoldLeftTInterval
    rw [Set.mem_Ioo] at hz ⊢
    constructor <;> linarith
  have h := hconn (z - Number.aperyConifoldZ1Poly) ht
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

private lemma aperyGFASecondReal_eq_canonicalLeftBranchTriple_second_deriv_of_left_connection
    {a₀ a_half a₁ δ ε : ℝ} (hδ : 0 < δ)
    (hε_pos : 0 < ε) (hεδ : ε < δ)
    (hεz : ε < Number.aperyConifoldZ1Poly)
    (hconn : IsCanonicalLeftAperyConnectionCoeffsOn a₀ a_half a₁
      aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    aperyGFASecondReal (aperyConifoldZ1 - ε) =
      deriv (deriv
        (fun z : ℝ => aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (z - Number.aperyConifoldZ1Poly)))
        (aperyConifoldZ1 - ε) := by
  have hx_left :
      Number.aperyConifoldZ1Poly - δ <
        Number.aperyConifoldZ1Poly - ε := by linarith
  have hx_right :
      Number.aperyConifoldZ1Poly - ε <
        Number.aperyConifoldZ1Poly := by linarith
  have hx_abs : |aperyConifoldZ1 - ε| < aperyConifoldZ1 := by
    have hz_pos : 0 < aperyConifoldZ1 := by
      change 0 < Number.aperyConifoldZ1Poly
      exact Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hx_pos : 0 < aperyConifoldZ1 - ε := sub_pos.mpr hεz
    rw [abs_of_pos hx_pos]
    linarith
  rw [aperyGFASecondReal_eq_canonical_second_deriv (z := aperyConifoldZ1 - ε) hx_abs]
  have hev := aperyGFAReal_eventuallyEq_canonicalLeftBranchTriple_of_left_connection
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
    (x := aperyConifoldZ1 - ε) hδ
    (by
      change Number.aperyConifoldZ1Poly - δ <
        Number.aperyConifoldZ1Poly - ε
      exact hx_left)
    (by
      change Number.aperyConifoldZ1Poly - ε <
        Number.aperyConifoldZ1Poly
      exact hx_right) hconn
  exact hev.deriv.deriv_eq

private lemma hasDerivAt_sqrt_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun u : ℝ => Real.sqrt (-u))
      (-(1 / (2 * Real.sqrt (-t)))) t := by
  have hneg : HasDerivAt (fun u : ℝ => -u) (-1) t := by
    simpa using (hasDerivAt_id t).neg
  have hne : -t ≠ 0 := by linarith
  have h := hneg.sqrt hne
  convert h using 1
  ring

private lemma hasDerivAt_sqrt_neg_inv_factor {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun u : ℝ => -(1 / (2 * Real.sqrt (-u))))
      (-(1 / (4 * (Real.sqrt (-t)) ^ 3))) t := by
  have hs := hasDerivAt_sqrt_neg ht
  have hs_ne : Real.sqrt (-t) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have hinv := hs.inv hs_ne
  have hmul := hinv.const_mul (-(1 / 2 : ℝ))
  have hfun : (fun u : ℝ => -(1 / (2 * Real.sqrt (-u)))) =
      (fun u : ℝ => -(1 / 2 : ℝ) * (Real.sqrt (-u))⁻¹) := by
    funext u
    by_cases hu : Real.sqrt (-u) = 0
    · simp [hu]
    · field_simp [hu]
  rw [hfun]
  convert hmul using 1
  field_simp [hs_ne]
  ring_nf

private lemma hasDerivAt_sqrt_neg_mul_core
    {V Vp : ℝ → ℝ} {t : ℝ} (ht : t < 0)
    (hV : HasDerivAt V (Vp t) t) :
    HasDerivAt (fun u : ℝ => Real.sqrt (-u) * V u)
      (-(1 / (2 * Real.sqrt (-t))) * V t +
        Real.sqrt (-t) * Vp t) t := by
  exact (hasDerivAt_sqrt_neg ht).mul hV

private lemma hasDerivAt_sqrt_neg_mul_core_deriv
    {V Vp Vpp : ℝ → ℝ} {t : ℝ} (ht : t < 0)
    (hV : HasDerivAt V (Vp t) t)
    (hVp : HasDerivAt Vp (Vpp t) t) :
    HasDerivAt
      (fun u : ℝ =>
        -(1 / (2 * Real.sqrt (-u))) * V u +
          Real.sqrt (-u) * Vp u)
      (-(1 / (4 * (Real.sqrt (-t)) ^ 3)) * V t -
        Vp t / Real.sqrt (-t) + Real.sqrt (-t) * Vpp t) t := by
  have hf := hasDerivAt_sqrt_neg_inv_factor ht
  have hs := hasDerivAt_sqrt_neg ht
  have hleft := hf.mul hV
  have hright := hs.mul hVp
  have hsum := hleft.add hright
  have hs_ne : Real.sqrt (-t) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  convert hsum using 1
  field_simp [hs_ne]
  ring

private lemma hasDerivAt_sqrt_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := by
  simpa using (hasDerivAt_id t).sqrt (ne_of_gt ht)

private lemma hasDerivAt_sqrt_pos_inv_factor {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => 1 / (2 * Real.sqrt u))
      (-(1 / (4 * (Real.sqrt t) ^ 3))) t := by
  have hs := hasDerivAt_sqrt_pos ht
  have hs_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hinv := hs.inv hs_ne
  have hmul := hinv.const_mul ((1 / 2 : ℝ))
  have hfun : (fun u : ℝ => 1 / (2 * Real.sqrt u)) =
      (fun u : ℝ => (1 / 2 : ℝ) * (Real.sqrt u)⁻¹) := by
    funext u
    by_cases hu : Real.sqrt u = 0
    · simp [hu]
    · field_simp [hu]
  rw [hfun]
  convert hmul using 1
  field_simp [hs_ne]
  ring_nf

private lemma hasDerivAt_sqrt_pos_mul_core
    {V Vp : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hV : HasDerivAt V (Vp t) t) :
    HasDerivAt (fun u : ℝ => Real.sqrt u * V u)
      ((1 / (2 * Real.sqrt t)) * V t +
        Real.sqrt t * Vp t) t := by
  exact (hasDerivAt_sqrt_pos ht).mul hV

private lemma hasDerivAt_sqrt_pos_mul_core_deriv
    {V Vp Vpp : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hV : HasDerivAt V (Vp t) t)
    (hVp : HasDerivAt Vp (Vpp t) t) :
    HasDerivAt
      (fun u : ℝ =>
        (1 / (2 * Real.sqrt u)) * V u +
          Real.sqrt u * Vp u)
      (-(1 / (4 * (Real.sqrt t) ^ 3)) * V t +
        Vp t / Real.sqrt t + Real.sqrt t * Vpp t) t := by
  have hf := hasDerivAt_sqrt_pos_inv_factor ht
  have hs := hasDerivAt_sqrt_pos ht
  have hleft := hf.mul hV
  have hright := hs.mul hVp
  have hsum := hleft.add hright
  have hs_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  convert hsum using 1
  field_simp [hs_ne]
  ring

private lemma hasDerivAt_sqrt_pos_inv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (Real.sqrt u)⁻¹)
      (-(1 / (2 * (Real.sqrt t) ^ 3))) t := by
  have hs := hasDerivAt_sqrt_pos ht
  have hs_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hinv := hs.inv hs_ne
  convert hinv using 1
  field_simp [hs_ne]

private lemma hasDerivAt_sqrt_pos_inv_cube_factor {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => -(1 / (4 * (Real.sqrt u) ^ 3)))
      (3 / (8 * (Real.sqrt t) ^ 5)) t := by
  have hinv := hasDerivAt_sqrt_pos_inv ht
  have hcube := hinv.pow 3
  have hcoef := hcube.const_mul (-(1 / 4 : ℝ))
  have hs_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hfun : (fun u : ℝ => -(1 / (4 * (Real.sqrt u) ^ 3))) =
      fun u : ℝ => -(1 / 4 : ℝ) * ((Real.sqrt u)⁻¹) ^ 3 := by
    funext u
    by_cases hu : Real.sqrt u = 0
    · simp [hu]
    · field_simp [hu]
  rw [hfun]
  convert hcoef using 1
  field_simp [hs_ne]
  norm_num
  field_simp [hs_ne]
  norm_num

private lemma hasDerivAt_sqrt_pos_mul_core_deriv2
    {V Vp Vpp Vppp : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hV : HasDerivAt V (Vp t) t)
    (hVp : HasDerivAt Vp (Vpp t) t)
    (hVpp : HasDerivAt Vpp (Vppp t) t) :
    HasDerivAt
      (fun u : ℝ =>
        -(1 / (4 * (Real.sqrt u) ^ 3)) * V u +
          Vp u / Real.sqrt u + Real.sqrt u * Vpp u)
      (3 / (8 * (Real.sqrt t) ^ 5) * V t
        - 3 / (4 * (Real.sqrt t) ^ 3) * Vp t
        + 3 / (2 * Real.sqrt t) * Vpp t
        + Real.sqrt t * Vppp t) t := by
  have hcoef := hasDerivAt_sqrt_pos_inv_cube_factor ht
  have hinv := hasDerivAt_sqrt_pos_inv ht
  have hs := hasDerivAt_sqrt_pos ht
  have hleft := hcoef.mul hV
  have hmid := hinv.mul hVp
  have hright := hs.mul hVpp
  have hsum := (hleft.add hmid).add hright
  have hs_ne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  convert hsum using 1
  · ext u
    simp only [Pi.add_apply, Pi.mul_apply]
    by_cases hu : Real.sqrt u = 0
    · simp [hu]
    · field_simp [hu]
  · field_simp [hs_ne]
    ring

private lemma aperyCanonical_half_raw_eq_scaled_scalar
    {τ V Vp Vpp Vppp S R Q P : ℝ} (hτ : 0 < τ) :
    τ ^ 2 * Real.sqrt τ *
        (P * (-(3 / (8 * (Real.sqrt τ) ^ 5)) * V
              + (3 / (4 * (Real.sqrt τ) ^ 3)) * Vp
              - (3 / (2 * Real.sqrt τ)) * Vpp
              - Real.sqrt τ * Vppp)
          + Q * (-(1 / (4 * (Real.sqrt τ) ^ 3)) * V
              + Vp / Real.sqrt τ + Real.sqrt τ * Vpp)
          + R * (-(1 / (2 * Real.sqrt τ)) * V - Real.sqrt τ * Vp)
          + S * (Real.sqrt τ * V)) =
      τ ^ 3 * S * V
        - τ ^ 2 * R * (τ * Vp + (1 / 2) * V)
        + τ * Q * (τ ^ 2 * Vpp + τ * Vp - (1 / 4) * V)
        - P * (τ ^ 3 * Vppp + (3 / 2) * τ ^ 2 * Vpp
            - (3 / 4) * τ * Vp + (3 / 8) * V) := by
  have hs_ne : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  have hs2 : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
  field_simp [hs_ne]
  rw [show (Real.sqrt τ) ^ 4 = τ ^ 2 by
    rw [show (Real.sqrt τ) ^ 4 = ((Real.sqrt τ) ^ 2) ^ 2 by ring, hs2]]
  rw [show (Real.sqrt τ) ^ 6 = τ ^ 3 by
    rw [show (Real.sqrt τ) ^ 6 = ((Real.sqrt τ) ^ 2) ^ 3 by ring, hs2]]
  rw [hs2]
  ring

private lemma aperyCanonical_half_scalar_ode_of_raw
    {τ V Vp Vpp Vppp S R Q P : ℝ} (hτ : 0 < τ)
    (hraw :
      τ ^ 3 * S * V
        - τ ^ 2 * R * (τ * Vp + (1 / 2) * V)
        + τ * Q * (τ ^ 2 * Vpp + τ * Vp - (1 / 4) * V)
        - P * (τ ^ 3 * Vppp + (3 / 2) * τ ^ 2 * Vpp
            - (3 / 4) * τ * Vp + (3 / 8) * V) = 0) :
    P * (-(3 / (8 * (Real.sqrt τ) ^ 5)) * V
          + (3 / (4 * (Real.sqrt τ) ^ 3)) * Vp
          - (3 / (2 * Real.sqrt τ)) * Vpp
          - Real.sqrt τ * Vppp)
      + Q * (-(1 / (4 * (Real.sqrt τ) ^ 3)) * V
          + Vp / Real.sqrt τ + Real.sqrt τ * Vpp)
      + R * (-(1 / (2 * Real.sqrt τ)) * V - Real.sqrt τ * Vp)
      + S * (Real.sqrt τ * V) = 0 := by
  have hscaled := aperyCanonical_half_raw_eq_scaled_scalar
    (τ := τ) (V := V) (Vp := Vp) (Vpp := Vpp) (Vppp := Vppp)
    (S := S) (R := R) (Q := Q) (P := P) hτ
  rw [hraw] at hscaled
  have hfactor_ne : τ ^ 2 * Real.sqrt τ ≠ 0 := by
    have hτ_ne : τ ≠ 0 := ne_of_gt hτ
    have hs_ne : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
    exact mul_ne_zero (pow_ne_zero 2 hτ_ne) hs_ne
  exact mul_eq_zero.mp hscaled |>.resolve_left hfactor_ne

private lemma fallingFactorial_half_add_nat_one (m : ℕ) :
    fallingFactorial ((1 / 2 : ℝ) + (m : ℝ)) 1 = (m : ℝ) + 1 / 2 := by
  rw [fallingFactorial_one]
  ring

private lemma fallingFactorial_half_add_nat_two (m : ℕ) :
    fallingFactorial ((1 / 2 : ℝ) + (m : ℝ)) 2 =
      fallingFactorial (m : ℝ) 2 + (m : ℝ) - 1 / 4 := by
  rw [fallingFactorial_two, fallingFactorial_two]
  ring_nf

private lemma fallingFactorial_half_add_nat_three (m : ℕ) :
    fallingFactorial ((1 / 2 : ℝ) + (m : ℝ)) 3 =
      fallingFactorial (m : ℝ) 3 + (3 / 2) * fallingFactorial (m : ℝ) 2
        - (3 / 4) * (m : ℝ) + 3 / 8 := by
  simp only [fallingFactorial_two, fallingFactorial_three]
  ring_nf

private lemma frobeniusCoeff_falling_t_pow_summable_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ j : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    Summable (fun m : ℕ =>
      fallingFactorial ((m : ℕ) : ℝ) j *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  have h_absj := frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
    ps n z₁ ρ c₀ M₀ j hpk hslope hM0_small hM0_large
    h_thresh_general B hB_nn hB s hs_nn hs_lt
  apply Summable.of_norm
  refine h_absj.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
  calc ‖fallingFactorial ((m : ℕ) : ℝ) j *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
      = |fallingFactorial ((m : ℕ) : ℝ) j| *
            |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ |fallingFactorial ((m : ℕ) : ℝ) j| *
            |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
        mul_le_mul_of_nonneg_left (hs_abs_pow m)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem frobeniusValueDeriv_tsum_euler_half_one_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 1 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t * frobeniusValueDeriv ps n z₁ ρ c₀ t +
        (1 / 2) * frobeniusValue ps n z₁ ρ c₀ t := by
  have hsum0 : Summable (fun m : ℕ =>
      frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 0
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hsum1 : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa [fallingFactorial_one] using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 1
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hpt : ∀ m : ℕ,
      fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 1 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m =
        (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m +
          (1 / 2) * (frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    intro m
    rw [fallingFactorial_half_add_nat_one]
    ring
  rw [tsum_congr hpt]
  rw [hsum1.tsum_add (hsum0.mul_left (1 / 2))]
  rw [tsum_mul_left]
  rw [frobeniusValueDeriv_tsum_euler_one_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  unfold frobeniusValue
  ring

private theorem frobeniusValueDeriv_tsum_euler_half_two_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 2 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 2 * frobeniusValueDeriv2 ps n z₁ ρ c₀ t +
        t * frobeniusValueDeriv ps n z₁ ρ c₀ t -
        (1 / 4) * frobeniusValue ps n z₁ ρ c₀ t := by
  have hsum0 : Summable (fun m : ℕ =>
      frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 0
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hsum1 : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa [fallingFactorial_one] using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 1
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hsum2 : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) :=
    frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 2
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
      s hs_nn hs_lt t ht_abs
  have hpt : ∀ m : ℕ,
      fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 2 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m =
        (fallingFactorial (m : ℝ) 2 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m +
          (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) +
          (-1 / 4) * (frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    intro m
    rw [fallingFactorial_half_add_nat_two]
    ring
  rw [tsum_congr hpt]
  rw [(hsum2.add hsum1).tsum_add (hsum0.mul_left (-1 / 4))]
  rw [hsum2.tsum_add hsum1]
  rw [tsum_mul_left]
  rw [frobeniusValueDeriv_tsum_euler_two_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  rw [frobeniusValueDeriv_tsum_euler_one_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  unfold frobeniusValue
  ring

private theorem frobeniusValueDeriv_tsum_euler_half_three_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 3 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 3 * frobeniusValueDeriv3 ps n z₁ ρ c₀ t +
        (3 / 2) * (t ^ 2 * frobeniusValueDeriv2 ps n z₁ ρ c₀ t) -
        (3 / 4) * (t * frobeniusValueDeriv ps n z₁ ρ c₀ t) +
        (3 / 8) * frobeniusValue ps n z₁ ρ c₀ t := by
  have hsum0 : Summable (fun m : ℕ =>
      frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 0
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hsum1 : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa [fallingFactorial_one] using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 1
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hsum2 : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) :=
    frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 2
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
      s hs_nn hs_lt t ht_abs
  have hsum3 : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 3 * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) :=
    frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 3
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
      s hs_nn hs_lt t ht_abs
  have hpt : ∀ m : ℕ,
      fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 3 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m =
        ((fallingFactorial (m : ℝ) 3 *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m +
          (3 / 2) * (fallingFactorial (m : ℝ) 2 *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)) +
          (-3 / 4) * ((m : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)) +
          (3 / 8) * (frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    intro m
    rw [fallingFactorial_half_add_nat_three]
    ring
  rw [tsum_congr hpt]
  rw [((hsum3.add (hsum2.mul_left (3 / 2))).add
    (hsum1.mul_left (-3 / 4))).tsum_add (hsum0.mul_left (3 / 8))]
  rw [(hsum3.add (hsum2.mul_left (3 / 2))).tsum_add
    (hsum1.mul_left (-3 / 4))]
  rw [hsum3.tsum_add (hsum2.mul_left (3 / 2))]
  rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [frobeniusValueDeriv_tsum_euler_three_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  rw [frobeniusValueDeriv_tsum_euler_two_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  rw [frobeniusValueDeriv_tsum_euler_one_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  unfold frobeniusValue
  ring

private theorem frobeniusValueDeriv_tsum_euler_shift_one_one_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 1 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t * frobeniusValueDeriv ps n z₁ ρ c₀ t +
        frobeniusValue ps n z₁ ρ c₀ t := by
  have hsum0 : Summable (fun m : ℕ =>
      frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 0
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hsum1 : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    simpa [fallingFactorial_one] using
      frobeniusCoeff_falling_t_pow_summable_general ps n z₁ ρ c₀ M₀ 1
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs
  have hpt : ∀ m : ℕ,
      fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 1 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m =
        (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m +
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m := by
    intro m
    rw [fallingFactorial_one]
    ring
  rw [tsum_congr hpt]
  rw [hsum1.tsum_add hsum0]
  rw [frobeniusValueDeriv_tsum_euler_one_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
    s hs_nn hs_lt t ht_abs]
  unfold frobeniusValue
  ring

private lemma frobeniusCoeff_half_falling_abs_mul_pow_summable_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ j : ℕ)
    (hj : j ∈ Finset.range 4)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m : ℕ =>
      |fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) j| *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  have hbase : ∀ k : ℕ, Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) k| *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    intro k
    exact frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
      ps n z₁ ρ c₀ M₀ k hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB s hs_nn hs_lt
  have hj_lt : j < 4 := by simpa using hj
  interval_cases j
  · simpa using hbase 0
  · have hmaj := (hbase 1).add ((hbase 0).mul_left (1 / 2 : ℝ))
    refine hmaj.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    have htail_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
      mul_nonneg (abs_nonneg _) (pow_nonneg hs_nn _)
    have hff : |((m : ℕ) : ℝ) + 1 / 2| ≤ |((m : ℕ) : ℝ)| + 1 / 2 := by
      calc |((m : ℕ) : ℝ) + 1 / 2|
          ≤ |((m : ℕ) : ℝ)| + |(1 / 2 : ℝ)| := abs_add_le _ _
        _ = |((m : ℕ) : ℝ)| + 1 / 2 := by norm_num
    calc
      |fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 1| *
          |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
          ≤ (|((m : ℕ) : ℝ)| + 1 / 2) *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by
            rw [fallingFactorial_half_add_nat_one]
            calc
              |↑m + 1 / 2| * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
                  = |↑m + 1 / 2| *
                      (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring
              _ ≤ (|↑m| + 1 / 2) *
                    (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
                  mul_le_mul_of_nonneg_right hff htail_nn
              _ = (|↑m| + 1 / 2) *
                    |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by ring
        _ = |fallingFactorial ((m : ℕ) : ℝ) 1| *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m +
            (1 / 2) *
              (|fallingFactorial ((m : ℕ) : ℝ) 0| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
            rw [fallingFactorial_one, fallingFactorial_zero]
            ring
  · have hmaj := ((hbase 2).add (hbase 1)).add ((hbase 0).mul_left (1 / 4 : ℝ))
    refine hmaj.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    have htail_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
      mul_nonneg (abs_nonneg _) (pow_nonneg hs_nn _)
    have hff : |fallingFactorial ((m : ℕ) : ℝ) 2 + ((m : ℕ) : ℝ) - 1 / 4|
        ≤ |fallingFactorial ((m : ℕ) : ℝ) 2| + |((m : ℕ) : ℝ)| + 1 / 4 := by
      calc
        |fallingFactorial ((m : ℕ) : ℝ) 2 + ((m : ℕ) : ℝ) - 1 / 4|
            = |fallingFactorial ((m : ℕ) : ℝ) 2 + (((m : ℕ) : ℝ) - 1 / 4)| := by
                ring_nf
        _ ≤ |fallingFactorial ((m : ℕ) : ℝ) 2| + |((m : ℕ) : ℝ) - 1 / 4| :=
            abs_add_le _ _
        _ ≤ |fallingFactorial ((m : ℕ) : ℝ) 2| +
              (|((m : ℕ) : ℝ)| + 1 / 4) := by
            have hm_quarter : |((m : ℕ) : ℝ) - 1 / 4| ≤
                |((m : ℕ) : ℝ)| + 1 / 4 := by
              calc
                |((m : ℕ) : ℝ) - 1 / 4|
                    = |((m : ℕ) : ℝ) + (-1 / 4 : ℝ)| := by ring_nf
                _ ≤ |((m : ℕ) : ℝ)| + |(-1 / 4 : ℝ)| :=
                    abs_add_le (((m : ℕ) : ℝ)) (-1 / 4 : ℝ)
                _ = |((m : ℕ) : ℝ)| + 1 / 4 := by norm_num
            exact add_le_add (le_refl _) hm_quarter
        _ = |fallingFactorial ((m : ℕ) : ℝ) 2| + |((m : ℕ) : ℝ)| + 1 / 4 := by
            ring
    calc
      |fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 2| *
          |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
          ≤ (|fallingFactorial ((m : ℕ) : ℝ) 2| + |((m : ℕ) : ℝ)| + 1 / 4) *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by
            rw [fallingFactorial_half_add_nat_two]
            calc
              |fallingFactorial (↑m) 2 + ↑m - 1 / 4| *
                    |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
                  = |fallingFactorial (↑m) 2 + ↑m - 1 / 4| *
                      (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring
              _ ≤ (|fallingFactorial (↑m) 2| + |↑m| + 1 / 4) *
                    (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
                  mul_le_mul_of_nonneg_right hff htail_nn
              _ = (|fallingFactorial (↑m) 2| + |↑m| + 1 / 4) *
                    |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by ring
        _ = (|fallingFactorial ((m : ℕ) : ℝ) 2| *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m +
            |fallingFactorial ((m : ℕ) : ℝ) 1| *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) +
            (1 / 4) *
              (|fallingFactorial ((m : ℕ) : ℝ) 0| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
            rw [fallingFactorial_one, fallingFactorial_zero]
            ring
  · have hmaj_pos := (((hbase 3).add ((hbase 2).mul_left (3 / 2 : ℝ))).add
      ((hbase 1).mul_left (3 / 4 : ℝ))).add ((hbase 0).mul_left (3 / 8 : ℝ))
    refine hmaj_pos.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    have htail_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
      mul_nonneg (abs_nonneg _) (pow_nonneg hs_nn _)
    have hff : |fallingFactorial ((m : ℕ) : ℝ) 3 +
          (3 / 2) * fallingFactorial ((m : ℕ) : ℝ) 2 -
          (3 / 4) * ((m : ℕ) : ℝ) + 3 / 8|
        ≤ |fallingFactorial ((m : ℕ) : ℝ) 3| +
          (3 / 2) * |fallingFactorial ((m : ℕ) : ℝ) 2| +
          (3 / 4) * |((m : ℕ) : ℝ)| + 3 / 8 := by
      calc
        |fallingFactorial ((m : ℕ) : ℝ) 3 +
            (3 / 2) * fallingFactorial ((m : ℕ) : ℝ) 2 -
            (3 / 4) * ((m : ℕ) : ℝ) + 3 / 8|
            = |(fallingFactorial ((m : ℕ) : ℝ) 3 +
                (3 / 2) * fallingFactorial ((m : ℕ) : ℝ) 2) +
                (-(3 / 4) * ((m : ℕ) : ℝ) + 3 / 8)| := by
              ring_nf
        _ ≤ |fallingFactorial ((m : ℕ) : ℝ) 3 +
                (3 / 2) * fallingFactorial ((m : ℕ) : ℝ) 2| +
              |-(3 / 4) * ((m : ℕ) : ℝ) + 3 / 8| := abs_add_le _ _
        _ ≤ (|fallingFactorial ((m : ℕ) : ℝ) 3| +
                |(3 / 2) * fallingFactorial ((m : ℕ) : ℝ) 2|) +
              (|-(3 / 4) * ((m : ℕ) : ℝ)| + |(3 / 8 : ℝ)|) := by
              exact add_le_add (abs_add_le _ _) (abs_add_le _ _)
        _ = |fallingFactorial ((m : ℕ) : ℝ) 3| +
              (3 / 2) * |fallingFactorial ((m : ℕ) : ℝ) 2| +
              (3 / 4) * |((m : ℕ) : ℝ)| + 3 / 8 := by
            rw [abs_mul, abs_mul]
            norm_num
            ring
    calc
      |fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 3| *
          |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
          ≤ (|fallingFactorial ((m : ℕ) : ℝ) 3| +
              (3 / 2) * |fallingFactorial ((m : ℕ) : ℝ) 2| +
              (3 / 4) * |((m : ℕ) : ℝ)| + 3 / 8) *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by
            rw [fallingFactorial_half_add_nat_three]
            calc
              |fallingFactorial (↑m) 3 + 3 / 2 * fallingFactorial (↑m) 2 -
                    3 / 4 * ↑m + 3 / 8| *
                    |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
                  = |fallingFactorial (↑m) 3 + 3 / 2 * fallingFactorial (↑m) 2 -
                        3 / 4 * ↑m + 3 / 8| *
                      (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring
              _ ≤ (|fallingFactorial (↑m) 3| +
                    (3 / 2) * |fallingFactorial (↑m) 2| +
                    (3 / 4) * |↑m| + 3 / 8) *
                    (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
                  mul_le_mul_of_nonneg_right hff htail_nn
              _ = (|fallingFactorial (↑m) 3| +
                    (3 / 2) * |fallingFactorial (↑m) 2| +
                    (3 / 4) * |↑m| + 3 / 8) *
                    |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by ring
        _ = ((|fallingFactorial ((m : ℕ) : ℝ) 3| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m +
              (3 / 2) *
                (|fallingFactorial ((m : ℕ) : ℝ) 2| *
                  |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m)) +
              (3 / 4) *
                (|fallingFactorial ((m : ℕ) : ℝ) 1| *
                  |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m)) +
              (3 / 8) *
                (|fallingFactorial ((m : ℕ) : ℝ) 0| *
                  |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
            rw [fallingFactorial_one, fallingFactorial_zero]
            ring

set_option maxHeartbeats 800000 in
-- Expanding the four Frobenius Euler sums produces a large real-ring normal form.
private lemma aperyCanonical_half_raw_ode
    (c₀ s τ : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hτ_abs : |τ| ≤ s) :
    τ ^ 3 * (taylorShift aperySconifold Number.aperyConifoldZ1Poly).eval τ *
        frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ τ
      - τ ^ 2 * (taylorShift aperyRconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ τ +
          (1 / 2) * frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ)
      + τ * (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ ^ 2 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ τ +
          τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ -
          (1 / 4) * frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ)
      - (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ ^ 3 * frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ τ +
          (3 / 2) * (τ ^ 2 *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ τ) -
          (3 / 4) * (τ *
            frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ τ) +
          (3 / 8) * frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ) = 0 := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps2 : ps 2 = Number.aperyQconifold := by rw [hps_def]; rfl
  have hps3 : ps 3 = Number.aperyPconifold := by rw [hps_def]; rfl
  have hpk : (ps 3).eval z₁ = 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB : ∀ j ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j hj ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j (by simp at hj ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * 1000 * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    rw [show ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) by norm_num]
    rw [show ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 by norm_num]
    rw [hps3, hz_def]
    exact hs_lt
  have hbase :=
    pointwise_substLHS_analytic_eq_zero_at_rho ps 2 z₁ (1 / 2) c₀
      hpk
      (by simpa [hps_def, hz_def] using aperyCanonical_simpleZero_half)
      (by simpa [hps_def, hz_def] using aperyCanonical_no_integer_shift_half)
      s
      (fun j hj =>
        frobeniusCoeff_half_falling_abs_mul_pow_summable_general
          ps 2 z₁ (1 / 2) c₀ 9 j hj hpk hslope
          aperyCanonicalHalf_small aperyCanonicalHalf_large
          (fun m hm => by
            simpa [hps_def, hz_def] using aperyCanonicalHalf_threshold m hm)
          1000 (by norm_num) hB
          s hs_nn hs_lt')
      τ hτ_abs
  have h_sum_expand :
      ∑ j ∈ Finset.range (2 + 2),
          ((-1 : ℝ) ^ j) * τ ^ ((2 + 1) - j) *
            (taylorShift (ps j) z₁).eval τ *
            ∑' m : ℕ, fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) j *
              frobeniusCoeff ps 2 z₁ (1 / 2) c₀ m * τ ^ m
        =
        τ ^ 3 * (taylorShift (ps 0) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 0 *
              frobeniusCoeff ps 2 z₁ (1 / 2) c₀ m * τ ^ m)
          - τ ^ 2 * (taylorShift (ps 1) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 1 *
              frobeniusCoeff ps 2 z₁ (1 / 2) c₀ m * τ ^ m)
          + τ * (taylorShift (ps 2) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 2 *
              frobeniusCoeff ps 2 z₁ (1 / 2) c₀ m * τ ^ m)
          - (taylorShift (ps 3) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 3 *
              frobeniusCoeff ps 2 z₁ (1 / 2) c₀ m * τ ^ m) := by
    rw [show (2 + 2 : ℕ) = 3 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    ring
  rw [h_sum_expand] at hbase
  have hI0 :
      (∑' m : ℕ, fallingFactorial ((1 / 2 : ℝ) + ((m : ℕ) : ℝ)) 0 *
          frobeniusCoeff ps 2 z₁ (1 / 2) c₀ m * τ ^ m) =
        frobeniusValue ps 2 z₁ (1 / 2) c₀ τ := by
    simpa using
      frobeniusValueDeriv_tsum_euler_zero ps 2 z₁ (1 / 2) c₀ τ
  have hI1 :=
    frobeniusValueDeriv_tsum_euler_half_one_general ps 2 z₁ (1 / 2) c₀ 9
      hpk hslope aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold 1000 (by norm_num) hB s hs_nn hs_lt' τ hτ_abs
  have hI2 :=
    frobeniusValueDeriv_tsum_euler_half_two_general ps 2 z₁ (1 / 2) c₀ 9
      hpk hslope aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold 1000 (by norm_num) hB s hs_nn hs_lt' τ hτ_abs
  have hI3 :=
    frobeniusValueDeriv_tsum_euler_half_three_general ps 2 z₁ (1 / 2) c₀ 9
      hpk hslope aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold 1000 (by norm_num) hB s hs_nn hs_lt' τ hτ_abs
  rw [hI0, hI1, hI2, hI3] at hbase
  simpa [hps_def, hz_def, aperyCanonicalPsSeq] using hbase

set_option maxHeartbeats 800000 in
-- Expanding the four shifted Frobenius Euler sums produces a large real-ring normal form.
private lemma aperyCanonical_one_raw_ode
    (c₀ s τ : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hτ_abs : |τ| ≤ s) :
    τ ^ 3 * (taylorShift aperySconifold Number.aperyConifoldZ1Poly).eval τ *
        frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          1 c₀ τ
      - τ ^ 2 * (taylorShift aperyRconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          1 c₀ τ +
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            1 c₀ τ)
      + τ * (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ ^ 2 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          1 c₀ τ +
          2 * (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            1 c₀ τ))
      - (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ ^ 3 * frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          1 c₀ τ +
          3 * (τ ^ 2 *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              1 c₀ τ)) = 0 := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps2 : ps 2 = Number.aperyQconifold := by rw [hps_def]; rfl
  have hps3 : ps 3 = Number.aperyPconifold := by rw [hps_def]; rfl
  have hpk : (ps 3).eval z₁ = 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB : ∀ j ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j hj ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j (by simp at hj ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * 1000 * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    rw [show ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) by norm_num]
    rw [show ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 by norm_num]
    rw [hps3, hz_def]
    exact hs_lt
  have hbase :=
    pointwise_substLHS_analytic_eq_zero_at_rho ps 2 z₁ 1 c₀
      hpk
      (by simpa [hps_def, hz_def] using aperyCanonical_simpleZero_one)
      (by simpa [hps_def, hz_def] using aperyCanonical_no_integer_shift_one)
      s
      (fun j _hj =>
        frobeniusCoeff_fallingFactorial_shift_one_abs_mul_pow_summable_general
          ps 2 z₁ 1 c₀ 9 j hpk hslope
          (fun m hm => by
            have := Number.aperyConifold_small_O m (by omega)
            push_cast at this ⊢
            exact this)
          (fun m hm => by
            have := Number.aperyConifold_large_O m (by omega)
            push_cast at this ⊢
            exact this)
          (fun m hm => by
            rw [hps2, hps3]
            have := Number.aperyConifold_threshold_O m (by omega)
            push_cast at this ⊢
            exact this)
          1000 (by norm_num) hB
          s hs_nn hs_lt')
      τ hτ_abs
  have h_sum_expand :
      ∑ j ∈ Finset.range (2 + 2),
          ((-1 : ℝ) ^ j) * τ ^ ((2 + 1) - j) *
            (taylorShift (ps j) z₁).eval τ *
            ∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * τ ^ m
        =
        τ ^ 3 * (taylorShift (ps 0) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 0 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * τ ^ m)
          - τ ^ 2 * (taylorShift (ps 1) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 1 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * τ ^ m)
          + τ * (taylorShift (ps 2) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * τ ^ m)
          - (taylorShift (ps 3) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * τ ^ m) := by
    rw [show (2 + 2 : ℕ) = 3 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    ring
  rw [h_sum_expand] at hbase
  have hI0 :
      (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 0 *
          frobeniusCoeff ps 2 z₁ 1 c₀ m * τ ^ m) =
        frobeniusValue ps 2 z₁ 1 c₀ τ := by
    simpa using
      frobeniusValueDeriv_tsum_euler_zero ps 2 z₁ 1 c₀ τ
  have hI1 :=
    frobeniusValueDeriv_tsum_euler_shift_one_one_general ps 2 z₁ 1 c₀ 9
      hpk hslope
      (fun m hm => by
        have := Number.aperyConifold_small_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        rw [hps2, hps3]
        have := Number.aperyConifold_threshold_O m (by omega)
        push_cast at this ⊢
        exact this)
      1000 (by norm_num) hB s hs_nn hs_lt' τ hτ_abs
  have hI2 :=
    frobeniusValueDeriv_tsum_euler_shift_one_two_general ps 2 z₁ 1 c₀ 9
      hpk hslope
      (fun m hm => by
        have := Number.aperyConifold_small_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        rw [hps2, hps3]
        have := Number.aperyConifold_threshold_O m (by omega)
        push_cast at this ⊢
        exact this)
      1000 (by norm_num) hB s hs_nn hs_lt' τ hτ_abs
  have hI3 :=
    frobeniusValueDeriv_tsum_euler_shift_one_three_general ps 2 z₁ 1 c₀ 9
      hpk hslope
      (fun m hm => by
        have := Number.aperyConifold_small_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        rw [hps2, hps3]
        have := Number.aperyConifold_threshold_O m (by omega)
        push_cast at this ⊢
        exact this)
      1000 (by norm_num) hB s hs_nn hs_lt' τ hτ_abs
  rw [hI0, hI1, hI2, hI3] at hbase
  simpa [hps_def, hz_def, aperyCanonicalPsSeq] using hbase

private lemma aperyCanonical_zero_raw_ode
    (c₀ s τ : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hτ_abs : |τ| ≤ s) :
    τ ^ 3 * (taylorShift aperySconifold Number.aperyConifoldZ1Poly).eval τ *
        frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          0 c₀ τ
      - τ ^ 2 * (taylorShift aperyRconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          0 c₀ τ)
      + τ * (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ ^ 2 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          0 c₀ τ)
      - (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ *
        (τ ^ 3 * frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          0 c₀ τ) = 0 := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps2 : ps 2 = Number.aperyQconifold := by rw [hps_def]; rfl
  have hps3 : ps 3 = Number.aperyPconifold := by rw [hps_def]; rfl
  have hpk : (ps 3).eval z₁ = 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB : ∀ j ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j hj ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j (by simp at hj ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * 1000 * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    rw [show ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) by norm_num]
    rw [show ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 by norm_num]
    rw [hps3, hz_def]
    exact hs_lt
  have hsmall : ∀ m : ℕ, 9 ≤ m →
      (|(0 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := Number.aperyConifold_small_Z m (by omega)
    push_cast at this ⊢
    exact this
  have hlarge : ∀ m : ℕ, 9 ≤ m →
      3 * |(0 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := Number.aperyConifold_large_Z m (by omega)
    push_cast at this ⊢
    exact this
  have hthresh : ∀ m : ℕ, 9 ≤ m →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m + 1 : ℕ) : ℝ) - |(0 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m hm
    rw [hps2, hps3]
    have := Number.aperyConifold_threshold_Z m (by omega)
    push_cast at this ⊢
    exact this
  have hfall : ∀ j ∈ Finset.range (2 + 2), Summable (fun m : ℕ =>
      |fallingFactorial (((m : ℕ) : ℝ)) j| *
        |frobeniusCoeff ps 2 z₁ 0 c₀ m| * s ^ m) := by
    intro j _hj
    exact frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
      ps 2 z₁ 0 c₀ 9 j hpk hslope hsmall hlarge hthresh
      1000 (by norm_num) hB s hs_nn hs_lt'
  have hsol :
      ∀ k, PowerSeries.coeff (R := ℝ) k
        (substLHSGen ps 3 z₁ 0
          (frobeniusSolution ps 2 z₁ 0 c₀)) = 0 := by
    intro k
    simpa [hps_def, hz_def] using
      (aperyCanonical_frobeniusSolution_is_solution_zero_regular c₀).2 k
  have hg_abs' : ∀ j ∈ Finset.range (2 + 2), Summable (fun m : ℕ =>
      |fallingFactorial ((0 : ℝ) + ((m : ℕ) : ℝ)) j| *
        |PowerSeries.coeff (R := ℝ) m (frobeniusSolution ps 2 z₁ 0 c₀)| * s ^ m) := by
    intro j hj
    refine (hfall j hj).congr (fun m => ?_)
    rw [coeff_frobeniusSolution, zero_add]
  have heq := tsum_coeff_substLHSGen_eq_finsum_at_rho ps 3 z₁ 0
    (frobeniusSolution ps 2 z₁ 0 c₀) s hg_abs' τ hτ_abs
  have hLHS_zero : (∑' N : ℕ, PowerSeries.coeff (R := ℝ) N
      (substLHSGen ps 3 z₁ 0 (frobeniusSolution ps 2 z₁ 0 c₀)) *
        τ ^ N) = 0 := by
    have hterm : ∀ N : ℕ, PowerSeries.coeff (R := ℝ) N
        (substLHSGen ps 3 z₁ 0 (frobeniusSolution ps 2 z₁ 0 c₀)) *
          τ ^ N = 0 := fun N => by rw [hsol N, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  rw [hLHS_zero] at heq
  simp_rw [coeff_frobeniusSolution, zero_add] at heq
  have hbase := heq.symm
  have h_sum_expand :
      ∑ j ∈ Finset.range (2 + 2),
          ((-1 : ℝ) ^ j) * τ ^ ((2 + 1) - j) *
            (taylorShift (ps j) z₁).eval τ *
            ∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) j *
              frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m
        =
        τ ^ 3 * (taylorShift (ps 0) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) 0 *
              frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m)
          - τ ^ 2 * (taylorShift (ps 1) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) 1 *
              frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m)
          + τ * (taylorShift (ps 2) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) 2 *
              frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m)
          - (taylorShift (ps 3) z₁).eval τ *
            (∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) 3 *
              frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m) := by
    rw [show (2 + 2 : ℕ) = 3 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    ring
  rw [h_sum_expand] at hbase
  have hI0 :
      (∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) 0 *
          frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m) =
        frobeniusValue ps 2 z₁ 0 c₀ τ := by
    simpa using frobeniusValueDeriv_tsum_euler_zero ps 2 z₁ 0 c₀ τ
  have hI1 :=
    frobeniusValueDeriv_tsum_euler_one_general ps 2 z₁ 0 c₀ 9
      hpk hslope hsmall hlarge hthresh 1000 (by norm_num) hB
      s hs_nn hs_lt' τ hτ_abs
  have hI1' :
      (∑' m : ℕ, fallingFactorial (((m : ℕ) : ℝ)) 1 *
          frobeniusCoeff ps 2 z₁ 0 c₀ m * τ ^ m) =
        τ * frobeniusValueDeriv ps 2 z₁ 0 c₀ τ := by
    simpa [fallingFactorial_one] using hI1
  have hI2 :=
    frobeniusValueDeriv_tsum_euler_two_general ps 2 z₁ 0 c₀ 9
      hpk hslope hsmall hlarge hthresh 1000 (by norm_num) hB
      s hs_nn hs_lt' τ hτ_abs
  have hI3 :=
    frobeniusValueDeriv_tsum_euler_three_general ps 2 z₁ 0 c₀ 9
      hpk hslope hsmall hlarge hthresh 1000 (by norm_num) hB
      s hs_nn hs_lt' τ hτ_abs
  rw [hI0, hI1', hI2, hI3] at hbase
  simpa [hps_def, hz_def, aperyCanonicalPsSeq] using hbase

private lemma aperyCanonical_zero_raw_eq_scaled_scalar
    {τ V Vp Vpp Vppp S R Q P : ℝ} :
    τ ^ 3 * (P * (-Vppp) + Q * Vpp + R * (-Vp) + S * V) =
      τ ^ 3 * S * V
        - τ ^ 2 * R * (τ * Vp)
        + τ * Q * (τ ^ 2 * Vpp)
        - P * (τ ^ 3 * Vppp) := by
  ring

private lemma aperyCanonical_zero_scalar_ode_of_raw
    {τ V Vp Vpp Vppp S R Q P : ℝ} (hτ : 0 < τ)
    (hraw :
      τ ^ 3 * S * V
        - τ ^ 2 * R * (τ * Vp)
        + τ * Q * (τ ^ 2 * Vpp)
        - P * (τ ^ 3 * Vppp) = 0) :
    P * (-Vppp) + Q * Vpp + R * (-Vp) + S * V = 0 := by
  have hscaled := aperyCanonical_zero_raw_eq_scaled_scalar
    (τ := τ) (V := V) (Vp := Vp) (Vpp := Vpp) (Vppp := Vppp)
    (S := S) (R := R) (Q := Q) (P := P)
  rw [hraw] at hscaled
  have hfactor_ne : τ ^ 3 ≠ 0 := by
    exact pow_ne_zero 3 (ne_of_gt hτ)
  exact mul_eq_zero.mp hscaled |>.resolve_left hfactor_ne

private lemma aperyCanonical_one_raw_eq_scaled_scalar
    {τ V Vp Vpp Vppp S R Q P : ℝ} :
    τ ^ 2 *
        (P * (-(3 * Vpp + τ * Vppp))
          + Q * (2 * Vp + τ * Vpp)
          + R * (-(V + τ * Vp))
          + S * (τ * V)) =
      τ ^ 3 * S * V
        - τ ^ 2 * R * (τ * Vp + V)
        + τ * Q * (τ ^ 2 * Vpp + 2 * (τ * Vp))
        - P * (τ ^ 3 * Vppp + 3 * (τ ^ 2 * Vpp)) := by
  ring

private lemma aperyCanonical_one_scalar_ode_of_raw
    {τ V Vp Vpp Vppp S R Q P : ℝ} (hτ : 0 < τ)
    (hraw :
      τ ^ 3 * S * V
        - τ ^ 2 * R * (τ * Vp + V)
        + τ * Q * (τ ^ 2 * Vpp + 2 * (τ * Vp))
        - P * (τ ^ 3 * Vppp + 3 * (τ ^ 2 * Vpp)) = 0) :
    P * (-(3 * Vpp + τ * Vppp))
      + Q * (2 * Vp + τ * Vpp)
      + R * (-(V + τ * Vp))
      + S * (τ * V) = 0 := by
  have hscaled := aperyCanonical_one_raw_eq_scaled_scalar
    (τ := τ) (V := V) (Vp := Vp) (Vpp := Vpp) (Vppp := Vppp)
    (S := S) (R := R) (Q := Q) (P := P)
  rw [hraw] at hscaled
  have hfactor_ne : τ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (ne_of_gt hτ)
  exact mul_eq_zero.mp hscaled |>.resolve_left hfactor_ne

private lemma aperyCanonicalLeftZero_scalar_ode
    (c₀ s x : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    Polynomial.eval x Number.aperyPconifold *
        (-(frobeniusValueDeriv3 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x)))
      + Polynomial.eval x Number.aperyQconifold *
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x)
      + Polynomial.eval x aperyRconifold *
        (-(frobeniusValueDeriv aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x)))
      + Polynomial.eval x aperySconifold *
        frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          0 c₀ (Number.aperyConifoldZ1Poly - x) = 0 := by
  let τ := Number.aperyConifoldZ1Poly - x
  have hτ_abs : |τ| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at hτ_mem
    exact le_of_lt hτ_mem
  have hraw := aperyCanonical_zero_raw_ode c₀ s τ hs_pos.le hs_lt hτ_abs
  have hraw' :
      τ ^ 3 * aperySconifold.eval x *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            0 c₀ τ
        - τ ^ 2 * aperyRconifold.eval x *
          (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 0 c₀ τ)
        + τ * Number.aperyQconifold.eval x *
          (τ ^ 2 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 0 c₀ τ)
        - Number.aperyPconifold.eval x *
          (τ ^ 3 * frobeniusValueDeriv3 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 0 c₀ τ) = 0 := by
    have hx : Number.aperyConifoldZ1Poly - τ = x := by dsimp [τ]; ring
    simpa [τ, taylorShift_eval_at, hx] using hraw
  have hscalar := aperyCanonical_zero_scalar_ode_of_raw
    (τ := τ)
    (V := frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      0 c₀ τ)
    (Vp := frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      0 c₀ τ)
    (Vpp := frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      0 c₀ τ)
    (Vppp := frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      0 c₀ τ)
    (S := aperySconifold.eval x) (R := aperyRconifold.eval x)
    (Q := Number.aperyQconifold.eval x) (P := Number.aperyPconifold.eval x)
    hτ_pos (by
      convert hraw' using 1 <;> ring)
  simpa [τ] using hscalar

private lemma aperyCanonicalLeftHalf_scalar_ode
    (c₀ s x : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    Polynomial.eval x Number.aperyPconifold *
        (-(3 / (8 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 5)) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
          (3 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
            frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
          (3 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x))
      + Polynomial.eval x Number.aperyQconifold *
        (-(1 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
          frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) /
            Real.sqrt (Number.aperyConifoldZ1Poly - x) +
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x))
      + Polynomial.eval x aperyRconifold *
        (-(1 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x))
      + Polynomial.eval x aperySconifold *
        (Real.sqrt (Number.aperyConifoldZ1Poly - x) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) = 0 := by
  let τ := Number.aperyConifoldZ1Poly - x
  have hτ_abs : |τ| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at hτ_mem
    exact le_of_lt hτ_mem
  have hraw := aperyCanonical_half_raw_ode c₀ s τ hs_pos.le hs_lt hτ_abs
  have hraw' :
      τ ^ 3 * aperySconifold.eval x *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ
        - τ ^ 2 * aperyRconifold.eval x *
          (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ +
            (1 / 2) * frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ τ)
        + τ * Number.aperyQconifold.eval x *
          (τ ^ 2 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ +
            τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ τ -
            (1 / 4) * frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ τ)
        - Number.aperyPconifold.eval x *
          (τ ^ 3 * frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ τ +
            (3 / 2) * (τ ^ 2 *
              frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
                (1 / 2) c₀ τ) -
            (3 / 4) * (τ *
              frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
                (1 / 2) c₀ τ) +
            (3 / 8) * frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ τ) = 0 := by
    have hx : Number.aperyConifoldZ1Poly - τ = x := by dsimp [τ]; ring
    simpa [τ, taylorShift_eval_at, hx] using hraw
  have hscalar := aperyCanonical_half_scalar_ode_of_raw
    (τ := τ)
    (V := frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      (1 / 2) c₀ τ)
    (Vp := frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      (1 / 2) c₀ τ)
    (Vpp := frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      (1 / 2) c₀ τ)
    (Vppp := frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      (1 / 2) c₀ τ)
    (S := aperySconifold.eval x) (R := aperyRconifold.eval x)
    (Q := Number.aperyQconifold.eval x) (P := Number.aperyPconifold.eval x)
    hτ_pos (by
      convert hraw' using 1 <;> ring)
  simpa [τ] using hscalar

private lemma aperyCanonicalLeftOne_scalar_ode
    (c₀ s x : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    Polynomial.eval x Number.aperyPconifold *
        (-(3 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x) +
            (Number.aperyConifoldZ1Poly - x) *
              frobeniusValueDeriv3 aperyCanonicalPsSeq 2
                Number.aperyConifoldZ1Poly 1 c₀
                (Number.aperyConifoldZ1Poly - x)))
      + Polynomial.eval x Number.aperyQconifold *
        (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x) +
            (Number.aperyConifoldZ1Poly - x) *
              frobeniusValueDeriv2 aperyCanonicalPsSeq 2
                Number.aperyConifoldZ1Poly 1 c₀
                (Number.aperyConifoldZ1Poly - x))
      + Polynomial.eval x aperyRconifold *
        (-(frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              1 c₀ (Number.aperyConifoldZ1Poly - x) +
            (Number.aperyConifoldZ1Poly - x) *
              frobeniusValueDeriv aperyCanonicalPsSeq 2
                Number.aperyConifoldZ1Poly 1 c₀
                (Number.aperyConifoldZ1Poly - x)))
      + Polynomial.eval x aperySconifold *
        ((Number.aperyConifoldZ1Poly - x) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            1 c₀ (Number.aperyConifoldZ1Poly - x)) = 0 := by
  let τ := Number.aperyConifoldZ1Poly - x
  have hτ_abs : |τ| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at hτ_mem
    exact le_of_lt hτ_mem
  have hraw := aperyCanonical_one_raw_ode c₀ s τ hs_pos.le hs_lt hτ_abs
  have hraw' :
      τ ^ 3 * aperySconifold.eval x *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            1 c₀ τ
        - τ ^ 2 * aperyRconifold.eval x *
          (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            1 c₀ τ +
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              1 c₀ τ)
        + τ * Number.aperyQconifold.eval x *
          (τ ^ 2 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀ τ +
            2 * (τ * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀ τ))
        - Number.aperyPconifold.eval x *
          (τ ^ 3 * frobeniusValueDeriv3 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀ τ +
            3 * (τ ^ 2 *
              frobeniusValueDeriv2 aperyCanonicalPsSeq 2
                Number.aperyConifoldZ1Poly 1 c₀ τ)) = 0 := by
    have hx : Number.aperyConifoldZ1Poly - τ = x := by dsimp [τ]; ring
    simpa [τ, taylorShift_eval_at, hx] using hraw
  have hscalar := aperyCanonical_one_scalar_ode_of_raw
    (τ := τ)
    (V := frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      1 c₀ τ)
    (Vp := frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      1 c₀ τ)
    (Vpp := frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      1 c₀ τ)
    (Vppp := frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
      1 c₀ τ)
    (S := aperySconifold.eval x) (R := aperyRconifold.eval x)
    (Q := Number.aperyQconifold.eval x) (P := Number.aperyPconifold.eval x)
    hτ_pos (by
      convert hraw' using 1 <;> ring)
  simpa [τ] using hscalar

private lemma hasDerivAt_yAperyCanonicalLeftHalf_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ => yAperyCanonicalLeftHalf c₀
        (z - Number.aperyConifoldZ1Poly))
      (-(1 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
        Real.sqrt (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := by rw [hps_def]; rfl
  have hpk : (ps 3).eval z₁ = 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3, hz_def]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    rw [show ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) by norm_num]
    rw [show ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 by norm_num]
    rw [hps3, hz_def]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ (1 / 2) c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hV : HasDerivAt V (Vp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [V, Vp, hps_def, hz_def] using
      frobeniusValue_hasDerivAt_std_general ps 2 z₁
        (1 / 2) c₀ 9 hpk hslope
        aperyCanonicalHalf_small aperyCanonicalHalf_large
        (fun m hm => by
          simpa [hps_def, hz_def] using aperyCanonicalHalf_threshold m hm)
        1000 (by norm_num) hB s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hY := hasDerivAt_sqrt_pos_mul_core hτ_pos hV
  have hcomp := hY.comp x hinner
  have hfun :
      (fun y : ℝ => yAperyCanonicalLeftHalf c₀
        (y - Number.aperyConifoldZ1Poly)) =
      (fun y : ℝ => Real.sqrt (Number.aperyConifoldZ1Poly - y) *
        V (Number.aperyConifoldZ1Poly - y)) := by
    funext y
    simp [yAperyCanonicalLeftHalf, V, hps_def, hz_def]
  rw [hfun]
  convert hcomp using 1 <;> ring

private lemma hasDerivAt_deriv_yAperyCanonicalHalf_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_neg : x - Number.aperyConifoldZ1Poly < 0)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => yAperyCanonicalHalf c₀
        (z - Number.aperyConifoldZ1Poly)))
      (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) -
        frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) /
          Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
        Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := by
    rw [hps_def]
    rfl
  have hps2 : ps 2 = Number.aperyQconifold := by
    rw [hps_def]
    rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m : ℕ, 9 ≤ m →
      (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := Number.aperyConifold_small_H m (by omega)
    push_cast at this ⊢
    exact this
  have hM0_large' : ∀ m : ℕ, 9 ≤ m →
      3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := Number.aperyConifold_large_H m (by omega)
    push_cast at this ⊢
    exact this
  have hM0_thresh' : ∀ m' : ℕ, 9 ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := Number.aperyConifold_threshold_H m' (by omega)
    push_cast at this ⊢
    exact this
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * 1000 * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  let first : ℝ → ℝ := fun u =>
    -(1 / (2 * Real.sqrt (-u))) *
        frobeniusValue ps 2 z₁ (1 / 2) c₀ u +
      Real.sqrt (-u) *
        frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀ u
  let second : ℝ → ℝ := fun u =>
    -(1 / (4 * (Real.sqrt (-u)) ^ 3)) *
        frobeniusValue ps 2 z₁ (1 / 2) c₀ u -
      frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀ u / Real.sqrt (-u) +
      Real.sqrt (-u) * frobeniusValueDeriv2 ps 2 z₁ (1 / 2) c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hV : HasDerivAt
      (fun u => frobeniusValue ps 2 z₁ (1 / 2) c₀ u)
      (frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀
        (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa using frobeniusValue_hasDerivAt_std_general ps 2 z₁
      (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
      hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
      (x - Number.aperyConifoldZ1Poly) hx_mem
  have hVd : HasDerivAt
      (fun u => frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀ u)
      (frobeniusValueDeriv2 ps 2 z₁ (1 / 2) c₀
        (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa using frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
      (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
      hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
      (x - Number.aperyConifoldZ1Poly) hx_mem
  have hsecond_unshift : HasDerivAt first
      (second (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [first, second] using
      hasDerivAt_sqrt_neg_mul_core_deriv hx_neg hV hVd
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly))
      (second (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hsecond_unshift.comp x hinner
  have hneg_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly < 0 := by
    exact (isOpen_lt (continuous_id.sub continuous_const) continuous_const).mem_nhds hx_neg
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => yAperyCanonicalHalf c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hneg_ev, hmem_ev] with z hz_neg hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hVz : HasDerivAt
        (fun u => frobeniusValue ps 2 z₁ (1 / 2) c₀ u)
        (frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀
          (z - Number.aperyConifoldZ1Poly))
        (z - Number.aperyConifoldZ1Poly) := by
      simpa using frobeniusValue_hasDerivAt_std_general ps 2 z₁
        (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
        hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
        (z - Number.aperyConifoldZ1Poly) hz_mem
    have hY := hasDerivAt_sqrt_neg_mul_core hz_neg hVz
    have hcomp := hY.comp z hz_inner
    simpa [yAperyCanonicalHalf, first, hps_def, hz_def, Function.comp_def] using hcomp.deriv
  have hdd := hsecond_shift.congr_of_eventuallyEq hderiv_ev
  simpa [second, hps_def, hz_def] using hdd

private lemma deriv_deriv_yAperyCanonicalHalf_shift_eq
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_neg : x - Number.aperyConifoldZ1Poly < 0)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => yAperyCanonicalHalf c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) -
        frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) /
          Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
        Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly)) := by
  exact (hasDerivAt_deriv_yAperyCanonicalHalf_shift
    c₀ s hs_pos hs_lt x hx_neg hx_mem).deriv

private lemma hasDerivAt_deriv_yAperyCanonicalLeftHalf_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => yAperyCanonicalLeftHalf c₀
        (z - Number.aperyConifoldZ1Poly)))
      (-(1 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
        frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) /
          Real.sqrt (Number.aperyConifoldZ1Poly - x) +
        Real.sqrt (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := by
    rw [hps_def]
    rfl
  have hps2 : ps 2 = Number.aperyQconifold := by
    rw [hps_def]
    rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m : ℕ, 9 ≤ m →
      (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := Number.aperyConifold_small_H m (by omega)
    push_cast at this ⊢
    exact this
  have hM0_large' : ∀ m : ℕ, 9 ≤ m →
      3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := Number.aperyConifold_large_H m (by omega)
    push_cast at this ⊢
    exact this
  have hM0_thresh' : ∀ m' : ℕ, 9 ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := Number.aperyConifold_threshold_H m' (by omega)
    push_cast at this ⊢
    exact this
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * 1000 * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ (1 / 2) c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀ u
  let Vpp : ℝ → ℝ := fun u => frobeniusValueDeriv2 ps 2 z₁ (1 / 2) c₀ u
  let first : ℝ → ℝ := fun u =>
    (1 / (2 * Real.sqrt u)) * V u + Real.sqrt u * Vp u
  let second : ℝ → ℝ := fun u =>
    -(1 / (4 * (Real.sqrt u) ^ 3)) * V u +
      Vp u / Real.sqrt u + Real.sqrt u * Vpp u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hV : HasDerivAt V (Vp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [V, Vp, hps_def, hz_def] using
      frobeniusValue_hasDerivAt_std_general ps 2 z₁
        (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
        hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hVp : HasDerivAt Vp (Vpp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vp, Vpp, hps_def, hz_def] using
      frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
        (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
        hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hsecond_unshift : HasDerivAt first
      (second (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [first, second, V, Vp, Vpp, hps_def, hz_def] using
      hasDerivAt_sqrt_pos_mul_core_deriv hτ_pos hV hVp
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (Number.aperyConifoldZ1Poly - z))
      (-(second (Number.aperyConifoldZ1Poly - x))) x := by
    simpa using hsecond_unshift.comp x hinner
  have hsecond_neg : HasDerivAt
      (fun z : ℝ => - first (Number.aperyConifoldZ1Poly - z))
      (second (Number.aperyConifoldZ1Poly - x)) x := by
    simpa using hsecond_shift.neg
  have hpos_ev : ∀ᶠ z in nhds x,
      0 < Number.aperyConifoldZ1Poly - z := by
    exact (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds hτ_pos
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hderiv_ev :
      deriv (fun z : ℝ => yAperyCanonicalLeftHalf c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => - first (Number.aperyConifoldZ1Poly - z)) := by
    filter_upwards [hpos_ev, hmem_ev] with z hz_pos hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => Number.aperyConifoldZ1Poly - y) (-1) z := by
      simpa using (hasDerivAt_const z Number.aperyConifoldZ1Poly).sub
        (hasDerivAt_id z)
    have hVz : HasDerivAt V (Vp (Number.aperyConifoldZ1Poly - z))
        (Number.aperyConifoldZ1Poly - z) := by
      simpa [V, Vp, hps_def, hz_def] using
        frobeniusValue_hasDerivAt_std_general ps 2 z₁
          (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
          hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
          (Number.aperyConifoldZ1Poly - z) hz_mem
    have hY := hasDerivAt_sqrt_pos_mul_core hz_pos hVz
    have hcomp := hY.comp z hz_inner
    have hrewrite :
        (fun y : ℝ => yAperyCanonicalLeftHalf c₀
          (y - Number.aperyConifoldZ1Poly)) =
        (fun y : ℝ => Real.sqrt (Number.aperyConifoldZ1Poly - y) *
          V (Number.aperyConifoldZ1Poly - y)) := by
      funext y
      simp [yAperyCanonicalLeftHalf, V, hps_def, hz_def]
    rw [hrewrite]
    simpa [first, V, Vp, hps_def, hz_def] using hcomp.deriv
  have hdd := hsecond_neg.congr_of_eventuallyEq hderiv_ev
  simpa [second, V, Vp, Vpp, hps_def, hz_def] using hdd

private lemma deriv_deriv_yAperyCanonicalLeftHalf_shift_eq
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => yAperyCanonicalLeftHalf c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      (-(1 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
        frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) /
          Real.sqrt (Number.aperyConifoldZ1Poly - x) +
        Real.sqrt (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) := by
  exact (hasDerivAt_deriv_yAperyCanonicalLeftHalf_shift
    c₀ s hs_pos hs_lt x hτ_pos hτ_mem).deriv

private lemma hasDerivAt_deriv_deriv_yAperyCanonicalLeftHalf_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv (deriv
      (fun z : ℝ => yAperyCanonicalLeftHalf c₀
        (z - Number.aperyConifoldZ1Poly))))
      (-(3 / (8 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 5)) *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
        (3 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
          frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
        (3 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
        Real.sqrt (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := by
    rw [hps_def]
    rfl
  have hps2 : ps 2 = Number.aperyQconifold := by
    rw [hps_def]
    rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m : ℕ, 9 ≤ m →
      (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := Number.aperyConifold_small_H m (by omega)
    push_cast at this ⊢
    exact this
  have hM0_large' : ∀ m : ℕ, 9 ≤ m →
      3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := Number.aperyConifold_large_H m (by omega)
    push_cast at this ⊢
    exact this
  have hM0_thresh' : ∀ m' : ℕ, 9 ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := Number.aperyConifold_threshold_H m' (by omega)
    push_cast at this ⊢
    exact this
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    rw [hps_def, hz_def]
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * 1000 * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ (1 / 2) c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ (1 / 2) c₀ u
  let Vpp : ℝ → ℝ := fun u => frobeniusValueDeriv2 ps 2 z₁ (1 / 2) c₀ u
  let Vppp : ℝ → ℝ := fun u => frobeniusValueDeriv3 ps 2 z₁ (1 / 2) c₀ u
  let second : ℝ → ℝ := fun u =>
    -(1 / (4 * (Real.sqrt u) ^ 3)) * V u +
      Vp u / Real.sqrt u + Real.sqrt u * Vpp u
  let third : ℝ → ℝ := fun u =>
    3 / (8 * (Real.sqrt u) ^ 5) * V u -
      3 / (4 * (Real.sqrt u) ^ 3) * Vp u +
      3 / (2 * Real.sqrt u) * Vpp u + Real.sqrt u * Vppp u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hV : HasDerivAt V (Vp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [V, Vp, hps_def, hz_def] using
      frobeniusValue_hasDerivAt_std_general ps 2 z₁
        (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
        hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hVp : HasDerivAt Vp (Vpp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vp, Vpp, hps_def, hz_def] using
      frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
        (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
        hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hVpp : HasDerivAt Vpp (Vppp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vpp, Vppp, hps_def, hz_def] using
      frobeniusValueDeriv2_hasDerivAt_general ps 2 z₁
        (1 / 2) c₀ 9 hpk' hslope' hM0_small' hM0_large'
        hM0_thresh' 1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hthird_unshift : HasDerivAt second
      (third (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [second, third, V, Vp, Vpp, Vppp, hps_def, hz_def] using
      hasDerivAt_sqrt_pos_mul_core_deriv2 hτ_pos hV hVp hVpp
  have hthird_shift : HasDerivAt
      (fun z : ℝ => second (Number.aperyConifoldZ1Poly - z))
      (-(third (Number.aperyConifoldZ1Poly - x))) x := by
    simpa using hthird_unshift.comp x hinner
  have hpos_ev : ∀ᶠ z in nhds x,
      0 < Number.aperyConifoldZ1Poly - z := by
    exact (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds hτ_pos
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hderiv2_ev :
      deriv (deriv (fun z : ℝ => yAperyCanonicalLeftHalf c₀
        (z - Number.aperyConifoldZ1Poly))) =ᶠ[nhds x]
        (fun z : ℝ => second (Number.aperyConifoldZ1Poly - z)) := by
    filter_upwards [hpos_ev, hmem_ev] with z hz_pos hz_mem
    rw [deriv_deriv_yAperyCanonicalLeftHalf_shift_eq c₀ s hs_pos hs_lt
      z hz_pos hz_mem]
  have hdd := hthird_shift.congr_of_eventuallyEq hderiv2_ev
  convert hdd using 1 <;> ring

private lemma yAperyCanonicalLeftHalf_state_hasDerivAt
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_pos : 0 < x)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ =>
        (yAperyCanonicalLeftHalf c₀ (z - Number.aperyConifoldZ1Poly),
          deriv (fun y : ℝ =>
            yAperyCanonicalLeftHalf c₀ (y - Number.aperyConifoldZ1Poly)) z,
          deriv (deriv (fun y : ℝ =>
            yAperyCanonicalLeftHalf c₀ (y - Number.aperyConifoldZ1Poly))) z))
      (aperyODEStateField x
        (yAperyCanonicalLeftHalf c₀ (x - Number.aperyConifoldZ1Poly),
          deriv (fun y : ℝ =>
            yAperyCanonicalLeftHalf c₀ (y - Number.aperyConifoldZ1Poly)) x,
          deriv (deriv (fun y : ℝ =>
            yAperyCanonicalLeftHalf c₀ (y - Number.aperyConifoldZ1Poly))) x)) x := by
  let y : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftHalf c₀ (z - Number.aperyConifoldZ1Poly)
  have hy : HasDerivAt y (deriv y x) x := by
    have h0 := hasDerivAt_yAperyCanonicalLeftHalf_shift
      c₀ s hs_pos hs_lt x hτ_pos hτ_mem
    have h0' : HasDerivAt y
        (-(1 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) x := by
      simpa [y] using h0
    convert h0' using 1
    exact h0'.deriv
  have hdy_exp :
      deriv y x =
        (-(1 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) := by
    simpa [y] using (hasDerivAt_yAperyCanonicalLeftHalf_shift
      c₀ s hs_pos hs_lt x hτ_pos hτ_mem).deriv
  have hy' : HasDerivAt (deriv y) (deriv (deriv y) x) x := by
    have h0 := hasDerivAt_deriv_yAperyCanonicalLeftHalf_shift
      c₀ s hs_pos hs_lt x hτ_pos hτ_mem
    have h0' : HasDerivAt (deriv y)
        (-(1 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
          frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) /
            Real.sqrt (Number.aperyConifoldZ1Poly - x) +
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) x := by
      simpa [y] using h0
    convert h0' using 1
    exact h0'.deriv
  have hddy_exp :
      deriv (deriv y) x =
        (-(1 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
            frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
          frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) /
            Real.sqrt (Number.aperyConifoldZ1Poly - x) +
          Real.sqrt (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x)) := by
    simpa [y] using
      deriv_deriv_yAperyCanonicalLeftHalf_shift_eq c₀ s hs_pos hs_lt
        x hτ_pos hτ_mem
  let y3 : ℝ :=
    (-(3 / (8 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 5)) *
        frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) +
      (3 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
        frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
      (3 / (2 * Real.sqrt (Number.aperyConifoldZ1Poly - x))) *
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x) -
      Real.sqrt (Number.aperyConifoldZ1Poly - x) *
        frobeniusValueDeriv3 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ (Number.aperyConifoldZ1Poly - x))
  have hy'' : HasDerivAt (deriv (deriv y)) y3 x := by
    simpa [y, y3] using
      hasDerivAt_deriv_deriv_yAperyCanonicalLeftHalf_shift
        c₀ s hs_pos hs_lt x hτ_pos hτ_mem
  have hode :
      Polynomial.eval x Number.aperyPconifold * y3
        + Polynomial.eval x Number.aperyQconifold * deriv (deriv y) x
        + Polynomial.eval x aperyRconifold * deriv y x
        + Polynomial.eval x aperySconifold * y x = 0 := by
    have hscalar := aperyCanonicalLeftHalf_scalar_ode
      c₀ s x hs_pos hs_lt hτ_pos hτ_mem
    rw [hdy_exp, hddy_exp]
    simpa [y, y3, yAperyCanonicalLeftHalf] using hscalar
  have hP : Polynomial.eval x Number.aperyPconifold ≠ 0 :=
    aperyPconifold_eval_ne_zero_of_pos_lt_z1 hx_pos (sub_pos.mp hτ_pos)
  simpa [y] using
    hasDerivAt_aperyODEState_of_scalar_ode
      (y := y) (y' := deriv y) (y'' := deriv (deriv y))
      hy hy' hy'' hP hode

private lemma yAperyHalf_hasDerivAt
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_neg : t < 0) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun u => Ripple.Number.Frobenius.yAperyHalf c₀ u)
      (-(1 / (2 * Real.sqrt (-t))) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ t +
        Real.sqrt (-t) *
          frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ t) t := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m →
      (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m →
      3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁
    (1 / 2) c₀ M₀ hpk' hslope' hM0_small' hM0_large'
    hM0_thresh' B hB_nn hB' s hs_pos hs_lt' t ht_mem
  unfold Ripple.Number.Frobenius.yAperyHalf
  convert hasDerivAt_sqrt_neg_mul_core ht_neg hV using 1

private lemma yAperyHalf_hasDerivAt_second_expr
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_neg : t < 0) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun u : ℝ =>
        -(1 / (2 * Real.sqrt (-u))) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ u +
          Real.sqrt (-u) *
            frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
              (1 / 2) c₀ u)
      (-(1 / (4 * (Real.sqrt (-t)) ^ 3)) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ t -
        frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ t / Real.sqrt (-t) +
        Real.sqrt (-t) *
          frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ t) t := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m →
      (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m →
      3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁
    (1 / 2) c₀ M₀ hpk' hslope' hM0_small' hM0_large'
    hM0_thresh' B hB_nn hB' s hs_pos hs_lt' t ht_mem
  have hVd := frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
    (1 / 2) c₀ M₀ hpk' hslope' hM0_small' hM0_large'
    hM0_thresh' B hB_nn hB' s hs_pos hs_lt' t ht_mem
  convert hasDerivAt_sqrt_neg_mul_core_deriv ht_neg hV hVd using 1

private lemma deriv_deriv_yAperyHalf_shift_eq
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_neg : x - Number.aperyConifoldZ1Poly < 0)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.yAperyHalf c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) -
        frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) /
          Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
        Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
          frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly)) := by
  let first : ℝ → ℝ := fun u =>
    -(1 / (2 * Real.sqrt (-u))) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u +
      Real.sqrt (-u) *
        frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u
  let second : ℝ → ℝ := fun u =>
    -(1 / (4 * (Real.sqrt (-u)) ^ 3)) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u -
      frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u / Real.sqrt (-u) +
      Real.sqrt (-u) *
        frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hsecond_unshift : HasDerivAt first
      (second (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [first, second] using
      yAperyHalf_hasDerivAt_second_expr c₀ M₀ B hB_nn
        hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
        (x - Number.aperyConifoldZ1Poly) hx_neg hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly))
      (second (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hsecond_unshift.comp x hinner
  have hneg_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly < 0 := by
    exact (isOpen_lt (continuous_id.sub continuous_const) continuous_const).mem_nhds hx_neg
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.yAperyHalf c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hneg_ev, hmem_ev] with z hz_neg hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hY := yAperyHalf_hasDerivAt c₀ M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
      (z - Number.aperyConifoldZ1Poly) hz_neg hz_mem
    have hcomp := hY.comp z hz_inner
    simpa [first] using hcomp.deriv
  have hdd := hsecond_shift.congr_of_eventuallyEq hderiv_ev
  simpa [second] using hdd.deriv

private lemma deriv_deriv_yAperyZero_shift_eq
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.yAperyZero c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 c₀
        (x - Number.aperyConifoldZ1Poly) := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m →
      (|(0 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m →
      3 * |(0 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ 0 c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 0 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hVp : HasDerivAt Vp
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [Vp] using frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
      0 c₀ M₀ hpk' hslope' hM0_small' hM0_large'
      hM0_thresh' B hB_nn hB' s hs_pos hs_lt'
      (x - Number.aperyConifoldZ1Poly) hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => Vp (z - Number.aperyConifoldZ1Poly))
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hVp.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.yAperyZero c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => Vp (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁
      0 c₀ M₀ hpk' hslope' hM0_small' hM0_large'
      hM0_thresh' B hB_nn hB' s hs_pos hs_lt'
      (z - Number.aperyConifoldZ1Poly) hz_mem
    have hcomp := hV.comp z hz_inner
    unfold Ripple.Number.Frobenius.yAperyZero
    simpa [V, Vp, hps_def, hz_def] using hcomp.deriv
  have hdd := hsecond_shift.congr_of_eventuallyEq hderiv_ev
  simpa [Vp, hps_def, hz_def] using hdd.deriv

private lemma deriv_deriv_yApery_shift_eq
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.yApery c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀
            (x - Number.aperyConifoldZ1Poly)
        + (x - Number.aperyConifoldZ1Poly) *
          frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀
            (x - Number.aperyConifoldZ1Poly) := by
  let first : ℝ → ℝ := fun u =>
    frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
      + u * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
  let second : ℝ → ℝ := fun u =>
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
      + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hsecond_unshift : HasDerivAt first
      (second (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [first, second] using
      Ripple.Number.Frobenius.yApery_hasDerivAt_second c₀ M₀ B hB_nn
        hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
        (x - Number.aperyConifoldZ1Poly) hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly))
      (second (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hsecond_unshift.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.yApery c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hY := Ripple.Number.Frobenius.yApery_hasDerivAt c₀ M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
      (z - Number.aperyConifoldZ1Poly) hz_mem
    have hcomp := hY.comp z hz_inner
    simpa [first] using hcomp.deriv
  have hdd := hsecond_shift.congr_of_eventuallyEq hderiv_ev
  simpa [second] using hdd.deriv

private lemma aperyConifold_local_radius_exists :
    ∃ s : ℝ, 0 < s ∧
      s * (1 + 2 * (4 : ℝ) * 153 * ((2 : ℝ) ^ 3) /
        |Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative Number.aperyPconifold)|) < 1 := by
  let K : ℝ := 1 + 2 * (4 : ℝ) * 153 * ((2 : ℝ) ^ 3) /
    |Polynomial.eval Number.aperyConifoldZ1Poly
      (Polynomial.derivative Number.aperyPconifold)|
  have hden_pos : 0 <
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)| :=
    Number.aperyPconifold_deriv_eval_z1_abs_pos
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  dsimp [K]
  field_simp [hK_pos.ne']
  linarith

private lemma aperyConifold_common_B_bound :
    ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
        Number.aperyConifoldZ1Poly) ℓ| ≤ (153 : ℝ) :=
  aperyPsSeq_aperyConifold_taylorShift_coeff_abs_le_153

private lemma frobeniusValueDeriv_tendsto_neg_zero_general
    (ρ c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|ρ| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |ρ| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |ρ| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly ρ c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly ρ c₀ 0)) := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m →
      (|ρ| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m →
      3 * |ρ| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |ρ| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv ps 2 z₁ ρ c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general ps 2 z₁ ρ c₀ M₀
      hpk' hslope' hM0_small' hM0_large' hM0_thresh'
      B hB_nn hB' s hs_pos.le hs_lt'
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) := by
    exact Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa [hps_def, hz_def] using hct.tendsto.comp hneg

private lemma frobeniusValueDeriv2_tendsto_neg_zero_general
    (ρ c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|ρ| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |ρ| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |ρ| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv2
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly ρ c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv2
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly ρ c₀ 0)) := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m →
      (|ρ| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m →
      3 * |ρ| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |ρ| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv2 ps 2 z₁ ρ c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general ps 2 z₁ ρ c₀ M₀
      hpk' hslope' hM0_small' hM0_large' hM0_thresh'
      B hB_nn hB' s hs_pos.le hs_lt'
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) := by
    exact Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa [hps_def, hz_def] using hct.tendsto.comp hneg

private lemma frobeniusValueCanonicalHalf_tendsto_neg_zero_seed (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c₀) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly (1 / 2) c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hneg

private lemma frobeniusValueCanonicalHalfDeriv_tendsto_neg_zero (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly (1 / 2) c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hneg

private lemma frobeniusValueCanonicalHalfDeriv2_tendsto_neg_zero (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly (1 / 2) c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hneg

private lemma frobeniusValueCanonicalHalf_tendsto_pos_zero_seed (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c₀) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly (1 / 2) c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma frobeniusValueCanonicalZero_tendsto_pos_zero_seed (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c₀) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly 0 c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      (fun m hm => by
        have := Number.aperyConifold_small_Z m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_Z m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        simpa [aperyCanonicalPsSeq] using Number.aperyConifold_threshold_Z m (by omega))
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma frobeniusValueCanonicalOne_tendsto_pos_zero_seed (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 1 c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c₀) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValue aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 1 c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly 1 c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      (fun m hm => by
        have := Number.aperyConifold_small_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_O m (by omega)
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        simpa [aperyCanonicalPsSeq] using Number.aperyConifold_threshold_O m (by omega))
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma aperyCanonicalLeftBranchTriple_zero_on_left_corridor_forces_seeds_zero
    {a₀ a_half a₁ δ : ℝ} (hδ_pos : 0 < δ)
    (hzero : ∀ t ∈ aperyConifoldLeftTInterval δ,
      aperyCanonicalLeftBranchTriple a₀ a_half a₁ t = 0) :
    a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0 := by
  have hsqrt : Filter.Tendsto (fun ε : ℝ => Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine Ripple.Number.Frobenius.frobenius_three_branch_linear_independence
    (ε := δ)
    (f₁ := fun ε : ℝ => yAperyCanonicalLeftZero 1 (-ε))
    (f₂ := fun ε : ℝ => yAperyCanonicalLeftHalf 1 (-ε))
    (f₃ := fun ε : ℝ => yAperyCanonicalLeftOne 1 (-ε))
    (L₁ := 1) (L₂ := 1) (L₃ := 1)
    hδ_pos one_ne_zero one_ne_zero one_ne_zero
    ?hzero_branch ?hhalf_div_sqrt ?hone_div_eps
    ?hhalf_zero ?hone_zero ?hone_div_sqrt_zero ?hvanish
  · simpa [yAperyCanonicalLeftZero] using
      frobeniusValueCanonicalZero_tendsto_pos_zero_seed 1
  · refine (frobeniusValueCanonicalHalf_tendsto_pos_zero_seed 1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hsqrt_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
    simp [yAperyCanonicalLeftHalf, hsqrt_ne]
  · refine (frobeniusValueCanonicalOne_tendsto_pos_zero_seed 1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε_ne : ε ≠ 0 := hε_pos.ne'
    simp [yAperyCanonicalLeftOne, hε_ne]
  · have hV := frobeniusValueCanonicalHalf_tendsto_pos_zero_seed 1
    have hprod := hsqrt.mul hV
    simpa [yAperyCanonicalLeftHalf] using hprod
  · have heps : Filter.Tendsto (fun ε : ℝ => ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hV := frobeniusValueCanonicalOne_tendsto_pos_zero_seed 1
    have hprod := heps.mul hV
    simpa [yAperyCanonicalLeftOne] using hprod
  · have hV := frobeniusValueCanonicalOne_tendsto_pos_zero_seed 1
    have hprod := hsqrt.mul hV
    have hprod0 : Filter.Tendsto
        (fun ε : ℝ =>
          Real.sqrt ε *
            frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 1 ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hprod
    refine hprod0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hsqrt_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
    have hsqrt_sq : (Real.sqrt ε) ^ 2 = ε := by
      rw [Real.sq_sqrt hε_pos.le]
    have hdiv : ε / Real.sqrt ε = Real.sqrt ε := by
      field_simp [hsqrt_ne]
      simpa [pow_two] using hsqrt_sq.symm
    unfold yAperyCanonicalLeftOne
    simp only [neg_neg]
    calc
      Real.sqrt ε *
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 1 1 ε =
          (ε / Real.sqrt ε) *
            frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 1 ε := by rw [hdiv]
      _ = ε * frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 1 ε / Real.sqrt ε := by
          ring
  · intro ε hε
    have ht : -ε ∈ aperyConifoldLeftTInterval δ := by
      dsimp [aperyConifoldLeftTInterval]
      exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
    have h := hzero (-ε) ht
    have hpk :
        (aperyCanonicalPsSeq (2 + 1)).eval Number.aperyConifoldZ1Poly = 0 :=
      aperyCanonicalPsSeq_leading_eval_z1
    have hz0 :
        yAperyCanonicalLeftZero a₀ (-ε) =
          a₀ * yAperyCanonicalLeftZero 1 (-ε) := by
      unfold yAperyCanonicalLeftZero
      simpa using (frobeniusValue_smul_c₀ aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 a₀ 1 hpk (-(-ε)))
    have hzh :
        yAperyCanonicalLeftHalf a_half (-ε) =
          a_half * yAperyCanonicalLeftHalf 1 (-ε) := by
      unfold yAperyCanonicalLeftHalf
      have hsmul :
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              (1 / 2) a_half (- -ε) =
            a_half * frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) 1 (- -ε) := by
        simpa using (frobeniusValue_smul_c₀ aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly (1 / 2) a_half 1 hpk (-(-ε)))
      rw [hsmul]
      ring
    have hz1 :
        yAperyCanonicalLeftOne a₁ (-ε) =
          a₁ * yAperyCanonicalLeftOne 1 (-ε) := by
      unfold yAperyCanonicalLeftOne
      have hsmul :
          frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
              1 a₁ (- -ε) =
            a₁ * frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 1 (- -ε) := by
        simpa using (frobeniusValue_smul_c₀ aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 1 a₁ 1 hpk (-(-ε)))
      rw [hsmul]
      ring
    unfold aperyCanonicalLeftBranchTriple at h
    rw [hz0, hzh, hz1] at h
    exact h

lemma aperyCanonicalLeftBranchState_eq_zero_forces_seeds_zero
    {a₀ a_half a₁ δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ z ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly,
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z)
    (hinit : aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = 0) :
    a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0 := by
  exact aperyCanonicalLeftBranchTriple_zero_on_left_corridor_forces_seeds_zero
    hδ_pos
    (aperyCanonicalLeftBranchState_eq_zero_propagates_on_left_corridor
      hδ_pos hδ_lt_z1 hz₀ hbranch hinit)

private lemma yAperyCanonicalLeftZero_smul_c₀ (c c₀ t : ℝ) :
    yAperyCanonicalLeftZero (c * c₀) t =
      c * yAperyCanonicalLeftZero c₀ t := by
  have hpk :
      (aperyCanonicalPsSeq (2 + 1)).eval Number.aperyConifoldZ1Poly = 0 :=
    aperyCanonicalPsSeq_leading_eval_z1
  unfold yAperyCanonicalLeftZero
  simpa using (frobeniusValue_smul_c₀ aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 0 c c₀ hpk (-t))

private lemma yAperyCanonicalLeftHalf_smul_c₀ (c c₀ t : ℝ) :
    yAperyCanonicalLeftHalf (c * c₀) t =
      c * yAperyCanonicalLeftHalf c₀ t := by
  have hpk :
      (aperyCanonicalPsSeq (2 + 1)).eval Number.aperyConifoldZ1Poly = 0 :=
    aperyCanonicalPsSeq_leading_eval_z1
  unfold yAperyCanonicalLeftHalf
  rw [frobeniusValue_smul_c₀ aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly (1 / 2) c c₀ hpk (-t)]
  ring

private lemma yAperyCanonicalLeftOne_smul_c₀ (c c₀ t : ℝ) :
    yAperyCanonicalLeftOne (c * c₀) t =
      c * yAperyCanonicalLeftOne c₀ t := by
  have hpk :
      (aperyCanonicalPsSeq (2 + 1)).eval Number.aperyConifoldZ1Poly = 0 :=
    aperyCanonicalPsSeq_leading_eval_z1
  unfold yAperyCanonicalLeftOne
  rw [frobeniusValue_smul_c₀ aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 1 c c₀ hpk (-t)]
  ring

private lemma aperyCanonicalLeftBranchTriple_linear_combination
    (a₀ a_half a₁ t : ℝ) :
    aperyCanonicalLeftBranchTriple a₀ a_half a₁ t =
      a₀ * aperyCanonicalLeftBranchTriple 1 0 0 t +
        a_half * aperyCanonicalLeftBranchTriple 0 1 0 t +
          a₁ * aperyCanonicalLeftBranchTriple 0 0 1 t := by
  have h0_zero : yAperyCanonicalLeftZero 0 t = 0 := by
    have := yAperyCanonicalLeftZero_smul_c₀ 0 1 t
    simpa using this
  have hh_zero : yAperyCanonicalLeftHalf 0 t = 0 := by
    have := yAperyCanonicalLeftHalf_smul_c₀ 0 1 t
    simpa using this
  have h1_zero : yAperyCanonicalLeftOne 0 t = 0 := by
    have := yAperyCanonicalLeftOne_smul_c₀ 0 1 t
    simpa using this
  have hz0 :
      yAperyCanonicalLeftZero a₀ t =
        a₀ * yAperyCanonicalLeftZero 1 t := by
    rw [← yAperyCanonicalLeftZero_smul_c₀ a₀ 1 t]
    ring
  have hzh :
      yAperyCanonicalLeftHalf a_half t =
        a_half * yAperyCanonicalLeftHalf 1 t := by
    rw [← yAperyCanonicalLeftHalf_smul_c₀ a_half 1 t]
    ring
  have hz1 :
      yAperyCanonicalLeftOne a₁ t =
        a₁ * yAperyCanonicalLeftOne 1 t := by
    rw [← yAperyCanonicalLeftOne_smul_c₀ a₁ 1 t]
    ring
  unfold aperyCanonicalLeftBranchTriple
  rw [hz0, hzh, hz1, h0_zero, hh_zero, h1_zero]
  ring

/-- Coordinate-correct canonical left branch-state map, as a linear combination
of the three pure branch-state columns. -/
noncomputable def aperyCanonicalLeftBranchStateLinearMap (z : ℝ) :
    AperyODEState →ₗ[ℝ] AperyODEState where
  toFun A :=
    (A.1 * (aperyCanonicalLeftBranchState 1 0 0 z).1 +
        A.2.1 * (aperyCanonicalLeftBranchState 0 1 0 z).1 +
        A.2.2 * (aperyCanonicalLeftBranchState 0 0 1 z).1,
      A.1 * (aperyCanonicalLeftBranchState 1 0 0 z).2.1 +
          A.2.1 * (aperyCanonicalLeftBranchState 0 1 0 z).2.1 +
        A.2.2 * (aperyCanonicalLeftBranchState 0 0 1 z).2.1,
      A.1 * (aperyCanonicalLeftBranchState 1 0 0 z).2.2 +
          A.2.1 * (aperyCanonicalLeftBranchState 0 1 0 z).2.2 +
        A.2.2 * (aperyCanonicalLeftBranchState 0 0 1 z).2.2)
  map_add' A B := by
    ext <;> simp <;> ring
  map_smul' c A := by
    ext <;> simp <;> ring

@[simp] lemma aperyCanonicalLeftBranchStateLinearMap_apply
    (z a₀ a_half a₁ : ℝ) :
    aperyCanonicalLeftBranchStateLinearMap z (a₀, a_half, a₁) =
      (a₀ * (aperyCanonicalLeftBranchState 1 0 0 z).1 +
          a_half * (aperyCanonicalLeftBranchState 0 1 0 z).1 +
          a₁ * (aperyCanonicalLeftBranchState 0 0 1 z).1,
        a₀ * (aperyCanonicalLeftBranchState 1 0 0 z).2.1 +
            a_half * (aperyCanonicalLeftBranchState 0 1 0 z).2.1 +
          a₁ * (aperyCanonicalLeftBranchState 0 0 1 z).2.1,
        a₀ * (aperyCanonicalLeftBranchState 1 0 0 z).2.2 +
            a_half * (aperyCanonicalLeftBranchState 0 1 0 z).2.2 +
          a₁ * (aperyCanonicalLeftBranchState 0 0 1 z).2.2) := rfl

private lemma aperyCanonicalLeftBranchStateLinearMap_eq_state
    {δ z : ℝ}
    (hz : z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ x,
      x ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun y : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ y)
          (aperyODEStateField x
            (aperyCanonicalLeftBranchState a₀ a_half a₁ x)) x)
    (a₀ a_half a₁ : ℝ) :
    aperyCanonicalLeftBranchStateLinearMap z (a₀, a_half, a₁) =
      aperyCanonicalLeftBranchState a₀ a_half a₁ z := by
  let f : ℝ → ℝ := fun y =>
    aperyCanonicalLeftBranchTriple a₀ a_half a₁
      (y - Number.aperyConifoldZ1Poly)
  let f0 : ℝ → ℝ := fun y =>
    aperyCanonicalLeftBranchTriple 1 0 0
      (y - Number.aperyConifoldZ1Poly)
  let fh : ℝ → ℝ := fun y =>
    aperyCanonicalLeftBranchTriple 0 1 0
      (y - Number.aperyConifoldZ1Poly)
  let f1 : ℝ → ℝ := fun y =>
    aperyCanonicalLeftBranchTriple 0 0 1
      (y - Number.aperyConifoldZ1Poly)
  have hf_eq : f = fun y => a₀ * f0 y + a_half * fh y + a₁ * f1 y := by
    funext y
    exact aperyCanonicalLeftBranchTriple_linear_combination a₀ a_half a₁
      (y - Number.aperyConifoldZ1Poly)
  have h0_state := hbranch 1 0 0 z hz
  have hh_state := hbranch 0 1 0 z hz
  have h1_state := hbranch 0 0 1 z hz
  have h0_diff : DifferentiableAt ℝ f0 z := by
    have h := h0_state.differentiableAt.fst
    simpa [aperyCanonicalLeftBranchState, f0] using h
  have hh_diff : DifferentiableAt ℝ fh z := by
    have h := hh_state.differentiableAt.fst
    simpa [aperyCanonicalLeftBranchState, fh] using h
  have h1_diff : DifferentiableAt ℝ f1 z := by
    have h := h1_state.differentiableAt.fst
    simpa [aperyCanonicalLeftBranchState, f1] using h
  have h0_d_diff : DifferentiableAt ℝ (deriv f0) z := by
    have h := h0_state.differentiableAt.snd.fst
    simpa [aperyCanonicalLeftBranchState, f0] using h
  have hh_d_diff : DifferentiableAt ℝ (deriv fh) z := by
    have h := hh_state.differentiableAt.snd.fst
    simpa [aperyCanonicalLeftBranchState, fh] using h
  have h1_d_diff : DifferentiableAt ℝ (deriv f1) z := by
    have h := h1_state.differentiableAt.snd.fst
    simpa [aperyCanonicalLeftBranchState, f1] using h
  have hderiv :
      deriv f z =
        a₀ * deriv f0 z + a_half * deriv fh z + a₁ * deriv f1 z := by
    let g : ℝ → ℝ := fun y => a₀ * f0 y + a_half * fh y + a₁ * f1 y
    have hg : HasDerivAt g
        (a₀ * deriv f0 z + a_half * deriv fh z + a₁ * deriv f1 z) z := by
      have h0c : HasDerivAt (fun y => a₀ * f0 y) (a₀ * deriv f0 z) z :=
        h0_diff.hasDerivAt.const_mul a₀
      have hhc : HasDerivAt (fun y => a_half * fh y) (a_half * deriv fh z) z :=
        hh_diff.hasDerivAt.const_mul a_half
      have h1c : HasDerivAt (fun y => a₁ * f1 y) (a₁ * deriv f1 z) z :=
        h1_diff.hasDerivAt.const_mul a₁
      simpa [g, add_assoc] using (h0c.add hhc).add h1c
    have hf_has : HasDerivAt f
        (a₀ * deriv f0 z + a_half * deriv fh z + a₁ * deriv f1 z) z := by
      simpa [hf_eq] using hg
    exact hf_has.deriv
  have hderiv2 :
      deriv (deriv f) z =
        a₀ * deriv (deriv f0) z +
          a_half * deriv (deriv fh) z +
            a₁ * deriv (deriv f1) z := by
    let g : ℝ → ℝ := fun y => a₀ * deriv f0 y + a_half * deriv fh y +
      a₁ * deriv f1 y
    have hg : HasDerivAt g
        (a₀ * deriv (deriv f0) z +
          a_half * deriv (deriv fh) z +
            a₁ * deriv (deriv f1) z) z := by
      have h0c : HasDerivAt (fun y => a₀ * deriv f0 y)
          (a₀ * deriv (deriv f0) z) z :=
        h0_d_diff.hasDerivAt.const_mul a₀
      have hhc : HasDerivAt (fun y => a_half * deriv fh y)
          (a_half * deriv (deriv fh) z) z :=
        hh_d_diff.hasDerivAt.const_mul a_half
      have h1c : HasDerivAt (fun y => a₁ * deriv f1 y)
          (a₁ * deriv (deriv f1) z) z :=
        h1_d_diff.hasDerivAt.const_mul a₁
      simpa [g, add_assoc] using (h0c.add hhc).add h1c
    have hnear : ∀ᶠ y in nhds z,
        y ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly := by
      exact (isOpen_Ioo.mem_nhds hz)
    have hev : g =ᶠ[nhds z] deriv f := by
      filter_upwards [hnear] with y hy
      have hy0_state := hbranch 1 0 0 y hy
      have hyh_state := hbranch 0 1 0 y hy
      have hy1_state := hbranch 0 0 1 y hy
      have hy0 : DifferentiableAt ℝ f0 y := by
        have h := hy0_state.differentiableAt.fst
        simpa [aperyCanonicalLeftBranchState, f0] using h
      have hyh : DifferentiableAt ℝ fh y := by
        have h := hyh_state.differentiableAt.fst
        simpa [aperyCanonicalLeftBranchState, fh] using h
      have hy1 : DifferentiableAt ℝ f1 y := by
        have h := hy1_state.differentiableAt.fst
        simpa [aperyCanonicalLeftBranchState, f1] using h
      have hgy : deriv f y =
          a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y := by
        let gy : ℝ → ℝ := fun x => a₀ * f0 x + a_half * fh x + a₁ * f1 x
        have hgy_der : HasDerivAt gy
            (a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y) y := by
          have h0c : HasDerivAt (fun x => a₀ * f0 x) (a₀ * deriv f0 y) y :=
            hy0.hasDerivAt.const_mul a₀
          have hhc : HasDerivAt (fun x => a_half * fh x) (a_half * deriv fh y) y :=
            hyh.hasDerivAt.const_mul a_half
          have h1c : HasDerivAt (fun x => a₁ * f1 x) (a₁ * deriv f1 y) y :=
            hy1.hasDerivAt.const_mul a₁
          simpa [gy, add_assoc] using (h0c.add hhc).add h1c
        have hf_has : HasDerivAt f
            (a₀ * deriv f0 y + a_half * deriv fh y + a₁ * deriv f1 y) y := by
          simpa [hf_eq] using hgy_der
        exact hf_has.deriv
      simp [g, hgy]
    have hdf : HasDerivAt (deriv f)
        (a₀ * deriv (deriv f0) z +
          a_half * deriv (deriv fh) z +
            a₁ * deriv (deriv f1) z) z :=
      hg.congr_of_eventuallyEq hev.symm
    exact hdf.deriv
  ext
  · have hlin := aperyCanonicalLeftBranchTriple_linear_combination a₀ a_half a₁
      (z - Number.aperyConifoldZ1Poly)
    simpa [aperyCanonicalLeftBranchStateLinearMap, aperyCanonicalLeftBranchState]
      using hlin.symm
  · simpa [aperyCanonicalLeftBranchStateLinearMap, aperyCanonicalLeftBranchState,
      f, f0, fh, f1] using hderiv.symm
  · simpa [aperyCanonicalLeftBranchStateLinearMap, aperyCanonicalLeftBranchState,
      f, f0, fh, f1] using hderiv2.symm

lemma aperyCanonicalLeftBranchState_surjective_of_branch_ode
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z) :
    ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ,
        aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = Y := by
  let L : AperyODEState →ₗ[ℝ] AperyODEState :=
    aperyCanonicalLeftBranchStateLinearMap z₀
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro A hA
    rcases A with ⟨a₀, a_half, a₁⟩
    have hstate : aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = 0 := by
      have hrel := aperyCanonicalLeftBranchStateLinearMap_eq_state
        (δ := δ) (z := z₀) hz₀ hbranch a₀ a_half a₁
      simpa [L, hrel] using hA
    obtain ⟨ha₀, ha_half, ha₁⟩ :=
      aperyCanonicalLeftBranchState_eq_zero_forces_seeds_zero
        hδ_pos hδ_lt_z1 hz₀
        (fun z hz => hbranch a₀ a_half a₁ z hz) hstate
    ext <;> simp [ha₀, ha_half, ha₁]
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective L :=
    LinearMap.injective_iff_surjective.mp hinj
  intro Y
  rcases hsurj Y with ⟨A, hA⟩
  rcases A with ⟨a₀, a_half, a₁⟩
  refine ⟨a₀, a_half, a₁, ?_⟩
  have hrel := aperyCanonicalLeftBranchStateLinearMap_eq_state
    (δ := δ) (z := z₀) hz₀ hbranch a₀ a_half a₁
  simpa [L, hrel] using hA

lemma aperyCanonicalLeftBranchState_hasDerivAt_of_scalar_ode
    {a₀ a_half a₁ z y''' : ℝ}
    (hy : HasDerivAt
      (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))
      (deriv (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) z) z)
    (hy' : HasDerivAt
      (deriv (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)))
      (deriv (deriv (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))) z) z)
    (hy'' : HasDerivAt
      (deriv (deriv (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)))) y''' z)
    (hP : Polynomial.eval z Number.aperyPconifold ≠ 0)
    (hode :
      Polynomial.eval z Number.aperyPconifold * y'''
        + Polynomial.eval z Number.aperyQconifold *
          deriv (deriv (fun x : ℝ =>
            aperyCanonicalLeftBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly))) z
        + Polynomial.eval z aperyRconifold *
          deriv (fun x : ℝ =>
            aperyCanonicalLeftBranchTriple a₀ a_half a₁
              (x - Number.aperyConifoldZ1Poly)) z
        + Polynomial.eval z aperySconifold *
          aperyCanonicalLeftBranchTriple a₀ a_half a₁
            (z - Number.aperyConifoldZ1Poly) = 0) :
    HasDerivAt
      (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
      (aperyODEStateField z
        (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z := by
  simpa [aperyCanonicalLeftBranchState] using
    hasDerivAt_aperyODEState_of_scalar_ode
      (y := fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))
      (y' := deriv (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)))
      (y'' := deriv (deriv (fun x : ℝ =>
        aperyCanonicalLeftBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))))
      hy hy' hy'' hP hode

private lemma frobeniusValueCanonicalHalfDeriv_tendsto_pos_zero (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly (1 / 2) c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma frobeniusValueCanonicalHalfDeriv2_tendsto_pos_zero (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly (1 / 2) c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly (1 / 2) c₀ 9
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      aperyCanonicalHalf_small aperyCanonicalHalf_large
      aperyCanonicalHalf_threshold
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma frobeniusValueCanonicalDeriv_tendsto_neg_zero
    (ρ c₀ : ℝ) (M₀ : ℕ)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|ρ| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |ρ| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |ρ| - (2 : ℝ))) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly ρ c₀ M₀
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      (fun m hm => by
        have := hM0_small m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := hM0_large m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        simpa [aperyCanonicalPsSeq] using hM0_thresh m hm)
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hneg

private lemma frobeniusValueCanonicalDeriv2_tendsto_neg_zero
    (ρ c₀ : ℝ) (M₀ : ℕ)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|ρ| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |ρ| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |ρ| - (2 : ℝ))) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly ρ c₀ M₀
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      (fun m hm => by
        have := hM0_small m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := hM0_large m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        simpa [aperyCanonicalPsSeq] using hM0_thresh m hm)
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hneg

private lemma frobeniusValueCanonicalDeriv_tendsto_pos_zero
    (ρ c₀ : ℝ) (M₀ : ℕ)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|ρ| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |ρ| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |ρ| - (2 : ℝ))) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly ρ c₀ M₀
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      (fun m hm => by
        have := hM0_small m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := hM0_large m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        simpa [aperyCanonicalPsSeq] using hM0_thresh m hm)
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma frobeniusValueCanonicalDeriv2_tendsto_pos_zero
    (ρ c₀ : ℝ) (M₀ : ℕ)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|ρ| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |ρ| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |ρ| - (2 : ℝ))) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ ε)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ 0)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hslope : (Polynomial.derivative (aperyCanonicalPsSeq 3)).eval
      Number.aperyConifoldZ1Poly ≠ 0 := by
    simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hcont : ContinuousOn
      (fun t => frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly ρ c₀ t)
      (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly ρ c₀ M₀
      aperyCanonicalPsSeq_leading_eval_z1 hslope
      (fun m hm => by
        have := hM0_small m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        have := hM0_large m hm
        push_cast at this ⊢
        exact this)
      (fun m hm => by
        simpa [aperyCanonicalPsSeq] using hM0_thresh m hm)
      1000 (by norm_num) aperyCanonical_common_B_bound
      s hs_pos.le hs_lt
  have hnhds : Set.Icc (-s) s ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hs_pos
  have hct := hcont.continuousAt hnhds
  have hpos : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa using hct.tendsto.comp hpos

private lemma hasDerivAt_deriv_yAperyHalf_shift
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_neg : x - Number.aperyConifoldZ1Poly < 0)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.yAperyHalf c₀
        (z - Number.aperyConifoldZ1Poly)))
      (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) -
        frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly) /
          Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
        Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
          frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
            (1 / 2) c₀ (x - Number.aperyConifoldZ1Poly)) x := by
  let first : ℝ → ℝ := fun u =>
    -(1 / (2 * Real.sqrt (-u))) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u +
      Real.sqrt (-u) *
        frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u
  let second : ℝ → ℝ := fun u =>
    -(1 / (4 * (Real.sqrt (-u)) ^ 3)) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u -
      frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u / Real.sqrt (-u) +
      Real.sqrt (-u) *
        frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hsecond_unshift : HasDerivAt first
      (second (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [first, second] using
      yAperyHalf_hasDerivAt_second_expr c₀ M₀ B hB_nn
        hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
        (x - Number.aperyConifoldZ1Poly) hx_neg hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly))
      (second (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hsecond_unshift.comp x hinner
  have hneg_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly < 0 := by
    exact (isOpen_lt (continuous_id.sub continuous_const) continuous_const).mem_nhds hx_neg
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.yAperyHalf c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hneg_ev, hmem_ev] with z hz_neg hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hY := yAperyHalf_hasDerivAt c₀ M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
      (z - Number.aperyConifoldZ1Poly) hz_neg hz_mem
    have hcomp := hY.comp z hz_inner
    simpa [first] using hcomp.deriv
  exact hsecond_shift.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_deriv_yAperyZero_shift
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.yAperyZero c₀
        (z - Number.aperyConifoldZ1Poly)))
      (frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 c₀
        (x - Number.aperyConifoldZ1Poly)) x := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m →
      (|(0 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m →
      3 * |(0 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]
    exact hs_lt
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 0 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hVp : HasDerivAt Vp
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [Vp] using frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
      0 c₀ M₀ hpk' hslope' hM0_small' hM0_large'
      hM0_thresh' B hB_nn hB' s hs_pos hs_lt'
      (x - Number.aperyConifoldZ1Poly) hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => Vp (z - Number.aperyConifoldZ1Poly))
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hVp.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.yAperyZero c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => Vp (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁
      0 c₀ M₀ hpk' hslope' hM0_small' hM0_large'
      hM0_thresh' B hB_nn hB' s hs_pos hs_lt'
      (z - Number.aperyConifoldZ1Poly) hz_mem
    have hcomp := hV.comp z hz_inner
    unfold Ripple.Number.Frobenius.yAperyZero
    simpa [Vp, hps_def, hz_def] using hcomp.deriv
  simpa [Vp, hps_def, hz_def] using
    hsecond_shift.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_deriv_yApery_shift
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m →
        (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m →
        3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.yApery c₀
        (z - Number.aperyConifoldZ1Poly)))
      (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀
            (x - Number.aperyConifoldZ1Poly)
        + (x - Number.aperyConifoldZ1Poly) *
          frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀
            (x - Number.aperyConifoldZ1Poly)) x := by
  let first : ℝ → ℝ := fun u =>
    frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
      + u * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
  let second : ℝ → ℝ := fun u =>
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
      + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hsecond_unshift : HasDerivAt first
      (second (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [first, second] using
      Ripple.Number.Frobenius.yApery_hasDerivAt_second c₀ M₀ B hB_nn
        hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
        (x - Number.aperyConifoldZ1Poly) hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly))
      (second (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hsecond_unshift.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.yApery c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hY := Ripple.Number.Frobenius.yApery_hasDerivAt c₀ M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_pos hs_lt
      (z - Number.aperyConifoldZ1Poly) hz_mem
    have hcomp := hY.comp z hz_inner
    simpa [first] using hcomp.deriv
  simpa [second] using hsecond_shift.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_deriv_aperyBranchTriple_shift
    (a₀ a_half a₁ s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 153 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_neg : x - Number.aperyConifoldZ1Poly < 0)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)))
      (frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 a₀
          (x - Number.aperyConifoldZ1Poly) +
        (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
              (1 / 2) a_half (x - Number.aperyConifoldZ1Poly) -
          frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
              (1 / 2) a_half (x - Number.aperyConifoldZ1Poly) /
            Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
          Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
            frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
              (1 / 2) a_half (x - Number.aperyConifoldZ1Poly)) +
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 a₁
              (x - Number.aperyConifoldZ1Poly)
          + (x - Number.aperyConifoldZ1Poly) *
            frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 a₁
              (x - Number.aperyConifoldZ1Poly))) x := by
  let f0 : ℝ → ℝ := fun z =>
    Ripple.Number.Frobenius.yAperyZero a₀ (z - Number.aperyConifoldZ1Poly)
  let fh : ℝ → ℝ := fun z =>
    Ripple.Number.Frobenius.yAperyHalf a_half (z - Number.aperyConifoldZ1Poly)
  let f1 : ℝ → ℝ := fun z =>
    Ripple.Number.Frobenius.yApery a₁ (z - Number.aperyConifoldZ1Poly)
  let d0 : ℝ := frobeniusValueDeriv2
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
    2 Number.aperyConifoldZ1Poly 0 a₀
    (x - Number.aperyConifoldZ1Poly)
  let dh : ℝ :=
    (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
        (1 / 2) a_half (x - Number.aperyConifoldZ1Poly) -
      frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
        (1 / 2) a_half (x - Number.aperyConifoldZ1Poly) /
        Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
      Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
        frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly
          (1 / 2) a_half (x - Number.aperyConifoldZ1Poly))
  let d1 : ℝ :=
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 a₁
        (x - Number.aperyConifoldZ1Poly)
      + (x - Number.aperyConifoldZ1Poly) *
        frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 a₁
          (x - Number.aperyConifoldZ1Poly)
  have h0 : HasDerivAt (deriv f0) d0 x := by
    simpa [f0, d0] using
      hasDerivAt_deriv_yAperyZero_shift a₀ 9 153 (by norm_num)
        (fun m hm => Number.aperyConifold_small_Z m (by omega))
        (fun m hm => Number.aperyConifold_large_Z m (by omega))
        (fun m hm => Number.aperyConifold_threshold_Z m (by omega))
        aperyConifold_common_B_bound s hs_pos hs_lt x hx_mem
  have hh : HasDerivAt (deriv fh) dh x := by
    simpa [fh, dh] using
      hasDerivAt_deriv_yAperyHalf_shift a_half 9 153 (by norm_num)
        (fun m hm => Number.aperyConifold_small_H m (by omega))
        (fun m hm => Number.aperyConifold_large_H m (by omega))
        (fun m hm => Number.aperyConifold_threshold_H m (by omega))
        aperyConifold_common_B_bound s hs_pos hs_lt x hx_neg hx_mem
  have h1 : HasDerivAt (deriv f1) d1 x := by
    simpa [f1, d1] using
      hasDerivAt_deriv_yApery_shift a₁ 9 153 (by norm_num)
        (fun m hm => Number.aperyConifold_small_O m (by omega))
        (fun m hm => Number.aperyConifold_large_O m (by omega))
        (fun m hm => Number.aperyConifold_threshold_O m (by omega))
        aperyConifold_common_B_bound s hs_pos hs_lt x hx_mem
  have hsum : HasDerivAt (fun z : ℝ => deriv f0 z + deriv fh z + deriv f1 z)
      (d0 + dh + d1) x := by
    simpa [add_assoc] using (h0.add hh).add h1
  have hneg_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly < 0 := by
    exact (isOpen_lt (continuous_id.sub continuous_const) continuous_const).mem_nhds hx_neg
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => deriv f0 z + deriv fh z + deriv f1 z) := by
    filter_upwards [hneg_ev, hmem_ev] with z hz_neg hz_mem
    have h0d : DifferentiableAt ℝ f0 z := by
      have hinner : HasDerivAt
          (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
        simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
      have hV := frobeniusValue_hasDerivAt_std_general
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly 0 a₀ 9
        (by exact Number.aperyPconifold_eval_z1)
        (by exact Number.aperyPconifold_deriv_eval_z1_ne_zero)
        (fun m hm => by
          have := Number.aperyConifold_small_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_Z m (by omega)
          push_cast at this ⊢; exact this)
        153 (by norm_num) aperyConifold_common_B_bound
        s hs_pos hs_lt (z - Number.aperyConifoldZ1Poly) hz_mem
      exact (hV.comp z hinner).differentiableAt
    have hhd : DifferentiableAt ℝ fh z := by
      have hinner : HasDerivAt
          (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
        simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
      have hY := yAperyHalf_hasDerivAt a_half 9 153 (by norm_num)
        (fun m hm => Number.aperyConifold_small_H m (by omega))
        (fun m hm => Number.aperyConifold_large_H m (by omega))
        (fun m hm => Number.aperyConifold_threshold_H m (by omega))
        aperyConifold_common_B_bound s hs_pos hs_lt
        (z - Number.aperyConifoldZ1Poly) hz_neg hz_mem
      exact (hY.comp z hinner).differentiableAt
    have h1d : DifferentiableAt ℝ f1 z := by
      have hinner : HasDerivAt
          (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
        simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
      have hY := Ripple.Number.Frobenius.yApery_hasDerivAt a₁ 9 153 (by norm_num)
        (fun m hm => Number.aperyConifold_small_O m (by omega))
        (fun m hm => Number.aperyConifold_large_O m (by omega))
        (fun m hm => Number.aperyConifold_threshold_O m (by omega))
        aperyConifold_common_B_bound s hs_pos hs_lt
        (z - Number.aperyConifoldZ1Poly) hz_mem
      exact (hY.comp z hinner).differentiableAt
    change deriv (fun z : ℝ => f0 z + fh z + f1 z) z =
      deriv f0 z + deriv fh z + deriv f1 z
    have hA : deriv (fun z : ℝ => f0 z + fh z + f1 z) z =
        deriv (fun z : ℝ => f0 z + fh z) z + deriv f1 z := by
      simpa [Pi.add_apply, add_assoc] using deriv_add (h0d.add hhd) h1d
    have hB : deriv (fun z : ℝ => f0 z + fh z) z =
        deriv f0 z + deriv fh z := by
      simpa [Pi.add_apply] using deriv_add h0d hhd
    rw [hA, hB]
  simpa [d0, dh, d1] using hsum.congr_of_eventuallyEq hderiv_ev

private lemma frobeniusValue_half_tendsto_neg_zero_seed (c₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => frobeniusValue
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly (1 / 2) c₀ (-ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c₀) := by
  have hneg : Filter.Tendsto (fun ε : ℝ => -ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Filter.Tendsto (fun ε : ℝ => -ε) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  have hbase := Ripple.Number.Frobenius.aperyFrobenius_half_tendsto_at_zero.comp hneg
  have hscaled : Filter.Tendsto
      (fun ε : ℝ => c₀ *
        frobeniusValue
          (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c₀ * 1)) :=
    hbase.const_mul c₀
  rw [mul_one] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with ε
  have hpk :
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        (2 + 1)).eval Number.aperyConifoldZ1Poly = 0 :=
    Number.aperyPconifold_eval_z1
  have hsmul := frobeniusValue_smul_c₀
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
    2 Number.aperyConifoldZ1Poly (1 / 2) c₀ 1 hpk (-ε)
  simpa using hsmul.symm

private lemma aperyBranchTriple_second_scaled_tendsto
    (a₀ a_half a₁ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          deriv (deriv
            (fun z : ℝ => Ripple.Number.Frobenius.aperyBranchTriple a₀ a_half a₁
              (z - Number.aperyConifoldZ1Poly)))
            (aperyConifoldZ1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
  rcases aperyConifold_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have heps : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsqrt : Filter.Tendsto (fun ε : ℝ => Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have heps_sqrt : Filter.Tendsto (fun ε : ℝ => ε * Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using heps.mul hsqrt
  have heps2 : Filter.Tendsto (fun ε : ℝ => ε ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ 2 : ℝ)) := heps.pow 2
  have hV0dd := frobeniusValueDeriv2_tendsto_neg_zero_general
    0 a₀ 9 153 (by norm_num)
    (fun m hm => Number.aperyConifold_small_Z m (by omega))
    (fun m hm => Number.aperyConifold_large_Z m (by omega))
    (fun m hm => Number.aperyConifold_threshold_Z m (by omega))
    aperyConifold_common_B_bound s hs_pos hs_lt
  have hVh := frobeniusValue_half_tendsto_neg_zero_seed a_half
  have hVhd := frobeniusValueDeriv_tendsto_neg_zero_general
    (1 / 2) a_half 9 153 (by norm_num)
    (fun m hm => Number.aperyConifold_small_H m (by omega))
    (fun m hm => Number.aperyConifold_large_H m (by omega))
    (fun m hm => Number.aperyConifold_threshold_H m (by omega))
    aperyConifold_common_B_bound s hs_pos hs_lt
  have hVhdd := frobeniusValueDeriv2_tendsto_neg_zero_general
    (1 / 2) a_half 9 153 (by norm_num)
    (fun m hm => Number.aperyConifold_small_H m (by omega))
    (fun m hm => Number.aperyConifold_large_H m (by omega))
    (fun m hm => Number.aperyConifold_threshold_H m (by omega))
    aperyConifold_common_B_bound s hs_pos hs_lt
  have hV1d := frobeniusValueDeriv_tendsto_neg_zero_general
    1 a₁ 9 153 (by norm_num)
    (fun m hm => Number.aperyConifold_small_O m (by omega))
    (fun m hm => Number.aperyConifold_large_O m (by omega))
    (fun m hm => Number.aperyConifold_threshold_O m (by omega))
    aperyConifold_common_B_bound s hs_pos hs_lt
  have hV1dd := frobeniusValueDeriv2_tendsto_neg_zero_general
    1 a₁ 9 153 (by norm_num)
    (fun m hm => Number.aperyConifold_small_O m (by omega))
    (fun m hm => Number.aperyConifold_large_O m (by omega))
    (fun m hm => Number.aperyConifold_threshold_O m (by omega))
    aperyConifold_common_B_bound s hs_pos hs_lt
  have hmodel : Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          frobeniusValueDeriv2
            (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            2 Number.aperyConifoldZ1Poly 0 a₀ (-ε)
        - (1 / 4) *
          frobeniusValue
            (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            2 Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        - ε *
          frobeniusValueDeriv
            (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            2 Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        + ε ^ 2 *
          frobeniusValueDeriv2
            (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            2 Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        + ε * Real.sqrt ε *
          (2 *
            frobeniusValueDeriv
              (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
              2 Number.aperyConifoldZ1Poly 1 a₁ (-ε)
            - ε *
              frobeniusValueDeriv2
                (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
                2 Number.aperyConifoldZ1Poly 1 a₁ (-ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have h0term := heps_sqrt.mul hV0dd
    have hhmain := hVh.const_mul (-(1 / 4 : ℝ))
    have hhdterm := heps.mul hVhd
    have hhddterm := heps2.mul hVhdd
    have h1inner := (hV1d.const_mul (2 : ℝ)).sub (heps.mul hV1dd)
    have h1term := heps_sqrt.mul h1inner
    have hsum :=
      (((h0term.add hhmain).sub hhdterm).add hhddterm).add h1term
    convert hsum using 1
    · ext ε
      ring_nf
    · ring_nf
  refine hmodel.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_s : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < s :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hs_pos)
  filter_upwards [hev_pos, hev_s] with ε hε_pos hε_s
  have hx_neg :
      aperyConifoldZ1 - ε - Number.aperyConifoldZ1Poly < 0 := by
    change Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly < 0
    linarith
  have hx_mem :
      aperyConifoldZ1 - ε - Number.aperyConifoldZ1Poly ∈
        Metric.ball (0 : ℝ) s := by
    rw [Metric.mem_ball, Real.dist_eq]
    change |Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly - 0| < s
    rw [show Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly - 0 =
        -ε by ring, abs_neg, abs_of_pos hε_pos]
    exact hε_s
  have hderiv := (hasDerivAt_deriv_aperyBranchTriple_shift
    a₀ a_half a₁ s hs_pos hs_lt (aperyConifoldZ1 - ε)
    hx_neg hx_mem).deriv
  rw [hderiv]
  symm
  have hsub :
      aperyConifoldZ1 - ε - Number.aperyConifoldZ1Poly = -ε := by
    change Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly = -ε
    ring
  rw [hsub]
  simp only [neg_neg]
  change ε * Real.sqrt ε *
      (frobeniusValueDeriv2
          (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          2 Number.aperyConifoldZ1Poly 0 a₀ (-ε) +
        (-(1 / (4 * (Real.sqrt ε) ^ 3)) *
            frobeniusValue
              (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
              2 Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε) -
          frobeniusValueDeriv
              (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
              2 Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε) /
            Real.sqrt ε +
          Real.sqrt ε *
            frobeniusValueDeriv2
              (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
              2 Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)) +
        (2 *
            frobeniusValueDeriv
              (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
              2 Number.aperyConifoldZ1Poly 1 a₁ (-ε) +
          (-ε) *
            frobeniusValueDeriv2
              (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
              2 Number.aperyConifoldZ1Poly 1 a₁ (-ε))) = _
  have hs_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
  have hs2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε_pos.le
  field_simp [hs_ne]
  rw [show (Real.sqrt ε) ^ 4 = ε ^ 2 by
    rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 by ring, hs2]]
  rw [show (Real.sqrt ε) ^ 3 = ε * Real.sqrt ε by
    rw [show (Real.sqrt ε) ^ 3 = (Real.sqrt ε) ^ 2 * Real.sqrt ε by ring, hs2]]
  rw [hs2]
  ring

private lemma yAperyCanonicalHalf_second_scaled_tendsto (a_half : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          deriv (deriv
            (fun z : ℝ => yAperyCanonicalHalf a_half
              (z - Number.aperyConifoldZ1Poly)))
            (aperyConifoldZ1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have heps : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsqrt : Filter.Tendsto (fun ε : ℝ => Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have heps2 : Filter.Tendsto (fun ε : ℝ => ε ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ 2 : ℝ)) := heps.pow 2
  have hV := frobeniusValueCanonicalHalf_tendsto_neg_zero_seed a_half
  have hVd := frobeniusValueCanonicalHalfDeriv_tendsto_neg_zero a_half
  have hVdd := frobeniusValueCanonicalHalfDeriv2_tendsto_neg_zero a_half
  have hmodel : Filter.Tendsto
      (fun ε : ℝ =>
        -(1 / 4 : ℝ) *
          frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        - ε *
          frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        + ε ^ 2 *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have hmain := hV.const_mul (-(1 / 4 : ℝ))
    have hdterm := heps.mul hVd
    have hddterm := heps2.mul hVdd
    have hsum := (hmain.sub hdterm).add hddterm
    convert hsum using 1
    · ext ε
      ring
  refine hmodel.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_s : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < s :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hs_pos)
  filter_upwards [hev_pos, hev_s] with ε hε_pos hε_s
  have hx_neg :
      aperyConifoldZ1 - ε - Number.aperyConifoldZ1Poly < 0 := by
    change Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly < 0
    linarith
  have hx_mem :
      aperyConifoldZ1 - ε - Number.aperyConifoldZ1Poly ∈
        Metric.ball (0 : ℝ) s := by
    rw [Metric.mem_ball, Real.dist_eq]
    change |Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly - 0| < s
    rw [show Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly - 0 =
        -ε by ring, abs_neg, abs_of_pos hε_pos]
    exact hε_s
  rw [deriv_deriv_yAperyCanonicalHalf_shift_eq a_half s hs_pos hs_lt
    (aperyConifoldZ1 - ε) hx_neg hx_mem]
  symm
  have hsub :
      aperyConifoldZ1 - ε - Number.aperyConifoldZ1Poly = -ε := by
    change Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly = -ε
    ring
  rw [hsub]
  simp only [neg_neg]
  change ε * Real.sqrt ε *
      (-(1 / (4 * (Real.sqrt ε) ^ 3)) *
          frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε) -
        frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε) /
          Real.sqrt ε +
        Real.sqrt ε *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)) = _
  have hs_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
  have hs2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε_pos.le
  field_simp [hs_ne]
  rw [show (Real.sqrt ε) ^ 4 = ε ^ 2 by
    rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 by ring, hs2]]
  rw [hs2]

private lemma yAperyCanonicalLeftHalf_second_scaled_tendsto (a_half : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          deriv (deriv
            (fun z : ℝ => yAperyCanonicalLeftHalf a_half
              (z - Number.aperyConifoldZ1Poly)))
            (aperyConifoldZ1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have heps : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have heps2 : Filter.Tendsto (fun ε : ℝ => ε ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ 2 : ℝ)) := heps.pow 2
  have hV := frobeniusValueCanonicalHalf_tendsto_pos_zero_seed a_half
  have hVd := frobeniusValueCanonicalHalfDeriv_tendsto_pos_zero a_half
  have hVdd := frobeniusValueCanonicalHalfDeriv2_tendsto_pos_zero a_half
  have hmodel : Filter.Tendsto
      (fun ε : ℝ =>
        -(1 / 4 : ℝ) *
          frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε
        + ε *
          frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε
        + ε ^ 2 *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have hmain := hV.const_mul (-(1 / 4 : ℝ))
    have hdterm := heps.mul hVd
    have hddterm := heps2.mul hVdd
    have hsum := (hmain.add hdterm).add hddterm
    convert hsum using 1
    · ext ε
      ring
  refine hmodel.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_s : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < s :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hs_pos)
  filter_upwards [hev_pos, hev_s] with ε hε_pos hε_s
  have hx_tau_pos :
      0 < Number.aperyConifoldZ1Poly - (aperyConifoldZ1 - ε) := by
    change 0 < Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε)
    linarith
  have hx_tau_mem :
      Number.aperyConifoldZ1Poly - (aperyConifoldZ1 - ε) ∈
        Metric.ball (0 : ℝ) s := by
    rw [Metric.mem_ball, Real.dist_eq]
    change |Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε) - 0| < s
    rw [show Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε) - 0 =
        ε by ring, abs_of_pos hε_pos]
    exact hε_s
  rw [deriv_deriv_yAperyCanonicalLeftHalf_shift_eq a_half s hs_pos hs_lt
    (aperyConifoldZ1 - ε) hx_tau_pos hx_tau_mem]
  symm
  have hsub :
      Number.aperyConifoldZ1Poly - (aperyConifoldZ1 - ε) = ε := by
    change Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε) = ε
    ring
  rw [hsub]
  change ε * Real.sqrt ε *
      (-(1 / (4 * (Real.sqrt ε) ^ 3)) *
          frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε +
        frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε /
          Real.sqrt ε +
        Real.sqrt ε *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε) = _
  have hs_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
  have hs2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε_pos.le
  field_simp [hs_ne]
  rw [show (Real.sqrt ε) ^ 4 = ε ^ 2 by
    rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 by ring, hs2]]
  rw [hs2]

private lemma hasDerivAt_deriv_yAperyCanonicalZero_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => yAperyCanonicalZero c₀
        (z - Number.aperyConifoldZ1Poly)))
      (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀
        (x - Number.aperyConifoldZ1Poly)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 0 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hVp : HasDerivAt Vp
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    simpa [Vp] using frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
      0 c₀ 9 hpk' hslope'
      (fun m hm => by
        have := Number.aperyConifold_small_Z m (by omega)
        push_cast at this ⊢; exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_Z m (by omega)
        push_cast at this ⊢; exact this)
      (fun m hm => by
        have := Number.aperyConifold_threshold_Z m (by omega)
        push_cast at this ⊢; exact this)
      1000 (by norm_num) hB' s hs_pos hs_lt'
      (x - Number.aperyConifoldZ1Poly) hx_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => Vp (z - Number.aperyConifoldZ1Poly))
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hVp.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => yAperyCanonicalZero c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => Vp (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁
      0 c₀ 9 hpk' hslope'
      (fun m hm => by
        have := Number.aperyConifold_small_Z m (by omega)
        push_cast at this ⊢; exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_Z m (by omega)
        push_cast at this ⊢; exact this)
      (fun m hm => by
        have := Number.aperyConifold_threshold_Z m (by omega)
        push_cast at this ⊢; exact this)
      1000 (by norm_num) hB' s hs_pos hs_lt'
      (z - Number.aperyConifoldZ1Poly) hz_mem
    have hcomp := hV.comp z hz_inner
    simpa [yAperyCanonicalZero, Vp, hps_def, hz_def] using hcomp.deriv
  simpa [Vp, hps_def, hz_def] using
    hsecond_shift.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_deriv_yAperyCanonicalOne_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hx_mem : x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => yAperyCanonicalOne c₀
        (z - Number.aperyConifoldZ1Poly)))
      (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (x - Number.aperyConifoldZ1Poly)
        + (x - Number.aperyConifoldZ1Poly) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (x - Number.aperyConifoldZ1Poly)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ 1 c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 1 c₀ u
  let first : ℝ → ℝ := fun u => V u + u * Vp u
  let second : ℝ → ℝ := fun u =>
    2 * frobeniusValueDeriv ps 2 z₁ 1 c₀ u +
      u * frobeniusValueDeriv2 ps 2 z₁ 1 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => z - Number.aperyConifoldZ1Poly) 1 x := by
    simpa using (hasDerivAt_id x).sub_const Number.aperyConifoldZ1Poly
  have hsecond_unshift : HasDerivAt first
      (second (x - Number.aperyConifoldZ1Poly))
      (x - Number.aperyConifoldZ1Poly) := by
    have hV : HasDerivAt V
        (frobeniusValueDeriv ps 2 z₁ 1 c₀
          (x - Number.aperyConifoldZ1Poly))
        (x - Number.aperyConifoldZ1Poly) := by
      simpa [V] using frobeniusValue_hasDerivAt_std_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (x - Number.aperyConifoldZ1Poly) hx_mem
    have hVp : HasDerivAt Vp
        (frobeniusValueDeriv2 ps 2 z₁ 1 c₀
          (x - Number.aperyConifoldZ1Poly))
        (x - Number.aperyConifoldZ1Poly) := by
      simpa [Vp] using frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (x - Number.aperyConifoldZ1Poly) hx_mem
    have hid : HasDerivAt (fun u : ℝ => u) 1
        (x - Number.aperyConifoldZ1Poly) := hasDerivAt_id _
    have hprod := hid.mul hVp
    have hsum := hV.add hprod
    convert hsum using 1 <;> simp [first, second, Vp] <;> ring
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly))
      (second (x - Number.aperyConifoldZ1Poly)) x := by
    simpa using hsecond_unshift.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => yAperyCanonicalOne c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => first (z - Number.aperyConifoldZ1Poly)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
      simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
    have hV : HasDerivAt V
        (frobeniusValueDeriv ps 2 z₁ 1 c₀
          (z - Number.aperyConifoldZ1Poly))
        (z - Number.aperyConifoldZ1Poly) := by
      simpa [V] using frobeniusValue_hasDerivAt_std_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (z - Number.aperyConifoldZ1Poly) hz_mem
    have hid : HasDerivAt (fun u : ℝ => u) 1
        (z - Number.aperyConifoldZ1Poly) := hasDerivAt_id _
    have hprod := hid.mul hV
    have hcomp := hprod.comp z hz_inner
    simpa [yAperyCanonicalOne, first, V, Vp, hps_def, hz_def] using hcomp.deriv
  simpa [first, second, Vp, hps_def, hz_def] using
    hsecond_shift.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_deriv_yAperyCanonicalLeftZero_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => yAperyCanonicalLeftZero c₀
        (z - Number.aperyConifoldZ1Poly)))
      (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀
        (Number.aperyConifoldZ1Poly - x)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 0 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hVp : HasDerivAt Vp
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vp, hps_def, hz_def] using
      frobeniusValueDeriv_hasDerivAt_general ps 2 z₁ 0 c₀ 9
        hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_Z m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hsecond_shift : HasDerivAt
      (fun z : ℝ => - Vp (Number.aperyConifoldZ1Poly - z))
      (frobeniusValueDeriv2 ps 2 z₁ 0 c₀
        (Number.aperyConifoldZ1Poly - x)) x := by
    have hcomp := hVp.comp x hinner
    simpa using hcomp.neg
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hderiv_ev :
      deriv (fun z : ℝ => yAperyCanonicalLeftZero c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => - Vp (Number.aperyConifoldZ1Poly - z)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => Number.aperyConifoldZ1Poly - y) (-1) z := by
      simpa using (hasDerivAt_const z Number.aperyConifoldZ1Poly).sub
        (hasDerivAt_id z)
    have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁ 0 c₀ 9
      hpk' hslope'
      (fun m hm => by
        have := Number.aperyConifold_small_Z m (by omega)
        push_cast at this ⊢; exact this)
      (fun m hm => by
        have := Number.aperyConifold_large_Z m (by omega)
        push_cast at this ⊢; exact this)
      (fun m hm => by
        have := Number.aperyConifold_threshold_Z m (by omega)
        push_cast at this ⊢; exact this)
      1000 (by norm_num) hB' s hs_pos hs_lt'
      (Number.aperyConifoldZ1Poly - z) hz_mem
    have hcomp := hV.comp z hz_inner
    simpa [yAperyCanonicalLeftZero, Vp, hps_def, hz_def] using hcomp.deriv
  simpa [Vp, hps_def, hz_def] using
    hsecond_shift.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_yAperyCanonicalLeftZero_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ => yAperyCanonicalLeftZero c₀
        (z - Number.aperyConifoldZ1Poly))
      (-(frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀
        (Number.aperyConifoldZ1Poly - x))) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ 0 c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 0 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hV : HasDerivAt V
      (Vp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [V, Vp, hps_def, hz_def] using
      frobeniusValue_hasDerivAt_std_general ps 2 z₁ 0 c₀ 9
        hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_Z m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hcomp := hV.comp x hinner
  simpa [yAperyCanonicalLeftZero, V, Vp, hps_def, hz_def] using hcomp

private lemma deriv_deriv_yAperyCanonicalLeftZero_shift_eq
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => yAperyCanonicalLeftZero c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      frobeniusValueDeriv2 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀
        (Number.aperyConifoldZ1Poly - x) := by
  exact (hasDerivAt_deriv_yAperyCanonicalLeftZero_shift
    c₀ s hs_pos hs_lt x hτ_mem).deriv

private lemma hasDerivAt_deriv_deriv_yAperyCanonicalLeftZero_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv (deriv
      (fun z : ℝ => yAperyCanonicalLeftZero c₀
        (z - Number.aperyConifoldZ1Poly))))
      (-(frobeniusValueDeriv3 aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 0 c₀
        (Number.aperyConifoldZ1Poly - x))) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let Vpp : ℝ → ℝ := fun u => frobeniusValueDeriv2 ps 2 z₁ 0 c₀ u
  let Vppp : ℝ → ℝ := fun u => frobeniusValueDeriv3 ps 2 z₁ 0 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hVpp : HasDerivAt Vpp
      (Vppp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vpp, Vppp, hps_def, hz_def] using
      frobeniusValueDeriv2_hasDerivAt_general ps 2 z₁ 0 c₀ 9
        hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_Z m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_Z m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hthird_shift : HasDerivAt
      (fun z : ℝ => Vpp (Number.aperyConifoldZ1Poly - z))
      (-(Vppp (Number.aperyConifoldZ1Poly - x))) x := by
    simpa using hVpp.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hderiv2_ev :
      deriv (deriv (fun z : ℝ => yAperyCanonicalLeftZero c₀
        (z - Number.aperyConifoldZ1Poly))) =ᶠ[nhds x]
        (fun z : ℝ => Vpp (Number.aperyConifoldZ1Poly - z)) := by
    filter_upwards [hmem_ev] with z hz_mem
    rw [deriv_deriv_yAperyCanonicalLeftZero_shift_eq c₀ s hs_pos hs_lt
      z hz_mem]
  simpa [Vppp, hps_def, hz_def] using
    hthird_shift.congr_of_eventuallyEq hderiv2_ev

private lemma yAperyCanonicalLeftZero_state_hasDerivAt
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_pos : 0 < x)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ =>
        (yAperyCanonicalLeftZero c₀ (z - Number.aperyConifoldZ1Poly),
          deriv (fun y : ℝ =>
            yAperyCanonicalLeftZero c₀ (y - Number.aperyConifoldZ1Poly)) z,
          deriv (deriv (fun y : ℝ =>
            yAperyCanonicalLeftZero c₀ (y - Number.aperyConifoldZ1Poly))) z))
      (aperyODEStateField x
        (yAperyCanonicalLeftZero c₀ (x - Number.aperyConifoldZ1Poly),
          deriv (fun y : ℝ =>
            yAperyCanonicalLeftZero c₀ (y - Number.aperyConifoldZ1Poly)) x,
          deriv (deriv (fun y : ℝ =>
            yAperyCanonicalLeftZero c₀ (y - Number.aperyConifoldZ1Poly))) x)) x := by
  let y : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftZero c₀ (z - Number.aperyConifoldZ1Poly)
  have hy : HasDerivAt y (deriv y x) x := by
    have h0 := hasDerivAt_yAperyCanonicalLeftZero_shift
      c₀ s hs_pos hs_lt x hτ_mem
    have h0' : HasDerivAt y
        (-(frobeniusValueDeriv aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x))) x := by
      simpa [y] using h0
    convert h0' using 1
    exact h0'.deriv
  have hdy_exp :
      deriv y x =
        (-(frobeniusValueDeriv aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x))) := by
    simpa [y] using (hasDerivAt_yAperyCanonicalLeftZero_shift
      c₀ s hs_pos hs_lt x hτ_mem).deriv
  have hy' : HasDerivAt (deriv y) (deriv (deriv y) x) x := by
    have h0 := hasDerivAt_deriv_yAperyCanonicalLeftZero_shift
      c₀ s hs_pos hs_lt x hτ_mem
    have h0' : HasDerivAt (deriv y)
        (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x)) x := by
      simpa [y] using h0
    convert h0' using 1
    exact h0'.deriv
  have hddy_exp :
      deriv (deriv y) x =
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 c₀
          (Number.aperyConifoldZ1Poly - x) := by
    simpa [y] using
      deriv_deriv_yAperyCanonicalLeftZero_shift_eq c₀ s hs_pos hs_lt
        x hτ_mem
  let y3 : ℝ :=
    (-(frobeniusValueDeriv3 aperyCanonicalPsSeq 2
      Number.aperyConifoldZ1Poly 0 c₀
      (Number.aperyConifoldZ1Poly - x)))
  have hy'' : HasDerivAt (deriv (deriv y)) y3 x := by
    simpa [y, y3] using
      hasDerivAt_deriv_deriv_yAperyCanonicalLeftZero_shift
        c₀ s hs_pos hs_lt x hτ_mem
  have hode :
      Polynomial.eval x Number.aperyPconifold * y3
        + Polynomial.eval x Number.aperyQconifold * deriv (deriv y) x
        + Polynomial.eval x aperyRconifold * deriv y x
        + Polynomial.eval x aperySconifold * y x = 0 := by
    have hscalar := aperyCanonicalLeftZero_scalar_ode
      c₀ s x hs_pos hs_lt hτ_pos hτ_mem
    rw [hdy_exp, hddy_exp]
    simpa [y, y3, yAperyCanonicalLeftZero] using hscalar
  have hP : Polynomial.eval x Number.aperyPconifold ≠ 0 :=
    aperyPconifold_eval_ne_zero_of_pos_lt_z1 hx_pos (sub_pos.mp hτ_pos)
  simpa [y] using
    hasDerivAt_aperyODEState_of_scalar_ode
      (y := y) (y' := deriv y) (y'' := deriv (deriv y))
      hy hy' hy'' hP hode

private lemma hasDerivAt_deriv_yAperyCanonicalLeftOne_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv
      (fun z : ℝ => yAperyCanonicalLeftOne c₀
        (z - Number.aperyConifoldZ1Poly)))
      (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)
        + (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ 1 c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 1 c₀ u
  let first : ℝ → ℝ := fun u => V u + u * Vp u
  let second : ℝ → ℝ := fun u =>
    2 * frobeniusValueDeriv ps 2 z₁ 1 c₀ u +
      u * frobeniusValueDeriv2 ps 2 z₁ 1 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hsecond_unshift : HasDerivAt first
      (second (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    have hV : HasDerivAt V
        (frobeniusValueDeriv ps 2 z₁ 1 c₀
          (Number.aperyConifoldZ1Poly - x))
        (Number.aperyConifoldZ1Poly - x) := by
      simpa [V] using frobeniusValue_hasDerivAt_std_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
    have hVp : HasDerivAt Vp
        (frobeniusValueDeriv2 ps 2 z₁ 1 c₀
          (Number.aperyConifoldZ1Poly - x))
        (Number.aperyConifoldZ1Poly - x) := by
      simpa [Vp] using frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
    have hid : HasDerivAt (fun u : ℝ => u) 1
        (Number.aperyConifoldZ1Poly - x) := hasDerivAt_id _
    have hprod := hid.mul hVp
    have hsum := hV.add hprod
    convert hsum using 1 <;> simp [first, second, Vp] <;> ring
  have hsecond_neg : HasDerivAt
      (fun z : ℝ => - first (Number.aperyConifoldZ1Poly - z))
      (second (Number.aperyConifoldZ1Poly - x)) x := by
    have hcomp := hsecond_unshift.comp x hinner
    simpa using hcomp.neg
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hderiv_ev :
      deriv (fun z : ℝ => yAperyCanonicalLeftOne c₀
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => - first (Number.aperyConifoldZ1Poly - z)) := by
    filter_upwards [hmem_ev] with z hz_mem
    have hz_inner : HasDerivAt
        (fun y : ℝ => Number.aperyConifoldZ1Poly - y) (-1) z := by
      simpa using (hasDerivAt_const z Number.aperyConifoldZ1Poly).sub
        (hasDerivAt_id z)
    have hV : HasDerivAt V
        (frobeniusValueDeriv ps 2 z₁ 1 c₀
          (Number.aperyConifoldZ1Poly - z))
        (Number.aperyConifoldZ1Poly - z) := by
      simpa [V] using frobeniusValue_hasDerivAt_std_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - z) hz_mem
    have hid : HasDerivAt (fun u : ℝ => u) 1
        (Number.aperyConifoldZ1Poly - z) := hasDerivAt_id _
    have hprod := hid.mul hV
    have hcomp := hprod.comp z hz_inner
    simpa [yAperyCanonicalLeftOne, first, V, Vp, hps_def, hz_def] using hcomp.deriv
  simpa [first, second, Vp, hps_def, hz_def] using
    hsecond_neg.congr_of_eventuallyEq hderiv_ev

private lemma hasDerivAt_yAperyCanonicalLeftOne_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ => yAperyCanonicalLeftOne c₀
        (z - Number.aperyConifoldZ1Poly))
      (-(frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)
          + (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x))) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let V : ℝ → ℝ := fun u => frobeniusValue ps 2 z₁ 1 c₀ u
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 1 c₀ u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hV : HasDerivAt V
      (Vp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [V, Vp, hps_def, hz_def] using
      frobeniusValue_hasDerivAt_std_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hid : HasDerivAt (fun u : ℝ => u) 1
      (Number.aperyConifoldZ1Poly - x) := hasDerivAt_id _
  have hprod : HasDerivAt (fun u : ℝ => u * V u)
      (V (Number.aperyConifoldZ1Poly - x) +
        (Number.aperyConifoldZ1Poly - x) *
          Vp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    convert hid.mul hV using 1 <;> ring
  have hcomp := hprod.comp x hinner
  simpa [yAperyCanonicalLeftOne, V, Vp, hps_def, hz_def] using hcomp

private lemma deriv_deriv_yAperyCanonicalLeftOne_shift_eq
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    deriv (deriv
      (fun z : ℝ => yAperyCanonicalLeftOne c₀
        (z - Number.aperyConifoldZ1Poly))) x =
      (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)
        + (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)) := by
  exact (hasDerivAt_deriv_yAperyCanonicalLeftOne_shift
    c₀ s hs_pos hs_lt x hτ_mem).deriv

private lemma hasDerivAt_deriv_deriv_yAperyCanonicalLeftOne_shift
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (deriv (deriv
      (fun z : ℝ => yAperyCanonicalLeftOne c₀
        (z - Number.aperyConifoldZ1Poly))))
      (-(3 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)
          + (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv3 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x))) x := by
  set ps := aperyCanonicalPsSeq with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps_def, hz_def]
    exact aperyCanonicalPsSeq_leading_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ (1000 : ℝ) := by
    intro j' hj' ℓ
    exact aperyCanonical_common_B_bound j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * (1000 : ℝ) *
      ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps_def, hz_def, aperyCanonicalPsSeq_three]
    exact hs_lt
  let Vp : ℝ → ℝ := fun u => frobeniusValueDeriv ps 2 z₁ 1 c₀ u
  let Vpp : ℝ → ℝ := fun u => frobeniusValueDeriv2 ps 2 z₁ 1 c₀ u
  let Vppp : ℝ → ℝ := fun u => frobeniusValueDeriv3 ps 2 z₁ 1 c₀ u
  let second : ℝ → ℝ := fun u => 2 * Vp u + u * Vpp u
  let third : ℝ → ℝ := fun u => 3 * Vpp u + u * Vppp u
  have hinner : HasDerivAt
      (fun z : ℝ => Number.aperyConifoldZ1Poly - z) (-1) x := by
    simpa using (hasDerivAt_const x Number.aperyConifoldZ1Poly).sub
      (hasDerivAt_id x)
  have hVp : HasDerivAt Vp
      (Vpp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vp, Vpp, hps_def, hz_def] using
      frobeniusValueDeriv_hasDerivAt_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hVpp : HasDerivAt Vpp
      (Vppp (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    simpa [Vpp, Vppp, hps_def, hz_def] using
      frobeniusValueDeriv2_hasDerivAt_general ps 2 z₁
        1 c₀ 9 hpk' hslope'
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢; exact this)
        (fun m hm => by
          have := Number.aperyConifold_threshold_O m (by omega)
          push_cast at this ⊢; exact this)
        1000 (by norm_num) hB' s hs_pos hs_lt'
        (Number.aperyConifoldZ1Poly - x) hτ_mem
  have hthird_unshift : HasDerivAt second
      (third (Number.aperyConifoldZ1Poly - x))
      (Number.aperyConifoldZ1Poly - x) := by
    have hid : HasDerivAt (fun u : ℝ => u) 1
        (Number.aperyConifoldZ1Poly - x) := hasDerivAt_id _
    have hprod := hid.mul hVpp
    have hsum := (hVp.const_mul (2 : ℝ)).add hprod
    convert hsum using 1 <;> simp [second, third, Vpp] <;> ring
  have hthird_shift : HasDerivAt
      (fun z : ℝ => second (Number.aperyConifoldZ1Poly - z))
      (-(third (Number.aperyConifoldZ1Poly - x))) x := by
    simpa using hthird_unshift.comp x hinner
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hderiv2_ev :
      deriv (deriv (fun z : ℝ => yAperyCanonicalLeftOne c₀
        (z - Number.aperyConifoldZ1Poly))) =ᶠ[nhds x]
        (fun z : ℝ => second (Number.aperyConifoldZ1Poly - z)) := by
    filter_upwards [hmem_ev] with z hz_mem
    rw [deriv_deriv_yAperyCanonicalLeftOne_shift_eq c₀ s hs_pos hs_lt
      z hz_mem]
  have hdd := hthird_shift.congr_of_eventuallyEq hderiv2_ev
  convert hdd using 1 <;> ring

private lemma yAperyCanonicalLeftOne_state_hasDerivAt
    (c₀ : ℝ) (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_pos : 0 < x)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ =>
        (yAperyCanonicalLeftOne c₀ (z - Number.aperyConifoldZ1Poly),
          deriv (fun y : ℝ =>
            yAperyCanonicalLeftOne c₀ (y - Number.aperyConifoldZ1Poly)) z,
          deriv (deriv (fun y : ℝ =>
            yAperyCanonicalLeftOne c₀ (y - Number.aperyConifoldZ1Poly))) z))
      (aperyODEStateField x
        (yAperyCanonicalLeftOne c₀ (x - Number.aperyConifoldZ1Poly),
          deriv (fun y : ℝ =>
            yAperyCanonicalLeftOne c₀ (y - Number.aperyConifoldZ1Poly)) x,
          deriv (deriv (fun y : ℝ =>
            yAperyCanonicalLeftOne c₀ (y - Number.aperyConifoldZ1Poly))) x)) x := by
  let y : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftOne c₀ (z - Number.aperyConifoldZ1Poly)
  have hy : HasDerivAt y (deriv y x) x := by
    have h0 := hasDerivAt_yAperyCanonicalLeftOne_shift
      c₀ s hs_pos hs_lt x hτ_mem
    have h0' : HasDerivAt y
        (-(frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x)
            + (Number.aperyConifoldZ1Poly - x) *
              frobeniusValueDeriv aperyCanonicalPsSeq 2
                Number.aperyConifoldZ1Poly 1 c₀
                (Number.aperyConifoldZ1Poly - x))) x := by
      simpa [y] using h0
    convert h0' using 1
    exact h0'.deriv
  have hdy_exp :
      deriv y x =
        (-(frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x)
            + (Number.aperyConifoldZ1Poly - x) *
              frobeniusValueDeriv aperyCanonicalPsSeq 2
                Number.aperyConifoldZ1Poly 1 c₀
                (Number.aperyConifoldZ1Poly - x))) := by
    simpa [y] using (hasDerivAt_yAperyCanonicalLeftOne_shift
      c₀ s hs_pos hs_lt x hτ_mem).deriv
  have hy' : HasDerivAt (deriv y) (deriv (deriv y) x) x := by
    have h0 := hasDerivAt_deriv_yAperyCanonicalLeftOne_shift
      c₀ s hs_pos hs_lt x hτ_mem
    have h0' : HasDerivAt (deriv y)
        (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x)
          + (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x)) x := by
      simpa [y] using h0
    convert h0' using 1
    exact h0'.deriv
  have hddy_exp :
      deriv (deriv y) x =
        (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x)
          + (Number.aperyConifoldZ1Poly - x) *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 c₀
              (Number.aperyConifoldZ1Poly - x)) := by
    simpa [y] using
      deriv_deriv_yAperyCanonicalLeftOne_shift_eq c₀ s hs_pos hs_lt
        x hτ_mem
  let y3 : ℝ :=
    (-(3 * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 1 c₀
          (Number.aperyConifoldZ1Poly - x)
        + (Number.aperyConifoldZ1Poly - x) *
          frobeniusValueDeriv3 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 1 c₀
            (Number.aperyConifoldZ1Poly - x)))
  have hy'' : HasDerivAt (deriv (deriv y)) y3 x := by
    simpa [y, y3] using
      hasDerivAt_deriv_deriv_yAperyCanonicalLeftOne_shift
        c₀ s hs_pos hs_lt x hτ_mem
  have hode :
      Polynomial.eval x Number.aperyPconifold * y3
        + Polynomial.eval x Number.aperyQconifold * deriv (deriv y) x
        + Polynomial.eval x aperyRconifold * deriv y x
        + Polynomial.eval x aperySconifold * y x = 0 := by
    have hscalar := aperyCanonicalLeftOne_scalar_ode
      c₀ s x hs_pos hs_lt hτ_pos hτ_mem
    rw [hdy_exp, hddy_exp]
    simpa [y, y3, yAperyCanonicalLeftOne] using hscalar
  have hP : Polynomial.eval x Number.aperyPconifold ≠ 0 :=
    aperyPconifold_eval_ne_zero_of_pos_lt_z1 hx_pos (sub_pos.mp hτ_pos)
  simpa [y] using
    hasDerivAt_aperyODEState_of_scalar_ode
      (y := y) (y' := deriv y) (y'' := deriv (deriv y))
      hy hy' hy'' hP hode

private lemma aperyCanonicalLeftBranchState_hasDerivAt
    (a₀ a_half a₁ s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * 1000 * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (x : ℝ) (hx_pos : 0 < x)
    (hτ_pos : 0 < Number.aperyConifoldZ1Poly - x)
    (hτ_mem : Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt
      (fun z : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ z)
      (aperyODEStateField x
        (aperyCanonicalLeftBranchState a₀ a_half a₁ x)) x := by
  let S : ℝ → AperyODEState := fun z => aperyCanonicalLeftBranchState a₀ a_half a₁ z
  let S0 : ℝ → AperyODEState := fun z =>
    (yAperyCanonicalLeftZero a₀ (z - Number.aperyConifoldZ1Poly),
      deriv (fun y => yAperyCanonicalLeftZero a₀
        (y - Number.aperyConifoldZ1Poly)) z,
      deriv (deriv (fun y => yAperyCanonicalLeftZero a₀
        (y - Number.aperyConifoldZ1Poly))) z)
  let Sh : ℝ → AperyODEState := fun z =>
    (yAperyCanonicalLeftHalf a_half (z - Number.aperyConifoldZ1Poly),
      deriv (fun y => yAperyCanonicalLeftHalf a_half
        (y - Number.aperyConifoldZ1Poly)) z,
      deriv (deriv (fun y => yAperyCanonicalLeftHalf a_half
        (y - Number.aperyConifoldZ1Poly))) z)
  let S1 : ℝ → AperyODEState := fun z =>
    (yAperyCanonicalLeftOne a₁ (z - Number.aperyConifoldZ1Poly),
      deriv (fun y => yAperyCanonicalLeftOne a₁
        (y - Number.aperyConifoldZ1Poly)) z,
      deriv (deriv (fun y => yAperyCanonicalLeftOne a₁
        (y - Number.aperyConifoldZ1Poly))) z)
  let f0 : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftZero a₀ (z - Number.aperyConifoldZ1Poly)
  let fh : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftHalf a_half (z - Number.aperyConifoldZ1Poly)
  let f1 : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftOne a₁ (z - Number.aperyConifoldZ1Poly)
  let f : ℝ → ℝ := fun z =>
    aperyCanonicalLeftBranchTriple a₀ a_half a₁
      (z - Number.aperyConifoldZ1Poly)
  have hf_eq : f = fun z => f0 z + fh z + f1 z := by
    funext z
    simp [f, f0, fh, f1, aperyCanonicalLeftBranchTriple]
  have state_eq_at :
      ∀ z : ℝ,
        0 < Number.aperyConifoldZ1Poly - z →
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s →
          S z = S0 z + Sh z + S1 z := by
    intro z hzτ_pos hzτ_mem
    have h0d : DifferentiableAt ℝ f0 z := by
      simpa [f0] using
        (hasDerivAt_yAperyCanonicalLeftZero_shift
          a₀ s hs_pos hs_lt z hzτ_mem).differentiableAt
    have hhd : DifferentiableAt ℝ fh z := by
      simpa [fh] using
        (hasDerivAt_yAperyCanonicalLeftHalf_shift
          a_half s hs_pos hs_lt z hzτ_pos hzτ_mem).differentiableAt
    have h1d : DifferentiableAt ℝ f1 z := by
      simpa [f1] using
        (hasDerivAt_yAperyCanonicalLeftOne_shift
          a₁ s hs_pos hs_lt z hzτ_mem).differentiableAt
    have hderiv :
        deriv f z = deriv f0 z + deriv fh z + deriv f1 z := by
      let g : ℝ → ℝ := fun y => f0 y + fh y + f1 y
      have hg : HasDerivAt g (deriv f0 z + deriv fh z + deriv f1 z) z := by
        simpa [g, add_assoc] using
          (h0d.hasDerivAt.add hhd.hasDerivAt).add h1d.hasDerivAt
      have hf_has : HasDerivAt f (deriv f0 z + deriv fh z + deriv f1 z) z := by
        simpa [hf_eq] using hg
      exact hf_has.deriv
    have h0dd : DifferentiableAt ℝ (deriv f0) z := by
      simpa [f0] using
        (hasDerivAt_deriv_yAperyCanonicalLeftZero_shift
          a₀ s hs_pos hs_lt z hzτ_mem).differentiableAt
    have hhdd : DifferentiableAt ℝ (deriv fh) z := by
      simpa [fh] using
        (hasDerivAt_deriv_yAperyCanonicalLeftHalf_shift
          a_half s hs_pos hs_lt z hzτ_pos hzτ_mem).differentiableAt
    have h1dd : DifferentiableAt ℝ (deriv f1) z := by
      simpa [f1] using
        (hasDerivAt_deriv_yAperyCanonicalLeftOne_shift
          a₁ s hs_pos hs_lt z hzτ_mem).differentiableAt
    have hnear_pos : ∀ᶠ y in nhds z,
        0 < Number.aperyConifoldZ1Poly - y := by
      exact (isOpen_lt continuous_const
        (continuous_const.sub continuous_id)).mem_nhds hzτ_pos
    have hnear_mem : ∀ᶠ y in nhds z,
        Number.aperyConifoldZ1Poly - y ∈ Metric.ball (0 : ℝ) s := by
      have hopen : IsOpen {y : ℝ |
          Number.aperyConifoldZ1Poly - y ∈ Metric.ball (0 : ℝ) s} :=
        Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
      exact hopen.mem_nhds hzτ_mem
    have hderiv_ev :
        deriv f =ᶠ[nhds z] fun y => deriv f0 y + deriv fh y + deriv f1 y := by
      filter_upwards [hnear_pos, hnear_mem] with y hy_pos hy_mem
      have hy0 : DifferentiableAt ℝ f0 y := by
        simpa [f0] using
          (hasDerivAt_yAperyCanonicalLeftZero_shift
            a₀ s hs_pos hs_lt y hy_mem).differentiableAt
      have hyh : DifferentiableAt ℝ fh y := by
        simpa [fh] using
          (hasDerivAt_yAperyCanonicalLeftHalf_shift
            a_half s hs_pos hs_lt y hy_pos hy_mem).differentiableAt
      have hy1 : DifferentiableAt ℝ f1 y := by
        simpa [f1] using
          (hasDerivAt_yAperyCanonicalLeftOne_shift
            a₁ s hs_pos hs_lt y hy_mem).differentiableAt
      let gy : ℝ → ℝ := fun u => f0 u + fh u + f1 u
      have hgy : HasDerivAt gy (deriv f0 y + deriv fh y + deriv f1 y) y := by
        simpa [gy, add_assoc] using
          (hy0.hasDerivAt.add hyh.hasDerivAt).add hy1.hasDerivAt
      have hf_has : HasDerivAt f (deriv f0 y + deriv fh y + deriv f1 y) y := by
        simpa [hf_eq] using hgy
      exact hf_has.deriv
    have hderiv2 :
        deriv (deriv f) z =
          deriv (deriv f0) z + deriv (deriv fh) z + deriv (deriv f1) z := by
      let g : ℝ → ℝ := fun y => deriv f0 y + deriv fh y + deriv f1 y
      have hg : HasDerivAt g
          (deriv (deriv f0) z + deriv (deriv fh) z + deriv (deriv f1) z) z := by
        simpa [g] using
          (h0dd.hasDerivAt.add hhdd.hasDerivAt).add h1dd.hasDerivAt
      have hf_der : HasDerivAt (deriv f)
          (deriv (deriv f0) z + deriv (deriv fh) z + deriv (deriv f1) z) z :=
        hg.congr_of_eventuallyEq hderiv_ev
      exact hf_der.deriv
    have hz0_zero : ∀ t : ℝ, yAperyCanonicalLeftZero 0 t = 0 := by
      intro t
      have := yAperyCanonicalLeftZero_smul_c₀ 0 1 t
      simpa using this
    have hzh_zero : ∀ t : ℝ, yAperyCanonicalLeftHalf 0 t = 0 := by
      intro t
      have := yAperyCanonicalLeftHalf_smul_c₀ 0 1 t
      simpa using this
    have hz1_zero : ∀ t : ℝ, yAperyCanonicalLeftOne 0 t = 0 := by
      intro t
      have := yAperyCanonicalLeftOne_smul_c₀ 0 1 t
      simpa using this
    ext
    · simp [S, S0, Sh, S1, aperyCanonicalLeftBranchState,
        aperyCanonicalLeftBranchTriple, hz0_zero, hzh_zero, hz1_zero]
    · change deriv f z = deriv f0 z + deriv fh z + deriv f1 z
      exact hderiv
    · change deriv (deriv f) z =
        deriv (deriv f0) z + deriv (deriv fh) z + deriv (deriv f1) z
      exact hderiv2
  have h0 := yAperyCanonicalLeftZero_state_hasDerivAt
    a₀ s hs_pos hs_lt x hx_pos hτ_pos hτ_mem
  have hh := yAperyCanonicalLeftHalf_state_hasDerivAt
    a_half s hs_pos hs_lt x hx_pos hτ_pos hτ_mem
  have h1 := yAperyCanonicalLeftOne_state_hasDerivAt
    a₁ s hs_pos hs_lt x hx_pos hτ_pos hτ_mem
  have hsum : HasDerivAt (fun z : ℝ => S0 z + (Sh z + S1 z))
      (aperyODEStateField x (S0 x) +
        (aperyODEStateField x (Sh x) + aperyODEStateField x (S1 x))) x := by
    simpa [S0, Sh, S1] using h0.add (hh.add h1)
  have hx_sum : S x = S0 x + Sh x + S1 x :=
    state_eq_at x hτ_pos hτ_mem
  have hfield :
      aperyODEStateField x (S0 x) +
          (aperyODEStateField x (Sh x) + aperyODEStateField x (S1 x)) =
        aperyODEStateField x (S x) := by
    rw [hx_sum]
    ext <;> simp [aperyODEStateField] <;> ring
  have hsum' : HasDerivAt (fun z : ℝ => S0 z + (Sh z + S1 z))
      (aperyODEStateField x (S x)) x := by
    simpa [hfield] using hsum
  have hnear_pos : ∀ᶠ z in nhds x,
      0 < Number.aperyConifoldZ1Poly - z := by
    exact (isOpen_lt continuous_const
      (continuous_const.sub continuous_id)).mem_nhds hτ_pos
  have hnear_mem : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hτ_mem
  have hS_ev : S =ᶠ[nhds x] fun z => S0 z + (Sh z + S1 z) := by
    filter_upwards [hnear_pos, hnear_mem] with z hz_pos hz_mem
    simpa [add_assoc] using state_eq_at z hz_pos hz_mem
  simpa [S] using hsum'.congr_of_eventuallyEq hS_ev

private lemma aperyCanonicalBranchTriple_second_scaled_tendsto
    (a₀ a_half a₁ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          deriv (deriv
            (fun z : ℝ => aperyCanonicalBranchTriple a₀ a_half a₁
              (z - Number.aperyConifoldZ1Poly)))
            (aperyConifoldZ1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have heps : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsqrt : Filter.Tendsto (fun ε : ℝ => Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have heps_sqrt : Filter.Tendsto (fun ε : ℝ => ε * Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using heps.mul hsqrt
  have heps2 : Filter.Tendsto (fun ε : ℝ => ε ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ 2 : ℝ)) := heps.pow 2
  have hV0dd := frobeniusValueCanonicalDeriv2_tendsto_neg_zero
    0 a₀ 9
    (fun m hm => Number.aperyConifold_small_Z m (by omega))
    (fun m hm => Number.aperyConifold_large_Z m (by omega))
    (fun m hm => Number.aperyConifold_threshold_Z m (by omega))
  have hVh := frobeniusValueCanonicalHalf_tendsto_neg_zero_seed a_half
  have hVhd := frobeniusValueCanonicalHalfDeriv_tendsto_neg_zero a_half
  have hVhdd := frobeniusValueCanonicalHalfDeriv2_tendsto_neg_zero a_half
  have hV1d := frobeniusValueCanonicalDeriv_tendsto_neg_zero
    1 a₁ 9
    (fun m hm => Number.aperyConifold_small_O m (by omega))
    (fun m hm => Number.aperyConifold_large_O m (by omega))
    (fun m hm => Number.aperyConifold_threshold_O m (by omega))
  have hV1dd := frobeniusValueCanonicalDeriv2_tendsto_neg_zero
    1 a₁ 9
    (fun m hm => Number.aperyConifold_small_O m (by omega))
    (fun m hm => Number.aperyConifold_large_O m (by omega))
    (fun m hm => Number.aperyConifold_threshold_O m (by omega))
  have hmodel : Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 0 a₀ (-ε)
        - (1 / 4) *
          frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        - ε *
          frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        + ε ^ 2 *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)
        + ε * Real.sqrt ε *
          (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ (-ε)
            - ε * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ (-ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have h0term := heps_sqrt.mul hV0dd
    have hhmain := hVh.const_mul (-(1 / 4 : ℝ))
    have hhdterm := heps.mul hVhd
    have hhddterm := heps2.mul hVhdd
    have h1inner := (hV1d.const_mul (2 : ℝ)).sub (heps.mul hV1dd)
    have h1term := heps_sqrt.mul h1inner
    have hsum :=
      (((h0term.add hhmain).sub hhdterm).add hhddterm).add h1term
    convert hsum using 1
    · ext ε
      ring_nf
    · ring_nf
  refine hmodel.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_s : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < s :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hs_pos)
  filter_upwards [hev_pos, hev_s] with ε hε_pos hε_s
  let x : ℝ := aperyConifoldZ1 - ε
  have hx_neg : x - Number.aperyConifoldZ1Poly < 0 := by
    dsimp [x]
    change Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly < 0
    linarith
  have hx_mem :
      x - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [x]
    change |Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly - 0| < s
    rw [show Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly - 0 =
        -ε by ring, abs_neg, abs_of_pos hε_pos]
    exact hε_s
  let f0 : ℝ → ℝ := fun z =>
    yAperyCanonicalZero a₀ (z - Number.aperyConifoldZ1Poly)
  let fh : ℝ → ℝ := fun z =>
    yAperyCanonicalHalf a_half (z - Number.aperyConifoldZ1Poly)
  let f1 : ℝ → ℝ := fun z =>
    yAperyCanonicalOne a₁ (z - Number.aperyConifoldZ1Poly)
  let d0 : ℝ := frobeniusValueDeriv2 aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 0 a₀ (x - Number.aperyConifoldZ1Poly)
  let dh : ℝ :=
    (-(1 / (4 * (Real.sqrt (-(x - Number.aperyConifoldZ1Poly))) ^ 3)) *
      frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
        (1 / 2) a_half (x - Number.aperyConifoldZ1Poly) -
      frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
        (1 / 2) a_half (x - Number.aperyConifoldZ1Poly) /
        Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) +
      Real.sqrt (-(x - Number.aperyConifoldZ1Poly)) *
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) a_half (x - Number.aperyConifoldZ1Poly))
  let d1 : ℝ :=
    2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 1 a₁ (x - Number.aperyConifoldZ1Poly)
      + (x - Number.aperyConifoldZ1Poly) *
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 1 a₁ (x - Number.aperyConifoldZ1Poly)
  have h0 : HasDerivAt (deriv f0) d0 x := by
    simpa [f0, d0] using
      hasDerivAt_deriv_yAperyCanonicalZero_shift a₀ s hs_pos hs_lt x hx_mem
  have hh : HasDerivAt (deriv fh) dh x := by
    simpa [fh, dh] using
      hasDerivAt_deriv_yAperyCanonicalHalf_shift a_half s hs_pos hs_lt x hx_neg hx_mem
  have h1 : HasDerivAt (deriv f1) d1 x := by
    simpa [f1, d1] using
      hasDerivAt_deriv_yAperyCanonicalOne_shift a₁ s hs_pos hs_lt x hx_mem
  have hsum : HasDerivAt (fun z : ℝ => deriv f0 z + deriv fh z + deriv f1 z)
      (d0 + dh + d1) x := by
    simpa [add_assoc] using (h0.add hh).add h1
  have hneg_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly < 0 := by
    exact (isOpen_lt (continuous_id.sub continuous_const) continuous_const).mem_nhds hx_neg
  have hmem_ev : ∀ᶠ z in nhds x,
      z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        z - Number.aperyConifoldZ1Poly ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds hx_mem
  have hderiv_ev :
      deriv (fun z : ℝ => aperyCanonicalBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => deriv f0 z + deriv fh z + deriv f1 z) := by
    filter_upwards [hneg_ev, hmem_ev] with z hz_neg hz_mem
    have h0d : DifferentiableAt ℝ f0 z := by
      have hinner : HasDerivAt
          (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
        simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
      have hV := frobeniusValue_hasDerivAt_std_general
        aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 0 a₀ 9
        aperyCanonicalPsSeq_leading_eval_z1
        (by simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero)
        (fun m hm => by
          have := Number.aperyConifold_small_Z m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_Z m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          simpa [aperyCanonicalPsSeq] using Number.aperyConifold_threshold_Z m (by omega))
        1000 (by norm_num) aperyCanonical_common_B_bound
        s hs_pos hs_lt (z - Number.aperyConifoldZ1Poly) hz_mem
      simpa [f0, yAperyCanonicalLeftZero] using
        (hV.comp z hinner).differentiableAt
    have hhd : DifferentiableAt ℝ fh z := by
      have hinner : HasDerivAt
          (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
        simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
      have hV := frobeniusValue_hasDerivAt_std_general
        aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly (1 / 2) a_half 9
        aperyCanonicalPsSeq_leading_eval_z1
        (by simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero)
        aperyCanonicalHalf_small aperyCanonicalHalf_large aperyCanonicalHalf_threshold
        1000 (by norm_num) aperyCanonical_common_B_bound
        s hs_pos hs_lt (z - Number.aperyConifoldZ1Poly) hz_mem
      exact ((hasDerivAt_sqrt_neg_mul_core hz_neg hV).comp z hinner).differentiableAt
    have h1d : DifferentiableAt ℝ f1 z := by
      have hinner : HasDerivAt
          (fun y : ℝ => y - Number.aperyConifoldZ1Poly) 1 z := by
        simpa using (hasDerivAt_id z).sub_const Number.aperyConifoldZ1Poly
      have hV := frobeniusValue_hasDerivAt_std_general
        aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 1 a₁ 9
        aperyCanonicalPsSeq_leading_eval_z1
        (by simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero)
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          simpa [aperyCanonicalPsSeq] using Number.aperyConifold_threshold_O m (by omega))
        1000 (by norm_num) aperyCanonical_common_B_bound
        s hs_pos hs_lt (z - Number.aperyConifoldZ1Poly) hz_mem
      have hid : HasDerivAt (fun u : ℝ => u) 1
          (z - Number.aperyConifoldZ1Poly) := hasDerivAt_id _
      exact ((hid.mul hV).comp z hinner).differentiableAt
    change deriv (fun z : ℝ => f0 z + fh z + f1 z) z =
      deriv f0 z + deriv fh z + deriv f1 z
    have hA : deriv (fun z : ℝ => f0 z + fh z + f1 z) z =
        deriv (fun z : ℝ => f0 z + fh z) z + deriv f1 z := by
      simpa [Pi.add_apply, add_assoc] using deriv_add (h0d.add hhd) h1d
    have hB : deriv (fun z : ℝ => f0 z + fh z) z =
        deriv f0 z + deriv fh z := by
      simpa [Pi.add_apply] using deriv_add h0d hhd
    rw [hA, hB]
  have hderiv := (hsum.congr_of_eventuallyEq hderiv_ev).deriv
  rw [hderiv]
  symm
  have hsub : x - Number.aperyConifoldZ1Poly = -ε := by
    dsimp [x]
    change Number.aperyConifoldZ1Poly - ε - Number.aperyConifoldZ1Poly = -ε
    ring
  dsimp [d0, dh, d1]
  rw [hsub]
  simp only [neg_neg]
  change ε * Real.sqrt ε *
      (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 a₀ (-ε) +
        (-(1 / (4 * (Real.sqrt ε) ^ 3)) *
            frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε) -
          frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε) /
            Real.sqrt ε +
          Real.sqrt ε *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) a_half (-ε)) +
        (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ (-ε) +
          (-ε) * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ (-ε))) = _
  have hs_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
  have hs2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε_pos.le
  field_simp [hs_ne]
  rw [show (Real.sqrt ε) ^ 4 = ε ^ 2 by
    rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 by ring, hs2]]
  rw [show (Real.sqrt ε) ^ 3 = ε * Real.sqrt ε by
    rw [show (Real.sqrt ε) ^ 3 = (Real.sqrt ε) ^ 2 * Real.sqrt ε by ring, hs2]]
  rw [hs2]
  ring

private lemma aperyCanonicalLeftBranchTriple_second_scaled_tendsto
    (a₀ a_half a₁ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          deriv (deriv
            (fun z : ℝ => aperyCanonicalLeftBranchTriple a₀ a_half a₁
              (z - Number.aperyConifoldZ1Poly)))
            (aperyConifoldZ1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have heps : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsqrt : Filter.Tendsto (fun ε : ℝ => Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto Real.sqrt (nhds 0) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have heps_sqrt : Filter.Tendsto (fun ε : ℝ => ε * Real.sqrt ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using heps.mul hsqrt
  have heps2 : Filter.Tendsto (fun ε : ℝ => ε ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 ^ 2 : ℝ)) := heps.pow 2
  have hV0dd := frobeniusValueCanonicalDeriv2_tendsto_pos_zero
    0 a₀ 9
    (fun m hm => Number.aperyConifold_small_Z m (by omega))
    (fun m hm => Number.aperyConifold_large_Z m (by omega))
    (fun m hm => Number.aperyConifold_threshold_Z m (by omega))
  have hVh := frobeniusValueCanonicalHalf_tendsto_pos_zero_seed a_half
  have hVhd := frobeniusValueCanonicalHalfDeriv_tendsto_pos_zero a_half
  have hVhdd := frobeniusValueCanonicalHalfDeriv2_tendsto_pos_zero a_half
  have hV1d := frobeniusValueCanonicalDeriv_tendsto_pos_zero
    1 a₁ 9
    (fun m hm => Number.aperyConifold_small_O m (by omega))
    (fun m hm => Number.aperyConifold_large_O m (by omega))
    (fun m hm => Number.aperyConifold_threshold_O m (by omega))
  have hV1dd := frobeniusValueCanonicalDeriv2_tendsto_pos_zero
    1 a₁ 9
    (fun m hm => Number.aperyConifold_small_O m (by omega))
    (fun m hm => Number.aperyConifold_large_O m (by omega))
    (fun m hm => Number.aperyConifold_threshold_O m (by omega))
  have hmodel : Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly 0 a₀ ε
        - (1 / 4) *
          frobeniusValue aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε
        + ε *
          frobeniusValueDeriv aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε
        + ε ^ 2 *
          frobeniusValueDeriv2 aperyCanonicalPsSeq 2
            Number.aperyConifoldZ1Poly (1 / 2) a_half ε
        + ε * Real.sqrt ε *
          (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ ε
            + ε * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have h0term := heps_sqrt.mul hV0dd
    have hhmain := hVh.const_mul (-(1 / 4 : ℝ))
    have hhdterm := heps.mul hVhd
    have hhddterm := heps2.mul hVhdd
    have h1inner := (hV1d.const_mul (2 : ℝ)).add (heps.mul hV1dd)
    have h1term := heps_sqrt.mul h1inner
    have hsum :=
      (((h0term.add hhmain).add hhdterm).add hhddterm).add h1term
    convert hsum using 1
    · ext ε
      ring_nf
    · ring_nf
  refine hmodel.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_s : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < s :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hs_pos)
  filter_upwards [hev_pos, hev_s] with ε hε_pos hε_s
  let x : ℝ := aperyConifoldZ1 - ε
  have hx_tau_pos : 0 < Number.aperyConifoldZ1Poly - x := by
    dsimp [x]
    change 0 < Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε)
    linarith
  have hx_tau_mem :
      Number.aperyConifoldZ1Poly - x ∈ Metric.ball (0 : ℝ) s := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [x]
    change |Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε) - 0| < s
    rw [show Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε) - 0 =
        ε by ring, abs_of_pos hε_pos]
    exact hε_s
  let f0 : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftZero a₀ (z - Number.aperyConifoldZ1Poly)
  let fh : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftHalf a_half (z - Number.aperyConifoldZ1Poly)
  let f1 : ℝ → ℝ := fun z =>
    yAperyCanonicalLeftOne a₁ (z - Number.aperyConifoldZ1Poly)
  let d0 : ℝ := frobeniusValueDeriv2 aperyCanonicalPsSeq 2
    Number.aperyConifoldZ1Poly 0 a₀ (Number.aperyConifoldZ1Poly - x)
  let dh : ℝ :=
    (-(1 / (4 * (Real.sqrt (Number.aperyConifoldZ1Poly - x)) ^ 3)) *
      frobeniusValue aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
        (1 / 2) a_half (Number.aperyConifoldZ1Poly - x) +
      frobeniusValueDeriv aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
        (1 / 2) a_half (Number.aperyConifoldZ1Poly - x) /
        Real.sqrt (Number.aperyConifoldZ1Poly - x) +
      Real.sqrt (Number.aperyConifoldZ1Poly - x) *
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly
          (1 / 2) a_half (Number.aperyConifoldZ1Poly - x))
  let d1 : ℝ :=
    2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
        Number.aperyConifoldZ1Poly 1 a₁ (Number.aperyConifoldZ1Poly - x)
      + (Number.aperyConifoldZ1Poly - x) *
        frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 1 a₁ (Number.aperyConifoldZ1Poly - x)
  have h0 : HasDerivAt (deriv f0) d0 x := by
    simpa [f0, d0] using
      hasDerivAt_deriv_yAperyCanonicalLeftZero_shift a₀ s hs_pos hs_lt x
        hx_tau_mem
  have hh : HasDerivAt (deriv fh) dh x := by
    simpa [fh, dh] using
      hasDerivAt_deriv_yAperyCanonicalLeftHalf_shift a_half s hs_pos hs_lt x
        hx_tau_pos hx_tau_mem
  have h1 : HasDerivAt (deriv f1) d1 x := by
    simpa [f1, d1] using
      hasDerivAt_deriv_yAperyCanonicalLeftOne_shift a₁ s hs_pos hs_lt x
        hx_tau_mem
  have hsum : HasDerivAt (fun z : ℝ => deriv f0 z + deriv fh z + deriv f1 z)
      (d0 + dh + d1) x := by
    simpa [add_assoc] using (h0.add hh).add h1
  have hpos_ev : ∀ᶠ z in nhds x,
      0 < Number.aperyConifoldZ1Poly - z := by
    exact (isOpen_lt continuous_const (continuous_const.sub continuous_id)).mem_nhds hx_tau_pos
  have hmem_ev : ∀ᶠ z in nhds x,
      Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
    have hopen : IsOpen {z : ℝ |
        Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s} :=
      Metric.isOpen_ball.preimage (continuous_const.sub continuous_id)
    exact hopen.mem_nhds hx_tau_mem
  have hderiv_ev :
      deriv (fun z : ℝ => aperyCanonicalLeftBranchTriple a₀ a_half a₁
        (z - Number.aperyConifoldZ1Poly)) =ᶠ[nhds x]
        (fun z : ℝ => deriv f0 z + deriv fh z + deriv f1 z) := by
    filter_upwards [hpos_ev, hmem_ev] with z hz_pos hz_mem
    have h0d : DifferentiableAt ℝ f0 z := by
      have hinner : HasDerivAt
          (fun y : ℝ => Number.aperyConifoldZ1Poly - y) (-1) z := by
        simpa using (hasDerivAt_const z Number.aperyConifoldZ1Poly).sub
          (hasDerivAt_id z)
      have hV := frobeniusValue_hasDerivAt_std_general
        aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 0 a₀ 9
        aperyCanonicalPsSeq_leading_eval_z1
        (by simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero)
        (fun m hm => by
          have := Number.aperyConifold_small_Z m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_Z m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          simpa [aperyCanonicalPsSeq] using Number.aperyConifold_threshold_Z m (by omega))
        1000 (by norm_num) aperyCanonical_common_B_bound
        s hs_pos hs_lt (Number.aperyConifoldZ1Poly - z) hz_mem
      simpa [f0, yAperyCanonicalLeftZero] using
        (hV.comp z hinner).differentiableAt
    have hhd : DifferentiableAt ℝ fh z := by
      have hinner : HasDerivAt
          (fun y : ℝ => Number.aperyConifoldZ1Poly - y) (-1) z := by
        simpa using (hasDerivAt_const z Number.aperyConifoldZ1Poly).sub
          (hasDerivAt_id z)
      have hV := frobeniusValue_hasDerivAt_std_general
        aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly (1 / 2) a_half 9
        aperyCanonicalPsSeq_leading_eval_z1
        (by simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero)
        aperyCanonicalHalf_small aperyCanonicalHalf_large aperyCanonicalHalf_threshold
        1000 (by norm_num) aperyCanonical_common_B_bound
        s hs_pos hs_lt (Number.aperyConifoldZ1Poly - z) hz_mem
      simpa [fh, yAperyCanonicalLeftHalf] using
        ((hasDerivAt_sqrt_pos_mul_core hz_pos hV).comp z hinner).differentiableAt
    have h1d : DifferentiableAt ℝ f1 z := by
      have hinner : HasDerivAt
          (fun y : ℝ => Number.aperyConifoldZ1Poly - y) (-1) z := by
        simpa using (hasDerivAt_const z Number.aperyConifoldZ1Poly).sub
          (hasDerivAt_id z)
      have hV := frobeniusValue_hasDerivAt_std_general
        aperyCanonicalPsSeq 2 Number.aperyConifoldZ1Poly 1 a₁ 9
        aperyCanonicalPsSeq_leading_eval_z1
        (by simpa [aperyCanonicalPsSeq] using Number.aperyPconifold_deriv_eval_z1_ne_zero)
        (fun m hm => by
          have := Number.aperyConifold_small_O m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          have := Number.aperyConifold_large_O m (by omega)
          push_cast at this ⊢
          exact this)
        (fun m hm => by
          simpa [aperyCanonicalPsSeq] using Number.aperyConifold_threshold_O m (by omega))
        1000 (by norm_num) aperyCanonical_common_B_bound
        s hs_pos hs_lt (Number.aperyConifoldZ1Poly - z) hz_mem
      have hid : HasDerivAt (fun u : ℝ => u) 1
          (Number.aperyConifoldZ1Poly - z) := hasDerivAt_id _
      simpa [f1, yAperyCanonicalLeftOne] using
        ((hid.mul hV).comp z hinner).differentiableAt
    change deriv (fun z : ℝ => f0 z + fh z + f1 z) z =
      deriv f0 z + deriv fh z + deriv f1 z
    have hA : deriv (fun z : ℝ => f0 z + fh z + f1 z) z =
        deriv (fun z : ℝ => f0 z + fh z) z + deriv f1 z := by
      simpa [Pi.add_apply, add_assoc] using deriv_add (h0d.add hhd) h1d
    have hB : deriv (fun z : ℝ => f0 z + fh z) z =
        deriv f0 z + deriv fh z := by
      simpa [Pi.add_apply] using deriv_add h0d hhd
    rw [hA, hB]
  have hderiv := (hsum.congr_of_eventuallyEq hderiv_ev).deriv
  rw [hderiv]
  symm
  have hsub : Number.aperyConifoldZ1Poly - x = ε := by
    dsimp [x]
    change Number.aperyConifoldZ1Poly - (Number.aperyConifoldZ1Poly - ε) = ε
    ring
  dsimp [d0, dh, d1]
  rw [hsub]
  change ε * Real.sqrt ε *
      (frobeniusValueDeriv2 aperyCanonicalPsSeq 2
          Number.aperyConifoldZ1Poly 0 a₀ ε +
        (-(1 / (4 * (Real.sqrt ε) ^ 3)) *
            frobeniusValue aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) a_half ε +
          frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) a_half ε /
            Real.sqrt ε +
          Real.sqrt ε *
            frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly (1 / 2) a_half ε) +
        (2 * frobeniusValueDeriv aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ ε +
          ε * frobeniusValueDeriv2 aperyCanonicalPsSeq 2
              Number.aperyConifoldZ1Poly 1 a₁ ε)) = _
  have hs_ne : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε_pos).ne'
  have hs2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε_pos.le
  field_simp [hs_ne]
  rw [show (Real.sqrt ε) ^ 4 = ε ^ 2 by
    rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 by ring, hs2]]
  rw [show (Real.sqrt ε) ^ 3 = ε * Real.sqrt ε by
    rw [show (Real.sqrt ε) ^ 3 = (Real.sqrt ε) ^ 2 * Real.sqrt ε by ring, hs2]]
  rw [hs2]
  ring


/-- Positive three-halves asymptotic for `A''` on the left of the conifold. -/
def AperyASecondDerivativePositiveThreeHalvesLimit : Prop :=
  ∃ L : ℝ, 0 < L ∧
    Filter.Tendsto
      (fun ε : ℝ =>
        ε * Real.sqrt ε * aperyGFASecondReal (aperyConifoldZ1 - ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-- Transfer the nonzero half-branch connection coefficient through two
derivatives.  The model computation is
`d²/dz² (sqrt (z₁-z) * V(z-z₁)) =
  (-a_half / 4) * (z₁-z)^(-3/2) + lower-order terms`. -/
lemma aperyA_second_derivative_three_halves_asymptotic_via_frobenius
    (hconn : AperyAOrdinarySeriesHasNonzeroHalfConnection)
    (_hbirk : AperyFrobeniusBirkhoffSharpAsymptotics) :
    AperyASecondDerivativePositiveThreeHalvesLimit := by
  rcases hconn with ⟨a₀, a_half, a₁, δ, hδ_pos, hhalf_neg, hconn⟩
  refine ⟨-a_half / 4, by linarith, ?_⟩
  have hlim := aperyBranchTriple_second_scaled_tendsto a₀ a_half a₁
  refine hlim.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_δ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ_pos)
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε < Number.aperyConifoldZ1Poly :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
  filter_upwards [hev_pos, hev_δ, hev_z1] with ε hε_pos hεδ hεz
  rw [aperyGFASecondReal_eq_branchTriple_second_deriv_of_left_connection
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
    hδ_pos hε_pos hεδ hεz hconn]

/-- Canonical full-operator transfer of the half-branch connection coefficient
through two derivatives.  This is the version tied to the real Apéry ODE
`S,R,Q,P`. -/
lemma aperyA_second_derivative_three_halves_asymptotic_via_canonical_frobenius
    (hconn : AperyAOrdinarySeriesHasCanonicalNonzeroHalfConnection)
    (_hbirk : AperyFrobeniusBirkhoffSharpAsymptotics) :
    AperyASecondDerivativePositiveThreeHalvesLimit := by
  rcases hconn with ⟨a₀, a_half, a₁, δ, hδ_pos, hhalf_neg, hconn⟩
  refine ⟨-a_half / 4, by linarith, ?_⟩
  have hlim := aperyCanonicalBranchTriple_second_scaled_tendsto a₀ a_half a₁
  refine hlim.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_δ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ_pos)
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε < Number.aperyConifoldZ1Poly :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
  filter_upwards [hev_pos, hev_δ, hev_z1] with ε hε_pos hεδ hεz
  rw [aperyGFASecondReal_eq_canonicalBranchTriple_second_deriv_of_left_connection
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
    hδ_pos hε_pos hεδ hεz hconn]

/-- Coordinate-correct canonical full-operator transfer of the half-branch
connection coefficient through two derivatives.  The Frobenius coefficient
series is evaluated in `τ = z₁ - z`, matching `substLHSGen`/`taylorShift`. -/
lemma aperyA_second_derivative_three_halves_asymptotic_via_canonical_left_frobenius
    (hconn : AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection)
    (_hbirk : AperyFrobeniusBirkhoffSharpAsymptotics) :
    AperyASecondDerivativePositiveThreeHalvesLimit := by
  rcases hconn with ⟨a₀, a_half, a₁, δ, hδ_pos, hhalf_neg, hconn⟩
  refine ⟨-a_half / 4, by linarith, ?_⟩
  have hlim := aperyCanonicalLeftBranchTriple_second_scaled_tendsto a₀ a_half a₁
  refine hlim.congr' ?_
  have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev_δ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ_pos)
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε < Number.aperyConifoldZ1Poly :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
  filter_upwards [hev_pos, hev_δ, hev_z1] with ε hε_pos hεδ hεz
  rw [aperyGFASecondReal_eq_canonicalLeftBranchTriple_second_deriv_of_left_connection
    (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
    hδ_pos hε_pos hεδ hεz hconn]

/-- Any genuine left-corridor connection witness for the ordinary Apéry
`A` series has a strictly negative half-branch coefficient.

This packages the substantive sign/nonvanishing part of the connection
coefficient problem.  The proof compares the Frobenius-side limit

`ε √ε · A''(z₁-ε) → -a_half / 4`

with the coefficient-route lower bound for the same scaled second
derivative.  Thus the remaining connection-coefficient gap is only the
existence of a nontrivial left-corridor witness; once such a witness is
available, its sign is forced. -/
lemma AperyAOrdinarySeriesHasNonzeroHalfConnection.of_left_connection
    (hleft : ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧
      Ripple.Number.Frobenius.IsAperyConnectionCoeffsOn a₀ a_half a₁
        aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    AperyAOrdinarySeriesHasNonzeroHalfConnection := by
  rcases hleft with ⟨a₀, a_half, a₁, δ, hδ_pos, hconn⟩
  have hlim :
      Filter.Tendsto
        (fun ε : ℝ =>
          ε * Real.sqrt ε * aperyGFASecondReal (aperyConifoldZ1 - ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have hbranch := aperyBranchTriple_second_scaled_tendsto a₀ a_half a₁
    refine hbranch.congr' ?_
    have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
      self_mem_nhdsWithin
    have hev_δ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ_pos)
    have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
      Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε < Number.aperyConifoldZ1Poly :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
    filter_upwards [hev_pos, hev_δ, hev_z1] with ε hε_pos hεδ hεz
    rw [aperyGFASecondReal_eq_branchTriple_second_deriv_of_left_connection
      (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
      hδ_pos hε_pos hεδ hεz hconn]
  rcases aperyGFASecondReal_three_halves_lower_from_coefficients with
    ⟨K, hK_pos, δK, hδK_pos, hbound⟩
  have hev_lower : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      K ≤ ε * Real.sqrt ε *
        aperyGFASecondReal (aperyConifoldZ1 - ε) := by
    have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
      self_mem_nhdsWithin
    have hev_δK : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δK :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδK_pos)
    have hz1_pos : 0 < aperyConifoldZ1 := by
      change 0 < Number.aperyConifoldZ1Poly
      exact Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε < aperyConifoldZ1 :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
    filter_upwards [hev_pos, hev_δK, hev_z1] with ε hε_pos hεδK hεz
    have hz_pos : 0 < aperyConifoldZ1 - ε := by linarith
    have hz_lt : aperyConifoldZ1 - ε < aperyConifoldZ1 := by linarith
    have hz_near : aperyConifoldZ1 - (aperyConifoldZ1 - ε) < δK := by
      linarith
    have hb := hbound (aperyConifoldZ1 - ε) hz_pos hz_lt hz_near
    rw [show aperyConifoldZ1 - (aperyConifoldZ1 - ε) = ε by ring,
      abs_of_pos hε_pos] at hb
    exact hb
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact mem_closure_iff_nhdsWithin_neBot.mp (by
      show (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ))
      rw [closure_Ioi]
      exact Set.mem_Ici.mpr (le_refl (0 : ℝ)))
  have hK_le_limit : K ≤ -a_half / 4 :=
    ge_of_tendsto hlim hev_lower
  have hlimit_pos : 0 < -a_half / 4 :=
    lt_of_lt_of_le hK_pos hK_le_limit
  have hhalf_neg : a_half < 0 := by linarith
  exact ⟨a₀, a_half, a₁, δ, hδ_pos, hhalf_neg, hconn⟩

/-- Canonical full-operator sign forcing for any left-corridor connection
witness.  This is the non-reduced version used by the ordinary Apéry ODE. -/
lemma AperyAOrdinarySeriesHasCanonicalNonzeroHalfConnection.of_left_connection
    (hleft : ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧
      IsCanonicalAperyConnectionCoeffsOn a₀ a_half a₁
        aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    AperyAOrdinarySeriesHasCanonicalNonzeroHalfConnection := by
  rcases hleft with ⟨a₀, a_half, a₁, δ, hδ_pos, hconn⟩
  have hlim :
      Filter.Tendsto
        (fun ε : ℝ =>
          ε * Real.sqrt ε * aperyGFASecondReal (aperyConifoldZ1 - ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have hbranch := aperyCanonicalBranchTriple_second_scaled_tendsto a₀ a_half a₁
    refine hbranch.congr' ?_
    have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
      self_mem_nhdsWithin
    have hev_δ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ_pos)
    have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
      Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε < Number.aperyConifoldZ1Poly :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
    filter_upwards [hev_pos, hev_δ, hev_z1] with ε hε_pos hεδ hεz
    rw [aperyGFASecondReal_eq_canonicalBranchTriple_second_deriv_of_left_connection
      (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
      hδ_pos hε_pos hεδ hεz hconn]
  rcases aperyGFASecondReal_three_halves_lower_from_coefficients with
    ⟨K, hK_pos, δK, hδK_pos, hbound⟩
  have hev_lower : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      K ≤ ε * Real.sqrt ε *
        aperyGFASecondReal (aperyConifoldZ1 - ε) := by
    have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
      self_mem_nhdsWithin
    have hev_δK : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δK :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδK_pos)
    have hz1_pos : 0 < aperyConifoldZ1 := by
      change 0 < Number.aperyConifoldZ1Poly
      exact Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε < aperyConifoldZ1 :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
    filter_upwards [hev_pos, hev_δK, hev_z1] with ε hε_pos hεδK hεz
    have hz_pos : 0 < aperyConifoldZ1 - ε := by linarith
    have hz_lt : aperyConifoldZ1 - ε < aperyConifoldZ1 := by linarith
    have hz_near : aperyConifoldZ1 - (aperyConifoldZ1 - ε) < δK := by
      linarith
    have hb := hbound (aperyConifoldZ1 - ε) hz_pos hz_lt hz_near
    rw [show aperyConifoldZ1 - (aperyConifoldZ1 - ε) = ε by ring,
      abs_of_pos hε_pos] at hb
    exact hb
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact mem_closure_iff_nhdsWithin_neBot.mp (by
      show (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ))
      rw [closure_Ioi]
      exact Set.mem_Ici.mpr (le_refl (0 : ℝ)))
  have hK_le_limit : K ≤ -a_half / 4 :=
    ge_of_tendsto hlim hev_lower
  have hlimit_pos : 0 < -a_half / 4 :=
    lt_of_lt_of_le hK_pos hK_le_limit
  have hhalf_neg : a_half < 0 := by linarith
  exact ⟨a₀, a_half, a₁, δ, hδ_pos, hhalf_neg, hconn⟩

/-- Coordinate-correct canonical sign forcing for any left-corridor connection
witness.  This is the version aligned with the Frobenius variable
`τ = z₁ - z`. -/
lemma AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection.of_left_connection
    (hleft : ∃ a₀ a_half a₁ δ : ℝ, 0 < δ ∧
      IsCanonicalLeftAperyConnectionCoeffsOn a₀ a_half a₁
        aperyF5GFAReal (aperyConifoldLeftTInterval δ)) :
    AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection := by
  rcases hleft with ⟨a₀, a_half, a₁, δ, hδ_pos, hconn⟩
  have hlim :
      Filter.Tendsto
        (fun ε : ℝ =>
          ε * Real.sqrt ε * aperyGFASecondReal (aperyConifoldZ1 - ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-a_half / 4)) := by
    have hbranch := aperyCanonicalLeftBranchTriple_second_scaled_tendsto a₀ a_half a₁
    refine hbranch.congr' ?_
    have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
      self_mem_nhdsWithin
    have hev_δ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ_pos)
    have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
      Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε < Number.aperyConifoldZ1Poly :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
    filter_upwards [hev_pos, hev_δ, hev_z1] with ε hε_pos hεδ hεz
    rw [aperyGFASecondReal_eq_canonicalLeftBranchTriple_second_deriv_of_left_connection
      (a₀ := a₀) (a_half := a_half) (a₁ := a₁) (δ := δ)
      hδ_pos hε_pos hεδ hεz hconn]
  rcases aperyGFASecondReal_three_halves_lower_from_coefficients with
    ⟨K, hK_pos, δK, hδK_pos, hbound⟩
  have hev_lower : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      K ≤ ε * Real.sqrt ε *
        aperyGFASecondReal (aperyConifoldZ1 - ε) := by
    have hev_pos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
      self_mem_nhdsWithin
    have hev_δK : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δK :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδK_pos)
    have hz1_pos : 0 < aperyConifoldZ1 := by
      change 0 < Number.aperyConifoldZ1Poly
      exact Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
    have hev_z1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ε < aperyConifoldZ1 :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hz1_pos)
    filter_upwards [hev_pos, hev_δK, hev_z1] with ε hε_pos hεδK hεz
    have hz_pos : 0 < aperyConifoldZ1 - ε := by linarith
    have hz_lt : aperyConifoldZ1 - ε < aperyConifoldZ1 := by linarith
    have hz_near : aperyConifoldZ1 - (aperyConifoldZ1 - ε) < δK := by
      linarith
    have hb := hbound (aperyConifoldZ1 - ε) hz_pos hz_lt hz_near
    rw [show aperyConifoldZ1 - (aperyConifoldZ1 - ε) = ε by ring,
      abs_of_pos hε_pos] at hb
    exact hb
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact mem_closure_iff_nhdsWithin_neBot.mp (by
      show (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ))
      rw [closure_Ioi]
      exact Set.mem_Ici.mpr (le_refl (0 : ℝ)))
  have hK_le_limit : K ≤ -a_half / 4 :=
    ge_of_tendsto hlim hev_lower
  have hlimit_pos : 0 < -a_half / 4 :=
    lt_of_lt_of_le hK_pos hK_le_limit
  have hhalf_neg : a_half < 0 := by linarith
  exact ⟨a₀, a_half, a₁, δ, hδ_pos, hhalf_neg, hconn⟩

lemma AperyAOrdinarySeriesHasNonzeroHalfConnection.of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyBranchState a₀ a_half a₁ z₀ = Y) :
    AperyAOrdinarySeriesHasNonzeroHalfConnection := by
  exact Ripple.Number.AperyAOrdinarySeriesHasNonzeroHalfConnection.of_left_connection
    (apery_left_connection_exists_of_branch_state_surjective
      hδ_pos hδ_lt_z1 hz₀ hbranch hsurj)

lemma AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection.of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = Y) :
    AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection := by
  exact
    Ripple.Number.AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection.of_left_connection
      (apery_left_canonical_left_connection_exists_of_branch_state_surjective
        hδ_pos hδ_lt_z1 hz₀ hbranch hsurj)

/-- A positive left-limit for `(z₁-z)^(3/2) A''(z)` gives the required
eventual lower bound. -/
lemma aperyGFASecondReal_three_halves_lower_of_positive_limit
    (hlim : AperyASecondDerivativePositiveThreeHalvesLimit) :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  rcases hlim with ⟨L, hL_pos, hlim⟩
  refine ⟨L / 2, half_pos hL_pos, ?_⟩
  have htarget :
      Set.Ioi (L / 2) ∈ nhds L := by
    exact IsOpen.mem_nhds isOpen_Ioi (show L / 2 < L by linarith)
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      L / 2 <
        ε * Real.sqrt ε *
          aperyGFASecondReal (aperyConifoldZ1 - ε) :=
    hlim htarget
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro z hz_pos hz_lt hz_near
  have hε_pos : 0 < aperyConifoldZ1 - z := sub_pos.mpr hz_lt
  have hdist : dist (aperyConifoldZ1 - z) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos]
    exact hz_near
  have hmain := hδ hdist hε_pos
  rw [show aperyConifoldZ1 - (aperyConifoldZ1 - z) = z by ring] at hmain
  calc
    L / 2
        ≤ (aperyConifoldZ1 - z) * Real.sqrt (aperyConifoldZ1 - z) *
            aperyGFASecondReal z := le_of_lt hmain
    _ = |aperyConifoldZ1 - z| *
          Real.sqrt |aperyConifoldZ1 - z| * aperyGFASecondReal z := by
        rw [abs_of_pos hε_pos]

theorem aperyGFASecondReal_three_halves_lower_via_frobenius_of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyBranchState a₀ a_half a₁ z₀ = Y) :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  have hconn :=
    Ripple.Number.AperyAOrdinarySeriesHasNonzeroHalfConnection.of_branch_state_surjective
      hδ_pos hδ_lt_z1 hz₀ hbranch hsurj
  have hbirk := aperyFrobeniusRatioFamilyCoefficientControl_and_birkhoffSharpAsymptotics.2
  exact aperyGFASecondReal_three_halves_lower_of_positive_limit
    (aperyA_second_derivative_three_halves_asymptotic_via_frobenius
      hconn hbirk)

theorem aperyGFASecondReal_three_halves_lower_via_canonical_left_frobenius_of_branch_state_surjective
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z)
    (hsurj : ∀ Y : AperyODEState,
      ∃ a₀ a_half a₁ : ℝ, aperyCanonicalLeftBranchState a₀ a_half a₁ z₀ = Y) :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  have hconn :=
    Ripple.Number.AperyAOrdinarySeriesHasCanonicalLeftNonzeroHalfConnection.of_branch_state_surjective
      hδ_pos hδ_lt_z1 hz₀ hbranch hsurj
  have hbirk := aperyFrobeniusRatioFamilyCoefficientControl_and_birkhoffSharpAsymptotics.2
  exact aperyGFASecondReal_three_halves_lower_of_positive_limit
    (aperyA_second_derivative_three_halves_asymptotic_via_canonical_left_frobenius
      hconn hbirk)

theorem aperyGFASecondReal_three_halves_lower_via_canonical_left_frobenius_of_branch_ode
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyCanonicalLeftBranchState a₀ a_half a₁ x)
          (aperyODEStateField z
            (aperyCanonicalLeftBranchState a₀ a_half a₁ z)) z) :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  exact
    aperyGFASecondReal_three_halves_lower_via_canonical_left_frobenius_of_branch_state_surjective
      hδ_pos hδ_lt_z1 hz₀ hbranch
      (aperyCanonicalLeftBranchState_surjective_of_branch_ode
        hδ_pos hδ_lt_z1 hz₀ hbranch)

theorem aperyGFASecondReal_three_halves_lower_via_frobenius_of_branch_ode
    {δ z₀ : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly)
    (hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly)
    (hbranch : ∀ a₀ a_half a₁ z,
      z ∈ Set.Ioo (Number.aperyConifoldZ1Poly - δ)
          Number.aperyConifoldZ1Poly →
        HasDerivAt
          (fun x : ℝ => aperyBranchState a₀ a_half a₁ x)
          (aperyODEStateField z (aperyBranchState a₀ a_half a₁ z)) z) :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  exact aperyGFASecondReal_three_halves_lower_via_frobenius_of_branch_state_surjective
    hδ_pos hδ_lt_z1 hz₀ hbranch
    (aperyBranchState_surjective_of_branch_ode
      hδ_pos hδ_lt_z1 hz₀ hbranch)

/-- Phase 4 bridge: the sharp denominator lower bound follows from the
Frobenius half-branch connection coefficient and its differentiated
three-halves asymptotic. -/
theorem aperyGFASecondReal_three_halves_lower_via_frobenius :
    AperyGFASecondRealThreeHalvesLowerNearConifold := by
  rcases aperyCanonical_local_radius_exists with ⟨s, hs_pos, hs_lt⟩
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly :=
    Ripple.Number.Frobenius.aperyConifoldZ1Poly_pos
  let δ : ℝ := min (s / 2) (Number.aperyConifoldZ1Poly / 2)
  have hδ_pos : 0 < δ := by
    exact lt_min (half_pos hs_pos) (half_pos hz1_pos)
  have hδ_lt_s : δ < s := by
    exact lt_of_le_of_lt (min_le_left _ _)
      (half_lt_self hs_pos)
  have hδ_lt_z1 : δ < Number.aperyConifoldZ1Poly := by
    exact lt_of_le_of_lt (min_le_right _ _)
      (half_lt_self hz1_pos)
  let z₀ : ℝ := Number.aperyConifoldZ1Poly - δ / 2
  have hz₀ : z₀ ∈
      Set.Ioo (Number.aperyConifoldZ1Poly - δ)
        Number.aperyConifoldZ1Poly := by
    constructor <;> dsimp [z₀]
    · linarith [half_pos hδ_pos]
    · linarith [half_pos hδ_pos]
  exact
    aperyGFASecondReal_three_halves_lower_via_canonical_left_frobenius_of_branch_ode
      hδ_pos hδ_lt_z1 hz₀
      (by
        intro a₀ a_half a₁ z hz
        have hz_pos : 0 < z := by
          have hleft_pos : 0 < Number.aperyConifoldZ1Poly - δ :=
            sub_pos.mpr hδ_lt_z1
          exact lt_trans hleft_pos hz.1
        have hτ_pos : 0 < Number.aperyConifoldZ1Poly - z :=
          sub_pos.mpr hz.2
        have hτ_lt_δ : Number.aperyConifoldZ1Poly - z < δ := by
          linarith [hz.1]
        have hτ_mem :
            Number.aperyConifoldZ1Poly - z ∈ Metric.ball (0 : ℝ) s := by
          rw [Metric.mem_ball, Real.dist_eq]
          rw [sub_zero]
          rw [abs_of_pos hτ_pos]
          exact lt_trans hτ_lt_δ hδ_lt_s
        exact aperyCanonicalLeftBranchState_hasDerivAt
          a₀ a_half a₁ s hs_pos hs_lt z hz_pos hτ_pos hτ_mem)

end Ripple.Number
