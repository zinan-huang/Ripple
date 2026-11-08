import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Polynomial
import Ripple.Number.Frobenius.Falling

/-!
# Frobenius framework — polynomial change-of-variable at a regular singular point

This file sets up the change-of-variable tools used by the Frobenius
substitution. Given a linear ODE with polynomial coefficients
`p₀, …, p_k : ℝ[z]` and a target point `z₁ : ℝ`, the change `z = z₁ - t`
turns each `pⱼ(z)` into a polynomial `p̃ⱼ(t) := pⱼ(z₁ - t)` in `t`. The
coefficients of `p̃ⱼ(t)` at `t = 0` are exactly the values of `pⱼ` and
its derivatives at `z₁` (up to sign).

The file provides:

* `taylorShift p z₁`: the polynomial `p(z₁ - t)` in `t`.
* `taylorShift_eval_zero`: `(taylorShift p z₁).eval 0 = p.eval z₁`.
* `taylorShift_deriv_eval_zero`: the `t`-derivative of `taylorShift p z₁`
  at `t = 0` is `-(Polynomial.derivative p).eval z₁` (the sign from the
  `-1` in `z = z₁ - t`).

These match the concrete `aperyPconifold_eval_z1` and
`aperyPconifold_deriv_eval_z1` identities used in the Apéry file, and
will be the bridge between polynomial ODE coefficients and the leading
coefficients `b_j` fed into `indicialPolyFalling` in the full Frobenius
substitution theorem.
-/

namespace Ripple
namespace Number.Frobenius

open Polynomial

/-- Change of variable `z = z₁ - t`: `taylorShift p z₁` is the polynomial
`p(z₁ - t)` viewed as a polynomial in `t`. -/
noncomputable def taylorShift (p : Polynomial ℝ) (z₁ : ℝ) : Polynomial ℝ :=
  p.comp (C z₁ - X)

@[simp] lemma taylorShift_eval_zero (p : Polynomial ℝ) (z₁ : ℝ) :
    (taylorShift p z₁).eval 0 = p.eval z₁ := by
  simp [taylorShift]

@[simp] lemma taylorShift_C (c z₁ : ℝ) :
    taylorShift (C c) z₁ = C c := by
  simp [taylorShift]

@[simp] lemma taylorShift_X (z₁ : ℝ) :
    taylorShift X z₁ = C z₁ - X := by
  simp [taylorShift]

@[simp] lemma taylorShift_zero (z₁ : ℝ) :
    taylorShift 0 z₁ = 0 := by
  simp [taylorShift]

lemma taylorShift_add (p q : Polynomial ℝ) (z₁ : ℝ) :
    taylorShift (p + q) z₁ = taylorShift p z₁ + taylorShift q z₁ := by
  simp [taylorShift, add_comp]

lemma taylorShift_mul (p q : Polynomial ℝ) (z₁ : ℝ) :
    taylorShift (p * q) z₁ = taylorShift p z₁ * taylorShift q z₁ := by
  simp [taylorShift, mul_comp]

/-- `natDegree (taylorShift p z₁) ≤ natDegree p`. The substitution
`z = z₁ - t` is linear in `t`, so its composition into `p` cannot
raise the degree. -/
lemma taylorShift_natDegree_le (p : Polynomial ℝ) (z₁ : ℝ) :
    (taylorShift p z₁).natDegree ≤ p.natDegree := by
  unfold taylorShift
  by_cases hp : p = 0
  · simp [hp]
  refine (Polynomial.natDegree_comp_le).trans ?_
  have hlin : (C z₁ - X : Polynomial ℝ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
  calc p.natDegree * (C z₁ - X : Polynomial ℝ).natDegree
      ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hlin
    _ = p.natDegree := Nat.mul_one _

/-- For `ℓ > natDegree p`, the `ℓ`-th coefficient of `taylorShift p z₁`
is zero. -/
lemma taylorShift_coeff_eq_zero_of_natDegree_lt
    (p : Polynomial ℝ) (z₁ : ℝ) (ℓ : ℕ) (hℓ : p.natDegree < ℓ) :
    Polynomial.coeff (taylorShift p z₁) ℓ = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (taylorShift_natDegree_le p z₁) hℓ)

/-- The constant coefficient of `taylorShift p z₁` equals `p.eval z₁`. -/
lemma taylorShift_coeff_zero (p : Polynomial ℝ) (z₁ : ℝ) :
    Polynomial.coeff (taylorShift p z₁) 0 = p.eval z₁ := by
  rw [Polynomial.coeff_zero_eq_eval_zero, taylorShift_eval_zero]



/-- The `t`-derivative of `taylorShift p z₁` at `t = 0` equals
`-p'(z₁)`. The sign comes from the Jacobian `dz/dt = -1` of the
change of variable `z = z₁ - t`. -/
@[simp] lemma taylorShift_derivative_eval_zero (p : Polynomial ℝ) (z₁ : ℝ) :
    (Polynomial.derivative (taylorShift p z₁)).eval 0 =
      - (Polynomial.derivative p).eval z₁ := by
  simp [taylorShift, derivative_comp]

/-- The first-order coefficient of `taylorShift p z₁` equals `-p'(z₁)`.
The sign comes from the Jacobian `dz/dt = −1` of the change of variable
`z = z₁ − t`. -/
lemma taylorShift_coeff_one (p : Polynomial ℝ) (z₁ : ℝ) :
    Polynomial.coeff (taylorShift p z₁) 1 =
      - (Polynomial.derivative p).eval z₁ := by
  have h1 : Polynomial.coeff (taylorShift p z₁) 1 =
      Polynomial.coeff (Polynomial.derivative (taylorShift p z₁)) 0 := by
    rw [Polynomial.coeff_derivative]
    ring
  rw [h1, Polynomial.coeff_zero_eq_eval_zero,
      taylorShift_derivative_eval_zero]

/-- The second-order coefficient of `taylorShift p z₁` equals
`p''(z₁) / 2`. The factor `(-1)^2 = 1` from the Jacobian cancels out. -/
lemma taylorShift_coeff_two (p : Polynomial ℝ) (z₁ : ℝ) :
    Polynomial.coeff (taylorShift p z₁) 2 =
      (Polynomial.derivative (Polynomial.derivative p)).eval z₁ / 2 := by
  have h_eval :
      (Polynomial.derivative (Polynomial.derivative (taylorShift p z₁))).eval 0
        = (Polynomial.derivative (Polynomial.derivative p)).eval z₁ := by
    simp [taylorShift, Polynomial.derivative_comp]
  have e1 :
      Polynomial.coeff
          (Polynomial.derivative (Polynomial.derivative (taylorShift p z₁))) 0
        = Polynomial.coeff (taylorShift p z₁) 2 * 2 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    push_cast; ring
  rw [Polynomial.coeff_zero_eq_eval_zero] at e1
  rw [h_eval] at e1
  linarith

/-- The third-order coefficient of `taylorShift p z₁` equals
`-p'''(z₁) / 6`. The factor `(-1)^3 = -1` from the Jacobian gives the
overall sign. -/
lemma taylorShift_coeff_three (p : Polynomial ℝ) (z₁ : ℝ) :
    Polynomial.coeff (taylorShift p z₁) 3 =
      - (Polynomial.derivative (Polynomial.derivative
          (Polynomial.derivative p))).eval z₁ / 6 := by
  have h_eval :
      (Polynomial.derivative (Polynomial.derivative
          (Polynomial.derivative (taylorShift p z₁)))).eval 0
        = - (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative p))).eval z₁ := by
    simp [taylorShift, Polynomial.derivative_comp]
  have e1 :
      Polynomial.coeff
          (Polynomial.derivative (Polynomial.derivative
              (Polynomial.derivative (taylorShift p z₁)))) 0
        = Polynomial.coeff (taylorShift p z₁) 3 * 6 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative,
        Polynomial.coeff_derivative]
    push_cast; ring
  rw [Polynomial.coeff_zero_eq_eval_zero] at e1
  rw [h_eval] at e1
  linarith

/-- The fourth-order coefficient of `taylorShift p z₁` equals
`p''''(z₁) / 24`. The factor `(-1)^4 = 1` from the Jacobian cancels out. -/
lemma taylorShift_coeff_four (p : Polynomial ℝ) (z₁ : ℝ) :
    Polynomial.coeff (taylorShift p z₁) 4 =
      (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
          (Polynomial.derivative p)))).eval z₁ / 24 := by
  have h_eval :
      (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
          (Polynomial.derivative (taylorShift p z₁))))).eval 0
        = (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative p)))).eval z₁ := by
    simp [taylorShift, Polynomial.derivative_comp]
  have e1 :
      Polynomial.coeff
          (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
              (Polynomial.derivative (taylorShift p z₁))))) 0
        = Polynomial.coeff (taylorShift p z₁) 4 * 24 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative,
        Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    push_cast; ring
  rw [Polynomial.coeff_zero_eq_eval_zero] at e1
  rw [h_eval] at e1
  linarith

/-- Leading real coefficients at `t = 0` for a polynomial ODE coefficient
at the singular point `z = z₁`. Used to construct the `bs`-sequence that
feeds `indicialPolyFalling`. -/
noncomputable def leadingAtSingular (p : Polynomial ℝ) (z₁ : ℝ) : ℝ :=
  p.eval z₁

/-- Apéry-pattern Frobenius coefficient extraction. Given order-3 ODE
coefficients `p_0, p_1, p_2, p_3 : ℝ[z]` and singular point `z₁`, with
`p_3(z₁) = 0` (simple zero of leading coefficient), the `bs`-sequence
for the indicial polynomial is

```
bs 0 = 0,  bs 1 = 0,
bs 2 = p_2(z₁),
bs 3 = p_3'(z₁).
```

(Lower-order `p_1, p_0` do not contribute to the leading `t^{ρ-2}`
balance when `p_3` has a simple zero and `p_2(z₁) ≠ 0`; cf. the Apéry
conifold case.) -/
noncomputable def aperyPatternFallingCoeffs
    (p2 p3 : Polynomial ℝ) (z₁ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => p2.eval z₁
  | 3 => (Polynomial.derivative p3).eval z₁
  | _ + 4 => 0

@[simp] lemma aperyPatternFallingCoeffs_zero (p2 p3 : Polynomial ℝ) (z₁ : ℝ) :
    aperyPatternFallingCoeffs p2 p3 z₁ 0 = 0 := rfl

@[simp] lemma aperyPatternFallingCoeffs_two (p2 p3 : Polynomial ℝ) (z₁ : ℝ) :
    aperyPatternFallingCoeffs p2 p3 z₁ 2 = p2.eval z₁ := rfl

@[simp] lemma aperyPatternFallingCoeffs_three (p2 p3 : Polynomial ℝ) (z₁ : ℝ) :
    aperyPatternFallingCoeffs p2 p3 z₁ 3 =
      (Polynomial.derivative p3).eval z₁ := rfl

/-- Indicial polynomial at a simple-zero conifold: the general order-3
formula `P(ρ) = p_3'(z₁) · ρ^{(3)} + p_2(z₁) · ρ^{(2)}`.

This is the formula that the substitution theorem (TODO) will pick out
as the leading-order balance. -/
noncomputable def aperyPatternIndicialPoly
    (p2 p3 : Polynomial ℝ) (z₁ ρ : ℝ) : ℝ :=
  indicialPolyFalling (aperyPatternFallingCoeffs p2 p3 z₁) 3 ρ

lemma aperyPatternIndicialPoly_eq
    (p2 p3 : Polynomial ℝ) (z₁ ρ : ℝ) :
    aperyPatternIndicialPoly p2 p3 z₁ ρ =
      (Polynomial.derivative p3).eval z₁ * (ρ * (ρ - 1) * (ρ - 2)) +
      p2.eval z₁ * (ρ * (ρ - 1)) := by
  unfold aperyPatternIndicialPoly indicialPolyFalling
  rw [show (3 + 1 : ℕ) = 4 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
  simp [fallingFactorial, aperyPatternFallingCoeffs]
  ring

/-! ## Formal substitution bridge

For a third-order linear ODE `p_0 y + p_1 y' + p_2 y'' + p_3 y''' = 0`
at a regular singular point `z = z₁` with simple zero `p_3(z₁) = 0`
(Apéry pattern), substituting `y = t^ρ g(t)` with `t = z₁ - z` and
multiplying by `t^{3-ρ}` produces (algebraically, on the `g`-series)

```
substLHS =  X^3 · (taylorShift p_0) · g
          - X^2 · (taylorShift p_1) · F¹g
          + X   · (taylorShift p_2) · F²g
          -      (taylorShift p_3) · F³g
```

(signs from the Jacobian `d/dz = -d/dt`). The theorem
`coeff_one_substLHS` then identifies the `t^{ρ-2}` leading-order balance
with `aperyPatternIndicialPoly p_2 p_3 z₁ ρ · g(0)`. -/

open PowerSeries in
/-- Formal substitution `z = z₁ - t`, ansatz `y = t^ρ g(t)`, in an
order-3 linear ODE `Σ_j p_j(z) y^{(j)}(z) = 0`, scaled by `t^{3-ρ}`.
Produced entirely algebraically on the `g`-series (no `t^ρ` needed). -/
noncomputable def substLHS
    (p0 p1 p2 p3 : Polynomial ℝ) (z₁ ρ : ℝ) (g : PowerSeries ℝ) :
    PowerSeries ℝ :=
  ((X : PowerSeries ℝ) ^ 3) * ((taylorShift p0 z₁ : Polynomial ℝ) : PowerSeries ℝ)
      * fallingEulerOp ρ 0 g
  - ((X : PowerSeries ℝ) ^ 2) * ((taylorShift p1 z₁ : Polynomial ℝ) : PowerSeries ℝ)
      * fallingEulerOp ρ 1 g
  + (X : PowerSeries ℝ) * ((taylorShift p2 z₁ : Polynomial ℝ) : PowerSeries ℝ)
      * fallingEulerOp ρ 2 g
  - ((taylorShift p3 z₁ : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp ρ 3 g

open PowerSeries in
/-- Constant coefficient of `taylorShift p z₁` as a power series: `p(z₁)`. -/
@[simp] lemma coeff_zero_taylorShift_coe (p : Polynomial ℝ) (z₁ : ℝ) :
    coeff (R := ℝ) 0 ((taylorShift p z₁ : Polynomial ℝ) : PowerSeries ℝ) =
      p.eval z₁ := by
  rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  exact taylorShift_eval_zero p z₁

open PowerSeries in
/-- Linear coefficient of `taylorShift p z₁` as a power series:
`-p'(z₁)` (sign from `dz/dt = -1`). -/
@[simp] lemma coeff_one_taylorShift_coe (p : Polynomial ℝ) (z₁ : ℝ) :
    coeff (R := ℝ) 1 ((taylorShift p z₁ : Polynomial ℝ) : PowerSeries ℝ) =
      - (Polynomial.derivative p).eval z₁ := by
  rw [Polynomial.coeff_coe]
  have h := taylorShift_derivative_eval_zero p z₁
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h
  have hc : Polynomial.coeff (Polynomial.derivative (taylorShift p z₁)) 0
          = Polynomial.coeff (taylorShift p z₁) 1 := by
    rw [Polynomial.coeff_derivative]; push_cast; ring
  linarith

open PowerSeries in
/-- `coeff 0 (A * B) = coeff 0 A * coeff 0 B` for power series. -/
lemma coeff_zero_mul (A B : PowerSeries ℝ) :
    coeff (R := ℝ) 0 (A * B) =
      coeff (R := ℝ) 0 A * coeff (R := ℝ) 0 B := by
  have := PowerSeries.coeff_mul 0 A B
  rw [this]
  have hant : (Finset.antidiagonal (0 : ℕ)) = {(0, 0)} := rfl
  rw [hant, Finset.sum_singleton]

open PowerSeries in
/-- `coeff 1 (A * B) = A₀·B₁ + A₁·B₀` for power series. -/
lemma coeff_one_mul (A B : PowerSeries ℝ) :
    coeff (R := ℝ) 1 (A * B) =
      coeff (R := ℝ) 0 A * coeff (R := ℝ) 1 B
        + coeff (R := ℝ) 1 A * coeff (R := ℝ) 0 B := by
  have := PowerSeries.coeff_mul 1 A B
  rw [this]
  have hant : (Finset.antidiagonal (1 : ℕ)) = {(0, 1), (1, 0)} := rfl
  rw [hant]
  simp [Finset.sum_insert, Finset.sum_singleton]

open PowerSeries in
/-- **Substitution bridge.** For the Apéry-pattern order-3 ODE (simple
zero `p_3(z₁) = 0`), the `t^{ρ-2}` coefficient of the formal
substitution equals `aperyPatternIndicialPoly · g(0)`. -/
theorem coeff_one_substLHS
    (p0 p1 p2 p3 : Polynomial ℝ) (z₁ ρ : ℝ) (g : PowerSeries ℝ)
    (hp3 : p3.eval z₁ = 0) :
    coeff (R := ℝ) 1 (substLHS p0 p1 p2 p3 z₁ ρ g) =
      aperyPatternIndicialPoly p2 p3 z₁ ρ * coeff (R := ℝ) 0 g := by
  -- Abbreviations for the four polynomial factors as series.
  set A0 : PowerSeries ℝ := ((taylorShift p0 z₁ : Polynomial ℝ) : PowerSeries ℝ) with hA0def
  set A1 : PowerSeries ℝ := ((taylorShift p1 z₁ : Polynomial ℝ) : PowerSeries ℝ) with hA1def
  set A2 : PowerSeries ℝ := ((taylorShift p2 z₁ : Polynomial ℝ) : PowerSeries ℝ) with hA2def
  set A3 : PowerSeries ℝ := ((taylorShift p3 z₁ : Polynomial ℝ) : PowerSeries ℝ) with hA3def
  -- Rewrite substLHS so that each X^k factor is grouped on the left.
  have hsubst :
      substLHS p0 p1 p2 p3 z₁ ρ g
        = (X : PowerSeries ℝ) ^ 3 * (A0 * fallingEulerOp ρ 0 g)
          - (X : PowerSeries ℝ) ^ 2 * (A1 * fallingEulerOp ρ 1 g)
          + (X : PowerSeries ℝ) * (A2 * fallingEulerOp ρ 2 g)
          - A3 * fallingEulerOp ρ 3 g := by
    simp [substLHS, hA0def, hA1def, hA2def, hA3def, mul_assoc]
  rw [hsubst]
  simp only [map_add, map_sub]
  -- The X^3 term: coefficient at index 1 is 0 (3 > 1).
  have h3 : coeff (R := ℝ) 1
      ((X : PowerSeries ℝ) ^ 3 * (A0 * fallingEulerOp ρ 0 g)) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul']; simp
  -- The X^2 term: coefficient at index 1 is 0 (2 > 1).
  have h2 : coeff (R := ℝ) 1
      ((X : PowerSeries ℝ) ^ 2 * (A1 * fallingEulerOp ρ 1 g)) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul']; simp
  -- The X term: coeff 1 (X * φ) = coeff 0 φ.
  have h1 : coeff (R := ℝ) 1
      ((X : PowerSeries ℝ) * (A2 * fallingEulerOp ρ 2 g))
        = coeff (R := ℝ) 0 (A2 * fallingEulerOp ρ 2 g) := by
    simp [PowerSeries.coeff_succ_X_mul (R := ℝ) 0 (A2 * fallingEulerOp ρ 2 g)]
  rw [h3, h2, h1]
  -- Expand the two remaining mul-coefficients.
  rw [coeff_zero_mul A2 (fallingEulerOp ρ 2 g),
      coeff_one_mul A3 (fallingEulerOp ρ 3 g)]
  -- Taylor-shift coefficients and falling-Euler coefficients.
  rw [hA2def, hA3def, coeff_zero_taylorShift_coe, coeff_zero_taylorShift_coe,
      coeff_one_taylorShift_coe, hp3,
      coeff_zero_fallingEulerOp, coeff_zero_fallingEulerOp,
      coeff_fallingEulerOp]
  -- Match the indicial polynomial.
  rw [aperyPatternIndicialPoly_eq]
  simp [fallingFactorial]
  ring

/-! ## General-order substitution (STRATEGY.md Step 2) -/

open PowerSeries in
/-- General-order formal substitution `z = z₁ - t`, ansatz `y = t^ρ g(t)`,
in an order-`k` linear ODE `Σ_{j=0}^{k} p_j(z) y^{(j)}(z) = 0`, scaled by
`t^{k−ρ}`. Alternating sign comes from the Jacobian `dz/dt = -1`. -/
noncomputable def substLHSGen
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ : ℝ) (g : PowerSeries ℝ) :
    PowerSeries ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    ((-1 : ℝ) ^ j) •
      ((X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
        * fallingEulerOp ρ j g)

open PowerSeries in
/-- For `m ≥ 2`, any `(c • (X^m * φ))` has zero coefficient at index 1. -/
private lemma coeff_one_smul_X_pow_mul_ge
    (c : ℝ) (m : ℕ) (hm : 2 ≤ m) (φ : PowerSeries ℝ) :
    coeff (R := ℝ) 1 (c • ((X : PowerSeries ℝ) ^ m * φ)) = 0 := by
  rw [map_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · exfalso; omega
  · simp

open PowerSeries in
/-- **General-order substitution bridge** (STRATEGY.md Step 2).

For an order-`(n+1)` linear ODE `Σ_{j=0}^{n+1} p_j(z) y^{(j)}(z) = 0`
at a regular singular point with simple zero `p_{n+1}(z₁) = 0`, the
leading-order balance `coeff 1` of the scaled substitution is

```
(-1)^n · (p_n(z₁) · ρ^(n) + p_{n+1}'(z₁) · ρ^(n+1)) · g(0).
```

This generalizes `coeff_one_substLHS` (the Apéry-pattern order-3 case,
`n = 2`) to arbitrary order. Only the top two coefficients `p_n, p_{n+1}`
contribute at leading order — this is the universal simple-zero pattern. -/
theorem coeff_one_substLHSGen
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (g : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) 1 (substLHSGen ps (n + 1) z₁ ρ g) =
      ((-1 : ℝ) ^ n) *
        ((ps n).eval z₁ * fallingFactorial ρ n +
         (Polynomial.derivative (ps (n + 1))).eval z₁ * fallingFactorial ρ (n + 1)) *
        coeff (R := ℝ) 0 g := by
  unfold substLHSGen
  rw [map_sum]
  -- Range (n+2) = Range (n+1) ∪ {n+1}; Range (n+1) = Range n ∪ {n}.
  rw [show (n + 1 + 1 : ℕ) = n + 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_succ]
  -- The Σ_{j < n} summand vanishes because n+1-j ≥ 2.
  have hsum_lt :
      ∀ j ∈ Finset.range n,
        coeff (R := ℝ) 1 (((-1 : ℝ) ^ j) •
          ((X : PowerSeries ℝ) ^ (n + 1 - j) *
            ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ) *
            fallingEulerOp ρ j g)) = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hle : 2 ≤ n + 1 - j := by omega
    rw [mul_assoc]
    exact coeff_one_smul_X_pow_mul_ge _ _ hle _
  rw [Finset.sum_congr rfl hsum_lt]
  rw [Finset.sum_const_zero, zero_add]
  -- j = n term: X^(1) = X
  have hn1 : (n + 1 - n : ℕ) = 1 := by omega
  rw [hn1, pow_one]
  -- j = n+1 term: X^(0) = 1
  have hnn : (n + 1 - (n + 1) : ℕ) = 0 := by omega
  rw [hnn, pow_zero, one_mul]
  -- Expand coeff 1 on both remaining summands.
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  -- Middle term: coeff 1 (X * A_n * F^n g) = coeff 0 (A_n * F^n g)
  have hX :
      coeff (R := ℝ) 1
        ((X : PowerSeries ℝ) *
          (((taylorShift (ps n) z₁ : Polynomial ℝ) : PowerSeries ℝ) *
            fallingEulerOp ρ n g)) =
        coeff (R := ℝ) 0
          (((taylorShift (ps n) z₁ : Polynomial ℝ) : PowerSeries ℝ) *
            fallingEulerOp ρ n g) := by
    simp [coeff_succ_X_mul (R := ℝ) 0
      (((taylorShift (ps n) z₁ : Polynomial ℝ) : PowerSeries ℝ) *
        fallingEulerOp ρ n g)]
  rw [mul_assoc ((X : PowerSeries ℝ)), hX]
  -- Expand the two resulting mul-coefficients.
  rw [coeff_zero_mul, coeff_one_mul]
  rw [coeff_zero_taylorShift_coe, coeff_zero_taylorShift_coe,
      coeff_one_taylorShift_coe, hpk,
      coeff_zero_fallingEulerOp, coeff_zero_fallingEulerOp,
      coeff_fallingEulerOp]
  -- The p_{n+1}(z₁) = 0 term and the pow (n+1) sign match.
  have hsign : ((-1 : ℝ) ^ (n + 1)) = -((-1 : ℝ) ^ n) := by
    rw [pow_succ]; ring
  rw [hsign]
  ring

/-! ## General-order simple-zero indicial polynomial -/

/-- Indicial polynomial for an order-`(n+1)` linear ODE with a simple
zero of the leading coefficient at `z₁`. Falling-factorial basis:

```
P(ρ) = p_n(z₁) · ρ^(n) + p_{n+1}'(z₁) · ρ^(n+1).
```

Generalizes `aperyPatternIndicialPoly` (the Apéry-pattern order-3 case
`n = 2`). Whenever `p_{n+1}(z₁) = 0` simply, this is the polynomial
whose roots give the admissible Frobenius exponents ρ. -/
noncomputable def simpleZeroIndicialPoly
    (pn pn1 : Polynomial ℝ) (z₁ : ℝ) (n : ℕ) (ρ : ℝ) : ℝ :=
  pn.eval z₁ * fallingFactorial ρ n +
    (Polynomial.derivative pn1).eval z₁ * fallingFactorial ρ (n + 1)

/-- **Factorization of the indicial polynomial.** Since
`ρ^{(n+1)} = ρ^{(n)} · (ρ − n)`, the indicial polynomial factors as
```
simpleZeroIndicialPoly pn pn1 z₁ n ρ =
  ρ^{(n)} · (pn(z₁) + pn1'(z₁) · (ρ − n)).
```
The bracket is affine in `ρ` with leading coefficient `pn1'(z₁)` — the
"true" slope of the indicial polynomial at a simple zero. Non-degeneracy
`pn1'(z₁) ≠ 0` promotes the indicial polynomial from a formal sum to a
genuine polynomial of degree `n + 1` in `ρ`, which is the hypothesis
needed for eventual lower bounds `|P(ρ + m)| ≳ m^{n+1}` in the
convergence half. -/
lemma simpleZeroIndicialPoly_factor
    (pn pn1 : Polynomial ℝ) (z₁ : ℝ) (n : ℕ) (ρ : ℝ) :
    simpleZeroIndicialPoly pn pn1 z₁ n ρ =
      fallingFactorial ρ n *
        (pn.eval z₁ +
          (Polynomial.derivative pn1).eval z₁ * (ρ - (n : ℝ))) := by
  unfold simpleZeroIndicialPoly
  rw [fallingFactorial_succ]
  ring

open PowerSeries in
/-- **General-order substitution bridge (simple-zero form).**

Same content as `coeff_one_substLHSGen` but packaged with the named
indicial polynomial. For an order-`(n+1)` linear ODE with
`p_{n+1}(z₁) = 0`:

```
coeff 1 (substLHSGen ps (n+1) z₁ ρ g) =
  (-1)^n · simpleZeroIndicialPoly (p_n) (p_{n+1}) z₁ n ρ · g(0).
```
-/
theorem coeff_one_substLHSGen_simpleZero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (g : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) 1 (substLHSGen ps (n + 1) z₁ ρ g) =
      ((-1 : ℝ) ^ n) *
        simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ *
        coeff (R := ℝ) 0 g := by
  rw [coeff_one_substLHSGen ps n z₁ ρ g hpk]
  unfold simpleZeroIndicialPoly
  ring

/-- **Apéry as a special case.** The general-order simple-zero indicial
polynomial with `n = 2`, `p_n = q`, `p_{n+1} = p`, coincides with
`aperyPatternIndicialPoly`. -/
theorem aperyPatternIndicialPoly_eq_simpleZero
    (p2 p3 : Polynomial ℝ) (z₁ ρ : ℝ) :
    aperyPatternIndicialPoly p2 p3 z₁ ρ =
      simpleZeroIndicialPoly p2 p3 z₁ 2 ρ := by
  rw [aperyPatternIndicialPoly_eq]
  unfold simpleZeroIndicialPoly
  rw [fallingFactorial_two, fallingFactorial_three]
  ring

/-- **Framework → Indicial-root classification.**

If a formal series `g` has nonzero constant term and the order-`(n+1)`
substitution with simple zero `p_{n+1}(z₁) = 0` has vanishing leading
coefficient, then `ρ` is a root of the simple-zero indicial polynomial. -/
theorem simpleZeroIndicialPoly_eq_zero_of_substLHSGen_coeff_one_eq_zero
    {ps : ℕ → Polynomial ℝ} {n : ℕ} {z₁ ρ : ℝ} {g : PowerSeries ℝ}
    (hg : PowerSeries.coeff (R := ℝ) 0 g ≠ 0)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hvanish : PowerSeries.coeff (R := ℝ) 1 (substLHSGen ps (n + 1) z₁ ρ g) = 0) :
    simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ = 0 := by
  have hbridge := coeff_one_substLHSGen_simpleZero ps n z₁ ρ g hpk
  rw [hvanish] at hbridge
  have hsign : ((-1 : ℝ) ^ n) ≠ 0 :=
    pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
  have hprod :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ *
        PowerSeries.coeff (R := ℝ) 0 g = 0 := by
    have hall : ((-1 : ℝ) ^ n) *
        (simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ *
          PowerSeries.coeff (R := ℝ) 0 g) = 0 := by
      rw [← mul_assoc]; linarith [hbridge.symm]
    exact (mul_eq_zero.mp hall).resolve_left hsign
  exact (mul_eq_zero.mp hprod).resolve_right hg

/-! ## Shift identity and leading recurrence coefficient -/

open PowerSeries in
/-- **Shift identity (single X).** Multiplying `φ` by `X` before applying
`fallingEulerOp ρ j` is equivalent to first shifting `ρ → ρ + 1`, then
multiplying by `X`. Reflects the fact that `t · (t^ρ g)` has exponent
`ρ + 1`, and each coefficient of `g` at index `n` in `t · φ` comes from
index `n − 1` at the original ansatz. -/
lemma fallingEulerOp_X_mul (ρ : ℝ) (j : ℕ) (φ : PowerSeries ℝ) :
    fallingEulerOp ρ j ((X : PowerSeries ℝ) * φ) =
      (X : PowerSeries ℝ) * fallingEulerOp (ρ + 1) j φ := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | m
  · simp [coeff_fallingEulerOp]
  · rw [coeff_fallingEulerOp, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_succ_X_mul, coeff_fallingEulerOp]
    have hρ : (ρ + (m + 1 : ℕ) : ℝ) = (ρ + 1) + m := by push_cast; ring
    rw [hρ]

open PowerSeries in
/-- **Shift identity (general X^i).** Induction from the single-X case. -/
lemma fallingEulerOp_X_pow_mul (i : ℕ) (ρ : ℝ) (j : ℕ) (φ : PowerSeries ℝ) :
    fallingEulerOp ρ j ((X : PowerSeries ℝ) ^ i * φ) =
      (X : PowerSeries ℝ) ^ i * fallingEulerOp (ρ + i) j φ := by
  induction i generalizing ρ φ with
  | zero => simp
  | succ i ih =>
    have hX : ((X : PowerSeries ℝ) ^ (i + 1)) * φ
          = (X : PowerSeries ℝ) ^ i * ((X : PowerSeries ℝ) * φ) := by
      rw [pow_succ]; ring
    rw [hX, ih, fallingEulerOp_X_mul]
    have hρ : (ρ + ((i + 1 : ℕ) : ℝ)) = (ρ + i) + 1 := by push_cast; ring
    rw [hρ, pow_succ]
    ring

open PowerSeries in
/-- **Shift identity for `substLHSGen`.** Substituting `X^i · φ` into
the general substitution is the same as substituting `φ` at shifted
exponent `ρ + i`, then multiplying the whole result by `X^i`. -/
lemma substLHSGen_X_pow_mul
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ : ℝ)
    (i : ℕ) (φ : PowerSeries ℝ) :
    substLHSGen ps k z₁ ρ ((X : PowerSeries ℝ) ^ i * φ) =
      (X : PowerSeries ℝ) ^ i * substLHSGen ps k z₁ (ρ + i) φ := by
  unfold substLHSGen
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fallingEulerOp_X_pow_mul, mul_smul_comm]
  congr 1
  ring

open PowerSeries in
/-- **Leading coefficient of the Frobenius recurrence.**

For the order-`(n+1)` simple-zero regular singular case, the coefficient
of the `m`-th tail-mode of `g` (i.e., substituting `X^m · φ` as the
`g`-factor) in the `(m+1)`-th power-series coefficient of the scaled
substitution is

```
(-1)^n · P(ρ + m) · φ₀,
```

where `P = simpleZeroIndicialPoly`. This is exactly the leading piece of
the Frobenius recurrence for `g.coeff m`: solvability at index `m + 1`
requires `P(ρ + m) ≠ 0`, which under no-integer-shift conditions on the
indicial roots is automatic. -/
theorem coeff_succ_substLHSGen_X_pow_mul
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ) (φ : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ m * φ)) =
      ((-1 : ℝ) ^ n) *
        simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m) *
        coeff (R := ℝ) 0 φ := by
  rw [substLHSGen_X_pow_mul]
  have hrw : (m + 1 : ℕ) = 1 + m := by ring
  rw [hrw, PowerSeries.coeff_X_pow_mul]
  exact coeff_one_substLHSGen_simpleZero ps n z₁ (ρ + m) φ hpk

/-! ## Linearity of `substLHSGen` in `g`

The substitution operator is linear in the power series `g`. This
follows from coefficient-wise linearity of `fallingEulerOp` (it scales
`coeff n` by `fallingFactorial (ρ + n) k`) and the fact that
multiplication in `PowerSeries ℝ` is bilinear. These lemmas are the
building blocks for the Frobenius recurrence: once we know `substLHSGen`
is linear in `g`, we can decompose any `g` into modes and read off
coefficient contributions mode by mode. -/

open PowerSeries in
@[simp] lemma fallingEulerOp_zero (ρ : ℝ) (k : ℕ) :
    fallingEulerOp ρ k (0 : PowerSeries ℝ) = 0 := by
  apply PowerSeries.ext
  intro n
  simp

open PowerSeries in
lemma fallingEulerOp_add (ρ : ℝ) (k : ℕ) (f g : PowerSeries ℝ) :
    fallingEulerOp ρ k (f + g) =
      fallingEulerOp ρ k f + fallingEulerOp ρ k g := by
  apply PowerSeries.ext
  intro n
  simp [mul_add]

open PowerSeries in
lemma fallingEulerOp_smul (c ρ : ℝ) (k : ℕ) (f : PowerSeries ℝ) :
    fallingEulerOp ρ k (c • f) = c • fallingEulerOp ρ k f := by
  apply PowerSeries.ext
  intro n
  simp [mul_left_comm]

open PowerSeries in
@[simp] lemma substLHSGen_zero
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ : ℝ) :
    substLHSGen ps k z₁ ρ (0 : PowerSeries ℝ) = 0 := by
  unfold substLHSGen
  apply Finset.sum_eq_zero
  intro j _
  simp

open PowerSeries in
lemma substLHSGen_add
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ : ℝ) (f g : PowerSeries ℝ) :
    substLHSGen ps k z₁ ρ (f + g) =
      substLHSGen ps k z₁ ρ f + substLHSGen ps k z₁ ρ g := by
  unfold substLHSGen
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fallingEulerOp_add, mul_add, smul_add]

open PowerSeries in
lemma substLHSGen_smul
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ c : ℝ) (g : PowerSeries ℝ) :
    substLHSGen ps k z₁ ρ (c • g) = c • substLHSGen ps k z₁ ρ g := by
  unfold substLHSGen
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fallingEulerOp_smul, mul_smul_comm, smul_comm]

/-! ## Mode independence: `coeff (m+1)` of `substLHSGen` depends only on
    low coefficients of `g`

Under the simple-zero hypothesis `p_{n+1}(z₁) = 0`, if a power series
`h` has all coefficients up to index `m` vanishing, then the
`(m+1)`-th coefficient of `substLHSGen ps (n+1) z₁ ρ h` also vanishes.
Equivalently: `coeff (m+1) (substLHSGen ps (n+1) z₁ ρ g)` depends only
on `g.coeff 0, …, g.coeff m`. This is the independence statement
underlying the Frobenius recurrence: only modes ≤ m of `g` contribute to
mode `m+1` of the substituted ODE. -/

open PowerSeries in
/-- Constant coefficient of `substLHSGen` at a simple zero vanishes.
Only the top-order `j = n+1` term contributes to `coeff 0`, and that
term carries the factor `p_{n+1}(z₁) = 0`. -/
lemma coeff_zero_substLHSGen_simpleZero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (φ : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) 0 (substLHSGen ps (n + 1) z₁ ρ φ) = 0 := by
  unfold substLHSGen
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [LinearMap.map_smul_of_tower]
  by_cases hjtop : j = n + 1
  · subst hjtop
    have hxpow : ((X : PowerSeries ℝ) ^ (n + 1 - (n + 1))) = 1 := by simp
    rw [hxpow, one_mul, PowerSeries.coeff_mul]
    have hsingle : Finset.antidiagonal 0 = {(0, 0)} := rfl
    rw [hsingle, Finset.sum_singleton]
    refine smul_eq_zero.mpr (Or.inr ?_)
    refine mul_eq_zero.mpr (Or.inl ?_)
    have : PowerSeries.coeff (R := ℝ) 0
        ((taylorShift (ps (n + 1)) z₁ : Polynomial ℝ) : PowerSeries ℝ) = 0 := by
      rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero,
          taylorShift_eval_zero]
      exact hpk
    convert this using 2
  · have hlt : j < n + 1 := by
      have := Finset.mem_range.mp hj; omega
    have hpos : 0 < n + 1 - j := Nat.sub_pos_of_lt hlt
    rw [mul_assoc, show (0 : ℕ) = (n + 1 - j) - (n + 1 - j) from by omega,
        PowerSeries.coeff_X_pow_mul']
    rw [if_neg (by omega)]
    simp

open PowerSeries in
/-- **Mode independence.** Under the simple-zero hypothesis
`p_{n+1}(z₁) = 0`, if `h` has all coefficients up to index `m`
vanishing, then the `(m+1)`-th coefficient of
`substLHSGen ps (n+1) z₁ ρ h` also vanishes.

Consequently, by linearity, `coeff (m+1) (substLHSGen ps (n+1) z₁ ρ g)`
depends only on `g.coeff 0, …, g.coeff m`. -/
theorem coeff_succ_substLHSGen_of_coeff_le_eq_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ) (h : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hlow : ∀ i ≤ m, coeff (R := ℝ) i h = 0) :
    coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ h) = 0 := by
  have hdvd : (X : PowerSeries ℝ) ^ (m + 1) ∣ h := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    exact hlow i (Nat.lt_succ_iff.mp hi)
  obtain ⟨h', rfl⟩ := hdvd
  rw [substLHSGen_X_pow_mul, show (m + 1 : ℕ) = (m + 1) + 0 from rfl,
      PowerSeries.coeff_X_pow_mul']
  rw [if_pos (Nat.le_add_right _ _)]
  have := coeff_zero_substLHSGen_simpleZero ps n z₁ (ρ + ((m : ℝ) + 1)) h' hpk
  have hcast : ρ + ((m + 1 : ℕ) : ℝ) = ρ + ((m : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  simpa using this

open PowerSeries in
/-- **Mode independence, symmetric form.** Under the simple-zero
hypothesis, the `(m+1)`-th coefficient of `substLHSGen ps (n+1) z₁ ρ g`
depends only on the coefficients of `g` at indices ≤ m: two series
that agree on those indices produce the same `(m+1)`-th coefficient. -/
theorem coeff_succ_substLHSGen_congr_low
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ)
    (g g' : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hlow : ∀ i ≤ m, coeff (R := ℝ) i g = coeff (R := ℝ) i g') :
    coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g) =
      coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g') := by
  have hdecomp : g = (g - g') + g' := by ring
  rw [hdecomp, substLHSGen_add, map_add]
  have hzero :
      coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ (g - g')) = 0 := by
    apply coeff_succ_substLHSGen_of_coeff_le_eq_zero _ _ _ _ _ _ hpk
    intro i hi
    rw [map_sub]
    exact sub_eq_zero.mpr (hlow i hi)
  rw [hzero, zero_add]

open PowerSeries in
/-- **Leading coefficient of the Frobenius recurrence (general `g`).**

Splitting `g = (g.coeff m) • X^m + (g - (g.coeff m) • X^m)` and applying
linearity, the `(m+1)`-th coefficient of the Frobenius substitution
breaks cleanly into

```
coeff(m+1) S(g) = (-1)^n · P(ρ+m) · g.coeff m + coeff(m+1) S(tail),
```

where `tail = g − (g.coeff m) • X^m` has `tail.coeff m = 0`. This is the
shape of the classical Frobenius recurrence: the mode-`m` contribution
feeds into mode `(m+1)` through the indicial polynomial evaluated at the
shifted exponent. -/
theorem coeff_succ_substLHSGen_leading_extract
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ) (g : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g) =
      ((-1 : ℝ) ^ n) *
          simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m) *
          coeff (R := ℝ) m g +
        coeff (R := ℝ) (m + 1)
          (substLHSGen ps (n + 1) z₁ ρ
            (g - coeff (R := ℝ) m g • (X : PowerSeries ℝ) ^ m)) := by
  have hdecomp :
      g = coeff (R := ℝ) m g • (X : PowerSeries ℝ) ^ m +
            (g - coeff (R := ℝ) m g • (X : PowerSeries ℝ) ^ m) := by ring
  conv_lhs => rw [hdecomp]
  rw [substLHSGen_add, map_add, substLHSGen_smul, map_smul]
  congr 1
  -- Leading piece: coeff(m+1) substLHSGen (X^m) = (-1)^n · P(ρ+m)
  have hxm :
      coeff (R := ℝ) (m + 1)
          (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ m)) =
        ((-1 : ℝ) ^ n) *
          simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m) *
          coeff (R := ℝ) 0 (1 : PowerSeries ℝ) := by
    have := coeff_succ_substLHSGen_X_pow_mul ps n z₁ ρ m (1 : PowerSeries ℝ) hpk
    simpa using this
  rw [smul_eq_mul, hxm]
  simp
  ring

open PowerSeries in
/-- **Frobenius uniqueness at level `m`.** Two formal solutions that
agree on all coefficients strictly below index `m` must agree at index
`m` as well, provided the indicial polynomial at the shifted exponent
`ρ + m` does not vanish.

This is the "one step of induction" form of Frobenius uniqueness: under
the no-integer-shift hypothesis `P(ρ + m) ≠ 0`, the recurrence determines
`g.coeff m` uniquely from the preceding coefficients. -/
theorem substLHSGen_solution_unique_at_level
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ)
    (g g' : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hP : simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m) ≠ 0)
    (hg : coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g) = 0)
    (hg' : coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g') = 0)
    (hlow : ∀ i < m, coeff (R := ℝ) i g = coeff (R := ℝ) i g') :
    coeff (R := ℝ) m g = coeff (R := ℝ) m g' := by
  set P := simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m)
  have hgex := coeff_succ_substLHSGen_leading_extract ps n z₁ ρ m g hpk
  have hg'ex := coeff_succ_substLHSGen_leading_extract ps n z₁ ρ m g' hpk
  -- Tails agree: both have coeff m = 0 and agree on coeffs below m.
  have htail :
      coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ
          (g - coeff (R := ℝ) m g • (X : PowerSeries ℝ) ^ m)) =
        coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ
          (g' - coeff (R := ℝ) m g' • (X : PowerSeries ℝ) ^ m)) := by
    apply coeff_succ_substLHSGen_congr_low ps n z₁ ρ m _ _ hpk
    intro i hi
    rw [map_sub, map_sub, map_smul, map_smul]
    rcases lt_or_eq_of_le hi with hlt | heq
    · have hxi_zero : coeff (R := ℝ) i ((X : PowerSeries ℝ) ^ m) = 0 := by
        rw [PowerSeries.coeff_X_pow]
        exact if_neg (Nat.ne_of_lt hlt)
      rw [hxi_zero, smul_zero, smul_zero, hlow i hlt]
    · rw [heq]
      have hxm : coeff (R := ℝ) m ((X : PowerSeries ℝ) ^ m) = 1 := by
        rw [PowerSeries.coeff_X_pow]; simp
      rw [hxm, smul_eq_mul, smul_eq_mul, mul_one, mul_one, sub_self, sub_self]
  -- Combine the extracted forms with vanishing and htail.
  rw [hg, eq_comm, ← sub_eq_zero] at hgex
  rw [hg', eq_comm, ← sub_eq_zero] at hg'ex
  have hdiff : (-1 : ℝ) ^ n * P * (coeff (R := ℝ) m g - coeff (R := ℝ) m g') = 0 := by
    have h1 :
        (-1 : ℝ) ^ n * P * coeff (R := ℝ) m g =
        - coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ
            (g - coeff (R := ℝ) m g • (X : PowerSeries ℝ) ^ m)) := by
      linarith
    have h2 :
        (-1 : ℝ) ^ n * P * coeff (R := ℝ) m g' =
        - coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ
            (g' - coeff (R := ℝ) m g' • (X : PowerSeries ℝ) ^ m)) := by
      linarith
    rw [mul_sub, h1, h2, htail]; ring
  have hneg : (-1 : ℝ) ^ n ≠ 0 :=
    pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
  have hprod_ne : (-1 : ℝ) ^ n * P ≠ 0 := mul_ne_zero hneg hP
  have : coeff (R := ℝ) m g - coeff (R := ℝ) m g' = 0 :=
    (mul_eq_zero.mp hdiff).resolve_left hprod_ne
  linarith

open PowerSeries in
/-- **Frobenius uniqueness (global form).** Two formal power series
with identical constant term that both annihilate the substituted ODE
at every index `≥ 1` must coincide, provided the indicial polynomial
does not vanish on the lattice `ρ + m` for any positive integer `m`
(the no-integer-shift / non-resonance condition).

This packages the level-by-level uniqueness into a closed statement:
given compatible leading data (`g.coeff 0 = g'.coeff 0`) and non-resonance,
the Frobenius coefficients are forced all the way down. -/
theorem substLHSGen_solution_unique
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ)
    (g g' : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hP : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m) ≠ 0)
    (hg : ∀ m : ℕ, coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g) = 0)
    (hg' : ∀ m : ℕ, coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g') = 0)
    (h0 : coeff (R := ℝ) 0 g = coeff (R := ℝ) 0 g') :
    g = g' := by
  apply PowerSeries.ext
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; exact h0
    · apply substLHSGen_solution_unique_at_level ps n z₁ ρ m g g' hpk
          (hP m hmpos) (hg m) (hg' m)
      intro i hi
      exact ih i hi

/-! ## Linear decomposition of the Frobenius substitution

The substitution operator is linear in `g`. Combined with the
congr-low principle, this lets us write `coeff (m+1) S(g)` as an
explicit linear combination of `g.coeff i` for `i ≤ m`, with weights
determined by the action of `S` on the monomials `X^i`. These weights
are independent of `g`, so the Frobenius recurrence is a genuine
linear system. This form is the foundation for analytic convergence
estimates (STRATEGY Step 3, analytic half). -/

open PowerSeries in
/-- `substLHSGen` respects finite `Finset` sums (in `g`). -/
lemma substLHSGen_finset_sum
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ : ℝ)
    {α : Type*} (s : Finset α) (f : α → PowerSeries ℝ) :
    substLHSGen ps k z₁ ρ (∑ i ∈ s, f i) =
      ∑ i ∈ s, substLHSGen ps k z₁ ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, substLHSGen_add, ih, Finset.sum_insert ha]

open PowerSeries in
/-- **Linear decomposition of the Frobenius substitution.** Under the
simple-zero hypothesis `p_{n+1}(z₁) = 0`, the `(m+1)`-th coefficient
of `substLHSGen ps (n+1) z₁ ρ g` is a linear combination of
`g.coeff i` for `i ∈ [0, m]`, with weights
`coeff (m+1) (substLHSGen ... (X^i))` that depend only on the ODE
data (and not on `g`). This is the explicit "Frobenius recurrence is
a linear system" statement. -/
theorem coeff_succ_substLHSGen_linearity
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ) (g : PowerSeries ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g) =
      ∑ i ∈ Finset.range (m + 1),
        coeff (R := ℝ) i g *
          coeff (R := ℝ) (m + 1)
            (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i)) := by
  -- Truncation of `g` to its first `m+1` coefficients as a finite sum.
  set truncG : PowerSeries ℝ :=
    ∑ i ∈ Finset.range (m + 1),
      coeff (R := ℝ) i g • ((X : PowerSeries ℝ) ^ i) with htrunc_def
  -- `truncG` and `g` agree on coefficients `0, 1, …, m`.
  have hagree : ∀ j ≤ m, coeff (R := ℝ) j truncG = coeff (R := ℝ) j g := by
    intro j hj
    have hj_mem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    rw [htrunc_def, map_sum]
    rw [Finset.sum_eq_single j]
    · rw [map_smul, PowerSeries.coeff_X_pow]
      simp
    · intro i _ hij
      rw [map_smul, PowerSeries.coeff_X_pow]
      have hne : ¬ j = i := Ne.symm hij
      simp [hne]
    · intro h; exact absurd hj_mem h
  -- Apply congr_low to transfer from `g` to `truncG`.
  have hswap : coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ g) =
      coeff (R := ℝ) (m + 1) (substLHSGen ps (n + 1) z₁ ρ truncG) :=
    coeff_succ_substLHSGen_congr_low ps n z₁ ρ m g truncG hpk
      (fun i hi => (hagree i hi).symm)
  rw [hswap, htrunc_def, substLHSGen_finset_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [substLHSGen_smul, map_smul, smul_eq_mul]

open PowerSeries in
/-- **Diagonal weight = indicial polynomial.** The `i = m` weight in the
linear decomposition is exactly `(-1)^n · P(ρ + m)` — the same quantity
that appears as the denominator in the Frobenius recurrence. Immediate
specialization of `coeff_succ_substLHSGen_X_pow_mul` to `φ = 1`. -/
lemma coeff_succ_substLHSGen_X_pow_self
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ m)) =
      ((-1 : ℝ) ^ n) *
        simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + m) := by
  have h := coeff_succ_substLHSGen_X_pow_mul ps n z₁ ρ m (1 : PowerSeries ℝ) hpk
  simp only [mul_one] at h
  simpa using h

open PowerSeries in
/-- **Weight reduction via exponent shift.** The weight
`coeff (m+1) (substLHSGen ps (n+1) z₁ ρ (X^i))` in the linearity
decomposition simplifies, via `substLHSGen_X_pow_mul`, to a coefficient
of the action of `substLHSGen` (at shifted exponent `ρ + i`) on the
constant series `1`:

```
coeff (m+1) S_ρ (X^i) = coeff (m+1 − i) S_{ρ+i} (1)      if i ≤ m+1
```

This turns the per-`i` weight into a coefficient of a **universal**
series `substLHSGen ps (n+1) z₁ (ρ+i) 1`, whose coefficient growth
can be analyzed purely from the ODE polynomial data. Foundation for
uniform bounds on the Frobenius recurrence weights. -/
lemma coeff_succ_substLHSGen_X_pow_shift
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m i : ℕ)
    (hi : i ≤ m + 1) :
    coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i)) =
      coeff (R := ℝ) (m + 1 - i)
        (substLHSGen ps (n + 1) z₁ (ρ + (i : ℝ)) (1 : PowerSeries ℝ)) := by
  have hmul := substLHSGen_X_pow_mul ps (n + 1) z₁ ρ i (1 : PowerSeries ℝ)
  rw [mul_one] at hmul
  rw [hmul, PowerSeries.coeff_X_pow_mul']
  rw [if_pos hi]

open PowerSeries in
/-- **Off-diagonal vanishing (upper).** For `i > m`, the weight
`coeff (m+1) S(X^i)` vanishes — the action of `S` on `X^i` starts at
index `i + 1` or later (the leading term at index `i` from the
`j = n+1` slot is killed by the simple-zero hypothesis). This confirms
that the linear decomposition `coeff_succ_substLHSGen_linearity` has
support exactly `Finset.range (m + 1)`. -/
lemma coeff_succ_substLHSGen_X_pow_upper_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m i : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hi : m < i) :
    coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i)) = 0 := by
  apply coeff_succ_substLHSGen_of_coeff_le_eq_zero _ _ _ _ _ _ hpk
  intro j hj
  rw [PowerSeries.coeff_X_pow]
  have hne : j ≠ i := by omega
  simp [hne]

open PowerSeries in
/-- `fallingEulerOp ρ' j` applied to the constant series `1` produces the
scalar power series `(fallingFactorial ρ' j) • 1`. Only the constant
coefficient survives because `coeff n (1) = 0` for `n ≥ 1`. -/
lemma fallingEulerOp_one (ρ' : ℝ) (j : ℕ) :
    fallingEulerOp ρ' j (1 : PowerSeries ℝ) =
      (fallingFactorial ρ' j) • (1 : PowerSeries ℝ) := by
  ext n
  rw [coeff_fallingEulerOp, map_smul, smul_eq_mul]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; push_cast; simp
  · have h1 : coeff (R := ℝ) n (1 : PowerSeries ℝ) = 0 := by
      rw [PowerSeries.coeff_one, if_neg hn]
    rw [h1]; ring

open PowerSeries in
/-- **Explicit weight formula for `S_{ρ'}(1)`.** Applied to the constant
series `1`, the substitution operator's `m`-th coefficient expands as a
`(k+1)`-term sum over the ODE polynomial slots `j ∈ [0, k]`. Each slot
contributes the signed product of a falling factorial `(ρ')^{(j)}` and a
Taylor coefficient of the shifted polynomial `taylorShift (ps j) z₁` at
index `m − (k − j)` (zero when `k − j > m`, i.e. when the `X^{k−j}`
factor overshoots index `m`).

Combined with `coeff_succ_substLHSGen_X_pow_shift`, this gives a fully
explicit formula for the Frobenius recurrence weights
`coeff (m+1) S(X^i) = coeff (m+1-i) S_{ρ+i}(1)`, hooking the recurrence
directly onto the ODE polynomial Taylor data. Foundation for polynomial
growth bounds on the weights in the analytic-half majorant argument. -/
lemma coeff_substLHSGen_one_explicit
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ' : ℝ) (m : ℕ) :
    coeff (R := ℝ) m (substLHSGen ps k z₁ ρ' (1 : PowerSeries ℝ)) =
      ∑ j ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ j) * fallingFactorial ρ' j *
          (if k - j ≤ m then
              Polynomial.coeff (taylorShift (ps j) z₁) (m - (k - j))
           else 0) := by
  unfold substLHSGen
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [LinearMap.map_smul_of_tower, fallingEulerOp_one]
  have hrw :
      (X : PowerSeries ℝ) ^ (k - j) *
        ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ) *
        ((fallingFactorial ρ' j) • (1 : PowerSeries ℝ)) =
      (fallingFactorial ρ' j) •
        ((X : PowerSeries ℝ) ^ (k - j) *
          ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)) := by
    rw [mul_smul_comm, mul_one]
  rw [hrw, LinearMap.map_smul_of_tower, smul_eq_mul, smul_eq_mul]
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hle : k - j ≤ m
  · rw [if_pos hle, if_pos hle, Polynomial.coeff_coe]
    ring
  · rw [if_neg hle, if_neg hle, mul_zero, mul_zero, mul_zero]

open PowerSeries in
/-- **Fully explicit Frobenius recurrence weight.** Composing the
exponent-shift reduction `coeff (m+1) S_ρ(Xⁱ) = coeff (m+1−i) S_{ρ+i}(1)`
with the explicit expansion of `S_{ρ+i}(1)` gives a fully explicit
`(n+2)`-term sum formula for the weight of `X^i` in the Frobenius
recurrence, parameterized purely by the ODE Taylor data `taylorShift (ps j) z₁`
and the falling factorials `(ρ + i)^{(j)}`.

For `i ≤ m + 1`:
```
coeff (m+1) S_ρ(Xⁱ) =
  Σ_{j=0}^{n+1} (-1)^j · (ρ+i)^{(j)} ·
    [if n+1-j ≤ m+1-i then Taylor_{(m+1-i)-(n+1-j)}(p_j)(z₁) else 0]
```
where `Taylor_n(p)(z₁) = Polynomial.coeff (taylorShift p z₁) n`. This is
the target form for polynomial growth bounds on the weights in the
analytic-half majorant argument. -/
theorem coeff_succ_substLHSGen_X_pow_explicit
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m i : ℕ)
    (hi : i ≤ m + 1) :
    coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i)) =
      ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * fallingFactorial (ρ + (i : ℝ)) j *
          (if n + 1 - j ≤ m + 1 - i then
              Polynomial.coeff (taylorShift (ps j) z₁)
                ((m + 1 - i) - (n + 1 - j))
           else 0) := by
  rw [coeff_succ_substLHSGen_X_pow_shift ps n z₁ ρ m i hi]
  exact coeff_substLHSGen_one_explicit ps (n + 1) z₁ (ρ + (i : ℝ)) (m + 1 - i)

open PowerSeries in
/-- **Triangle-inequality bound on the Frobenius weight.** Applying the
triangle inequality to the fully explicit sum
`coeff_succ_substLHSGen_X_pow_explicit` bounds the absolute value of the
weight by an `(n+2)`-term sum of products
`|(ρ+i)^{(j)}| · |Taylor coeff of taylorShift (ps j) z₁|`. Combined with
`abs_fallingFactorial_le`, this is the launchpad for polynomial growth
estimates `|w_i| ≤ C · (i + n + constants)^{n+1}` used in the majorant
argument for Frobenius series convergence. -/
lemma abs_coeff_succ_substLHSGen_X_pow_le
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m i : ℕ)
    (hi : i ≤ m + 1) :
    |coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i))| ≤
      ∑ j ∈ Finset.range (n + 2),
        |fallingFactorial (ρ + (i : ℝ)) j| *
          (if n + 1 - j ≤ m + 1 - i then
              |Polynomial.coeff (taylorShift (ps j) z₁)
                ((m + 1 - i) - (n + 1 - j))|
           else 0) := by
  rw [coeff_succ_substLHSGen_X_pow_explicit ps n z₁ ρ m i hi]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro j _
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  by_cases hle : n + 1 - j ≤ m + 1 - i
  · rw [if_pos hle, if_pos hle]
  · rw [if_neg hle, if_neg hle, abs_zero, mul_zero]

open PowerSeries in
/-- **Polynomial growth bound on Frobenius recurrence weights.** Under a
uniform Taylor-coefficient bound `B` on the shifted polynomials
`taylorShift (ps j) z₁` for `j ∈ [0, n+1]`, the weight `w_i` satisfies
```
|w_i| ≤ (n+2) · B · (|ρ + i| + (n+1))^{n+1}
```
for every `i ≤ m + 1`. This is the explicit polynomial-in-`i` bound used
as a majorant in the geometric bound on `|frobeniusCoeff m|`, closing
the first half of the analytic convergence argument. -/
lemma abs_coeff_succ_substLHSGen_X_pow_bound
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m i : ℕ)
    (hi : i ≤ m + 1) (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i))| ≤
      ((n + 2 : ℕ) : ℝ) * B *
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  refine (abs_coeff_succ_substLHSGen_X_pow_le ps n z₁ ρ m i hi).trans ?_
  have hbound : ∀ j ∈ Finset.range (n + 2),
      |fallingFactorial (ρ + (i : ℝ)) j| *
        (if n + 1 - j ≤ m + 1 - i then
            |Polynomial.coeff (taylorShift (ps j) z₁)
              ((m + 1 - i) - (n + 1 - j))|
         else 0) ≤
      B * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    intro j hj
    have hj_le : j ≤ n + 1 := by
      have := Finset.mem_range.mp hj; omega
    have h_inner_le_B :
        (if n + 1 - j ≤ m + 1 - i then
            |Polynomial.coeff (taylorShift (ps j) z₁)
              ((m + 1 - i) - (n + 1 - j))|
         else (0 : ℝ)) ≤ B := by
      by_cases hle : n + 1 - j ≤ m + 1 - i
      · rw [if_pos hle]; exact hB j hj _
      · rw [if_neg hle]; exact hB_nn
    have h_ff : |fallingFactorial (ρ + (i : ℝ)) j| ≤
        (|ρ + (i : ℝ)| + (j : ℝ)) ^ j :=
      abs_fallingFactorial_le _ _
    have h_base_le : (|ρ + (i : ℝ)| + (j : ℝ)) ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) := by
      have : (j : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hj_le
      linarith
    have h_base_nn : (0 : ℝ) ≤ |ρ + (i : ℝ)| + (j : ℝ) := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith [abs_nonneg (ρ + (i : ℝ))]
    have h_big_nn : (0 : ℝ) ≤ |ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [abs_nonneg (ρ + (i : ℝ))]
    have h_big_ge_one :
        (1 : ℝ) ≤ |ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ n + 1 := by omega
        exact_mod_cast this
      linarith [abs_nonneg (ρ + (i : ℝ))]
    have h_pow1 : (|ρ + (i : ℝ)| + (j : ℝ)) ^ j ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ j :=
      pow_le_pow_left₀ h_base_nn h_base_le j
    have h_pow2 : (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ j ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      pow_le_pow_right₀ h_big_ge_one hj_le
    have h_ff_big : |fallingFactorial (ρ + (i : ℝ)) j| ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      le_trans h_ff (le_trans h_pow1 h_pow2)
    have h_inner_nn :
        (0 : ℝ) ≤
          (if n + 1 - j ≤ m + 1 - i then
              |Polynomial.coeff (taylorShift (ps j) z₁)
                ((m + 1 - i) - (n + 1 - j))|
           else 0) := by
      by_cases hle : n + 1 - j ≤ m + 1 - i
      · rw [if_pos hle]; exact abs_nonneg _
      · rw [if_neg hle]
    have h_pow_big_nn :
        (0 : ℝ) ≤ (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      pow_nonneg h_big_nn (n + 1)
    calc |fallingFactorial (ρ + (i : ℝ)) j| *
          (if n + 1 - j ≤ m + 1 - i then
              |Polynomial.coeff (taylorShift (ps j) z₁)
                ((m + 1 - i) - (n + 1 - j))|
           else 0)
        ≤ (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * B :=
          mul_le_mul h_ff_big h_inner_le_B h_inner_nn h_pow_big_nn
      _ = B * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by ring
  calc _ ≤ ∑ _ ∈ Finset.range (n + 2),
              B * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
          Finset.sum_le_sum hbound
    _ = ((n + 2 : ℕ) : ℝ) *
          (B * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
          rw [Finset.sum_const, Finset.card_range]; push_cast; ring
    _ = ((n + 2 : ℕ) : ℝ) * B *
          (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by ring

open PowerSeries in
/-- **Per-`j` sharpened version of `abs_coeff_succ_substLHSGen_X_pow_bound`.**
Replaces the uniform Taylor-coefficient bound `B` by per-`j` bounds
`B_j` on `taylorShift (ps j) z₁`. The conclusion replaces
`(n+2)·B·(|ρ+i|+(n+1))^{n+1}` with `(Σ_j B_j)·(|ρ+i|+(n+1))^{n+1}`,
which is strictly tighter whenever some `B_j < max_j B_j` (e.g. at the
Apéry conifold where `B_0 = B_1 = 0` makes the per-`j` form `2×`
sharper than the uniform form). -/
lemma abs_coeff_succ_substLHSGen_X_pow_bound_per_j
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ) (m i : ℕ)
    (hi : i ≤ m + 1) (Bj : ℕ → ℝ)
    (hBj_nn : ∀ j ∈ Finset.range (n + 2), 0 ≤ Bj j)
    (hBj : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ Bj j) :
    |coeff (R := ℝ) (m + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i))| ≤
      (∑ j ∈ Finset.range (n + 2), Bj j) *
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  refine (abs_coeff_succ_substLHSGen_X_pow_le ps n z₁ ρ m i hi).trans ?_
  have hbound : ∀ j ∈ Finset.range (n + 2),
      |fallingFactorial (ρ + (i : ℝ)) j| *
        (if n + 1 - j ≤ m + 1 - i then
            |Polynomial.coeff (taylorShift (ps j) z₁)
              ((m + 1 - i) - (n + 1 - j))|
         else 0) ≤
      Bj j * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
    intro j hj
    have hj_le : j ≤ n + 1 := by
      have := Finset.mem_range.mp hj; omega
    have h_inner_le : (if n + 1 - j ≤ m + 1 - i then
            |Polynomial.coeff (taylorShift (ps j) z₁)
              ((m + 1 - i) - (n + 1 - j))|
         else (0 : ℝ)) ≤ Bj j := by
      by_cases hle : n + 1 - j ≤ m + 1 - i
      · rw [if_pos hle]; exact hBj j hj _
      · rw [if_neg hle]; exact hBj_nn j hj
    have h_ff : |fallingFactorial (ρ + (i : ℝ)) j| ≤
        (|ρ + (i : ℝ)| + (j : ℝ)) ^ j :=
      abs_fallingFactorial_le _ _
    have h_base_le : (|ρ + (i : ℝ)| + (j : ℝ)) ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) := by
      have : (j : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hj_le
      linarith
    have h_base_nn : (0 : ℝ) ≤ |ρ + (i : ℝ)| + (j : ℝ) := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith [abs_nonneg (ρ + (i : ℝ))]
    have h_big_nn : (0 : ℝ) ≤ |ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [abs_nonneg (ρ + (i : ℝ))]
    have h_big_ge_one :
        (1 : ℝ) ≤ |ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ n + 1 := by omega
        exact_mod_cast this
      linarith [abs_nonneg (ρ + (i : ℝ))]
    have h_pow1 : (|ρ + (i : ℝ)| + (j : ℝ)) ^ j ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ j :=
      pow_le_pow_left₀ h_base_nn h_base_le j
    have h_pow2 : (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ j ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      pow_le_pow_right₀ h_big_ge_one hj_le
    have h_ff_big : |fallingFactorial (ρ + (i : ℝ)) j| ≤
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      le_trans h_ff (le_trans h_pow1 h_pow2)
    have h_inner_nn :
        (0 : ℝ) ≤
          (if n + 1 - j ≤ m + 1 - i then
              |Polynomial.coeff (taylorShift (ps j) z₁)
                ((m + 1 - i) - (n + 1 - j))|
           else 0) := by
      by_cases hle : n + 1 - j ≤ m + 1 - i
      · rw [if_pos hle]; exact abs_nonneg _
      · rw [if_neg hle]
    have h_pow_big_nn :
        (0 : ℝ) ≤ (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      pow_nonneg h_big_nn (n + 1)
    calc |fallingFactorial (ρ + (i : ℝ)) j| *
          (if n + 1 - j ≤ m + 1 - i then
              |Polynomial.coeff (taylorShift (ps j) z₁)
                ((m + 1 - i) - (n + 1 - j))|
           else 0)
        ≤ (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * Bj j :=
          mul_le_mul h_ff_big h_inner_le h_inner_nn h_pow_big_nn
      _ = Bj j * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by ring
  calc _ ≤ ∑ j ∈ Finset.range (n + 2),
              Bj j * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
          Finset.sum_le_sum hbound
    _ = (∑ j ∈ Finset.range (n + 2), Bj j) *
          (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
          rw [← Finset.sum_mul]

/-! ## Frobenius existence: recursive coefficient builder

Given an indicial root `ρ` and a chosen constant-term value `c₀`, the
Frobenius recurrence determines the power-series coefficients
recursively:
```
a_0 = c₀
a_{m+1} = - coeff(m+2) S(partial_m) / ((-1)^n · P(ρ + (m+1))),
```
where `partial_m = Σ_{i≤m} a_i · X^i` is the truncation through index
`m` and `S = substLHSGen ps (n+1) z₁ ρ`. The definition uses structural
recursion on `ℕ`, returning the pair `(a_{m+1}, partial_{m+1})`. -/

open PowerSeries in
/-- Joint recursion tracking both the most recent Frobenius coefficient
and the partial-sum power series up to that index. -/
noncomputable def frobeniusBuilder
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) : ℕ → ℝ × PowerSeries ℝ
  | 0 => (c₀, (PowerSeries.C (R := ℝ)) c₀)
  | m + 1 =>
    let prev := frobeniusBuilder ps n z₁ ρ c₀ m
    let series : PowerSeries ℝ := prev.2
    let denom : ℝ := ((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + (m + 1 : ℕ))
    let nextCoeff : ℝ :=
      - PowerSeries.coeff (R := ℝ) (m + 1 + 1)
          (substLHSGen ps (n + 1) z₁ ρ series) / denom
    (nextCoeff, series + nextCoeff • ((PowerSeries.X : PowerSeries ℝ) ^ (m + 1)))

/-- The `m`-th Frobenius coefficient produced by the recurrence. -/
noncomputable def frobeniusCoeff
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ) : ℝ :=
  (frobeniusBuilder ps n z₁ ρ c₀ m).1

/-- The partial sum `Σ_{i≤m} a_i · X^i` through index `m`. -/
noncomputable def frobeniusPartialSum
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ) : PowerSeries ℝ :=
  (frobeniusBuilder ps n z₁ ρ c₀ m).2

@[simp] lemma frobeniusCoeff_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    frobeniusCoeff ps n z₁ ρ c₀ 0 = c₀ := rfl

@[simp] lemma frobeniusPartialSum_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    frobeniusPartialSum ps n z₁ ρ c₀ 0 = (PowerSeries.C (R := ℝ)) c₀ := rfl

/-- Recursive extension: the partial sum through `m+1` equals the partial
sum through `m` plus the newly-computed coefficient times `X^{m+1}`. -/
lemma frobeniusPartialSum_succ
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ) :
    frobeniusPartialSum ps n z₁ ρ c₀ (m + 1) =
      frobeniusPartialSum ps n z₁ ρ c₀ m
        + frobeniusCoeff ps n z₁ ρ c₀ (m + 1) •
          ((PowerSeries.X : PowerSeries ℝ) ^ (m + 1)) := rfl

/-- Coefficients of the partial sum above its index vanish. -/
lemma coeff_frobeniusPartialSum_gt
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    ∀ (m i : ℕ), m < i →
      PowerSeries.coeff (R := ℝ) i (frobeniusPartialSum ps n z₁ ρ c₀ m) = 0 := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.mp hi
    simp [frobeniusPartialSum, frobeniusBuilder, PowerSeries.coeff_C, hi0]
  | succ m ih =>
    intro i hi
    rw [frobeniusPartialSum_succ, map_add, map_smul]
    have h1 : PowerSeries.coeff (R := ℝ) i
        (frobeniusPartialSum ps n z₁ ρ c₀ m) = 0 := ih i (by omega)
    have h2 : PowerSeries.coeff (R := ℝ) i
        ((PowerSeries.X : PowerSeries ℝ) ^ (m + 1)) = 0 := by
      rw [PowerSeries.coeff_X_pow]
      have : i ≠ m + 1 := by omega
      simp [this]
    rw [h1, h2]; simp

/-- Coefficients of the partial sum up to and including its index agree
with the Frobenius recurrence. -/
lemma coeff_frobeniusPartialSum_le
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    ∀ (m i : ℕ), i ≤ m →
      PowerSeries.coeff (R := ℝ) i (frobeniusPartialSum ps n z₁ ρ c₀ m) =
        frobeniusCoeff ps n z₁ ρ c₀ i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    simp [frobeniusPartialSum, frobeniusBuilder, frobeniusCoeff,
          PowerSeries.coeff_C]
  | succ m ih =>
    intro i hi
    rw [frobeniusPartialSum_succ, map_add, map_smul]
    by_cases hle : i ≤ m
    · rw [ih i hle]
      have hne : i ≠ m + 1 := by omega
      rw [PowerSeries.coeff_X_pow]
      simp [hne]
    · have hEq : i = m + 1 := by omega
      subst hEq
      have h1 : PowerSeries.coeff (R := ℝ) (m + 1)
          (frobeniusPartialSum ps n z₁ ρ c₀ m) = 0 :=
        coeff_frobeniusPartialSum_gt ps n z₁ ρ c₀ m (m + 1) (by omega)
      rw [h1, PowerSeries.coeff_X_pow]
      simp

/-- **Annihilation at one level.** Under the simple-zero hypothesis and
non-resonance at level `m + 1`, the partial sum through index `m + 1`
zeroes out the `(m + 2)`-th coefficient of the substituted series. -/
theorem coeff_frobeniusPartialSum_annihilates
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hnr : simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0) :
    PowerSeries.coeff (R := ℝ) (m + 1 + 1)
        (substLHSGen ps (n + 1) z₁ ρ
          (frobeniusPartialSum ps n z₁ ρ c₀ (m + 1))) = 0 := by
  set P := simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
      (ρ + ((m + 1 : ℕ) : ℝ)) with hP
  set gₘ := frobeniusPartialSum ps n z₁ ρ c₀ m with hgm
  set g := frobeniusPartialSum ps n z₁ ρ c₀ (m + 1) with hg
  set a : ℝ := frobeniusCoeff ps n z₁ ρ c₀ (m + 1) with ha
  have ha_def : a = - PowerSeries.coeff (R := ℝ) (m + 1 + 1)
      (substLHSGen ps (n + 1) z₁ ρ gₘ) / (((-1 : ℝ) ^ n) * P) := by
    simp [ha, frobeniusCoeff, frobeniusBuilder, hgm, frobeniusPartialSum, hP]
  have hg_eq : g = gₘ + a • ((PowerSeries.X : PowerSeries ℝ) ^ (m + 1)) := by
    rw [hg, hgm, ha]; exact frobeniusPartialSum_succ ps n z₁ ρ c₀ m
  have hcoeff_m1 : PowerSeries.coeff (R := ℝ) (m + 1) g = a := by
    rw [hg, ha]
    exact coeff_frobeniusPartialSum_le ps n z₁ ρ c₀ (m + 1) (m + 1) le_rfl
  have hg_sub : g - PowerSeries.coeff (R := ℝ) (m + 1) g •
      ((PowerSeries.X : PowerSeries ℝ) ^ (m + 1)) = gₘ := by
    rw [hcoeff_m1, hg_eq]; ring
  have hextract :
      PowerSeries.coeff (R := ℝ) (m + 1 + 1) (substLHSGen ps (n + 1) z₁ ρ g) =
        ((-1 : ℝ) ^ n) * P * PowerSeries.coeff (R := ℝ) (m + 1) g +
        PowerSeries.coeff (R := ℝ) (m + 1 + 1) (substLHSGen ps (n + 1) z₁ ρ gₘ) := by
    have := coeff_succ_substLHSGen_leading_extract ps n z₁ ρ (m + 1) g hpk
    rw [this, hg_sub]
  rw [hextract, hcoeff_m1]
  have hdenom : ((-1 : ℝ) ^ n) * P ≠ 0 := by
    have hpow : ((-1 : ℝ) ^ n) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    exact mul_ne_zero hpow hnr
  have hkey : ((-1 : ℝ) ^ n) * P * a =
      - PowerSeries.coeff (R := ℝ) (m + 1 + 1)
          (substLHSGen ps (n + 1) z₁ ρ gₘ) := by
    rw [ha_def, mul_div_assoc', mul_neg, neg_div,
        mul_div_cancel_left₀ _ hdenom]
  linarith [hkey]

/-- The limit Frobenius series with coefficients given by the
recurrence. This is the candidate local solution of the ODE at the
regular singular point `z₁` for the indicial exponent `ρ`. -/
noncomputable def frobeniusSolution
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (frobeniusCoeff ps n z₁ ρ c₀)

@[simp] lemma coeff_frobeniusSolution
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ) :
    PowerSeries.coeff (R := ℝ) m (frobeniusSolution ps n z₁ ρ c₀) =
      frobeniusCoeff ps n z₁ ρ c₀ m := by
  simp [frobeniusSolution]

@[simp] lemma coeff_zero_frobeniusSolution
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    PowerSeries.coeff (R := ℝ) 0 (frobeniusSolution ps n z₁ ρ c₀) = c₀ := by
  simp

/-- The solution and the partial sum through index `m` agree on
coefficients `0..m`. Used together with `coeff_succ_substLHSGen_congr_low`
to lift level annihilation from partial sums to the limit series. -/
lemma coeff_frobeniusSolution_eq_partialSum_of_le
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m i : ℕ) (hi : i ≤ m) :
    PowerSeries.coeff (R := ℝ) i (frobeniusSolution ps n z₁ ρ c₀) =
      PowerSeries.coeff (R := ℝ) i (frobeniusPartialSum ps n z₁ ρ c₀ m) := by
  rw [coeff_frobeniusSolution,
      coeff_frobeniusPartialSum_le ps n z₁ ρ c₀ m i hi]

/-- **Full Frobenius annihilation at positive levels.** Under the
simple-zero hypothesis and non-resonance at level `M + 1`, the limit
series `frobeniusSolution` zeroes out `coeff (M + 2)` of the substitution
for every `M ≥ 0`. Equivalently, `coeff (m + 1) S(frobeniusSolution) = 0`
for every `m ≥ 1`. -/
theorem coeff_frobeniusSolution_annihilates_succ
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hnr : simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0) :
    PowerSeries.coeff (R := ℝ) (m + 1 + 1)
        (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) = 0 := by
  have hcongr :
      PowerSeries.coeff (R := ℝ) (m + 1 + 1)
          (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) =
      PowerSeries.coeff (R := ℝ) (m + 1 + 1)
          (substLHSGen ps (n + 1) z₁ ρ
            (frobeniusPartialSum ps n z₁ ρ c₀ (m + 1))) := by
    apply coeff_succ_substLHSGen_congr_low ps n z₁ ρ (m + 1) _ _ hpk
    intro i hi
    exact coeff_frobeniusSolution_eq_partialSum_of_le ps n z₁ ρ c₀ (m + 1) i hi
  rw [hcongr]
  exact coeff_frobeniusPartialSum_annihilates ps n z₁ ρ c₀ m hpk hnr

/-- Level-0 annihilation for the Frobenius solution: follows directly
from the simple-zero of `p_{n+1}` at `z₁`. -/
lemma coeff_zero_substLHSGen_frobeniusSolution
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    PowerSeries.coeff (R := ℝ) 0
        (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) = 0 :=
  coeff_zero_substLHSGen_simpleZero ps n z₁ ρ
    (frobeniusSolution ps n z₁ ρ c₀) hpk

/-- Level-1 annihilation for the Frobenius solution: follows from the
simple-zero of `p_{n+1}` together with `ρ` being a root of the indicial
polynomial `simpleZeroIndicialPoly (ps n) (ps (n+1)) z₁ n (·)`. -/
lemma coeff_one_substLHSGen_frobeniusSolution
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ = 0) :
    PowerSeries.coeff (R := ℝ) 1
        (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) = 0 := by
  have hcongr :
      PowerSeries.coeff (R := ℝ) 1
          (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) =
      PowerSeries.coeff (R := ℝ) 1
          (substLHSGen ps (n + 1) z₁ ρ
            (frobeniusPartialSum ps n z₁ ρ c₀ 0)) := by
    apply coeff_succ_substLHSGen_congr_low ps n z₁ ρ 0 _ _ hpk
    intro i hi
    exact coeff_frobeniusSolution_eq_partialSum_of_le ps n z₁ ρ c₀ 0 i hi
  rw [hcongr]
  have hg : frobeniusPartialSum ps n z₁ ρ c₀ 0 = PowerSeries.C (R := ℝ) c₀ := rfl
  rw [hg]
  have hextract :=
    coeff_succ_substLHSGen_leading_extract ps n z₁ ρ 0
      (PowerSeries.C (R := ℝ) c₀) hpk
  have hcoeff0 : PowerSeries.coeff (R := ℝ) 0 (PowerSeries.C (R := ℝ) c₀) = c₀ := by
    simp
  have hsub : (PowerSeries.C (R := ℝ) c₀) -
      (PowerSeries.coeff (R := ℝ) 0 (PowerSeries.C (R := ℝ) c₀)) •
        ((PowerSeries.X : PowerSeries ℝ) ^ 0) = 0 := by
    rw [hcoeff0, pow_zero]
    ext k
    rcases eq_or_ne k 0 with hk | hk
    · subst hk; simp
    · simp [PowerSeries.coeff_C, hk]
  rw [hextract, hsub]
  simp [hcoeff0, hindicial]

/-- **Frobenius existence.** Under
* the simple-zero hypothesis `(ps (n+1))(z₁) = 0`,
* the indicial root hypothesis `simpleZeroIndicialPoly (ps n) (ps (n+1)) z₁ n ρ = 0`,
* non-resonance at every positive integer shift,

the formal series `frobeniusSolution ps n z₁ ρ c₀` annihilates every
coefficient of `substLHSGen ps (n+1) z₁ ρ` and has constant term `c₀`. -/
theorem frobeniusSolution_is_solution
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + (m : ℝ)) ≠ 0) :
    PowerSeries.coeff (R := ℝ) 0 (frobeniusSolution ps n z₁ ρ c₀) = c₀ ∧
    ∀ k, PowerSeries.coeff (R := ℝ) k
        (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) = 0 := by
  refine ⟨by simp, ?_⟩
  intro k
  match k with
  | 0 => exact coeff_zero_substLHSGen_frobeniusSolution ps n z₁ ρ c₀ hpk
  | 1 => exact coeff_one_substLHSGen_frobeniusSolution ps n z₁ ρ c₀ hpk hindicial
  | m + 2 =>
    have hnr' := hnr (m + 1) (by omega)
    have hcast : ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := rfl
    exact coeff_frobeniusSolution_annihilates_succ ps n z₁ ρ c₀ m hpk hnr'

open PowerSeries in
/-- **Frobenius recurrence as a linear combination of prior coefficients.**
The `(m+1)`-th Frobenius coefficient unrolls to a weighted sum of the
earlier coefficients `frobeniusCoeff i` for `i ∈ [0, m]`, where each
weight is `coeff (m+2) (substLHSGen ps (n+1) z₁ ρ (X^i))` (the action of
the substitution operator on the monomial `X^i`), divided by the
negated indicial denominator `(-1)^n · P(ρ + (m+1))`.

This is the explicit linear form of the Frobenius recurrence, suitable
for coefficient-growth estimates in the analytic half of STRATEGY Step 3
(convergence of the formal series). -/
theorem frobeniusCoeff_succ_linear_combination
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0) :
    frobeniusCoeff ps n z₁ ρ c₀ (m + 1) =
      - (∑ i ∈ Finset.range (m + 1),
            frobeniusCoeff ps n z₁ ρ c₀ i *
              coeff (R := ℝ) (m + 1 + 1)
                (substLHSGen ps (n + 1) z₁ ρ ((X : PowerSeries ℝ) ^ i))) /
        (((-1 : ℝ) ^ n) *
          simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
            (ρ + ((m + 1 : ℕ) : ℝ))) := by
  -- Unfold the builder definition of frobeniusCoeff at m+1.
  have hdef :
      frobeniusCoeff ps n z₁ ρ c₀ (m + 1) =
        - coeff (R := ℝ) (m + 1 + 1)
            (substLHSGen ps (n + 1) z₁ ρ
              (frobeniusPartialSum ps n z₁ ρ c₀ m)) /
          (((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))) := by
    simp [frobeniusCoeff, frobeniusBuilder, frobeniusPartialSum]
  rw [hdef]
  congr 1
  congr 1
  -- Apply linearity to the substitution of partialSum_m.
  rw [coeff_succ_substLHSGen_linearity ps n z₁ ρ (m + 1)
        (frobeniusPartialSum ps n z₁ ρ c₀ m) hpk]
  -- Split off the i = m+1 term (which vanishes since partialSum.coeff(m+1) = 0).
  rw [Finset.sum_range_succ]
  have hzero :
      coeff (R := ℝ) (m + 1) (frobeniusPartialSum ps n z₁ ρ c₀ m) = 0 :=
    coeff_frobeniusPartialSum_gt ps n z₁ ρ c₀ m (m + 1) (by omega)
  rw [hzero, zero_mul, add_zero]
  -- Replace partialSum.coeff(i) with frobeniusCoeff(i) for i ∈ [0, m].
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_le : i ≤ m := by
    have := Finset.mem_range.mp hi; omega
  rw [coeff_frobeniusPartialSum_le ps n z₁ ρ c₀ m i hi_le]

/-- **Frobenius series rigidity at the indicial recurrence.** Any
sequence `b : ℕ → ℝ` satisfying `b 0 = c₀` together with the same
linear recurrence as `frobeniusCoeff_succ_linear_combination` must equal
`frobeniusCoeff ps n z₁ ρ c₀` pointwise. This is the analytic-uniqueness
kernel: it says that the indicial recurrence pins down a single
power-series solution from its leading term. -/
theorem frobeniusCoeff_unique_of_recurrence
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (b : ℕ → ℝ) (h0 : b 0 = c₀)
    (hrec : ∀ m,
      b (m + 1) =
        -(∑ i ∈ Finset.range (m + 1),
              b i *
                PowerSeries.coeff (R := ℝ) (m + 1 + 1)
                  (substLHSGen ps (n + 1) z₁ ρ
                    ((PowerSeries.X : PowerSeries ℝ) ^ i))) /
          (((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ)))) :
    ∀ m, b m = frobeniusCoeff ps n z₁ ρ c₀ m := by
  have aux : ∀ m i, i ≤ m → b i = frobeniusCoeff ps n z₁ ρ c₀ i := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have : i = 0 := Nat.le_zero.mp hi
      subst this
      rw [h0, frobeniusCoeff_zero]
    | succ k ih =>
      intro i hi
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · exact ih i (Nat.lt_succ_iff.mp hlt)
      · subst heq
        rw [hrec k, frobeniusCoeff_succ_linear_combination ps n z₁ ρ c₀ k hpk]
        congr 1
        congr 1
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_lt : j < k + 1 := Finset.mem_range.mp hj
        rw [ih j (Nat.lt_succ_iff.mp hj_lt)]
  intro m; exact aux m m (le_refl _)

/-- **Frobenius coefficients are ℝ-linear in the indicial leading term.**
The recurrence is homogeneous: scaling the seed `c₀` by `c` scales every
coefficient by the same `c`. Proved by appealing to the rigidity lemma
`frobeniusCoeff_unique_of_recurrence` with the candidate sequence
`b m := c * frobeniusCoeff … c₀ m`. -/
lemma frobeniusCoeff_smul_c₀
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (m : ℕ) :
    frobeniusCoeff ps n z₁ ρ (c * c₀) m =
      c * frobeniusCoeff ps n z₁ ρ c₀ m := by
  symm
  refine frobeniusCoeff_unique_of_recurrence ps n z₁ ρ (c * c₀) hpk
    (fun k => c * frobeniusCoeff ps n z₁ ρ c₀ k)
    ?_ ?_ m
  · simp [frobeniusCoeff_zero]
  · intro k
    change c * frobeniusCoeff ps n z₁ ρ c₀ (k + 1) = _
    rw [frobeniusCoeff_succ_linear_combination ps n z₁ ρ c₀ k hpk]
    set D : ℝ := ((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + ((k + 1 : ℕ) : ℝ))
    set W : ℕ → ℝ := fun i =>
      PowerSeries.coeff (R := ℝ) (k + 1 + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((PowerSeries.X : PowerSeries ℝ) ^ i))
    have hsum : c * (∑ i ∈ Finset.range (k + 1),
        frobeniusCoeff ps n z₁ ρ c₀ i * W i) =
        ∑ i ∈ Finset.range (k + 1),
          c * frobeniusCoeff ps n z₁ ρ c₀ i * W i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    change c * (- (∑ i ∈ Finset.range (k + 1),
        frobeniusCoeff ps n z₁ ρ c₀ i * W i) / D) =
        - (∑ i ∈ Finset.range (k + 1),
            c * frobeniusCoeff ps n z₁ ρ c₀ i * W i) / D
    rw [← hsum]; ring

/-- **Frobenius coefficients are additive in the indicial leading term.**
The recurrence is linear-homogeneous, so coefficients distribute over a
sum of seeds. Proved via `frobeniusCoeff_unique_of_recurrence` applied
to `b m := frobeniusCoeff … c₀₁ m + frobeniusCoeff … c₀₂ m`. -/
lemma frobeniusCoeff_add_c₀
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀₁ c₀₂ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (m : ℕ) :
    frobeniusCoeff ps n z₁ ρ (c₀₁ + c₀₂) m =
      frobeniusCoeff ps n z₁ ρ c₀₁ m + frobeniusCoeff ps n z₁ ρ c₀₂ m := by
  symm
  refine frobeniusCoeff_unique_of_recurrence ps n z₁ ρ (c₀₁ + c₀₂) hpk
    (fun k => frobeniusCoeff ps n z₁ ρ c₀₁ k + frobeniusCoeff ps n z₁ ρ c₀₂ k)
    ?_ ?_ m
  · simp [frobeniusCoeff_zero]
  · intro k
    change frobeniusCoeff ps n z₁ ρ c₀₁ (k + 1) + frobeniusCoeff ps n z₁ ρ c₀₂ (k + 1) = _
    rw [frobeniusCoeff_succ_linear_combination ps n z₁ ρ c₀₁ k hpk,
        frobeniusCoeff_succ_linear_combination ps n z₁ ρ c₀₂ k hpk]
    set D : ℝ := ((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + ((k + 1 : ℕ) : ℝ))
    set W : ℕ → ℝ := fun i =>
      PowerSeries.coeff (R := ℝ) (k + 1 + 1)
        (substLHSGen ps (n + 1) z₁ ρ ((PowerSeries.X : PowerSeries ℝ) ^ i))
    have hsum :
        (∑ i ∈ Finset.range (k + 1), frobeniusCoeff ps n z₁ ρ c₀₁ i * W i) +
          (∑ i ∈ Finset.range (k + 1), frobeniusCoeff ps n z₁ ρ c₀₂ i * W i) =
        ∑ i ∈ Finset.range (k + 1),
          (frobeniusCoeff ps n z₁ ρ c₀₁ i + frobeniusCoeff ps n z₁ ρ c₀₂ i) * W i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    change -(∑ i ∈ Finset.range (k + 1), frobeniusCoeff ps n z₁ ρ c₀₁ i * W i) / D
        + -(∑ i ∈ Finset.range (k + 1), frobeniusCoeff ps n z₁ ρ c₀₂ i * W i) / D =
      -(∑ i ∈ Finset.range (k + 1),
          (frobeniusCoeff ps n z₁ ρ c₀₁ i + frobeniusCoeff ps n z₁ ρ c₀₂ i) * W i) / D
    rw [← hsum]; ring

/-- **Frobenius coefficients vanish for the zero seed.** Direct corollary
of the homogeneous-linear smul lemma with `c = 0`. -/
@[simp] lemma frobeniusCoeff_zero_seed
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (m : ℕ) :
    frobeniusCoeff ps n z₁ ρ 0 m = 0 := by
  have h := frobeniusCoeff_smul_c₀ ps n z₁ ρ 0 0 hpk m
  rw [zero_mul] at h
  rw [h, zero_mul]

open PowerSeries in
/-- **Combined Frobenius recurrence bound (per-`i` form).** Applying the
polynomial growth bound on the weights to the explicit linear form of
the recurrence, the `(m+1)`-th Frobenius coefficient satisfies
```
|frobeniusCoeff (m+1)| · |D(m+1)| ≤
  Σ_{i≤m} |frobeniusCoeff i| · W_i
```
where `W_i = (n+2)·B·(|ρ+i|+(n+1))^{n+1}` is the per-`i` weight bound and
`D(m+1) = (-1)^n · P(ρ+(m+1))` is the indicial denominator. `B` is any
uniform Taylor-coefficient bound on `taylorShift (ps j) z₁` for
`j ∈ [0, n+1]`. Keeping the `i`-dependence in the sum is sharper than
pulling out a uniform bound and is needed for geometric majorant
arguments. -/
theorem abs_frobeniusCoeff_succ_bound
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hD : ((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0)
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      |((-1 : ℝ) ^ n) *
        simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
          (ρ + ((m + 1 : ℕ) : ℝ))| ≤
      ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          (((n + 2 : ℕ) : ℝ) * B *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
  rw [frobeniusCoeff_succ_linear_combination ps n z₁ ρ c₀ m hpk]
  rw [abs_div, abs_neg]
  have hD_abs_pos : 0 < |((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ))| := abs_pos.mpr hD
  rw [div_mul_cancel₀ _ (ne_of_gt hD_abs_pos)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_le : i ≤ m := by
    have := Finset.mem_range.mp hi; omega
  rw [abs_mul]
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ i| := abs_nonneg _
  have hwbound :=
    abs_coeff_succ_substLHSGen_X_pow_bound ps n z₁ ρ (m + 1) i
      (by omega) B hB_nn hB
  -- hwbound: |coeff (m+1+1) S(X^i)| ≤ (n+2)·B·(|ρ+i|+(n+1))^{n+1}
  exact mul_le_mul_of_nonneg_left hwbound h_abs_a_nn

open PowerSeries in
/-- **Per-`j` sharpened version of `abs_frobeniusCoeff_succ_bound`.**
Replaces the uniform Taylor-coefficient bound `B` by per-`j` bounds
`Bj` on `taylorShift (ps j) z₁`. The per-summand weight becomes
`(Σ_j Bj)·(|ρ+i|+(n+1))^{n+1}` instead of `(n+2)·B·(...)^{n+1}`,
which is strictly tighter when some `Bj < max_j Bj` (e.g. at the
Apéry conifold the per-`j` form gives a `2×` sharper Gronwall bound,
since `B_0 = B_1 = 0`). -/
theorem abs_frobeniusCoeff_succ_bound_per_j
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hD : ((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0)
    (Bj : ℕ → ℝ)
    (hBj_nn : ∀ j ∈ Finset.range (n + 2), 0 ≤ Bj j)
    (hBj : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ Bj j) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      |((-1 : ℝ) ^ n) *
        simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
          (ρ + ((m + 1 : ℕ) : ℝ))| ≤
      ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          ((∑ j ∈ Finset.range (n + 2), Bj j) *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
  rw [frobeniusCoeff_succ_linear_combination ps n z₁ ρ c₀ m hpk]
  rw [abs_div, abs_neg]
  have hD_abs_pos : 0 < |((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ))| := abs_pos.mpr hD
  rw [div_mul_cancel₀ _ (ne_of_gt hD_abs_pos)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_le : i ≤ m := by
    have := Finset.mem_range.mp hi; omega
  rw [abs_mul]
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ i| := abs_nonneg _
  have hwbound :=
    abs_coeff_succ_substLHSGen_X_pow_bound_per_j ps n z₁ ρ (m + 1) i
      (by omega) Bj hBj_nn hBj
  exact mul_le_mul_of_nonneg_left hwbound h_abs_a_nn

/-! ## Elementary affine lower bound -/

/-- **Affine lower bound.** Whenever `|x|` is large enough that
`|b|·|x|` dominates twice `|a|`, the linear combination
`a + b·x` has absolute value at least `|b|·|x| / 2`.

Proof: `|b·x| = |(a + b·x) + (-a)| ≤ |a + b·x| + |a|`, so
`|a + b·x| ≥ |b|·|x| - |a| ≥ |b|·|x| / 2`. -/
lemma abs_affine_ge_of_large (a b x : ℝ)
    (hx : 2 * |a| ≤ |b| * |x|) :
    |b| * |x| / 2 ≤ |a + b * x| := by
  have h1 : |b * x| ≤ |a + b * x| + |a| := by
    have hineq : |(a + b * x) + (-a)| ≤ |a + b * x| + |(-a)| :=
      abs_add_le _ _
    have heq : (a + b * x) + (-a) = b * x := by ring
    rw [heq, abs_neg] at hineq
    exact hineq
  rw [abs_mul] at h1
  linarith

/-- **Polynomial-growth lower bound on the indicial polynomial (simple-zero case).**

Under the Frobenius hypothesis `pₙ(z₁) = 0` (regular singular point with
simple zero of the leading coefficient), the indicial polynomial at the
shifted argument `ρ + (m+1)` has absolute value at least
`((m+1) − |ρ| − n)^{n+1} · |p_{n+1}'(z₁)|` whenever `|ρ| + n < m + 1`.

This is the denominator lower bound feeding the Frobenius geometric
majorant: it turns the Gronwall-style recurrence into a geometric bound
`|a_m| ≤ M · R^m`. -/
lemma simpleZeroIndicialPoly_abs_lower_bound_simple_zero
    (pn pn1 : Polynomial ℝ) (z₁ : ℝ) (n : ℕ) (ρ : ℝ) (m : ℕ)
    (hpn : pn.eval z₁ = 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ)) :
    (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1)
      * |(Polynomial.derivative pn1).eval z₁| ≤
    |simpleZeroIndicialPoly pn pn1 z₁ n (ρ + ((m + 1 : ℕ) : ℝ))| := by
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hMdef
  have hff : (M - |ρ| - (n : ℝ)) ^ n ≤ fallingFactorial (ρ + M) n :=
    fallingFactorial_shifted_lower_bound ρ n (m + 1) hm
  have hΔ_pos : 0 < M - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hΔ_nn : 0 ≤ M - |ρ| - (n : ℝ) := le_of_lt hΔ_pos
  have hrin : M - |ρ| - (n : ℝ) ≤ (ρ + M) - (n : ℝ) := by
    have hρ_ge : -ρ ≤ |ρ| := neg_le_abs ρ
    linarith
  have hrin_pos : 0 < (ρ + M) - (n : ℝ) := lt_of_lt_of_le hΔ_pos hrin
  have hff_nn : 0 ≤ fallingFactorial (ρ + M) n :=
    le_trans (pow_nonneg hΔ_nn n) hff
  have hE_nn : 0 ≤ |(Polynomial.derivative pn1).eval z₁| := abs_nonneg _
  rw [simpleZeroIndicialPoly_factor, hpn, zero_add]
  rw [abs_mul, abs_mul, abs_of_nonneg hff_nn, abs_of_pos hrin_pos]
  rw [pow_succ]
  have hprod :
      (M - |ρ| - (n : ℝ)) ^ n * (M - |ρ| - (n : ℝ)) ≤
        fallingFactorial (ρ + M) n * ((ρ + M) - (n : ℝ)) :=
    mul_le_mul hff hrin hΔ_nn hff_nn
  nlinarith [hprod, hE_nn]

/-- **Gronwall-form recurrence bound (simple-zero case).**

Combining `abs_frobeniusCoeff_succ_bound` (the raw recurrence inequality
with `|D(m+1)|` on the LHS) with the denominator lower bound
`simpleZeroIndicialPoly_abs_lower_bound_simple_zero`, we get a clean
Gronwall-style inequality:

  |a_{m+1}| · ((m+1 − |ρ| − n)^{n+1} · |p_{n+1}'(z₁)|) ≤
    ∑_{i=0}^m |a_i| · ((n+2)·B · (|ρ+i| + (n+1))^{n+1}).

Hypotheses:
- `hpk : (pₙ₊₁)(z₁) = 0` — regular singular point
- `hpn : pₙ(z₁) = 0` — simple-zero assumption making the denominator
  factor through the product form
- `hslope : pₙ₊₁'(z₁) ≠ 0` — non-degeneracy (the effective leading
  coefficient is exactly `pₙ₊₁'(z₁) · (ρ + m + 1 − n)`)
- `hm : |ρ| + n < m + 1` — large-m regime where the falling factorial
  is positive
- `B` is a uniform Taylor-coefficient bound on the shifted polynomials.

This inequality turns the Frobenius recurrence into something ready for
a geometric majorant: the LHS grows like `m^{n+1}` while each
per-summand weight grows like `(m+n+1)^{n+1}`, giving a bounded ratio. -/
theorem abs_frobeniusCoeff_succ_gronwall_simple_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      ((((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          (((n + 2 : ℕ) : ℝ) * B *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
  set L : ℝ := (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hLdef
  have hLB :
      L ≤ |simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
             (ρ + ((m + 1 : ℕ) : ℝ))| :=
    simpleZeroIndicialPoly_abs_lower_bound_simple_zero
      (ps n) (ps (n + 1)) z₁ n ρ m hpn hm
  have hΔ_pos : 0 < ((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hL_pos : 0 < L := by
    have h1 : 0 < (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) :=
      pow_pos hΔ_pos _
    have h2 : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
      abs_pos.mpr hslope
    exact mul_pos h1 h2
  have habs_neg_one_pow : |((-1 : ℝ) ^ n)| = 1 := by
    rw [abs_pow]; simp
  have hD_abs :
      L ≤ |((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))| := by
    rw [abs_mul, habs_neg_one_pow, one_mul]
    exact hLB
  have hD_ne : ((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0 := by
    intro h
    have hzero : |((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ))| = 0 := by rw [h]; exact abs_zero
    linarith
  have hmain :=
    abs_frobeniusCoeff_succ_bound ps n z₁ ρ c₀ m hpk hD_ne B hB_nn hB
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
  have hLHS :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * L ≤
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
          |((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))| :=
    mul_le_mul_of_nonneg_left hD_abs h_abs_a_nn
  exact le_trans hLHS hmain

/-- **Per-`j` sharpened Gronwall (simple-zero).** Same statement as
`abs_frobeniusCoeff_succ_gronwall_simple_zero` but with per-`j` Taylor
bounds `Bj` in place of a uniform `B`. The per-summand weight tightens
to `(Σ_j Bj)·(|ρ+i|+(n+1))^{n+1}`, which at the Apéry conifold halves
the constant (B_0 = B_1 = 0). -/
theorem abs_frobeniusCoeff_succ_gronwall_simple_zero_per_j
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (Bj : ℕ → ℝ)
    (hBj_nn : ∀ j ∈ Finset.range (n + 2), 0 ≤ Bj j)
    (hBj : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ Bj j) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      ((((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          ((∑ j ∈ Finset.range (n + 2), Bj j) *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
  set L : ℝ := (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hLdef
  have hLB :
      L ≤ |simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
             (ρ + ((m + 1 : ℕ) : ℝ))| :=
    simpleZeroIndicialPoly_abs_lower_bound_simple_zero
      (ps n) (ps (n + 1)) z₁ n ρ m hpn hm
  have hΔ_pos : 0 < ((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hL_pos : 0 < L := by
    have h1 : 0 < (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) :=
      pow_pos hΔ_pos _
    have h2 : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
      abs_pos.mpr hslope
    exact mul_pos h1 h2
  have habs_neg_one_pow : |((-1 : ℝ) ^ n)| = 1 := by
    rw [abs_pow]; simp
  have hD_abs :
      L ≤ |((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))| := by
    rw [abs_mul, habs_neg_one_pow, one_mul]
    exact hLB
  have hD_ne : ((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0 := by
    intro h
    have hzero : |((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ))| = 0 := by rw [h]; exact abs_zero
    linarith
  have hmain :=
    abs_frobeniusCoeff_succ_bound_per_j ps n z₁ ρ c₀ m hpk hD_ne Bj hBj_nn hBj
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
  have hLHS :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * L ≤
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
          |((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))| :=
    mul_le_mul_of_nonneg_left hD_abs h_abs_a_nn
  exact le_trans hLHS hmain

/-- Elementary inequality: for `i : ℕ`, `|ρ + i| ≤ |ρ| + i`. -/
lemma abs_shift_add_nat_le (ρ : ℝ) (i : ℕ) :
    |ρ + (i : ℝ)| ≤ |ρ| + (i : ℝ) := by
  have h : |ρ + (i : ℝ)| ≤ |ρ| + |(i : ℝ)| := abs_add_le ρ ((i : ℝ))
  have hi_abs : |(i : ℝ)| = (i : ℝ) := abs_of_nonneg (Nat.cast_nonneg i)
  linarith

/-- **Uniform weight bound across summands.** Every per-summand weight
`(|ρ + i| + (n+1))^{n+1}` for `i ≤ m` is dominated by the fixed
quantity `(|ρ| + m + (n+1))^{n+1}`. -/
lemma weight_poly_uniform_bound
    (ρ : ℝ) (n i m : ℕ) (hi : i ≤ m) :
    (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
    (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  refine pow_le_pow_left₀ ?_ ?_ _
  · have h1 : (0 : ℝ) ≤ |ρ + (i : ℝ)| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  · have h1 : |ρ + (i : ℝ)| ≤ |ρ| + (i : ℝ) := abs_shift_add_nat_le ρ i
    have h2 : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
    linarith

/-- **Gronwall inequality with uniform weight.** Combining the
simple-zero Gronwall bound with the uniform weight dominance, we factor
the polynomial weight out of the sum:

  |a_{m+1}| · ((m+1 − |ρ| − n)^{n+1} · |pₙ₊₁'(z₁)|) ≤
    ((n+2)·B · (|ρ| + m + (n+1))^{n+1}) · Σᵢ₌₀^m |aᵢ|.

This is the definitive Gronwall-form recurrence: the weight factor
becomes `m`-dependent but uniform in `i`, so the ratio against the
denominator's `(m+1 − |ρ| − n)^{n+1}` tends to the constant
`|pₙ₊₁'(z₁)|⁻¹` as `m → ∞`, yielding a bounded contraction constant. -/
theorem abs_frobeniusCoeff_succ_gronwall_uniform
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      ((((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      ((n + 2 : ℕ) : ℝ) * B *
        (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) *
        ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| := by
  have hG := abs_frobeniusCoeff_succ_gronwall_simple_zero
    ps n z₁ ρ c₀ m hpk hpn hslope hm B hB_nn hB
  refine le_trans hG ?_
  set C : ℝ := ((n + 2 : ℕ) : ℝ) * B *
                (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) with hCdef
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact hB_nn
    · apply pow_nonneg
      have h1 : (0 : ℝ) ≤ |ρ| := abs_nonneg _
      have h2 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_le : i ≤ m := by
    have := Finset.mem_range.mp hi; omega
  have hwbd : (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
              (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
    weight_poly_uniform_bound ρ n i m hi_le
  have hCoeff_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B := by
    apply mul_nonneg
    · positivity
    · exact hB_nn
  have hInner :
      ((n + 2 : ℕ) : ℝ) * B *
        (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
      ((n + 2 : ℕ) : ℝ) * B *
        (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hwbd hCoeff_nn
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ i| := abs_nonneg _
  have := mul_le_mul_of_nonneg_left hInner h_abs_a_nn
  -- this: |aᵢ| * (C·(|ρ+i|+(n+1))^{n+1}) ≤ |aᵢ| * C
  -- goal wants: |aᵢ| * (C · (|ρ+i|+(n+1))^{n+1}) ≤ C * |aᵢ|
  -- rearrange
  linarith [this, h_abs_a_nn, hC_nn]

/-- **Per-`j` sharpened uniform Gronwall.** Same as
`abs_frobeniusCoeff_succ_gronwall_uniform` but with per-`j` Taylor
bounds `Bj`. The constant `(n+2)·B` becomes `Σ_j Bj`, which is
strictly tighter when some `Bj < max_j Bj`. At the Apéry conifold
this gives `Σ_j Bj = 306` instead of `(n+2)·B = 612` (using
`B_2 = B_3 = 153`, `B_0 = B_1 = 0`). -/
theorem abs_frobeniusCoeff_succ_gronwall_uniform_per_j
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (Bj : ℕ → ℝ)
    (hBj_nn : ∀ j ∈ Finset.range (n + 2), 0 ≤ Bj j)
    (hBj : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ Bj j) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      ((((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      (∑ j ∈ Finset.range (n + 2), Bj j) *
        (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) *
        ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| := by
  have hG := abs_frobeniusCoeff_succ_gronwall_simple_zero_per_j
    ps n z₁ ρ c₀ m hpk hpn hslope hm Bj hBj_nn hBj
  refine le_trans hG ?_
  set S : ℝ := ∑ j ∈ Finset.range (n + 2), Bj j with hSdef
  have hS_nn : 0 ≤ S := by
    apply Finset.sum_nonneg
    exact hBj_nn
  set C : ℝ := S * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) with hCdef
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg hS_nn
    apply pow_nonneg
    have h1 : (0 : ℝ) ≤ |ρ| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_le : i ≤ m := by
    have := Finset.mem_range.mp hi; omega
  have hwbd : (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
              (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
    weight_poly_uniform_bound ρ n i m hi_le
  have hInner :
      S * (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
      S * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hwbd hS_nn
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ i| := abs_nonneg _
  have := mul_le_mul_of_nonneg_left hInner h_abs_a_nn
  linarith [this, h_abs_a_nn, hC_nn]

/-- Elementary arithmetic: once `m` dominates `3|ρ| + 3n`, the ratio
between the numerator-base `|ρ| + m + (n+1)` and the denominator-base
`m + 1 − |ρ| − n` is bounded by `2`.

Explicit calculation: the inequality `|ρ| + m + n + 1 ≤ 2(m + 1 − |ρ| − n)`
rearranges to `3|ρ| + 3n ≤ m + 1`, which follows from `3|ρ| + 3n ≤ m`. -/
lemma base_ratio_le_two
    (ρ : ℝ) (n m : ℕ)
    (hm : 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ)) :
    |ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ) ≤
    2 * (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) := by
  have hcast1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hcast2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast1, hcast2]
  linarith

/-- **Polynomial ratio bound.** Taking the `(n+1)`-th power of
`base_ratio_le_two` shows that the polynomial weight grows at most
`2^{n+1}` times faster than the denominator factor, once `m` is
sufficiently large. -/
lemma weight_to_denominator_pow_bounded
    (ρ : ℝ) (n m : ℕ)
    (hm : 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ)) :
    (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
    ((2 : ℝ) ^ (n + 1)) *
      (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) := by
  have hbase := base_ratio_le_two ρ n m hm
  have h_nn : 0 ≤ |ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) ≤ |ρ| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hpow : (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
              (2 * (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ))) ^ (n + 1) :=
    pow_le_pow_left₀ h_nn hbase _
  rw [mul_pow] at hpow
  exact hpow

/-- **Contracted Frobenius recurrence bound.** Dividing out the
polynomial factor `(m + 1 − |ρ| − n)^{n+1}` from the uniform Gronwall
inequality using `weight_to_denominator_pow_bounded` yields the clean
contraction bound

  |a_{m+1}| · |pₙ₊₁'(z₁)| ≤ (n+2)·B · 2^{n+1} · Σᵢ₌₀^m |aᵢ|.

Valid for `m` exceeding both the simple-zero threshold
`|ρ| + n < m + 1` and the ratio threshold `3|ρ| + 3n ≤ m`.

This is the key Gronwall-iteration step: from here, setting
`K := (n+2)·B·2^{n+1}/|pₙ₊₁'(z₁)|` gives `|a_{m+1}| ≤ K · Σᵢ |aᵢ|`,
which chains into a geometric majorant `|a_m| ≤ M·(1+K)^m`. -/
theorem abs_frobeniusCoeff_succ_contracted
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm_small : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hm_large : 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      |(Polynomial.derivative (ps (n + 1))).eval z₁| ≤
      ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) *
        ∑ i ∈ Finset.range (m + 1),
          |frobeniusCoeff ps n z₁ ρ c₀ i| := by
  have hG := abs_frobeniusCoeff_succ_gronwall_uniform
    ps n z₁ ρ c₀ m hpk hpn hslope hm_small B hB_nn hB
  have hr := weight_to_denominator_pow_bounded ρ n m hm_large
  set Δpow : ℝ := (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) with hΔpow_def
  set S : ℝ :=
    ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| with hS_def
  set C : ℝ := ((n + 2 : ℕ) : ℝ) * B with hC_def
  have hΔ_pos : 0 < ((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hΔpow_pos : 0 < Δpow := pow_pos hΔ_pos _
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg
    · positivity
    · exact hB_nn
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_step1 :
      C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * S ≤
      C * ((2:ℝ)^(n+1) * Δpow) * S := by
    have h1 : C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
              C * ((2:ℝ)^(n+1) * Δpow) :=
      mul_le_mul_of_nonneg_left hr hC_nn
    exact mul_le_mul_of_nonneg_right h1 hS_nn
  have hG' :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      C * ((2:ℝ)^(n+1) * Δpow) * S :=
    le_trans hG h_step1
  have h_reassoc_L :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) =
      (|frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) * Δpow := by ring
  have h_reassoc_R :
      C * ((2:ℝ)^(n+1) * Δpow) * S =
      (C * (2:ℝ)^(n+1) * S) * Δpow := by ring
  rw [h_reassoc_L, h_reassoc_R] at hG'
  exact le_of_mul_le_mul_right hG' hΔpow_pos

/-- **Per-`j` sharpened contracted Frobenius.** Same as
`abs_frobeniusCoeff_succ_contracted` but with per-`j` Taylor bounds
`Bj`. Constant tightens from `(n+2)·B·2^{n+1}` to
`(Σ_j Bj)·2^{n+1}`. At the Apéry conifold (`B_0 = B_1 = 0`,
`B_2 = B_3 = 153`): `K_per_j` numerator `306·16 = 4896`, vs
`K_uniform` numerator `4·153·16 = 9792`. Same `2×` improvement that
propagates through all upstream layers. -/
theorem abs_frobeniusCoeff_succ_contracted_per_j
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm_small : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hm_large : 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (Bj : ℕ → ℝ)
    (hBj_nn : ∀ j ∈ Finset.range (n + 2), 0 ≤ Bj j)
    (hBj : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ Bj j) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      |(Polynomial.derivative (ps (n + 1))).eval z₁| ≤
      (∑ j ∈ Finset.range (n + 2), Bj j) * ((2 : ℝ) ^ (n + 1)) *
        ∑ i ∈ Finset.range (m + 1),
          |frobeniusCoeff ps n z₁ ρ c₀ i| := by
  have hG := abs_frobeniusCoeff_succ_gronwall_uniform_per_j
    ps n z₁ ρ c₀ m hpk hpn hslope hm_small Bj hBj_nn hBj
  have hr := weight_to_denominator_pow_bounded ρ n m hm_large
  set Δpow : ℝ := (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) with hΔpow_def
  set S : ℝ :=
    ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| with hS_def
  set C : ℝ := ∑ j ∈ Finset.range (n + 2), Bj j with hC_def
  have hΔ_pos : 0 < ((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hΔpow_pos : 0 < Δpow := pow_pos hΔ_pos _
  have hC_nn : 0 ≤ C := Finset.sum_nonneg hBj_nn
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_step1 :
      C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * S ≤
      C * ((2:ℝ)^(n+1) * Δpow) * S := by
    have h1 : C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
              C * ((2:ℝ)^(n+1) * Δpow) :=
      mul_le_mul_of_nonneg_left hr hC_nn
    exact mul_le_mul_of_nonneg_right h1 hS_nn
  have hG' :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      C * ((2:ℝ)^(n+1) * Δpow) * S :=
    le_trans hG h_step1
  have h_reassoc_L :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) =
      (|frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) * Δpow := by ring
  have h_reassoc_R :
      C * ((2:ℝ)^(n+1) * Δpow) * S =
      (C * (2:ℝ)^(n+1) * S) * Δpow := by ring
  rw [h_reassoc_L, h_reassoc_R] at hG'
  exact le_of_mul_le_mul_right hG' hΔpow_pos

/-- **Discrete Gronwall iteration.** Given a nonnegative sequence
`a : ℕ → ℝ` and a threshold `M₀` beyond which each term satisfies
`a_{m+1} ≤ K · S_m` (where `S_m := Σᵢ₌₀^m a_i`), the partial sums grow
at most geometrically with ratio `(1 + K)`:

  S_m ≤ S_{M₀} · (1 + K)^{m − M₀}   for all m ≥ M₀.

This is a pure combinatorial lemma, independent of the Frobenius
machinery — the contracted Frobenius bound
`abs_frobeniusCoeff_succ_contracted` instantiates it with
`a = |frobeniusCoeff …|` and `K = (n+2)·B·2^{n+1}/|pₙ₊₁'(z₁)|`. -/
lemma discrete_gronwall_iteration
    (a : ℕ → ℝ) (K : ℝ) (hK_nn : 0 ≤ K) (M₀ : ℕ)
    (h_rec : ∀ m, M₀ ≤ m →
        a (m + 1) ≤ K * ∑ i ∈ Finset.range (m + 1), a i) :
    ∀ m, M₀ ≤ m →
      (∑ i ∈ Finset.range (m + 1), a i) ≤
        (∑ i ∈ Finset.range (M₀ + 1), a i) * (1 + K) ^ (m - M₀) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have h_split :
        ∑ i ∈ Finset.range (k + 2), a i =
          (∑ i ∈ Finset.range (k + 1), a i) + a (k + 1) := by
      rw [Finset.sum_range_succ]
    rw [h_split]
    have h_a : a (k + 1) ≤ K * ∑ i ∈ Finset.range (k + 1), a i :=
      h_rec k hk
    have h_sum_combined :
        (∑ i ∈ Finset.range (k + 1), a i) + a (k + 1) ≤
          (1 + K) * ∑ i ∈ Finset.range (k + 1), a i := by linarith
    have h_one_plus_K_nn : 0 ≤ 1 + K := by linarith
    have h_chain :
        (1 + K) * ∑ i ∈ Finset.range (k + 1), a i ≤
          (1 + K) *
            ((∑ i ∈ Finset.range (M₀ + 1), a i) * (1 + K) ^ (k - M₀)) :=
      mul_le_mul_of_nonneg_left ih h_one_plus_K_nn
    have h_exp : k + 1 - M₀ = (k - M₀) + 1 := by omega
    calc (∑ i ∈ Finset.range (k + 1), a i) + a (k + 1)
        ≤ (1 + K) * ∑ i ∈ Finset.range (k + 1), a i := h_sum_combined
      _ ≤ (1 + K) *
            ((∑ i ∈ Finset.range (M₀ + 1), a i) * (1 + K) ^ (k - M₀)) :=
          h_chain
      _ = (∑ i ∈ Finset.range (M₀ + 1), a i) *
            (1 + K) ^ ((k - M₀) + 1) := by
          rw [pow_succ]; ring
      _ = (∑ i ∈ Finset.range (M₀ + 1), a i) *
            (1 + K) ^ (k + 1 - M₀) := by
          rw [h_exp]

/-- **Frobenius geometric majorant.** The full composition: applying
`discrete_gronwall_iteration` to the contracted Frobenius bound, we
obtain an explicit geometric majorant for the partial sums of
`|frobeniusCoeff|` beyond a threshold `M₀`:

  Σᵢ₌₀^m |aᵢ| ≤ Σᵢ₌₀^{M₀} |aᵢ| · (1 + K) ^ (m − M₀)

where `K = (n+2)·B·2^{n+1} / |pₙ₊₁'(z₁)|`.

The threshold `M₀` must dominate both the simple-zero regime
(`|ρ| + n < m + 1`) and the ratio regime (`3|ρ| + 3n ≤ m`); any such
`M₀` is legitimate and the assumption is phrased in that generality.

A pointwise consequence is `|a_m| ≤ M · (1 + K)^m` (take
`M := Σᵢ₌₀^{M₀}|aᵢ| · (1 + K)^{−M₀}`), giving a nonzero radius of
convergence of at least `1/(1+K)` for the Frobenius power series. -/
theorem frobeniusCoeff_sum_geometric_majorant
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    ∀ m, M₀ ≤ m →
      (∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i|) ≤
      (∑ i ∈ Finset.range (M₀ + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i|) *
          (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
            |(Polynomial.derivative (ps (n + 1))).eval z₁|) ^ (m - M₀) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact hB_nn
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have h_rec : ∀ m, M₀ ≤ m →
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| ≤
        K * ∑ i ∈ Finset.range (m + 1),
              |frobeniusCoeff ps n z₁ ρ c₀ i| := by
    intro m hm
    have h1 := hM0_small m hm
    have h2 := hM0_large m hm
    have h_contract := abs_frobeniusCoeff_succ_contracted
      ps n z₁ ρ c₀ m hpk hpn hslope h1 h2 B hB_nn hB
    have hK_rewrite :
        K * ∑ i ∈ Finset.range (m + 1),
              |frobeniusCoeff ps n z₁ ρ c₀ i| =
        (((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) *
          ∑ i ∈ Finset.range (m + 1),
            |frobeniusCoeff ps n z₁ ρ c₀ i|) /
        |(Polynomial.derivative (ps (n + 1))).eval z₁| := by
      change ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
            |(Polynomial.derivative (ps (n + 1))).eval z₁| * _ = _
      rw [div_mul_eq_mul_div]
    rw [hK_rewrite, le_div_iff₀ hslope_pos]
    exact h_contract
  intro m hm
  exact discrete_gronwall_iteration
    (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m|) K hK_nn M₀ h_rec m hm

/-- **Pointwise geometric bound** on `|frobeniusCoeff m|` for `m ≥ M₀`.
Follows from the partial-sum majorant via `Finset.single_le_sum`
(the `m`-th term is bounded by the partial sum up to `m`).

    |aₘ| ≤ Σᵢ₌₀^{M₀} |aᵢ| · (1 + K)^{m − M₀}

This is the shape that gives a positive radius of convergence
`≥ 1/(1+K)` for the Frobenius power series `Σₘ aₘ · tᵐ`: for any
`0 ≤ |t| < 1/(1+K)`, the series `Σₘ |aₘ|·|t|ᵐ` is dominated by a
geometric series with ratio `(1+K)·|t| < 1`. -/
theorem abs_frobeniusCoeff_pointwise_geometric
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    ∀ m, M₀ ≤ m →
      |frobeniusCoeff ps n z₁ ρ c₀ m| ≤
      (∑ i ∈ Finset.range (M₀ + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i|) *
        (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
          |(Polynomial.derivative (ps (n + 1))).eval z₁|) ^ (m - M₀) := by
  intro m hm
  have hsum :=
    frobeniusCoeff_sum_geometric_majorant
      ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB m hm
  have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have h_single :
      |frobeniusCoeff ps n z₁ ρ c₀ m| ≤
        ∑ i ∈ Finset.range (m + 1),
          |frobeniusCoeff ps n z₁ ρ c₀ i| :=
    Finset.single_le_sum (f := fun i => |frobeniusCoeff ps n z₁ ρ c₀ i|)
      (fun i _ => abs_nonneg _) hmem
  exact le_trans h_single hsum

/-- **Absolute summability on the Frobenius disk.** For any real `s`
with `0 ≤ s` and `s·(1 + K) < 1`, the series
`Σₘ |frobeniusCoeff m| · sᵐ` is summable. Here
`K = (n+2)·B·2^{n+1}/|pₙ₊₁'(z₁)|` is the geometric-majorant ratio
from `abs_frobeniusCoeff_pointwise_geometric`.

Proof idea: shift the tail by `M₀`, apply the pointwise geometric
bound, and compare term-by-term against the convergent geometric series
`C · rᵏ` with `r := s·(1+K) < 1` and `C := S_{M₀}·s^{M₀}`.

This is the bridge from the algebraic geometric bound to Mathlib's
analytic infrastructure: having `Summable` means the series has a
well-defined sum, and the series defines a continuous function on
`|s| < 1/(1+K)` with value `∑' m, aₘ · sᵐ`. -/
theorem frobeniusCoeff_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact hB_nn
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := mul_nonneg hSmaj_nn (pow_nonneg hs_nn _)
  -- Shift index by M₀: reduces to a summable tail
  rw [← summable_nat_add_iff M₀]
  -- Compare shifted tail with C · r^k
  refine Summable.of_nonneg_of_le ?_ ?_
    ((summable_geometric_of_lt_one hr_nn hr_lt_1).mul_left C)
  · intro k
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hs_nn _)
  · intro k
    have hpt := abs_frobeniusCoeff_pointwise_geometric
      ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB
      (k + M₀) (Nat.le_add_left M₀ k)
    have hsub : k + M₀ - M₀ = k := by omega
    rw [hsub] at hpt
    -- hpt: |a_{k+M₀}| ≤ Smaj * (1+K)^k
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have step1 :
        |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| * s ^ (k + M₀) ≤
          (Smaj * (1 + K) ^ k) * s ^ (k + M₀) :=
      mul_le_mul_of_nonneg_right hpt hs_pow_nn
    have step2 :
        (Smaj * (1 + K) ^ k) * s ^ (k + M₀) = C * r ^ k := by
      rw [hC_def, hr_def, mul_pow, pow_add]
      ring
    linarith [step1, step2.le, step2.ge]

/-- **Signed summability of the Frobenius series.** For real `s` with
`|s|·(1+K) < 1`, the signed series `Σₘ aₘ·sᵐ` is summable. Follows from
`frobeniusCoeff_abs_mul_pow_summable` (applied at `|s|`) via
`Summable.of_norm`: absolute summability of a real-valued series
implies summability. -/
theorem frobeniusCoeff_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ)
    (hs_lt : |s| * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m => frobeniusCoeff ps n z₁ ρ c₀ m * s ^ m) := by
  have habs :=
    frobeniusCoeff_abs_mul_pow_summable ps n z₁ ρ c₀ M₀ hpk hpn hslope
      hM0_small hM0_large B hB_nn hB |s| (abs_nonneg s) hs_lt
  apply Summable.of_norm
  convert habs using 1
  funext m
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

/-- **Frobenius series value function.** For any `t` in the convergence
disk `|t|·(1+K) < 1`, the Frobenius series has a well-defined sum. We
package this as a function `frobeniusValue` defined on all of `ℝ` (with
the convention that outside the convergence disk, the `tsum` may return
`0` by Mathlib's default for non-summable series). -/
noncomputable def frobeniusValue
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (t : ℝ) : ℝ :=
  ∑' m, frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m

/-- **Initial condition at `t = 0`.** The Frobenius series sum at `t = 0`
is exactly the seed constant `c₀`. This follows from the `tsum_eq_single`
pattern: all terms with `m ≥ 1` vanish because `0^m = 0`, and the `m = 0`
term is `c₀ · 1 = c₀`. -/
@[simp] lemma frobeniusValue_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    frobeniusValue ps n z₁ ρ c₀ 0 = c₀ := by
  unfold frobeniusValue
  rw [tsum_eq_single 0]
  · simp [frobeniusCoeff_zero]
  · intro m hm
    have hm_ne : m ≠ 0 := hm
    rw [zero_pow hm_ne, mul_zero]

/-- **Frobenius series value is ℝ-linear in the indicial leading term.**
Pointwise consequence of the homogeneous-linear recurrence
`frobeniusCoeff_smul_c₀`: scaling the seed `c₀` by `c` scales the entire
series sum by the same `c`. Holds at every `t` (no summability hypothesis
needed because `tsum_mul_left` works unconditionally). -/
lemma frobeniusValue_smul_c₀
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (t : ℝ) :
    frobeniusValue ps n z₁ ρ (c * c₀) t =
      c * frobeniusValue ps n z₁ ρ c₀ t := by
  unfold frobeniusValue
  rw [← tsum_mul_left]
  refine tsum_congr ?_
  intro m
  rw [frobeniusCoeff_smul_c₀ ps n z₁ ρ c c₀ hpk m, mul_assoc]

/-- The Frobenius series sum vanishes when the seed is `0`. Direct
corollary of `frobeniusValue_smul_c₀` with `c = 0`. -/
@[simp] lemma frobeniusValue_zero_seed
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (t : ℝ) :
    frobeniusValue ps n z₁ ρ 0 t = 0 := by
  have h := frobeniusValue_smul_c₀ ps n z₁ ρ 0 0 hpk t
  rw [zero_mul, zero_mul] at h
  exact h

/-- **Bridge to Mathlib's `FormalMultilinearSeries.ofScalars`.** The
hand-rolled `frobeniusValue` agrees pointwise with the canonical
power-series sum produced by `FormalMultilinearSeries.ofScalarsSum`
applied to the coefficient sequence `frobeniusCoeff …`. With this
identification the Frobenius series gains access to Mathlib's analytic
infrastructure: `HasFPowerSeriesOnBall`, `AnalyticAt`,
`eqOn_of_preconnected_of_eventuallyEq`, etc. -/
theorem frobeniusValue_eq_ofScalarsSum
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (t : ℝ) :
    frobeniusValue ps n z₁ ρ c₀ t =
      FormalMultilinearSeries.ofScalarsSum (𝕜 := ℝ) (E := ℝ)
        (frobeniusCoeff ps n z₁ ρ c₀) t := by
  unfold frobeniusValue
  rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [smul_eq_mul]

/-- **HasSum at a convergence-disk point.** For `t` in the convergence
disk `|t|·(1+K) < 1`, the Frobenius series `HasSum` at the value
`frobeniusValue ps n z₁ ρ c₀ t`. This packages the summability together
with the sum identification, and is the standard form used with
`HasSum.tendsto_sum_nat`, `HasSum.unique`, etc. -/
theorem frobeniusCoeff_hasSum
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (t : ℝ)
    (ht : |t| * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    HasSum (fun m => frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)
      (frobeniusValue ps n z₁ ρ c₀ t) := by
  have hs :=
    frobeniusCoeff_mul_pow_summable ps n z₁ ρ c₀ M₀ hpk hpn hslope
      hM0_small hM0_large B hB_nn hB t ht
  exact hs.hasSum

/-- **`HasFPowerSeriesOnBall` for the Frobenius series.** For radius
`s > 0` strictly inside the Frobenius convergence disk
`s · (1 + K/D) < 1`, the function `t ↦ frobeniusValue ps n z₁ ρ c₀ t`
is represented on `Metric.eball 0 (ENNReal.ofReal s)` by the formal
power series `FormalMultilinearSeries.ofScalars ℝ (frobeniusCoeff …)`.
This is the gateway into Mathlib's analytic infrastructure
(`AnalyticAt`, `AnalyticOnNhd`, `eqOn_of_preconnected_of_eventuallyEq`). -/
theorem frobeniusValue_hasFPowerSeriesOnBall
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    HasFPowerSeriesOnBall
      (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ
        (frobeniusCoeff ps n z₁ ρ c₀))
      (0 : ℝ) (ENNReal.ofReal s) := by
  set p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ
      (frobeniusCoeff ps n z₁ ρ c₀) with hp_def
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact hB_nn
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  refine ⟨?radius, ?pos, ?sum⟩
  · -- r_le : ENNReal.ofReal s ≤ p.radius
    have habs : Summable
        (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
      frobeniusCoeff_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
        hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_pos.le hs_lt
    set sN : NNReal := Real.toNNReal s with hsN_def
    have hcoe : (sN : ℝ) = s := Real.coe_toNNReal s hs_pos.le
    have hsum : Summable (fun m : ℕ => ‖p m‖ * (sN : ℝ) ^ m) := by
      rw [hcoe]
      refine habs.congr ?_
      intro m
      simp [p, Real.norm_eq_abs]
    have hrad := p.le_radius_of_summable hsum
    have heq : ENNReal.ofReal s = (sN : ENNReal) := rfl
    rw [heq]
    exact hrad
  · -- r_pos
    exact ENNReal.ofReal_pos.mpr hs_pos
  · -- hasSum
    intro y hy
    have hy_dist : dist y (0 : ℝ) < s := by
      have hmem : edist y (0 : ℝ) < ENNReal.ofReal s := hy
      exact (edist_lt_ofReal).mp hmem
    have hy_abs : |y| < s := by
      simpa [Real.dist_eq] using hy_dist
    have ht : |y| * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1 := by
      rw [← hK_def]
      have h1 : |y| * (1 + K) < s * (1 + K) :=
        mul_lt_mul_of_pos_right hy_abs hR_pos
      linarith
    have hsum := frobeniusCoeff_hasSum ps n z₁ ρ c₀ M₀ hpk hpn hslope
      hM0_small hM0_large B hB_nn hB y ht
    have hcongr : (fun m : ℕ => p m (fun _ : Fin m => y))
        = (fun m : ℕ => frobeniusCoeff ps n z₁ ρ c₀ m * y ^ m) := by
      funext m
      simp [p, smul_eq_mul, mul_comm]
    rw [hcongr]
    simpa [zero_add] using hsum

/-- **`AnalyticOnNhd` packaging.** On the open ball `Metric.ball 0 s`
inside the Frobenius convergence disk, `frobeniusValue ps n z₁ ρ c₀`
is analytic at every point. This is the form needed by
`eqOn_of_preconnected_of_eventuallyEq` and other Mathlib tools that
propagate local agreement to global agreement on connected open sets. -/
theorem frobeniusValue_analyticOnNhd
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    AnalyticOnNhd ℝ (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) := by
  have hball := frobeniusValue_hasFPowerSeriesOnBall ps n z₁ ρ c₀ M₀
    hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_pos hs_lt
  have hAnal := hball.analyticOnNhd
  rwa [Metric.eball_ofReal] at hAnal

/-- **Cross-zero rigidity for the Frobenius series.** Given any
function `g : ℝ → ℝ` analytic on the open ball `Metric.ball 0 s`
inside the Frobenius convergence disk, if `g` agrees with
`frobeniusValue` in a neighborhood of `0`, then they agree on the
whole ball. This is the key tool for propagating local agreement
(e.g. from Picard uniqueness on a sub-interval not containing `0`)
across `0` to the whole disk. The proof composes
`frobeniusValue_analyticOnNhd` with Mathlib's
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. -/
theorem frobeniusValue_eqOn_of_eventuallyEq
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (g : ℝ → ℝ)
    (hg_anal : AnalyticOnNhd ℝ g (Metric.ball (0 : ℝ) s))
    (hfg : Filter.EventuallyEq (nhds (0 : ℝ)) g
      (fun t => frobeniusValue ps n z₁ ρ c₀ t)) :
    Set.EqOn g (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) := by
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) :=
    frobeniusValue_analyticOnNhd ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_pos hs_lt
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have hConn : IsPreconnected (Metric.ball (0 : ℝ) s) :=
    (convex_ball (0 : ℝ) s).isPreconnected
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hg_anal hF hConn h0 hfg

/-- **Series-data form of cross-zero rigidity.** A function `g`
analytic on `Metric.ball 0 s` whose power series at `0` is exactly
`FormalMultilinearSeries.ofScalars ℝ (frobeniusCoeff …)` agrees with
`frobeniusValue` on the whole ball. This is the form most natural
when the candidate `g` arrives with its own `HasFPowerSeriesAt`
data — typically obtained from term-by-term construction of an
analytic ODE solution. -/
theorem frobeniusValue_eqOn_of_hasFPowerSeriesAt
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (g : ℝ → ℝ)
    (hg_anal : AnalyticOnNhd ℝ g (Metric.ball (0 : ℝ) s))
    (hg_series : HasFPowerSeriesAt g
        (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ
          (frobeniusCoeff ps n z₁ ρ c₀)) (0 : ℝ)) :
    Set.EqOn g (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) := by
  -- Step A. Both `g` and `frobeniusValue` are represented by the same
  -- power series on a common (smaller) ball at `0`.
  have hF_ball := frobeniusValue_hasFPowerSeriesOnBall ps n z₁ ρ c₀ M₀
    hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_pos hs_lt
  obtain ⟨r', hg_ball⟩ := hg_series
  set rmin : ENNReal := min r' (ENNReal.ofReal s) with hrmin_def
  have hr_pos : 0 < rmin :=
    lt_min hg_ball.r_pos (ENNReal.ofReal_pos.mpr hs_pos)
  have hg_small : HasFPowerSeriesOnBall g _ (0 : ℝ) rmin :=
    hg_ball.mono hr_pos (min_le_left _ _)
  have hF_small : HasFPowerSeriesOnBall
      (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t) _ (0 : ℝ) rmin :=
    hF_ball.mono hr_pos (min_le_right _ _)
  -- Step B. By `HasFPowerSeriesOnBall.unique`, the two functions agree
  -- on `Metric.eball 0 rmin`, which is a 𝓝 0 neighborhood.
  have hEq : Set.EqOn g (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.eball (0 : ℝ) rmin) :=
    hg_small.unique hF_small
  have hnhd : Metric.eball (0 : ℝ) rmin ∈ nhds (0 : ℝ) :=
    Metric.eball_mem_nhds (0 : ℝ) hr_pos
  have hfg_evt : Filter.EventuallyEq (nhds (0 : ℝ)) g
      (fun t => frobeniusValue ps n z₁ ρ c₀ t) :=
    hEq.eventuallyEq_of_mem hnhd
  -- Step C. Lift to the whole ball via cross-zero rigidity.
  exact frobeniusValue_eqOn_of_eventuallyEq ps n z₁ ρ c₀ M₀
    hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_pos hs_lt
    g hg_anal hfg_evt

/-- **Partial-sum convergence.** Inside the convergence disk, the
finite partial sums `Σᵢ<M frobeniusCoeff i · tⁱ` converge to
`frobeniusValue t` as `M → ∞`. This is the standard operational form
for computing values and establishing continuity in downstream arguments. -/
theorem frobeniusPartialSum_tendsto_frobeniusValue
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (t : ℝ)
    (ht : |t| * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Filter.Tendsto
      (fun M => ∑ i ∈ Finset.range M,
          frobeniusCoeff ps n z₁ ρ c₀ i * t ^ i)
      Filter.atTop
      (nhds (frobeniusValue ps n z₁ ρ c₀ t)) := by
  have hs := frobeniusCoeff_hasSum ps n z₁ ρ c₀ M₀
    hpk hpn hslope hM0_small hM0_large B hB_nn hB t ht
  exact hs.tendsto_sum_nat

/-- **Continuity on the Frobenius disk.** For any radius `s` strictly
inside the convergence disk, `frobeniusValue` is continuous on
`[-s, s]`. This is the operational continuity statement that lets us
compute limits, apply the intermediate-value theorem, and connect
Frobenius series to ODE solutions. -/
theorem frobeniusValue_continuousOn
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValue ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValue
  have hsum :
      Summable (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
    frobeniusCoeff_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)
    (u := fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    calc ‖frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = |frobeniusCoeff ps n z₁ ρ c₀ m| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow hcoeff_nn

/-- **Derivative-series absolute summability.** For `s ≥ 0` inside the
Frobenius convergence disk (`s·(1+K) < 1`), the formally-differentiated
series `Σₖ (k+1)·|a_{k+1}|·sᵏ` is summable. This is the key building
block for `HasDerivAt` and analytic ODE satisfaction: the derivative of
`Σ aₘ·tᵐ` formally equals `Σ (k+1)·a_{k+1}·tᵏ`, and we need this series
to converge on the same disk.

Proof: use the pointwise geometric bound `|aₘ| ≤ S_{M₀}·(1+K)^{m-M₀}`,
shift past `M₀`, and compare against `(k+M₀+1)·rᵏ` where `r = s·(1+K)`.
Split `(k+M₀+1) = (k+1) + M₀`; both `Σ (k+1)·rᵏ` (via Mathlib's
`summable_choose_mul_geometric_of_norm_lt_one` at `k = 1`) and `Σ rᵏ`
(geometric) converge for `|r| < 1`. -/
theorem frobeniusCoeff_succ_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k => ((k + 1 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg ?_ hB_nn) ?_
      · positivity
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (le_of_lt hR_pos)) (pow_nonneg hs_nn _)
  -- Summable bound: (k+M₀+1)·r^k, written as (k+1)·r^k + M₀·r^k
  have h_choose : Summable (fun k : ℕ => ((k + 1).choose 1 : ℝ) * r ^ k) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr_norm).summable
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_bound :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_both :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) * r ^ k) := by
      have := h_choose.add (h_geom.mul_left (M₀ : ℝ))
      convert this using 1
      funext k
      push_cast
      simp [Nat.choose_one_right]
      ring
    exact h_sum_both.mul_left C
  -- Shift by M₀
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_bound
  · intro k
    refine mul_nonneg (mul_nonneg ?_ (abs_nonneg _)) (pow_nonneg hs_nn _)
    positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 1 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric
        ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB
        (k + M₀ + 1) hidx
    have hsub : k + M₀ + 1 - M₀ = k + 1 := by omega
    rw [hsub] at hpt
    -- hpt: |a_{k+M₀+1}| ≤ Smaj * (1+K)^(k+1)
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hkM0_1_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 1)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 1)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hkM0_1_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 1)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_succ]
      ring
    exact step1.trans_eq step2

/-- **Second-derivative series absolute summability.** For `s ≥ 0`
inside the Frobenius convergence disk, the formally-twice-differentiated
series `Σₖ (k+1)(k+2)·|a_{k+2}|·sᵏ` is summable. Same template as
lemma `frobeniusCoeff_succ_abs_mul_pow_summable` (1st derivative), but
using the weight `(k+M₀+1)(k+M₀+2) = (k+1)(k+2) + 2M₀·k + (M₀²+3M₀)`
and reducing to three Mathlib summables: `descFactorial 2`,
`descFactorial 1` (i.e. `(k+1)`), and geometric. -/
theorem frobeniusCoeff_succ_succ_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 2)| * s ^ k) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg ?_ hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Bound constant: Smaj · (1+K)^2 · s^M₀.
  set C : ℝ := Smaj * (1 + K) ^ 2 * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _))
      (pow_nonneg hs_nn _)
  -- Three summable pieces for (k+M₀+1)(k+M₀+2)·r^k.
  have h_desc2 : Summable (fun k : ℕ => ((k + 2).descFactorial 2 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 2 hr_norm
  have h_desc1 : Summable (fun k : ℕ => ((k + 1).descFactorial 1 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 1 hr_norm
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  -- Combine: (k+M₀+1)(k+M₀+2) = (k+1)(k+2) + 2M₀(k+1) + (M₀² + M₀).
  -- Note (k+1)(k+2) = (k+2).descFactorial 2, and (k+1) = (k+1).descFactorial 1.
  have h_combo :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) *
                                   ((k + M₀ + 2 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_all :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) *
                                ((k + M₀ + 2 : ℕ) : ℝ) * r ^ k) := by
      have h1 := h_desc2
      have h2 := h_desc1.mul_left (2 * M₀ : ℝ)
      have h3 := h_geom.mul_left ((M₀ : ℝ)^2 + M₀)
      have hcomb := (h1.add h2).add h3
      convert hcomb using 1
      funext k
      have hdesc2_nat : (k + 2).descFactorial 2 = (k + 1) * (k + 2) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial]
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h0 : k + 2 - 0 = k + 2 := by omega
        rw [h1, h0]
        ring
      have hdesc2 : ((k + 2).descFactorial 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
        rw [hdesc2_nat]; push_cast; ring
      have hdesc1_nat : (k + 1).descFactorial 1 = k + 1 := by
        rw [Nat.descFactorial, Nat.descFactorial]
        have h0 : k + 1 - 0 = k + 1 := by omega
        rw [h0]
        ring
      have hdesc1 : ((k + 1).descFactorial 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by
        rw [hdesc1_nat]
      rw [hdesc2, hdesc1]
      push_cast
      ring
    exact h_sum_all.mul_left C
  -- Shift by M₀.
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_combo
  · intro k
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) (abs_nonneg _)) (pow_nonneg hs_nn _)
    · positivity
    · positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 2 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric
        ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB
        (k + M₀ + 2) hidx
    have hsub : k + M₀ + 2 - M₀ = k + 2 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hfac_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) := by
      refine mul_nonneg ?_ ?_ <;> exact Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 2)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 2)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hfac_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 2)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_add]
      ring
    exact step1.trans_eq step2

/-- **General fallingFactorial-weighted absolute summability.** For any
order `j`, the weight `|fallingFactorial (m:ℝ) j| · |aₘ| · sᵐ` is
summable on the Frobenius convergence disk.  Generalises lemmas
`frobeniusCoeff_succ_abs_mul_pow_summable` (j=1, after shift) and
`frobeniusCoeff_succ_succ_abs_mul_pow_summable` (j=2).  Proof: use
`abs_fallingFactorial_le`: `|ff (m:ℝ) j| ≤ (m+j)^j`, bound
`(k+M₀+j)^j ≤ (M₀+j+1)^j · (k+1)^j ≤ (M₀+j+1)^j · ((k+j).descFactorial j)`,
apply `summable_descFactorial_mul_geometric_of_norm_lt_one j`, combine
with the pointwise geometric bound on `|aₘ|`. -/
theorem frobeniusCoeff_fallingFactorial_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ) (j : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j' ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m : ℕ => |fallingFactorial ((m : ℕ) : ℝ) j| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg ?_ hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Bound constant: Smaj · s^M₀ · (M₀+j+1)^j.
  set C : ℝ := Smaj * s ^ M₀ * (((M₀ + j + 1 : ℕ) : ℝ) ^ j) with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact hSmaj_nn
    · exact pow_nonneg hs_nn _
    · exact pow_nonneg (Nat.cast_nonneg _) _
  -- Summable descending-factorial × geometric.
  have h_desc : Summable (fun k : ℕ => (((k + j).descFactorial j : ℕ) : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one j hr_norm
  -- Key Nat inequality (generalised over k, j): (k+1)^j ≤ (k+j).descFactorial j.
  have h_pow_le_desc : ∀ (kk jj : ℕ), (kk + 1) ^ jj ≤ (kk + jj).descFactorial jj := by
    intro kk jj
    have h := Nat.pow_sub_le_descFactorial (kk + jj) jj
    have hsub : (kk + jj) + 1 - jj = kk + 1 := by omega
    rw [hsub] at h
    exact h
  -- Shift past M₀.
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ (h_desc.mul_left C)
  · intro k
    refine mul_nonneg (mul_nonneg ?_ (abs_nonneg _)) (pow_nonneg hs_nn _)
    exact abs_nonneg _
  intro k
  -- Step 1: |ff (k+M₀ : ℝ) j| ≤ (k+M₀+j)^j.
  have h_ff_abs :
      |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| ≤ (((k + M₀ + j : ℕ) : ℝ)) ^ j := by
    have h := abs_fallingFactorial_le ((k + M₀ : ℕ) : ℝ) j
    have habs : |((k + M₀ : ℕ) : ℝ)| = ((k + M₀ : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    have hcast : ((k + M₀ : ℕ) : ℝ) + (j : ℝ) = ((k + M₀ + j : ℕ) : ℝ) := by
      push_cast; ring
    rw [habs, hcast] at h
    exact h
  -- Step 2: (k+M₀+j) ≤ (M₀+j+1)·(k+1).
  have h_factor_le : (k + M₀ + j : ℕ) ≤ (M₀ + j + 1) * (k + 1) := by
    have : (M₀ + j + 1) * (k + 1) = k + M₀ + j + ((M₀ + j) * k + 1) := by ring
    omega
  have h_factor_le_R :
      ((k + M₀ + j : ℕ) : ℝ) ≤ ((M₀ + j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h_factor_le
    push_cast at this ⊢; linarith
  have h_kMj_nn : (0 : ℝ) ≤ ((k + M₀ + j : ℕ) : ℝ) := Nat.cast_nonneg _
  have h_pow_factor :
      ((k + M₀ + j : ℕ) : ℝ) ^ j ≤
        (((M₀ + j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ j :=
    pow_le_pow_left₀ h_kMj_nn h_factor_le_R j
  have h_desc_lower_nat : (k + 1) ^ j ≤ (k + j).descFactorial j := h_pow_le_desc k j
  have h_desc_lower_R :
      ((k + 1 : ℕ) : ℝ) ^ j ≤ (((k + j).descFactorial j : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h_desc_lower_nat
    push_cast at this ⊢; linarith
  -- Step 4: pointwise geometric bound on |a_{k+M₀}|.
  have h_idx : M₀ ≤ k + M₀ := by omega
  have hpt :=
    abs_frobeniusCoeff_pointwise_geometric
      ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB
      (k + M₀) h_idx
  have hsub : k + M₀ - M₀ = k := by omega
  rw [hsub] at hpt
  -- Assemble the overall bound.
  have h_a_nn : (0 : ℝ) ≤ |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| := abs_nonneg _
  have h_s_nn_k : (0 : ℝ) ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
  have h_pow_Mj_nn : (0 : ℝ) ≤ ((M₀ + j + 1 : ℕ) : ℝ) ^ j := pow_nonneg (Nat.cast_nonneg _) _
  have hmaj_nn : (0 : ℝ) ≤ Smaj * (1 + K) ^ k :=
    mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _)
  -- |ff| · |a| · s^{k+M₀} ≤ (k+M₀+j)^j · Smaj·(1+K)^k · s^{k+M₀}.
  have step1 :
      |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| *
        |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| * s ^ (k + M₀) ≤
      (((k + M₀ + j : ℕ) : ℝ) ^ j) * (Smaj * (1 + K) ^ k) * s ^ (k + M₀) := by
    have hA : |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| *
              |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| ≤
              (((k + M₀ + j : ℕ) : ℝ) ^ j) * (Smaj * (1 + K) ^ k) :=
      mul_le_mul h_ff_abs hpt h_a_nn (pow_nonneg h_kMj_nn j)
    exact mul_le_mul_of_nonneg_right hA h_s_nn_k
  -- (k+M₀+j)^j ≤ (M₀+j+1)^j · ((k+j).descFactorial j).
  have step2 :
      (((k + M₀ + j : ℕ) : ℝ) ^ j) * (Smaj * (1 + K) ^ k) * s ^ (k + M₀) ≤
      ((((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ)) *
        (Smaj * (1 + K) ^ k) * s ^ (k + M₀) := by
    have h_A :
        ((((M₀ + j + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ)) ^ j =
        ((((M₀ + j + 1 : ℕ) : ℝ))) ^ j * (((k + 1 : ℕ) : ℝ)) ^ j := mul_pow _ _ _
    have h_k1_to_desc :
        (((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + 1 : ℕ) : ℝ)) ^ j ≤
        (((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h_desc_lower_R h_pow_Mj_nn
    have h_tot :
        (((k + M₀ + j : ℕ) : ℝ)) ^ j ≤
        (((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ) := by
      calc (((k + M₀ + j : ℕ) : ℝ)) ^ j
          ≤ ((((M₀ + j + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ)) ^ j := h_pow_factor
        _ = _ := h_A
        _ ≤ _ := h_k1_to_desc
    have := mul_le_mul_of_nonneg_right h_tot hmaj_nn
    exact mul_le_mul_of_nonneg_right this h_s_nn_k
  -- Final rearrangement equals C · (k+j).descFactorial j · r^k.
  have step3 :
      ((((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ)) *
        (Smaj * (1 + K) ^ k) * s ^ (k + M₀) =
      C * ((((k + j).descFactorial j : ℕ) : ℝ) * r ^ k) := by
    rw [hC_def, hr_def, mul_pow, pow_add]
    ring
  calc |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| * s ^ (k + M₀)
      ≤ _ := step1
    _ ≤ _ := step2
    _ = C * ((((k + j).descFactorial j : ℕ) : ℝ) * r ^ k) := step3

/-- **Shift decomposition.** Inside the convergence disk the Frobenius
value splits as `c₀ + t · tail(t)`, where `tail(t) = Σₘ a_{m+1}·tᵐ`.
This is the standard identity that lets us extract the seed constant
and work with the reduced "tail" series; it is used later to compute
derivatives at `t = 0`. -/
theorem frobeniusValue_eq_c0_add_t_mul_tail
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (t : ℝ)
    (ht : |t| * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    frobeniusValue ps n z₁ ρ c₀ t =
      c₀ + t * ∑' m, frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m := by
  have hsum :=
    frobeniusCoeff_mul_pow_summable ps n z₁ ρ c₀ M₀ hpk hpn hslope
      hM0_small hM0_large B hB_nn hB t ht
  unfold frobeniusValue
  rw [hsum.tsum_eq_zero_add]
  have h0 : frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = c₀ := by
    simp [frobeniusCoeff, frobeniusBuilder]
  rw [h0]
  congr 1
  rw [← tsum_mul_left]
  congr 1
  funext m
  ring

/-- **Differentiability on the Frobenius disk.** On the open ball
`|t| < s` (where `s·(1+K) < 1`), the Frobenius series defines a
differentiable function whose derivative is obtained by termwise
differentiation. This is the analytic capstone: it says the series
behaves like a genuine analytic function, not just a continuous `tsum`.

Proof: apply Mathlib's `hasDerivAt_tsum_of_isPreconnected` with the
explicit derivative series `(m : ℝ) · aₘ · y^{m-1}` and the uniform
sup-norm bound `(m : ℝ) · |aₘ| · s^{m-1}`, which is summable by the
derivative-series summability lemma (shifted by `1`). -/
theorem frobeniusValue_hasDerivAt
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValue ps n z₁ ρ c₀ y)
      (∑' (m : ℕ), (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ (m - 1)) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    frobeniusCoeff ps n z₁ ρ c₀ m * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  -- 1. Summability of u (shift by 1 reduces to our derivative-series lemma)
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite :
        (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k := by
      funext k
      simp [hu_def]
    rw [hrewrite]
    exact frobeniusCoeff_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  -- 2. Each g m is differentiable with derivative g' m
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :
        HasDerivAt (fun x : ℝ => frobeniusCoeff ps n z₁ ρ c₀ m * x ^ m)
          (frobeniusCoeff ps n z₁ ρ c₀ m * ((m : ℝ) * y ^ (m - 1))) y :=
      hpow.const_mul (frobeniusCoeff ps n z₁ ρ c₀ m)
    have heq : frobeniusCoeff ps n z₁ ρ c₀ m * ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  -- 3. Bound on g' m y for y ∈ ball 0 s
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    calc ‖g' m y‖
        = (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg hm_nn]
      _ ≤ (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le
            (mul_nonneg hm_nn hcoeff_nn)
      _ = u m := rfl
  -- 4. Series converges at y₀ = 0 (trivially, since g m 0 = 0 for m ≥ 1)
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m
      simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]
    exact summable_zero
  -- 5. Apply hasDerivAt_tsum_of_isPreconnected
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  -- 6. Conclude: the tsum of g equals frobeniusValue pointwise
  have hfun_eq : (fun z => ∑' m, g m z) = fun y => frobeniusValue ps n z₁ ρ c₀ y := by
    funext y
    unfold frobeniusValue
    rfl
  rw [hfun_eq] at h
  exact h

/-- **Shifted derivative-series form.** The termwise derivative sum
`Σ' m · aₘ · t^(m-1)` (with natural subtraction) equals the standard
shifted form `Σ' (m+1) · a_{m+1} · t^m`. Useful because the latter
matches the clean `Σ cₘ · t^m` pattern needed for iterated
differentiation and ODE substitution. -/
theorem frobeniusValue_deriv_tsum_shift
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ (m - 1)) =
      ∑' (m : ℕ),
        ((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m := by
  -- Signed summability of the left-hand series: bounded by the
  -- absolute-value summability lemma.
  have hsum_abs :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k) :=
    frobeniusCoeff_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  -- Signed version: |t| ≤ s, so |(k+1)·a_{k+1}·t^k| ≤ (k+1)·|a_{k+1}|·s^k.
  have hsum_signed :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (k + 1) * t ^ k) := by
    apply Summable.of_norm
    refine hsum_abs.of_nonneg_of_le ?_ ?_
    · intro k; positivity
    · intro k
      have hknn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have htk : |t ^ k| ≤ s ^ k := by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
      calc ‖((k + 1 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (k + 1) * t ^ k‖
          = ((k + 1 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * |t ^ k| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hknn]
        _ ≤ ((k + 1 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k :=
            mul_le_mul_of_nonneg_left htk
              (mul_nonneg hknn (abs_nonneg _))
  -- Split LHS at m=0: the m=0 term is 0 (factor of `(0:ℝ)`).
  have hLHS_split :
      Summable (fun m : ℕ => (m : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ (m - 1)) := by
    rw [← summable_nat_add_iff 1]
    have hrewrite :
        (fun i => ((i + 1 : ℕ) : ℝ) *
          frobeniusCoeff ps n z₁ ρ c₀ (i + 1) * t ^ (i + 1 - 1)) =
        fun k => ((k + 1 : ℕ) : ℝ) *
          frobeniusCoeff ps n z₁ ρ c₀ (k + 1) * t ^ k := by
      funext k; simp
    change Summable fun i => (((i + 1 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (i + 1) * t ^ (i + 1 - 1))
    rw [hrewrite]
    exact hsum_signed
  -- Now the key identity: tsum over ℕ splits at 0, and the 0-term is 0.
  rw [hLHS_split.tsum_eq_zero_add]
  simp

/-- **Derivative of the Frobenius value** (standard tsum form). The
formal derivative, named as a function so it can be iterated. Its
coefficients are the "Cauchy-shifted" sequence `bₘ = (m+1)·a_{m+1}`. -/
noncomputable def frobeniusValueDeriv
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ t : ℝ) : ℝ :=
  ∑' (m : ℕ), ((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m

@[simp] lemma frobeniusValueDeriv_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    frobeniusValueDeriv ps n z₁ ρ c₀ 0 = frobeniusCoeff ps n z₁ ρ c₀ 1 := by
  unfold frobeniusValueDeriv
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    simp [zero_pow hm]

/-- The first formal derivative is ℝ-linear in the indicial leading
term, by termwise application of `frobeniusCoeff_smul_c₀`. -/
lemma frobeniusValueDeriv_smul_c₀
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (t : ℝ) :
    frobeniusValueDeriv ps n z₁ ρ (c * c₀) t =
      c * frobeniusValueDeriv ps n z₁ ρ c₀ t := by
  unfold frobeniusValueDeriv
  rw [← tsum_mul_left]
  refine tsum_congr ?_
  intro m
  rw [frobeniusCoeff_smul_c₀ ps n z₁ ρ c c₀ hpk (m + 1)]
  ring

/-- The first formal derivative vanishes when the seed is `0`. -/
@[simp] lemma frobeniusValueDeriv_zero_seed
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (t : ℝ) :
    frobeniusValueDeriv ps n z₁ ρ 0 t = 0 := by
  have h := frobeniusValueDeriv_smul_c₀ ps n z₁ ρ 0 0 hpk t
  rw [zero_mul, zero_mul] at h
  exact h

/-- **Euler-operator identity, k = 0.** Trivial base case:
`Σ' m, fallingFactorial (m:ℝ) 0 · aₘ · tᵐ = t^0 · frobeniusValue t`.
Unfolds via `fallingFactorial_zero` and definitional unfolding of
`frobeniusValue`. -/
theorem frobeniusValueDeriv_tsum_euler_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (t : ℝ) :
    (∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) 0 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 0 * frobeniusValue ps n z₁ ρ c₀ t := by
  simp [frobeniusValue, fallingFactorial_zero]

/-- **Euler-operator identity, k = 1.** On the convergence disk,
`Σ' m, m·aₘ·tᵐ = t · frobeniusValueDeriv(t)`.  This is the analytic
counterpart of `fallingEulerOp ρ 1` evaluated at `ρ = 0`: the operator
`θ = t·d/dt` acts on the Frobenius series by multiplying `aₘ` by `m`.
A building block for turning the formal `substLHSGen = 0` identity
into a pointwise analytic ODE. -/
theorem frobeniusValueDeriv_tsum_euler_one
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t * frobeniusValueDeriv ps n z₁ ρ c₀ t := by
  have hs_abs_pos_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  -- Signed summability of the LHS.
  have hsum : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    -- Absolute bound: m · |aₘ| · sᵐ, via shift-1 form + mul_right by s.
    have h_shift_abs : Summable (fun m : ℕ =>
        (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1)) := by
      rw [← summable_nat_add_iff 1]
      have hrewrite :
          (fun i => ((i + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (i + 1)| * s ^ (i + 1 - 1)) =
          fun k => ((k + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k := by
        funext k; simp
      change Summable fun i => (((i + 1 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (i + 1)| * s ^ (i + 1 - 1))
      rw [hrewrite]
      exact frobeniusCoeff_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
        hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
    have h_abs_sum : Summable (fun m : ℕ =>
        (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
      have := h_shift_abs.mul_right s
      convert this using 1
      funext m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · have hm1 : m = (m - 1) + 1 := by omega
        have hpow : s ^ m = s ^ (m - 1) * s := by
          conv_lhs => rw [hm1]
          rw [pow_succ]
        rw [hpow]; ring
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    calc ‖(m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hmnn]
      _ ≤ (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pos_pow m)
            (mul_nonneg hmnn (abs_nonneg _))
  -- Split at m=0: the m=0 term is zero.
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  -- Reindex: Σ' n, (n+1)·a_{n+1}·t^(n+1) = t · frobeniusValueDeriv t.
  unfold frobeniusValueDeriv
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **Clean HasDerivAt statement.** Combining `frobeniusValue_hasDerivAt`
(termwise differentiation with `t^(m-1)` form) and
`frobeniusValue_deriv_tsum_shift` (reindex to `t^m` form), we obtain
the standard form: `d/dt frobeniusValue(t) = frobeniusValueDeriv(t)`
on the open convergence disk. -/
theorem frobeniusValue_hasDerivAt_std
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValue ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv ps n z₁ ρ c₀ t) t := by
  have h := frobeniusValue_hasDerivAt ps n z₁ ρ c₀ M₀ hpk hpn hslope
    hM0_small hM0_large B hB_nn hB s hs_pos hs_lt t ht_mem
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  have hshift := frobeniusValue_deriv_tsum_shift ps n z₁ ρ c₀ M₀
    hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt t ht_abs
  unfold frobeniusValueDeriv
  rw [← hshift]
  exact h

/-- **Continuity of `frobeniusValueDeriv`** on the closed disk
`[-s, s]` where `s·(1+K) < 1`. Parallels `frobeniusValue_continuousOn`,
using the derivative-series summable lemma (lemma 10) as the uniform
bound. -/
theorem frobeniusValueDeriv_continuousOn
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValueDeriv ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValueDeriv
  have hsum :
      Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m) :=
    frobeniusCoeff_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => ((m + 1 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m)
    (u := fun m => ((m + 1 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hmnn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
    calc ‖((m + 1 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m‖
        = ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hmnn]
      _ ≤ ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hmnn hcoeff_nn)

/-- **Second derivative of the Frobenius value** (standard tsum form).
Coefficients `cₘ = (m+1)(m+2)·a_{m+2}`. -/
noncomputable def frobeniusValueDeriv2
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ t : ℝ) : ℝ :=
  ∑' (m : ℕ), ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
    frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * t ^ m

@[simp] lemma frobeniusValueDeriv2_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    frobeniusValueDeriv2 ps n z₁ ρ c₀ 0 =
      2 * frobeniusCoeff ps n z₁ ρ c₀ 2 := by
  unfold frobeniusValueDeriv2
  rw [tsum_eq_single 0]
  · norm_num
  · intro m hm
    simp [zero_pow hm]

/-- The second formal derivative is ℝ-linear in the indicial leading
term, by termwise application of `frobeniusCoeff_smul_c₀`. -/
lemma frobeniusValueDeriv2_smul_c₀
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (t : ℝ) :
    frobeniusValueDeriv2 ps n z₁ ρ (c * c₀) t =
      c * frobeniusValueDeriv2 ps n z₁ ρ c₀ t := by
  unfold frobeniusValueDeriv2
  rw [← tsum_mul_left]
  refine tsum_congr ?_
  intro m
  rw [frobeniusCoeff_smul_c₀ ps n z₁ ρ c c₀ hpk (m + 2)]
  ring

/-- The second formal derivative vanishes when the seed is `0`. -/
@[simp] lemma frobeniusValueDeriv2_zero_seed
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0) (t : ℝ) :
    frobeniusValueDeriv2 ps n z₁ ρ 0 t = 0 := by
  have h := frobeniusValueDeriv2_smul_c₀ ps n z₁ ρ 0 0 hpk t
  rw [zero_mul, zero_mul] at h
  exact h

/-- **Continuity of `frobeniusValueDeriv2`** on the closed disk
`[-s, s]` where `s·(1+K) < 1`. Parallels `frobeniusValueDeriv_continuousOn`,
using `frobeniusCoeff_succ_succ_abs_mul_pow_summable` as the uniform
bound. -/
theorem frobeniusValueDeriv2_continuousOn
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValueDeriv2 ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValueDeriv2
  have hsum :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (k + 2)| * s ^ k) :=
    frobeniusCoeff_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * t ^ m)
    (u := fun m => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hprod_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| := abs_nonneg _
    calc ‖((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * t ^ m‖
        = ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg (Nat.cast_nonneg (m + 1 : ℕ)),
              abs_of_nonneg (Nat.cast_nonneg (m + 2 : ℕ))]
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hprod_nn hcoeff_nn)

/-- **Second-order HasDerivAt.** On the open disk `|t| < s` with
`s·(1+K) < 1`, `frobeniusValueDeriv` is itself differentiable and its
derivative equals `frobeniusValueDeriv2`. Structurally identical to
`frobeniusValue_hasDerivAt`, using lemma 16 for the uniform bound. -/
theorem frobeniusValueDeriv_hasDerivAt
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValueDeriv ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv2 ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    ((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * (((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1)) *
      y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * ((m + 1 : ℕ) : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  -- 1. Summability of u (shift by 1 → 2nd-derivative summable lemma).
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 2)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      have hplus : (k + 1 + 1 : ℕ) = k + 2 := by omega
      simp only [hsub, hplus]
    rw [hrewrite]
    exact frobeniusCoeff_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  -- 2. Each g m is differentiable with derivative g' m.
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :=
      hpow.const_mul (((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1))
    have heq : ((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1) *
        ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * (((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1)) *
          y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  -- 3. ‖g' m y‖ ≤ u m on the ball.
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| :=
      mul_nonneg (mul_nonneg hm_nn hm1_nn) hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn]
          ring
      _ ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  -- 4. Series converges at y₀ = 0.
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  -- 5. Apply hasDerivAt_tsum_of_isPreconnected.
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  -- 6. The tsum of g is frobeniusValueDeriv; rewrite and reindex g' to standard form.
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValueDeriv ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValueDeriv; rfl
  rw [hfun_eq] at h
  -- The HasDerivAt gives ∑' m, g' m t as the derivative;
  -- we need to show this equals frobeniusValueDeriv2 t.
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  -- Signed summability of g' m t via absolute bound against u.
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| :=
      mul_nonneg (mul_nonneg hm_nn hm1_nn) hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
          abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn]
      ring
    have hu_eq : u m = (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  -- Split the tsum at m=0 and reindex.
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv2 ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv2
    rw [hsum_signed.tsum_eq_zero_add]
    -- m=0 term of g': 0 · (...) · t^(0-1) = 0 (factor of Nat.cast 0).
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    -- Reindex: match term-by-term.
    congr 1
    funext k
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (k + 2) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    have he1 : (k + 1 + 1 : ℕ) = k + 2 := by omega
    simp only [hkk, he1]
    push_cast
    ring
  rw [hshift] at h
  exact h

/-- **Euler-operator identity at `k = 2`** (analytic bridge).
`Σ' m, m(m-1) · aₘ · tᵐ = t² · frobeniusValueDeriv2(t)` on the disk
`|t| ≤ s` with `s·(1+K) < 1`. Counterpart to `coeff_fallingEulerOp`
at order 2: turns formal `fallingEulerOp 0 2 (frobeniusSolution)`
coefficients into pointwise `t² · V''(t)`. Building block for the
analytic LHS assembly. -/
theorem frobeniusValueDeriv_tsum_euler_two
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial (m : ℝ) 2 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 2 * frobeniusValueDeriv2 ps n z₁ ρ c₀ t := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  -- Absolute-summable weighted series, via shift-2 form × s².
  have h_shift_abs :=
    frobeniusCoeff_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  -- h_shift_abs : Summable (fun k => (k+1)(k+2) · |a_{k+2}| · sᵏ)
  have h_shift_s2 := h_shift_abs.mul_right (s ^ 2)
  have h_abs_sum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    rw [← summable_nat_add_iff 2]
    convert h_shift_s2 using 1
    funext k
    have hff : fallingFactorial ((k + 2 : ℕ) : ℝ) 2 =
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
      rw [fallingFactorial_two]; push_cast; ring
    have hpow : s ^ (k + 2) = s ^ k * s ^ 2 := by rw [pow_add]
    rw [hff, hpow]; ring
  -- Signed summability follows by absolute bound.
  have hsum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hff_nn : 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 2 := by
      rw [fallingFactorial_two]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        have hfac : 0 ≤ (m : ℝ) - 1 := by linarith
        exact mul_nonneg hm_nn hfac
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 2 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hff_nn]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg hff_nn (abs_nonneg _))
  -- Peel off m = 0 and m = 1 (both zero by fallingFactorial_two at 0, 1).
  rw [← hsum.sum_add_tsum_nat_add 2]
  have h0 : fallingFactorial ((0 : ℕ) : ℝ) 2 *
      frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = 0 := by
    rw [fallingFactorial_two]; push_cast; ring
  have h1 : fallingFactorial ((1 : ℕ) : ℝ) 2 *
      frobeniusCoeff ps n z₁ ρ c₀ 1 * t ^ 1 = 0 := by
    rw [fallingFactorial_two]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1,
    add_zero]
  -- Reindex the tail to match t² · frobeniusValueDeriv2.
  unfold frobeniusValueDeriv2
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hff : fallingFactorial ((k + 2 : ℕ) : ℝ) 2 =
      ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    rw [fallingFactorial_two]; push_cast; ring
  rw [hff]
  have hpow : t ^ (k + 2) = t ^ 2 * t ^ k := by
    rw [pow_add]; ring
  rw [hpow]; ring

/-- **Third-derivative series absolute summability.**
`Σ (k+1)(k+2)(k+3)·|a_{k+3}|·sᵏ` summable on `s·(1+K) < 1`. Used for
the 3rd-order `HasDerivAt` result. Weight expansion:
`(k+M₀+1)(k+M₀+2)(k+M₀+3) = d₃(k) + 3M₀·d₂(k) + 3M₀(M₀+1)·d₁(k)
  + M₀(M₀+1)(M₀+2)`, where `dⱼ(k) = (k+j).descFactorial j`. -/
theorem frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                ((k + 3 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 3)| * s ^ k) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg ?_ hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) ^ 3 * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _))
      (pow_nonneg hs_nn _)
  have h_desc3 : Summable (fun k : ℕ => ((k + 3).descFactorial 3 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 3 hr_norm
  have h_desc2 : Summable (fun k : ℕ => ((k + 2).descFactorial 2 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 2 hr_norm
  have h_desc1 : Summable (fun k : ℕ => ((k + 1).descFactorial 1 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 1 hr_norm
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_combo :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) *
                                   ((k + M₀ + 2 : ℕ) : ℝ) *
                                   ((k + M₀ + 3 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_all :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) *
                                ((k + M₀ + 2 : ℕ) : ℝ) *
                                ((k + M₀ + 3 : ℕ) : ℝ) * r ^ k) := by
      have h1 := h_desc3
      have h2 := h_desc2.mul_left (3 * M₀ : ℝ)
      have h3 := h_desc1.mul_left (3 * (M₀ : ℝ) * ((M₀ : ℝ) + 1))
      have h4 := h_geom.mul_left ((M₀ : ℝ) * ((M₀ : ℝ) + 1) * ((M₀ : ℝ) + 2))
      have hcomb := ((h1.add h2).add h3).add h4
      convert hcomb using 1
      funext k
      have hdesc3_nat : (k + 3).descFactorial 3 = (k + 1) * (k + 2) * (k + 3) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
            Nat.descFactorial]
        have h2 : k + 3 - 2 = k + 1 := by omega
        have h1 : k + 3 - 1 = k + 2 := by omega
        have h0 : k + 3 - 0 = k + 3 := by omega
        rw [h2, h1, h0]
        ring
      have hdesc3 : ((k + 3).descFactorial 3 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
        rw [hdesc3_nat]; push_cast; ring
      have hdesc2_nat : (k + 2).descFactorial 2 = (k + 1) * (k + 2) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial]
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h0 : k + 2 - 0 = k + 2 := by omega
        rw [h1, h0]
        ring
      have hdesc2 : ((k + 2).descFactorial 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
        rw [hdesc2_nat]; push_cast; ring
      have hdesc1_nat : (k + 1).descFactorial 1 = k + 1 := by
        rw [Nat.descFactorial, Nat.descFactorial]
        have h0 : k + 1 - 0 = k + 1 := by omega
        rw [h0]
        ring
      have hdesc1 : ((k + 1).descFactorial 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by
        rw [hdesc1_nat]
      rw [hdesc3, hdesc2, hdesc1]
      push_cast
      ring
    exact h_sum_all.mul_left C
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_combo
  · intro k
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_)
      (abs_nonneg _)) (pow_nonneg hs_nn _)
    · positivity
    · positivity
    · positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 3 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric
        ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB
        (k + M₀ + 3) hidx
    have hsub : k + M₀ + 3 - M₀ = k + 3 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hfac_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
        ((k + M₀ + 3 : ℕ) : ℝ) := by
      refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> exact Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 3)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 3)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hfac_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 3)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
             ((k + M₀ + 3 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_add]
      ring
    exact step1.trans_eq step2

/-- **Third derivative of the Frobenius value** (standard tsum form).
Coefficients `cₘ = (m+1)(m+2)(m+3)·a_{m+3}`. -/
noncomputable def frobeniusValueDeriv3
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ t : ℝ) : ℝ :=
  ∑' (m : ℕ), ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
    frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * t ^ m

@[simp] lemma frobeniusValueDeriv3_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) :
    frobeniusValueDeriv3 ps n z₁ ρ c₀ 0 =
      6 * frobeniusCoeff ps n z₁ ρ c₀ 3 := by
  unfold frobeniusValueDeriv3
  rw [tsum_eq_single 0]
  · norm_num
  · intro m hm
    simp [zero_pow hm]

/-- `frobeniusValueDeriv3` is continuous on the closed disk `[-s, s]`.
Analogue of `frobeniusValueDeriv2_continuousOn` for the third derivative,
using the 3rd-derivative summability lemma. -/
theorem frobeniusValueDeriv3_continuousOn
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValueDeriv3 ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValueDeriv3
  have hsum :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
        ((k + 3 : ℕ) : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ (k + 3)| * s ^ k) :=
    frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * t ^ m)
    (u := fun m => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hprod_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        ((m + 3 : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| := abs_nonneg _
    calc ‖((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * t ^ m‖
        = ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg (Nat.cast_nonneg (m + 1 : ℕ)),
              abs_of_nonneg (Nat.cast_nonneg (m + 2 : ℕ)),
              abs_of_nonneg (Nat.cast_nonneg (m + 3 : ℕ))]
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hprod_nn hcoeff_nn)

/-- **Third-order HasDerivAt.** On the open disk `|t| < s` with
`s·(1+K) < 1`, `frobeniusValueDeriv2` is differentiable and its
derivative equals `frobeniusValueDeriv3`. Same template as lemma 17,
using the 3rd-derivative summability lemma. -/
theorem frobeniusValueDeriv2_hasDerivAt
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValueDeriv2 ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv3 ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 2)) * y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  -- 1. Summability of u (shift by 1 → 3rd-derivative summable lemma).
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 3)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      have hplus : (k + 1 + 2 : ℕ) = k + 3 := by omega
      simp only [hsub, hplus]
    rw [hrewrite]
    exact frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  -- 2. Each g m is differentiable with derivative g' m.
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :=
      hpow.const_mul (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (m + 2))
    have heq : ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (m + 2) *
        ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          frobeniusCoeff ps n z₁ ρ c₀ (m + 2)) * y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  -- 3. ‖g' m y‖ ≤ u m on the ball.
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| :=
      mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn) hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
              abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
              abs_of_nonneg hm2_nn]
          ring
      _ ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  -- 4. Series converges at y₀ = 0.
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  -- 5. Apply hasDerivAt_tsum_of_isPreconnected.
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  -- 6. Rewrite lhs to frobeniusValueDeriv2; reindex g' to frobeniusValueDeriv3.
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValueDeriv2 ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValueDeriv2; rfl
  rw [hfun_eq] at h
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  -- Signed summability of g' m t via absolute bound against u.
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| :=
      mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn) hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
          abs_of_nonneg hm2_nn]
      ring
    have hu_eq : u m = (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  -- Split the tsum at m=0 and reindex.
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv3 ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv3
    rw [hsum_signed.tsum_eq_zero_add]
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    congr 1
    funext k
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
      ((k + 3 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (k + 3) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    have he1 : (k + 1 + 2 : ℕ) = k + 3 := by omega
    simp only [hkk, he1]
    push_cast
    ring
  rw [hshift] at h
  exact h

/-- **Euler-operator identity at `k = 3`** (analytic bridge).
`Σ' m, m(m-1)(m-2) · aₘ · tᵐ = t³ · frobeniusValueDeriv3(t)` on the
disk.  Counterpart to `coeff_fallingEulerOp` at order 3 (ρ=0). -/
theorem frobeniusValueDeriv_tsum_euler_three
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial (m : ℝ) 3 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 3 * frobeniusValueDeriv3 ps n z₁ ρ c₀ t := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  -- Absolute-summable series, via shift-3 form × s³.
  have h_shift_abs :=
    frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  have h_shift_s3 := h_shift_abs.mul_right (s ^ 3)
  have h_abs_sum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 3 *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    rw [← summable_nat_add_iff 3]
    convert h_shift_s3 using 1
    funext k
    have hff : fallingFactorial ((k + 3 : ℕ) : ℝ) 3 =
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
      rw [fallingFactorial_three]; push_cast; ring
    have hpow : s ^ (k + 3) = s ^ k * s ^ 3 := by rw [pow_add]
    rw [hff, hpow]; ring
  have hsum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 3 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hff_nn : 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 3 := by
      rw [fallingFactorial_three]
      rcases Nat.lt_or_ge m 3 with hm | hm
      · have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> norm_num
      · have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by linarith
        have hf1 : 0 ≤ (m : ℝ) - 1 := by linarith
        have hf2 : 0 ≤ (m : ℝ) - 2 := by linarith
        exact mul_nonneg (mul_nonneg hm_nn hf1) hf2
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 3 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 3 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hff_nn]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 3 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg hff_nn (abs_nonneg _))
  -- Peel off m = 0, 1, 2 (all zero by fallingFactorial_three at 0, 1, 2).
  rw [← hsum.sum_add_tsum_nat_add 3]
  have h0 : fallingFactorial ((0 : ℕ) : ℝ) 3 *
      frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = 0 := by
    rw [fallingFactorial_three]; push_cast; ring
  have h1 : fallingFactorial ((1 : ℕ) : ℝ) 3 *
      frobeniusCoeff ps n z₁ ρ c₀ 1 * t ^ 1 = 0 := by
    rw [fallingFactorial_three]; push_cast; ring
  have h2 : fallingFactorial ((2 : ℕ) : ℝ) 3 *
      frobeniusCoeff ps n z₁ ρ c₀ 2 * t ^ 2 = 0 := by
    rw [fallingFactorial_three]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h1, h2, add_zero]
  -- Reindex the tail.
  unfold frobeniusValueDeriv3
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hff : fallingFactorial ((k + 3 : ℕ) : ℝ) 3 =
      ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
    rw [fallingFactorial_three]; push_cast; ring
  rw [hff]
  have hpow : t ^ (k + 3) = t ^ 3 * t ^ k := by
    rw [pow_add]; ring
  rw [hpow]; ring

/-- **Fourth-derivative series absolute summability.**
`Σ (k+1)(k+2)(k+3)(k+4)·|a_{k+4}|·sᵏ` summable on `s·(1+K) < 1`.
Weight expansion:
`(k+M₀+1)(k+M₀+2)(k+M₀+3)(k+M₀+4)
  = d₄(k) + 4M₀·d₃(k) + 6M₀(M₀+1)·d₂(k)
  + 4M₀(M₀+1)(M₀+2)·d₁(k) + M₀(M₀+1)(M₀+2)(M₀+3)`. -/
theorem frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 4)| * s ^ k) := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg ?_ hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) ^ 4 * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _))
      (pow_nonneg hs_nn _)
  have h_desc4 : Summable (fun k : ℕ => ((k + 4).descFactorial 4 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 4 hr_norm
  have h_desc3 : Summable (fun k : ℕ => ((k + 3).descFactorial 3 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 3 hr_norm
  have h_desc2 : Summable (fun k : ℕ => ((k + 2).descFactorial 2 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 2 hr_norm
  have h_desc1 : Summable (fun k : ℕ => ((k + 1).descFactorial 1 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 1 hr_norm
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_combo :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) *
                                   ((k + M₀ + 2 : ℕ) : ℝ) *
                                   ((k + M₀ + 3 : ℕ) : ℝ) *
                                   ((k + M₀ + 4 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_all :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) *
                                ((k + M₀ + 2 : ℕ) : ℝ) *
                                ((k + M₀ + 3 : ℕ) : ℝ) *
                                ((k + M₀ + 4 : ℕ) : ℝ) * r ^ k) := by
      have h1 := h_desc4
      have h2 := h_desc3.mul_left (4 * M₀ : ℝ)
      have h3 := h_desc2.mul_left (6 * (M₀ : ℝ) * ((M₀ : ℝ) + 1))
      have h4 := h_desc1.mul_left (4 * (M₀ : ℝ) * ((M₀ : ℝ) + 1) * ((M₀ : ℝ) + 2))
      have h5 := h_geom.mul_left ((M₀ : ℝ) * ((M₀ : ℝ) + 1) *
                                  ((M₀ : ℝ) + 2) * ((M₀ : ℝ) + 3))
      have hcomb := ((((h1.add h2).add h3).add h4).add h5)
      convert hcomb using 1
      funext k
      have hdesc4_nat :
          (k + 4).descFactorial 4 = (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
            Nat.descFactorial, Nat.descFactorial]
        have h3 : k + 4 - 3 = k + 1 := by omega
        have h2 : k + 4 - 2 = k + 2 := by omega
        have h1 : k + 4 - 1 = k + 3 := by omega
        have h0 : k + 4 - 0 = k + 4 := by omega
        rw [h3, h2, h1, h0]
        ring
      have hdesc4 : ((k + 4).descFactorial 4 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) := by
        rw [hdesc4_nat]; push_cast; ring
      have hdesc3_nat :
          (k + 3).descFactorial 3 = (k + 1) * (k + 2) * (k + 3) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
            Nat.descFactorial]
        have h2 : k + 3 - 2 = k + 1 := by omega
        have h1 : k + 3 - 1 = k + 2 := by omega
        have h0 : k + 3 - 0 = k + 3 := by omega
        rw [h2, h1, h0]
        ring
      have hdesc3 : ((k + 3).descFactorial 3 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
        rw [hdesc3_nat]; push_cast; ring
      have hdesc2_nat : (k + 2).descFactorial 2 = (k + 1) * (k + 2) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial]
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h0 : k + 2 - 0 = k + 2 := by omega
        rw [h1, h0]
        ring
      have hdesc2 : ((k + 2).descFactorial 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
        rw [hdesc2_nat]; push_cast; ring
      have hdesc1_nat : (k + 1).descFactorial 1 = k + 1 := by
        rw [Nat.descFactorial, Nat.descFactorial]
        have h0 : k + 1 - 0 = k + 1 := by omega
        rw [h0]
        ring
      have hdesc1 : ((k + 1).descFactorial 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by
        rw [hdesc1_nat]
      rw [hdesc4, hdesc3, hdesc2, hdesc1]
      push_cast
      ring
    exact h_sum_all.mul_left C
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_combo
  · intro k
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_)
      ?_) (abs_nonneg _)) (pow_nonneg hs_nn _)
    · positivity
    · positivity
    · positivity
    · positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 4 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric
        ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB
        (k + M₀ + 4) hidx
    have hsub : k + M₀ + 4 - M₀ = k + 4 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hfac_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
        ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_ <;>
        exact Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 4)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 4)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hfac_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 4)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
             ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_add]
      ring
    exact step1.trans_eq step2

/-- **Fourth derivative of the Frobenius value** (standard tsum form).
Coefficients `cₘ = (m+1)(m+2)(m+3)(m+4)·a_{m+4}`. -/
noncomputable def frobeniusValueDeriv4
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ t : ℝ) : ℝ :=
  ∑' (m : ℕ), ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
    ((m + 3 : ℕ) : ℝ) * ((m + 4 : ℕ) : ℝ) *
    frobeniusCoeff ps n z₁ ρ c₀ (m + 4) * t ^ m

/-- **Fourth-order HasDerivAt.** On the open disk `|t| < s` with
`s·(1+K) < 1`, `frobeniusValueDeriv3` is differentiable and its
derivative equals `frobeniusValueDeriv4`. -/
theorem frobeniusValueDeriv3_hasDerivAt
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValueDeriv3 ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv4 ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 3)) * y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  -- 1. Summability of u (shift by 1 → 4th-derivative summable lemma).
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 4)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      have hplus : (k + 1 + 3 : ℕ) = k + 4 := by omega
      simp only [hsub, hplus]
    rw [hrewrite]
    exact frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable
      ps n z₁ ρ c₀ M₀ hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  -- 2. Each g m is differentiable with derivative g' m.
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :=
      hpow.const_mul (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        ((m + 3 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 3))
    have heq : ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (m + 3) *
        ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
          frobeniusCoeff ps n z₁ ρ c₀ (m + 3)) * y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  -- 3. ‖g' m y‖ ≤ u m on the ball.
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm3_nn : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              ((m + 3 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn)
        hm3_nn) hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
              abs_mul, abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
              abs_of_nonneg hm2_nn, abs_of_nonneg hm3_nn]
          ring
      _ ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  -- 4. Series converges at y₀ = 0.
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  -- 5. Apply hasDerivAt_tsum_of_isPreconnected.
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  -- 6. Rewrite lhs to frobeniusValueDeriv3; reindex g' to frobeniusValueDeriv4.
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValueDeriv3 ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValueDeriv3; rfl
  rw [hfun_eq] at h
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm3_nn : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              ((m + 3 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn)
        hm3_nn) hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_mul, abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
          abs_of_nonneg hm2_nn, abs_of_nonneg hm3_nn]
      ring
    have hu_eq : u m =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv4 ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv4
    rw [hsum_signed.tsum_eq_zero_add]
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    congr 1
    funext k
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
      ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (k + 4) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    have he1 : (k + 1 + 3 : ℕ) = k + 4 := by omega
    simp only [hkk, he1]
    push_cast
    ring
  rw [hshift] at h
  exact h

/-- **Euler-operator identity at `k = 4`** (analytic bridge).
`Σ' m, m(m-1)(m-2)(m-3)·aₘ·tᵐ = t⁴ · frobeniusValueDeriv4(t)`
on the disk.  Counterpart to `coeff_fallingEulerOp` at order 4 (ρ=0);
final Euler-identity piece needed for ζ(3)'s n=3 Apéry ODE. -/
theorem frobeniusValueDeriv_tsum_euler_four
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' (m : ℕ), fallingFactorial (m : ℝ) 4 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 4 * frobeniusValueDeriv4 ps n z₁ ρ c₀ t := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  -- Expand `fallingFactorial x 4 = x(x-1)(x-2)(x-3)`.
  have hff4 : ∀ x : ℝ, fallingFactorial x 4 =
      x * (x - 1) * (x - 2) * (x - 3) := by
    intro x; rw [show (4 : ℕ) = 3 + 1 from rfl, fallingFactorial_succ,
      fallingFactorial_three]; push_cast; ring
  -- Absolute-summable series, via shift-4 form × s⁴.
  have h_shift_abs :=
    frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable ps n z₁ ρ c₀ M₀
      hpk hpn hslope hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
  have h_shift_s4 := h_shift_abs.mul_right (s ^ 4)
  have h_abs_sum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 4 *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    rw [← summable_nat_add_iff 4]
    convert h_shift_s4 using 1
    funext k
    have hff : fallingFactorial ((k + 4 : ℕ) : ℝ) 4 =
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) := by
      rw [hff4]; push_cast; ring
    have hpow : s ^ (k + 4) = s ^ k * s ^ 4 := by rw [pow_add]
    rw [hff, hpow]; ring
  have hsum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 4 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hff_nn : 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 4 := by
      rw [hff4]
      rcases Nat.lt_or_ge m 4 with hm | hm
      · have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> norm_num
      · have h4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by linarith
        have hf1 : 0 ≤ (m : ℝ) - 1 := by linarith
        have hf2 : 0 ≤ (m : ℝ) - 2 := by linarith
        have hf3 : 0 ≤ (m : ℝ) - 3 := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hm_nn hf1) hf2) hf3
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 4 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 4 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hff_nn]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 4 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg hff_nn (abs_nonneg _))
  -- Peel off m = 0, 1, 2, 3 (all zero by hff4 at integers < 4).
  rw [← hsum.sum_add_tsum_nat_add 4]
  have h0 : fallingFactorial ((0 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = 0 := by
    rw [hff4]; push_cast; ring
  have h1 : fallingFactorial ((1 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 1 * t ^ 1 = 0 := by
    rw [hff4]; push_cast; ring
  have h2 : fallingFactorial ((2 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 2 * t ^ 2 = 0 := by
    rw [hff4]; push_cast; ring
  have h3 : fallingFactorial ((3 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 3 * t ^ 3 = 0 := by
    rw [hff4]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h1, h2, h3, add_zero]
  -- Reindex the tail.
  unfold frobeniusValueDeriv4
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hff : fallingFactorial ((k + 4 : ℕ) : ℝ) 4 =
      ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
        ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) := by
    rw [hff4]; push_cast; ring
  rw [hff]
  have hpow : t ^ (k + 4) = t ^ 4 * t ^ k := by
    rw [pow_add]; ring
  rw [hpow]; ring

set_option maxHeartbeats 400000 in
-- Cauchy product + antidiagonal reindex + signed/abs summability juggling
-- exceeds the default heartbeat budget during unification.
open PowerSeries in
/-- **Analytic polynomial-times-frobenius bridge** (Cauchy product).
For a polynomial `P` and the Frobenius series (convergent on the
disk `|t| ≤ s`, `s·(1+K) < 1`):
    `P.eval t · V(t) = Σ' N, coeff_N((P:PS) * g) · t^N`,
where `g = frobeniusSolution`.  Direction: turns formal power-series
product coefficients into a pointwise analytic product.  Backbone of
the analytic LHS assembly for `substLHSGen`. -/
theorem poly_eval_mul_frobeniusValue_tsum_coeff
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (P : Polynomial ℝ) (t : ℝ) (ht_abs : |t| ≤ s) :
    P.eval t * frobeniusValue ps n z₁ ρ c₀ t =
      ∑' N : ℕ, coeff (R := ℝ) N
        ((↑P : PowerSeries ℝ) * frobeniusSolution ps n z₁ ρ c₀) * t ^ N := by
  set K : ℝ := ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg ?_ hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  -- Hypothesis for `frobeniusCoeff_hasSum` at t: |t|·(1+K) < 1.
  have ht_lt : |t| * (1 + K) < 1 := by
    have h1 : |t| * (1 + K) ≤ s * (1 + K) :=
      mul_le_mul_of_nonneg_right ht_abs (le_of_lt hR_pos)
    exact lt_of_le_of_lt h1 hs_lt
  -- HasSum 1: frobenius tsum.
  have hfrob_hasSum :
      HasSum (fun m => frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)
        (frobeniusValue ps n z₁ ρ c₀ t) :=
    frobeniusCoeff_hasSum ps n z₁ ρ c₀ M₀ hpk hpn hslope
      hM0_small hM0_large B hB_nn hB t ht_lt
  have hfrob_summable :=
    frobeniusCoeff_mul_pow_summable ps n z₁ ρ c₀ M₀ hpk hpn hslope
      hM0_small hM0_large B hB_nn hB t ht_lt
  -- HasSum 2: polynomial tsum as finite-support.
  let fP : ℕ → ℝ := fun i => P.coeff i * t ^ i
  have hP_zero : ∀ i ∉ Finset.range (P.natDegree + 1), fP i = 0 := by
    intro i hi
    rw [Finset.mem_range, not_lt] at hi
    have h0 : P.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [fP, h0]
  have hP_hasSum : HasSum fP (P.eval t) := by
    have h : HasSum fP (∑ i ∈ Finset.range (P.natDegree + 1), fP i) :=
      hasSum_sum_of_ne_finset_zero (f := fP)
        (s := Finset.range (P.natDegree + 1)) hP_zero
    convert h using 1
    rw [Polynomial.eval_eq_sum_range]
  have hP_summable : Summable fP := hP_hasSum.summable
  -- Absolute summability of the frobenius series on |t| ≤ s.
  have hfrob_abs_t :
      Summable (fun m : ℕ => ‖frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖) := by
    have hfrob_abs_s :=
      frobeniusCoeff_abs_mul_pow_summable ps n z₁ ρ c₀ M₀ hpk hpn hslope
        hM0_small hM0_large B hB_nn hB s hs_nn hs_lt
    refine hfrob_abs_s.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |t| ^ m ≤ s ^ m := pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  -- |fP| is summable (finite support).
  have hfP_abs : Summable (fun i => ‖fP i‖) := by
    have h_abs_zero : ∀ i ∉ Finset.range (P.natDegree + 1),
        ‖fP i‖ = 0 := by
      intro i hi; rw [hP_zero i hi, norm_zero]
    exact (hasSum_sum_of_ne_finset_zero (f := fun i => ‖fP i‖)
      (s := Finset.range (P.natDegree + 1)) h_abs_zero).summable
  -- Pair-product summability via mul_of_summable_norm.
  have hpair_summable :
      Summable (fun x : ℕ × ℕ => fP x.1 *
        (frobeniusCoeff ps n z₁ ρ c₀ x.2 * t ^ x.2)) :=
    summable_mul_of_summable_norm hfP_abs hfrob_abs_t
  -- Apply Cauchy product (antidiagonal form).
  have hcauchy :=
    hP_summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hfrob_summable
      hpair_summable
  -- LHS equals P.eval t * frobeniusValue t.
  have hLHS : (∑' i, fP i) * (∑' m, frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      P.eval t * frobeniusValue ps n z₁ ρ c₀ t := by
    rw [hP_hasSum.tsum_eq, hfrob_hasSum.tsum_eq]
  rw [hLHS] at hcauchy
  rw [hcauchy]
  -- Match term-by-term.
  congr 1
  funext N
  -- RHS Cauchy inner sum.
  -- coeff N ((P : PS) * frobeniusSolution) = Σ p ∈ antidiagonal N, P.coeff p.1 · a_{p.2}
  have hcoeff_mul :
      coeff (R := ℝ) N
        ((↑P : PowerSeries ℝ) * frobeniusSolution ps n z₁ ρ c₀) =
      ∑ p ∈ Finset.antidiagonal N,
        P.coeff p.1 * frobeniusCoeff ps n z₁ ρ c₀ p.2 := by
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Polynomial.coeff_coe, coeff_frobeniusSolution]
  rw [hcoeff_mul]
  -- Left side: Σ p ∈ antidiagonal N, fP p.1 · (a_{p.2} · t^{p.2})
  --         = Σ p ∈ antidiagonal N, P.coeff p.1 · a_{p.2} · t^N
  --         = (Σ p ∈ antidiagonal N, P.coeff p.1 · a_{p.2}) · t^N
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  change P.coeff p.1 * t ^ p.1 *
    (frobeniusCoeff ps n z₁ ρ c₀ p.2 * t ^ p.2) =
    P.coeff p.1 * frobeniusCoeff ps n z₁ ρ c₀ p.2 * t ^ N
  have ht_pow : t ^ p.1 * t ^ p.2 = t ^ N := by
    rw [← pow_add, hp]
  rw [← ht_pow]
  ring

set_option maxHeartbeats 400000 in
-- Generic Cauchy-product bridge: many tsum manipulations + antidiagonal
-- rearrangement push past the default heartbeat budget.
open PowerSeries in
/-- **Generic Cauchy-product bridge**: polynomial-eval times power-series
analytic value.  For any polynomial `P` and power series `g` whose
coefficients are absolutely summable with weight `sᵐ`, the pointwise
product equals the tsum of the formal product coefficients.
Abstracts `poly_eval_mul_frobeniusValue_tsum_coeff` — proof uses no
Frobenius-specific input beyond abs-summability of coefficients. -/
theorem polyEval_mul_tsum_coeff_eq_tsum_coeff_mul
    (P : Polynomial ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : Summable (fun m : ℕ => |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    P.eval t * (∑' m : ℕ, coeff (R := ℝ) m g * t ^ m) =
      ∑' N : ℕ, coeff (R := ℝ) N ((↑P : PowerSeries ℝ) * g) * t ^ N := by
  -- Signed summability of g-series on |t| ≤ s.
  have hg_signed_t : Summable (fun m : ℕ => coeff (R := ℝ) m g * t ^ m) := by
    apply Summable.of_norm
    refine hg_abs.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |t| ^ m ≤ s ^ m := pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hg_hasSum :
      HasSum (fun m => coeff (R := ℝ) m g * t ^ m)
        (∑' m, coeff (R := ℝ) m g * t ^ m) := hg_signed_t.hasSum
  -- Absolute summability of g-series on |t| ≤ s.
  have hg_abs_t :
      Summable (fun m : ℕ => ‖coeff (R := ℝ) m g * t ^ m‖) := by
    refine hg_abs.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |t| ^ m ≤ s ^ m := pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  -- Polynomial tsum via finite support.
  let fP : ℕ → ℝ := fun i => P.coeff i * t ^ i
  have hP_zero : ∀ i ∉ Finset.range (P.natDegree + 1), fP i = 0 := by
    intro i hi
    rw [Finset.mem_range, not_lt] at hi
    have h0 : P.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [fP, h0]
  have hP_hasSum : HasSum fP (P.eval t) := by
    have h : HasSum fP (∑ i ∈ Finset.range (P.natDegree + 1), fP i) :=
      hasSum_sum_of_ne_finset_zero (f := fP)
        (s := Finset.range (P.natDegree + 1)) hP_zero
    convert h using 1
    rw [Polynomial.eval_eq_sum_range]
  have hP_summable : Summable fP := hP_hasSum.summable
  have hfP_abs : Summable (fun i => ‖fP i‖) := by
    have h_abs_zero : ∀ i ∉ Finset.range (P.natDegree + 1),
        ‖fP i‖ = 0 := by
      intro i hi; rw [hP_zero i hi, norm_zero]
    exact (hasSum_sum_of_ne_finset_zero (f := fun i => ‖fP i‖)
      (s := Finset.range (P.natDegree + 1)) h_abs_zero).summable
  -- Pair-product summability via mul_of_summable_norm.
  have hpair_summable :
      Summable (fun x : ℕ × ℕ => fP x.1 *
        (coeff (R := ℝ) x.2 g * t ^ x.2)) :=
    summable_mul_of_summable_norm hfP_abs hg_abs_t
  -- Cauchy product (antidiagonal form).
  have hcauchy :=
    hP_summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg_signed_t
      hpair_summable
  have hLHS : (∑' i, fP i) * (∑' m, coeff (R := ℝ) m g * t ^ m) =
      P.eval t * (∑' m, coeff (R := ℝ) m g * t ^ m) := by
    rw [hP_hasSum.tsum_eq]
  rw [hLHS] at hcauchy
  rw [hcauchy]
  -- Match term-by-term via `coeff_mul` and `Polynomial.coeff_coe`.
  congr 1
  funext N
  have hcoeff_mul :
      coeff (R := ℝ) N ((↑P : PowerSeries ℝ) * g) =
      ∑ p ∈ Finset.antidiagonal N, P.coeff p.1 * coeff (R := ℝ) p.2 g := by
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Polynomial.coeff_coe]
  rw [hcoeff_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  change P.coeff p.1 * t ^ p.1 *
    (coeff (R := ℝ) p.2 g * t ^ p.2) =
    P.coeff p.1 * coeff (R := ℝ) p.2 g * t ^ N
  have ht_pow : t ^ p.1 * t ^ p.2 = t ^ N := by
    rw [← pow_add, hp]
  rw [← ht_pow]; ring

open PowerSeries in
/-- **X-shift analytic bridge**: for a power series `F` whose coefficient
sequence is absolutely summable on the disk, multiplying by `Xᵏ`
corresponds pointwise to multiplying the tsum by `tᵏ`.
`Σ' N, coeff N (Xᵏ · F) · tᴺ = tᵏ · Σ' M, coeff M F · tᴹ`.

Proof chain: `coeff (M+k) (Xᵏ · F) = coeff M F` (`coeff_X_pow_mul`),
`coeff N (Xᵏ · F) = 0` for `N < k` (`coeff_X_pow_mul'`); apply
`hasSum_nat_add_iff k` with zero prefix contribution. -/
theorem tsum_coeff_X_pow_mul_of_summable
    (k : ℕ) (F : PowerSeries ℝ) (t : ℝ)
    (hF : Summable (fun m : ℕ => coeff (R := ℝ) m F * t ^ m)) :
    (∑' N : ℕ, coeff (R := ℝ) N ((X : PowerSeries ℝ) ^ k * F) * t ^ N) =
      t ^ k * ∑' M : ℕ, coeff (R := ℝ) M F * t ^ M := by
  set S : ℝ := ∑' M : ℕ, coeff (R := ℝ) M F * t ^ M with hS_def
  -- g(M) := coeff M F · t^M has sum S.
  have hF_hasSum :
      HasSum (fun M : ℕ => coeff (R := ℝ) M F * t ^ M) S := hF.hasSum
  -- The "shifted" summand f(N+k) = t^k · (coeff N F · t^N).
  have h_shift :
      (fun N : ℕ => coeff (R := ℝ) (N + k) ((X : PowerSeries ℝ) ^ k * F) *
                      t ^ (N + k)) =
      (fun N : ℕ => t ^ k * (coeff (R := ℝ) N F * t ^ N)) := by
    funext N
    rw [coeff_X_pow_mul (R := ℝ) F k N, pow_add]
    ring
  -- HasSum of shifted series at t^k · S.
  have h_shift_sum :
      HasSum (fun N : ℕ => coeff (R := ℝ) (N + k) ((X : PowerSeries ℝ) ^ k * F) *
                             t ^ (N + k)) (t ^ k * S) := by
    rw [h_shift]
    exact hF_hasSum.mul_left (t ^ k)
  -- Prefix terms at N < k are zero (coeff_X_pow_mul').
  have h_prefix_zero :
      ∀ i ∈ Finset.range k,
        coeff (R := ℝ) i ((X : PowerSeries ℝ) ^ k * F) * t ^ i = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coeff_X_pow_mul' (R := ℝ) F k i, if_neg (by omega : ¬ k ≤ i),
        zero_mul]
  have h_prefix_sum :
      ∑ i ∈ Finset.range k,
        coeff (R := ℝ) i ((X : PowerSeries ℝ) ^ k * F) * t ^ i = 0 := by
    apply Finset.sum_eq_zero
    exact h_prefix_zero
  -- Assemble via hasSum_nat_add_iff.
  have h_total :
      HasSum (fun N : ℕ => coeff (R := ℝ) N ((X : PowerSeries ℝ) ^ k * F) * t ^ N)
        (t ^ k * S) := by
    have :=
      (hasSum_nat_add_iff
        (f := fun N => coeff (R := ℝ) N ((X : PowerSeries ℝ) ^ k * F) * t ^ N)
        k).mp h_shift_sum
    rw [h_prefix_sum, add_zero] at this
    exact this
  exact h_total.tsum_eq

set_option maxHeartbeats 800000 in
-- Companion summability uses the full Cauchy pair-to-antidiagonal chain,
-- pushing past the default heartbeat budget.
open PowerSeries in
/-- **Companion summability for the generic Cauchy bridge.**  The signed
`t`-series of `(P:PS) · g` is summable whenever `g`'s coefficients are
`sᵐ`-abs-summable and `|t| ≤ s`. -/
theorem summable_coeff_polyPS_mul_mul_pow
    (P : Polynomial ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : Summable (fun m : ℕ => |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    Summable (fun N : ℕ =>
      coeff (R := ℝ) N (((P : Polynomial ℝ) : PowerSeries ℝ) * g) * t ^ N) := by
  -- Abbreviate the two ℕ → ℝ series to avoid slow unification through
  -- `Polynomial.coeff` / `PowerSeries.coeff` inside antidiagonal types.
  set Fp : ℕ → ℝ := fun i => P.coeff i * t ^ i with hFp_def
  set Gp : ℕ → ℝ := fun m => coeff (R := ℝ) m g * t ^ m with hGp_def
  -- Polynomial coefficient series is norm-summable (finite support).
  have hFp_abs : Summable (fun i => ‖Fp i‖) := by
    have h_zero : ∀ i ∉ Finset.range (P.natDegree + 1), ‖Fp i‖ = 0 := by
      intro i hi
      rw [Finset.mem_range, not_lt] at hi
      have h0 : P.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [Fp, h0]
    exact (hasSum_sum_of_ne_finset_zero (f := fun i => ‖Fp i‖)
      (s := Finset.range (P.natDegree + 1)) h_zero).summable
  -- Norm-summability of g-series on `|t| ≤ s`.
  have hGp_abs : Summable (fun m : ℕ => ‖Gp m‖) := by
    refine hg_abs.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    simp only [Gp]
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) ht_abs _) (abs_nonneg _)
  -- Pair-product summability.
  have hpair : Summable (fun x : ℕ × ℕ => Fp x.1 * Gp x.2) :=
    summable_mul_of_summable_norm hFp_abs hGp_abs
  -- Antidiagonal summability.
  have h_antidiag : Summable
      (fun N : ℕ => ∑ p ∈ Finset.antidiagonal N, Fp p.1 * Gp p.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hpair
  -- Match `coeff N ((P:PS) * g) * t^N` term-by-term with the antidiagonal.
  refine h_antidiag.congr (fun N => ?_)
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [Polynomial.coeff_coe]
  have ht_pow : t ^ N = t ^ p.1 * t ^ p.2 := by
    rw [← pow_add, hp]
  simp only [Fp, Gp]
  rw [ht_pow]; ring

open PowerSeries in
/-- **Per-`j` analytic summand bridge.**  For `g` whose coefficients have
abs-summability weighted by `|fallingFactorial (m:ℝ) j| * sᵐ` on a radius
`s ≥ |t|`, the analytic value of the `j`-th summand of `substLHSGen ps k z₁ 0 g`
equals the product form
  `(-1)^j · t^{k-j} · (taylorShift (ps j) z₁).eval t · (Σ' m, falling·a_m·tᵐ)`.

Combines three bridges:
1. `coeff_smul` + `tsum_mul_left` — pulls `(-1)^j` out of the tsum.
2. Polynomial-coercion fusion — merges `X^{k-j} · (taylorShift (ps j) z₁)` into
   a single polynomial `Pⱼ` whose eval at `t` is `t^{k-j} · (taylorShift …).eval t`.
3. `polyEval_mul_tsum_coeff_eq_tsum_coeff_mul` — converts
   `Σ' N, coeff N (Pⱼ · fallingEulerOp 0 j g) · t^N` into
   `Pⱼ.eval t · Σ' m, coeff m (fallingEulerOp 0 j g) · tᵐ`.
4. `coeff_fallingEulerOp` at `ρ = 0` rewrites the inner coefficients to
   `fallingFactorial (m:ℝ) j · coeff m g`. -/
theorem tsum_substLHSGen_summand_eq
    (ps : ℕ → Polynomial ℝ) (k j : ℕ) (z₁ : ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| * |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' N : ℕ, coeff (R := ℝ) N
        (((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
          * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
          * fallingEulerOp 0 j g)) * t ^ N) =
      ((-1 : ℝ) ^ j) * t ^ (k - j) *
        (taylorShift (ps j) z₁).eval t *
        ∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
          coeff (R := ℝ) m g * t ^ m := by
  -- Scalar pull-out on each coefficient.
  have h_coeff_mul : ∀ N : ℕ,
      coeff (R := ℝ) N (((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
          * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
          * fallingEulerOp 0 j g)) * t ^ N =
      ((-1 : ℝ) ^ j) * (coeff (R := ℝ) N ((X : PowerSeries ℝ) ^ (k - j)
            * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
            * fallingEulerOp 0 j g) * t ^ N) := by
    intro N
    rw [PowerSeries.coeff_smul]
    simp [smul_eq_mul, mul_assoc]
  -- Fuse X^{k-j} and taylorShift (ps j) z₁ as a single polynomial `Pj`.
  set Pj : Polynomial ℝ := Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ with hPj_def
  have hPj_coe :
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) =
      (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ) := by
    change ((Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ : Polynomial ℝ) :
              PowerSeries ℝ) = _
    push_cast
    rfl
  have hPj_eval :
      Pj.eval t = t ^ (k - j) * (taylorShift (ps j) z₁).eval t := by
    simp [hPj_def]
  -- Absolute summability of the `fallingEulerOp 0 j g` coefficient series on `s`.
  have h_eul_abs : Summable (fun m : ℕ =>
      |coeff (R := ℝ) m (fallingEulerOp 0 j g)| * s ^ m) := by
    refine hg_abs.congr (fun m => ?_)
    rw [coeff_fallingEulerOp, zero_add, abs_mul]
  -- Apply the generic Cauchy bridge with `P := Pj`, `g := fallingEulerOp 0 j g`.
  have h_cauchy :
      Pj.eval t * (∑' m : ℕ, coeff (R := ℝ) m (fallingEulerOp 0 j g) * t ^ m) =
        ∑' N : ℕ, coeff (R := ℝ) N
          (((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp 0 j g) * t ^ N :=
    polyEval_mul_tsum_coeff_eq_tsum_coeff_mul Pj (fallingEulerOp 0 j g) s h_eul_abs t ht_abs
  -- Rewrite the inner Euler-operator series via `coeff_fallingEulerOp` at `ρ = 0`.
  have h_tsum_eul :
      (∑' m : ℕ, coeff (R := ℝ) m (fallingEulerOp 0 j g) * t ^ m) =
      ∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
        coeff (R := ℝ) m g * t ^ m := by
    apply tsum_congr
    intro m
    rw [coeff_fallingEulerOp, zero_add]
  -- Assemble the final chain.
  simp_rw [h_coeff_mul]
  rw [tsum_mul_left]
  rw [show (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
        * fallingEulerOp 0 j g =
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp 0 j g from by
        rw [hPj_coe]]
  rw [← h_cauchy, h_tsum_eul, hPj_eval]
  ring

open PowerSeries in
/-- **Per-`j` summability companion.**  The `t`-series of the `j`-th
`substLHSGen` summand is summable whenever the `fallingFactorial`-weighted
coefficient series of `g` is abs-summable on a radius `s ≥ |t|`. -/
theorem summable_substLHSGen_summand_coeff_mul_pow
    (ps : ℕ → Polynomial ℝ) (k j : ℕ) (z₁ : ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| * |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    Summable (fun N : ℕ => coeff (R := ℝ) N
        (((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
          * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
          * fallingEulerOp 0 j g)) * t ^ N) := by
  -- Replace the smul-wrapped summand by a constant-scaled plain product
  -- and apply the companion summability with the fused polynomial `Pj`.
  set Pj : Polynomial ℝ := Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ with hPj_def
  have hPj_coe :
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) =
      (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ) := by
    change ((Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ : Polynomial ℝ) :
              PowerSeries ℝ) = _
    push_cast
    rfl
  -- Absolute summability of `coeff m (fallingEulerOp 0 j g) * s^m`.
  have h_eul_abs : Summable (fun m : ℕ =>
      |coeff (R := ℝ) m (fallingEulerOp 0 j g)| * s ^ m) := by
    refine hg_abs.congr (fun m => ?_)
    rw [coeff_fallingEulerOp, zero_add, abs_mul]
  -- Summability for `coeff N ((Pj:PS) * fallingEulerOp 0 j g) * t^N`.
  have h_base : Summable (fun N : ℕ => coeff (R := ℝ) N
      (((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp 0 j g) * t ^ N) :=
    summable_coeff_polyPS_mul_mul_pow Pj (fallingEulerOp 0 j g) s h_eul_abs t ht_abs
  -- Scalar multiple is summable; congr through smul = constant multiplication.
  have h_scalar := h_base.mul_left ((-1 : ℝ) ^ j)
  refine h_scalar.congr (fun N => ?_)
  rw [PowerSeries.coeff_smul]
  rw [show (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
        * fallingEulerOp 0 j g =
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp 0 j g from by
        rw [hPj_coe]]
  simp [smul_eq_mul, mul_assoc]

open PowerSeries in
/-- **Finset aggregation of the per-`j` analytic summand bridge.**  For
`k, z₁, g` and `s ≥ |t|`, assuming `fallingFactorial`-weighted
abs-summability of `g`'s coefficients for every `j ∈ range (k+1)`:
  `∑' N, coeff N (substLHSGen ps k z₁ 0 g) · t^N
    = ∑_{j ∈ range(k+1)} (-1)^j · t^{k-j} · (taylorShift (ps j) z₁).eval t
        · Σ' m, fallingFactorial (m:ℝ) j · coeff m g · t^m`. -/
theorem tsum_coeff_substLHSGen_eq_finsum
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ : ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range (k + 1), Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| * |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' N : ℕ, coeff (R := ℝ) N (substLHSGen ps k z₁ 0 g) * t ^ N) =
      ∑ j ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ j) * t ^ (k - j) *
          (taylorShift (ps j) z₁).eval t *
          ∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
            coeff (R := ℝ) m g * t ^ m := by
  -- Distribute `coeff N` over the Finset sum inside `substLHSGen`, then
  -- distribute `· t^N` and swap the tsum/finset-sum using per-j summability.
  unfold substLHSGen
  -- Step 1: rewrite `coeff N (∑_j …) · t^N = ∑_j (coeff N (…) · t^N)`.
  have h_coeff_sum_mul : ∀ N : ℕ,
      coeff (R := ℝ) N (∑ j ∈ Finset.range (k + 1),
          ((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
            * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
            * fallingEulerOp 0 j g)) * t ^ N =
      ∑ j ∈ Finset.range (k + 1),
        coeff (R := ℝ) N (((-1 : ℝ) ^ j) •
          ((X : PowerSeries ℝ) ^ (k - j)
            * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
            * fallingEulerOp 0 j g)) * t ^ N := by
    intro N
    rw [map_sum (PowerSeries.coeff (R := ℝ) N) _ _, Finset.sum_mul]
  simp_rw [h_coeff_sum_mul]
  -- Step 2: swap `∑' N, ∑_j = ∑_j, ∑' N` via `Summable.tsum_finsetSum`.
  rw [Summable.tsum_finsetSum (fun j hj =>
    summable_substLHSGen_summand_coeff_mul_pow ps k j z₁ g s (hg_abs j hj) t ht_abs)]
  -- Step 3: apply the per-j bridge to each summand.
  apply Finset.sum_congr rfl
  intro j hj
  exact tsum_substLHSGen_summand_eq ps k j z₁ g s (hg_abs j hj) t ht_abs

open PowerSeries in
/-- **Pointwise analytic annihilation of `substLHS` on the disk.**
The formal annihilation `frobeniusSolution_is_solution` says every
coefficient of `substLHSGen ps (n+1) z₁ 0 (frobeniusSolution …)` is zero.
Combined with `tsum_coeff_substLHSGen_eq_finsum`, this gives the
pointwise identity on the disk `|t| ≤ s`:
  `∑_{j ∈ range(n+2)} (-1)^j · t^{(n+1)-j} · (taylorShift (ps j) z₁).eval t
     · Σ' m, fallingFactorial (m:ℝ) j · frobeniusCoeff … m · t^m = 0`.
The inner tsums are the Euler-bridge expressions `t^j · V^{(j)}(t)`
(after applying `frobeniusValueDeriv_tsum_euler_k`). -/
theorem pointwise_substLHS_analytic_eq_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n 0 = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ((m : ℝ)) ≠ 0)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| *
          |frobeniusCoeff ps n z₁ 0 c₀ m| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * t ^ ((n + 1) - j) *
          (taylorShift (ps j) z₁).eval t *
          ∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
            frobeniusCoeff ps n z₁ 0 c₀ m * t ^ m = 0 := by
  -- Shift `hnr` to the `ρ = 0` form expected by `frobeniusSolution_is_solution`.
  have hnr' : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ((0 : ℝ) + (m : ℝ)) ≠ 0 := by
    intro m hm; rw [zero_add]; exact hnr m hm
  -- Formal annihilation: every coefficient of `substLHSGen …` is zero.
  have hsol :=
    (frobeniusSolution_is_solution ps n z₁ 0 c₀ hpk hindicial hnr').2
  -- Summability hypothesis in terms of `coeff m (frobeniusSolution …)`.
  have hg_abs' : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) j| *
        |coeff (R := ℝ) m (frobeniusSolution ps n z₁ 0 c₀)| * s ^ m) := by
    intro j hj
    refine (hg_abs j hj).congr (fun m => ?_)
    rw [coeff_frobeniusSolution]
  -- Apply the finset aggregation lemma at `k = n+1`, `g = frobeniusSolution …`.
  have heq := tsum_coeff_substLHSGen_eq_finsum ps (n + 1) z₁
    (frobeniusSolution ps n z₁ 0 c₀) s hg_abs' t ht_abs
  -- LHS tsum vanishes term-by-term.
  have hLHS_zero : (∑' N : ℕ, coeff (R := ℝ) N
      (substLHSGen ps (n + 1) z₁ 0 (frobeniusSolution ps n z₁ 0 c₀)) *
        t ^ N) = 0 := by
    have hterm : ∀ N : ℕ, coeff (R := ℝ) N
        (substLHSGen ps (n + 1) z₁ 0 (frobeniusSolution ps n z₁ 0 c₀)) *
          t ^ N = 0 := fun N => by rw [hsol N, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  rw [hLHS_zero] at heq
  -- `heq : 0 = ∑_j … · (∑' m, … · coeff m (frobeniusSolution …) · t^m)`.
  -- Rewrite `coeff m (frobeniusSolution …)` to `frobeniusCoeff …` term-by-term,
  -- which is exactly the goal's summand.
  simp_rw [coeff_frobeniusSolution] at heq
  exact heq.symm

open PowerSeries in
/-- **Pointwise ODE form after Euler bridging.**
Given Euler-bridge hypotheses `V j` identifying the inner
`fallingFactorial`-weighted tsum with `t^j · V j t` for each
`j ∈ range (n+2)`, and `|t| ≤ s`, the pointwise identity collapses to

  `t^{n+1} · ∑_{j ∈ range (n+2)} (-1)^j · (taylorShift (ps j) z₁).eval t · V j t = 0`.

The factor `t^{n+1}` is the leading Frobenius power; away from `t = 0`
this gives the classical ODE `∑_j (-1)^j · p_j(z₁+t) · V^{(j)}(t) = 0`,
and by continuity of both sides the equation extends to `t = 0`. -/
theorem pointwise_substLHS_ODE_form
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n 0 = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ((m : ℝ)) ≠ 0)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| *
          |frobeniusCoeff ps n z₁ 0 c₀ m| * s ^ m))
    (V : ℕ → ℝ → ℝ)
    (hEuler : ∀ j ∈ Finset.range (n + 2), ∀ t : ℝ, |t| ≤ s →
      (∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
          frobeniusCoeff ps n z₁ 0 c₀ m * t ^ m) = t ^ j * V j t)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    t ^ (n + 1) * ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * (taylorShift (ps j) z₁).eval t * V j t = 0 := by
  have hbase := pointwise_substLHS_analytic_eq_zero
    ps n z₁ c₀ hpk hindicial hnr s hg_abs t ht_abs
  have key : ∑ j ∈ Finset.range (n + 2),
      t ^ (n + 1) *
        ((-1 : ℝ) ^ j * (taylorShift (ps j) z₁).eval t * V j t) = 0 := by
    rw [← hbase]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj_le : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have ht_pow : t ^ ((n + 1) - j) * t ^ j = t ^ (n + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hj_le]
    rw [hEuler j hj t ht_abs, ← ht_pow]
    ring
  rw [← Finset.mul_sum] at key
  exact key

open PowerSeries in
/-- **Pointwise ODE away from the origin.**  Dividing the
`t^{n+1} · F(t) = 0` identity by `t^{n+1}` for `t ≠ 0` on the disk gives
  `∑_{j ∈ range(n+2)} (-1)^j · (taylorShift (ps j) z₁).eval t · V j t = 0`.
The continuity argument that closes the `t = 0` endpoint is separate
(requires continuity of each `V j` at the origin; done once per concrete
`V_j` instantiation). -/
theorem pointwise_ODE_of_analytic_away_from_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n 0 = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ((m : ℝ)) ≠ 0)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| *
          |frobeniusCoeff ps n z₁ 0 c₀ m| * s ^ m))
    (V : ℕ → ℝ → ℝ)
    (hEuler : ∀ j ∈ Finset.range (n + 2), ∀ t : ℝ, |t| ≤ s →
      (∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
          frobeniusCoeff ps n z₁ 0 c₀ m * t ^ m) = t ^ j * V j t)
    (t : ℝ) (ht_abs : |t| ≤ s) (ht_ne : t ≠ 0) :
    ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * (taylorShift (ps j) z₁).eval t * V j t = 0 := by
  have hfac := pointwise_substLHS_ODE_form
    ps n z₁ c₀ hpk hindicial hnr s hg_abs V hEuler t ht_abs
  have ht_pow_ne : t ^ (n + 1) ≠ 0 := pow_ne_zero _ ht_ne
  exact (mul_eq_zero.mp hfac).resolve_left ht_pow_ne

open PowerSeries in
/-- **Closing the `t = 0` endpoint by continuity.**  The ODE identity
from `pointwise_ODE_of_analytic_away_from_zero` holds for every
`t ≠ 0` on the disk; when each `V j` is continuous at `0`, the sum is
continuous at `0` and the identity extends to `t = 0`. -/
theorem pointwise_ODE_of_analytic_at_zero
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n 0 = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ((m : ℝ)) ≠ 0)
    (s : ℝ) (hs_pos : 0 < s)
    (hg_abs : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
        |fallingFactorial ((m : ℕ) : ℝ) j| *
          |frobeniusCoeff ps n z₁ 0 c₀ m| * s ^ m))
    (V : ℕ → ℝ → ℝ)
    (hEuler : ∀ j ∈ Finset.range (n + 2), ∀ t : ℝ, |t| ≤ s →
      (∑' m : ℕ, fallingFactorial ((m : ℕ) : ℝ) j *
          frobeniusCoeff ps n z₁ 0 c₀ m * t ^ m) = t ^ j * V j t)
    (hV_cont : ∀ j ∈ Finset.range (n + 2), ContinuousAt (V j) 0) :
    ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * (taylorShift (ps j) z₁).eval 0 * V j 0 = 0 := by
  set F : ℝ → ℝ := fun t => ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℝ) ^ j) * (taylorShift (ps j) z₁).eval t * V j t with hF_def
  -- `F` tends to `F 0` as `t → 0`: each summand's factors are continuous at 0.
  have hF_tendsto : Filter.Tendsto F (nhds 0) (nhds (F 0)) := by
    change Filter.Tendsto (fun t => ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * (taylorShift (ps j) z₁).eval t * V j t)
        (nhds 0) (nhds (∑ j ∈ Finset.range (n + 2),
          ((-1 : ℝ) ^ j) * (taylorShift (ps j) z₁).eval 0 * V j 0))
    refine tendsto_finset_sum _ (fun j hj => ?_)
    have h_poly : Filter.Tendsto
        (fun t : ℝ => (taylorShift (ps j) z₁).eval t) (nhds 0)
        (nhds ((taylorShift (ps j) z₁).eval 0)) :=
      (taylorShift (ps j) z₁).continuous.continuousAt
    have h_V : Filter.Tendsto (V j) (nhds 0) (nhds (V j 0)) := hV_cont j hj
    exact ((tendsto_const_nhds).mul h_poly).mul h_V
  -- A positive sequence `u k = s / (k + 1)` with `0 < u k ≤ s` and `u k → 0`.
  have hu_pos : ∀ k : ℕ, 0 < s / ((k : ℝ) + 1) := fun k =>
    div_pos hs_pos (by positivity)
  have hu_ne : ∀ k : ℕ, s / ((k : ℝ) + 1) ≠ 0 := fun k => ne_of_gt (hu_pos k)
  have hu_abs : ∀ k : ℕ, |s / ((k : ℝ) + 1)| ≤ s := fun k => by
    rw [abs_of_pos (hu_pos k)]
    exact div_le_self hs_pos.le (by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith)
  have hu_tendsto : Filter.Tendsto (fun k : ℕ => s / ((k : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    have heq : (fun k : ℕ => s / ((k : ℝ) + 1)) =
        fun k : ℕ => s * (1 / ((k : ℝ) + 1)) := by
      funext k; ring
    rw [heq]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul s
  -- `F` vanishes along the sequence.
  have hFu_zero : ∀ k : ℕ, F (s / ((k : ℝ) + 1)) = 0 := fun k =>
    pointwise_ODE_of_analytic_away_from_zero ps n z₁ c₀ hpk hindicial hnr s
      hg_abs V hEuler (s / ((k : ℝ) + 1)) (hu_abs k) (hu_ne k)
  -- Two limits of `F ∘ u` coincide: `F 0` and `0`.
  have h1 : Filter.Tendsto (fun k : ℕ => F (s / ((k : ℝ) + 1)))
      Filter.atTop (nhds (F 0)) := hF_tendsto.comp hu_tendsto
  have h2 : Filter.Tendsto (fun k : ℕ => F (s / ((k : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have : (fun k : ℕ => F (s / ((k : ℝ) + 1))) = fun _ => (0 : ℝ) := by
      funext k; exact hFu_zero k
    rw [this]; exact tendsto_const_nhds
  have hF0 : F 0 = 0 := tendsto_nhds_unique h1 h2
  -- Unfold `F` and conclude.
  simpa [hF_def] using hF0

/-! ## General-ρ pointwise analytic bridge

The ρ = 0 chain above specializes the substitution bridge to the
resonance-free case at the origin. For Apéry's conifold the three
indicial roots are `{0, 1/2, 1}`; the ρ = 0 root is resonant (ρ + 1 = 1
is also a root), so the non-resonant analytic bridge must run through
ρ = 1 or ρ = 1/2. The following theorems lift the per-j summand bridge
and the finset-aggregated analytic identity to arbitrary real ρ, with
the inner tsums now carrying `fallingFactorial (ρ + m) j` instead of
`fallingFactorial m j`. The `t^{n+1}` factoring step is ρ-dependent and
is handled separately per concrete ρ value. -/

open PowerSeries in
/-- **Per-`j` analytic summand bridge at general ρ.** Same structure as
`tsum_substLHSGen_summand_eq`, but with the Frobenius indicial parameter
`ρ` free. The inner tsum weight is `fallingFactorial (ρ + m) j`. -/
theorem tsum_substLHSGen_summand_eq_at_rho
    (ps : ℕ → Polynomial ℝ) (k j : ℕ) (z₁ ρ : ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : Summable (fun m : ℕ =>
        |fallingFactorial (ρ + ((m : ℕ) : ℝ)) j| *
          |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' N : ℕ, coeff (R := ℝ) N
        (((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
          * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
          * fallingEulerOp ρ j g)) * t ^ N) =
      ((-1 : ℝ) ^ j) * t ^ (k - j) *
        (taylorShift (ps j) z₁).eval t *
        ∑' m : ℕ, fallingFactorial (ρ + ((m : ℕ) : ℝ)) j *
          coeff (R := ℝ) m g * t ^ m := by
  have h_coeff_mul : ∀ N : ℕ,
      coeff (R := ℝ) N (((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
          * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
          * fallingEulerOp ρ j g)) * t ^ N =
      ((-1 : ℝ) ^ j) * (coeff (R := ℝ) N ((X : PowerSeries ℝ) ^ (k - j)
            * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
            * fallingEulerOp ρ j g) * t ^ N) := by
    intro N
    rw [PowerSeries.coeff_smul]
    simp [smul_eq_mul, mul_assoc]
  set Pj : Polynomial ℝ := Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ with hPj_def
  have hPj_coe :
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) =
      (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ) := by
    change ((Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ : Polynomial ℝ) :
              PowerSeries ℝ) = _
    push_cast
    rfl
  have hPj_eval :
      Pj.eval t = t ^ (k - j) * (taylorShift (ps j) z₁).eval t := by
    simp [hPj_def]
  have h_eul_abs : Summable (fun m : ℕ =>
      |coeff (R := ℝ) m (fallingEulerOp ρ j g)| * s ^ m) := by
    refine hg_abs.congr (fun m => ?_)
    rw [coeff_fallingEulerOp, abs_mul]
  have h_cauchy :
      Pj.eval t * (∑' m : ℕ, coeff (R := ℝ) m (fallingEulerOp ρ j g) * t ^ m) =
        ∑' N : ℕ, coeff (R := ℝ) N
          (((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp ρ j g) * t ^ N :=
    polyEval_mul_tsum_coeff_eq_tsum_coeff_mul Pj (fallingEulerOp ρ j g) s h_eul_abs t ht_abs
  have h_tsum_eul :
      (∑' m : ℕ, coeff (R := ℝ) m (fallingEulerOp ρ j g) * t ^ m) =
      ∑' m : ℕ, fallingFactorial (ρ + ((m : ℕ) : ℝ)) j *
        coeff (R := ℝ) m g * t ^ m := by
    apply tsum_congr
    intro m
    rw [coeff_fallingEulerOp]
  simp_rw [h_coeff_mul]
  rw [tsum_mul_left]
  rw [show (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
        * fallingEulerOp ρ j g =
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp ρ j g from by
        rw [hPj_coe]]
  rw [← h_cauchy, h_tsum_eul, hPj_eval]
  ring

open PowerSeries in
/-- **Per-`j` summability companion at general ρ.** Lifts
`summable_substLHSGen_summand_coeff_mul_pow` to arbitrary ρ, with the
inner summability hypothesis carrying `fallingFactorial (ρ + m) j`. -/
theorem summable_substLHSGen_summand_coeff_mul_pow_at_rho
    (ps : ℕ → Polynomial ℝ) (k j : ℕ) (z₁ ρ : ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : Summable (fun m : ℕ =>
        |fallingFactorial (ρ + ((m : ℕ) : ℝ)) j| *
          |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    Summable (fun N : ℕ => coeff (R := ℝ) N
        (((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
          * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
          * fallingEulerOp ρ j g)) * t ^ N) := by
  set Pj : Polynomial ℝ := Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ with hPj_def
  have hPj_coe :
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) =
      (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ) := by
    change ((Polynomial.X ^ (k - j) * taylorShift (ps j) z₁ : Polynomial ℝ) :
              PowerSeries ℝ) = _
    push_cast
    rfl
  have h_eul_abs : Summable (fun m : ℕ =>
      |coeff (R := ℝ) m (fallingEulerOp ρ j g)| * s ^ m) := by
    refine hg_abs.congr (fun m => ?_)
    rw [coeff_fallingEulerOp, abs_mul]
  have h_base : Summable (fun N : ℕ => coeff (R := ℝ) N
      (((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp ρ j g) * t ^ N) :=
    summable_coeff_polyPS_mul_mul_pow Pj (fallingEulerOp ρ j g) s h_eul_abs t ht_abs
  have h_scalar := h_base.mul_left ((-1 : ℝ) ^ j)
  refine h_scalar.congr (fun N => ?_)
  rw [PowerSeries.coeff_smul]
  rw [show (X : PowerSeries ℝ) ^ (k - j)
        * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
        * fallingEulerOp ρ j g =
      ((Pj : Polynomial ℝ) : PowerSeries ℝ) * fallingEulerOp ρ j g from by
        rw [hPj_coe]]
  simp [smul_eq_mul, mul_assoc]

open PowerSeries in
/-- **Finset aggregation at general ρ.** Lifts
`tsum_coeff_substLHSGen_eq_finsum` to arbitrary ρ. -/
theorem tsum_coeff_substLHSGen_eq_finsum_at_rho
    (ps : ℕ → Polynomial ℝ) (k : ℕ) (z₁ ρ : ℝ) (g : PowerSeries ℝ)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range (k + 1), Summable (fun m : ℕ =>
        |fallingFactorial (ρ + ((m : ℕ) : ℝ)) j| *
          |coeff (R := ℝ) m g| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    (∑' N : ℕ, coeff (R := ℝ) N (substLHSGen ps k z₁ ρ g) * t ^ N) =
      ∑ j ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ j) * t ^ (k - j) *
          (taylorShift (ps j) z₁).eval t *
          ∑' m : ℕ, fallingFactorial (ρ + ((m : ℕ) : ℝ)) j *
            coeff (R := ℝ) m g * t ^ m := by
  unfold substLHSGen
  have h_coeff_sum_mul : ∀ N : ℕ,
      coeff (R := ℝ) N (∑ j ∈ Finset.range (k + 1),
          ((-1 : ℝ) ^ j) • ((X : PowerSeries ℝ) ^ (k - j)
            * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
            * fallingEulerOp ρ j g)) * t ^ N =
      ∑ j ∈ Finset.range (k + 1),
        coeff (R := ℝ) N (((-1 : ℝ) ^ j) •
          ((X : PowerSeries ℝ) ^ (k - j)
            * ((taylorShift (ps j) z₁ : Polynomial ℝ) : PowerSeries ℝ)
            * fallingEulerOp ρ j g)) * t ^ N := by
    intro N
    rw [map_sum (PowerSeries.coeff (R := ℝ) N) _ _, Finset.sum_mul]
  simp_rw [h_coeff_sum_mul]
  rw [Summable.tsum_finsetSum (fun j hj =>
    summable_substLHSGen_summand_coeff_mul_pow_at_rho
      ps k j z₁ ρ g s (hg_abs j hj) t ht_abs)]
  apply Finset.sum_congr rfl
  intro j hj
  exact tsum_substLHSGen_summand_eq_at_rho ps k j z₁ ρ g s (hg_abs j hj) t ht_abs

open PowerSeries in
/-- **Pointwise analytic annihilation at general ρ.** Lifts
`pointwise_substLHS_analytic_eq_zero` to arbitrary ρ via
`frobeniusSolution_is_solution` (already stated at general ρ) and
`tsum_coeff_substLHSGen_eq_finsum_at_rho`. -/
theorem pointwise_substLHS_analytic_eq_zero_at_rho
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n ρ = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n (ρ + (m : ℝ)) ≠ 0)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
        |fallingFactorial (ρ + ((m : ℕ) : ℝ)) j| *
          |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    ∑ j ∈ Finset.range (n + 2),
        ((-1 : ℝ) ^ j) * t ^ ((n + 1) - j) *
          (taylorShift (ps j) z₁).eval t *
          ∑' m : ℕ, fallingFactorial (ρ + ((m : ℕ) : ℝ)) j *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m = 0 := by
  have hsol := (frobeniusSolution_is_solution ps n z₁ ρ c₀ hpk hindicial hnr).2
  have hg_abs' : ∀ j ∈ Finset.range (n + 2), Summable (fun m : ℕ =>
      |fallingFactorial (ρ + ((m : ℕ) : ℝ)) j| *
        |coeff (R := ℝ) m (frobeniusSolution ps n z₁ ρ c₀)| * s ^ m) := by
    intro j hj; refine (hg_abs j hj).congr (fun m => ?_); rw [coeff_frobeniusSolution]
  have heq := tsum_coeff_substLHSGen_eq_finsum_at_rho ps (n + 1) z₁ ρ
    (frobeniusSolution ps n z₁ ρ c₀) s hg_abs' t ht_abs
  have hLHS_zero : (∑' N : ℕ, coeff (R := ℝ) N
      (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) * t ^ N) = 0 := by
    have hterm : ∀ N : ℕ, coeff (R := ℝ) N
        (substLHSGen ps (n + 1) z₁ ρ (frobeniusSolution ps n z₁ ρ c₀)) *
          t ^ N = 0 := fun N => by rw [hsol N, zero_mul]
    rw [tsum_congr hterm, tsum_zero]
  rw [hLHS_zero] at heq
  simp_rw [coeff_frobeniusSolution] at heq
  exact heq.symm

open PowerSeries in
/-- **Apéry-shape pointwise ODE at ρ = 1.** Specializing
`pointwise_substLHS_analytic_eq_zero_at_rho` to `n = 2`, `ρ = 1`, and the
Apéry shape `ps 0 = 0, ps 1 = 0` collapses the sum over `j ∈ {0,1,2,3}`
to just the `j = 2, 3` terms. Conclusion:
  `t · (taylorShift (ps 2) z₁).eval t · I₂(t)
    = (taylorShift (ps 3) z₁).eval t · I₃(t)`
where `Iⱼ(t) := Σ' m, fallingFactorial (1+m) j · aₘ · tᵐ`. This is
Apéry's conifold-ODE in Frobenius shape, closed on the full disk
`|t| ≤ s`. Division by `t` to extract the pure ODE on `t ≠ 0` is a
subsequent step. -/
theorem pointwise_substLHS_analytic_apery_shape
    (ps : ℕ → Polynomial ℝ) (z₁ c₀ : ℝ)
    (hps0 : ps 0 = 0) (hps1 : ps 1 = 0)
    (hpk : (ps 3).eval z₁ = 0)
    (hindicial :
      simpleZeroIndicialPoly (ps 2) (ps 3) z₁ 2 (1 : ℝ) = 0)
    (hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly (ps 2) (ps 3) z₁ 2 ((1 : ℝ) + (m : ℝ)) ≠ 0)
    (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range 4, Summable (fun m : ℕ =>
        |fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j| *
          |frobeniusCoeff ps 2 z₁ 1 c₀ m| * s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    t * (taylorShift (ps 2) z₁).eval t *
        (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
          frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m) =
      (taylorShift (ps 3) z₁).eval t *
        ∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
          frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m := by
  have hbase :=
    pointwise_substLHS_analytic_eq_zero_at_rho ps 2 z₁ 1 c₀
      hpk hindicial hnr s hg_abs t ht_abs
  -- Expand the sum over j = 0,1,2,3.
  have h_sum_expand :
      ∑ j ∈ Finset.range 4,
          ((-1 : ℝ) ^ j) * t ^ ((2 + 1) - j) *
            (taylorShift (ps j) z₁).eval t *
            ∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m
        = (1 : ℝ) * t ^ 3 * (taylorShift (ps 0) z₁).eval t *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 0 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m)
          + (-1 : ℝ) * t ^ 2 * (taylorShift (ps 1) z₁).eval t *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 1 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m)
          + (1 : ℝ) * t ^ 1 * (taylorShift (ps 2) z₁).eval t *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m)
          + (-1 : ℝ) * t ^ 0 * (taylorShift (ps 3) z₁).eval t *
            (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
              frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
    ring
  rw [h_sum_expand] at hbase
  -- The j=0 and j=1 terms vanish because ps 0 = 0 and ps 1 = 0.
  have h0_zero : (taylorShift (ps 0) z₁).eval t = 0 := by
    rw [hps0]; simp [taylorShift]
  have h1_zero : (taylorShift (ps 1) z₁).eval t = 0 := by
    rw [hps1]; simp [taylorShift]
  rw [h0_zero, h1_zero] at hbase
  -- Simplify and rearrange.
  have : (1 : ℝ) * t ^ 1 * (taylorShift (ps 2) z₁).eval t *
        (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
          frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m)
      + (-1 : ℝ) * t ^ 0 * (taylorShift (ps 3) z₁).eval t *
        (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
          frobeniusCoeff ps 2 z₁ 1 c₀ m * t ^ m) = 0 := by linarith
  linarith [this]

/-! ### _general chain: drops `hpn : (ps n).eval z₁ = 0` via a threshold

The original summability chain requires `pn(z₁) = 0` (the "simple zero"
assumption) so that the constant term of the indicial polynomial
vanishes. The Apéry ζ(3) conifold setting needs the `Q(z₁) ≠ 0` case;
there we replace the simple-zero hypothesis with the *threshold*
`2·|pn(z₁)| ≤ |pn1'(z₁)| · (m+1 − |ρ| − n)`, which holds for every
sufficiently large `m`. Chasing through the chain costs only a constant
factor of `2` in the geometric-majorant ratio `K`. -/

/-- **Lower bound on `|simpleZeroIndicialPoly|` — general (no `pn(z₁)=0`).**

Under the threshold
`2·|pn(z₁)| ≤ |pn1'(z₁)| · ((m+1) − |ρ| − n)`
we still get a polynomial growth lower bound for the indicial at the
shifted argument `ρ + (m+1)`, but with an extra factor of `1/2`:

  Δ^{n+1} · |pn1'(z₁)| / 2 ≤ |indicial(ρ + (m+1))|,

where `Δ := (m+1) − |ρ| − n`. -/
lemma simpleZeroIndicialPoly_abs_lower_bound_general
    (pn pn1 : Polynomial ℝ) (z₁ : ℝ) (n : ℕ) (ρ : ℝ) (m : ℕ)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (h_thresh : 2 * |pn.eval z₁| ≤
        |(Polynomial.derivative pn1).eval z₁| *
          (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ))) :
    (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
      |(Polynomial.derivative pn1).eval z₁| / 2 ≤
    |simpleZeroIndicialPoly pn pn1 z₁ n (ρ + ((m + 1 : ℕ) : ℝ))| := by
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hMdef
  set Δ : ℝ := M - |ρ| - (n : ℝ) with hΔdef
  have hff : Δ ^ n ≤ fallingFactorial (ρ + M) n :=
    fallingFactorial_shifted_lower_bound ρ n (m + 1) hm
  have hΔ_pos : 0 < Δ := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    simp [hΔdef]; linarith
  have hΔ_nn : 0 ≤ Δ := le_of_lt hΔ_pos
  have hrin : Δ ≤ (ρ + M) - (n : ℝ) := by
    have hρ_ge : -ρ ≤ |ρ| := neg_le_abs ρ
    simp [hΔdef]; linarith
  have hrin_pos : 0 < (ρ + M) - (n : ℝ) := lt_of_lt_of_le hΔ_pos hrin
  have hff_nn : 0 ≤ fallingFactorial (ρ + M) n :=
    le_trans (pow_nonneg hΔ_nn n) hff
  have hE_nn : 0 ≤ |(Polynomial.derivative pn1).eval z₁| := abs_nonneg _
  -- Work on the factored form.
  rw [simpleZeroIndicialPoly_factor]
  -- Rewrite `ρ + M - n` variations.
  set E : ℝ := (Polynomial.derivative pn1).eval z₁ with hEdef
  set P : ℝ := pn.eval z₁ with hPdef
  -- Bracket bound: |E·(ρ+M-n) + P| ≥ |E|·(ρ+M-n) − |P| ≥ |E|·Δ − |P| ≥ |E|·Δ/2.
  have habs_EΔ : |E| * Δ ≤ |E| * ((ρ + M) - (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hrin hE_nn
  have habs_mul_eq : |E * ((ρ + M) - (n : ℝ))| = |E| * ((ρ + M) - (n : ℝ)) := by
    rw [abs_mul, abs_of_pos hrin_pos]
  -- Use: |a + b| ≥ |a| − |b|.
  have htri :
      |E| * ((ρ + M) - (n : ℝ)) - |P| ≤
        |E * ((ρ + M) - (n : ℝ)) + P| := by
    have h1 : |E * ((ρ + M) - (n : ℝ))| ≤
        |E * ((ρ + M) - (n : ℝ)) + P| + |P| := by
      have := abs_add_le (E * ((ρ + M) - (n : ℝ)) + P) (-P)
      have hneg : |(-P)| = |P| := abs_neg _
      have heq : E * ((ρ + M) - (n : ℝ)) + P + -P = E * ((ρ + M) - (n : ℝ)) := by ring
      rw [heq] at this
      linarith [this, hneg.le, hneg.ge]
    rw [habs_mul_eq] at h1
    linarith
  -- From h_thresh: 2·|P| ≤ |E|·((m+1)-|ρ|-n), i.e. 2·|P| ≤ |E|·Δ, so |E|·Δ − |P| ≥ |E|·Δ/2.
  have h_thresh' : 2 * |P| ≤ |E| * Δ := by
    simp [hPdef, hEdef, hΔdef]; linarith [h_thresh]
  have hhalf : |E| * Δ / 2 ≤ |E| * Δ - |P| := by linarith
  have hbracket_lb :
      |E| * Δ / 2 ≤ |E * ((ρ + M) - (n : ℝ)) + P| := by
    have : |E| * Δ - |P| ≤ |E| * ((ρ + M) - (n : ℝ)) - |P| := by linarith [habs_EΔ]
    linarith [htri, hhalf, this]
  -- Combine with fallingFactorial lower bound.
  have hbracket_nn : 0 ≤ |E * ((ρ + M) - (n : ℝ)) + P| := abs_nonneg _
  -- The factored form equals fallingFactorial (ρ+M) n * (P + E·(ρ+M-n)).
  have hprod_eq :
      |fallingFactorial (ρ + M) n * (P + E * ((ρ + M) - (n : ℝ)))| =
      fallingFactorial (ρ + M) n * |E * ((ρ + M) - (n : ℝ)) + P| := by
    rw [abs_mul, abs_of_nonneg hff_nn]
    congr 1
    rw [show P + E * ((ρ + M) - (n : ℝ)) = E * ((ρ + M) - (n : ℝ)) + P from by ring]
  have hhalfEΔ_nn : 0 ≤ |E| * Δ / 2 := by positivity
  have h_step1 :
      Δ ^ n * (|E| * Δ / 2) ≤
      fallingFactorial (ρ + M) n * |E * ((ρ + M) - (n : ℝ)) + P| :=
    mul_le_mul hff hbracket_lb hhalfEΔ_nn hff_nn
  -- rearrange LHS: Δ^n · (|E|·Δ/2) = Δ^{n+1} · |E| / 2
  have h_LHS_eq :
      Δ ^ n * (|E| * Δ / 2) = Δ ^ (n + 1) * |E| / 2 := by
    rw [pow_succ]; ring
  rw [h_LHS_eq] at h_step1
  -- assemble
  have : |fallingFactorial (ρ + M) n * (P + E * ((ρ + M) - (n : ℝ)))| =
      fallingFactorial (ρ + M) n * |E * ((ρ + M) - (n : ℝ)) + P| := hprod_eq
  rw [this]
  -- Rewrite goal's indicial factored form to match.
  change Δ ^ (n + 1) * |E| / 2 ≤
    fallingFactorial (ρ + M) n * |E * ((ρ + M) - (n : ℝ)) + P|
  exact h_step1

/-- **Gronwall-form recurrence bound — general (no `pn(z₁)=0`).**
Same shape as `abs_frobeniusCoeff_succ_gronwall_simple_zero`, but with
an extra factor of `2` on the RHS, arising from the half-strength
denominator lower bound `simpleZeroIndicialPoly_abs_lower_bound_general`.
-/
theorem abs_frobeniusCoeff_succ_gronwall_simple_zero_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (h_thresh : 2 * |(ps n).eval z₁| ≤
        |(Polynomial.derivative (ps (n + 1))).eval z₁| *
          (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      ((((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      2 * ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          (((n + 2 : ℕ) : ℝ) * B *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) := by
  set L : ℝ := (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hLdef
  have hLB_half :
      L / 2 ≤ |simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
             (ρ + ((m + 1 : ℕ) : ℝ))| :=
    simpleZeroIndicialPoly_abs_lower_bound_general
      (ps n) (ps (n + 1)) z₁ n ρ m hm h_thresh
  have hΔ_pos : 0 < ((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hL_pos : 0 < L := by
    have h1 : 0 < (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) :=
      pow_pos hΔ_pos _
    have h2 : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
      abs_pos.mpr hslope
    exact mul_pos h1 h2
  have hL_half_pos : 0 < L / 2 := by linarith
  have habs_neg_one_pow : |((-1 : ℝ) ^ n)| = 1 := by
    rw [abs_pow]; simp
  have hD_abs :
      L / 2 ≤ |((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))| := by
    rw [abs_mul, habs_neg_one_pow, one_mul]
    exact hLB_half
  have hD_ne : ((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ)) ≠ 0 := by
    intro h
    have hzero : |((-1 : ℝ) ^ n) *
      simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
        (ρ + ((m + 1 : ℕ) : ℝ))| = 0 := by rw [h]; exact abs_zero
    linarith
  have hmain :=
    abs_frobeniusCoeff_succ_bound ps n z₁ ρ c₀ m hpk hD_ne B hB_nn hB
  -- hmain: |a_{m+1}| · |D| ≤ RHS_original.
  -- From hD_abs: L/2 ≤ |D|, so |a_{m+1}| · L/2 ≤ |a_{m+1}| · |D| ≤ RHS.
  have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
  have hLHS :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * (L / 2) ≤
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
          |((-1 : ℝ) ^ n) *
            simpleZeroIndicialPoly (ps n) (ps (n + 1)) z₁ n
              (ρ + ((m + 1 : ℕ) : ℝ))| :=
    mul_le_mul_of_nonneg_left hD_abs h_abs_a_nn
  have hchain : |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * (L / 2) ≤
      ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          (((n + 2 : ℕ) : ℝ) * B *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) :=
    le_trans hLHS hmain
  -- Multiply both sides by 2.
  linarith [hchain]

/-- **Uniform Gronwall inequality — general.** Companion of
`abs_frobeniusCoeff_succ_gronwall_uniform`, with the extra factor of 2
on the RHS. -/
theorem abs_frobeniusCoeff_succ_gronwall_uniform_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (h_thresh : 2 * |(ps n).eval z₁| ≤
        |(Polynomial.derivative (ps (n + 1))).eval z₁| *
          (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      ((((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      2 * ((n + 2 : ℕ) : ℝ) * B *
        (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) *
        ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| := by
  have hG := abs_frobeniusCoeff_succ_gronwall_simple_zero_general
    ps n z₁ ρ c₀ m hpk hslope hm h_thresh B hB_nn hB
  refine le_trans hG ?_
  -- RHS of hG: 2 * ∑ i, |a_i| * ((n+2)·B · weight_i).
  -- Goal RHS: 2·(n+2)·B · weight_max · ∑ i, |a_i|.
  set C : ℝ := ((n + 2 : ℕ) : ℝ) * B *
                (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) with hCdef
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact hB_nn
    · apply pow_nonneg
      have h1 : (0 : ℝ) ≤ |ρ| := abs_nonneg _
      have h2 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
  have h_sum_le :
      ∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i| *
          (((n + 2 : ℕ) : ℝ) * B *
            (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) ≤
      C * ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i ≤ m := by
      have := Finset.mem_range.mp hi; omega
    have hwbd : (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
                (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      weight_poly_uniform_bound ρ n i m hi_le
    have hCoeff_nn : 0 ≤ ((n + 2 : ℕ) : ℝ) * B := by
      apply mul_nonneg
      · positivity
      · exact hB_nn
    have hInner :
        ((n + 2 : ℕ) : ℝ) * B *
          (|ρ + (i : ℝ)| + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
        ((n + 2 : ℕ) : ℝ) * B *
          (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hwbd hCoeff_nn
    have h_abs_a_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ i| := abs_nonneg _
    have := mul_le_mul_of_nonneg_left hInner h_abs_a_nn
    linarith [this, h_abs_a_nn, hC_nn]
  -- Now scale by 2.
  have h_sum_nn : 0 ≤ ∑ i ∈ Finset.range (m + 1),
      |frobeniusCoeff ps n z₁ ρ c₀ i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith [h_sum_le, h_sum_nn, hC_nn]

/-- **Contracted Frobenius recurrence bound — general.** Companion of
`abs_frobeniusCoeff_succ_contracted`, with the factor of 2 absorbed
into the numerator. -/
theorem abs_frobeniusCoeff_succ_contracted_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (m : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hm_small : (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hm_large : 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh : 2 * |(ps n).eval z₁| ≤
        |(Polynomial.derivative (ps (n + 1))).eval z₁| *
          (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      |(Polynomial.derivative (ps (n + 1))).eval z₁| ≤
      2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) *
        ∑ i ∈ Finset.range (m + 1),
          |frobeniusCoeff ps n z₁ ρ c₀ i| := by
  have hG := abs_frobeniusCoeff_succ_gronwall_uniform_general
    ps n z₁ ρ c₀ m hpk hslope hm_small h_thresh B hB_nn hB
  have hr := weight_to_denominator_pow_bounded ρ n m hm_large
  set Δpow : ℝ := (((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)) ^ (n + 1) with hΔpow_def
  set S : ℝ :=
    ∑ i ∈ Finset.range (m + 1), |frobeniusCoeff ps n z₁ ρ c₀ i| with hS_def
  set C : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B with hC_def
  have hΔ_pos : 0 < ((m + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ) := by
    have hρ_nn : 0 ≤ |ρ| := abs_nonneg _
    linarith
  have hΔpow_pos : 0 < Δpow := pow_pos hΔ_pos _
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · positivity
    · exact hB_nn
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_step1 :
      C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * S ≤
      C * ((2:ℝ)^(n+1) * Δpow) * S := by
    have h1 : C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) ≤
              C * ((2:ℝ)^(n+1) * Δpow) :=
      mul_le_mul_of_nonneg_left hr hC_nn
    exact mul_le_mul_of_nonneg_right h1 hS_nn
  -- hG: |a_{m+1}| · (Δpow · |pn1'|) ≤ 2·(n+2)·B · weight_max · S = C · weight_max · S.
  have hG' :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
      C * ((2:ℝ)^(n+1) * Δpow) * S := by
    have hstep : C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * S =
        2 * ((n + 2 : ℕ) : ℝ) * B *
          (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * S := by
      rw [hC_def]
    have hG'' :
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
          (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) ≤
        C * (|ρ| + (m : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) * S := by
      rw [hstep]
      exact hG
    exact le_trans hG'' h_step1
  have h_reassoc_L :
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        (Δpow * |(Polynomial.derivative (ps (n + 1))).eval z₁|) =
      (|frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) * Δpow := by ring
  have h_reassoc_R :
      C * ((2:ℝ)^(n+1) * Δpow) * S =
      (C * (2:ℝ)^(n+1) * S) * Δpow := by ring
  rw [h_reassoc_L, h_reassoc_R] at hG'
  have h_final : |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      |(Polynomial.derivative (ps (n + 1))).eval z₁| ≤
      C * (2:ℝ)^(n+1) * S :=
    le_of_mul_le_mul_right hG' hΔpow_pos
  -- Now C = 2·(n+2)·B; goal wants 2·(n+2)·B·2^{n+1}·S.
  have heq : C * (2:ℝ)^(n+1) * S =
      2 * ((n + 2 : ℕ) : ℝ) * B * (2:ℝ)^(n+1) * S := by
    rw [hC_def]
  rw [heq] at h_final
  exact h_final

/-- **Frobenius geometric majorant — general.** Same shape as
`frobeniusCoeff_sum_geometric_majorant`, but with
`K = 2·(n+2)·B·2^{n+1}/|pn1'|` (doubled) and with the threshold
hypothesis replacing the simple-zero hypothesis. -/
theorem frobeniusCoeff_sum_geometric_majorant_general
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
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    ∀ m, M₀ ≤ m →
      (∑ i ∈ Finset.range (m + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i|) ≤
      (∑ i ∈ Finset.range (M₀ + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i|) *
          (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
            |(Polynomial.derivative (ps (n + 1))).eval z₁|) ^ (m - M₀) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · positivity
          · positivity
        · exact hB_nn
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have h_rec : ∀ m, M₀ ≤ m →
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| ≤
        K * ∑ i ∈ Finset.range (m + 1),
              |frobeniusCoeff ps n z₁ ρ c₀ i| := by
    intro m hm
    have h1 := hM0_small m hm
    have h2 := hM0_large m hm
    have h3 := h_thresh_general m hm
    have h_contract := abs_frobeniusCoeff_succ_contracted_general
      ps n z₁ ρ c₀ m hpk hslope h1 h2 h3 B hB_nn hB
    have hK_rewrite :
        K * ∑ i ∈ Finset.range (m + 1),
              |frobeniusCoeff ps n z₁ ρ c₀ i| =
        (2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) *
          ∑ i ∈ Finset.range (m + 1),
            |frobeniusCoeff ps n z₁ ρ c₀ i|) /
        |(Polynomial.derivative (ps (n + 1))).eval z₁| := by
      change 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
            |(Polynomial.derivative (ps (n + 1))).eval z₁| * _ = _
      rw [div_mul_eq_mul_div]
    rw [hK_rewrite, le_div_iff₀ hslope_pos]
    exact h_contract
  intro m hm
  exact discrete_gronwall_iteration
    (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m|) K hK_nn M₀ h_rec m hm

/-- **Pointwise geometric bound — general.** -/
theorem abs_frobeniusCoeff_pointwise_geometric_general
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
        |Polynomial.coeff (taylorShift (ps j) z₁) ℓ| ≤ B) :
    ∀ m, M₀ ≤ m →
      |frobeniusCoeff ps n z₁ ρ c₀ m| ≤
      (∑ i ∈ Finset.range (M₀ + 1),
        |frobeniusCoeff ps n z₁ ρ c₀ i|) *
        (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
          |(Polynomial.derivative (ps (n + 1))).eval z₁|) ^ (m - M₀) := by
  intro m hm
  have hsum :=
    frobeniusCoeff_sum_geometric_majorant_general
      ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB m hm
  have hmem : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have h_single :
      |frobeniusCoeff ps n z₁ ρ c₀ m| ≤
        ∑ i ∈ Finset.range (m + 1),
          |frobeniusCoeff ps n z₁ ρ c₀ i| :=
    Finset.single_le_sum (f := fun i => |frobeniusCoeff ps n z₁ ρ c₀ i|)
      (fun i _ => abs_nonneg _) hmem
  exact le_trans h_single hsum

/-- **Absolute summability — general.** -/
theorem frobeniusCoeff_abs_mul_pow_summable_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · positivity
          · positivity
        · exact hB_nn
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := mul_nonneg hSmaj_nn (pow_nonneg hs_nn _)
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_
    ((summable_geometric_of_lt_one hr_nn hr_lt_1).mul_left C)
  · intro k
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hs_nn _)
  · intro k
    have hpt := abs_frobeniusCoeff_pointwise_geometric_general
      ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB (k + M₀) (Nat.le_add_left M₀ k)
    have hsub : k + M₀ - M₀ = k := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have step1 :
        |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| * s ^ (k + M₀) ≤
          (Smaj * (1 + K) ^ k) * s ^ (k + M₀) :=
      mul_le_mul_of_nonneg_right hpt hs_pow_nn
    have step2 :
        (Smaj * (1 + K) ^ k) * s ^ (k + M₀) = C * r ^ k := by
      rw [hC_def, hr_def, mul_pow, pow_add]
      ring
    linarith [step1, step2.le, step2.ge]

/-- **Shifted absolute summability — general.** From the absolute
summability of `|aₘ| · sᵐ`, the shifted series `|aₘ₊₁| · sᵐ` is also
summable. The path: shift by 1 via `summable_nat_add_iff` to get
`|aₘ₊₁| · sᵐ⁺¹` summable, then divide by `s` (when `s > 0`); the
`s = 0` case is trivial finite-support summability. Building block
for tail-tsum sup-norm bounds in the Gap E witness construction. -/
theorem frobeniusCoeff_abs_mul_pow_summable_shift_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m => |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m) := by
  by_cases hs_zero : s = 0
  · subst hs_zero
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℕ))
    intro m hm
    have hm_ne : m ≠ 0 := by simpa using hm
    rw [zero_pow hm_ne, mul_zero]
  · have hpos : 0 < s := lt_of_le_of_ne hs_nn (Ne.symm hs_zero)
    have habs := frobeniusCoeff_abs_mul_pow_summable_general
      ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB s hs_nn hs_lt
    have hshifted : Summable (fun m => |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
        s ^ (m + 1)) := (summable_nat_add_iff 1).mpr habs
    have h_eq : (fun m => |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m) =
                (fun m => (|frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
                  s ^ (m + 1)) / s) := by
      funext m
      rw [pow_succ]
      field_simp
    rw [h_eq]
    exact hshifted.div_const s

/-- **Tail tsum sup-norm bound (general).** For any `t` in the doubled
disk, the tail series `∑' m, aₘ₊₁ · tᵐ` has absolute value bounded by
the absolute-coefficient tail tsum at `|t|`. Combines the shifted
absolute summability with `norm_tsum_le_tsum_norm`. The key analytic
inequality powering the small-ε control of `core(ε) − 1`. -/
theorem frobeniusCoeff_tail_tsum_abs_le_general
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
    (t : ℝ)
    (ht : |t| * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    |∑' m, frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m| ≤
      ∑' m, |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ m := by
  have habs_summ := frobeniusCoeff_abs_mul_pow_summable_shift_general
    ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
    B hB_nn hB |t| (abs_nonneg t) ht
  have h_pointwise : ∀ m,
      ‖frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m‖ =
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ m := by
    intro m
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have habs_summ' :
      Summable (fun m => ‖frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m‖) := by
    have h_eq : (fun m => ‖frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m‖) =
                (fun m => |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ m) :=
      funext h_pointwise
    rw [h_eq]; exact habs_summ
  have hbound := norm_tsum_le_tsum_norm habs_summ'
  rw [Real.norm_eq_abs] at hbound
  have h_eq : (fun m => ‖frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m‖) =
              (fun m => |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ m) :=
    funext h_pointwise
  rw [h_eq] at hbound
  exact hbound

/-- **General fallingFactorial-weighted absolute summability — general.**
Companion of `frobeniusCoeff_fallingFactorial_abs_mul_pow_summable`. -/
theorem frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ) (j : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j' ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m : ℕ => |fallingFactorial ((m : ℕ) : ℝ) j| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * s ^ M₀ * (((M₀ + j + 1 : ℕ) : ℝ) ^ j) with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact hSmaj_nn
    · exact pow_nonneg hs_nn _
    · exact pow_nonneg (Nat.cast_nonneg _) _
  have h_desc : Summable (fun k : ℕ => (((k + j).descFactorial j : ℕ) : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one j hr_norm
  have h_pow_le_desc : ∀ (kk jj : ℕ), (kk + 1) ^ jj ≤ (kk + jj).descFactorial jj := by
    intro kk jj
    have h := Nat.pow_sub_le_descFactorial (kk + jj) jj
    have hsub : (kk + jj) + 1 - jj = kk + 1 := by omega
    rw [hsub] at h
    exact h
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ (h_desc.mul_left C)
  · intro k
    refine mul_nonneg (mul_nonneg ?_ (abs_nonneg _)) (pow_nonneg hs_nn _)
    exact abs_nonneg _
  intro k
  have h_ff_abs :
      |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| ≤ (((k + M₀ + j : ℕ) : ℝ)) ^ j := by
    have h := abs_fallingFactorial_le ((k + M₀ : ℕ) : ℝ) j
    have habs : |((k + M₀ : ℕ) : ℝ)| = ((k + M₀ : ℕ) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    have hcast : ((k + M₀ : ℕ) : ℝ) + (j : ℝ) = ((k + M₀ + j : ℕ) : ℝ) := by
      push_cast; ring
    rw [habs, hcast] at h
    exact h
  have h_factor_le : (k + M₀ + j : ℕ) ≤ (M₀ + j + 1) * (k + 1) := by
    have : (M₀ + j + 1) * (k + 1) = k + M₀ + j + ((M₀ + j) * k + 1) := by ring
    omega
  have h_factor_le_R :
      ((k + M₀ + j : ℕ) : ℝ) ≤ ((M₀ + j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h_factor_le
    push_cast at this ⊢; linarith
  have h_kMj_nn : (0 : ℝ) ≤ ((k + M₀ + j : ℕ) : ℝ) := Nat.cast_nonneg _
  have h_pow_factor :
      ((k + M₀ + j : ℕ) : ℝ) ^ j ≤
        (((M₀ + j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ j :=
    pow_le_pow_left₀ h_kMj_nn h_factor_le_R j
  have h_desc_lower_nat : (k + 1) ^ j ≤ (k + j).descFactorial j := h_pow_le_desc k j
  have h_desc_lower_R :
      ((k + 1 : ℕ) : ℝ) ^ j ≤ (((k + j).descFactorial j : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h_desc_lower_nat
    push_cast at this ⊢; linarith
  have h_idx : M₀ ≤ k + M₀ := by omega
  have hpt :=
    abs_frobeniusCoeff_pointwise_geometric_general
      ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB (k + M₀) h_idx
  have hsub : k + M₀ - M₀ = k := by omega
  rw [hsub] at hpt
  have h_a_nn : (0 : ℝ) ≤ |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| := abs_nonneg _
  have h_s_nn_k : (0 : ℝ) ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
  have h_pow_Mj_nn : (0 : ℝ) ≤ ((M₀ + j + 1 : ℕ) : ℝ) ^ j := pow_nonneg (Nat.cast_nonneg _) _
  have hmaj_nn : (0 : ℝ) ≤ Smaj * (1 + K) ^ k :=
    mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _)
  have step1 :
      |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| *
        |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| * s ^ (k + M₀) ≤
      (((k + M₀ + j : ℕ) : ℝ) ^ j) * (Smaj * (1 + K) ^ k) * s ^ (k + M₀) := by
    have hA : |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| *
              |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| ≤
              (((k + M₀ + j : ℕ) : ℝ) ^ j) * (Smaj * (1 + K) ^ k) :=
      mul_le_mul h_ff_abs hpt h_a_nn (pow_nonneg h_kMj_nn j)
    exact mul_le_mul_of_nonneg_right hA h_s_nn_k
  have step2 :
      (((k + M₀ + j : ℕ) : ℝ) ^ j) * (Smaj * (1 + K) ^ k) * s ^ (k + M₀) ≤
      ((((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ)) *
        (Smaj * (1 + K) ^ k) * s ^ (k + M₀) := by
    have h_A :
        ((((M₀ + j + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ)) ^ j =
        ((((M₀ + j + 1 : ℕ) : ℝ))) ^ j * (((k + 1 : ℕ) : ℝ)) ^ j := mul_pow _ _ _
    have h_k1_to_desc :
        (((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + 1 : ℕ) : ℝ)) ^ j ≤
        (((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h_desc_lower_R h_pow_Mj_nn
    have h_tot :
        (((k + M₀ + j : ℕ) : ℝ)) ^ j ≤
        (((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ) := by
      calc (((k + M₀ + j : ℕ) : ℝ)) ^ j
          ≤ ((((M₀ + j + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ)) ^ j := h_pow_factor
        _ = _ := h_A
        _ ≤ _ := h_k1_to_desc
    have := mul_le_mul_of_nonneg_right h_tot hmaj_nn
    exact mul_le_mul_of_nonneg_right this h_s_nn_k
  have step3 :
      ((((M₀ + j + 1 : ℕ) : ℝ)) ^ j * (((k + j).descFactorial j : ℕ) : ℝ)) *
        (Smaj * (1 + K) ^ k) * s ^ (k + M₀) =
      C * ((((k + j).descFactorial j : ℕ) : ℝ) * r ^ k) := by
    rw [hC_def, hr_def, mul_pow, pow_add]
    ring
  calc |fallingFactorial ((k + M₀ : ℕ) : ℝ) j| *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀)| * s ^ (k + M₀)
      ≤ _ := step1
    _ ≤ _ := step2
    _ = C * ((((k + j).descFactorial j : ℕ) : ℝ) * r ^ k) := step3

/-- Embed a 4-tuple of polynomials as an ℕ-indexed sequence for use
with `substLHSGen`. -/
noncomputable def aperyPsSeq
    (p0 p1 p2 p3 : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | _ + 4 => 0

open PowerSeries in
/-- **Consistency.** The hand-written order-3 `substLHS` coincides with
`substLHSGen` instantiated at `k = 3` and the 4-tuple-to-ℕ embedding. -/
theorem substLHS_eq_substLHSGen
    (p0 p1 p2 p3 : Polynomial ℝ) (z₁ ρ : ℝ) (g : PowerSeries ℝ) :
    substLHS p0 p1 p2 p3 z₁ ρ g =
      substLHSGen (aperyPsSeq p0 p1 p2 p3) 3 z₁ ρ g := by
  unfold substLHS substLHSGen
  rw [show (3 + 1 : ℕ) = 4 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
  simp [aperyPsSeq, pow_zero, pow_succ, show (3 - 0 : ℕ) = 3 from rfl,
        show (3 - 1 : ℕ) = 2 from rfl, show (3 - 2 : ℕ) = 1 from rfl]
  ring

/-- **Shift-by-one identity for falling factorial.**
`fallingFactorial (x + 1) k = fallingFactorial x k + k · fallingFactorial x (k-1)`.
Proved by induction on `k` using the recursive definition. -/
lemma fallingFactorial_add_one (x : ℝ) (k : ℕ) :
    fallingFactorial (x + 1) k =
      fallingFactorial x k + (k : ℝ) * fallingFactorial x (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [fallingFactorial_succ (x + 1) k, ih]
    cases k with
    | zero => simp [fallingFactorial]
    | succ k' =>
      have hsub1 : (k' + 1 + 1 - 1 : ℕ) = k' + 1 := rfl
      have hsub2 : (k' + 1 - 1 : ℕ) = k' := rfl
      rw [hsub1, hsub2]
      rw [show fallingFactorial x (k' + 1 + 1) =
            fallingFactorial x (k' + 1) * (x - ((k' + 1 : ℕ) : ℝ))
          from fallingFactorial_succ x (k' + 1)]
      rw [show fallingFactorial x (k' + 1) =
            fallingFactorial x k' * (x - ((k' : ℕ) : ℝ))
          from fallingFactorial_succ x k']
      push_cast
      ring

/-- **Summability bridge: ρ = 0 → ρ = 1 form.** Using the shift-by-one
identity, summability of `|fallingFactorial m j| · |aₘ| · sᵐ` at two
consecutive j values upgrades to summability of
`|fallingFactorial (1+m) j| · |aₘ| · sᵐ`. For `j ∈ {0,1,2,3}` at ρ = 1,
all fallingFactorial values are nonneg, so the triangle-inequality step
is tight (equality on summands). -/
theorem frobeniusCoeff_fallingFactorial_shift_one_abs_mul_pow_summable
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ) (j : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hpn : (ps n).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j' ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m : ℕ => |fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  -- Base summability at j and j-1 (the latter only used when j ≥ 1).
  have h_base_j : Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) j| *
      |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
    frobeniusCoeff_fallingFactorial_abs_mul_pow_summable
      ps n z₁ ρ c₀ M₀ j hpk hpn hslope hM0_small hM0_large B hB_nn hB
      s hs_nn hs_lt
  have h_base_prev : Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
      |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
    frobeniusCoeff_fallingFactorial_abs_mul_pow_summable
      ps n z₁ ρ c₀ M₀ (j - 1) hpk hpn hslope hM0_small hM0_large B hB_nn hB
      s hs_nn hs_lt
  -- The sum `A + j·B` is summable.
  have h_sum : Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) j| *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
      + (j : ℝ) * (|fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m)) :=
    h_base_j.add (h_base_prev.mul_left (j : ℝ))
  refine Summable.of_nonneg_of_le ?_ ?_ h_sum
  · intro m
    refine mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
    exact pow_nonneg hs_nn _
  · intro m
    have hff : fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j =
        fallingFactorial ((m : ℕ) : ℝ) j +
          (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1) := by
      have := fallingFactorial_add_one ((m : ℕ) : ℝ) j
      rw [add_comm ((m : ℕ) : ℝ) 1] at this
      exact this
    rw [hff]
    have h_tri : |fallingFactorial ((m : ℕ) : ℝ) j +
        (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| ≤
        |fallingFactorial ((m : ℕ) : ℝ) j| +
          (j : ℝ) * |fallingFactorial ((m : ℕ) : ℝ) (j - 1)| := by
      have h_step1 : |fallingFactorial ((m : ℕ) : ℝ) j +
              (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)|
            ≤ |fallingFactorial ((m : ℕ) : ℝ) j| +
              |(j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| := by
        simpa [Real.norm_eq_abs] using
          norm_add_le (fallingFactorial ((m : ℕ) : ℝ) j)
            ((j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1))
      have h_step2 : |(j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)|
            = (j : ℝ) * |fallingFactorial ((m : ℕ) : ℝ) (j - 1)| := by
        rw [abs_mul]
        congr 1
        exact abs_of_nonneg (Nat.cast_nonneg j)
      linarith
    have h_abs_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    have hs_pow_nn : 0 ≤ s ^ m := pow_nonneg hs_nn _
    have h_acc_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
      mul_nonneg h_abs_nn hs_pow_nn
    calc |fallingFactorial ((m : ℕ) : ℝ) j +
            (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
          |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
        = |fallingFactorial ((m : ℕ) : ℝ) j +
            (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
            (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring
      _ ≤ (|fallingFactorial ((m : ℕ) : ℝ) j| +
            (j : ℝ) * |fallingFactorial ((m : ℕ) : ℝ) (j - 1)|) *
            (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
          mul_le_mul_of_nonneg_right h_tri h_acc_nn
      _ = |fallingFactorial ((m : ℕ) : ℝ) j| *
            |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
          + (j : ℝ) * (|fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
            |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring

/-- **Shifted fallingFactorial-weighted absolute summability — general.**
Companion of `frobeniusCoeff_fallingFactorial_shift_one_abs_mul_pow_summable`. -/
theorem frobeniusCoeff_fallingFactorial_shift_one_abs_mul_pow_summable_general
    (ps : ℕ → Polynomial ℝ) (n : ℕ) (z₁ ρ c₀ : ℝ) (M₀ : ℕ) (j : ℕ)
    (hpk : (ps (n + 1)).eval z₁ = 0)
    (hslope : (Polynomial.derivative (ps (n + 1))).eval z₁ ≠ 0)
    (hM0_small : ∀ m, M₀ ≤ m → (|ρ| + (n : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |ρ| + 3 * (n : ℝ) ≤ (m : ℝ))
    (h_thresh_general : ∀ m', M₀ ≤ m' →
        2 * |(ps n).eval z₁| ≤
          |(Polynomial.derivative (ps (n + 1))).eval z₁| *
            (((m' + 1 : ℕ) : ℝ) - |ρ| - (n : ℝ)))
    (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ j' ∈ Finset.range (n + 2), ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m : ℕ => |fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j| *
                |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
  have h_base_j : Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) j| *
      |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
    frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
      ps n z₁ ρ c₀ M₀ j hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB s hs_nn hs_lt
  have h_base_prev : Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
      |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
    frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
      ps n z₁ ρ c₀ M₀ (j - 1) hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB s hs_nn hs_lt
  have h_sum : Summable (fun m : ℕ =>
      |fallingFactorial ((m : ℕ) : ℝ) j| *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
      + (j : ℝ) * (|fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m)) :=
    h_base_j.add (h_base_prev.mul_left (j : ℝ))
  refine Summable.of_nonneg_of_le ?_ ?_ h_sum
  · intro m
    refine mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
    exact pow_nonneg hs_nn _
  · intro m
    have hff : fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j =
        fallingFactorial ((m : ℕ) : ℝ) j +
          (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1) := by
      have := fallingFactorial_add_one ((m : ℕ) : ℝ) j
      rw [add_comm ((m : ℕ) : ℝ) 1] at this
      exact this
    rw [hff]
    have h_tri : |fallingFactorial ((m : ℕ) : ℝ) j +
        (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| ≤
        |fallingFactorial ((m : ℕ) : ℝ) j| +
          (j : ℝ) * |fallingFactorial ((m : ℕ) : ℝ) (j - 1)| := by
      have h_step1 : |fallingFactorial ((m : ℕ) : ℝ) j +
              (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)|
            ≤ |fallingFactorial ((m : ℕ) : ℝ) j| +
              |(j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| := by
        simpa [Real.norm_eq_abs] using
          norm_add_le (fallingFactorial ((m : ℕ) : ℝ) j)
            ((j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1))
      have h_step2 : |(j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)|
            = (j : ℝ) * |fallingFactorial ((m : ℕ) : ℝ) (j - 1)| := by
        rw [abs_mul]
        congr 1
        exact abs_of_nonneg (Nat.cast_nonneg j)
      linarith
    have h_abs_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    have hs_pow_nn : 0 ≤ s ^ m := pow_nonneg hs_nn _
    have h_acc_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
      mul_nonneg h_abs_nn hs_pow_nn
    calc |fallingFactorial ((m : ℕ) : ℝ) j +
            (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
          |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
        = |fallingFactorial ((m : ℕ) : ℝ) j +
            (j : ℝ) * fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
            (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring
      _ ≤ (|fallingFactorial ((m : ℕ) : ℝ) j| +
            (j : ℝ) * |fallingFactorial ((m : ℕ) : ℝ) (j - 1)|) *
            (|frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
          mul_le_mul_of_nonneg_right h_tri h_acc_nn
      _ = |fallingFactorial ((m : ℕ) : ℝ) j| *
            |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m
          + (j : ℝ) * (|fallingFactorial ((m : ℕ) : ℝ) (j - 1)| *
            |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by ring

/-- **First-derivative shift summability — general.** Companion of
`frobeniusCoeff_succ_abs_mul_pow_summable` with `hpn` removed and
threshold hypothesis added; constant `K` doubled. -/
theorem frobeniusCoeff_succ_abs_mul_pow_summable_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k => ((k + 1 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (le_of_lt hR_pos)) (pow_nonneg hs_nn _)
  have h_choose : Summable (fun k : ℕ => ((k + 1).choose 1 : ℝ) * r ^ k) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 1 hr_norm).summable
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_bound :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_both :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) * r ^ k) := by
      have := h_choose.add (h_geom.mul_left (M₀ : ℝ))
      convert this using 1
      funext k
      push_cast
      simp [Nat.choose_one_right]
      ring
    exact h_sum_both.mul_left C
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_bound
  · intro k
    refine mul_nonneg (mul_nonneg ?_ (abs_nonneg _)) (pow_nonneg hs_nn _)
    positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 1 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric_general
        ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
        B hB_nn hB (k + M₀ + 1) hidx
    have hsub : k + M₀ + 1 - M₀ = k + 1 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hkM0_1_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 1)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 1)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hkM0_1_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 1)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_succ]
      ring
    exact step1.trans_eq step2

/-- **Second-derivative shift summability — general.** Companion of
`frobeniusCoeff_succ_succ_abs_mul_pow_summable`. -/
theorem frobeniusCoeff_succ_succ_abs_mul_pow_summable_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 2)| * s ^ k) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) ^ 2 * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _))
      (pow_nonneg hs_nn _)
  have h_desc2 : Summable (fun k : ℕ => ((k + 2).descFactorial 2 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 2 hr_norm
  have h_desc1 : Summable (fun k : ℕ => ((k + 1).descFactorial 1 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 1 hr_norm
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_combo :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) *
                                   ((k + M₀ + 2 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_all :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) *
                                ((k + M₀ + 2 : ℕ) : ℝ) * r ^ k) := by
      have h1 := h_desc2
      have h2 := h_desc1.mul_left (2 * M₀ : ℝ)
      have h3 := h_geom.mul_left ((M₀ : ℝ)^2 + M₀)
      have hcomb := (h1.add h2).add h3
      convert hcomb using 1
      funext k
      have hdesc2_nat : (k + 2).descFactorial 2 = (k + 1) * (k + 2) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial]
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h0 : k + 2 - 0 = k + 2 := by omega
        rw [h1, h0]
        ring
      have hdesc2 : ((k + 2).descFactorial 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
        rw [hdesc2_nat]; push_cast; ring
      have hdesc1_nat : (k + 1).descFactorial 1 = k + 1 := by
        rw [Nat.descFactorial, Nat.descFactorial]
        have h0 : k + 1 - 0 = k + 1 := by omega
        rw [h0]
        ring
      have hdesc1 : ((k + 1).descFactorial 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by
        rw [hdesc1_nat]
      rw [hdesc2, hdesc1]
      push_cast
      ring
    exact h_sum_all.mul_left C
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_combo
  · intro k
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) (abs_nonneg _)) (pow_nonneg hs_nn _)
    · positivity
    · positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 2 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric_general
        ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
        B hB_nn hB (k + M₀ + 2) hidx
    have hsub : k + M₀ + 2 - M₀ = k + 2 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hfac_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) := by
      refine mul_nonneg ?_ ?_ <;> exact Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 2)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 2)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hfac_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 2)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_add]
      ring
    exact step1.trans_eq step2

/-- **Third-derivative shift summability — general.** Companion of
`frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable`. -/
theorem frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                ((k + 3 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 3)| * s ^ k) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) ^ 3 * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _))
      (pow_nonneg hs_nn _)
  have h_desc3 : Summable (fun k : ℕ => ((k + 3).descFactorial 3 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 3 hr_norm
  have h_desc2 : Summable (fun k : ℕ => ((k + 2).descFactorial 2 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 2 hr_norm
  have h_desc1 : Summable (fun k : ℕ => ((k + 1).descFactorial 1 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 1 hr_norm
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_combo :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) *
                                   ((k + M₀ + 2 : ℕ) : ℝ) *
                                   ((k + M₀ + 3 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_all :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) *
                                ((k + M₀ + 2 : ℕ) : ℝ) *
                                ((k + M₀ + 3 : ℕ) : ℝ) * r ^ k) := by
      have h1 := h_desc3
      have h2 := h_desc2.mul_left (3 * M₀ : ℝ)
      have h3 := h_desc1.mul_left (3 * (M₀ : ℝ) * ((M₀ : ℝ) + 1))
      have h4 := h_geom.mul_left ((M₀ : ℝ) * ((M₀ : ℝ) + 1) * ((M₀ : ℝ) + 2))
      have hcomb := ((h1.add h2).add h3).add h4
      convert hcomb using 1
      funext k
      have hdesc3_nat : (k + 3).descFactorial 3 = (k + 1) * (k + 2) * (k + 3) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
            Nat.descFactorial]
        have h2 : k + 3 - 2 = k + 1 := by omega
        have h1 : k + 3 - 1 = k + 2 := by omega
        have h0 : k + 3 - 0 = k + 3 := by omega
        rw [h2, h1, h0]
        ring
      have hdesc3 : ((k + 3).descFactorial 3 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
        rw [hdesc3_nat]; push_cast; ring
      have hdesc2_nat : (k + 2).descFactorial 2 = (k + 1) * (k + 2) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial]
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h0 : k + 2 - 0 = k + 2 := by omega
        rw [h1, h0]
        ring
      have hdesc2 : ((k + 2).descFactorial 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
        rw [hdesc2_nat]; push_cast; ring
      have hdesc1_nat : (k + 1).descFactorial 1 = k + 1 := by
        rw [Nat.descFactorial, Nat.descFactorial]
        have h0 : k + 1 - 0 = k + 1 := by omega
        rw [h0]
        ring
      have hdesc1 : ((k + 1).descFactorial 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by
        rw [hdesc1_nat]
      rw [hdesc3, hdesc2, hdesc1]
      push_cast
      ring
    exact h_sum_all.mul_left C
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_combo
  · intro k
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_)
      (abs_nonneg _)) (pow_nonneg hs_nn _)
    · positivity
    · positivity
    · positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 3 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric_general
        ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
        B hB_nn hB (k + M₀ + 3) hidx
    have hsub : k + M₀ + 3 - M₀ = k + 3 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hfac_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
        ((k + M₀ + 3 : ℕ) : ℝ) := by
      refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> exact Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 3)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 3)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hfac_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 3)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
             ((k + M₀ + 3 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_add]
      ring
    exact step1.trans_eq step2

/-- **Fourth-derivative shift summability — general.** Companion of
`frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable`. -/
theorem frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
                ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) *
                |frobeniusCoeff ps n z₁ ρ c₀ (k + 4)| * s ^ k) := by
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hB_nn) ?_ <;> positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  set r : ℝ := s * (1 + K) with hr_def
  have hr_nn : 0 ≤ r := mul_nonneg hs_nn (le_of_lt hR_pos)
  have hr_lt_1 : r < 1 := hs_lt
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt_1
  set Smaj : ℝ := ∑ i ∈ Finset.range (M₀ + 1),
    |frobeniusCoeff ps n z₁ ρ c₀ i| with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set C : ℝ := Smaj * (1 + K) ^ 4 * s ^ M₀ with hC_def
  have hC_nn : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hSmaj_nn (pow_nonneg (le_of_lt hR_pos) _))
      (pow_nonneg hs_nn _)
  have h_desc4 : Summable (fun k : ℕ => ((k + 4).descFactorial 4 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 4 hr_norm
  have h_desc3 : Summable (fun k : ℕ => ((k + 3).descFactorial 3 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 3 hr_norm
  have h_desc2 : Summable (fun k : ℕ => ((k + 2).descFactorial 2 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 2 hr_norm
  have h_desc1 : Summable (fun k : ℕ => ((k + 1).descFactorial 1 : ℝ) * r ^ k) :=
    summable_descFactorial_mul_geometric_of_norm_lt_one 1 hr_norm
  have h_geom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr_nn hr_lt_1
  have h_combo :
      Summable (fun k : ℕ => C * (((k + M₀ + 1 : ℕ) : ℝ) *
                                   ((k + M₀ + 2 : ℕ) : ℝ) *
                                   ((k + M₀ + 3 : ℕ) : ℝ) *
                                   ((k + M₀ + 4 : ℕ) : ℝ) * r ^ k)) := by
    have h_sum_all :
        Summable (fun k : ℕ => ((k + M₀ + 1 : ℕ) : ℝ) *
                                ((k + M₀ + 2 : ℕ) : ℝ) *
                                ((k + M₀ + 3 : ℕ) : ℝ) *
                                ((k + M₀ + 4 : ℕ) : ℝ) * r ^ k) := by
      have h1 := h_desc4
      have h2 := h_desc3.mul_left (4 * M₀ : ℝ)
      have h3 := h_desc2.mul_left (6 * (M₀ : ℝ) * ((M₀ : ℝ) + 1))
      have h4 := h_desc1.mul_left (4 * (M₀ : ℝ) * ((M₀ : ℝ) + 1) * ((M₀ : ℝ) + 2))
      have h5 := h_geom.mul_left ((M₀ : ℝ) * ((M₀ : ℝ) + 1) *
                                  ((M₀ : ℝ) + 2) * ((M₀ : ℝ) + 3))
      have hcomb := ((((h1.add h2).add h3).add h4).add h5)
      convert hcomb using 1
      funext k
      have hdesc4_nat :
          (k + 4).descFactorial 4 = (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
            Nat.descFactorial, Nat.descFactorial]
        have h3 : k + 4 - 3 = k + 1 := by omega
        have h2 : k + 4 - 2 = k + 2 := by omega
        have h1 : k + 4 - 1 = k + 3 := by omega
        have h0 : k + 4 - 0 = k + 4 := by omega
        rw [h3, h2, h1, h0]
        ring
      have hdesc4 : ((k + 4).descFactorial 4 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) := by
        rw [hdesc4_nat]; push_cast; ring
      have hdesc3_nat :
          (k + 3).descFactorial 3 = (k + 1) * (k + 2) * (k + 3) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial,
            Nat.descFactorial]
        have h2 : k + 3 - 2 = k + 1 := by omega
        have h1 : k + 3 - 1 = k + 2 := by omega
        have h0 : k + 3 - 0 = k + 3 := by omega
        rw [h2, h1, h0]
        ring
      have hdesc3 : ((k + 3).descFactorial 3 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
        rw [hdesc3_nat]; push_cast; ring
      have hdesc2_nat : (k + 2).descFactorial 2 = (k + 1) * (k + 2) := by
        rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial]
        have h1 : k + 2 - 1 = k + 1 := by omega
        have h0 : k + 2 - 0 = k + 2 := by omega
        rw [h1, h0]
        ring
      have hdesc2 : ((k + 2).descFactorial 2 : ℝ) =
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
        rw [hdesc2_nat]; push_cast; ring
      have hdesc1_nat : (k + 1).descFactorial 1 = k + 1 := by
        rw [Nat.descFactorial, Nat.descFactorial]
        have h0 : k + 1 - 0 = k + 1 := by omega
        rw [h0]
        ring
      have hdesc1 : ((k + 1).descFactorial 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by
        rw [hdesc1_nat]
      rw [hdesc4, hdesc3, hdesc2, hdesc1]
      push_cast
      ring
    exact h_sum_all.mul_left C
  rw [← summable_nat_add_iff M₀]
  refine Summable.of_nonneg_of_le ?_ ?_ h_combo
  · intro k
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_)
      ?_) (abs_nonneg _)) (pow_nonneg hs_nn _)
    · positivity
    · positivity
    · positivity
    · positivity
  · intro k
    have hidx : M₀ ≤ k + M₀ + 4 := by omega
    have hpt :=
      abs_frobeniusCoeff_pointwise_geometric_general
        ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
        B hB_nn hB (k + M₀ + 4) hidx
    have hsub : k + M₀ + 4 - M₀ = k + 4 := by omega
    rw [hsub] at hpt
    have hs_pow_nn : 0 ≤ s ^ (k + M₀) := pow_nonneg hs_nn _
    have hfac_nn : (0 : ℝ) ≤ ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
        ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_ <;>
        exact Nat.cast_nonneg _
    have step1 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + M₀ + 4)| * s ^ (k + M₀) ≤
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 4)) * s ^ (k + M₀) := by
      have := mul_le_mul_of_nonneg_left hpt hfac_nn
      exact mul_le_mul_of_nonneg_right this hs_pow_nn
    have step2 :
        ((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
          ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) *
          (Smaj * (1 + K) ^ (k + 4)) * s ^ (k + M₀) =
        C * (((k + M₀ + 1 : ℕ) : ℝ) * ((k + M₀ + 2 : ℕ) : ℝ) *
             ((k + M₀ + 3 : ℕ) : ℝ) * ((k + M₀ + 4 : ℕ) : ℝ) * r ^ k) := by
      rw [hC_def, hr_def, mul_pow, pow_add, pow_add]
      ring
    exact step1.trans_eq step2

/-- **Continuity of `frobeniusValueDeriv` — general.** Companion of
`frobeniusValueDeriv_continuousOn`. -/
theorem frobeniusValueDeriv_continuousOn_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValueDeriv ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValueDeriv
  have hsum :
      Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m) :=
    frobeniusCoeff_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => ((m + 1 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m)
    (u := fun m => ((m + 1 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hmnn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
    calc ‖((m + 1 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m‖
        = ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hmnn]
      _ ≤ ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hmnn hcoeff_nn)

/-- **Continuity of `frobeniusValueDeriv2` — general.** Companion of
`frobeniusValueDeriv2_continuousOn`. -/
theorem frobeniusValueDeriv2_continuousOn_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValueDeriv2 ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValueDeriv2
  have hsum :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (k + 2)| * s ^ k) :=
    frobeniusCoeff_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * t ^ m)
    (u := fun m => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hprod_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| := abs_nonneg _
    calc ‖((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * t ^ m‖
        = ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg (Nat.cast_nonneg (m + 1 : ℕ)),
              abs_of_nonneg (Nat.cast_nonneg (m + 2 : ℕ))]
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hprod_nn hcoeff_nn)

/-- **Continuity of `frobeniusValueDeriv3` — general.** Companion of
`frobeniusValueDeriv3_continuousOn`. -/
theorem frobeniusValueDeriv3_continuousOn_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValueDeriv3 ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValueDeriv3
  have hsum :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
        ((k + 3 : ℕ) : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ (k + 3)| * s ^ k) :=
    frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * t ^ m)
    (u := fun m => ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hprod_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        ((m + 3 : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| := abs_nonneg _
    calc ‖((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * t ^ m‖
        = ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg (Nat.cast_nonneg (m + 1 : ℕ)),
              abs_of_nonneg (Nat.cast_nonneg (m + 2 : ℕ)),
              abs_of_nonneg (Nat.cast_nonneg (m + 3 : ℕ))]
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hprod_nn hcoeff_nn)

/-- **Euler-operator identity at `k = 1` — general.** Companion of
`frobeniusValueDeriv_tsum_euler_one`. -/
theorem frobeniusValueDeriv_tsum_euler_one_general
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
    (∑' (m : ℕ), (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t * frobeniusValueDeriv ps n z₁ ρ c₀ t := by
  have hs_abs_pos_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  have hsum : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    have h_shift_abs : Summable (fun m : ℕ =>
        (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1)) := by
      rw [← summable_nat_add_iff 1]
      have hrewrite :
          (fun i => ((i + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (i + 1)| * s ^ (i + 1 - 1)) =
          fun k => ((k + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k := by
        funext k; simp
      change Summable fun i => (((i + 1 : ℕ) : ℝ) *
        |frobeniusCoeff ps n z₁ ρ c₀ (i + 1)| * s ^ (i + 1 - 1))
      rw [hrewrite]
      exact frobeniusCoeff_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
    have h_abs_sum : Summable (fun m : ℕ =>
        (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
      have := h_shift_abs.mul_right s
      convert this using 1
      funext m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · have hm1 : m = (m - 1) + 1 := by omega
        have hpow : s ^ m = s ^ (m - 1) * s := by
          conv_lhs => rw [hm1]
          rw [pow_succ]
        rw [hpow]; ring
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    calc ‖(m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hmnn]
      _ ≤ (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pos_pow m)
            (mul_nonneg hmnn (abs_nonneg _))
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  unfold frobeniusValueDeriv
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **Euler-operator identity at `k = 2` — general.** Companion of
`frobeniusValueDeriv_tsum_euler_two`. -/
theorem frobeniusValueDeriv_tsum_euler_two_general
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
    (∑' (m : ℕ), fallingFactorial (m : ℝ) 2 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 2 * frobeniusValueDeriv2 ps n z₁ ρ c₀ t := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  have h_shift_abs :=
    frobeniusCoeff_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  have h_shift_s2 := h_shift_abs.mul_right (s ^ 2)
  have h_abs_sum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    rw [← summable_nat_add_iff 2]
    convert h_shift_s2 using 1
    funext k
    have hff : fallingFactorial ((k + 2 : ℕ) : ℝ) 2 =
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
      rw [fallingFactorial_two]; push_cast; ring
    have hpow : s ^ (k + 2) = s ^ k * s ^ 2 := by rw [pow_add]
    rw [hff, hpow]; ring
  have hsum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hff_nn : 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 2 := by
      rw [fallingFactorial_two]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        have hfac : 0 ≤ (m : ℝ) - 1 := by linarith
        exact mul_nonneg hm_nn hfac
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 2 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hff_nn]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg hff_nn (abs_nonneg _))
  rw [← hsum.sum_add_tsum_nat_add 2]
  have h0 : fallingFactorial ((0 : ℕ) : ℝ) 2 *
      frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = 0 := by
    rw [fallingFactorial_two]; push_cast; ring
  have h1 : fallingFactorial ((1 : ℕ) : ℝ) 2 *
      frobeniusCoeff ps n z₁ ρ c₀ 1 * t ^ 1 = 0 := by
    rw [fallingFactorial_two]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1,
    add_zero]
  unfold frobeniusValueDeriv2
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hff : fallingFactorial ((k + 2 : ℕ) : ℝ) 2 =
      ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    rw [fallingFactorial_two]; push_cast; ring
  rw [hff]
  have hpow : t ^ (k + 2) = t ^ 2 * t ^ k := by
    rw [pow_add]; ring
  rw [hpow]; ring

/-- **Euler-operator identity at `k = 3` — general.** Companion of
`frobeniusValueDeriv_tsum_euler_three`. -/
theorem frobeniusValueDeriv_tsum_euler_three_general
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
    (∑' (m : ℕ), fallingFactorial (m : ℝ) 3 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 3 * frobeniusValueDeriv3 ps n z₁ ρ c₀ t := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  have h_shift_abs :=
    frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  have h_shift_s3 := h_shift_abs.mul_right (s ^ 3)
  have h_abs_sum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 3 *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    rw [← summable_nat_add_iff 3]
    convert h_shift_s3 using 1
    funext k
    have hff : fallingFactorial ((k + 3 : ℕ) : ℝ) 3 =
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
      rw [fallingFactorial_three]; push_cast; ring
    have hpow : s ^ (k + 3) = s ^ k * s ^ 3 := by rw [pow_add]
    rw [hff, hpow]; ring
  have hsum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 3 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hff_nn : 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 3 := by
      rw [fallingFactorial_three]
      rcases Nat.lt_or_ge m 3 with hm | hm
      · have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> norm_num
      · have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by linarith
        have hf1 : 0 ≤ (m : ℝ) - 1 := by linarith
        have hf2 : 0 ≤ (m : ℝ) - 2 := by linarith
        exact mul_nonneg (mul_nonneg hm_nn hf1) hf2
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 3 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 3 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hff_nn]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 3 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg hff_nn (abs_nonneg _))
  rw [← hsum.sum_add_tsum_nat_add 3]
  have h0 : fallingFactorial ((0 : ℕ) : ℝ) 3 *
      frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = 0 := by
    rw [fallingFactorial_three]; push_cast; ring
  have h1 : fallingFactorial ((1 : ℕ) : ℝ) 3 *
      frobeniusCoeff ps n z₁ ρ c₀ 1 * t ^ 1 = 0 := by
    rw [fallingFactorial_three]; push_cast; ring
  have h2 : fallingFactorial ((2 : ℕ) : ℝ) 3 *
      frobeniusCoeff ps n z₁ ρ c₀ 2 * t ^ 2 = 0 := by
    rw [fallingFactorial_three]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h1, h2, add_zero]
  unfold frobeniusValueDeriv3
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hff : fallingFactorial ((k + 3 : ℕ) : ℝ) 3 =
      ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) := by
    rw [fallingFactorial_three]; push_cast; ring
  rw [hff]
  have hpow : t ^ (k + 3) = t ^ 3 * t ^ k := by
    rw [pow_add]; ring
  rw [hpow]; ring

/-- **V → V' HasDerivAt — general.** Companion of
`frobeniusValue_hasDerivAt_std`, threading the threshold-form
hypothesis instead of `(ps n).eval z₁ = 0`. -/
theorem frobeniusValue_hasDerivAt_std_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValue ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    frobeniusCoeff ps n z₁ ρ c₀ m * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
        ((k + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 1)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      simp only [hsub]
    rw [hrewrite]
    exact frobeniusCoeff_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul := hpow.const_mul (frobeniusCoeff ps n z₁ ρ c₀ m)
    have heq : frobeniusCoeff ps n z₁ ρ c₀ m * ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    have hprefix_nn : 0 ≤ (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| :=
      mul_nonneg hm_nn hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg hm_nn]
      _ ≤ (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValue ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValue; rfl
  rw [hfun_eq] at h
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    have hprefix_nn : 0 ≤ (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| :=
      mul_nonneg hm_nn hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
          abs_of_nonneg hm_nn]
    have hu_eq : u m =
        (m : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv
    rw [hsum_signed.tsum_eq_zero_add]
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    refine tsum_congr (fun k => ?_)
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (k + 1) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    simp only [hkk]
  rw [hshift] at h
  exact h

/-- **First-order HasDerivAt — general.** Companion of
`frobeniusValueDeriv_hasDerivAt`. (`frobeniusValue` differentiates to
`frobeniusValueDeriv` was the original; here we lift the
`frobeniusValueDeriv → frobeniusValueDeriv2` step structurally identical
to the original `frobeniusValueDeriv_hasDerivAt`.) -/
theorem frobeniusValueDeriv_hasDerivAt_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValueDeriv ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv2 ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    ((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * (((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1)) *
      y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * ((m + 1 : ℕ) : ℝ) * |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| *
      s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 2)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      have hplus : (k + 1 + 1 : ℕ) = k + 2 := by omega
      simp only [hsub, hplus]
    rw [hrewrite]
    exact frobeniusCoeff_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :=
      hpow.const_mul (((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1))
    have heq : ((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1) *
        ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * (((m + 1 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 1)) *
          y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| :=
      mul_nonneg (mul_nonneg hm_nn hm1_nn) hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
              abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn]
          ring
      _ ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValueDeriv ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValueDeriv; rfl
  rw [hfun_eq] at h
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| :=
      mul_nonneg (mul_nonneg hm_nn hm1_nn) hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow,
          abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn]
      ring
    have hu_eq : u m = (m : ℝ) * ((m + 1 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 1)| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv2 ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv2
    rw [hsum_signed.tsum_eq_zero_add]
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    congr 1
    funext k
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (k + 2) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    have he1 : (k + 1 + 1 : ℕ) = k + 2 := by omega
    simp only [hkk, he1]
    push_cast
    ring
  rw [hshift] at h
  exact h

/-- **Second-order HasDerivAt — general.** Companion of
`frobeniusValueDeriv2_hasDerivAt`. -/
theorem frobeniusValueDeriv2_hasDerivAt_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValueDeriv2 ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv3 ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 2) * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 2)) * y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 3)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      have hplus : (k + 1 + 2 : ℕ) = k + 3 := by omega
      simp only [hsub, hplus]
    rw [hrewrite]
    exact frobeniusCoeff_succ_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :=
      hpow.const_mul (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (m + 2))
    have heq : ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (m + 2) *
        ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          frobeniusCoeff ps n z₁ ρ c₀ (m + 2)) * y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| :=
      mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn) hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
              abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
              abs_of_nonneg hm2_nn]
          ring
      _ ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValueDeriv2 ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValueDeriv2; rfl
  rw [hfun_eq] at h
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| :=
      mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn) hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
          abs_of_nonneg hm2_nn]
      ring
    have hu_eq : u m = (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 2)| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv3 ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv3
    rw [hsum_signed.tsum_eq_zero_add]
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    congr 1
    funext k
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
      ((k + 3 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (k + 3) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    have he1 : (k + 1 + 2 : ℕ) = k + 3 := by omega
    simp only [hkk, he1]
    push_cast
    ring
  rw [hshift] at h
  exact h

/-- **Third-order HasDerivAt — general.** Companion of
`frobeniusValueDeriv3_hasDerivAt`. -/
theorem frobeniusValueDeriv3_hasDerivAt_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun y => frobeniusValueDeriv3 ps n z₁ ρ c₀ y)
      (frobeniusValueDeriv4 ps n z₁ ρ c₀ t) t := by
  set g : ℕ → ℝ → ℝ := fun m y =>
    ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 3) * y ^ m with hg_def
  set g' : ℕ → ℝ → ℝ := fun m y =>
    (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (m + 3)) * y ^ (m - 1) with hg'_def
  set u : ℕ → ℝ := fun m =>
    (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
      |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ (m - 1) with hu_def
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  have hu_summable : Summable u := by
    rw [← summable_nat_add_iff 1 (f := u)]
    have hrewrite : (fun i => u (i + 1)) = fun k =>
          ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (k + 4)| * s ^ k := by
      funext k
      rw [hu_def]
      have hsub : (k + 1 - 1 : ℕ) = k := by omega
      have hplus : (k + 1 + 3 : ℕ) = k + 4 := by omega
      simp only [hsub, hplus]
    rw [hrewrite]
    exact frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable_general
      ps n z₁ ρ c₀ M₀ hpk hslope hM0_small hM0_large h_thresh_general
      B hB_nn hB s hs_nn hs_lt
  have hg : ∀ m (y : ℝ), HasDerivAt (g m) (g' m y) y := by
    intro m y
    have hpow : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * y ^ (m - 1)) y :=
      hasDerivAt_pow m y
    have hmul :=
      hpow.const_mul (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        ((m + 3 : ℕ) : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ (m + 3))
    have heq : ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
        frobeniusCoeff ps n z₁ ρ c₀ (m + 3) *
        ((m : ℝ) * y ^ (m - 1)) =
        (m : ℝ) * (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
          frobeniusCoeff ps n z₁ ρ c₀ (m + 3)) * y ^ (m - 1) := by ring
    rw [heq] at hmul
    exact hmul
  have hg'_bound : ∀ m (y : ℝ), y ∈ Metric.ball (0 : ℝ) s → ‖g' m y‖ ≤ u m := by
    intro m y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hy_abs : |y| ≤ s := le_of_lt hy
    have hy_pow_le : |y| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hy_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm3_nn : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              ((m + 3 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn)
        hm3_nn) hcoeff_nn
    calc ‖g' m y‖
        = (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * |y| ^ (m - 1) := by
          rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
              abs_mul, abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
              abs_of_nonneg hm2_nn, abs_of_nonneg hm3_nn]
          ring
      _ ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
            |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
      _ = u m := by rw [hu_def]
  have hg0 : Summable (fun m => g m 0) := by
    apply (summable_nat_add_iff 1).mp
    have : (fun m => g (m + 1) 0) = fun _ => (0 : ℝ) := by
      funext m; simp [hg_def, zero_pow (Nat.succ_ne_zero m)]
    rw [this]; exact summable_zero
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    hu_summable Metric.isOpen_ball (convex_ball (0 : ℝ) s).isPreconnected
    (fun m y _ => hg m y) (fun m y hy => hg'_bound m y hy)
    h0_mem hg0 ht_mem
  have hfun_eq : (fun z => ∑' m, g m z) =
      fun y => frobeniusValueDeriv3 ps n z₁ ρ c₀ y := by
    funext y; unfold frobeniusValueDeriv3; rfl
  rw [hfun_eq] at h
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hsum_signed : Summable fun m => g' m t := by
    apply Summable.of_norm
    refine hu_summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hy_pow_le : |t| ^ (m - 1) ≤ s ^ (m - 1) :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hm1_nn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm2_nn : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hm3_nn : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| := abs_nonneg _
    have hprefix_nn :
        0 ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
              ((m + 3 : ℕ) : ℝ) *
              |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm_nn hm1_nn) hm2_nn)
        hm3_nn) hcoeff_nn
    have hnorm_eq : ‖g' m t‖ =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * |t| ^ (m - 1) := by
      rw [hg'_def, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
          abs_mul, abs_pow, abs_of_nonneg hm_nn, abs_of_nonneg hm1_nn,
          abs_of_nonneg hm2_nn, abs_of_nonneg hm3_nn]
      ring
    have hu_eq : u m =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ) *
          |frobeniusCoeff ps n z₁ ρ c₀ (m + 3)| * s ^ (m - 1) := by
      rw [hu_def]
    rw [hnorm_eq, hu_eq]
    exact mul_le_mul_of_nonneg_left hy_pow_le hprefix_nn
  have hshift :
      (∑' m, g' m t) = frobeniusValueDeriv4 ps n z₁ ρ c₀ t := by
    unfold frobeniusValueDeriv4
    rw [hsum_signed.tsum_eq_zero_add]
    have h0 : g' 0 t = 0 := by simp [hg'_def]
    rw [h0, zero_add]
    congr 1
    funext k
    show g' (k + 1) t = ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
      ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) *
      frobeniusCoeff ps n z₁ ρ c₀ (k + 4) * t ^ k
    rw [hg'_def]
    have hkk : (k + 1 - 1 : ℕ) = k := by omega
    have he1 : (k + 1 + 3 : ℕ) = k + 4 := by omega
    simp only [hkk, he1]
    push_cast
    ring
  rw [hshift] at h
  exact h

/-- **Euler-operator identity at `k = 4` — general.** Companion of
`frobeniusValueDeriv_tsum_euler_four`. -/
theorem frobeniusValueDeriv_tsum_euler_four_general
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
    (∑' (m : ℕ), fallingFactorial (m : ℝ) 4 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 4 * frobeniusValueDeriv4 ps n z₁ ρ c₀ t := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  have hff4 : ∀ x : ℝ, fallingFactorial x 4 =
      x * (x - 1) * (x - 2) * (x - 3) := by
    intro x; rw [show (4 : ℕ) = 3 + 1 from rfl, fallingFactorial_succ,
      fallingFactorial_three]; push_cast; ring
  have h_shift_abs :=
    frobeniusCoeff_succ_succ_succ_succ_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  have h_shift_s4 := h_shift_abs.mul_right (s ^ 4)
  have h_abs_sum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 4 *
        |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    rw [← summable_nat_add_iff 4]
    convert h_shift_s4 using 1
    funext k
    have hff : fallingFactorial ((k + 4 : ℕ) : ℝ) 4 =
        ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
          ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) := by
      rw [hff4]; push_cast; ring
    have hpow : s ^ (k + 4) = s ^ k * s ^ 4 := by rw [pow_add]
    rw [hff, hpow]; ring
  have hsum : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 4 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs_sum.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    have hff_nn : 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 4 := by
      rw [hff4]
      rcases Nat.lt_or_ge m 4 with hm | hm
      · have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> norm_num
      · have h4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by linarith
        have hf1 : 0 ≤ (m : ℝ) - 1 := by linarith
        have hf2 : 0 ≤ (m : ℝ) - 2 := by linarith
        have hf3 : 0 ≤ (m : ℝ) - 3 := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hm_nn hf1) hf2) hf3
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 4 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 4 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hff_nn]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 4 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg hff_nn (abs_nonneg _))
  rw [← hsum.sum_add_tsum_nat_add 4]
  have h0 : fallingFactorial ((0 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = 0 := by
    rw [hff4]; push_cast; ring
  have h1 : fallingFactorial ((1 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 1 * t ^ 1 = 0 := by
    rw [hff4]; push_cast; ring
  have h2 : fallingFactorial ((2 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 2 * t ^ 2 = 0 := by
    rw [hff4]; push_cast; ring
  have h3 : fallingFactorial ((3 : ℕ) : ℝ) 4 *
      frobeniusCoeff ps n z₁ ρ c₀ 3 * t ^ 3 = 0 := by
    rw [hff4]; push_cast; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h1, h2, h3, add_zero]
  unfold frobeniusValueDeriv4
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hff : fallingFactorial ((k + 4 : ℕ) : ℝ) 4 =
      ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) *
        ((k + 3 : ℕ) : ℝ) * ((k + 4 : ℕ) : ℝ) := by
    rw [hff4]; push_cast; ring
  rw [hff]
  have hpow : t ^ (k + 4) = t ^ 4 * t ^ k := by
    rw [pow_add]; ring
  rw [hpow]; ring

/-- **Shift-one Euler identity at `j = 2` — general.** At the ρ=1
branch, the weight on `a_m` is `fallingFactorial (1+m) 2 = (1+m)·m`.
Using `fallingFactorial (1+m) 2 = m(m-1) + 2m` and splitting into
`euler_two_general` + `euler_one_general`, the tsum becomes
`t²·V''(t) + 2t·V'(t)`. -/
theorem frobeniusValueDeriv_tsum_euler_shift_one_two_general
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
    (∑' (m : ℕ), fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 2 * frobeniusValueDeriv2 ps n z₁ ρ c₀ t +
        2 * (t * frobeniusValueDeriv ps n z₁ ρ c₀ t) := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  -- Summability of fallingFactorial m 2 * a_m * t^m (non-abs).
  have h_abs2 := frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
    ps n z₁ ρ c₀ M₀ 2 hpk hslope hM0_small hM0_large h_thresh_general
    B hB_nn hB s hs_nn hs_lt
  have hff2_nn : ∀ m : ℕ, 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 2 := by
    intro m; rw [fallingFactorial_two]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg hm_nn (by linarith)
  have hsum2 : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs2.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 2 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hff2_nn m)]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg (hff2_nn m) (abs_nonneg _))
      _ = |fallingFactorial ((m : ℕ) : ℝ) 2| *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by
          rw [abs_of_nonneg (hff2_nn m)]
  -- Summability of m * a_m * t^m (non-abs).
  have h_abs1 := frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
    ps n z₁ ρ c₀ M₀ 1 hpk hslope hM0_small hM0_large h_thresh_general
    B hB_nn hB s hs_nn hs_lt
  have h_abs1' : Summable (fun m : ℕ =>
      |(m : ℝ)| * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) := by
    convert h_abs1 using 1
    funext m
    rw [fallingFactorial_one]
  have hsum1 : Summable (fun m : ℕ =>
      (m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs1'.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    calc ‖(m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = |(m : ℝ)| * |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
      _ ≤ |(m : ℝ)| * |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  -- Pointwise identity.
  have hpt : ∀ m : ℕ,
      fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m =
        fallingFactorial (m : ℝ) 2 *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m
        + 2 * ((m : ℝ) * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    intro m
    have hff : fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 =
        fallingFactorial ((m : ℕ) : ℝ) 2 +
          (2 : ℝ) * fallingFactorial ((m : ℕ) : ℝ) 1 := by
      have := fallingFactorial_add_one ((m : ℕ) : ℝ) 2
      rw [add_comm ((m : ℕ) : ℝ) 1] at this
      simpa using this
    rw [hff, fallingFactorial_one]; ring
  rw [tsum_congr hpt]
  rw [(hsum2.tsum_add (hsum1.mul_left 2))]
  rw [tsum_mul_left]
  rw [frobeniusValueDeriv_tsum_euler_two_general ps n z₁ ρ c₀ M₀
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs]
  rw [frobeniusValueDeriv_tsum_euler_one_general ps n z₁ ρ c₀ M₀
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs]

/-- **Shift-one Euler identity at `j = 3` — general.** At the ρ=1
branch, `fallingFactorial (1+m) 3 = (1+m)·m·(m-1) = m(m-1)(m-2) + 3m(m-1)`,
so the tsum becomes `t³·V'''(t) + 3t²·V''(t)`. -/
theorem frobeniusValueDeriv_tsum_euler_shift_one_three_general
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
    (∑' (m : ℕ), fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
        frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) =
      t ^ 3 * frobeniusValueDeriv3 ps n z₁ ρ c₀ t +
        3 * (t ^ 2 * frobeniusValueDeriv2 ps n z₁ ρ c₀ t) := by
  have hs_abs_pow : ∀ m, |t ^ m| ≤ s ^ m := fun m => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht_abs _
  -- Summability of fallingFactorial m 3 * a_m * t^m.
  have h_abs3 := frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
    ps n z₁ ρ c₀ M₀ 3 hpk hslope hM0_small hM0_large h_thresh_general
    B hB_nn hB s hs_nn hs_lt
  have hff3_nn : ∀ m : ℕ, 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 3 := by
    intro m; rw [fallingFactorial_three]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hcases with rfl | rfl | rfl <;> norm_num
    · have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by linarith
      have hf1 : 0 ≤ (m : ℝ) - 1 := by linarith
      have hf2 : 0 ≤ (m : ℝ) - 2 := by linarith
      exact mul_nonneg (mul_nonneg hm_nn hf1) hf2
  have hsum3 : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 3 * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs3.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 3 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 3 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hff3_nn m)]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 3 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg (hff3_nn m) (abs_nonneg _))
      _ = |fallingFactorial ((m : ℕ) : ℝ) 3| *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by
          rw [abs_of_nonneg (hff3_nn m)]
  -- Summability of fallingFactorial m 2 * a_m * t^m.
  have h_abs2 := frobeniusCoeff_fallingFactorial_abs_mul_pow_summable_general
    ps n z₁ ρ c₀ M₀ 2 hpk hslope hM0_small hM0_large h_thresh_general
    B hB_nn hB s hs_nn hs_lt
  have hff2_nn : ∀ m : ℕ, 0 ≤ fallingFactorial ((m : ℕ) : ℝ) 2 := by
    intro m; rw [fallingFactorial_two]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg hm_nn (by linarith)
  have hsum2 : Summable (fun m : ℕ =>
      fallingFactorial (m : ℝ) 2 * frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    apply Summable.of_norm
    refine h_abs2.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    calc ‖fallingFactorial ((m : ℕ) : ℝ) 2 *
              frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * |t ^ m| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hff2_nn m)]
      _ ≤ fallingFactorial ((m : ℕ) : ℝ) 2 *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left (hs_abs_pow m)
            (mul_nonneg (hff2_nn m) (abs_nonneg _))
      _ = |fallingFactorial ((m : ℕ) : ℝ) 2| *
              |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m := by
          rw [abs_of_nonneg (hff2_nn m)]
  -- Pointwise identity.
  have hpt : ∀ m : ℕ,
      fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
          frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m =
        fallingFactorial (m : ℝ) 3 *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m
        + 3 * (fallingFactorial (m : ℝ) 2 *
            frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m) := by
    intro m
    have hff : fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 =
        fallingFactorial ((m : ℕ) : ℝ) 3 +
          (3 : ℝ) * fallingFactorial ((m : ℕ) : ℝ) 2 := by
      have := fallingFactorial_add_one ((m : ℕ) : ℝ) 3
      rw [add_comm ((m : ℕ) : ℝ) 1] at this
      simpa using this
    rw [hff]; ring
  rw [tsum_congr hpt]
  rw [(hsum3.tsum_add (hsum2.mul_left 3))]
  rw [tsum_mul_left]
  rw [frobeniusValueDeriv_tsum_euler_three_general ps n z₁ ρ c₀ M₀
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs]
  rw [frobeniusValueDeriv_tsum_euler_two_general ps n z₁ ρ c₀ M₀
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_nn hs_lt t ht_abs]

/-! ## Mathlib analytic-side migration — `_general` chain (drops `hpn=0`)

These lemmas parallel the `frobeniusCoeff_hasSum` / `_hasFPowerSeriesOnBall`
/ `_analyticOnNhd` / `_eqOn_of_eventuallyEq` chain at lines ~2245–2410, but
without the `hpn : (ps n).eval z₁ = 0` hypothesis. Replaces it with the
`h_thresh_general` Mₒ-threshold absorbing the residual `(ps n).eval z₁`
contribution. The K factor in the disk-radius condition gains an extra
factor of `2` to match `frobeniusCoeff_abs_mul_pow_summable_general`.
-/

theorem frobeniusCoeff_mul_pow_summable_general
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
    (s : ℝ)
    (hs_lt : |s| * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    Summable (fun m => frobeniusCoeff ps n z₁ ρ c₀ m * s ^ m) := by
  have habs :=
    frobeniusCoeff_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀ hpk hslope
      hM0_small hM0_large h_thresh_general B hB_nn hB |s| (abs_nonneg s) hs_lt
  apply Summable.of_norm
  convert habs using 1
  funext m
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

/-- **Shift decomposition (general).** General-threshold variant of
`frobeniusValue_eq_c0_add_t_mul_tail`. Replaces the simple-zero
hypothesis `(ps n).eval z₁ = 0` with the standard threshold condition
admitting `(ps n).eval z₁ ≠ 0` (apery's `Q(z₁) ≠ 0` case), and uses
the doubled disk constant `2·(n+2)·B·2^(n+1)`. -/
theorem frobeniusValue_eq_c0_add_t_mul_tail_general
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
    (t : ℝ)
    (ht : |t| * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    frobeniusValue ps n z₁ ρ c₀ t =
      c₀ + t * ∑' m, frobeniusCoeff ps n z₁ ρ c₀ (m + 1) * t ^ m := by
  have hsum :=
    frobeniusCoeff_mul_pow_summable_general ps n z₁ ρ c₀ M₀ hpk hslope
      hM0_small hM0_large h_thresh_general B hB_nn hB t ht
  unfold frobeniusValue
  rw [hsum.tsum_eq_zero_add]
  have h0 : frobeniusCoeff ps n z₁ ρ c₀ 0 * t ^ 0 = c₀ := by
    simp [frobeniusCoeff, frobeniusBuilder]
  rw [h0]
  congr 1
  rw [← tsum_mul_left]
  congr 1
  funext m
  ring

theorem frobeniusCoeff_hasSum_general
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
    (t : ℝ)
    (ht : |t| * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    HasSum (fun m => frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)
      (frobeniusValue ps n z₁ ρ c₀ t) :=
  (frobeniusCoeff_mul_pow_summable_general ps n z₁ ρ c₀ M₀ hpk hslope
    hM0_small hM0_large h_thresh_general B hB_nn hB t ht).hasSum

theorem frobeniusValue_hasFPowerSeriesOnBall_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    HasFPowerSeriesOnBall
      (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ
        (frobeniusCoeff ps n z₁ ρ c₀))
      (0 : ℝ) (ENNReal.ofReal s) := by
  set p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ
      (frobeniusCoeff ps n z₁ ρ c₀) with hp_def
  set K : ℝ := 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
               |(Polynomial.derivative (ps (n + 1))).eval z₁| with hK_def
  have hslope_pos : 0 < |(Polynomial.derivative (ps (n + 1))).eval z₁| :=
    abs_pos.mpr hslope
  have hK_nn : 0 ≤ K := by
    have hnum_nn : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · positivity
          · positivity
        · exact hB_nn
      · positivity
    exact div_nonneg hnum_nn (le_of_lt hslope_pos)
  have hR_pos : 0 < 1 + K := by linarith
  refine ⟨?radius, ?pos, ?sum⟩
  · have habs : Summable
        (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
      frobeniusCoeff_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
        hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB
        s hs_pos.le hs_lt
    set sN : NNReal := Real.toNNReal s with hsN_def
    have hcoe : (sN : ℝ) = s := Real.coe_toNNReal s hs_pos.le
    have hsum : Summable (fun m : ℕ => ‖p m‖ * (sN : ℝ) ^ m) := by
      rw [hcoe]
      refine habs.congr ?_
      intro m
      simp [p, Real.norm_eq_abs]
    have hrad := p.le_radius_of_summable hsum
    have heq : ENNReal.ofReal s = (sN : ENNReal) := rfl
    rw [heq]
    exact hrad
  · exact ENNReal.ofReal_pos.mpr hs_pos
  · intro y hy
    have hy_dist : dist y (0 : ℝ) < s := by
      have hmem : edist y (0 : ℝ) < ENNReal.ofReal s := hy
      exact (edist_lt_ofReal).mp hmem
    have hy_abs : |y| < s := by
      simpa [Real.dist_eq] using hy_dist
    have ht : |y| * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
        |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1 := by
      rw [← hK_def]
      have h1 : |y| * (1 + K) < s * (1 + K) :=
        mul_lt_mul_of_pos_right hy_abs hR_pos
      linarith
    have hsum := frobeniusCoeff_hasSum_general ps n z₁ ρ c₀ M₀ hpk hslope
      hM0_small hM0_large h_thresh_general B hB_nn hB y ht
    have hcongr : (fun m : ℕ => p m (fun _ : Fin m => y))
        = (fun m : ℕ => frobeniusCoeff ps n z₁ ρ c₀ m * y ^ m) := by
      funext m
      simp [p, smul_eq_mul, mul_comm]
    rw [hcongr]
    simpa [zero_add] using hsum

theorem frobeniusValue_analyticOnNhd_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    AnalyticOnNhd ℝ (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) := by
  have hball := frobeniusValue_hasFPowerSeriesOnBall_general ps n z₁ ρ c₀ M₀
    hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_pos hs_lt
  have hAnal := hball.analyticOnNhd
  rwa [Metric.eball_ofReal] at hAnal

theorem frobeniusValue_eqOn_of_eventuallyEq_general
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
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * ((n + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (n + 1)) /
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1)
    (g : ℝ → ℝ)
    (hg_anal : AnalyticOnNhd ℝ g (Metric.ball (0 : ℝ) s))
    (hfg : Filter.EventuallyEq (nhds (0 : ℝ)) g
      (fun t => frobeniusValue ps n z₁ ρ c₀ t)) :
    Set.EqOn g (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) := by
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => frobeniusValue ps n z₁ ρ c₀ t)
      (Metric.ball (0 : ℝ) s) :=
    frobeniusValue_analyticOnNhd_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_pos hs_lt
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have hConn : IsPreconnected (Metric.ball (0 : ℝ) s) :=
    (convex_ball (0 : ℝ) s).isPreconnected
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hg_anal hF hConn h0 hfg

/-- **Continuity on the Frobenius disk — general (Q(z₁) ≠ 0 admissible).**
Companion of `frobeniusValue_continuousOn` that drops `hpn : (ps n).eval z₁ = 0`
in favour of the threshold hypothesis `h_thresh_general` used by the
`_general` summability chain. The disk constant is doubled (`2·(n+2)·B·2^(n+1)`
instead of `(n+2)·B·2^(n+1)`), matching `frobeniusCoeff_abs_mul_pow_summable_general`. -/
theorem frobeniusValue_continuousOn_general
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
      |(Polynomial.derivative (ps (n + 1))).eval z₁|) < 1) :
    ContinuousOn (fun t => frobeniusValue ps n z₁ ρ c₀ t) (Set.Icc (-s) s) := by
  unfold frobeniusValue
  have hsum :
      Summable (fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m) :=
    frobeniusCoeff_abs_mul_pow_summable_general ps n z₁ ρ c₀ M₀
      hpk hslope hM0_small hM0_large h_thresh_general B hB_nn hB s hs_nn hs_lt
  refine continuousOn_tsum
    (f := fun m t => frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m)
    (u := fun m => |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m)
    ?_ hsum ?_
  · intro m
    exact (continuous_const.mul (continuous_id.pow m)).continuousOn
  · intro m t ht
    rw [Set.mem_Icc] at ht
    have ht_abs : |t| ≤ s := abs_le.mpr ht
    have hpow : |t| ^ m ≤ s ^ m :=
      pow_le_pow_left₀ (abs_nonneg _) ht_abs m
    have hcoeff_nn : 0 ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| := abs_nonneg _
    calc ‖frobeniusCoeff ps n z₁ ρ c₀ m * t ^ m‖
        = |frobeniusCoeff ps n z₁ ρ c₀ m| * |t| ^ m := by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ |frobeniusCoeff ps n z₁ ρ c₀ m| * s ^ m :=
          mul_le_mul_of_nonneg_left hpow hcoeff_nn

end Number.Frobenius
end Ripple
