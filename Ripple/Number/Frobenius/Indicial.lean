import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Frobenius framework — Step 1: formal Euler-operator substitution

This file starts the general Frobenius / regular-singular-point
infrastructure described in `STRATEGY.md`. We formalise the Euler
operator `L = t · d/dt` acting on formal power series and the shifted
operator `ρ + L` that appears when substituting the Frobenius ansatz
`y(t) = t^ρ · g(t)` into a linear ODE rewritten in Euler form:
`(Σ_j a_j(t) · L^j) y = 0`.

The main result, `coeff_zero_indicialSum`, states that the constant
coefficient of `Σ_j a_j(0) · (ρ + L)^j g` equals `P(ρ) · g(0)`, where
`P(ρ) = Σ_j a_j(0) · ρ^j` is the indicial polynomial. This is the
algebraic kernel of the leading-coefficient identity for the Frobenius
substitution.

The concrete Apéry indicial polynomial (`aperyConifoldIndicial` in
`Ripple/Number/AperyConifoldIndicial.lean`) is an instance of this
general construction; the generalisation will be threaded through once
the remaining Frobenius steps (`Substitution.lean`, `LocalSolution.lean`)
are in place.
-/

namespace Ripple
namespace Number.Frobenius

open PowerSeries

/-- Euler operator `L = t · d/dt` on formal power series over `ℝ`:
coefficient-wise `aₙ ↦ n · aₙ`. -/
noncomputable def eulerOp (f : PowerSeries ℝ) : PowerSeries ℝ :=
  mk fun n => (n : ℝ) * coeff (R := ℝ) n f

@[simp] lemma coeff_eulerOp (f : PowerSeries ℝ) (n : ℕ) :
    coeff (R := ℝ) n (eulerOp f) = (n : ℝ) * coeff (R := ℝ) n f := by
  simp [eulerOp]

/-- The shifted Euler operator `ρ + L`: coefficient-wise
`aₙ ↦ (ρ + n) · aₙ`. -/
noncomputable def shiftedEuler (ρ : ℝ) (f : PowerSeries ℝ) : PowerSeries ℝ :=
  mk fun n => (ρ + n) * coeff (R := ℝ) n f

@[simp] lemma coeff_shiftedEuler (ρ : ℝ) (f : PowerSeries ℝ) (n : ℕ) :
    coeff (R := ℝ) n (shiftedEuler ρ f) = (ρ + n) * coeff (R := ℝ) n f := by
  simp [shiftedEuler]

/-- Iterating the shifted Euler operator scales the `n`-th coefficient by
`(ρ + n)^j`. -/
lemma coeff_shiftedEuler_iterate (ρ : ℝ) (f : PowerSeries ℝ) (j n : ℕ) :
    coeff (R := ℝ) n ((shiftedEuler ρ)^[j] f) = (ρ + n) ^ j * coeff (R := ℝ) n f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', coeff_shiftedEuler, ih]
    ring

/-- Key algebraic identity: the constant coefficient of `(ρ + L)^j g`
equals `ρ^j · g(0)`. This is the Lean version of
`(ρ + L)^j g |_{t=0} = ρ^j · g(0)`. -/
lemma coeff_zero_shiftedEuler_iterate (ρ : ℝ) (g : PowerSeries ℝ) (j : ℕ) :
    coeff (R := ℝ) 0 ((shiftedEuler ρ)^[j] g) = ρ ^ j * coeff (R := ℝ) 0 g := by
  have h := coeff_shiftedEuler_iterate ρ g j 0
  simpa using h

/-- The indicial polynomial associated to a normalised ODE
`Σ_{j=0}^{k} a_j(t) L^j y = 0`: evaluate the coefficients at `t = 0`,
then view `P(ρ) = Σ_j a_j(0) · ρ^j` as a polynomial in `ρ`.

The input `as : ℕ → ℝ` supplies the values `a_j(0)` and is ignored for
`j > k`. In the typical regular-singular-point setup one has `a_k(0) = 1`
(leading term normalised), but that is not required here. -/
noncomputable def indicialPoly (as : ℕ → ℝ) (k : ℕ) (ρ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), as j * ρ ^ j

lemma indicialPoly_zero_order (as : ℕ → ℝ) (ρ : ℝ) :
    indicialPoly as 0 ρ = as 0 := by
  simp [indicialPoly]

lemma indicialPoly_succ (as : ℕ → ℝ) (k : ℕ) (ρ : ℝ) :
    indicialPoly as (k + 1) ρ =
      indicialPoly as k ρ + as (k + 1) * ρ ^ (k + 1) := by
  simp [indicialPoly, Finset.sum_range_succ]

/-- **Leading-coefficient identity.** For the Frobenius ansatz
`y = t^ρ · g` and the Euler-form ODE `Σ_j a_j(t) L^j y = 0`, the constant
coefficient (coefficient of `t^0`) of the Frobenius-substituted operator
`Σ_j a_j(0) · (ρ + L)^j g` factors as `P(ρ) · g(0)`, where `P` is the
indicial polynomial.

This is the algebraic content of Step 1 of the Frobenius framework:
demanding vanishing at leading order and `g(0) ≠ 0` forces `P(ρ) = 0`,
i.e. `ρ` is an indicial root. -/
theorem coeff_zero_indicialSum (as : ℕ → ℝ) (k : ℕ) (ρ : ℝ) (g : PowerSeries ℝ) :
    coeff (R := ℝ) 0
        (∑ j ∈ Finset.range (k + 1), (as j) • (shiftedEuler ρ)^[j] g)
      = indicialPoly as k ρ * coeff (R := ℝ) 0 g := by
  rw [map_sum]
  unfold indicialPoly
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [LinearMap.map_smul, coeff_zero_shiftedEuler_iterate]
  simp [smul_eq_mul]
  ring

/-- **Corollary — indicial equation.** If the Frobenius-substituted
operator vanishes at leading order (constant coefficient equal to `0`)
and the formal series `g` has nonzero constant term, then `ρ` is a root
of the indicial polynomial. -/
theorem indicial_root_of_leading_vanish
    (as : ℕ → ℝ) (k : ℕ) (ρ : ℝ) (g : PowerSeries ℝ)
    (hg : coeff (R := ℝ) 0 g ≠ 0)
    (hvanish : coeff (R := ℝ) 0
        (∑ j ∈ Finset.range (k + 1), (as j) • (shiftedEuler ρ)^[j] g) = 0) :
    indicialPoly as k ρ = 0 := by
  have hmul : indicialPoly as k ρ * coeff (R := ℝ) 0 g = 0 := by
    rw [← coeff_zero_indicialSum]; exact hvanish
  exact (mul_eq_zero.mp hmul).resolve_right hg

end Number.Frobenius
end Ripple
