/-
  Ripple.LPP.MinPolyData — algebraic data & decomposition for the single-
  species min-polynomial PIVP (RTCRN1 Lemma 5.1). Split out from
  `Ripple.LPP.AlgebraicConstruction` so that `Ripple.Core.MinPolyBounded`
  can reuse the data without a circular import.

  Content (all axiom-free, proved):
    • `minPolyField`, `minPolyPIVP` — the PIVP data
    • `minPolyField_eval` — evaluation at a real point
    • `posPart`, `negPart` and their properties
    • `minPolyProd`, `minPolyDegr` — production/degradation split
    • coefficient non-negativity
    • `minPolyField_eq_decomp` — the core algebraic identity
-/


import Ripple.Core.BoundedTime
import Ripple.LPP.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing

namespace Ripple
namespace Algebraic

open MvPolynomial

/-! ## Data: single-species min-polynomial PIVP -/

/-- The syntactic MvPolynomial field for the one-species min-poly CRN:
    `field₀ = Σ_{k ≤ n} (c_k : ℚ) · X₀ᵏ`, where `c_k = P.coeff k`. -/
noncomputable def minPolyField (P : Polynomial ℤ) : MvPolynomial (Fin 1) ℚ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    C ((P.coeff k : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k

/-- The single-species PolyPIVP for RTCRN1's algebraic-number construction:
    one species X₀ with ODE dx/dt = P(x), x(0) = 0, output = X₀. -/
noncomputable def minPolyPIVP (P : Polynomial ℤ) : PolyPIVP 1 where
  field := fun _ => minPolyField P
  init := fun _ => 0
  output := 0

/-- Evaluation of the syntactic field at a real point yields the polynomial
sum with cast coefficients. -/
theorem minPolyField_eval (P : Polynomial ℤ) (x : Fin 1 → ℝ) :
    (minPolyField P).eval₂ (Rat.castHom ℝ) x
      = ∑ k ∈ Finset.range (P.natDegree + 1), ((P.coeff k : ℝ)) * x 0 ^ k := by
  unfold minPolyField
  change (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)
    (∑ k ∈ Finset.range (P.natDegree + 1),
      C ((P.coeff k : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k)
      = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp

/-! ## Decomposition: production + degradation split

Split each integer coefficient `c_k` into its positive part `c_k⁺` and
negative part `c_k⁻`, with `c_k = c_k⁺ − c_k⁻` and both parts `≥ 0`.

  prod_poly = Σ_{k} (c_k⁺ : ℚ) · X₀ᵏ
  degr_poly = Σ_{k ≥ 1} (c_k⁻ : ℚ) · X₀^{k-1}

When `c_0 ≥ 0` (WLOG by replacing P with −P) the identity

  field = prod_poly − degr_poly · X₀

holds as a formal polynomial identity, giving the CRN decomposition. -/

/-- Non-negative positive part of an integer: `c⁺ = max(c, 0)`, but we
express it via `if` so it extracts cleanly in `ℚ`. -/
def posPart (c : ℤ) : ℤ := if 0 ≤ c then c else 0

/-- Non-negative negative part: `c⁻ = max(−c, 0) = |c| when c ≤ 0 else 0`. -/
def negPart (c : ℤ) : ℤ := if c < 0 then -c else 0

theorem posPart_nonneg (c : ℤ) : 0 ≤ posPart c := by
  unfold posPart; split_ifs with h <;> [exact h; rfl]

theorem negPart_nonneg (c : ℤ) : 0 ≤ negPart c := by
  unfold negPart; split_ifs with h
  · exact Int.neg_nonneg.mpr (le_of_lt h)
  · rfl

theorem posPart_sub_negPart (c : ℤ) : posPart c - negPart c = c := by
  unfold posPart negPart
  by_cases h : 0 ≤ c
  · simp [h, not_lt.mpr h]
  · have hlt : c < 0 := lt_of_not_ge h
    simp [h, hlt]

/-- Production polynomial for the algebraic CRN: positive-part sum. -/
noncomputable def minPolyProd (P : Polynomial ℤ) : MvPolynomial (Fin 1) ℚ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    C ((posPart (P.coeff k) : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k

/-- Degradation polynomial: negative-part sum, with one X₀ factored out. -/
noncomputable def minPolyDegr (P : Polynomial ℤ) : MvPolynomial (Fin 1) ℚ :=
  ∑ k ∈ Finset.range P.natDegree,
    C ((negPart (P.coeff (k + 1)) : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k

/-- Non-negativity of every coefficient of the production polynomial. -/
theorem minPolyProd_coeff_nonneg (P : Polynomial ℤ) (σ : Fin 1 →₀ ℕ) :
    0 ≤ (minPolyProd P).coeff σ := by
  unfold minPolyProd
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro k _
  by_cases hσ : σ = Finsupp.single 0 k
  · rw [MvPolynomial.coeff_C_mul]
    have := posPart_nonneg (P.coeff k)
    have hq : (0 : ℚ) ≤ (posPart (P.coeff k) : ℚ) := by exact_mod_cast this
    have hX : (((X 0 : MvPolynomial (Fin 1) ℚ) ^ k).coeff σ) =
        (if σ = Finsupp.single 0 k then 1 else 0) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
      by_cases hh : σ = Finsupp.single 0 k
      · rw [if_pos hh.symm, if_pos hh]
      · rw [if_neg (fun h => hh h.symm), if_neg hh]
    rw [hX, if_pos hσ, mul_one]; exact hq
  · rw [MvPolynomial.coeff_C_mul]
    have hX : (((X 0 : MvPolynomial (Fin 1) ℚ) ^ k).coeff σ) =
        (if σ = Finsupp.single 0 k then 1 else 0) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
      by_cases hh : σ = Finsupp.single 0 k
      · rw [if_pos hh.symm, if_pos hh]
      · rw [if_neg (fun h => hh h.symm), if_neg hh]
    rw [hX, if_neg hσ, mul_zero]

/-- Non-negativity of every coefficient of the degradation polynomial. -/
theorem minPolyDegr_coeff_nonneg (P : Polynomial ℤ) (σ : Fin 1 →₀ ℕ) :
    0 ≤ (minPolyDegr P).coeff σ := by
  unfold minPolyDegr
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro k _
  by_cases hσ : σ = Finsupp.single 0 k
  · rw [MvPolynomial.coeff_C_mul]
    have := negPart_nonneg (P.coeff (k+1))
    have hq : (0 : ℚ) ≤ (negPart (P.coeff (k+1)) : ℚ) := by exact_mod_cast this
    have hX : (((X 0 : MvPolynomial (Fin 1) ℚ) ^ k).coeff σ) =
        (if σ = Finsupp.single 0 k then 1 else 0) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
      by_cases hh : σ = Finsupp.single 0 k
      · rw [if_pos hh.symm, if_pos hh]
      · rw [if_neg (fun h => hh h.symm), if_neg hh]
    rw [hX, if_pos hσ, mul_one]; exact hq
  · rw [MvPolynomial.coeff_C_mul]
    have hX : (((X 0 : MvPolynomial (Fin 1) ℚ) ^ k).coeff σ) = (if σ = Finsupp.single 0 k then 1 else 0) := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
      by_cases hh : σ = Finsupp.single 0 k
      · rw [if_pos hh.symm, if_pos hh]
      · rw [if_neg (fun h => hh h.symm), if_neg hh]
    rw [hX, if_neg hσ, mul_zero]

/-- Core algebraic identity: under the WLOG hypothesis `c_0 ≥ 0`, the
syntactic field `Σ_k C(c_k) X^k` equals `prod - degr * X` as a formal
polynomial identity. This is the RTCRN1 Lemma 5.1 decomposition. -/
theorem minPolyField_eq_decomp (P : Polynomial ℤ) (hc0 : 0 ≤ P.coeff 0) :
    minPolyField P = minPolyProd P - minPolyDegr P * X 0 := by
  unfold minPolyField minPolyProd minPolyDegr
  -- RHS's degr * X distributes
  rw [Finset.sum_mul]
  -- Peel off k=0 term from both the field sum and the prod sum
  rw [Finset.sum_range_succ' (fun k =>
    C ((P.coeff k : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k) P.natDegree]
  rw [Finset.sum_range_succ' (fun k =>
    C ((posPart (P.coeff k) : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k) P.natDegree]
  -- Match term by term
  have hc0_pos : posPart (P.coeff 0) = P.coeff 0 := by
    unfold posPart; rw [if_pos hc0]
  have hx0 : ((X 0 : MvPolynomial (Fin 1) ℚ) ^ (0 : ℕ)) = 1 := pow_zero _
  -- Rewrite the "shift" sums so their summands match
  have hsum_eq : ∀ k ∈ Finset.range P.natDegree,
      C ((posPart (P.coeff (k + 1)) : ℚ))
        * (X 0 : MvPolynomial (Fin 1) ℚ) ^ (k + 1)
      - C ((negPart (P.coeff (k + 1)) : ℚ))
        * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k * X 0
      = C ((P.coeff (k + 1) : ℚ))
        * (X 0 : MvPolynomial (Fin 1) ℚ) ^ (k + 1) := by
    intro k _
    have h_mul_assoc : C ((negPart (P.coeff (k + 1)) : ℚ))
        * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k * X 0
        = C ((negPart (P.coeff (k + 1)) : ℚ))
          * (X 0 : MvPolynomial (Fin 1) ℚ) ^ (k + 1) := by
      rw [mul_assoc, pow_succ]
    rw [h_mul_assoc]
    rw [← sub_mul]
    congr 1
    rw [← map_sub]
    congr 1
    have : (posPart (P.coeff (k+1)) : ℚ) - (negPart (P.coeff (k+1)) : ℚ)
        = ((posPart (P.coeff (k+1)) - negPart (P.coeff (k+1)) : ℤ) : ℚ) := by
      push_cast; ring
    rw [this, posPart_sub_negPart]
  -- Now goal: Σ c_{k+1} X^{k+1} + c_0 X^0
  --        = (Σ pos_{k+1} X^{k+1} + pos_0 X^0) - Σ neg_{k+1} X^k X
  -- Move to: prove the two sides are ring-equal after substituting hsum_eq
  have hrw : ∀ k ∈ Finset.range P.natDegree,
      C ((P.coeff (k + 1) : ℚ)) * (X 0 : MvPolynomial (Fin 1) ℚ) ^ (k + 1)
      = C ((posPart (P.coeff (k + 1)) : ℚ))
          * (X 0 : MvPolynomial (Fin 1) ℚ) ^ (k + 1)
        - C ((negPart (P.coeff (k + 1)) : ℚ))
          * (X 0 : MvPolynomial (Fin 1) ℚ) ^ k * X 0 := fun k hk =>
    (hsum_eq k hk).symm
  rw [Finset.sum_congr rfl hrw]
  rw [Finset.sum_sub_distrib]
  rw [hc0_pos]
  ring

end Algebraic
end Ripple
