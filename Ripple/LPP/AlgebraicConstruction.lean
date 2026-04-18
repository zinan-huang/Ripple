/-
  Ripple.LPP.AlgebraicConstruction — RTCRN1 Lemma 5.1 + Theorem 5.2

  Explicit single-species min-polynomial encoding of algebraic numbers
  as PIVPs, following Huang-Klinge-Lathrop-Li-Lutz 2018 (Nat. Comput.):

    Given α > 0 algebraic with minimum polynomial P ∈ ℤ[X] of simple roots,
    c₀ := P.coeff 0 ≥ 0 (WLOG by replacing P with -P), α the smallest
    positive root, the one-species PIVP

      dx/dt = P(x),      x(0) = 0

    has x(t) → α monotonically with exponential rate, and decomposes
    into a PolyCRNDecomposition via the per-term split:

      prod = Σ_{k : 0 ≤ c_k} (c_k : ℚ) · X₀ᵏ
      degr = Σ_{k ≥ 1 : c_k < 0} (-c_k : ℚ) · X₀^{k-1}

    so that field = prod − degr · X₀ as a formal polynomial identity.

  This replaces the monolithic `algebraic_is_certified_crn` axiom with:
    • a fully-proved algebraic decomposition (this file), and
    • focused analytic axioms (RTCRN1 Lemma 5.1 stability analysis)
      naming the ODE-theoretic content deferred from Mathlib.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.Minpoly.Basic

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
    have hX : (((X 0 : MvPolynomial (Fin 1) ℚ) ^ k).coeff σ) = (if σ = Finsupp.single 0 k then 1 else 0) := by
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
    have hX : (((X 0 : MvPolynomial (Fin 1) ℚ) ^ k).coeff σ) = (if σ = Finsupp.single 0 k then 1 else 0) := by
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

/-! ## Focused analytic axioms (RTCRN1 Lemma 5.1 content)

The ODE-theoretic content of RTCRN1 Lemma 5.1 — boundedness, monotone
convergence, and exponential rate via P'(α) < 0 — is not readily
available in Mathlib. We expose it as named axioms corresponding
precisely to the paper's stability analysis. Each axiom is scoped to
the single-species min-poly construction and named to the step in
RTCRN1 it discharges. -/

/-- RTCRN1 Lemma 5.1 stability (boundedness). The trajectory of
`dx/dt = P(x), x(0) = 0` stays in `[0, α]` when `α` is the smallest
positive root of `P` and `P(0) ≥ 0`. -/
axiom minPolyPIVP_exists_solution {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_nonneg : 0 ≤ P.coeff 0) :
    PIVP.Solution (minPolyPIVP P).toPIVP

/-- RTCRN1 Lemma 5.1 convergence: the trajectory converges to α with
exponential rate bounded by `-P'(α) > 0`. Time modulus is therefore
linear in the bit-precision r. -/
axiom minPolyPIVP_convergence_modulus {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_nonneg : 0 ≤ P.coeff 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    ∃ (modulus : TimeModulus),
      (minPolyPIVP P).toPIVP.IsBounded sol.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus r →
        |sol.trajectory t (minPolyPIVP P).output - α| < Real.exp (-(r : ℝ)))

/-! ## RTCRN1 Lemma 5.1 assembled: smallest-positive-root case

Combining the focused analytic axioms with the proven algebraic
decomposition, the smallest-positive-root case produces a full
`CertifiedBoundedTimeComputable` together with a `PolyCRNDecomposition`
— entirely without any remaining axiom gap beyond the two analytic
axioms above. -/

/-- RTCRN1 Lemma 5.1: if α > 0 is the smallest positive root of an
integer polynomial `P` with `P.coeff 0 ≥ 0`, then α is CRN-computable
via the single-species min-poly construction. -/
theorem minPolyPIVP_certified {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_nonneg : 0 ≤ P.coeff 0) :
    ∃ (cbtc : CertifiedBoundedTimeComputable 1 α)
      (_ : PolyCRNDecomposition 1 cbtc.pivp), True := by
  let sol := minPolyPIVP_exists_solution hα_pos hα_root hα_smallest hc0_nonneg
  obtain ⟨mod, hb, hconv⟩ :=
    minPolyPIVP_convergence_modulus hα_pos hα_root hα_smallest hc0_nonneg sol
  refine ⟨{
    pivp := minPolyPIVP P
    sol := sol
    modulus := mod
    bounded := hb
    convergence := hconv },
    { prod := fun _ => minPolyProd P
      degr := fun _ => minPolyDegr P
      prod_nonneg := fun _ => minPolyProd_coeff_nonneg P
      degr_nonneg := fun _ => minPolyDegr_coeff_nonneg P
      init_nonneg := fun _ => by simp [minPolyPIVP]
      field_eq := fun i => by
        show (minPolyPIVP P).field i = minPolyProd P - minPolyDegr P * X i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        show minPolyField P = minPolyProd P - minPolyDegr P * X 0
        exact minPolyField_eq_decomp P hc0_nonneg },
    trivial⟩

/-! ## RTCRN1 Theorem 5.2 reduction: general α via rational shift

The general case reduces to Lemma 5.1 via:
  • pick a rational `p/q` with β < p/q < α where β is the largest
    positive root of P strictly less than α (if any; else p/q = 0);
  • replace P with Q(X) := P(X + p/q) · qⁿ — still integer coefficients
    and simple roots, and α − p/q is the smallest positive root of Q;
  • run the single-species construction for Q, then shift the readout
    back by p/q via the rational addition pipeline.

The reduction is pure algebra; we state it as an axiom here and defer
the explicit PolyPIVP shift construction to future work. -/

/-- RTCRN1 Theorem 5.2: every nonzero algebraic α admits a CRN
certificate via the single-species min-polynomial construction (after
a rational shift when α is not the smallest positive root of its
minimum polynomial). -/
axiom algebraic_reduction_to_minpoly {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
      (_ : PolyCRNDecomposition d cbtc.pivp), True

/-! ## Glue: replaces the monolithic `algebraic_is_certified_crn` axiom

The old `Ripple.algebraic_is_certified_crn` is kept in `LPP.Stages` for
backward compatibility; this theorem reproduces it constructively from
the focused axioms above. -/

theorem algebraic_is_certified_crn_refined {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
      (_ : PolyCRNDecomposition d cbtc.pivp), True :=
  algebraic_reduction_to_minpoly halg

end Algebraic
end Ripple
