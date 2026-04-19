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

The general case reduces to Lemma 5.1 in two focused steps:
  • algebraic_shift_to_smallest_positive_root: pick rational `q` and
    integer polynomial `P` such that α − q is the smallest positive
    root of P with `P.coeff 0 ≥ 0` (pure algebra — ensures P's roots
    in the positive real axis are bounded below by α − q);
  • certified_add_rational: the CRN/PolyCRNDecomposition output for
    a real β carries over to β + q for any q : ℚ (closure property,
    corresponds to RTCRN1 Section 4 addition closure).

These two axioms jointly implement Theorem 5.2, and both are named
to the precise paper content they discharge — no monolithic escape. -/

/-- Structural gap lemma supporting
`algebraic_shift_to_smallest_positive_root`. Given a nonzero integer
polynomial `p` and a real `α`, there exists a rational `q < α` such
that `p` has no real root in the open interval `(q, α)`. Proof: the
real roots of `p` form a finite set, so either no root lies below
`α` (pick any `q < α`) or the maximal root below `α` is strictly
less than `α`, and density of ℚ provides a rational strictly between
them. -/
lemma exists_rational_gap_below_real (p : Polynomial ℤ) (hp : p ≠ 0)
    (α : ℝ) :
    ∃ q : ℚ, (q : ℝ) < α ∧
      ∀ r : ℝ, (q : ℝ) < r → r < α →
        (Polynomial.aeval r p : ℝ) ≠ 0 := by
  classical
  let pℝ : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  have hpℝ_ne : pℝ ≠ 0 := by
    intro h
    apply hp
    have h' : p.map (Int.castRingHom ℝ)
        = (0 : Polynomial ℤ).map (Int.castRingHom ℝ) := by
      show pℝ = _
      rw [h, Polynomial.map_zero]
    exact Polynomial.map_injective _ Int.cast_injective h'
  -- aeval r p = eval r pℝ.
  have h_aeval_eq : ∀ r : ℝ,
      (Polynomial.aeval r p : ℝ) = pℝ.eval r := by
    intro r
    show Polynomial.eval₂ (Int.castRingHom ℝ) r p = pℝ.eval r
    rw [Polynomial.eval₂_eq_eval_map]
  -- S = real roots of p strictly below α.
  set S : Set ℝ := {r : ℝ | r < α ∧ pℝ.IsRoot r} with hS_def
  have hS_sub : S ⊆ {x | pℝ.IsRoot x} := fun _ hx => hx.2
  have hS_fin : S.Finite :=
    (Polynomial.finite_setOf_isRoot hpℝ_ne).subset hS_sub
  by_cases hS_ne : S.Nonempty
  · -- Pick the max element via the Finset induced by hS_fin.
    set T : Finset ℝ := hS_fin.toFinset with hT_def
    have hT_ne : T.Nonempty := by
      rw [hT_def, Set.Finite.toFinset_nonempty]
      exact hS_ne
    let r_max := T.max' hT_ne
    have hr_max_mem_T : r_max ∈ T := T.max'_mem hT_ne
    have hr_max_mem : r_max ∈ S := by
      have := hr_max_mem_T
      rwa [hT_def, Set.Finite.mem_toFinset] at this
    have hr_max_ub : ∀ r ∈ S, r ≤ r_max := fun r hr =>
      T.le_max' r (by rw [hT_def, Set.Finite.mem_toFinset]; exact hr)
    have hrmax_lt : r_max < α := hr_max_mem.1
    obtain ⟨q, _hq_gt, hq_lt⟩ := exists_rat_btwn hrmax_lt
    refine ⟨q, hq_lt, fun r hqr hrα hroot => ?_⟩
    have hroot' : pℝ.IsRoot r := by
      rw [Polynomial.IsRoot, ← h_aeval_eq r]
      exact hroot
    have hrS : r ∈ S := ⟨hrα, hroot'⟩
    have hle : r ≤ r_max := hr_max_ub r hrS
    linarith
  · -- S empty: no real root below α. Any q : ℚ with q < α works.
    obtain ⟨q, _, hq_lt⟩ := exists_rat_btwn (show α - 1 < α by linarith)
    refine ⟨q, hq_lt, fun r _ hrα hroot => ?_⟩
    have hroot' : pℝ.IsRoot r := by
      rw [Polynomial.IsRoot, ← h_aeval_eq r]
      exact hroot
    exact hS_ne ⟨r, hrα, hroot'⟩

/-- **Rational → integer polynomial clearing preserving real roots.**

Reusable step in the DNA 25 / RTCRN1 normalization chain: given any
nonzero `p : ℚ[X]`, there is a nonzero `P : ℤ[X]` with exactly the
same real roots (up to a nonzero scalar factor, so both sides vanish
simultaneously). Proof: `IsLocalization.integerNormalization` scales
`p` by a nonzero element `b` of `ℤ` to clear all denominators; the
real roots are preserved because `P.aeval β = b · p.aeval β` and
`b ≠ 0`.

This is the "clearing denominators" lemma per Xiang's 2026-04-18
guidance — factored as a standalone theorem so the algebraic-shift
axiom below reduces to pure root geometry without polynomial-
arithmetic clutter. -/
theorem rational_polynomial_to_integer_real_roots
    (p : Polynomial ℚ) (hp : p ≠ 0) :
    ∃ P : Polynomial ℤ, P ≠ 0 ∧
      ∀ β : ℝ, (Polynomial.aeval β P : ℝ) = 0 ↔
               (Polynomial.aeval β p : ℝ) = 0 := by
  classical
  let P : Polynomial ℤ :=
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) p
  obtain ⟨b, hb_mem, hb_eq⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  have hb_ne : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hb_mem
  have hP_ne : P ≠ 0 := by
    intro h
    exact hp
      ((IsLocalization.integerNormalization_eq_zero_iff
        (M := nonZeroDivisors ℤ) le_rfl p).mp h)
  refine ⟨P, hP_ne, fun β => ?_⟩
  -- aeval β P = (b : ℝ) * aeval β p via integerNormalization_spec.
  have h_cast : (algebraMap ℤ ℝ : ℤ →+* ℝ)
      = (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) := by
    ext n; simp
  have h_aeval : (Polynomial.aeval β P : ℝ)
      = (b : ℝ) * Polynomial.aeval β p := by
    -- Express aeval β P via eval₂ with composition to ℝ through ℚ.
    have h1 : (Polynomial.aeval β P : ℝ)
        = Polynomial.eval₂ (algebraMap ℚ ℝ) β (P.map (algebraMap ℤ ℚ)) := by
      rw [Polynomial.eval₂_map]
      show Polynomial.aeval β P = Polynomial.eval₂ (algebraMap ℤ ℝ) β P
      rw [Polynomial.aeval_def]
    -- Unfold ℤ-algebra smul to multiplication by C ((b : ℚ)).
    rw [Algebra.smul_def, eq_intCast (algebraMap ℤ (Polynomial ℚ)) b,
        ← Polynomial.C_eq_intCast (R := ℚ) b] at hb_eq
    rw [h1, hb_eq, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        ← Polynomial.aeval_def]
    simp
  constructor
  · intro h
    rw [h_aeval] at h
    rcases mul_eq_zero.mp h with hb0 | hp0
    · exact absurd (by exact_mod_cast hb0) hb_ne
    · exact hp0
  · intro h
    rw [h_aeval, h, mul_zero]

/-- Algebraic reduction to smallest-positive-root form. Given an
algebraic α, there exist a rational shift `q` and an integer
polynomial `P` such that α − q is the smallest positive root of P
with `P.coeff 0 ≥ 0`.

Proof composes three bricks:
1. `exists_rational_gap_below_real`: choose `q ∈ ℚ` with `q < α` and
   `(q, α)` containing no real root of the witnessing `p₀ : ℤ[X]`.
2. Shift `p₀` to `p₀(X + q) : ℚ[X]`, so `α − q` is its smallest
   positive real root (by the gap property).
3. `rational_polynomial_to_integer_real_roots`: clear denominators
   to `P_abs : ℤ[X]` with identical real roots, then sign-flip to
   enforce `P.coeff 0 ≥ 0`. -/
theorem algebraic_shift_to_smallest_positive_root {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (q : ℚ) (P : Polynomial ℤ),
      0 < α - (q : ℝ) ∧
      (Polynomial.aeval (α - (q : ℝ)) P : ℝ) = 0 ∧
      (∀ β : ℝ, 0 < β → β < α - (q : ℝ) →
        (Polynomial.aeval β P : ℝ) ≠ 0) ∧
      0 ≤ P.coeff 0 := by
  classical
  obtain ⟨p₀, hp₀_ne, hp₀_root⟩ := halg
  -- Brick 1: rational gap below α with no real roots of p₀.
  obtain ⟨q, hq_lt, hq_gap⟩ := exists_rational_gap_below_real p₀ hp₀_ne α
  -- Shift to ℚ[X] and compose with (X + C q).
  set p_ℚ_pre : Polynomial ℚ := p₀.map (algebraMap ℤ ℚ) with hp_ℚ_pre_def
  set p_ℚ : Polynomial ℚ := p_ℚ_pre.comp (Polynomial.X + Polynomial.C q)
    with hp_ℚ_def
  have hp_ℚ_pre_ne : p_ℚ_pre ≠ 0 := by
    rw [hp_ℚ_pre_def]
    exact fun h => hp₀_ne (Polynomial.map_injective _
      ((algebraMap ℤ ℚ).injective_int) (by rw [h, Polynomial.map_zero]))
  have hp_ℚ_ne : p_ℚ ≠ 0 := by
    intro h
    rw [hp_ℚ_def, Polynomial.comp_eq_zero_iff] at h
    rcases h with h | ⟨_, hcst⟩
    · exact hp_ℚ_pre_ne h
    · have hdeg : (Polynomial.X + Polynomial.C q : Polynomial ℚ).natDegree = 1 :=
        Polynomial.natDegree_X_add_C q
      have : (Polynomial.X + Polynomial.C q : Polynomial ℚ).natDegree = 0 := by
        rw [hcst]; simp
      omega
  -- Evaluation identity: aeval β p_ℚ = aeval (β + q) p₀ for β : ℝ.
  have h_eval : ∀ β : ℝ, (Polynomial.aeval β p_ℚ : ℝ) =
      (Polynomial.aeval (β + (q : ℝ)) p₀ : ℝ) := by
    intro β
    rw [hp_ℚ_def, Polynomial.aeval_comp, hp_ℚ_pre_def,
        Polynomial.aeval_map_algebraMap]
    simp
  -- Brick 2: clear denominators from p_ℚ : ℚ[X] to P_abs : ℤ[X].
  obtain ⟨P_abs, hP_abs_ne, hP_abs_iff⟩ :=
    rational_polynomial_to_integer_real_roots p_ℚ hp_ℚ_ne
  have h_P_abs_root : ∀ β : ℝ, (Polynomial.aeval β P_abs : ℝ) = 0 ↔
      (Polynomial.aeval (β + (q : ℝ)) p₀ : ℝ) = 0 := by
    intro β; rw [hP_abs_iff β, h_eval β]
  -- Sign case split: normalize so coeff 0 is non-negative.
  by_cases h_c0 : 0 ≤ P_abs.coeff 0
  · refine ⟨q, P_abs, by linarith, ?_, ?_, h_c0⟩
    · rw [h_P_abs_root]; simpa using hp₀_root
    · intro β hβ_pos hβ_lt hroot
      exact hq_gap (β + (q : ℝ)) (by linarith) (by linarith)
        ((h_P_abs_root β).mp hroot)
  · push_neg at h_c0
    refine ⟨q, -P_abs, by linarith, ?_, ?_, ?_⟩
    · have hroot : (Polynomial.aeval (α - (q : ℝ)) P_abs : ℝ) = 0 := by
        rw [h_P_abs_root]; simpa using hp₀_root
      simp [hroot]
    · intro β hβ_pos hβ_lt
      have hne : (Polynomial.aeval β P_abs : ℝ) ≠ 0 := fun hroot =>
        hq_gap (β + (q : ℝ)) (by linarith) (by linarith)
          ((h_P_abs_root β).mp hroot)
      simp [hne]
    · show 0 ≤ (-P_abs).coeff 0
      rw [Polynomial.coeff_neg]; linarith

/-- Additive closure for the certified CRN-computable data: shifting
the target by a rational number preserves the existence of a certified
CRN construction with a valid PolyCRNDecomposition. This is the
syntactic-certificate version of [RTCRN1] Lemma 4.3 (R_LCRN is closed
under addition), applied at the PolyPIVP / PolyCRNDecomposition level
rather than the IsRealTimeComputable property level. -/
axiom certified_add_rational {β : ℝ} (q : ℚ) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (_pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True

/-- RTCRN1 Theorem 5.2 assembled: every nonzero algebraic α admits a
CRN certificate via min-polynomial shift + Lemma 5.1 + additive
closure. This is now a theorem, not an axiom. -/
theorem algebraic_reduction_to_minpoly {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
      (_ : PolyCRNDecomposition d cbtc.pivp), True := by
  obtain ⟨q, P, hpos, hroot, hsmallest, hc0⟩ :=
    algebraic_shift_to_smallest_positive_root halg
  obtain ⟨cbtc, pcd, _⟩ := minPolyPIVP_certified hpos hroot hsmallest hc0
  have : α - (q : ℝ) + (q : ℝ) = α := by ring
  rw [← this]
  exact certified_add_rational q cbtc pcd

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
