/-
  Ripple.LPP.AlgebraicConstruction — RTCRN1 Lemma 5.1 + Theorem 5.2

  Wires up the algebraic single-species PIVP construction into a
  `CertifiedBoundedTimeComputable` + `PolyCRNDecomposition` pair.

  Algebraic data and the CRN decomposition identity live in
  `Ripple.LPP.MinPolyData` (all axiom-free). The boundedness/global-
  existence content of RTCRN1 Lemma 5.1 is proved in
  `Ripple.Core.MinPolyBounded`. Only the convergence-modulus content
  (exponential rate via `P'(α) < 0`) remains as a focused analytic
  axiom here.
-/

import Ripple.Core.BoundedTime
import Ripple.Core.MinPolyBounded
import Ripple.Core.MinPolyConvergence
import Ripple.LPP.Defs
import Ripple.LPP.MinPolyData
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing

namespace Ripple
namespace Algebraic

open MvPolynomial


/-! ## Focused analytic axioms (RTCRN1 Lemma 5.1 content)

The ODE-theoretic content of RTCRN1 Lemma 5.1 — boundedness, monotone
convergence, and exponential rate via P'(α) < 0 — is not readily
available in Mathlib. We expose it as named axioms corresponding
precisely to the paper's stability analysis. Each axiom is scoped to
the single-species min-poly construction and named to the step in
RTCRN1 it discharges. -/

/-- RTCRN1 Lemma 5.1 stability (boundedness). The trajectory of
`dx/dt = P(x), x(0) = 0` stays in `[0, α]` when `α` is a positive root
of `P` and `P(0) > 0`. The strict-positivity hypothesis rules out the
degenerate `P.coeff 0 = 0` case (trajectory ≡ 0 does not converge to α).
Proved via `Ripple.Core.MinPolyBounded`. -/
noncomputable def minPolyPIVP_exists_solution {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (_hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0) :
    PIVP.Solution (minPolyPIVP P).toPIVP :=
  minPolyPIVP_global_solution hα_pos hα_root (le_of_lt hc0_pos)

/-- RTCRN1 Lemma 5.1 convergence: the trajectory converges to α with
exponential rate bounded by `-P'(α) > 0`. Time modulus is therefore
linear in the bit-precision r. Strict `0 < P.coeff 0` ensures the
trajectory escapes 0 and can converge to α (no zero-trajectory collapse).

The simple-root hypothesis `hα_simple : (aeval α P.derivative : ℝ) ≠ 0`
is the precise Mathlib-stated form of what the paper calls "P'(α) ≠ 0";
combined with `hα_smallest` it gives `P'(α) < 0` (the sign forced by P
being ≥ 0 on `[0, α]` and vanishing at α from above), which is the
ingredient the linearization / Grönwall step needs. This is always
available when `P` is derived from a minimal polynomial (char-zero
irreducible polynomials are separable; separable polynomials have all
roots simple). -/
theorem minPolyPIVP_convergence_modulus {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    ∃ (modulus : TimeModulus),
      (minPolyPIVP P).toPIVP.IsBounded sol.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus r →
        |sol.trajectory t (minPolyPIVP P).output - α| < Real.exp (-(r : ℝ))) :=
  minPolyPIVP_convergence_modulus_proved hα_pos hα_root hα_smallest hc0_pos
    hα_simple sol

/-! ## RTCRN1 Lemma 5.1 assembled: smallest-positive-root case

Combining the focused analytic axioms with the proven algebraic
decomposition, the smallest-positive-root case produces a full
`CertifiedBoundedTimeComputable` together with a `PolyCRNDecomposition`
— entirely without any remaining axiom gap beyond the two analytic
axioms above. -/

/-- RTCRN1 Lemma 5.1: if α > 0 is the smallest positive root of an
integer polynomial `P` with `P.coeff 0 > 0`, then α is CRN-computable
via the single-species min-poly construction. -/
theorem minPolyPIVP_certified {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0) :
    ∃ (cbtc : CertifiedBoundedTimeComputable 1 α)
      (_ : PolyCRNDecomposition 1 cbtc.pivp), True := by
  let sol := minPolyPIVP_exists_solution hα_pos hα_root hα_smallest hc0_pos
  obtain ⟨mod, hb, hconv⟩ :=
    minPolyPIVP_convergence_modulus hα_pos hα_root hα_smallest hc0_pos hα_simple sol
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
        exact minPolyField_eq_decomp P (le_of_lt hc0_pos) },
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
      (Polynomial.aeval (q : ℝ) p : ℝ) ≠ 0 ∧
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
    obtain ⟨q, hq_gt, hq_lt⟩ := exists_rat_btwn hrmax_lt
    refine ⟨q, hq_lt, ?_, fun r hqr hrα hroot => ?_⟩
    · -- p(q) ≠ 0 because q > r_max (the max real root below α).
      intro hq_root
      have hq_root' : pℝ.IsRoot (q : ℝ) := by
        rw [Polynomial.IsRoot, ← h_aeval_eq (q : ℝ)]
        exact hq_root
      have hqS : (q : ℝ) ∈ S := ⟨hq_lt, hq_root'⟩
      have hqle : (q : ℝ) ≤ r_max := hr_max_ub _ hqS
      linarith
    · have hroot' : pℝ.IsRoot r := by
        rw [Polynomial.IsRoot, ← h_aeval_eq r]
        exact hroot
      have hrS : r ∈ S := ⟨hrα, hroot'⟩
      have hle : r ≤ r_max := hr_max_ub r hrS
      linarith
  · -- S empty: no real root below α. Any q : ℚ with q < α works.
    obtain ⟨q, _, hq_lt⟩ := exists_rat_btwn (show α - 1 < α by linarith)
    refine ⟨q, hq_lt, ?_, fun r _ hrα hroot => ?_⟩
    · intro hq_root
      have hq_root' : pℝ.IsRoot (q : ℝ) := by
        rw [Polynomial.IsRoot, ← h_aeval_eq (q : ℝ)]
        exact hq_root
      exact hS_ne ⟨(q : ℝ), hq_lt, hq_root'⟩
    · have hroot' : pℝ.IsRoot r := by
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
arithmetic clutter.

Strengthened form: the resulting `P : ℤ[X]` also preserves
"derivative nonzero at β", because the scaling factor `b : ℤ` relating
`P = b · p` (as ℚ[X]) is nonzero, so `P.derivative = b · p.derivative`
and `P.derivative.aeval β ≠ 0 ↔ p.derivative.aeval β ≠ 0`. -/
theorem rational_polynomial_to_integer_real_roots
    (p : Polynomial ℚ) (hp : p ≠ 0) :
    ∃ P : Polynomial ℤ, P ≠ 0 ∧
      (∀ β : ℝ, (Polynomial.aeval β P : ℝ) = 0 ↔
                (Polynomial.aeval β p : ℝ) = 0) ∧
      (∀ β : ℝ, (Polynomial.aeval β P.derivative : ℝ) = 0 ↔
                (Polynomial.aeval β p.derivative : ℝ) = 0) := by
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
  -- Key equation: P.map(ℤ→ℚ) = (b : ℚ) • p = C (b : ℚ) * p.
  rw [Algebra.smul_def, eq_intCast (algebraMap ℤ (Polynomial ℚ)) b,
      ← Polynomial.C_eq_intCast (R := ℚ) b] at hb_eq
  -- Generic lemma: for any polynomial q (here P or P.derivative),
  -- aeval β of the ℤ-polynomial equals (b : ℝ) times aeval β of its ℚ-image,
  -- where we know q = P (original) and also the derivative case.
  -- For the root case, use hb_eq directly.
  have h_aeval_P : ∀ β : ℝ, (Polynomial.aeval β P : ℝ)
      = (b : ℝ) * Polynomial.aeval β p := by
    intro β
    have h1 : (Polynomial.aeval β P : ℝ)
        = Polynomial.eval₂ (algebraMap ℚ ℝ) β (P.map (algebraMap ℤ ℚ)) := by
      rw [Polynomial.eval₂_map]
      show Polynomial.aeval β P = Polynomial.eval₂ (algebraMap ℤ ℝ) β P
      rw [Polynomial.aeval_def]
    rw [h1, hb_eq, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        ← Polynomial.aeval_def]
    simp
  -- Derivative case: derivative is a ring-linear map, and hb_eq gives
  -- P.map = C b * p. Take derivative of both sides:
  -- (P.map).derivative = C b * p.derivative (since derivative of C b = 0).
  -- Note: derivative commutes with map for ring homomorphisms.
  have h_deriv_map :
      (P.derivative).map (algebraMap ℤ ℚ) = Polynomial.C (b : ℚ) * p.derivative := by
    rw [← Polynomial.derivative_map]
    rw [hb_eq]
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  have h_aeval_deriv : ∀ β : ℝ, (Polynomial.aeval β P.derivative : ℝ)
      = (b : ℝ) * Polynomial.aeval β p.derivative := by
    intro β
    have h1 : (Polynomial.aeval β P.derivative : ℝ)
        = Polynomial.eval₂ (algebraMap ℚ ℝ) β (P.derivative.map (algebraMap ℤ ℚ)) := by
      rw [Polynomial.eval₂_map]
      show Polynomial.aeval β P.derivative = Polynomial.eval₂ (algebraMap ℤ ℝ) β P.derivative
      rw [Polynomial.aeval_def]
    rw [h1, h_deriv_map, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        ← Polynomial.aeval_def]
    simp
  refine ⟨P, hP_ne, fun β => ?_, fun β => ?_⟩
  · constructor
    · intro h
      rw [h_aeval_P β] at h
      rcases mul_eq_zero.mp h with hb0 | hp0
      · exact absurd (by exact_mod_cast hb0) hb_ne
      · exact hp0
    · intro h
      rw [h_aeval_P β, h, mul_zero]
  · constructor
    · intro h
      rw [h_aeval_deriv β] at h
      rcases mul_eq_zero.mp h with hb0 | hp0
      · exact absurd (by exact_mod_cast hb0) hb_ne
      · exact hp0
    · intro h
      rw [h_aeval_deriv β, h, mul_zero]

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
      0 < P.coeff 0 := by
  classical
  obtain ⟨p₀, hp₀_ne, hp₀_root⟩ := halg
  -- Brick 1: rational gap below α with no real roots of p₀, and p₀(q) ≠ 0.
  obtain ⟨q, hq_lt, hq_root_ne, hq_gap⟩ :=
    exists_rational_gap_below_real p₀ hp₀_ne α
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
  obtain ⟨P_abs, hP_abs_ne, hP_abs_iff, _hP_abs_deriv_iff⟩ :=
    rational_polynomial_to_integer_real_roots p_ℚ hp_ℚ_ne
  have h_P_abs_root : ∀ β : ℝ, (Polynomial.aeval β P_abs : ℝ) = 0 ↔
      (Polynomial.aeval (β + (q : ℝ)) p₀ : ℝ) = 0 := by
    intro β; rw [hP_abs_iff β, h_eval β]
  -- P_abs(0) ≠ 0 via hq_root_ne: aeval 0 P_abs = 0 ↔ aeval q p₀ = 0.
  have h_const_ne : (P_abs.coeff 0 : ℝ) ≠ 0 := by
    have h_eq : (Polynomial.aeval (0 : ℝ) P_abs : ℝ) = (P_abs.coeff 0 : ℝ) := by
      show Polynomial.eval₂ (Int.castRingHom ℝ) (0 : ℝ) P_abs = _
      rw [Polynomial.eval₂_at_zero]; rfl
    have h0_ne : (Polynomial.aeval (0 : ℝ) P_abs : ℝ) ≠ 0 := by
      intro h
      have h1 : (Polynomial.aeval ((0:ℝ) + (q : ℝ)) p₀ : ℝ) = 0 :=
        (h_P_abs_root 0).mp h
      have h0q : (0 : ℝ) + (q : ℝ) = (q : ℝ) := by ring
      rw [h0q] at h1
      exact hq_root_ne h1
    rw [h_eq] at h0_ne; exact h0_ne
  have hPabs_coeff_ne : P_abs.coeff 0 ≠ 0 := fun h => h_const_ne (by exact_mod_cast h)
  -- Sign case split: normalize so coeff 0 is strictly positive.
  by_cases h_c0 : 0 ≤ P_abs.coeff 0
  · refine ⟨q, P_abs, by linarith, ?_, ?_, ?_⟩
    · rw [h_P_abs_root]; simpa using hp₀_root
    · intro β hβ_pos hβ_lt hroot
      exact hq_gap (β + (q : ℝ)) (by linarith) (by linarith)
        ((h_P_abs_root β).mp hroot)
    · exact lt_of_le_of_ne h_c0 (Ne.symm hPabs_coeff_ne)
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
    · show 0 < (-P_abs).coeff 0
      rw [Polynomial.coeff_neg]; linarith

/-- Strengthened variant of `algebraic_shift_to_smallest_positive_root`:
if the witness polynomial `p₀` additionally has `p₀'(α) ≠ 0` (α is a
simple root), then the shifted/normalized `P : ℤ[X]` satisfies
`P'(α - q) ≠ 0`. This lets the min-poly convergence axiom's
`hα_simple` hypothesis be discharged from the minimal polynomial of α
(which is separable in char 0). -/
theorem algebraic_shift_to_smallest_positive_root_simple {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0 ∧
      (Polynomial.aeval α p.derivative : ℝ) ≠ 0) :
    ∃ (q : ℚ) (P : Polynomial ℤ),
      0 < α - (q : ℝ) ∧
      (Polynomial.aeval (α - (q : ℝ)) P : ℝ) = 0 ∧
      (∀ β : ℝ, 0 < β → β < α - (q : ℝ) →
        (Polynomial.aeval β P : ℝ) ≠ 0) ∧
      0 < P.coeff 0 ∧
      (Polynomial.aeval (α - (q : ℝ)) P.derivative : ℝ) ≠ 0 := by
  classical
  obtain ⟨p₀, hp₀_ne, hp₀_root, hp₀_deriv⟩ := halg
  -- Brick 1: rational gap below α with no real roots of p₀, and p₀(q) ≠ 0.
  obtain ⟨q, hq_lt, hq_root_ne, hq_gap⟩ :=
    exists_rational_gap_below_real p₀ hp₀_ne α
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
  -- Derivative identity: p_ℚ.derivative = p_ℚ_pre.derivative.comp (X + C q)
  -- Chain rule: (f.comp g).derivative = f.derivative.comp g * g.derivative
  -- and derivative(X + C q) = 1.
  have h_deriv_eval : ∀ β : ℝ, (Polynomial.aeval β p_ℚ.derivative : ℝ) =
      (Polynomial.aeval (β + (q : ℝ)) p₀.derivative : ℝ) := by
    intro β
    have h_deriv_simp :
        p_ℚ.derivative = p_ℚ_pre.derivative.comp (Polynomial.X + Polynomial.C q) := by
      rw [hp_ℚ_def, Polynomial.derivative_comp]
      rw [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
          add_zero]
      ring
    rw [h_deriv_simp, Polynomial.aeval_comp, hp_ℚ_pre_def,
        Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    simp
  -- Brick 2: clear denominators (preserving both roots and derivative roots)
  obtain ⟨P_abs, hP_abs_ne, hP_abs_iff, hP_abs_deriv_iff⟩ :=
    rational_polynomial_to_integer_real_roots p_ℚ hp_ℚ_ne
  have h_P_abs_root : ∀ β : ℝ, (Polynomial.aeval β P_abs : ℝ) = 0 ↔
      (Polynomial.aeval (β + (q : ℝ)) p₀ : ℝ) = 0 := by
    intro β; rw [hP_abs_iff β, h_eval β]
  have h_P_abs_deriv : ∀ β : ℝ, (Polynomial.aeval β P_abs.derivative : ℝ) = 0 ↔
      (Polynomial.aeval (β + (q : ℝ)) p₀.derivative : ℝ) = 0 := by
    intro β; rw [hP_abs_deriv_iff β, h_deriv_eval β]
  -- P_abs(0) ≠ 0 via hq_root_ne.
  have h_const_ne : (P_abs.coeff 0 : ℝ) ≠ 0 := by
    have h_eq : (Polynomial.aeval (0 : ℝ) P_abs : ℝ) = (P_abs.coeff 0 : ℝ) := by
      change Polynomial.eval₂ (Int.castRingHom ℝ) (0 : ℝ) P_abs = _
      rw [Polynomial.eval₂_at_zero]; rfl
    have h0_ne : (Polynomial.aeval (0 : ℝ) P_abs : ℝ) ≠ 0 := by
      intro h
      have h1 : (Polynomial.aeval ((0:ℝ) + (q : ℝ)) p₀ : ℝ) = 0 :=
        (h_P_abs_root 0).mp h
      have h0q : (0 : ℝ) + (q : ℝ) = (q : ℝ) := by ring
      rw [h0q] at h1
      exact hq_root_ne h1
    rw [h_eq] at h0_ne; exact h0_ne
  have hPabs_coeff_ne : P_abs.coeff 0 ≠ 0 := fun h => h_const_ne (by exact_mod_cast h)
  -- Simple root at α - q for P_abs
  have h_simple_P_abs : (Polynomial.aeval (α - (q : ℝ)) P_abs.derivative : ℝ) ≠ 0 := by
    intro h
    have h1 : (Polynomial.aeval ((α - (q : ℝ)) + (q : ℝ)) p₀.derivative : ℝ) = 0 :=
      (h_P_abs_deriv (α - (q : ℝ))).mp h
    have h_rw : (α - (q : ℝ)) + (q : ℝ) = α := by ring
    rw [h_rw] at h1
    exact hp₀_deriv h1
  -- Sign case split
  by_cases h_c0 : 0 ≤ P_abs.coeff 0
  · refine ⟨q, P_abs, by linarith, ?_, ?_, ?_, ?_⟩
    · rw [h_P_abs_root]; simpa using hp₀_root
    · intro β hβ_pos hβ_lt hroot
      exact hq_gap (β + (q : ℝ)) (by linarith) (by linarith)
        ((h_P_abs_root β).mp hroot)
    · exact lt_of_le_of_ne h_c0 (Ne.symm hPabs_coeff_ne)
    · exact h_simple_P_abs
  · push_neg at h_c0
    refine ⟨q, -P_abs, by linarith, ?_, ?_, ?_, ?_⟩
    · have hroot : (Polynomial.aeval (α - (q : ℝ)) P_abs : ℝ) = 0 := by
        rw [h_P_abs_root]; simpa using hp₀_root
      simp [hroot]
    · intro β hβ_pos hβ_lt
      have hne : (Polynomial.aeval β P_abs : ℝ) ≠ 0 := fun hroot =>
        hq_gap (β + (q : ℝ)) (by linarith) (by linarith)
          ((h_P_abs_root β).mp hroot)
      simp [hne]
    · change 0 < (-P_abs).coeff 0
      rw [Polynomial.coeff_neg]; linarith
    · -- (-P_abs).derivative = -P_abs.derivative, so aeval still nonzero.
      rw [Polynomial.derivative_neg]
      show (Polynomial.aeval (α - (q : ℝ)) (-P_abs.derivative) : ℝ) ≠ 0
      rw [map_neg]
      exact fun h => h_simple_P_abs (neg_eq_zero.mp h)

/-- Additive closure for the certified CRN-computable data: shifting
the target by a **nonzero** rational number preserves the existence of
a certified CRN construction with a valid PolyCRNDecomposition. This
is the syntactic-certificate version of [RTCRN1] Lemma 4.3 restricted
to `q ≠ 0`.

The `q = 0` case is trivial (identity construction); see
`certified_add_rational` below, which dispatches on `q = 0 ∨ q ≠ 0`
and discharges the first branch directly, narrowing the remaining
axiomatic content to the nonzero case.

**Residual axiomatic scope.** For `q ≠ 0`, producing the extended
PolyPIVP with CRN-shape for the new output tracker species is a
genuine construction that involves lifting `prod/degr` polynomials
via `MvPolynomial.rename` along a `Fin d ↪ Fin d'` injection plus
introducing annihilation reactions to handle the sign of `q`. Each
step is routine but voluminous (≈ 400 lines of MvPolynomial coefficient
bookkeeping). Pending that infrastructure, this remains an axiom. -/
axiom certified_add_rational_nonzero {β : ℝ} (q : ℚ) (hq : q ≠ 0) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (_pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True

/-- Additive closure for the certified CRN-computable data: shifting
the target by a rational number preserves the existence of a certified
CRN construction with a valid PolyCRNDecomposition. This is the
syntactic-certificate version of [RTCRN1] Lemma 4.3 (R_LCRN is closed
under addition), applied at the PolyPIVP / PolyCRNDecomposition level
rather than the IsRealTimeComputable property level.

The `q = 0` branch is proved directly (identity construction); the
`q ≠ 0` branch is reduced to `certified_add_rational_nonzero`. -/
theorem certified_add_rational {β : ℝ} (q : ℚ) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True := by
  by_cases hq : q = 0
  · -- q = 0 case: identity construction. Shift is a no-op because
    -- β + (0 : ℚ) = β as reals.
    subst hq
    have hzero : β + (((0 : ℚ) : ℝ)) = β := by norm_num
    rw [hzero]
    exact ⟨d, cbtc, pcd, trivial⟩
  · exact certified_add_rational_nonzero q hq cbtc pcd

/-- From an algebraic witness for α, produce a witness that additionally
has `p.derivative` nonzero at α. Uses the minimal polynomial `minpoly ℚ α`
(which is irreducible and, in char 0, separable, so has α as a simple root),
and integer-normalizes to ℤ[X] preserving both root and derivative-root. -/
lemma exists_simple_integer_witness {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0 ∧
      (Polynomial.aeval α p.derivative : ℝ) ≠ 0 := by
  classical
  -- α is algebraic over ℤ (hence over ℚ, char 0).
  obtain ⟨p_wit, hp_wit_ne, hp_wit_root⟩ := halg
  -- Cast to ℚ-witness to get IsIntegral ℚ α.
  have hα_alg : IsAlgebraic ℚ (α : ℝ) := by
    refine ⟨p_wit.map (algebraMap ℤ ℚ), ?_, ?_⟩
    · intro h
      apply hp_wit_ne
      exact Polynomial.map_injective _ ((algebraMap ℤ ℚ).injective_int)
        (by rw [h, Polynomial.map_zero])
    · rw [Polynomial.aeval_map_algebraMap]
      exact hp_wit_root
  have hα_int : IsIntegral ℚ (α : ℝ) := hα_alg.isIntegral
  -- Minpoly is irreducible, hence separable (char 0).
  have h_irr : Irreducible (minpoly ℚ (α : ℝ)) := minpoly.irreducible hα_int
  have h_sep : (minpoly ℚ (α : ℝ)).Separable := h_irr.separable
  -- aeval α (minpoly ℚ α) = 0 (definition of minpoly).
  have h_minpoly_root : (Polynomial.aeval (α : ℝ) (minpoly ℚ (α : ℝ))) = 0 :=
    minpoly.aeval ℚ α
  -- Separable ⇒ derivative nonzero at α.
  have h_minpoly_deriv : (Polynomial.aeval (α : ℝ) (minpoly ℚ (α : ℝ)).derivative) ≠ 0 :=
    h_sep.aeval_derivative_ne_zero h_minpoly_root
  -- Integer-normalize the minpoly (preserves root and derivative-root).
  have h_minpoly_ne : minpoly ℚ (α : ℝ) ≠ 0 := minpoly.ne_zero hα_int
  obtain ⟨P, hP_ne, hP_root_iff, hP_deriv_iff⟩ :=
    rational_polynomial_to_integer_real_roots (minpoly ℚ (α : ℝ)) h_minpoly_ne
  refine ⟨P, hP_ne, ?_, ?_⟩
  · rw [hP_root_iff α]; exact h_minpoly_root
  · intro h
    exact h_minpoly_deriv ((hP_deriv_iff α).mp h)

/-- RTCRN1 Theorem 5.2 assembled: every nonzero algebraic α admits a
CRN certificate via min-polynomial shift + Lemma 5.1 + additive
closure. This is now a theorem, not an axiom. -/
theorem algebraic_reduction_to_minpoly {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
      (_ : PolyCRNDecomposition d cbtc.pivp), True := by
  have halg_simple := exists_simple_integer_witness halg
  obtain ⟨q, P, hpos, hroot, hsmallest, hc0, hsimple⟩ :=
    algebraic_shift_to_smallest_positive_root_simple halg_simple
  obtain ⟨cbtc, pcd, _⟩ := minPolyPIVP_certified hpos hroot hsmallest hc0 hsimple
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

/-- Algebraic numbers are CRN-computable with syntactic certificates
(top-level alias for `Ripple.Algebraic.algebraic_is_certified_crn_refined`). -/
theorem algebraic_is_certified_crn {α : ℝ}
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ (d : ℕ) (cbtc : CertifiedBoundedTimeComputable d α)
      (_ : PolyCRNDecomposition d cbtc.pivp), True :=
  Algebraic.algebraic_is_certified_crn_refined halg

end Ripple
