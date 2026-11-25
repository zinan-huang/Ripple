/-
  Ripple.DualRail.ConstantAnnihilationGeneral —
  UCNC 2025 Problem 1 (Haisler-Huang-Migunov-Mohammed-Provence) for general
  bounded multi-dimensional GPACs.

  This file resolves the general n-dimensional case of UCNC 2025 Problem 1.
  The argument (research note `notes/constant-annihilation-UCNC25.tex`,
  rev. 2026-04-26) is:

  1. **Algebraic identity** (`posPlusNeg_eq_absMvEval_at_sigma`).
     For any polynomial `q : MvPolynomial (Fin n) ℚ` and non-negative state
     `(u, v) ≥ 0`,
        p̂⁺(u,v) + p̂⁻(u,v) = |q|(σ_1, …, σ_n)
     where p̂ = q ∘ (u - v), |q| is the polynomial obtained from `q` by
     replacing each coefficient with its absolute value, and σ_j = u_j + v_j.

  2. **Per-component σ-drift** (`sigma_drift`).
     σ_i' = |p_i|(σ_1, …, σ_n) − (k/2)·(σ_i² − y_i²).

  3. **Nagumo box invariance.** For
        k_⋆(p, β) := max_i 2·|p_i|(2β, …, 2β) / (3β²),
     and any k > k_⋆(p, β) + 1, the box
        B_β = { (u, v) ≥ 0 : σ_i ≤ 2β, |u_i − v_i| ≤ β  ∀i }
     is forward-invariant under the constant-k uniform dual-rail flow,
     starting from (0, 0).

  Status: scaffolding + main theorem statement; algebraic identity and
  σ-barrier proofs are work-in-progress.

  References:
  - `Ripple/DualRail/ConstantAnnihilation.lean` (problem statement, base infra)
  - `Ripple/DualRail/ScalarCubic.lean` (scalar cubic case, 0 sorry / 0 axiom)
  - `Ripple/DualRail/ScalarQuintic.lean` (scalar quintic case, 0 sorry / 0 axiom)
  - `notes/constant-annihilation-UCNC25.tex` (research note, this is its
    Lean counterpart)
-/

import Ripple.DualRail.ConstantAnnihilation
import Ripple.Core.ODEGlobal
import Ripple.Core.ZeroInitPositivity
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Basic

namespace Ripple
namespace DualRail

open MvPolynomial

/-! ## Absolute polynomial

`absMv q` replaces every coefficient of `q` with its absolute value. It is
idempotent on polynomials whose coefficients are already non-negative, and
satisfies `posPart q + negPart q = absMv q` as polynomials. -/

/-- Polynomial obtained from `q` by replacing each coefficient with its
absolute value. -/
noncomputable def absMv {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  q.support.sum (fun s => monomial s |q.coeff s|)

/-- Coefficient specification for `absMv`. -/
theorem absMv_coeff {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ ℚ) (t : σ →₀ ℕ) :
    (absMv q).coeff t = |q.coeff t| := by
  classical
  unfold absMv
  rw [MvPolynomial.coeff_sum]
  by_cases h : q.coeff t = 0
  · -- Both sides are 0.
    rw [h, abs_zero]
    apply Finset.sum_eq_zero
    intro s hs
    rw [MvPolynomial.coeff_monomial]
    split_ifs with heq
    · -- s = t but s ∈ support means q.coeff s ≠ 0, contradiction with h via heq.
      exfalso
      have hs_ne : q.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
      rw [heq] at hs_ne
      exact hs_ne h
    · rfl
  · -- t ∈ q.support, sum reduces to the t-summand.
    have ht_mem : t ∈ q.support := MvPolynomial.mem_support_iff.mpr h
    rw [Finset.sum_eq_single t]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro s _ hne
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · intro hnot; exact absurd ht_mem hnot

/-- Coefficients of `absMv q` are non-negative. -/
theorem absMv_coeff_nonneg {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ ℚ) (t : σ →₀ ℕ) :
    0 ≤ (absMv q).coeff t := by
  rw [absMv_coeff]; exact abs_nonneg _

/-- Decomposition: `posPart q + negPart q = absMv q`. -/
theorem posPart_add_negPart {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ ℚ) :
    posPart q + negPart q = absMv q := by
  classical
  ext t
  rw [MvPolynomial.coeff_add, posPart_coeff_spec, negPart_coeff_spec, absMv_coeff]
  rcases lt_trichotomy (q.coeff t) 0 with h | h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add, abs_of_neg h]
  · rw [h, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0), abs_zero, add_zero]
  · rw [if_pos h, if_neg (not_lt.mpr h.le), abs_of_pos h, add_zero]

/-- Evaluating `absMv q` at non-negative input gives a non-negative result. -/
theorem absMv_eval_nonneg {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ ℚ) (x : σ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (absMv q).eval₂ (Rat.castHom ℝ) x := by
  classical
  unfold absMv
  rw [MvPolynomial.eval₂_sum]
  refine Finset.sum_nonneg ?_
  intro s _
  rw [MvPolynomial.eval₂_monomial]
  have h1 : (0 : ℝ) ≤ (Rat.castHom ℝ) |q.coeff s| := by
    have : (0 : ℚ) ≤ |q.coeff s| := abs_nonneg _
    have := (Rat.cast_nonneg (K := ℝ)).mpr this
    simpa using this
  have h2 : (0 : ℝ) ≤ s.prod (fun n e => x n ^ e) := by
    apply Finset.prod_nonneg
    intro i _
    exact pow_nonneg (hx i) _
  exact mul_nonneg h1 h2

/-! ## Monotone evaluation bound

We work directly with `absMv (dualRailHom n p_i)` evaluated at the constant
state `2β·𝟙`, avoiding a polynomial-level identity between
`absMv ∘ dualRailHom` and a "σ-rail" hom. The key observation: for any
polynomial with non-negative coefficients, evaluation at non-negative input
is monotone in the input. Combined with `posPart_add_negPart`, this gives

   p̂_i⁺(u,v) + p̂_i⁻(u,v) ≤ M_i

on the box `0 ≤ u_j, v_j ≤ 2β` where
   M_i := absMv (dualRailHom n p_i) evaluated at the constant `2β`.

`M_i` plays the role of `|p_i|(2β, …, 2β)` in the research note. -/

/-- Evaluation of a polynomial whose coefficients are all non-negative is
monotone in non-negative input. -/
theorem nonneg_coeff_eval₂_mono {σ : Type*} [DecidableEq σ] [Fintype σ]
    (p : MvPolynomial σ ℚ) (h_nn : ∀ s, 0 ≤ p.coeff s)
    {w w' : σ → ℝ} (hw : ∀ k, 0 ≤ w k) (hle : ∀ k, w k ≤ w' k) :
    p.eval₂ (Rat.castHom ℝ) w ≤ p.eval₂ (Rat.castHom ℝ) w' := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  apply Finset.sum_le_sum
  intro s _
  have hcoeff_nn : (0 : ℝ) ≤ (Rat.castHom ℝ) (p.coeff s) := by
    have := (Rat.cast_nonneg (K := ℝ)).mpr (h_nn s)
    simpa using this
  have hw'_nn : ∀ k, 0 ≤ w' k := fun k => le_trans (hw k) (hle k)
  have h_prod_nn : (0 : ℝ) ≤ ∏ i ∈ s.support, w i ^ s i := by
    apply Finset.prod_nonneg
    intro i _; exact pow_nonneg (hw i) _
  have h_prod_le :
      ∏ i ∈ s.support, w i ^ s i ≤ ∏ i ∈ s.support, w' i ^ s i := by
    apply Finset.prod_le_prod
    · intro i _; exact pow_nonneg (hw i) _
    · intro i _; exact pow_le_pow_left₀ (hw i) (hle i) _
  exact mul_le_mul_of_nonneg_left h_prod_le hcoeff_nn

/-! ## The boundedness threshold (working definitions) -/

/-- Per-component upper bound on `(p̂_i⁺ + p̂_i⁻)(u,v)` over the box
`0 ≤ u_j, v_j ≤ 2β`. By `posPart_add_negPart` and monotonicity, this equals
the evaluation of `absMv (dualRailHom n p_i)` at the constant `2β`. -/
noncomputable def boxAbsBound (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (β : ℝ) (i : Fin n) : ℝ :=
  (absMv (dualRailHom n (p i))).eval₂ (Rat.castHom ℝ) (fun _ => 2 * β)

/-- `M_i ≥ 0` for every `i`. -/
theorem boxAbsBound_nonneg (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) {β : ℝ} (hβ : 0 ≤ β) (i : Fin n) :
    0 ≤ boxAbsBound n p β i := by
  unfold boxAbsBound
  apply absMv_eval_nonneg
  intro _; linarith

/-- **Per-component σ-drift bound.** On the box `0 ≤ w_k ≤ 2β`,
`p̂_i⁺(w) + p̂_i⁻(w) ≤ M_i := boxAbsBound n p β i`. -/
theorem posPart_add_negPart_eval_le (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (β : ℝ) (i : Fin n)
    (w : Fin (2 * n) → ℝ) (hw_nn : ∀ k, 0 ≤ w k)
    (hw_le : ∀ k, w k ≤ 2 * β) :
    (posPart (dualRailHom n (p i))).eval₂ (Rat.castHom ℝ) w
      + (negPart (dualRailHom n (p i))).eval₂ (Rat.castHom ℝ) w
      ≤ boxAbsBound n p β i := by
  classical
  -- Step 1: posPart + negPart eval₂ at w = absMv(dualRailHom (p i)) eval₂ at w.
  have h_sum_eq : (posPart (dualRailHom n (p i))).eval₂ (Rat.castHom ℝ) w
        + (negPart (dualRailHom n (p i))).eval₂ (Rat.castHom ℝ) w
      = (absMv (dualRailHom n (p i))).eval₂ (Rat.castHom ℝ) w := by
    rw [← MvPolynomial.eval₂_add, posPart_add_negPart]
  rw [h_sum_eq]
  -- Step 2: absMv has all-non-negative coefficients. Monotone evaluation
  -- gives (absMv ...).eval at w ≤ (absMv ...).eval at constant `2β`.
  unfold boxAbsBound
  apply nonneg_coeff_eval₂_mono
  · intro s; exact absMv_coeff_nonneg _ s
  · exact hw_nn
  · exact hw_le

/-! ## The boundedness threshold

For a bounded GPAC `p` with `|y_i(t)| ≤ β`, define
   k_⋆(p, β) := max_i 2 · |p_i|(2β, …, 2β) / (3 β²).
For `k > k_⋆ + 1` (or any explicit positive offset) the box
   B_β := { (u, v) ≥ 0 : σ_i ≤ 2β, |u_i − v_i| ≤ β ∀i }
is forward-invariant under the constant-k uniform dual-rail flow.

We package the threshold as a function returning `ℚ` so it plugs directly
into `constantAnnihilationDualRail`. -/

/-- The constant `M_i := |p_i|(2β, …, 2β)` from the threshold formula. -/
noncomputable def absPolyAtTwoBeta (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) (β : ℝ) (i : Fin n) : ℝ :=
  (absMv (p i)).eval₂ (Rat.castHom ℝ) (fun _ => 2 * β)

/-- `M_i ≥ 0` for every `i`. -/
theorem absPolyAtTwoBeta_nonneg (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) ℚ) {β : ℝ} (hβ : 0 ≤ β) (i : Fin n) :
    0 ≤ absPolyAtTwoBeta n p β i := by
  unfold absPolyAtTwoBeta
  apply absMv_eval_nonneg
  intro _; linarith

/-! ## Row formulas for `constantAnnihilationDualRail`

The PolyPIVP indexes rows by a single `K : Fin (2 * n)`; even rows hold `u_i`,
odd rows hold `v_i`. We package the per-row evaluation as two clean lemmas. -/

/-- The u-row drift evaluated at `w` equals
`(dualRailPosPart n p i).eval₂ w − k · w(2i) · w(2i+1)`. -/
theorem evalField_u (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ)
    (w : Fin (2 * n) → ℝ) (i : Fin n) :
    (constantAnnihilationDualRail n p k).evalField w
        ⟨2 * i.val, by have := i.isLt; omega⟩
      = (dualRailPosPart n p i).eval₂ (Rat.castHom ℝ) w
        - (k : ℝ) * w ⟨2 * i.val, by have := i.isLt; omega⟩
            * w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  unfold constantAnnihilationDualRail PolyPIVP.evalField
  dsimp only
  have hdiv : (2 * i.val) / 2 = i.val := by omega
  have hmod : (2 * i.val) % 2 = 0 := by omega
  simp only [hdiv, hmod, decide_true, if_true]
  have heq : (⟨i.val, by have := i.isLt; omega⟩ : Fin n) = i := Fin.eta i _
  rw [heq]
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, eq_ratCast]

/-- The v-row drift evaluated at `w` equals
`(dualRailNegPart n p i).eval₂ w − k · w(2i) · w(2i+1)`. -/
theorem evalField_v (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ)
    (w : Fin (2 * n) → ℝ) (i : Fin n) :
    (constantAnnihilationDualRail n p k).evalField w
        ⟨2 * i.val + 1, by have := i.isLt; omega⟩
      = (dualRailNegPart n p i).eval₂ (Rat.castHom ℝ) w
        - (k : ℝ) * w ⟨2 * i.val, by have := i.isLt; omega⟩
            * w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  unfold constantAnnihilationDualRail PolyPIVP.evalField
  dsimp only
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  have hmod_ne : (2 * i.val + 1) % 2 ≠ 0 := by omega
  have h_is_u : decide ((2 * i.val + 1) % 2 = 0) = false := decide_eq_false hmod_ne
  have heq : (⟨i.val, by have := i.isLt; omega⟩ : Fin n) = i := Fin.eta i _
  simp only [hdiv, h_is_u, Bool.false_eq_true, if_false, heq,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, eq_ratCast]

/-- **n-dim drift-difference identity.** For every `i`,
`(u-row drift) − (v-row drift) = p_i(y₁, …, y_n)` where `y_j = w(2j) − w(2j+1)`.
The annihilation term `k·u_i·v_i` cancels in the difference, so the dual-rail
invariant `u_i − v_i = y_i` is exactly preserved by the ODE. -/
theorem constantAnnihilationDualRail_drift_diff (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ)
    (w : Fin (2 * n) → ℝ) (i : Fin n) :
    (constantAnnihilationDualRail n p k).evalField w
        ⟨2 * i.val, by have := i.isLt; omega⟩
      - (constantAnnihilationDualRail n p k).evalField w
          ⟨2 * i.val + 1, by have := i.isLt; omega⟩
      = (p i).eval₂ (Rat.castHom ℝ)
        (fun j : Fin n =>
          w ⟨2 * j.val, by have := j.isLt; omega⟩
            - w ⟨2 * j.val + 1, by have := j.isLt; omega⟩) := by
  rw [evalField_u, evalField_v]
  have hsub := dualRailPos_sub_dualRailNeg_eval n p i w
  linarith [hsub]

/-- **n-dim drift-sum bound (box version).** On the box
`{0 ≤ w_K ≤ 2β}`, the sum of the u_i and v_i drifts is bounded by
`M_i − 2k·w(2i)·w(2i+1)` where `M_i = boxAbsBound n p β i`. This is the
σ-drift inequality used in Nagumo's box-invariance argument: at the upper
face `σ_i = 2β`, we have `w(2i) + w(2i+1) = 2β`, hence `w(2i)·w(2i+1) ≥
β² − ¼·y_i² ≥ ¾·β²` (using `|y_i| ≤ β`), so the inward-pointing condition
`σ_i' < 0` reduces to `M_i < (3/2)·k·β²`, i.e. `k > k_⋆ := 2 M_i/(3β²)`. -/
theorem constantAnnihilationDualRail_drift_sum_le (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) (β : ℝ)
    (w : Fin (2 * n) → ℝ) (hw_nn : ∀ K, 0 ≤ w K) (hw_le : ∀ K, w K ≤ 2 * β)
    (i : Fin n) :
    (constantAnnihilationDualRail n p k).evalField w
        ⟨2 * i.val, by have := i.isLt; omega⟩
      + (constantAnnihilationDualRail n p k).evalField w
          ⟨2 * i.val + 1, by have := i.isLt; omega⟩
      ≤ boxAbsBound n p β i
        - 2 * (k : ℝ) * w ⟨2 * i.val, by have := i.isLt; omega⟩
            * w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  rw [evalField_u, evalField_v]
  have hbnd := posPart_add_negPart_eval_le n p β i w hw_nn hw_le
  -- LHS = (p̂⁺.eval w − k·u·v) + (p̂⁻.eval w − k·u·v) = (p̂⁺ + p̂⁻).eval w − 2 k u v
  -- RHS = M_i − 2 k u v
  show (dualRailPosPart n p i).eval₂ (Rat.castHom ℝ) w
        - (k : ℝ) * w ⟨2 * i.val, _⟩ * w ⟨2 * i.val + 1, _⟩
      + ((dualRailNegPart n p i).eval₂ (Rat.castHom ℝ) w
        - (k : ℝ) * w ⟨2 * i.val, _⟩ * w ⟨2 * i.val + 1, _⟩)
      ≤ _
  unfold dualRailPosPart dualRailNegPart
  linarith [hbnd]

/-! ## σ-face algebraic identity

Key inequality powering the upper-face Nagumo argument: on the face
`σ_i = u_i + v_i = 2β` with the GPAC dual-rail invariant
`y_i = u_i − v_i ∈ [-β, β]`, we have `u_i · v_i ≥ (3/4) β²`.

Proof: from `4 u v = (u + v)² − (u − v)² = 4β² − y²` and `y² ≤ β²`,
`4 u v ≥ 4β² − β² = 3 β²`. -/

/-- **σ-corner lemma.** If `u + v = 2β` and `|u − v| ≤ β`, then
`u · v ≥ (3/4) β²`. This is the geometric core of the upper-face
Nagumo inequality. -/
theorem uv_bound_at_sigma_face (u v β : ℝ)
    (hsum : u + v = 2 * β) (hdiff : |u - v| ≤ β) :
    u * v ≥ (3 / 4) * β ^ 2 := by
  -- 4 u v = (u + v)² − (u − v)² = (2β)² − (u − v)² ≥ 4β² − β² = 3β².
  have h4uv : 4 * (u * v) = (u + v) ^ 2 - (u - v) ^ 2 := by ring
  have hsq : (u - v) ^ 2 ≤ β ^ 2 := by
    have := sq_abs (u - v)
    have h := sq_le_sq' (a := u - v) (b := β) (by linarith [neg_abs_le (u - v)])
      (le_of_abs_le hdiff)
    linarith [h]
  rw [hsum] at h4uv
  -- 4uv = 4β² − (u-v)² ≥ 4β² − β² = 3β².
  have h_sigma_sq : (2 * β) ^ 2 = 4 * β ^ 2 := by ring
  linarith [h4uv, hsq, h_sigma_sq]

/-! ## The boundedness threshold (rational witness) -/

/-- **Threshold value (real-valued).** `k_⋆(p, β) := max_i 2·M_i / (3β²)`
where `M_i = boxAbsBound n p β i`. We use `Finset.max'` over `Fin n` (which
is non-empty because `[NeZero n]` holds). -/
noncomputable def thresholdK (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (β : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' (Finset.univ_nonempty)
    (fun i => 2 * boxAbsBound n p β i / (3 * β ^ 2))

/-- The threshold dominates each per-component ratio. -/
theorem thresholdK_ge (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (β : ℝ) (i : Fin n) :
    2 * boxAbsBound n p β i / (3 * β ^ 2) ≤ thresholdK n p β := by
  unfold thresholdK
  exact Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => 2 * boxAbsBound n p β j / (3 * β ^ 2))
    (Finset.mem_univ i)

/-- **Upper-face σ-drift inequality.** If `k > thresholdK n p β` and
`β > 0`, then on the face `w(2i) + w(2i+1) = 2β` with the dual-rail
constraint `|w(2i) − w(2i+1)| ≤ β` and the box `0 ≤ w_K ≤ 2β`, the
σ-drift `(u_i' + v_i')` is *strictly negative*. This is exactly the
Nagumo inward-pointing condition at the upper face. -/
theorem sigma_drift_strict_neg_at_upper_face (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) (β : ℝ)
    (hβ : 0 < β) (hk : (thresholdK n p β : ℝ) < (k : ℝ))
    (w : Fin (2 * n) → ℝ) (hw_nn : ∀ K, 0 ≤ w K) (hw_le : ∀ K, w K ≤ 2 * β)
    (i : Fin n)
    (hface : w ⟨2 * i.val, by have := i.isLt; omega⟩
              + w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ = 2 * β)
    (hdiff : |w ⟨2 * i.val, by have := i.isLt; omega⟩
              - w ⟨2 * i.val + 1, by have := i.isLt; omega⟩| ≤ β) :
    (constantAnnihilationDualRail n p k).evalField w
        ⟨2 * i.val, by have := i.isLt; omega⟩
      + (constantAnnihilationDualRail n p k).evalField w
          ⟨2 * i.val + 1, by have := i.isLt; omega⟩ < 0 := by
  -- Step 1: σ-drift sum bound.
  have hsum_le := constantAnnihilationDualRail_drift_sum_le n p k β w hw_nn hw_le i
  -- Step 2: u·v lower bound at the face.
  have huv := uv_bound_at_sigma_face _ _ _ hface hdiff
  -- Step 3: ratio bound: M_i / (3β²/2) < k, i.e. M_i < (3/2) k β².
  have hβ2 : (0 : ℝ) < β ^ 2 := pow_pos hβ 2
  have hβ2' : (0 : ℝ) < 3 * β ^ 2 := by linarith
  have hMle : 2 * boxAbsBound n p β i ≤ thresholdK n p β * (3 * β ^ 2) := by
    have hr := thresholdK_ge n p β i
    -- hr : 2 * M_i / (3β²) ≤ thresholdK
    have : 2 * boxAbsBound n p β i = (2 * boxAbsBound n p β i / (3 * β ^ 2)) * (3 * β ^ 2) := by
      field_simp
    rw [this]
    exact (mul_le_mul_of_nonneg_right hr (le_of_lt hβ2'))
  -- Step 4: combine.
  -- LHS = u' + v' ≤ M_i - 2k·u·v ≤ thresholdK·(3β²) - 2k·(3β²/4) = (3β²)·(thresholdK - k/2)
  -- For LHS < 0 we need thresholdK < k/2 ... wait that's not quite right.
  --
  -- Actually: M_i ≤ thresholdK · (3β²/2) (from hMle dividing by 2)
  --         u·v ≥ 3β²/4 (from huv)
  -- So u'+v' ≤ M_i - 2k·u·v ≤ thresholdK·(3β²/2) - 2k·(3β²/4) = (3β²/2)·(thresholdK - k)
  -- and thresholdK - k < 0 from hk, so LHS < 0.
  have hM_half : boxAbsBound n p β i ≤ thresholdK n p β * (3 * β ^ 2) / 2 := by
    linarith [hMle]
  have hkuv : 2 * (k : ℝ) * w ⟨2 * i.val, by have := i.isLt; omega⟩
                * w ⟨2 * i.val + 1, by have := i.isLt; omega⟩
              ≥ 2 * (k : ℝ) * ((3 / 4) * β ^ 2) := by
    have hMnn : (0 : ℝ) ≤ 2 * boxAbsBound n p β i := by
      have := boxAbsBound_nonneg n p hβ.le i; linarith
    have hRatio_nn : (0 : ℝ) ≤ 2 * boxAbsBound n p β i / (3 * β ^ 2) :=
      div_nonneg hMnn (le_of_lt hβ2')
    have hThr_nn : (0 : ℝ) ≤ thresholdK n p β :=
      le_trans hRatio_nn (thresholdK_ge n p β i)
    have hk_pos : 0 < (k : ℝ) := lt_of_le_of_lt hThr_nn hk
    have h2k_pos : 0 < 2 * (k : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left huv (le_of_lt h2k_pos)
    -- hmul : 2k · ((3/4)β²) ≤ 2k · (u v); rearrange.
    have hrew : 2 * (k : ℝ) * w ⟨2 * i.val, by have := i.isLt; omega⟩
                  * w ⟨2 * i.val + 1, by have := i.isLt; omega⟩
                = 2 * (k : ℝ) * (w ⟨2 * i.val, by have := i.isLt; omega⟩
                    * w ⟨2 * i.val + 1, by have := i.isLt; omega⟩) := by ring
    rw [hrew]; linarith [hmul]
  -- Combine: LHS ≤ M_i - 2k·u·v ≤ thresholdK·(3β²/2) - 2k·(3β²/4)
  --                              = (3β²/2)·(thresholdK - k) < 0.
  have h_combined : (constantAnnihilationDualRail n p k).evalField w
        ⟨2 * i.val, by have := i.isLt; omega⟩
      + (constantAnnihilationDualRail n p k).evalField w
          ⟨2 * i.val + 1, by have := i.isLt; omega⟩
      ≤ thresholdK n p β * (3 * β ^ 2) / 2
        - 2 * (k : ℝ) * ((3 / 4) * β ^ 2) := by
    linarith [hsum_le, hM_half, hkuv]
  have h_neg : thresholdK n p β * (3 * β ^ 2) / 2
        - 2 * (k : ℝ) * ((3 / 4) * β ^ 2) < 0 := by
    -- = (3β²/2)·(thresholdK - k); thresholdK < k.
    have : thresholdK n p β * (3 * β ^ 2) / 2 - 2 * (k : ℝ) * ((3 / 4) * β ^ 2)
        = (3 * β ^ 2 / 2) * (thresholdK n p β - (k : ℝ)) := by ring
    rw [this]
    apply mul_neg_of_pos_of_neg
    · linarith
    · linarith
  linarith [h_combined, h_neg]

/-! ## The main theorem (statement; proof is the file's WIP target)

`ConstantAnnihilationBounded` from `ConstantAnnihilation.lean` is a
`Prop`; the theorem below says it holds.

**Proof outline (per the research note, rev. 2026-04-26).** Given a
bounded GPAC `(p, ySol, β)`:

1. Pick `k > thresholdK n p β + 1` (rational, positive).
2. Apply Picard-Lindelöf to get a maximal `ûSol` solving the constant-k
   uniform dual-rail ODE with `ûSol 0 = 0`.
3. **Lower face (positivity).** At any face `w(K) = 0` with `K = 2i`,
   the drift is `p̂_i⁺(w) − 0 ≥ 0` (since `p̂_i⁺` has non-negative
   coefficients). Same for `K = 2i+1` via `p̂_i⁻`. Nagumo's theorem
   gives `ûSol t K ≥ 0`.
4. **Upper face (σ-bound).** At any face `σ_i = 2β`, by Cauchy-Schwarz
   on `(u_i + v_i)² = (2β)²` and `|u_i − v_i| ≤ β`, we get
   `u_i v_i ≥ (3/4)β²`. Then `σ_i' ≤ M_i − 2k·u_i v_i ≤ M_i − (3/2)k β²`,
   which is negative once `k > 2M_i/(3β²) = thresholdK`. Nagumo gives
   `σ_i ≤ 2β`, hence each `u_i, v_i ≤ 2β`.
5. **Dual-rail identity.** From `drift_diff` the difference
   `u_i − v_i` satisfies `d/dt(u_i − v_i) = p_i(u_1 − v_1, …, u_n − v_n)`
   with `(u_i − v_i)(0) = 0 = y_i(0)` by the GPAC hypothesis (after
   normalizing `y₀ = 0`). ODE uniqueness then gives `u_i − v_i = y_i`. -/
/-- **n = 0 base case.** With zero variables, the dual-rail system is empty;
the conjecture's universal/existential statements are all vacuous. -/
theorem constantAnnihilation_bounded_zero
    (p : Fin 0 → MvPolynomial (Fin 0) ℚ) (y₀ : Fin 0 → ℚ)
    (ySol : ℝ → Fin 0 → ℝ) (β : ℝ) (_hBd : OriginalBounded p y₀ ySol β) :
    ∃ (k : ℚ), 0 < k ∧
      ∃ (ûSol : ℝ → Fin (2 * 0) → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ B) ∧
        (∀ t ≥ (0 : ℝ), ∀ i : Fin 0,
          ûSol t ⟨2 * i.val, by omega⟩ - ûSol t ⟨2 * i.val + 1, by omega⟩
            = ySol t i) := by
  refine ⟨1, by norm_num, fun _ _ => 0, 1, by norm_num, ?_, ?_⟩
  · intro _ _ K
    -- K : Fin 0 has no inhabitants.
    exact K.elim0
  · intro _ _ i
    exact i.elim0

/-! ## CRN decomposition for the constant-annihilation dual-rail system

For row `K = 2i` (u-row), the field `p̂_i⁺ − k·X(2i)·X(2i+1)` factors as
`prod − degr · X_K` with `prod = p̂_i⁺` and `degr = (C k)·X(2i+1)`.

For row `K = 2i+1` (v-row), the field `p̂_i⁻ − k·X(2i)·X(2i+1)` factors as
`prod = p̂_i⁻` and `degr = (C k)·X(2i)`.

Non-negativity of all coefficients is immediate from
`posPart_coeff_nonneg`/`negPart_coeff_nonneg` (for the prod side), and
from `0 ≤ k` plus `coeff_X_nonneg` (for the degr side). -/

/-- Coefficient-level non-negativity for the bare variable `X j`. -/
private lemma cag_coeff_X_nonneg {d : ℕ} (j : Fin d) (σ : Fin d →₀ ℕ) :
    0 ≤ ((MvPolynomial.X j : MvPolynomial (Fin d) ℚ)).coeff σ := by
  classical
  rw [MvPolynomial.coeff_X]
  split_ifs <;> norm_num

/-- Coefficient-level non-negativity for products. -/
private lemma cag_coeff_mul_nonneg {d : ℕ} (p q : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) (hq : ∀ σ, 0 ≤ q.coeff σ) :
    ∀ σ, 0 ≤ (p * q).coeff σ := by
  classical
  intro σ
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro ⟨a, b⟩ _
  exact mul_nonneg (hp a) (hq b)

/-- Coefficient-level non-negativity for `C k` when `0 ≤ k`. -/
private lemma cag_coeff_C_nonneg {d : ℕ} (k : ℚ) (hk_nn : 0 ≤ k)
    (σ : Fin d →₀ ℕ) :
    0 ≤ ((MvPolynomial.C k : MvPolynomial (Fin d) ℚ)).coeff σ := by
  classical
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hk_nn
  · norm_num

/-- Production polynomial for the constant-annihilation dual-rail decomp. -/
private noncomputable def cag_prod (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (K : Fin (2 * n)) :
    MvPolynomial (Fin (2 * n)) ℚ :=
  if K.val % 2 = 0 then
    dualRailPosPart n p ⟨K.val / 2, by have := K.isLt; omega⟩
  else
    dualRailNegPart n p ⟨K.val / 2, by have := K.isLt; omega⟩

/-- Degradation polynomial: `C k` times the partner-rail `X` variable. -/
private noncomputable def cag_degr (n : ℕ) [NeZero n] (k : ℚ)
    (K : Fin (2 * n)) : MvPolynomial (Fin (2 * n)) ℚ :=
  if K.val % 2 = 0 then
    MvPolynomial.C (σ := Fin (2 * n)) k *
      MvPolynomial.X ⟨2 * (K.val / 2) + 1, by have := K.isLt; omega⟩
  else
    MvPolynomial.C (σ := Fin (2 * n)) k *
      MvPolynomial.X ⟨2 * (K.val / 2), by have := K.isLt; omega⟩

private lemma cag_prod_nonneg (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (K : Fin (2 * n))
    (σ : Fin (2 * n) →₀ ℕ) :
    0 ≤ (cag_prod n p K).coeff σ := by
  unfold cag_prod
  split_ifs with _h
  · exact posPart_coeff_nonneg _ σ
  · exact negPart_coeff_nonneg _ σ

private lemma cag_degr_nonneg (n : ℕ) [NeZero n] (k : ℚ) (hk_nn : 0 ≤ k)
    (K : Fin (2 * n)) (σ : Fin (2 * n) →₀ ℕ) :
    0 ≤ (cag_degr n k K).coeff σ := by
  unfold cag_degr
  split_ifs with _h
  · exact cag_coeff_mul_nonneg _ _ (cag_coeff_C_nonneg k hk_nn)
      (cag_coeff_X_nonneg _) σ
  · exact cag_coeff_mul_nonneg _ _ (cag_coeff_C_nonneg k hk_nn)
      (cag_coeff_X_nonneg _) σ

private lemma cag_field_eq (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) (K : Fin (2 * n)) :
    (constantAnnihilationDualRail n p k).field K =
      cag_prod n p K - cag_degr n k K * MvPolynomial.X K := by
  unfold cag_prod cag_degr
  by_cases h : K.val % 2 = 0
  · have hKv : K.val = 2 * (K.val / 2) := by omega
    have hKX : (MvPolynomial.X K : MvPolynomial (Fin (2 * n)) ℚ)
        = MvPolynomial.X ⟨2 * (K.val / 2), by have := K.isLt; omega⟩ := by
      congr 1; exact Fin.ext hKv
    show (if ((K.val % 2 = 0 : Bool)) then _ else _) =
        (if K.val % 2 = 0 then _ else _) -
        (if K.val % 2 = 0 then _ else _) * MvPolynomial.X K
    have hBool : ((K.val % 2 = 0 : Bool)) = true := by simp [h]
    simp only [hBool, h, if_true, decide_true]
    rw [hKX]
    ring
  · have hKv : K.val = 2 * (K.val / 2) + 1 := by omega
    have hKX : (MvPolynomial.X K : MvPolynomial (Fin (2 * n)) ℚ)
        = MvPolynomial.X ⟨2 * (K.val / 2) + 1, by have := K.isLt; omega⟩ := by
      congr 1; exact Fin.ext hKv
    show (if ((K.val % 2 = 0 : Bool)) then _ else _) =
        (if K.val % 2 = 0 then _ else _) -
        (if K.val % 2 = 0 then _ else _) * MvPolynomial.X K
    have hBool : ((K.val % 2 = 0 : Bool)) = false := by simp [h]
    simp only [hBool, h, if_false, decide_false, Bool.false_eq_true]
    rw [hKX]

noncomputable def constantAnnihilationDualRail_pcd (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) (hk_nn : 0 ≤ k) :
    PolyCRNDecomposition (2 * n) (constantAnnihilationDualRail n p k) where
  prod := cag_prod n p
  degr := cag_degr n k
  prod_nonneg := cag_prod_nonneg n p
  degr_nonneg := cag_degr_nonneg n k hk_nn
  init_nonneg := by intro K; change (0 : ℚ) ≤ 0; exact le_refl _
  field_eq := cag_field_eq n p k

/-! ### Skeleton for the n ≥ 1 case

The remaining work splits into four analytic / structural sub-lemmas which
together close `constantAnnihilation_bounded_pos`. Each is stated as a
named lemma with `sorry` so the modular structure is visible: closing them
in turn closes the main theorem with no further architectural work.

1. `posK_witness` — produce a rational `k` strictly above `thresholdK n p β`
   along with positivity. (Largely arithmetic.)
2. `posK_picard` — Picard–Lindelöf existence of a global solution `ûSol`
   to the constant-`k` uniform dual-rail ODE, with the dual-rail-split
   initial condition derived from `y₀`. Requires
   `locally_lipschitz_bounded_global_ode_proved_continuous` plus a Lipschitz
   bound for the polynomial right-hand side over the box `[0, 2β]^{2n}`.
3. `posK_boxBound` — Nagumo box invariance: if `ûSol` is the solution from
   `posK_picard`, then `0 ≤ ûSol t K ≤ 2β` for all `t ≥ 0` and all `K`.
   The lower face uses `dualRailPosPart_eval_nonneg` /
   `dualRailNegPart_eval_nonneg`; the upper face uses
   `sigma_drift_strict_neg_at_upper_face`.
4. `posK_identity` — Dual-rail identity: `(u_i − v_i)(t) = ySol t i`. Uses
   `constantAnnihilationDualRail_drift_diff` (the difference satisfies the
   original GPAC) plus ODE uniqueness against `ySol` from
   `OriginalBounded`. -/

/-- Sub-lemma 1: rational threshold witness above `thresholdK`. -/
lemma posK_witness (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (β : ℝ) (_hβ : 0 < β) :
    ∃ (k : ℚ), 0 < k ∧ thresholdK n p β < (k : ℝ) := by
  -- Take any rational strictly greater than `thresholdK n p β`.
  obtain ⟨q, hq⟩ := exists_rat_gt (max (thresholdK n p β) 0 + 1)
  refine ⟨q, ?_, ?_⟩
  · -- `q > max(thresholdK, 0) + 1 ≥ 0 + 1 = 1 > 0`.
    have h1 : (1 : ℝ) ≤ max (thresholdK n p β) 0 + 1 := by
      have : (0 : ℝ) ≤ max (thresholdK n p β) 0 := le_max_right _ _
      linarith
    have : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (by linarith) hq.le
    exact_mod_cast this
  · -- `thresholdK ≤ max(thresholdK, 0) < max(thresholdK, 0) + 1 < q`.
    have h2 : thresholdK n p β ≤ max (thresholdK n p β) 0 := le_max_left _ _
    linarith

/-! ### Sub-lemma 2 (core): Nagumo box invariance against the bounded GPAC

For any candidate solution `y` of the constant-`k` uniform dual-rail ODE
on `Ico 0 T` whose initial condition is the dual-rail split of `y₀`,
`y` stays in the box `[0, 2β]^{2n}` on `Ico 0 T`. This is the unique
analytic core of UCNC25 Problem 1's general n-dim case, split into three
sub-lemmas: `posK_invariant_nonneg`, `posK_invariant_diffBound`, and
`posK_invariant_sigmaBound`. -/

/-- Componentwise non-negativity arm of `posK_invariant`. Closed via
`crn_local_nonneg` on the CRN decomposition `constantAnnihilationDualRail_pcd`. -/
lemma posK_invariant_nonneg (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ) (k : ℚ)
    (hk_pos : 0 < k) (T : ℝ) (hT : 0 < T) (y : ℝ → Fin (2 * n) → ℝ)
    (hy_init : y 0 = (fun K =>
      if K.val % 2 = 0
        then (max ((y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0)
        else (max (-(y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0)))
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((constantAnnihilationDualRail n p k).evalField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ K, 0 ≤ y t K := by
  have hk_nn : (0 : ℚ) ≤ k := le_of_lt hk_pos
  have h_crn : IsCRNImplementable (2 * n)
      (constantAnnihilationDualRail n p k).toPIVP.field :=
    (constantAnnihilationDualRail_pcd n p k hk_nn).toIsCRNImplementable
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x z : Fin (2 * n) → ℝ,
      ‖x‖ ≤ R → ‖z‖ ≤ R →
      ‖(constantAnnihilationDualRail n p k).evalField x
          - (constantAnnihilationDualRail n p k).evalField z‖
        ≤ L * ‖x - z‖ :=
    Ripple.polyPIVP_field_locally_lipschitz _
  have h_init_nn : ∀ K, 0 ≤ y 0 K := by
    intro K0
    have hK := congrFun hy_init K0
    rw [hK]
    split_ifs <;> exact le_max_right _ _
  have h_field_eq : (constantAnnihilationDualRail n p k).toPIVP.field
      = fun x => (constantAnnihilationDualRail n p k).evalField x := by
    funext x; rfl
  have h_ode' : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((constantAnnihilationDualRail n p k).toPIVP.field (y s)) s := by
    intro s hs
    rw [h_field_eq]
    exact h_deriv s hs
  exact crn_local_nonneg h_crn h_lip T hT y h_init_nn h_ode'

/-- Diff-bound arm: `|u_i(t) - v_i(t)| ≤ β` from ODE uniqueness against
`ySol`. The candidate `z(t) i := y t (2i) - y t (2i+1)` satisfies the
original GPAC and matches `ySol(0)`, so `z = ySol` on each compact
subinterval of `Ico 0 T`. Combining with `OriginalBounded` gives the bound. -/
lemma posK_invariant_diffBound (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β)
    (k : ℚ) (hk_pos : 0 < k) (T : ℝ) (hT : 0 < T) (y : ℝ → Fin (2 * n) → ℝ)
    (hy_init : y 0 = (fun K =>
      if K.val % 2 = 0
        then (max ((y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0)
        else (max (-(y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0)))
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((constantAnnihilationDualRail n p k).evalField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin n,
      |y t ⟨2 * i.val, by have := i.isLt; omega⟩
        - y t ⟨2 * i.val + 1, by have := i.isLt; omega⟩| ≤ β := by
  classical
  have hβ : 0 < β := hBd.1
  have h_ySol_init : ySol 0 = (fun j => (y₀ j : ℝ)) := hBd.2.1
  have h_ySol_deriv := hBd.2.2.1
  have h_ySol_bd := hBd.2.2.2
  -- Define the candidate: z s j = y s (2j) - y s (2j+1).
  set z : ℝ → Fin n → ℝ := fun s j =>
    y s ⟨2 * j.val, by have := j.isLt; omega⟩
      - y s ⟨2 * j.val + 1, by have := j.isLt; omega⟩ with hz_def
  -- Build the original GPAC as a PolyPIVP for the Lipschitz lemma.
  let P : PolyPIVP n :=
    { field := p, init := y₀, output := ⟨0, by have := NeZero.ne n; omega⟩ }
  set F : (Fin n → ℝ) → Fin n → ℝ := P.toPIVP.field with hF_def
  have hF_unfold : ∀ x : Fin n → ℝ,
      F x = (fun i => (p i).eval₂ (Rat.castHom ℝ) x) := by
    intro x; funext i; rfl
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x w : Fin n → ℝ,
      ‖x‖ ≤ R → ‖w‖ ≤ R → ‖F x - F w‖ ≤ L * ‖x - w‖ :=
    Ripple.polyPIVP_field_locally_lipschitz P
  -- z(0) = y₀ (cast to ℝ). max(y₀,0) - max(-y₀,0) = y₀.
  have h_z0 : z 0 = (fun j => (y₀ j : ℝ)) := by
    funext j
    show y 0 ⟨2 * j.val, _⟩ - y 0 ⟨2 * j.val + 1, _⟩ = (y₀ j : ℝ)
    rw [show y 0 = _ from hy_init]
    have hev : (2 * j.val) % 2 = 0 := by omega
    have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
    have hdiv1 : (2 * j.val) / 2 = j.val := by omega
    have hdiv2 : (2 * j.val + 1) / 2 = j.val := by omega
    simp only [hev, hodd, hdiv1, hdiv2, ↓reduceIte]
    have heq1 : (⟨j.val, by have := j.isLt; omega⟩ : Fin n) = j := Fin.eta j _
    rw [heq1]
    by_cases h : 0 ≤ ((y₀ j : ℝ))
    · rw [max_eq_left h, max_eq_right (by linarith : -(y₀ j : ℝ) ≤ 0)]; ring
    · replace h : ((y₀ j : ℝ)) < 0 := lt_of_not_ge h
      rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(y₀ j : ℝ))]; ring
  -- z satisfies the original GPAC on Ico 0 T.
  have h_z_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivAt z (F (z s)) s := by
    intro s hs
    have h := h_deriv s hs
    have hpi := (hasDerivAt_pi (φ := fun u => y u)
      (φ' := (constantAnnihilationDualRail n p k).evalField (y s))).1 h
    rw [hF_unfold]
    apply (hasDerivAt_pi (φ := z)
      (φ' := fun j => (p j).eval₂ (Rat.castHom ℝ) (z s))).2
    intro j
    have hu := hpi ⟨2 * j.val, by have := j.isLt; omega⟩
    have hv := hpi ⟨2 * j.val + 1, by have := j.isLt; omega⟩
    have hdiff := hu.sub hv
    have heq := constantAnnihilationDualRail_drift_diff n p k (y s) j
    rw [heq] at hdiff
    exact hdiff
  -- Main statement: pick t' ∈ Ico 0 T, apply uniqueness on Icc 0 t for some t < T.
  intro t' ht' i
  -- Pick t with t' ≤ t < T.
  have h_lt : t' < T := ht'.2
  have h_t_pos : 0 < (T - t') / 2 := by linarith [ht'.1]
  set t := t' + (T - t') / 2 with ht_def
  have ht_lt_T : t < T := by simp [ht_def]; linarith
  have ht_ge_t' : t' ≤ t := by simp [ht_def]; linarith [h_t_pos.le]
  have ht_pos : (0 : ℝ) < t := by linarith [ht'.1, h_t_pos]
  -- Both z and ySol are continuous on Icc 0 t.
  have h_z_cont : ContinuousOn z (Set.Icc 0 t) := by
    intro s hs
    have hs_in : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht_lt_T⟩
    exact (h_z_deriv s hs_in).continuousAt.continuousWithinAt
  have h_ySol_cont : ContinuousOn ySol (Set.Icc 0 t) := by
    intro s hs
    have hs_pos : 0 ≤ s := hs.1
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro j; exact (h_ySol_deriv s hs_pos j).continuousAt
  -- Get a uniform sup-norm bound M for both on Icc 0 t.
  have h_z_norm_cont : ContinuousOn (fun s => ‖z s‖) (Set.Icc 0 t) :=
    h_z_cont.norm
  have h_ySol_norm_cont : ContinuousOn (fun s => ‖ySol s‖) (Set.Icc 0 t) :=
    h_ySol_cont.norm
  obtain ⟨s_z, _, hs_z_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr ht_pos.le) h_z_norm_cont
  obtain ⟨s_y, _, hs_y_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr ht_pos.le) h_ySol_norm_cont
  set M : ℝ := max (‖z s_z‖) (‖ySol s_y‖) + 1 with hM_def
  have hM_pos : 0 < M := by
    show 0 < max (‖z s_z‖) (‖ySol s_y‖) + 1
    have h1 : 0 ≤ max (‖z s_z‖) (‖ySol s_y‖) :=
      le_max_of_le_left (norm_nonneg _)
    linarith
  have hM_z_bd : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖z s‖ ≤ M := by
    intro s hs
    have h1 : ‖z s‖ ≤ ‖z s_z‖ := hs_z_max hs
    have h2 : ‖z s_z‖ ≤ max (‖z s_z‖) (‖ySol s_y‖) := le_max_left _ _
    show ‖z s‖ ≤ max (‖z s_z‖) (‖ySol s_y‖) + 1
    linarith
  have hM_y_bd : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖ySol s‖ ≤ M := by
    intro s hs
    have h1 : ‖ySol s‖ ≤ ‖ySol s_y‖ := hs_y_max hs
    have h2 : ‖ySol s_y‖ ≤ max (‖z s_z‖) (‖ySol s_y‖) := le_max_right _ _
    show ‖ySol s‖ ≤ max (‖z s_z‖) (‖ySol s_y‖) + 1
    linarith
  -- HasDerivWithinAt forms on Icc 0 t for solutions_agree_on_Icc.
  have h_z_deriv_within : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt z (F (z s)) (Set.Icc 0 t) s := by
    intro s hs
    have hs_in : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht_lt_T⟩
    exact (h_z_deriv s hs_in).hasDerivWithinAt
  have h_ySol_deriv_within : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt ySol (F (ySol s)) (Set.Icc 0 t) s := by
    intro s hs
    have hs_pos : 0 ≤ s := hs.1
    rw [hF_unfold]
    have h_pi : HasDerivAt ySol
        (fun j => (p j).eval₂ (Rat.castHom ℝ) (ySol s)) s := by
      rw [hasDerivAt_pi]; intro j; exact h_ySol_deriv s hs_pos j
    exact h_pi.hasDerivWithinAt
  -- Apply ODE uniqueness.
  have h_eq : Set.EqOn z ySol (Set.Icc 0 t) :=
    solutions_agree_on_Icc (y₀ := fun j => (y₀ j : ℝ))
      ht_pos hM_pos.le h_lip h_z0 h_ySol_init
      h_z_deriv_within h_ySol_deriv_within hM_z_bd hM_y_bd
  -- t' ∈ Icc 0 t, so z t' = ySol t', and |ySol t' i| ≤ β.
  have ht'_in : t' ∈ Set.Icc (0 : ℝ) t := ⟨ht'.1, ht_ge_t'⟩
  have h_z_eq_y : z t' = ySol t' := h_eq ht'_in
  have h_z_eq_i : z t' i = ySol t' i := congrFun h_z_eq_y i
  show |y t' ⟨2 * i.val, _⟩ - y t' ⟨2 * i.val + 1, _⟩| ≤ β
  have heq_lhs : y t' ⟨2 * i.val, by have := i.isLt; omega⟩
        - y t' ⟨2 * i.val + 1, by have := i.isLt; omega⟩ = z t' i := rfl
  rw [heq_lhs, h_z_eq_i]
  exact h_ySol_bd t' ht'.1 i

/-- Right-side strict decrease at a point with negative derivative. If
`HasDerivAt f f' x` and `f' < 0`, then there exists `δ > 0` such that for all
`τ ∈ [x, x + δ]`, `f τ ≤ f x`. -/
private lemma right_le_of_hasDerivAt_neg {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (hf' : f' < 0) :
    ∃ δ > 0, ∀ τ ∈ Set.Icc x (x + δ), f τ ≤ f x := by
  -- Use slope tendsto: (f(x+h) - f x)/h → f' as h → 0⁺. Pick threshold f'/2.
  have h_slope : Filter.Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x))
                    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds f') :=
    hf.tendsto_slope_zero_right
  -- slope tends to f' < 0; eventually (in 𝓝[>] 0) slope < f'/2 < 0.
  have h_lt : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      h⁻¹ • (f (x + h) - f x) < f' / 2 :=
    h_slope.eventually_lt_const (by linarith)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_lt
  obtain ⟨δ, hδ, h_prop⟩ := h_lt
  refine ⟨δ / 2, by linarith, ?_⟩
  intro τ hτ
  obtain ⟨hτl, hτr⟩ := hτ
  rcases eq_or_lt_of_le hτl with hτ_eq | hτ_gt
  · -- τ = x.
    rw [← hτ_eq]
  · -- τ > x. Set h := τ - x ∈ (0, δ).
    set h := τ - x with hh_def
    have hh_pos : 0 < h := by simp [hh_def]; linarith
    have hh_lt_δ : h < δ := by
      simp [hh_def]; linarith
    have hh_in : h ∈ Set.Ioi (0 : ℝ) := hh_pos
    have hh_dist : dist h 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh_pos]; exact hh_lt_δ
    have h_app := h_prop hh_dist hh_in
    -- h_app: h⁻¹ • (f (x + h) - f x) < f'/2.
    -- Hence f (x+h) - f x = h * (h⁻¹ • (f(x+h)-fx)) ≤ h*(f'/2) < 0.
    have hxh : x + h = τ := by simp [hh_def]
    rw [hxh] at h_app
    -- Rewrite smul as mul.
    have h_app' : h⁻¹ * (f τ - f x) < f' / 2 := by
      simpa [smul_eq_mul] using h_app
    -- Multiply both sides by h > 0: f τ - f x < h * (f' / 2).
    have h_mul : h * (h⁻¹ * (f τ - f x)) < h * (f' / 2) :=
      mul_lt_mul_of_pos_left h_app' hh_pos
    -- h * (h⁻¹ * (f τ - f x)) = f τ - f x.
    have h_simp : h * (h⁻¹ * (f τ - f x)) = f τ - f x := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hh_pos), one_mul]
    rw [h_simp] at h_mul
    -- h * (f' / 2) < 0.
    have h_neg : h * (f' / 2) < 0 := mul_neg_of_pos_of_neg hh_pos (by linarith)
    linarith

/-- HasDerivAt formula for `σ_i := y(2i) + y(2i+1)` along the
constant-annihilation dual-rail flow. -/
private lemma sigma_has_deriv (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (k : ℚ) (i : Fin n)
    {T : ℝ} (y : ℝ → Fin (2 * n) → ℝ)
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((constantAnnihilationDualRail n p k).evalField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (fun s => y s ⟨2 * i.val, by have := i.isLt; omega⟩
                            + y s ⟨2 * i.val + 1, by have := i.isLt; omega⟩)
        ((constantAnnihilationDualRail n p k).evalField (y t)
              ⟨2 * i.val, by have := i.isLt; omega⟩
            + (constantAnnihilationDualRail n p k).evalField (y t)
                ⟨2 * i.val + 1, by have := i.isLt; omega⟩) t := by
  intro t ht
  have hy_t := h_deriv t ht
  have hy_coord : ∀ K : Fin (2 * n),
      HasDerivAt (fun s => y s K)
        ((constantAnnihilationDualRail n p k).evalField (y t) K) t :=
    hasDerivAt_pi.mp hy_t
  exact (hy_coord ⟨2 * i.val, by have := i.isLt; omega⟩).add
        (hy_coord ⟨2 * i.val + 1, by have := i.isLt; omega⟩)

/-- σ-bound arm via Nagumo barrier: `y t (2i) + y t (2i+1) ≤ 2β`. Uses
`sigma_drift_strict_neg_at_upper_face` plus the diff-bound from
`posK_invariant_diffBound` and componentwise non-negativity. -/
lemma posK_invariant_sigmaBound (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β)
    (k : ℚ) (hk_pos : 0 < k) (hk_lt : thresholdK n p β < (k : ℝ))
    (T : ℝ) (hT : 0 < T) (y : ℝ → Fin (2 * n) → ℝ)
    (hy_init : y 0 = (fun K =>
      if K.val % 2 = 0
        then (max ((y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0)
        else (max (-(y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0)))
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((constantAnnihilationDualRail n p k).evalField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin n,
      y t ⟨2 * i.val, by have := i.isLt; omega⟩
        + y t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ≤ 2 * β := by
  classical
  have hβ : 0 < β := hBd.1
  have h_ySol_init : ySol 0 = (fun j => (y₀ j : ℝ)) := hBd.2.1
  have h_ySol_bd := hBd.2.2.2
  -- |y₀ i| ≤ β: from |ySol 0 i| ≤ β and ySol 0 i = y₀ i.
  have h_y₀_bd : ∀ i : Fin n, |((y₀ i : ℝ))| ≤ β := by
    intro i
    have h := h_ySol_bd 0 (le_refl _) i
    rw [show ((y₀ i : ℝ)) = ySol 0 i from by rw [h_ySol_init]]
    exact h
  -- σ_i abbrev.
  set σ : ℝ → Fin n → ℝ := fun τ i =>
    y τ ⟨2 * i.val, by have := i.isLt; omega⟩
      + y τ ⟨2 * i.val + 1, by have := i.isLt; omega⟩ with hσ_def
  -- σ_i(0) = |y₀ i| ≤ β.
  have hσ_init : ∀ i : Fin n, σ 0 i = |((y₀ i : ℝ))| := by
    intro i
    show y 0 ⟨2 * i.val, _⟩ + y 0 ⟨2 * i.val + 1, _⟩ = |((y₀ i : ℝ))|
    rw [show y 0 = _ from hy_init]
    have hev : (2 * i.val) % 2 = 0 := by omega
    have hodd : (2 * i.val + 1) % 2 ≠ 0 := by omega
    have hdiv1 : (2 * i.val) / 2 = i.val := by omega
    have hdiv2 : (2 * i.val + 1) / 2 = i.val := by omega
    simp only [hev, hodd, hdiv1, hdiv2, ↓reduceIte]
    have heq1 : (⟨i.val, by have := i.isLt; omega⟩ : Fin n) = i := Fin.eta i _
    rw [heq1]
    -- max(a, 0) + max(-a, 0) = |a|.
    by_cases h : 0 ≤ ((y₀ i : ℝ))
    · rw [max_eq_left h, max_eq_right (by linarith : -(y₀ i : ℝ) ≤ 0),
          add_zero, abs_of_nonneg h]
    · replace h : ((y₀ i : ℝ)) < 0 := lt_of_not_ge h
      rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(y₀ i : ℝ)),
          zero_add, abs_of_neg h]
  -- σ_i(0) ≤ β < 2β (since β > 0).
  have hσ_init_le : ∀ i : Fin n, σ 0 i ≤ β := by
    intro i; rw [hσ_init i]; exact h_y₀_bd i
  -- Componentwise non-negativity (from helper lemma).
  have h_nn := posK_invariant_nonneg n p y₀ k hk_pos T hT y hy_init h_deriv
  -- diffBound (from helper lemma).
  have h_diff := posK_invariant_diffBound n p y₀ ySol β hBd k hk_pos T hT y
                   hy_init h_deriv
  -- σ HasDerivAt formula.
  have hσ_deriv : ∀ i : Fin n, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt (σ · i)
        ((constantAnnihilationDualRail n p k).evalField (y t)
              ⟨2 * i.val, by have := i.isLt; omega⟩
            + (constantAnnihilationDualRail n p k).evalField (y t)
                ⟨2 * i.val + 1, by have := i.isLt; omega⟩) t := by
    intro i t ht
    exact sigma_has_deriv n p k i y h_deriv t ht
  -- σ continuity on any [0, t'] ⊆ [0, T).
  have hσ_cont_at : ∀ i : Fin n, ∀ τ ∈ Set.Ico (0 : ℝ) T,
      ContinuousAt (σ · i) τ :=
    fun i τ hτ => (hσ_deriv i τ hτ).continuousAt
  -- Main proof: contradiction.
  intro t' ht' i₀
  by_contra h_gt
  push_neg at h_gt
  -- h_gt : 2β < σ t' i₀.
  have ht'_nn : 0 ≤ t' := ht'.1
  have ht'_lt_T : t' < T := ht'.2
  -- ContinuousOn for σ on Icc 0 t'.
  have hσ_cont_Icc : ∀ i : Fin n, ContinuousOn (σ · i) (Set.Icc 0 t') := by
    intro i τ hτ
    refine (hσ_cont_at i τ ?_).continuousWithinAt
    exact ⟨hτ.1, lt_of_le_of_lt hτ.2 ht'_lt_T⟩
  -- The set S := {τ ∈ [0, t'] | ∀ i, σ i τ ≤ 2β}.
  set S : Set ℝ := {τ | τ ∈ Set.Icc (0 : ℝ) t' ∧ ∀ i : Fin n, σ τ i ≤ 2 * β}
    with hS_def
  have h0_mem : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_refl _, ht'_nn⟩, ?_⟩
    intro i
    have h1 : σ 0 i ≤ β := hσ_init_le i
    linarith
  have hS_ne : S.Nonempty := ⟨0, h0_mem⟩
  have hS_bdd : BddAbove S := ⟨t', fun τ hτ => hτ.1.2⟩
  set τ_star : ℝ := sSup S with hτ_def
  have hτ_le : τ_star ≤ t' := csSup_le hS_ne (fun τ hτ => hτ.1.2)
  have hτ_nn : 0 ≤ τ_star := le_csSup hS_bdd h0_mem
  have hτ_in_Icc : τ_star ∈ Set.Icc (0 : ℝ) t' := ⟨hτ_nn, hτ_le⟩
  have hτ_in_Ico : τ_star ∈ Set.Ico (0 : ℝ) T :=
    ⟨hτ_nn, lt_of_le_of_lt hτ_le ht'_lt_T⟩
  -- σ i τ_star ≤ 2β for all i, by sequential continuity.
  have h_τ_in_S : ∀ i : Fin n, σ τ_star i ≤ 2 * β := by
    intro i
    rcases eq_or_lt_of_le hτ_nn with hτ_zero | hτ_pos
    · rw [← hτ_zero]
      have h1 : σ 0 i ≤ β := hσ_init_le i
      linarith
    · have hs_cont_τ : ContinuousWithinAt (σ · i) (Set.Icc 0 t') τ_star :=
        hσ_cont_Icc i τ_star hτ_in_Icc
      by_contra h_gt_τ
      push_neg at h_gt_τ
      rw [Metric.continuousWithinAt_iff] at hs_cont_τ
      obtain ⟨δ, hδ, hδ_prop⟩ := hs_cont_τ ((σ τ_star i - 2 * β) / 2) (by linarith)
      obtain ⟨u, hu_mem, hu_lt⟩ :=
        exists_lt_of_lt_csSup hS_ne (show τ_star - δ < τ_star by linarith)
      have hu_le := le_csSup hS_bdd hu_mem
      have hu_in_Icc : u ∈ Set.Icc (0 : ℝ) t' := hu_mem.1
      have hu_dist : dist u τ_star < δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith : u - τ_star ≤ 0)]
        linarith
      have h_close := hδ_prop hu_in_Icc hu_dist
      rw [Real.dist_eq] at h_close
      have h_abs := abs_sub_lt_iff.mp h_close
      -- σ_i u ≤ 2β (since u ∈ S).
      have hσ_u : σ u i ≤ 2 * β := hu_mem.2 i
      linarith [h_abs.2]
  -- τ_star ∈ S.
  have hτ_in_S : τ_star ∈ S := ⟨hτ_in_Icc, h_τ_in_S⟩
  -- τ_star ≠ t' (else σ i₀ τ_star ≤ 2β contradicts h_gt at t').
  have hτ_lt : τ_star < t' := by
    rcases eq_or_lt_of_le hτ_le with hτ_eq | hτ_lt
    · exfalso
      have := h_τ_in_S i₀
      rw [hτ_eq] at this
      linarith
    · exact hτ_lt
  -- At τ_star, for each i, σ i τ_star ≤ 2β. Box-bound y K ≤ 2β.
  have h_box_le : ∀ K, y τ_star K ≤ 2 * β := by
    intro K
    rcases Nat.even_or_odd K.val with h_even | h_odd
    · obtain ⟨j_val, hj_val⟩ := h_even
      have hj_lt : j_val < n := by have := K.isLt; omega
      let j : Fin n := ⟨j_val, hj_lt⟩
      have hK_eq : K = ⟨2 * j.val, by have := j.isLt; omega⟩ := by
        apply Fin.ext; show K.val = 2 * j_val; omega
      rw [hK_eq]
      have hσ_j : σ τ_star j ≤ 2 * β := h_τ_in_S j
      have h_other_nn : 0 ≤ y τ_star ⟨2 * j.val + 1, by have := j.isLt; omega⟩ :=
        h_nn τ_star hτ_in_Ico _
      show y τ_star ⟨2 * j.val, _⟩ ≤ 2 * β
      have : σ τ_star j = y τ_star ⟨2 * j.val, _⟩
                          + y τ_star ⟨2 * j.val + 1, _⟩ := rfl
      linarith
    · obtain ⟨j_val, hj_val⟩ := h_odd
      have hj_lt : j_val < n := by have := K.isLt; omega
      let j : Fin n := ⟨j_val, hj_lt⟩
      have hK_eq : K = ⟨2 * j.val + 1, by have := j.isLt; omega⟩ := by
        apply Fin.ext; show K.val = 2 * j_val + 1; omega
      rw [hK_eq]
      have hσ_j : σ τ_star j ≤ 2 * β := h_τ_in_S j
      have h_other_nn : 0 ≤ y τ_star ⟨2 * j.val, by have := j.isLt; omega⟩ :=
        h_nn τ_star hτ_in_Ico _
      show y τ_star ⟨2 * j.val + 1, _⟩ ≤ 2 * β
      have : σ τ_star j = y τ_star ⟨2 * j.val, _⟩
                          + y τ_star ⟨2 * j.val + 1, _⟩ := rfl
      linarith
  -- For each i, find δ_i > 0 with σ i τ ≤ 2β on [τ_star, τ_star + δ_i].
  have h_per_i : ∀ i : Fin n, ∃ δ_i > 0,
      ∀ τ ∈ Set.Icc τ_star (τ_star + δ_i), σ τ i ≤ 2 * β := by
    intro i
    rcases lt_or_eq_of_le (h_τ_in_S i) with h_lt | h_eq
    · -- σ i τ_star < 2β. Use continuity.
      have hs_cont_τ : ContinuousAt (σ · i) τ_star := hσ_cont_at i τ_star hτ_in_Ico
      rw [Metric.continuousAt_iff] at hs_cont_τ
      obtain ⟨δ, hδ, hδ_prop⟩ := hs_cont_τ ((2 * β - σ τ_star i) / 2) (by linarith)
      refine ⟨δ / 2, by linarith, ?_⟩
      intro τ hτ
      obtain ⟨hτl, hτr⟩ := hτ
      rcases eq_or_lt_of_le hτl with hτ_eq' | hτ_gt'
      · rw [← hτ_eq']; linarith
      · have hτ_dist : dist τ τ_star < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < τ - τ_star)]
          linarith
        have h_close := hδ_prop hτ_dist
        rw [Real.dist_eq] at h_close
        have h_abs := abs_sub_lt_iff.mp h_close
        linarith
    · -- σ i τ_star = 2β. Use sigma_drift_strict_neg_at_upper_face.
      have h_face : y τ_star ⟨2 * i.val, by have := i.isLt; omega⟩
                    + y τ_star ⟨2 * i.val + 1, by have := i.isLt; omega⟩ = 2 * β := by
        change σ τ_star i = 2 * β; linarith [h_eq]
      have h_diff_τ := h_diff τ_star hτ_in_Ico i
      have h_strict := sigma_drift_strict_neg_at_upper_face n p k β hβ hk_lt
        (y τ_star) (h_nn τ_star hτ_in_Ico) h_box_le i h_face h_diff_τ
      -- HasDerivAt for σ_i at τ_star, value < 0.
      have h_d := hσ_deriv i τ_star hτ_in_Ico
      obtain ⟨δ_i, hδ_i, hδ_prop⟩ := right_le_of_hasDerivAt_neg h_d h_strict
      refine ⟨δ_i, hδ_i, ?_⟩
      intro τ hτ
      have h_le := hδ_prop τ hτ
      -- σ τ i ≤ σ τ_star i = 2β.
      linarith [h_eq, h_le]
  -- Combine δ_i's: take the min. Use Finset.inf' over the universe of Fin n.
  -- Build δ_choice : Fin n → ℝ giving each δ_i > 0.
  choose δ_choice hδ_pos hδ_prop using h_per_i
  -- δ := min over i of δ_choice i.
  let δ : ℝ := (Finset.univ : Finset (Fin n)).inf' Finset.univ_nonempty δ_choice
  have hδ_pos_all : 0 < δ := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _; exact hδ_pos i
  have hδ_le : ∀ i : Fin n, δ ≤ δ_choice i := by
    intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)
  -- Pick δ' := min(δ, t' - τ_star) / 2 > 0; then τ_star + δ' ≤ τ_star + δ ≤ τ_star + δ_choice i.
  set δ' : ℝ := min δ (t' - τ_star) / 2 with hδ'_def
  have h_min_pos : 0 < min δ (t' - τ_star) := lt_min hδ_pos_all (by linarith)
  have hδ'_pos : 0 < δ' := by
    show 0 < min δ (t' - τ_star) / 2
    linarith
  have hδ'_le_δ : δ' ≤ δ := by
    have h1 : min δ (t' - τ_star) ≤ δ := min_le_left _ _
    show min δ (t' - τ_star) / 2 ≤ δ
    linarith [hδ_pos_all]
  have hδ'_le_t : τ_star + δ' ≤ t' := by
    have h1 : min δ (t' - τ_star) ≤ t' - τ_star := min_le_right _ _
    have h2 : δ' ≤ t' - τ_star := by
      show min δ (t' - τ_star) / 2 ≤ t' - τ_star
      linarith
    linarith
  -- τ_star + δ' ∈ S → τ_star + δ' ≤ τ_star, contradiction.
  have h_in_S : (τ_star + δ') ∈ S := by
    refine ⟨⟨by linarith, hδ'_le_t⟩, ?_⟩
    intro i
    have h_in_int : τ_star + δ' ∈ Set.Icc τ_star (τ_star + δ_choice i) := by
      refine ⟨by linarith, ?_⟩
      have : δ' ≤ δ_choice i := le_trans hδ'_le_δ (hδ_le i)
      linarith
    exact hδ_prop i (τ_star + δ') h_in_int
  have h_contra : τ_star + δ' ≤ τ_star := le_csSup hS_bdd h_in_S
  linarith

lemma posK_invariant (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β)
    (k : ℚ) (hk_pos : 0 < k) (hk_lt : thresholdK n p β < (k : ℝ))
    (T : ℝ) (hT : 0 < T) (y : ℝ → Fin (2 * n) → ℝ)
    (hy_init : y 0 = (fun K =>
      if K.val % 2 = 0
        then (max ((y₀ ⟨K.val / 2, by
                have hK := K.isLt; omega⟩ : ℝ)) 0)
        else (max (-(y₀ ⟨K.val / 2, by
                have hK := K.isLt; omega⟩ : ℝ)) 0)))
    (h_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y ((constantAnnihilationDualRail n p k).evalField (y t)) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ K, 0 ≤ y t K ∧ y t K ≤ 2 * β := by
  -- Combine three sub-lemmas.
  have h_nn := posK_invariant_nonneg n p y₀ k hk_pos T hT y hy_init h_deriv
  have h_sigma := posK_invariant_sigmaBound n p y₀ ySol β hBd k hk_pos hk_lt
    T hT y hy_init h_deriv
  intro t ht K
  refine ⟨h_nn t ht K, ?_⟩
  -- Box bound: y t K ≤ 2β. Express K in terms of its parity-based pair.
  by_cases h : K.val % 2 = 0
  · -- K = 2i. Sister index is 2i+1 (≥ 0). σ ≤ 2β → y t K ≤ 2β.
    set i : Fin n := ⟨K.val / 2, by have := K.isLt; omega⟩
    have hKv : K = ⟨2 * i.val, by have := i.isLt; omega⟩ := by
      apply Fin.ext; simp only [i]; omega
    rw [hKv]
    have h_sister_nn : 0 ≤ y t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ :=
      h_nn t ht _
    have hσ := h_sigma t ht i
    linarith
  · -- K = 2i+1. Sister is 2i.
    set i : Fin n := ⟨K.val / 2, by have := K.isLt; omega⟩
    have hKv : K = ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
      apply Fin.ext; simp only [i]; omega
    rw [hKv]
    have h_sister_nn : 0 ≤ y t ⟨2 * i.val, by have := i.isLt; omega⟩ :=
      h_nn t ht _
    have hσ := h_sigma t ht i
    linarith

/-- Sub-lemma 2 (Picard form): existence of a globally-defined dual-rail
solution `ûSol` with the dual-rail-split initial condition derived from `y₀`.

Closed via `polyPIVP_field_locally_lipschitz` + `posK_invariant` +
`locally_lipschitz_bounded_global_ode_proved_continuous`. -/
lemma posK_picard (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β)
    (k : ℚ) (hk_pos : 0 < k) (hk_lt : thresholdK n p β < (k : ℝ)) :
    ∃ (ûSol : ℝ → Fin (2 * n) → ℝ),
      ûSol 0 = (fun K =>
        if K.val % 2 = 0
          then (max ((y₀ ⟨K.val / 2, by
                  have hK := K.isLt; omega⟩ : ℝ)) 0)
          else (max (-(y₀ ⟨K.val / 2, by
                  have hK := K.isLt; omega⟩ : ℝ)) 0)) ∧
      (∀ t ≥ (0 : ℝ),
        HasDerivAt (fun s => ûSol s)
          ((constantAnnihilationDualRail n p k).evalField (ûSol t)) t) := by
  classical
  have hβ : 0 < β := hBd.1
  -- Set up the Picard machinery: F is the polynomial vector field, y₀_dr is
  -- the dual-rail split of the GPAC initial condition.
  set F : (Fin (2 * n) → ℝ) → Fin (2 * n) → ℝ :=
    (constantAnnihilationDualRail n p k).evalField with hF_def
  set y₀_dr : Fin (2 * n) → ℝ := fun K =>
    if K.val % 2 = 0
      then max ((y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0
      else max (-(y₀ ⟨K.val / 2, by have hK := K.isLt; omega⟩ : ℝ)) 0
    with hy₀_dr_def
  -- (A) Local Lipschitz of F on every closed ball, from
  -- `polyPIVP_field_locally_lipschitz`.
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (2 * n) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F x - F y‖ ≤ L * ‖x - y‖ :=
    Ripple.polyPIVP_field_locally_lipschitz (constantAnnihilationDualRail n p k)
  -- The barrier M = 2β.
  have hM_pos : (0 : ℝ) < 2 * β := by linarith
  -- (B') Initial conditions of `y₀_dr` are inside the box.
  have h_y₀_dr_nn : ∀ K, 0 ≤ y₀_dr K := by
    intro K
    simp only [hy₀_dr_def]
    split_ifs <;> exact le_max_right _ _
  have h_y₀_dr_sigma : ∀ i : Fin n,
      y₀_dr ⟨2 * i.val, by have := i.isLt; omega⟩ +
        y₀_dr ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ≤ 2 * β := by
    intro i
    simp only [hy₀_dr_def]
    have hev : (2 * i.val) % 2 = 0 := by omega
    have hodd : (2 * i.val + 1) % 2 ≠ 0 := by omega
    have hdiv1 : (2 * i.val) / 2 = i.val := by omega
    have hdiv2 : (2 * i.val + 1) / 2 = i.val := by omega
    simp only [hev, hodd, hdiv1, hdiv2, ↓reduceIte]
    have heq1 : (⟨i.val, by omega⟩ : Fin n) = i := Fin.eta i _
    rw [heq1]
    -- max(y₀ i, 0) + max(-y₀ i, 0) = |y₀ i| ≤ β ≤ 2β.
    have habs : max ((y₀ i : ℝ)) 0 + max (-(y₀ i : ℝ)) 0 = |(y₀ i : ℝ)| := by
      by_cases h : 0 ≤ ((y₀ i : ℝ))
      · rw [max_eq_left h, max_eq_right (by linarith : -(y₀ i : ℝ) ≤ 0),
          abs_of_nonneg h]; ring
      · replace h : ((y₀ i : ℝ)) < 0 := lt_of_not_ge h
        rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(y₀ i : ℝ)),
          abs_of_neg h]; ring
    rw [habs]
    have h_ySol0 : ySol 0 = (fun j => (y₀ j : ℝ)) := hBd.2.1
    have h_bd0 : |ySol 0 i| ≤ β := hBd.2.2.2 0 le_rfl i
    rw [h_ySol0] at h_bd0
    linarith
  -- (B) A priori sup-norm bound from `posK_invariant`: any Ico solution
  -- starting at `y₀_dr` stays componentwise in `[0, 2β]`, hence has
  -- sup-norm ≤ 2β.
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin (2 * n) → ℝ),
      y 0 = y₀_dr →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (F (y t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ 2 * β := by
    intro T hT y hy0 h_deriv_y t ht
    have h_box := posK_invariant n p y₀ ySol β hBd k hk_pos hk_lt T hT y
      hy0 h_deriv_y t ht
    rw [pi_norm_le_iff_of_nonneg hM_pos.le]
    intro K
    have ⟨h_K_nn, h_K_le⟩ := h_box K
    rw [Real.norm_eq_abs, abs_of_nonneg h_K_nn]
    exact h_K_le
  -- (C) Apply the global-existence theorem.
  obtain ⟨ûSol, hûSol_init, hûSol_deriv, _hûSol_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous F y₀_dr
      h_lip (2 * β) hM_pos h_invariant
  refine ⟨ûSol, hûSol_init, ?_⟩
  intro t ht
  exact hûSol_deriv t ht

/-- Sub-lemma 3: Nagumo box invariance for the specific dual-rail solution.
Trivial corollary of `posK_invariant`. -/
lemma posK_boxBound (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β)
    (k : ℚ) (hk_pos : 0 < k) (hk_lt : thresholdK n p β < (k : ℝ))
    (ûSol : ℝ → Fin (2 * n) → ℝ)
    (hûSol_init : ûSol 0 = (fun K =>
      if K.val % 2 = 0
        then (max ((y₀ ⟨K.val / 2, by
                have hK := K.isLt; omega⟩ : ℝ)) 0)
        else (max (-(y₀ ⟨K.val / 2, by
                have hK := K.isLt; omega⟩ : ℝ)) 0)))
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => ûSol s)
        ((constantAnnihilationDualRail n p k).evalField (ûSol t)) t) :
    ∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ 2 * β := by
  intro t ht K
  -- Apply `posK_invariant` on `Ico 0 (t + 1)` (any open right-end works).
  have h_deriv' : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
      HasDerivAt ûSol
        ((constantAnnihilationDualRail n p k).evalField (ûSol s)) s := by
    intro s hs
    exact h_deriv s hs.1
  have ht_in : t ∈ Set.Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  exact posK_invariant n p y₀ ySol β hBd k hk_pos hk_lt (t + 1)
    (by linarith) ûSol hûSol_init h_deriv' t ht_in K

/-- Algebraic half of sub-lemma 4: the difference `z_i := u_i − v_i` of the
dual-rail solution satisfies the original GPAC. This is a direct consequence
of `constantAnnihilationDualRail_drift_diff` plus the projection lemma
`hasDerivAt_pi`. No analytic content — closed. -/
lemma posK_diff_solves_original (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ)
    (k : ℚ) (ûSol : ℝ → Fin (2 * n) → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => ûSol s)
        ((constantAnnihilationDualRail n p k).evalField (ûSol t)) t) :
    ∀ t ≥ (0 : ℝ), ∀ i : Fin n,
      HasDerivAt
        (fun s => ûSol s ⟨2 * i.val, by have := i.isLt; omega⟩
                  - ûSol s ⟨2 * i.val + 1, by have := i.isLt; omega⟩)
        ((p i).eval₂ (Rat.castHom ℝ)
          (fun j : Fin n => ûSol t ⟨2 * j.val, by have := j.isLt; omega⟩
            - ûSol t ⟨2 * j.val + 1, by have := j.isLt; omega⟩)) t := by
  intro t ht i
  have h := h_deriv t ht
  -- Projection of the vector derivative to component K = 2i and K = 2i+1.
  have hpi := (hasDerivAt_pi (φ := fun s => ûSol s)
    (φ' := (constantAnnihilationDualRail n p k).evalField (ûSol t))).1 h
  have hu := hpi ⟨2 * i.val, by have := i.isLt; omega⟩
  have hv := hpi ⟨2 * i.val + 1, by have := i.isLt; omega⟩
  -- Difference of the two component derivatives.
  have hdiff := hu.sub hv
  -- Identify the drift difference with `p i (y_1, …, y_n)` via `drift_diff`.
  have heq := constantAnnihilationDualRail_drift_diff n p k (ûSol t) i
  rw [heq] at hdiff
  exact hdiff

/-- Sub-lemma 4: Dual-rail identity from ODE uniqueness.

Closed via `solutions_agree_on_Icc` (Mathlib's
`ODE_solution_unique_of_mem_Icc_right` wrapped for the `Fin n → ℝ`-valued
polynomial vector field) plus `polyPIVP_field_locally_lipschitz` for the
Lipschitz hypothesis. -/
lemma posK_identity (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β)
    (k : ℚ) (_hk_pos : 0 < k)
    (ûSol : ℝ → Fin (2 * n) → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => ûSol s)
        ((constantAnnihilationDualRail n p k).evalField (ûSol t)) t)
    (h_init_diff : ∀ i : Fin n,
      ûSol 0 ⟨2 * i.val, by have := i.isLt; omega⟩
        - ûSol 0 ⟨2 * i.val + 1, by have := i.isLt; omega⟩
        = (y₀ i : ℝ))
    (h_box : ∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ 2 * β) :
    ∀ t ≥ (0 : ℝ), ∀ i : Fin n,
      ûSol t ⟨2 * i.val, by have := i.isLt; omega⟩
        - ûSol t ⟨2 * i.val + 1, by have := i.isLt; omega⟩
        = ySol t i := by
  classical
  have hβ : 0 < β := hBd.1
  -- Define the candidate solution z(t) i := u_i(t) − v_i(t).
  set z : ℝ → Fin n → ℝ := fun t i =>
    ûSol t ⟨2 * i.val, by have := i.isLt; omega⟩
      - ûSol t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ with hz_def
  -- Reduce the goal to: ∀ t ≥ 0, z t = ySol t.
  suffices h : ∀ t ≥ (0 : ℝ), z t = ySol t by
    intro t ht i
    exact congrFun (h t ht) i
  -- The original GPAC packaged as a PolyPIVP, to invoke the Lipschitz lemma.
  let P : PolyPIVP n :=
    { field := p
      init := y₀
      output := ⟨0, by have := NeZero.ne n; omega⟩ }
  set F : (Fin n → ℝ) → Fin n → ℝ := P.toPIVP.field with hF_def
  have hF_unfold : ∀ y : Fin n → ℝ,
      F y = (fun i => (p i).eval₂ (Rat.castHom ℝ) y) := by
    intro y; funext i; rfl
  -- Local Lipschitz of F on every closed ball.
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F x - F y‖ ≤ L * ‖x - y‖ :=
    Ripple.polyPIVP_field_locally_lipschitz P
  -- Initial conditions match: z 0 = ySol 0 = y₀ (cast to ℝ).
  have h_z0 : z 0 = (fun i => (y₀ i : ℝ)) := by
    funext i; exact h_init_diff i
  have h_y0 : ySol 0 = (fun i => (y₀ i : ℝ)) := hBd.2.1
  -- Sup-norm bounds on z and ySol: both ≤ 2β.
  have h_z_bd : ∀ t ≥ (0 : ℝ), ‖z t‖ ≤ 2 * β := by
    intro t ht
    rw [pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * β)]
    intro i
    have hu := h_box t ht ⟨2 * i.val, by have := i.isLt; omega⟩
    have hv := h_box t ht ⟨2 * i.val + 1, by have := i.isLt; omega⟩
    have hzi : |z t i| ≤ 2 * β := by
      simp only [hz_def]
      have h1 : 0 ≤ ûSol t ⟨2 * i.val, by have := i.isLt; omega⟩ := hu.1
      have h2 : ûSol t ⟨2 * i.val, by have := i.isLt; omega⟩ ≤ 2 * β := hu.2
      have h3 : 0 ≤ ûSol t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := hv.1
      have h4 : ûSol t ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ≤ 2 * β := hv.2
      rw [abs_le]; constructor <;> linarith
    rwa [Real.norm_eq_abs]
  have h_y_bd : ∀ t ≥ (0 : ℝ), ‖ySol t‖ ≤ 2 * β := by
    intro t ht
    rw [pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * β)]
    intro i
    have hyi : |ySol t i| ≤ β := hBd.2.2.2 t ht i
    rw [Real.norm_eq_abs]; linarith
  -- Strategy: prove EqOn z ySol on [0, T] for arbitrary T > 0, then use
  -- this to conclude z t = ySol t for any t ≥ 0.
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · -- t = 0: direct from h_z0, h_y0.
    rw [← hzero, h_z0, h_y0]
  -- t > 0: apply solutions_agree_on_Icc on [0, t + 1].
  set T : ℝ := t + 1 with hT_def
  have hT_pos : (0 : ℝ) < T := by linarith
  -- Both z and ySol satisfy the original ODE in HasDerivWithinAt form on
  -- [0, T].
  have hz_deriv_within : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt z (F (z s)) (Set.Icc 0 T) s := by
    intro s hs
    have hs_nn : 0 ≤ s := hs.1
    have hpc := posK_diff_solves_original n p k ûSol h_deriv s hs_nn
    -- Vector form: project component-wise via hasDerivAt_pi.
    have h_pi : HasDerivAt z (fun i => (p i).eval₂ (Rat.castHom ℝ) (z s)) s := by
      rw [hasDerivAt_pi]; intro i; exact hpc i
    rw [hF_unfold]
    exact h_pi.hasDerivWithinAt
  have hy_deriv_within : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt ySol (F (ySol s)) (Set.Icc 0 T) s := by
    intro s hs
    have hs_nn : 0 ≤ s := hs.1
    have h_pi : HasDerivAt ySol (fun i => (p i).eval₂ (Rat.castHom ℝ) (ySol s)) s := by
      rw [hasDerivAt_pi]; intro i; exact hBd.2.2.1 s hs_nn i
    rw [hF_unfold]
    exact h_pi.hasDerivWithinAt
  -- Sup-norm bounds on [0, T].
  have hz_bd_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖z s‖ ≤ 2 * β :=
    fun s hs => h_z_bd s hs.1
  have hy_bd_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖ySol s‖ ≤ 2 * β :=
    fun s hs => h_y_bd s hs.1
  -- Apply solutions_agree_on_Icc.
  have h_eq_on : Set.EqOn z ySol (Set.Icc 0 T) :=
    solutions_agree_on_Icc hT_pos (by linarith : (0 : ℝ) ≤ 2 * β) h_lip
      (by rw [h_z0]) (by rw [h_y0]) hz_deriv_within hy_deriv_within
      hz_bd_T hy_bd_T
  -- t ∈ [0, T] (in fact t < T), so EqOn gives z t = ySol t.
  have ht_in_T : t ∈ Set.Icc (0 : ℝ) T := ⟨ht, by linarith⟩
  exact h_eq_on ht_in_T

/-- **The main theorem (n ≥ 1 reduction).** Assembles the four sub-lemmas. -/
theorem constantAnnihilation_bounded_pos
    (n : ℕ) [NeZero n]
    (p : Fin n → MvPolynomial (Fin n) ℚ) (y₀ : Fin n → ℚ)
    (ySol : ℝ → Fin n → ℝ) (β : ℝ) (hBd : OriginalBounded p y₀ ySol β) :
    ∃ (k : ℚ), 0 < k ∧
      ∃ (ûSol : ℝ → Fin (2 * n) → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ B) ∧
        (∀ t ≥ (0 : ℝ), ∀ i : Fin n,
          ûSol t ⟨2 * i.val, by have := i.isLt; omega⟩
            - ûSol t ⟨2 * i.val + 1, by have := i.isLt; omega⟩
            = ySol t i) := by
  have hβ : 0 < β := hBd.1
  obtain ⟨k, hk_pos, hk_lt⟩ := posK_witness n p β hβ
  obtain ⟨ûSol, h_init_form, h_deriv⟩ :=
    posK_picard n p y₀ ySol β hBd k hk_pos hk_lt
  have h_box : ∀ t ≥ (0 : ℝ), ∀ K, 0 ≤ ûSol t K ∧ ûSol t K ≤ 2 * β :=
    posK_boxBound n p y₀ ySol β hBd k hk_pos hk_lt ûSol h_init_form h_deriv
  refine ⟨k, hk_pos, ûSol, 2 * β, by linarith, h_box, ?_⟩
  -- Dual-rail identity from sub-lemma 4.
  have h_init_diff : ∀ i : Fin n,
      ûSol 0 ⟨2 * i.val, by have := i.isLt; omega⟩
        - ûSol 0 ⟨2 * i.val + 1, by have := i.isLt; omega⟩
        = (y₀ i : ℝ) := by
    intro i
    simp only [h_init_form]
    have hev : (2 * i.val) % 2 = 0 := by omega
    have hodd : (2 * i.val + 1) % 2 ≠ 0 := by omega
    have hdiv1 : (2 * i.val) / 2 = i.val := by omega
    have hdiv2 : (2 * i.val + 1) / 2 = i.val := by omega
    simp only [hev, hodd, hdiv1, hdiv2, ↓reduceIte]
    have heq1 : (⟨i.val, by omega⟩ : Fin n) = i := Fin.eta i _
    rw [heq1]
    by_cases h : 0 ≤ ((y₀ i : ℝ))
    · rw [max_eq_left h, max_eq_right (by linarith : -(y₀ i : ℝ) ≤ 0)]; ring
    · replace h : ((y₀ i : ℝ)) < 0 := lt_of_not_ge h
      rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(y₀ i : ℝ))]; ring
  exact posK_identity n p y₀ ySol β hBd k hk_pos ûSol h_deriv h_init_diff h_box

/-- **UCNC 2025 Problem 1 (resolution).** For every bounded GPAC there is
a constant `k > 0` such that the constant-k uniform dual-rail system is
bounded on `[0, ∞)`.

Reduces to the two cases `n = 0` (vacuous) and `n ≥ 1`
(`constantAnnihilation_bounded_pos`). -/
theorem constantAnnihilation_bounded :
    ConstantAnnihilationBounded := by
  intro n p y₀ ySol β hBd
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact constantAnnihilation_bounded_zero p y₀ ySol β hBd
  · have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    exact constantAnnihilation_bounded_pos n p y₀ ySol β hBd

end DualRail
end Ripple
