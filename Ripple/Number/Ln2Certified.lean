/-
  Ripple.Number.Ln2Certified — log 2 is LPP-computable

  Builds a `CertifiedBoundedTimeComputable` witness for `log 2` on top of the
  existing `Ripple.Number.Ln2` construction (closed-form trajectory +
  convergence) and pairs it with a `PolyCRNDecomposition` that splits the
  PIVP vector field into production/degradation polynomials with
  non-negative rational coefficients. Applying
  `bounded_crn_is_lpp_computable` concludes
  `IsLPPComputable (log 2)` — with no dual-rail detour.

  The closed-form `ln2Solution` involves `log(2 - exp(-t))`, which is only
  real-valued for `t > -log 2`. We use a clamped trajectory
  `ln2SolutionExt t := ln2Solution (max t (-1/2))`, which (i) agrees with
  `ln2Solution` on `t ≥ 0`, (ii) is globally continuous, and (iii) remains
  inside the safe domain `(-log 2, ∞)` everywhere, since `-1/2 > -log 2`.

  Construction (matches `ln2PIVP` in `Ripple.Number.Ln2`):
    field₀ := X₁ · X₂                  (f' = v·r)
    field₁ := −X₁                      (v' = −v)
    field₂ := −(X₁ · X₂²)              (r' = −v·r²)
    init   := (0, 1, 1),  output := 0.

  Production/degradation split:
    prod₀ := X₁ · X₂;           degr₀ := 0              (f' = v·r − 0·f)
    prod₁ := 0;                 degr₁ := C 1            (v' = 0 − 1·v)
    prod₂ := 0;                 degr₂ := X₁ · X₂        (r' = 0 − (v·r)·r)

  All monomial coefficients lie in {0, 1} ⊂ ℚ≥0 and all initial
  concentrations are in {0, 1}.
-/

import Ripple.Number.Ln2
import Ripple.LPP.BoundedLPP
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Ripple.Number

open Ripple
open MvPolynomial
open Real

/-! ## The syntactic PolyPIVP for log 2 -/

/-- The syntactic `PolyPIVP 3` whose semantic image is `ln2PIVP`. -/
noncomputable def ln2PolyPIVP : PolyPIVP 3 where
  field := fun i =>
    match i with
    | 0 => X 1 * X 2
    | 1 => - X 1
    | 2 => - (X 1 * X 2 ^ 2)
  init := fun i =>
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 1
  output := 0

/-! ## Syntactic field equals semantic field -/

/-- The evaluated polynomial field matches the semantic `ln2PIVP` field. -/
theorem ln2PolyPIVP_evalField_eq (x : Fin 3 → ℝ) (i : Fin 3) :
    ln2PolyPIVP.toPIVP.field x i = ln2PIVP.field x i := by
  show ln2PolyPIVP.evalField x i = ln2PIVP.field x i
  unfold PolyPIVP.evalField
  fin_cases i
  · show ((X 1 * X 2 : MvPolynomial (Fin 3) ℚ)).eval₂ (Rat.castHom ℝ) x =
        ln2PIVP.field x 0
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    simp [ln2PIVP]
  · show ((- X 1 : MvPolynomial (Fin 3) ℚ)).eval₂ (Rat.castHom ℝ) x =
        ln2PIVP.field x 1
    simp only [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
    simp [ln2PIVP]
  · show ((- (X 1 * X 2 ^ 2) : MvPolynomial (Fin 3) ℚ)).eval₂
          (Rat.castHom ℝ) x = ln2PIVP.field x 2
    simp only [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
    simp [ln2PIVP]

/-- Initial condition matches. -/
theorem ln2PolyPIVP_init_eq (i : Fin 3) :
    (ln2PolyPIVP.toPIVP.init i : ℝ) = ln2PIVP.init i := by
  show ((ln2PolyPIVP.init i : ℚ) : ℝ) = ln2PIVP.init i
  fin_cases i <;> simp [ln2PolyPIVP, ln2PIVP]

/-! ## Continuous extension of the closed-form trajectory -/

/-- A safe cap: `-1/2 > -log 2`, so `2 - exp(-t) > 0` for all `t ≥ -1/2`.
    Proof: `-t ≤ 1/2 < log 2`, hence `exp(-t) ≤ exp(1/2) < exp(log 2) = 2`. -/
private lemma two_sub_exp_pos_of_ge_neg_half {t : ℝ} (ht : -(1/2 : ℝ) ≤ t) :
    0 < 2 - Real.exp (-t) := by
  have h1 : -t ≤ (1/2 : ℝ) := by linarith
  have h_half_lt_log2 : (1/2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have h2 : Real.exp (-t) ≤ Real.exp (1/2 : ℝ) := Real.exp_le_exp.mpr h1
  have h3 : Real.exp (1/2 : ℝ) < Real.exp (Real.log 2) :=
    Real.exp_lt_exp.mpr h_half_lt_log2
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h3
  linarith

/-- Clamped (continuous) extension of `ln2Solution` to all of ℝ. Agrees with
`ln2Solution` on `t ≥ 0` (since `max t (-1/2) = t` there) and is globally
continuous because its argument stays in the safe domain. -/
noncomputable def ln2SolutionExt (t : ℝ) : Fin 3 → ℝ :=
  ln2Solution (max t (-(1/2 : ℝ)))

/-- On `t ≥ 0`, `ln2SolutionExt` agrees with `ln2Solution`. -/
theorem ln2SolutionExt_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ln2SolutionExt t = ln2Solution t := by
  unfold ln2SolutionExt
  have : max t (-(1/2 : ℝ)) = t := by
    apply max_eq_left; linarith
  rw [this]

/-- Continuity of the closed-form extension. -/
theorem ln2SolutionExt_continuous : Continuous ln2SolutionExt := by
  unfold ln2SolutionExt
  -- It suffices to show `fun t => ln2Solution (max t (-1/2))` is continuous
  -- coordinatewise.
  apply continuous_pi
  intro i
  have hmax_cont : Continuous (fun t : ℝ => max t (-(1/2 : ℝ))) :=
    continuous_id.max continuous_const
  have hmax_ge : ∀ t : ℝ, -(1/2 : ℝ) ≤ max t (-(1/2 : ℝ)) := fun t => le_max_right _ _
  fin_cases i
  · -- component 0: log(2 - exp(-(max t (-1/2))))
    change Continuous fun t => ln2Solution (max t (-(1/2 : ℝ))) 0
    have hfun : (fun t => ln2Solution (max t (-(1/2 : ℝ))) 0)
        = fun t => Real.log (2 - Real.exp (-(max t (-(1/2 : ℝ))))) := by
      funext t; simp [ln2_sol_f]
    rw [hfun]
    have hinner : Continuous (fun t : ℝ => 2 - Real.exp (-(max t (-(1/2 : ℝ))))) :=
      continuous_const.sub (Real.continuous_exp.comp (hmax_cont.neg))
    exact hinner.log (fun t => ne_of_gt
      (two_sub_exp_pos_of_ge_neg_half (hmax_ge t)))
  · -- component 1: exp(-(max t (-1/2)))
    change Continuous fun t => ln2Solution (max t (-(1/2 : ℝ))) 1
    have hfun : (fun t => ln2Solution (max t (-(1/2 : ℝ))) 1)
        = fun t => Real.exp (-(max t (-(1/2 : ℝ)))) := by
      funext t; simp [ln2_sol_v]
    rw [hfun]
    exact Real.continuous_exp.comp hmax_cont.neg
  · -- component 2: 1 / (2 - exp(-(max t (-1/2))))
    change Continuous fun t => ln2Solution (max t (-(1/2 : ℝ))) 2
    have hfun : (fun t => ln2Solution (max t (-(1/2 : ℝ))) 2)
        = fun t => 1 / (2 - Real.exp (-(max t (-(1/2 : ℝ))))) := by
      funext t; simp [ln2_sol_r]
    rw [hfun]
    have hinner : Continuous (fun t : ℝ => 2 - Real.exp (-(max t (-(1/2 : ℝ))))) :=
      continuous_const.sub (Real.continuous_exp.comp (hmax_cont.neg))
    exact continuous_const.div hinner (fun t => ne_of_gt
      (two_sub_exp_pos_of_ge_neg_half (hmax_ge t)))

/-! ## Solution bundle -/

/-- `ln2SolutionExt` is a semantic solution of `ln2PolyPIVP.toPIVP`.
On `t ≥ 0` it equals `ln2Solution`, and we reuse the derivative chain of
`Ripple.Number.Ln2`. -/
noncomputable def ln2PolySolution : PIVP.Solution ln2PolyPIVP.toPIVP where
  trajectory := ln2SolutionExt
  init_cond := by
    funext i
    rw [ln2SolutionExt_of_nonneg (le_refl 0)]
    rw [ln2_sol_init]
    rw [ln2PolyPIVP_init_eq]
  is_solution := fun t ht => by
    -- Rewrite syntactic field to semantic field.
    have hfield_eq : ln2PolyPIVP.toPIVP.field (ln2SolutionExt t)
        = ln2PIVP.field (ln2SolutionExt t) := by
      funext i; exact ln2PolyPIVP_evalField_eq _ i
    rw [hfield_eq]
    -- On `t ≥ 0`, `ln2SolutionExt t = ln2Solution t`.
    rw [ln2SolutionExt_of_nonneg ht]
    -- Now reprove HasDerivAt for ln2SolutionExt at t ≥ 0 using that
    -- ln2SolutionExt agrees with ln2Solution on a right-neighborhood of 0
    -- and on an open set around any t > 0; at t = 0, use that
    -- ln2SolutionExt = ln2Solution on [0, ∞) and that ln2Solution is
    -- smooth at 0 via the formula (valid on (-log 2, ∞)).
    -- We show HasDerivAt by reducing to `ln2Solution` (which is smooth near t)
    -- using `HasDerivAt.congr_of_eventuallyEq`.
    have hsol_deriv : HasDerivAt ln2Solution (ln2PIVP.field (ln2Solution t)) t := by
      have hfield : ln2PIVP.field (ln2Solution t) =
          ![exp (-t) / (2 - exp (-t)), -exp (-t),
            -(exp (-t) / (2 - exp (-t)) ^ 2)] := by
        ext i; fin_cases i <;>
          simp [ln2PIVP, ln2Solution, Matrix.cons_val_zero,
            Matrix.cons_val_one]
        · field_simp
        · ring
      rw [hfield, hasDerivAt_pi]
      have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
        simpa [id] using (hasDerivAt_id t).neg
      have h_exp_neg := h_neg.exp
      have h_inner := (hasDerivAt_const t (2:ℝ)).sub h_exp_neg
      have h2pos : (2 : ℝ) - exp (-t) ≠ 0 := ne_of_gt (two_sub_exp_pos ht)
      intro i; fin_cases i
      · change HasDerivAt (fun s => log (2 - exp (-s)))
          (exp (-t) / (2 - exp (-t))) t
        convert h_inner.log h2pos using 1
        simp [Pi.sub_apply]
      · change HasDerivAt (fun s => exp (-s)) (-exp (-t)) t
        convert h_exp_neg using 1; ring
      · change HasDerivAt (fun s => 1 / (2 - exp (-s)))
          (-(exp (-t) / (2 - exp (-t)) ^ 2)) t
        have h_one := hasDerivAt_const t (1:ℝ)
        convert h_one.div h_inner h2pos using 1
        simp [Pi.sub_apply]; ring
    -- Now transport to ln2SolutionExt using eventual equality.
    -- On the open set `{s : -(1/2) < s}`, we have `max s (-1/2) = s`,
    -- so `ln2SolutionExt s = ln2Solution s`.
    have hEventually : ln2SolutionExt =ᶠ[nhds t] ln2Solution := by
      have hopen : IsOpen {s : ℝ | -(1/2 : ℝ) < s} := isOpen_lt continuous_const continuous_id
      have hmem : t ∈ {s : ℝ | -(1/2 : ℝ) < s} := by
        show -(1/2 : ℝ) < t; linarith
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
      intro s (hs : -(1/2 : ℝ) < s)
      unfold ln2SolutionExt
      have : max s (-(1/2 : ℝ)) = s := max_eq_left (by linarith)
      rw [this]
    exact hsol_deriv.congr_of_eventuallyEq hEventually

/-! ## CertifiedBoundedTimeComputable witness -/

/-- Boundedness transported through the trajectory extension. For `t ≥ 0`,
`ln2SolutionExt t = ln2Solution t`, and `ln2_bounded` gives the bound. -/
theorem ln2PolyPIVP_bounded : ln2PolyPIVP.toPIVP.IsBounded ln2SolutionExt := by
  obtain ⟨M, hM_pos, hM_bound⟩ := ln2_bounded
  refine ⟨M, hM_pos, ?_⟩
  intro t ht
  rw [ln2SolutionExt_of_nonneg ht]
  exact hM_bound t ht

/-- `CertifiedBoundedTimeComputable` witness for `log 2`. -/
noncomputable def ln2CBTC : CertifiedBoundedTimeComputable 3 (log 2) where
  pivp := ln2PolyPIVP
  sol := ln2PolySolution
  modulus := fun r => (r : ℝ) + 1
  bounded := ln2PolyPIVP_bounded
  trajectory_continuous := ln2SolutionExt_continuous
  convergence := by
    intro r t htr
    have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
    have ht_pos : 0 ≤ t := by
      have : (0 : ℝ) ≤ (r : ℝ) + 1 := by linarith
      linarith
    show |ln2SolutionExt t ln2PolyPIVP.output - log 2| < Real.exp (-(r : ℝ))
    have hout : ln2PolyPIVP.output = (0 : Fin 3) := rfl
    rw [hout, ln2SolutionExt_of_nonneg ht_pos]
    calc |ln2Solution t 0 - log 2|
        ≤ exp (-t) := ln2_convergence t ht_pos
      _ < exp (-(↑r + 1)) := by apply exp_lt_exp.mpr; linarith
      _ = exp (-(↑r : ℝ) - 1) := by ring_nf
      _ < exp (-(↑r : ℝ)) := by apply exp_lt_exp.mpr; linarith

/-- ln 2 is real-time computable: `ln2CBTC` has modulus `r + 1`. -/
theorem ln2_is_realtime : Ripple.IsRealTimeComputable (log 2) :=
  ⟨3, ln2CBTC, 2, by norm_num, fun r => by
    change (r : ℝ) + 1 ≤ 2 * ((r : ℝ) + 1)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith⟩

/-! ## PolyCRNDecomposition witness -/

/-- Production polynomials: prod₀ = X 1 · X 2, prod₁ = 0, prod₂ = 0. -/
noncomputable def ln2Prod : Fin 3 → MvPolynomial (Fin 3) ℚ
  | 0 => X 1 * X 2
  | 1 => 0
  | 2 => 0

/-- Degradation polynomials: degr₀ = 0, degr₁ = C 1, degr₂ = X 1 · X 2. -/
noncomputable def ln2Degr : Fin 3 → MvPolynomial (Fin 3) ℚ
  | 0 => 0
  | 1 => C 1
  | 2 => X 1 * X 2

private lemma coeff_mul_nonneg {d : ℕ} (p q : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) (hq : ∀ σ, 0 ≤ q.coeff σ) :
    ∀ σ, 0 ≤ (p * q).coeff σ := by
  classical
  intro σ
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro ⟨a, b⟩ _
  exact mul_nonneg (hp a) (hq b)

private lemma coeff_X_nonneg {d : ℕ} (i : Fin d) :
    ∀ σ, 0 ≤ ((X i : MvPolynomial (Fin d) ℚ)).coeff σ := by
  classical
  intro σ
  rw [MvPolynomial.coeff_X']
  split_ifs <;> norm_num

private lemma coeff_C_nonneg {d : ℕ} {c : ℚ} (hc : 0 ≤ c) :
    ∀ σ, 0 ≤ ((C c : MvPolynomial (Fin d) ℚ)).coeff σ := by
  intro σ
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · exact le_refl _

/-- Non-negativity of prod coefficients. -/
theorem ln2Prod_nonneg (i : Fin 3) (σ : Fin 3 →₀ ℕ) : 0 ≤ (ln2Prod i).coeff σ := by
  fin_cases i
  · -- prod 0 = X 1 * X 2
    show 0 ≤ ((X 1 * X 2 : MvPolynomial (Fin 3) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _ (coeff_X_nonneg 1) (coeff_X_nonneg 2) σ
  · simp [ln2Prod]
  · simp [ln2Prod]

/-- Non-negativity of degr coefficients. -/
theorem ln2Degr_nonneg (i : Fin 3) (σ : Fin 3 →₀ ℕ) : 0 ≤ (ln2Degr i).coeff σ := by
  fin_cases i
  · simp [ln2Degr]
  · -- degr 1 = C 1
    show 0 ≤ ((C 1 : MvPolynomial (Fin 3) ℚ)).coeff σ
    exact coeff_C_nonneg (by norm_num) σ
  · -- degr 2 = X 1 * X 2
    show 0 ≤ ((X 1 * X 2 : MvPolynomial (Fin 3) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _ (coeff_X_nonneg 1) (coeff_X_nonneg 2) σ

/-- Initial conditions are non-negative: 0, 1, 1. -/
theorem ln2PolyPIVP_init_nonneg (i : Fin 3) : 0 ≤ ln2PolyPIVP.init i := by
  fin_cases i <;> simp [ln2PolyPIVP]

/-- Syntactic field decomposition: field_i = prod_i - degr_i * X_i. -/
theorem ln2PolyPIVP_field_eq (i : Fin 3) :
    ln2PolyPIVP.field i = ln2Prod i - ln2Degr i * MvPolynomial.X i := by
  fin_cases i
  · -- field 0 = X 1 * X 2 = X 1 * X 2 - 0 * X 0
    show (X 1 * X 2 : MvPolynomial (Fin 3) ℚ) = X 1 * X 2 - 0 * X 0
    ring
  · -- field 1 = - X 1 = 0 - C 1 * X 1
    show (- X 1 : MvPolynomial (Fin 3) ℚ) = 0 - C 1 * X 1
    rw [MvPolynomial.C_1]; ring
  · -- field 2 = -(X 1 * X 2 ^ 2) = 0 - (X 1 * X 2) * X 2
    show (- (X 1 * X 2 ^ 2) : MvPolynomial (Fin 3) ℚ) = 0 - X 1 * X 2 * X 2
    ring

/-- `PolyCRNDecomposition` witness for `ln2PolyPIVP`. -/
noncomputable def ln2PCD : PolyCRNDecomposition 3 ln2PolyPIVP where
  prod := ln2Prod
  degr := ln2Degr
  prod_nonneg := ln2Prod_nonneg
  degr_nonneg := ln2Degr_nonneg
  init_nonneg := ln2PolyPIVP_init_nonneg
  field_eq := ln2PolyPIVP_field_eq

/-! ## Main theorem: log 2 is LPP-computable -/

/-- `log 2 ∈ [0, 1]`: lower bound by `1 ≤ 2`, upper bound via `log 2 < 0.6932`
(from `Real.log_two_lt_d9`). -/
private theorem log_two_in_unit : 0 ≤ log 2 ∧ log 2 ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact Real.log_nonneg (by norm_num)
  · linarith [Real.log_two_lt_d9]

/-- **log 2 is LPP-computable** via the direct bounded-CRN-computable route
(no dual-rail). -/
theorem ln2_is_lpp_computable : IsLPPComputable (log 2) :=
  bounded_crn_is_lpp_computable log_two_in_unit ln2CBTC ln2PCD

end Ripple.Number
